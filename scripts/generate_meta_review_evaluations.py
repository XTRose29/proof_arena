from __future__ import annotations

import argparse
import json
import random
import threading
import time
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import requests

from scripts.env_file import load_env_file


load_env_file()

from app.config import (  # noqa: E402
    META_REVIEW_EVALUATIONS_DIR,
    QUESTION_SETS_DIR,
    cornell_gateway_api_key,
    cornell_gateway_base_url,
)
from app.services import _evaluation_prompt, _parse_evaluation, _rubric_text  # noqa: E402


MODELS = (
    "claude-sonnet-5",
    "gemini-3.1-pro-preview",
    "gpt-5.6-terra",
    "moonshot.kimi-k2-thinking",
)
RETRYABLE_STATUS_CODES = {408, 409, 429, 500, 502, 503, 504}
MAX_ATTEMPTS = 6
MAX_COMPLETION_TOKENS = 4000
REQUEST_TIMEOUT_SECONDS = 300

_write_lock = threading.Lock()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def chat_completions_url() -> str:
    base_url = cornell_gateway_base_url().rstrip("/")
    return f"{base_url}/chat/completions" if base_url.endswith("/v1") else f"{base_url}/v1/chat/completions"


def submission_files() -> list[Path]:
    paths = [
        path
        for question_dir in QUESTION_SETS_DIR.iterdir()
        if question_dir.is_dir()
        for path in question_dir.glob("*.lean")
        if path.is_file()
    ]
    return sorted(paths, key=lambda path: (path.stat().st_size, str(path)))


def output_path(submission_path: Path, model: str) -> Path:
    return (
        META_REVIEW_EVALUATIONS_DIR
        / submission_path.parent.name
        / submission_path.stem
        / f"{model}.txt"
    )


def valid_existing_evaluation(path: Path) -> bool:
    if not path.is_file():
        return False
    try:
        _parse_evaluation(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    return True


def extract_message_content(payload: dict[str, Any]) -> str:
    content = payload["choices"][0]["message"]["content"]
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "".join(
            str(item.get("text", ""))
            for item in content
            if isinstance(item, dict) and item.get("type") in {"text", "output_text"}
        )
    raise ValueError("The gateway response did not contain text content.")


def request_evaluation(model: str, prompt: str) -> tuple[dict[str, Any], dict[str, Any]]:
    api_key = cornell_gateway_api_key()
    base_url = cornell_gateway_base_url()
    if not api_key or not base_url:
        raise RuntimeError(
            "Cornell AI Gateway is not configured. Set CORNELL_AI_GATEWAY_API_KEY and "
            "CORNELL_AI_GATEWAY_BASE_URL, or configure the existing gateway fallbacks."
        )

    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }
    request_payload: dict[str, Any] = {
        "model": model,
        "max_completion_tokens": MAX_COMPLETION_TOKENS,
        "messages": [{"role": "user", "content": prompt}],
        "response_format": {"type": "json_object"},
    }

    last_error: Exception | None = None
    for attempt in range(1, MAX_ATTEMPTS + 1):
        try:
            response = requests.post(
                chat_completions_url(),
                headers=headers,
                json=request_payload,
                timeout=REQUEST_TIMEOUT_SECONDS,
            )
            if response.status_code == 400 and "response_format" in request_payload:
                request_payload.pop("response_format")
                continue
            if response.status_code in RETRYABLE_STATUS_CODES:
                raise requests.HTTPError(
                    f"Gateway returned retryable status {response.status_code}",
                    response=response,
                )
            response.raise_for_status()
            response_payload = response.json()
            evaluation = _parse_evaluation(extract_message_content(response_payload))
            usage = response_payload.get("usage", {})
            return evaluation, usage if isinstance(usage, dict) else {}
        except (KeyError, IndexError, TypeError, ValueError, requests.RequestException) as exc:
            last_error = exc
            if attempt == MAX_ATTEMPTS:
                break
            delay = min(60.0, (2 ** (attempt - 1)) + random.random())
            time.sleep(delay)

    raise RuntimeError(f"{model} failed after {MAX_ATTEMPTS} attempts: {last_error}") from last_error


def append_jsonl(path: Path, record: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with _write_lock:
        with path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def save_evaluation(path: Path, evaluation: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_path = path.with_suffix(path.suffix + ".tmp")
    temporary_path.write_text(
        json.dumps(evaluation, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    temporary_path.replace(path)


def generate_one(
    submission_path: Path,
    model: str,
    rubric_text: str,
    usage_log_path: Path,
    error_log_path: Path,
) -> tuple[str, str, str, dict[str, Any]]:
    destination = output_path(submission_path, model)
    relative_submission = str(submission_path.relative_to(QUESTION_SETS_DIR))
    if valid_existing_evaluation(destination):
        return "skipped", relative_submission, model, {}

    started_at = time.monotonic()
    try:
        proof_content = submission_path.read_text(encoding="utf-8")
        evaluation, usage = request_evaluation(model, _evaluation_prompt(proof_content, rubric_text))
        save_evaluation(destination, evaluation)
        append_jsonl(
            usage_log_path,
            {
                "at": utc_now(),
                "model": model,
                "output": str(destination.relative_to(META_REVIEW_EVALUATIONS_DIR)),
                "seconds": round(time.monotonic() - started_at, 3),
                "submission": relative_submission,
                "usage": usage,
            },
        )
        return "generated", relative_submission, model, usage
    except Exception as exc:
        append_jsonl(
            error_log_path,
            {
                "at": utc_now(),
                "error": str(exc),
                "model": model,
                "submission": relative_submission,
            },
        )
        return "failed", relative_submission, model, {"error": str(exc)}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate four validated model evaluations for every question_sets submission."
    )
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--limit-submissions", type=int)
    parser.add_argument("--model", action="append", choices=MODELS, dest="models")
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    models = tuple(args.models or MODELS)
    submissions = submission_files()
    if args.limit_submissions is not None:
        submissions = submissions[: max(0, args.limit_submissions)]

    jobs = [
        (submission_path, model)
        for submission_path in submissions
        for model in models
        if not valid_existing_evaluation(output_path(submission_path, model))
    ]
    existing = len(submissions) * len(models) - len(jobs)
    print(
        f"submissions={len(submissions)} models={len(models)} existing={existing} "
        f"pending={len(jobs)} workers={args.workers}",
        flush=True,
    )
    if args.dry_run or not jobs:
        return

    rubric_text = _rubric_text()
    usage_log_path = META_REVIEW_EVALUATIONS_DIR / "_generation_usage.jsonl"
    error_log_path = META_REVIEW_EVALUATIONS_DIR / "_generation_errors.jsonl"
    counts = {"generated": 0, "skipped": existing, "failed": 0}

    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as executor:
        futures: dict[Future[tuple[str, str, str, dict[str, Any]]], tuple[Path, str]] = {
            executor.submit(
                generate_one,
                submission_path,
                model,
                rubric_text,
                usage_log_path,
                error_log_path,
            ): (submission_path, model)
            for submission_path, model in jobs
        }
        for future in as_completed(futures):
            status, submission, model, details = future.result()
            counts[status] += 1
            completed = counts["generated"] + counts["failed"]
            suffix = f" error={details.get('error')}" if status == "failed" else ""
            print(
                f"[{completed}/{len(jobs)}] {status} model={model} submission={submission}{suffix}",
                flush=True,
            )

    print(json.dumps(counts, sort_keys=True), flush=True)
    if counts["failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
