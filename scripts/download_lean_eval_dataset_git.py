#!/usr/bin/env python3
"""Download public lean-eval proofs using git instead of the GitHub REST API."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


DEFAULT_OUTPUT = Path("lean_eval_dataset")
DEFAULT_CACHE = Path(os.environ.get("LEAN_EVAL_DOWNLOAD_CACHE", "/private/tmp/lean_eval_download_cache"))
SUBMISSIONS_REPO = "https://github.com/leanprover/lean-eval-submissions.git"


def run(args: list[str], cwd: Path | None = None) -> str:
    proc = subprocess.run(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        command = " ".join(args)
        raise RuntimeError(f"{command} failed: {proc.stderr.strip()}")
    return proc.stdout


def safe_name(value: str, max_len: int = 100) -> str:
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value.strip())
    value = value.strip("._")
    return (value or "unknown")[:max_len]


def ensure_clone(url: str, dest: Path) -> None:
    if (dest / ".git").exists():
        run(["git", "fetch", "--all", "--tags"], cwd=dest)
        return
    dest.parent.mkdir(parents=True, exist_ok=True)
    run(["git", "clone", url, str(dest)])


def checkout_ref(repo_dir: Path, ref: str) -> None:
    try:
        run(["git", "checkout", "--detach", ref], cwd=repo_dir)
    except subprocess.CalledProcessError:
        run(["git", "fetch", "origin", ref], cwd=repo_dir)
        run(["git", "checkout", "--detach", ref], cwd=repo_dir)


def iter_public_records(results_dir: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path in sorted(results_dir.glob("*.json")):
        data = json.loads(path.read_text())
        user = data.get("user") or path.stem
        for model, solved in data.get("solved", {}).items():
            if not isinstance(solved, dict):
                continue
            for problem_id, record in solved.items():
                if not isinstance(record, dict):
                    continue
                if not record.get("submission_public"):
                    continue
                repo = record.get("submission_repo")
                ref = record.get("submission_ref")
                if not repo or not ref or "/" not in repo:
                    continue
                records.append(
                    {
                        "user": user,
                        "model": model,
                        "problem_id": problem_id,
                        "record": record,
                    }
                )
    return records


def infer_submission_kind(record: dict[str, Any]) -> str:
    kind = record.get("submission_kind")
    if kind in {"gist", "repo"}:
        return kind
    _, source = record["submission_repo"].split("/", 1)
    if re.fullmatch(r"[0-9a-f]{20,64}", source):
        return "gist"
    return "repo"


def lakefile_matches_problem(text: str, problem_id: str) -> bool:
    name_patterns = [
        rf'^\s*name\s*=\s*"{re.escape(problem_id)}"\s*$',
        rf"^\s*name\s*:=\s*`?{re.escape(problem_id)}\s*$",
    ]
    return any(re.search(pattern, text, flags=re.MULTILINE) for pattern in name_patterns)


def source_url(record: dict[str, Any]) -> str:
    kind = infer_submission_kind(record)
    owner, name = record["submission_repo"].split("/", 1)
    if kind == "gist":
        return f"https://gist.github.com/{name}.git"
    return f"https://github.com/{owner}/{name}.git"


def source_cache_dir(cache_dir: Path, record: dict[str, Any]) -> Path:
    kind = infer_submission_kind(record)
    return cache_dir / "sources" / f"{kind}_{safe_name(record['submission_repo'], 160)}"


def lean_files_from_gist(repo_dir: Path) -> dict[str, str]:
    lean_files: dict[str, str] = {}
    for path in repo_dir.rglob("*.lean"):
        if ".git" in path.parts:
            continue
        rel = path.relative_to(repo_dir).as_posix()
        if rel == "Submission.lean" or rel.startswith("Submission/"):
            lean_files[rel] = path.read_text()
    return lean_files


def lean_files_from_repo(repo_dir: Path, problem_id: str) -> dict[str, str]:
    candidate_dirs: list[Path] = []
    for lakefile in list(repo_dir.rglob("lakefile.toml")) + list(repo_dir.rglob("lakefile.lean")):
        if ".git" in lakefile.parts:
            continue
        try:
            text = lakefile.read_text()
        except UnicodeDecodeError:
            continue
        if not lakefile_matches_problem(text, problem_id):
            continue
        directory = lakefile.parent
        if (directory / "Submission.lean").exists():
            candidate_dirs.append(directory)

    lean_files: dict[str, str] = {}
    for directory in candidate_dirs:
        primary = directory / "Submission.lean"
        lean_files["Submission.lean"] = primary.read_text()
        support_dir = directory / "Submission"
        if support_dir.exists():
            for path in support_dir.rglob("*.lean"):
                rel = path.relative_to(directory).as_posix()
                lean_files[rel] = path.read_text()
    return lean_files


def proof_stem(entry: dict[str, Any]) -> str:
    record = entry["record"]
    source = record["submission_repo"].replace("/", "_")
    issue = record.get("issue_number", "unknown")
    ref = record.get("submission_ref", "")[:12]
    parts = [
        safe_name(entry["user"], 40),
        safe_name(entry["model"], 60),
        f"issue{issue}",
        safe_name(source, 80),
        safe_name(ref, 16),
    ]
    return "__".join(parts)


def write_entry(output_dir: Path, entry: dict[str, Any], lean_files: dict[str, str]) -> list[str]:
    primary = lean_files.get("Submission.lean")
    if primary is None:
        raise RuntimeError("Submission.lean not found")

    problem_dir = output_dir / safe_name(entry["problem_id"])
    problem_dir.mkdir(parents=True, exist_ok=True)
    stem = proof_stem(entry)
    written: list[str] = []

    primary_path = problem_dir / f"{stem}.lean"
    primary_path.write_text(primary)
    written.append(str(primary_path))

    support_files = {rel: text for rel, text in lean_files.items() if rel != "Submission.lean"}
    if support_files:
        support_dir = problem_dir / f"{stem}_support"
        support_dir.mkdir(parents=True, exist_ok=True)
        for rel, text in support_files.items():
            path = support_dir / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            written.append(str(path))

    return written


def main() -> int:
    output_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUTPUT
    cache_dir = DEFAULT_CACHE
    submissions_dir = cache_dir / "lean-eval-submissions"

    ensure_clone(SUBMISSIONS_REPO, submissions_dir)
    checkout_ref(submissions_dir, "main")

    records = iter_public_records(submissions_dir / "results")
    manifest: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    print(f"Found {len(records)} public solved records.", flush=True)

    for index, entry in enumerate(records, start=1):
        record = entry["record"]
        label = f"{entry['problem_id']} / {entry['user']} / {entry['model']}"
        try:
            repo_dir = source_cache_dir(cache_dir, record)
            ensure_clone(source_url(record), repo_dir)
            checkout_ref(repo_dir, record["submission_ref"])
            if infer_submission_kind(record) == "gist":
                lean_files = lean_files_from_gist(repo_dir)
            else:
                lean_files = lean_files_from_repo(repo_dir, entry["problem_id"])
                if not lean_files:
                    lean_files = lean_files_from_gist(repo_dir)
            if not lean_files:
                raise RuntimeError("no Submission.lean or Submission/*.lean files found")
            written = write_entry(output_dir, entry, lean_files)
            manifest.append({**entry, "written_files": written})
            print(f"[{index}/{len(records)}] wrote {len(written)} file(s): {label}", flush=True)
        except Exception as exc:
            failures.append({"label": label, "error": str(exc)})
            print(f"[{index}/{len(records)}] skipped {label}: {exc}", file=sys.stderr, flush=True)

    (output_dir / "_manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    (output_dir / "_failures.json").write_text(json.dumps(failures, indent=2, ensure_ascii=False) + "\n")
    print(f"Downloaded {len(manifest)} records into {output_dir}.", flush=True)
    print(f"Failures: {len(failures)}", flush=True)
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
