from __future__ import annotations

import re
from pathlib import Path

from .config import QUESTION_SETS_DIR, REPO_ROOT


CANONICAL_SUFFIX_RE = re.compile(
    r"(_codex[\w\.\-]*|_claude[\w\.\-]*|_copy[\w\.\-]*| copy|_app->[\w\.\-]+)$",
    re.IGNORECASE,
)


def canonical_question_key(path: Path) -> str:
    stem = path.stem.lower().replace(" ", "_")
    stem = CANONICAL_SUFFIX_RE.sub("", stem)
    if stem.endswith("_b"):
        stem = stem[:-2]
    stem = re.sub(r"__+", "_", stem).strip("_")
    return stem or path.stem.lower()


def humanize_slug(slug: str) -> str:
    parts = [part for part in re.split(r"[_\-]+", slug) if part]
    return " ".join(part.capitalize() for part in parts) or slug


def question_set_lean_files() -> list[Path]:
    if not QUESTION_SETS_DIR.exists():
        return []
    return sorted(path for path in QUESTION_SETS_DIR.rglob("*.lean") if path.is_file())


def source_lean_files() -> list[Path]:
    return question_set_lean_files()


def question_key_for_path(path: Path) -> str:
    if path.is_relative_to(QUESTION_SETS_DIR):
        relative = path.relative_to(QUESTION_SETS_DIR)
        if len(relative.parts) >= 2:
            return relative.parts[0].strip().lower().replace(" ", "_")
    return canonical_question_key(path)


def guess_author(path: Path) -> str | None:
    if path.is_relative_to(QUESTION_SETS_DIR):
        stem = path.stem
        normalized = CANONICAL_SUFFIX_RE.sub("", stem)
        normalized = normalized.rstrip("_ ").lower()
        if normalized.endswith("_b"):
            normalized = normalized[:-2]
        if normalized and normalized != question_key_for_path(path):
            return stem
        return None
    parts = path.relative_to(REPO_ROOT).parts
    if not parts:
        return None
    first = parts[0]
    known_group_dirs = {"data", "src", "AutoformalizationBenchmark"}
    return None if first in known_group_dirs else first
