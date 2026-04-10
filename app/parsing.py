from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

from .config import QUESTION_SETS_DIR, REPO_ROOT, ROOT


NODE_BLOCK_RE = re.compile(r"/-!\s*NODE(?P<meta>.*?)-/\s*", re.DOTALL)
META_FIELD_RE = re.compile(r"\\(?P<key>[A-Za-z_]+):\s*(?P<value>.*)")
DECL_RE = re.compile(r"^\s*(theorem|lemma|def|structure|class|inductive|abbrev)\s+([^\s(:{]+)", re.MULTILINE)
CANONICAL_SUFFIX_RE = re.compile(
    r"(_codex[\w\.\-]*|_claude[\w\.\-]*|_copy[\w\.\-]*| copy|_app->[\w\.\-]+)$",
    re.IGNORECASE,
)


@dataclass
class ParsedNode:
    name: str
    node_type: str
    inputs: list[str]
    natural: str
    nl_proof: str
    code: str
    start_line: int
    end_line: int
    ordinal: int
    declaration_kind: str | None
    declaration_name: str | None


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


def parse_meta(meta_block: str) -> dict[str, str]:
    result: dict[str, str] = {}
    current_key: str | None = None
    buffer: list[str] = []
    for raw_line in meta_block.splitlines():
        line = raw_line.rstrip()
        field_match = META_FIELD_RE.match(line.strip())
        if field_match:
            if current_key is not None:
                result[current_key] = "\n".join(buffer).strip()
            current_key = field_match.group("key")
            buffer = [field_match.group("value").strip()]
        elif current_key is not None:
            stripped = line.strip()
            if stripped:
                buffer.append(stripped)
            else:
                buffer.append("")
    if current_key is not None:
        result[current_key] = "\n".join(buffer).strip()
    return result


def parse_inputs(value: str) -> list[str]:
    value = value.strip()
    if not value:
        return []
    try:
        parsed = json.loads(value)
        if isinstance(parsed, list):
            return [str(item) for item in parsed]
    except json.JSONDecodeError:
        pass
    return [item.strip() for item in value.split(",") if item.strip()]


def find_declaration(code: str) -> tuple[str | None, str | None]:
    match = DECL_RE.search(code)
    if not match:
        return None, None
    return match.group(1), match.group(2)


def parse_nodes(content: str) -> list[ParsedNode]:
    matches = list(NODE_BLOCK_RE.finditer(content))
    nodes: list[ParsedNode] = []
    for index, match in enumerate(matches):
        code_start = match.end()
        code_end = matches[index + 1].start() if index + 1 < len(matches) else len(content)
        meta = parse_meta(match.group("meta"))
        code = content[code_start:code_end].strip("\n")
        decl_kind, decl_name = find_declaration(code)
        start_line = content.count("\n", 0, code_start) + 1
        end_line = content.count("\n", 0, code_end) + 1
        nodes.append(
            ParsedNode(
                name=meta.get("name", f"Node {index + 1}"),
                node_type=meta.get("type", "unknown"),
                inputs=parse_inputs(meta.get("inputs", "")),
                natural=meta.get("natural", ""),
                nl_proof=meta.get("NL_proof", ""),
                code=code.strip(),
                start_line=start_line,
                end_line=end_line,
                ordinal=index + 1,
                declaration_kind=decl_kind,
                declaration_name=decl_name,
            )
        )
    return nodes


def question_set_lean_files() -> list[Path]:
    if not QUESTION_SETS_DIR.exists():
        return []
    return sorted(path for path in QUESTION_SETS_DIR.rglob("*.lean") if path.is_file())


def inferred_repo_lean_files() -> list[Path]:
    files: list[Path] = []
    for path in REPO_ROOT.rglob("*.lean"):
        if path.is_relative_to(ROOT):
            continue
        try:
            content = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if "NODE" in content:
            files.append(path)
    return sorted(files)


def source_lean_files() -> list[Path]:
    question_set_files = question_set_lean_files()
    if question_set_files:
        return question_set_files
    return inferred_repo_lean_files()


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
