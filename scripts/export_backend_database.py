from __future__ import annotations

import argparse
import json
from datetime import date, datetime, timezone
from decimal import Decimal
from pathlib import Path
from typing import Any

from sqlalchemy import inspect, text

from scripts.env_file import load_env_file

load_env_file()

from app.database import engine


DEFAULT_OUTPUT_DIR = Path("backend_database_export")
SENSITIVE_FIELDS = {
    "auth_tokens": {"token"},
    "meta_review_drafts": {"reason"},
    "meta_review_sessions": {"selection_reason"},
    "meta_review_votes": {"reason"},
    "preference_evaluations": {"evaluator_display_name", "general_comment"},
    "users": {
        "affiliation",
        "display_name",
        "email",
        "experience_level",
        "password_hash",
        "password_salt",
    },
}
PREFERRED_TABLE_ORDER = [
    "questions",
    "proofs",
    "preference_evaluations",
    "preference_votes",
    "users",
    "auth_tokens",
]


def json_default(value: Any) -> str:
    if isinstance(value, datetime):
        return value.isoformat()
    if isinstance(value, date):
        return value.isoformat()
    if isinstance(value, Decimal):
        return str(value)
    if isinstance(value, bytes):
        return value.hex()
    return str(value)


def table_sort_key(table_name: str) -> tuple[int, str]:
    try:
        return PREFERRED_TABLE_ORDER.index(table_name), table_name
    except ValueError:
        return len(PREFERRED_TABLE_ORDER), table_name


def redact_row(table_name: str, row: dict[str, Any], include_sensitive: bool) -> dict[str, Any]:
    if include_sensitive:
        return row
    redacted = dict(row)
    for field in SENSITIVE_FIELDS.get(table_name, set()):
        if field in redacted and redacted[field] is not None:
            redacted[field] = "[REDACTED]"
    return redacted


def table_order_clause(inspector: Any, table_name: str) -> str:
    primary_key = inspector.get_pk_constraint(table_name).get("constrained_columns") or []
    if not primary_key:
        return ""
    preparer = engine.dialect.identifier_preparer
    quoted_columns = ", ".join(preparer.quote(column_name) for column_name in primary_key)
    return f" ORDER BY {quoted_columns}"


def export_table(conn: Any, inspector: Any, table_name: str, output_dir: Path, include_sensitive: bool) -> int:
    preparer = engine.dialect.identifier_preparer
    quoted_table = preparer.quote(table_name)
    rows = conn.execute(text(f"SELECT * FROM {quoted_table}{table_order_clause(inspector, table_name)}")).mappings().all()
    payload = [redact_row(table_name, dict(row), include_sensitive) for row in rows]
    path = output_dir / "tables" / f"{table_name}.json"
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False, default=json_default) + "\n", encoding="utf-8")
    return len(payload)


def schema_payload(inspector: Any, table_names: list[str]) -> dict[str, Any]:
    schema: dict[str, Any] = {}
    for table_name in table_names:
        schema[table_name] = {
            "columns": [
                {
                    "name": column["name"],
                    "type": str(column["type"]),
                    "nullable": column["nullable"],
                    "default": column.get("default"),
                    "primary_key": bool(column.get("primary_key")),
                }
                for column in inspector.get_columns(table_name)
            ],
            "primary_key": inspector.get_pk_constraint(table_name).get("constrained_columns", []),
            "foreign_keys": inspector.get_foreign_keys(table_name),
            "indexes": inspector.get_indexes(table_name),
        }
    return schema


def write_manifest(output_dir: Path, table_counts: dict[str, int], include_sensitive: bool) -> None:
    redacted_fields = {
        table_name: sorted(fields)
        for table_name, fields in SENSITIVE_FIELDS.items()
        if table_name in table_counts and not include_sensitive
    }
    manifest = {
        "exported_at": datetime.now(timezone.utc).isoformat(),
        "database_dialect": engine.dialect.name,
        "output_dir": str(output_dir),
        "include_sensitive": include_sensitive,
        "redacted_fields": redacted_fields,
        "tables": table_counts,
    }
    (output_dir / "_manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, default=json_default) + "\n",
        encoding="utf-8",
    )


def export_database(output_dir: Path, include_sensitive: bool) -> dict[str, int]:
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "tables").mkdir(parents=True, exist_ok=True)

    with engine.begin() as conn:
        inspector = inspect(conn)
        table_names = sorted(inspector.get_table_names(), key=table_sort_key)
        table_counts = {
            table_name: export_table(conn, inspector, table_name, output_dir, include_sensitive)
            for table_name in table_names
        }
        (output_dir / "_schema.json").write_text(
            json.dumps(schema_payload(inspector, table_names), indent=2, ensure_ascii=False, default=json_default) + "\n",
            encoding="utf-8",
        )

    write_manifest(output_dir, table_counts, include_sensitive)
    return table_counts


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Export the configured backend database into JSON files.")
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help=f"Output folder inside the repo. Default: {DEFAULT_OUTPUT_DIR}",
    )
    parser.add_argument(
        "--include-sensitive",
        action="store_true",
        help="Include auth tokens and password hashes instead of redacting them.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    table_counts = export_database(args.output, args.include_sensitive)
    counts = ", ".join(f"{table}: {count}" for table, count in table_counts.items())
    print(f"Exported backend database to {args.output}: {counts}")


if __name__ == "__main__":
    main()
