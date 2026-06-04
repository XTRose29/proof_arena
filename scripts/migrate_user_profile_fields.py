from __future__ import annotations

from sqlalchemy import inspect, text

from scripts.env_file import load_env_file

load_env_file()

from app.database import Base, engine, ensure_models_imported


USER_PROFILE_COLUMNS = {
    "affiliation": "TEXT NOT NULL DEFAULT ''",
    "experience_level": "TEXT NOT NULL DEFAULT ''",
}
EVALUATION_PROFILE_COLUMNS = [
    "evaluator_affiliation",
    "evaluator_experience_level",
]


def _drop_column_sql(table: str, column: str) -> str:
    if engine.dialect.name == "sqlite":
        return f"ALTER TABLE {table} DROP COLUMN {column}"
    return f"ALTER TABLE {table} DROP COLUMN IF EXISTS {column}"


def _add_user_columns(conn: object, existing_columns: set[str]) -> None:
    for column_name, column_definition in USER_PROFILE_COLUMNS.items():
        if column_name not in existing_columns:
            conn.execute(text(f"ALTER TABLE users ADD COLUMN {column_name} {column_definition}"))


def _copy_evaluation_profile_fields(conn: object, evaluation_columns: set[str]) -> None:
    if not set(EVALUATION_PROFILE_COLUMNS).issubset(evaluation_columns):
        return

    rows = conn.execute(
        text(
            """
            SELECT user_id, evaluator_affiliation, evaluator_experience_level
            FROM preference_evaluations
            ORDER BY id DESC
            """
        )
    ).mappings()

    seen_users: set[int] = set()
    for row in rows:
        user_id = row["user_id"]
        if user_id in seen_users:
            continue
        seen_users.add(user_id)
        conn.execute(
            text(
                """
                UPDATE users
                SET
                  affiliation = CASE
                    WHEN TRIM(COALESCE(affiliation, '')) = '' THEN :affiliation
                    ELSE affiliation
                  END,
                  experience_level = CASE
                    WHEN TRIM(COALESCE(experience_level, '')) = '' THEN :experience_level
                    ELSE experience_level
                  END
                WHERE id = :user_id
                """
            ),
            {
                "user_id": user_id,
                "affiliation": (row["evaluator_affiliation"] or "").strip(),
                "experience_level": (row["evaluator_experience_level"] or "").strip(),
            },
        )


def main() -> None:
    ensure_models_imported()

    with engine.begin() as conn:
        inspector = inspect(conn)
        tables = set(inspector.get_table_names())
        if "users" not in tables:
            Base.metadata.create_all(bind=conn)
            inspector = inspect(conn)

        user_columns = {column["name"] for column in inspector.get_columns("users")}
        _add_user_columns(conn, user_columns)

        tables = set(inspector.get_table_names())
        if "preference_evaluations" in tables:
            evaluation_columns = {column["name"] for column in inspector.get_columns("preference_evaluations")}
            _copy_evaluation_profile_fields(conn, evaluation_columns)
            for column_name in EVALUATION_PROFILE_COLUMNS:
                if column_name in evaluation_columns:
                    conn.execute(text(_drop_column_sql("preference_evaluations", column_name)))

    Base.metadata.create_all(bind=engine)
    print("Migrated affiliation and Lean experience fields to users.")


if __name__ == "__main__":
    main()
