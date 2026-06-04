from __future__ import annotations

from sqlalchemy import inspect, text

from scripts.env_file import load_env_file

load_env_file()

from app.database import Base, engine, ensure_models_imported


DROP_INDEXES = [
    "idx_preference_evaluations_user_node_a",
    "idx_preference_evaluations_user_node_b",
    "idx_nodes_question_id",
    "idx_nodes_proof_id",
    "idx_nodes_name_type",
]
PREFERENCE_EVALUATION_COLUMNS = [
    "mode",
    "entity_a_kind",
    "entity_b_kind",
    "entity_a_node_id",
    "entity_b_node_id",
]


def _drop_column_sql(table: str, column: str) -> str:
    if engine.dialect.name == "sqlite":
        return f"ALTER TABLE {table} DROP COLUMN {column}"
    return f"ALTER TABLE {table} DROP COLUMN IF EXISTS {column}"


def main() -> None:
    ensure_models_imported()

    with engine.begin() as conn:
        inspector = inspect(conn)
        tables = set(inspector.get_table_names())

        for index_name in DROP_INDEXES:
            conn.execute(text(f"DROP INDEX IF EXISTS {index_name}"))

        if "preference_evaluations" in tables:
            columns = {column["name"] for column in inspector.get_columns("preference_evaluations")}
            for column_name in PREFERENCE_EVALUATION_COLUMNS:
                if column_name in columns:
                    conn.execute(text(_drop_column_sql("preference_evaluations", column_name)))

        if "proofs" in tables:
            columns = {column["name"] for column in inspector.get_columns("proofs")}
            if "node_count" in columns:
                conn.execute(text(_drop_column_sql("proofs", "node_count")))

        conn.execute(text("DROP TABLE IF EXISTS nodes"))

    Base.metadata.create_all(bind=engine)
    print("Migrated database to proof-only comparisons.")


if __name__ == "__main__":
    main()
