from __future__ import annotations

from sqlalchemy import inspect, text

from scripts.env_file import load_env_file

load_env_file()

from app.database import Base, engine, ensure_models_imported


CRITERION_CHECK = "criterion IN ('reuse', 'naming', 'documentation', 'proof_quality', 'overall')"
PREFERENCE_CHECK = (
    "preference IN ('a_way_better', 'a_better', 'no_difference', 'b_better', 'b_way_better')"
)


def _sqlite_table_sql() -> str:
    return f"""
    CREATE TABLE preference_votes (
        id INTEGER NOT NULL,
        evaluation_id INTEGER NOT NULL,
        criterion TEXT NOT NULL,
        preference TEXT NOT NULL,
        created_at TEXT NOT NULL,
        PRIMARY KEY (id),
        CONSTRAINT ck_preference_votes_criterion CHECK ({CRITERION_CHECK}),
        CONSTRAINT ck_preference_votes_preference CHECK ({PREFERENCE_CHECK}),
        FOREIGN KEY(evaluation_id) REFERENCES preference_evaluations (id) ON DELETE CASCADE
    )
    """


def main() -> None:
    ensure_models_imported()

    if engine.dialect.name != "sqlite":
        with engine.begin() as conn:
            inspector = inspect(conn)
            if "preference_votes" not in inspector.get_table_names():
                Base.metadata.create_all(bind=conn)
                print("Created preference vote table with reuse rubric criteria.")
                return

            conn.execute(text("ALTER TABLE preference_votes DROP CONSTRAINT IF EXISTS ck_preference_votes_criterion"))
            conn.execute(
                text(
                    """
                    UPDATE preference_votes
                    SET criterion = CASE criterion
                        WHEN 'clarity' THEN 'documentation'
                        WHEN 'conciseness' THEN 'reuse'
                        WHEN 'idiomatic_structure' THEN 'proof_quality'
                        ELSE criterion
                    END
                    WHERE criterion IN ('clarity', 'conciseness', 'idiomatic_structure')
                    """
                )
            )
            conn.execute(
                text(
                    f"""
                    ALTER TABLE preference_votes
                    ADD CONSTRAINT ck_preference_votes_criterion CHECK ({CRITERION_CHECK})
                    """
                )
            )
        print("Migrated preference votes to reuse rubric criteria.")
        return

    with engine.begin() as conn:
        inspector = inspect(conn)
        if "preference_votes" not in inspector.get_table_names():
            Base.metadata.create_all(bind=conn)
            print("Created preference vote table with reuse rubric criteria.")
            return

        create_sql = conn.execute(
            text("SELECT sql FROM sqlite_master WHERE type = 'table' AND name = 'preference_votes'")
        ).scalar_one()
        if CRITERION_CHECK in create_sql:
            print("Preference vote table already uses reuse rubric criteria.")
            return

        conn.exec_driver_sql("PRAGMA foreign_keys=OFF")
        conn.execute(text("DROP INDEX IF EXISTS idx_preference_votes_evaluation_id"))
        conn.execute(text("ALTER TABLE preference_votes RENAME TO preference_votes_old"))
        conn.execute(text(_sqlite_table_sql()))
        conn.execute(
            text(
                """
                INSERT INTO preference_votes (id, evaluation_id, criterion, preference, created_at)
                SELECT
                    id,
                    evaluation_id,
                    CASE criterion
                        WHEN 'clarity' THEN 'documentation'
                        WHEN 'conciseness' THEN 'reuse'
                        WHEN 'idiomatic_structure' THEN 'proof_quality'
                        ELSE criterion
                    END AS criterion,
                    preference,
                    created_at
                FROM preference_votes_old
                WHERE criterion IN (
                    'clarity',
                    'conciseness',
                    'idiomatic_structure',
                    'reuse',
                    'naming',
                    'documentation',
                    'proof_quality',
                    'overall'
                )
                """
            )
        )
        conn.execute(text("DROP TABLE preference_votes_old"))
        conn.execute(text("CREATE INDEX idx_preference_votes_evaluation_id ON preference_votes (evaluation_id)"))
        conn.exec_driver_sql("PRAGMA foreign_keys=ON")

    print("Migrated preference votes to reuse rubric criteria.")


if __name__ == "__main__":
    main()
