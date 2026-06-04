from __future__ import annotations

from sqlalchemy import text

from scripts.env_file import load_env_file

load_env_file()

from app.database import SessionLocal, ensure_models_imported


TABLES = [
    "questions",
    "proofs",
    "preference_evaluations",
    "preference_votes",
    "users",
    "auth_tokens",
]


def main() -> None:
    ensure_models_imported()
    session = SessionLocal()
    try:
        for table in TABLES:
            count = session.execute(text(f"SELECT COUNT(*) FROM {table}")).scalar_one()
            print(f"{table}: {count}")
    finally:
        session.close()


if __name__ == "__main__":
    main()
