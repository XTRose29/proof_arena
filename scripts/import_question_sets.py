from __future__ import annotations

from scripts.env_file import load_env_file

load_env_file()

from app.database import Base, SessionLocal, engine, ensure_models_imported
from app.services import sync_question_sets


def main() -> None:
    ensure_models_imported()
    Base.metadata.create_all(bind=engine)
    session = SessionLocal()
    try:
        stats = sync_question_sets(session)
    finally:
        session.close()
    print(
        "Synchronized question sets: "
        f"{stats['questions']} questions, {stats['proofs']} proofs"
    )


if __name__ == "__main__":
    main()
