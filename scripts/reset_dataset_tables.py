from __future__ import annotations

from sqlalchemy import text

from scripts.env_file import load_env_file

load_env_file()

from app.database import Base, SessionLocal, engine, ensure_models_imported


def main() -> None:
    ensure_models_imported()
    Base.metadata.create_all(bind=engine)

    session = SessionLocal()
    try:
        session.execute(text("DELETE FROM preference_votes"))
        session.execute(text("DELETE FROM preference_evaluations"))
        session.execute(text("DELETE FROM nodes"))
        session.execute(text("DELETE FROM proofs"))
        session.execute(text("DELETE FROM questions"))
        session.commit()
    finally:
        session.close()

    print("Cleared dataset tables: questions, proofs, nodes, preference_evaluations, preference_votes")


if __name__ == "__main__":
    main()
