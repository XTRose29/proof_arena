from __future__ import annotations

from app.database import Base, SessionLocal, engine, ensure_models_imported
from app.services import import_question_sets


def main() -> None:
    ensure_models_imported()
    Base.metadata.create_all(bind=engine)
    session = SessionLocal()
    try:
        stats = import_question_sets(session, replace_existing=True)
    finally:
        session.close()
    print(
        "Imported question sets: "
        f"{stats['questions']} questions, {stats['proofs']} proofs, {stats['nodes']} nodes"
    )


if __name__ == "__main__":
    main()
