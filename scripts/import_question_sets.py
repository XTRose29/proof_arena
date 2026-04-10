from __future__ import annotations

from proof_arena.app.database import Base, SessionLocal, engine
from proof_arena.app.services import import_question_sets


def main() -> None:
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
