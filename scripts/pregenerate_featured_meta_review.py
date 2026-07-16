from __future__ import annotations

from scripts.env_file import load_env_file

load_env_file()

from app.database import Base, SessionLocal, engine, ensure_models_imported
from app.services import build_featured_meta_review


def main() -> None:
    ensure_models_imported()
    Base.metadata.create_all(bind=engine)
    session = SessionLocal()
    try:
        review = build_featured_meta_review(session)
    finally:
        session.close()

    print(f"Featured meta review ready: session {review['sessionId']} for {review['source']['title']}")


if __name__ == "__main__":
    main()
