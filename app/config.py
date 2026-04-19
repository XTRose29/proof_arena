from __future__ import annotations

import os
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
REPO_ROOT = ROOT.parent
STATIC_DIR = ROOT / "static"
QUESTION_SETS_DIR = ROOT / "question_sets"
LOCAL_DB_PATH = ROOT / "proof_arena.db"


def database_url() -> str:
    return os.environ.get("PROOF_ARENA_DATABASE_URL", f"sqlite:///{LOCAL_DB_PATH}")


def cors_origins() -> list[str]:
    raw = os.environ.get("PROOF_ARENA_CORS_ORIGINS", "*")
    return [item.strip() for item in raw.split(",") if item.strip()]


def auto_seed_enabled() -> bool:
    return os.environ.get("PROOF_ARENA_AUTO_SEED", "true").lower() in {"1", "true", "yes", "on"}


def google_client_id() -> str:
    return os.environ.get("PROOF_ARENA_GOOGLE_CLIENT_ID", "").strip()
