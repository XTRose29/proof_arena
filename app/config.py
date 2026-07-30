from __future__ import annotations

import os
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
REPO_ROOT = ROOT.parent
STATIC_DIR = ROOT / "static"
QUESTION_SETS_DIR = ROOT / "question_sets"
LOCAL_DB_PATH = ROOT / "proof_arena.db"
GOOGLE_VERIFICATION_FILE = STATIC_DIR / "googlef32254fd0dfa1cb9.html"


def database_url() -> str:
    return os.environ.get("PROOF_ARENA_DATABASE_URL", f"sqlite:///{LOCAL_DB_PATH}")


def cors_origins() -> list[str]:
    raw = os.environ.get("PROOF_ARENA_CORS_ORIGINS", "*")
    return [item.strip() for item in raw.split(",") if item.strip()]


def auto_seed_enabled() -> bool:
    return os.environ.get("PROOF_ARENA_AUTO_SEED", "true").lower() in {"1", "true", "yes", "on"}


def google_client_id() -> str:
    return os.environ.get("PROOF_ARENA_GOOGLE_CLIENT_ID", "").strip()


def anthropic_api_key() -> str:
    return os.environ.get("ANTHROPIC_API_KEY", "").strip()


def anthropic_base_url() -> str:
    return os.environ.get("ANTHROPIC_BASE_URL", "https://api.anthropic.com").rstrip("/")


def claude_model() -> str:
    return os.environ.get("CLAUDE_MODEL", "").strip()


def cornell_gateway_api_key() -> str:
    return os.environ.get("CORNELL_AI_GATEWAY_API_KEY", "").strip() or anthropic_api_key()


def cornell_gateway_base_url() -> str:
    configured = os.environ.get("CORNELL_AI_GATEWAY_BASE_URL", "").strip().rstrip("/")
    if configured:
        return configured
    existing_gateway = anthropic_base_url()
    return existing_gateway if existing_gateway != "https://api.anthropic.com" else ""


def cornell_gateway_model() -> str:
    return os.environ.get("CORNELL_AI_GATEWAY_MODEL", "gpt-5.4-mini").strip()
