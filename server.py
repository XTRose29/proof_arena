from __future__ import annotations

import os

import uvicorn


def main() -> None:
    host = os.environ.get("PROOF_ARENA_HOST", "127.0.0.1")
    port = int(os.environ.get("PROOF_ARENA_PORT", "8000"))
    uvicorn.run("proof_arena.app.main:app", host=host, port=port, reload=False)


if __name__ == "__main__":
    main()
