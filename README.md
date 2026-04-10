# Proof Arena

Proof Arena is now structured as a deployable `FastAPI + PostgreSQL` app that serves the existing static frontend and stores both question data and evaluator responses in the backend database.

## What Changed

- Replaced the prototype `http.server` backend with FastAPI.
- Added SQLAlchemy-backed persistence with PostgreSQL support.
- Kept the current API surface:
  - `GET /api/health`
  - `GET /api/summary`
  - `GET /api/comparison?mode=option1|option2|option3|option4`
  - `POST /api/evaluations`
  - `GET /api/evaluations?limit=50`
- Kept `proof_arena/question_sets/` as the source format for import, but the deployed app now reads from the database after import/seed.

## Layout

```text
proof_arena/
  app/
    main.py
    database.py
    models.py
    parsing.py
    schemas.py
    services.py
  question_sets/
  scripts/
    import_question_sets.py
  static/
  Dockerfile
  docker-compose.yml
  requirements.txt
  server.py
```

## Local Development

### 1. Install dependencies

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r proof_arena/requirements.txt
```

### 2. Run with local SQLite

This is useful for development only.

```bash
python3 -m proof_arena.server
```

Then open:

```text
http://127.0.0.1:8000
```

### 3. Run with PostgreSQL

Set:

```bash
export PROOF_ARENA_DATABASE_URL='postgresql+psycopg://proof_arena:password@localhost:5432/proof_arena'
python3 -m proof_arena.server
```

## Docker Compose

This starts both PostgreSQL and the web app:

```bash
docker compose -f proof_arena/docker-compose.yml up --build
```

The app will be available at:

```text
http://127.0.0.1:8000
```

## Importing Question Sets

The app auto-seeds the database on startup when it finds an empty database and `PROOF_ARENA_AUTO_SEED=true`.

You can also re-import manually:

```bash
python3 -m proof_arena.scripts.import_question_sets
```

That command replaces existing questions, proofs, nodes, and saved evaluations with a fresh import from:

```text
proof_arena/question_sets/
```

## Environment Variables

- `PROOF_ARENA_DATABASE_URL`
  - Example: `postgresql+psycopg://proof_arena:password@db:5432/proof_arena`
- `PROOF_ARENA_HOST`
  - Default: `127.0.0.1`
- `PROOF_ARENA_PORT`
  - Default: `8000`
- `PROOF_ARENA_AUTO_SEED`
  - Default: `true`
- `PROOF_ARENA_CORS_ORIGINS`
  - Comma-separated origins, default `*`

See [`.env.example`](/Users/xutianruo/Documents/autoformalization_benchmark/proof_arena/.env.example).

## Remote Deployment

For a public deployment you need four pieces:

1. An app host for the FastAPI server.
2. A managed PostgreSQL database.
3. Environment variables for the database URL and allowed origins.
4. A reverse proxy or managed platform that exposes HTTPS.

The simplest production path is:

1. Put this repo on GitHub.
2. Deploy the app container to Railway, Render, Fly.io, or a VPS with Docker.
3. Create a managed PostgreSQL instance on the same platform.
4. Set `PROOF_ARENA_DATABASE_URL` to the managed database connection string.
5. Set `PROOF_ARENA_CORS_ORIGINS` to your deployed frontend domain.
6. Run the import once if auto-seed is disabled or if you want a controlled refresh.

## Production Notes

- Do not expose Postgres directly to the public internet unless you have a good reason.
- Put the FastAPI app behind HTTPS.
- Add authentication before collecting real user data from external users.
- If you expect schema evolution, add Alembic next rather than editing tables manually.
