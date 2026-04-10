# Proof Arena

Proof Arena is a deployable `FastAPI + PostgreSQL` app for randomized A/B comparison of Lean proofs or proof nodes, lightweight evaluator login, and persistent storage of both the dataset and submitted preferences.

The current production deployment uses:

- Vercel for the web app and API
- Neon PostgreSQL for persistent storage

## What The App Does

- Parses Lean files from `question_sets/`
- Stores parsed questions, proofs, and nodes in PostgreSQL
- Serves the frontend and API from the same FastAPI app
- Loads randomized comparison pairs from the database
- Saves evaluator metadata and A/B preference submissions into the database

Current API surface:

- `GET /api/health`
- `POST /api/auth/register`
- `POST /api/auth/login`
- `GET /api/me`
- `GET /api/summary`
- `GET /api/comparison`
- `POST /api/evaluations`
- `GET /api/evaluations?limit=50`

## Repository Layout

```text
proof_arena/
  app/
    config.py
    database.py
    main.py
    models.py
    parsing.py
    schemas.py
    services.py
  question_sets/
  scripts/
    import_question_sets.py
  static/
  .env.example
  docker-compose.yml
  Dockerfile
  requirements.txt
  server.py
  vercel.json
```

## Data Flow

### Question data

Lean files in `question_sets/` are not read directly by the webpage at request time.

Instead:

1. The sync script parses files from `question_sets/`
2. Parsed records are inserted or updated in PostgreSQL
3. The frontend reads dataset information through the API
4. The API serves randomized A/B comparisons from the database

### User submissions

When a user submits an evaluation:

1. The evaluator logs in or creates an account
2. The frontend collects evaluator metadata at the top of the page
3. The evaluator scores each criterion using A/B preference choices
4. The frontend sends `POST /api/evaluations`
5. The backend writes to:
   - `users`
   - `auth_tokens`
   - `preference_evaluations`
   - `preference_votes`

So evaluator metadata, A/B assignments, and preference scores are stored in PostgreSQL, not in local files.

## Environment Variables

Required:

- `PROOF_ARENA_DATABASE_URL`
  - Example:
    `postgresql+psycopg://user:password@host:5432/dbname?sslmode=require`

Optional:

- `PROOF_ARENA_HOST`
  - Default: `127.0.0.1`
- `PROOF_ARENA_PORT`
  - Default: `8000`
- `PROOF_ARENA_AUTO_SEED`
  - Default: `false`
- `PROOF_ARENA_CORS_ORIGINS`
  - Default: `*`

See [`.env.example`](/Users/xutianruo/Documents/proof_arena/.env.example).

## Local Development

### 1. Create a virtual environment

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

### 2. Set environment variables

For local PostgreSQL:

```bash
export PROOF_ARENA_DATABASE_URL='postgresql+psycopg://proof_arena:password@localhost:5432/proof_arena'
export PROOF_ARENA_AUTO_SEED=false
```

### 3. Run the app

```bash
python3 -m server
```

Then open:

```text
http://127.0.0.1:8000
```

## Syncing Question Sets

To sync `question_sets/` into PostgreSQL:

```bash
python3 -m scripts.import_question_sets
```

This command:

- creates tables if needed
- parses Lean files under `question_sets/`
- adds new questions/proofs/nodes
- updates changed questions/proofs/nodes
- removes dataset records that no longer exist locally
- preserves saved user evaluations and votes

Use it when:

- setting up a new database
- refreshing the dataset after editing `question_sets/`

## Deployment

### Vercel

This repo is configured for Vercel with [vercel.json](/Users/xutianruo/Documents/proof_arena/vercel.json) and a root-level [server.py](/Users/xutianruo/Documents/proof_arena/server.py) entrypoint.

For Vercel, set these environment variables in Project Settings:

- `PROOF_ARENA_DATABASE_URL`
- `PROOF_ARENA_AUTO_SEED=false`
- `PROOF_ARENA_CORS_ORIGINS`

Recommended:

- keep `PROOF_ARENA_AUTO_SEED=false` in production
- run imports intentionally instead of during cold start

### Neon PostgreSQL

Use a Neon connection string in SQLAlchemy form:

```text
postgresql+psycopg://user:password@host/dbname?sslmode=require
```

If you use a pooled Neon connection string, keep the parameters Neon provides.

## Current Production Behavior

- The website reads dataset snapshots and randomized comparison data from PostgreSQL
- Submitted evaluations are saved into PostgreSQL with evaluator identity and metadata
- If the database is empty, the site will show `0 questions, 0 proofs, 0 nodes`
- After importing `question_sets/`, the UI will start serving real comparisons

## Notes

- Do not commit `.env`
- Do not expose PostgreSQL directly to the public internet unless necessary
- If you expect schema changes, add Alembic migrations instead of hand-editing tables
- If this will be used by external evaluators, add authentication before relying on it for real collection
