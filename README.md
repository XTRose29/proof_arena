# Proof Arena

Proof Arena is a deployable `FastAPI + PostgreSQL` app for randomized A/B comparison of Lean proofs, model-generated meta-reviews, Google-based evaluator login, and persistent storage of the resulting judgments.

The current production deployment uses:

- Vercel for the web app and API
- Neon PostgreSQL for persistent storage

## What The App Does

- Parses Lean files from `question_sets/`
- Stores parsed questions and proofs in PostgreSQL
- Serves the frontend and API from the same FastAPI app
- Loads randomized same-question proof pairs from the database
- Saves evaluator metadata and A/B preference submissions into the database
- Pre-generates two independent rubric-based evaluations for one featured database proof
- Saves each evaluator's A/B/tie choice for that featured pair

Current API surface:

- `GET /api/health`
- `POST /api/auth/register`
- `POST /api/auth/login`
- `POST /api/auth/google`
- `GET /api/auth/config`
- `GET /api/me`
- `GET /api/summary`
- `GET /api/comparison`
- `POST /api/evaluations`
- `GET /api/evaluations?limit=50`
- `GET /api/meta-review/proofs`
- `GET /api/meta-review/featured`
- `POST /api/meta-review/generate`
- `POST /api/meta-review/{session_id}/selection`

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
    dataset_counts.py
    download_lean_eval_dataset_git.py
    export_backend_database.py
    import_question_sets.py
    migrate_proof_only_schema.py
    migrate_user_profile_fields.py
    pregenerate_featured_meta_review.py
  static/
  backend_database_export/
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

1. The sync script reads Lean files from `question_sets/`
2. Parsed records are inserted or updated in PostgreSQL
3. The frontend reads dataset information through the API
4. The API serves randomized A/B comparisons from the database

### User submissions

When a user submits an evaluation:

1. The evaluator logs in with Google
2. The frontend collects evaluator metadata at the top of the page
3. The evaluator scores each criterion using A/B preference choices
4. The frontend sends `POST /api/evaluations`
5. The backend writes to:
   - `users`
   - `auth_tokens`
   - `preference_evaluations`
   - `preference_votes`

So evaluator metadata, A/B assignments, and preference scores are stored in PostgreSQL, not in local files.

### Current database tables

The current backend schema is proof-only:

- `questions`
- `proofs`
- `preference_evaluations`
- `preference_votes`
- `users`
- `auth_tokens`
- `meta_review_sessions`
- `meta_review_votes`

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
- `PROOF_ARENA_GOOGLE_CLIENT_ID`
  - Google OAuth web client ID used by the frontend sign-in button and backend ID token verification
- `ANTHROPIC_API_KEY`
  - API key used to generate the two meta-review evaluations
- `CLAUDE_MODEL`
  - Claude model identifier used for both independent evaluation calls
- `ANTHROPIC_BASE_URL`
  - Optional Anthropic-compatible API base URL; defaults to `https://api.anthropic.com`

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
export PROOF_ARENA_GOOGLE_CLIENT_ID='your-google-web-client-id.apps.googleusercontent.com'
export ANTHROPIC_API_KEY='your-api-key'
export CLAUDE_MODEL='your-claude-model'
```

### 3. Run the app

```bash
python3 -m server
```

Then open:

```text
http://127.0.0.1:8000
```

## Database Operations

### Sync question sets

To sync `question_sets/` into PostgreSQL:

```bash
python3 -m scripts.import_question_sets
```

This command:

- creates tables if needed
- parses Lean files under `question_sets/`
- adds new questions/proofs
- updates changed questions/proofs
- removes dataset records that no longer exist locally
- preserves saved user evaluations and votes

Use it when:

- setting up a new database
- refreshing the dataset after editing `question_sets/`

For an older database that still has node-comparison tables or columns, run:

```bash
python3 -m scripts.migrate_proof_only_schema
```

To move evaluator affiliation and Lean experience fields from evaluations to users, run:

```bash
python3 -m scripts.migrate_user_profile_fields
```

To generate the single featured meta-review shown when users open the Meta Reviewer tab, run:

```bash
python3 -m scripts.pregenerate_featured_meta_review
```

### Export backend data

To export the configured backend database into repo-local JSON files:

```bash
python3 -m scripts.export_backend_database
```

The export is written to `backend_database_export/`. Auth tokens and password hashes are redacted by default; pass `--include-sensitive` only for a private backup.

The export folder contains:

- `_manifest.json`
- `_schema.json`
- one JSON file per database table under `tables/`

## Deployment

### Vercel

This repo is configured for Vercel with [vercel.json](/Users/xutianruo/Documents/proof_arena/vercel.json) and a root-level [server.py](/Users/xutianruo/Documents/proof_arena/server.py) entrypoint.

For Vercel, set these environment variables in Project Settings:

- `PROOF_ARENA_DATABASE_URL`
- `PROOF_ARENA_AUTO_SEED=false`
- `PROOF_ARENA_CORS_ORIGINS`
- `PROOF_ARENA_GOOGLE_CLIENT_ID`
- `ANTHROPIC_API_KEY`
- `CLAUDE_MODEL`
- `ANTHROPIC_BASE_URL` (only when using a compatible proxy or gateway)

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
- If the database is empty, the site will show `0 questions, 0 proofs`
- After importing `question_sets/`, the UI will start serving real comparisons

## Notes

- Do not commit `.env`
- Do not expose PostgreSQL directly to the public internet unless necessary
- If you expect schema changes, add Alembic migrations instead of hand-editing tables
- Google Sign-In must be configured before evaluators can submit preferences
