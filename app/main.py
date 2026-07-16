from __future__ import annotations

from pathlib import Path

from fastapi import Depends, FastAPI, Header, HTTPException, Query, Request
from fastapi.exceptions import RequestValidationError
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from sqlalchemy.orm import Session

from .config import GOOGLE_VERIFICATION_FILE, STATIC_DIR, auto_seed_enabled, cors_origins, google_client_id
from .database import Base, SessionLocal, engine, ensure_models_imported, get_db
from .schemas import (
    GoogleAuthRequest,
    LoginRequest,
    MetaReviewGenerateRequest,
    MetaReviewSelectionRequest,
    PreferenceEvaluationCreate,
    RegisterRequest,
    UpdateProfileRequest,
)
from .services import (
    auth_user_from_token,
    build_random_comparison,
    build_meta_review,
    database_proof_options,
    create_user,
    evaluations_payload,
    featured_meta_review,
    init_database,
    login_user_with_google,
    login_user,
    save_preference_evaluation,
    save_meta_review_selection,
    serialize_user,
    summary_payload,
    update_user_profile,
)


app = FastAPI(title="Proof Arena API")
app.add_middleware(
    CORSMiddleware,
    allow_origins=cors_origins(),
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.exception_handler(HTTPException)
async def http_exception_handler(_: Request, exc: HTTPException) -> JSONResponse:
    return JSONResponse(status_code=exc.status_code, content={"error": str(exc.detail)})


@app.exception_handler(RequestValidationError)
async def validation_exception_handler(_: Request, exc: RequestValidationError) -> JSONResponse:
    return JSONResponse(status_code=422, content={"error": str(exc)})


@app.on_event("startup")
def on_startup() -> None:
    ensure_models_imported()
    Base.metadata.create_all(bind=engine)
    if auto_seed_enabled():
        session = SessionLocal()
        try:
            init_database(session)
        finally:
            session.close()


@app.get("/api/health")
def healthcheck() -> dict[str, str]:
    return {"status": "ok"}


@app.post("/api/auth/register", status_code=201)
def register(payload: RegisterRequest, db: Session = Depends(get_db)) -> dict:
    try:
        token, user = create_user(db, payload)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"token": token, "user": user}


@app.post("/api/auth/login")
def login(payload: LoginRequest, db: Session = Depends(get_db)) -> dict:
    try:
        token, user = login_user(db, payload)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"token": token, "user": user}


@app.post("/api/auth/google")
def google_login(payload: GoogleAuthRequest, db: Session = Depends(get_db)) -> dict:
    try:
        token, user = login_user_with_google(db, payload)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"token": token, "user": user}


@app.get("/api/me")
def get_me(
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict:
    try:
        user = auth_user_from_token(db, authorization)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    return {"user": serialize_user(user)}


@app.put("/api/me")
def put_me(
    payload: UpdateProfileRequest,
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict:
    try:
        user = auth_user_from_token(db, authorization)
        updated_user = update_user_profile(db, user, payload)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"user": updated_user}


@app.get("/api/auth/config")
def auth_config() -> dict[str, str]:
    return {"googleClientId": google_client_id()}


@app.get("/api/summary")
def get_summary(db: Session = Depends(get_db)) -> dict:
    return summary_payload(db)


@app.get("/api/evaluations")
def get_evaluations(
    limit: int = Query(default=100, ge=1, le=1000),
    db: Session = Depends(get_db),
) -> dict:
    return evaluations_payload(db, limit=limit)


@app.get("/api/comparison")
def get_comparison(
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict:
    try:
        user = auth_user_from_token(db, authorization)
        return build_random_comparison(db, user)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    except (LookupError, ValueError) as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc


@app.post("/api/evaluations", status_code=201)
def create_evaluation(
    payload: PreferenceEvaluationCreate,
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict[str, int | bool]:
    try:
        user = auth_user_from_token(db, authorization)
        session_id = save_preference_evaluation(db, user, payload)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    except (KeyError, TypeError, ValueError) as exc:
        raise HTTPException(status_code=400, detail=f"Invalid request: {exc}") from exc
    return {"ok": True, "sessionId": session_id}


@app.get("/api/meta-review/proofs")
def get_meta_review_proofs(
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict:
    try:
        auth_user_from_token(db, authorization)
        return {"proofs": database_proof_options(db)}
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc


@app.get("/api/meta-review/featured")
def get_featured_meta_review(
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict:
    try:
        auth_user_from_token(db, authorization)
        return featured_meta_review(db)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    except LookupError as exc:
        raise HTTPException(status_code=404, detail=str(exc)) from exc


@app.post("/api/meta-review/generate", status_code=201)
def generate_meta_review(
    payload: MetaReviewGenerateRequest,
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict:
    try:
        user = auth_user_from_token(db, authorization)
        return build_meta_review(db, user, payload)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    except (KeyError, ValueError) as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc


@app.post("/api/meta-review/{session_id}/selection")
def select_meta_review(
    session_id: int,
    payload: MetaReviewSelectionRequest,
    authorization: str | None = Header(default=None),
    db: Session = Depends(get_db),
) -> dict[str, bool]:
    try:
        user = auth_user_from_token(db, authorization)
        save_meta_review_selection(db, user, session_id, payload)
    except PermissionError as exc:
        raise HTTPException(status_code=401, detail=str(exc)) from exc
    except (KeyError, ValueError) as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"ok": True}


@app.get("/")
def index() -> FileResponse:
    return FileResponse(STATIC_DIR / "index.html")


@app.get("/styles.css")
def styles() -> FileResponse:
    return FileResponse(STATIC_DIR / "styles.css")


@app.get("/app.js")
def javascript() -> FileResponse:
    return FileResponse(STATIC_DIR / "app.js")


@app.get("/googlef32254fd0dfa1cb9.html")
def google_site_verification() -> FileResponse:
    return FileResponse(GOOGLE_VERIFICATION_FILE, media_type="text/html")


if Path(STATIC_DIR).exists():
    app.mount("/static", StaticFiles(directory=STATIC_DIR), name="static")
