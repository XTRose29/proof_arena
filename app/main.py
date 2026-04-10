from __future__ import annotations

from pathlib import Path

from fastapi import Depends, FastAPI, HTTPException, Query, Request
from fastapi.exceptions import RequestValidationError
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles
from sqlalchemy.orm import Session

from .config import STATIC_DIR, auto_seed_enabled, cors_origins
from .database import Base, SessionLocal, engine, get_db
from .schemas import EvaluationCreate
from .services import build_comparison, evaluations_payload, init_database, save_evaluation, summary_payload


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
    mode: str = Query(default="option1"),
    db: Session = Depends(get_db),
) -> dict:
    try:
        return build_comparison(db, mode)
    except (LookupError, ValueError) as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc


@app.post("/api/evaluations", status_code=201)
def create_evaluation(payload: EvaluationCreate, db: Session = Depends(get_db)) -> dict[str, int | bool]:
    try:
        session_id = save_evaluation(db, payload)
    except (KeyError, TypeError, ValueError) as exc:
        raise HTTPException(status_code=400, detail=f"Invalid request: {exc}") from exc
    return {"ok": True, "sessionId": session_id}


@app.get("/")
def index() -> FileResponse:
    return FileResponse(STATIC_DIR / "index.html")


@app.get("/styles.css")
def styles() -> FileResponse:
    return FileResponse(STATIC_DIR / "styles.css")


@app.get("/app.js")
def javascript() -> FileResponse:
    return FileResponse(STATIC_DIR / "app.js")


if Path(STATIC_DIR).exists():
    app.mount("/static", StaticFiles(directory=STATIC_DIR), name="static")
