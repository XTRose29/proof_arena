from __future__ import annotations

import base64
import hashlib
import hmac
import random
import secrets
from datetime import datetime, timezone
from typing import Any

from sqlalchemy import func, select, text
from sqlalchemy.orm import Session

from .config import REPO_ROOT, google_client_id
from .models import (
    AuthToken,
    PreferenceEvaluation,
    PreferenceVote,
    Proof,
    Question,
    User,
)
from .parsing import guess_author, humanize_slug, question_key_for_path, source_lean_files
from .schemas import GoogleAuthRequest, LoginRequest, PreferenceEvaluationCreate, RegisterRequest, UpdateProfileRequest, UserPayload


MODE_LABELS = {
    "same_question_proofs": "Two complete proofs of the same question",
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def fetch_one_dict(session: Session, query: str, params: dict[str, Any]) -> dict[str, Any] | None:
    row = session.execute(text(query), params).mappings().first()
    return dict(row) if row else None


def fetch_all_dicts(session: Session, query: str, params: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    result = session.execute(text(query), params or {}).mappings().all()
    return [dict(row) for row in result]


def _hash_password(password: str, salt: str) -> str:
    derived = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt.encode("utf-8"), 120000)
    return base64.b64encode(derived).decode("ascii")


def _new_salt() -> str:
    return secrets.token_hex(16)


def serialize_user(user: User) -> dict[str, Any]:
    payload = UserPayload(
        id=user.id,
        email=user.email,
        displayName=user.display_name,
        affiliation=user.affiliation,
        experienceLevel=user.experience_level,
    )
    return payload.model_dump()


def create_user(session: Session, payload: RegisterRequest) -> tuple[str, dict[str, Any]]:
    existing = session.execute(select(User).where(User.email == payload.email.lower())).scalar_one_or_none()
    if existing is not None:
        raise ValueError("An account with this email already exists.")

    salt = _new_salt()
    user = User(
        email=payload.email.lower(),
        display_name=payload.displayName.strip(),
        affiliation=payload.affiliation.strip(),
        experience_level=payload.experienceLevel.strip(),
        password_hash=_hash_password(payload.password, salt),
        password_salt=salt,
        created_at=utc_now(),
    )
    session.add(user)
    session.flush()

    token = AuthToken(user_id=user.id, token=secrets.token_urlsafe(32), created_at=utc_now())
    session.add(token)
    session.commit()
    return token.token, serialize_user(user)


def login_user(session: Session, payload: LoginRequest) -> tuple[str, dict[str, Any]]:
    user = session.execute(select(User).where(User.email == payload.email.lower())).scalar_one_or_none()
    if user is None:
        raise ValueError("Invalid email or password.")

    candidate_hash = _hash_password(payload.password, user.password_salt)
    if not hmac.compare_digest(candidate_hash, user.password_hash):
        raise ValueError("Invalid email or password.")

    token = AuthToken(user_id=user.id, token=secrets.token_urlsafe(32), created_at=utc_now())
    session.add(token)
    session.commit()
    return token.token, serialize_user(user)


def login_user_with_google(session: Session, payload: GoogleAuthRequest) -> tuple[str, dict[str, Any]]:
    client_id = google_client_id()
    if not client_id:
        raise ValueError("Google login is not configured.")

    try:
        from google.auth.transport import requests as google_requests
        from google.oauth2 import id_token

        token_payload = id_token.verify_oauth2_token(
            payload.credential,
            google_requests.Request(),
            client_id,
        )
    except ImportError as exc:
        raise ValueError("Google authentication dependency is not installed.") from exc
    except ValueError as exc:
        raise ValueError("Google authentication failed.") from exc

    if not token_payload.get("email_verified"):
        raise ValueError("Google account email must be verified.")

    email = str(token_payload.get("email", "")).strip().lower()
    display_name = str(token_payload.get("name", "")).strip() or email.split("@")[0]
    if not email:
        raise ValueError("Google account did not provide an email address.")

    user = session.execute(select(User).where(User.email == email)).scalar_one_or_none()
    if user is None:
        user = User(
            email=email,
            display_name=display_name,
            affiliation="",
            experience_level="",
            password_hash="google_oauth",
            password_salt="google_oauth",
            created_at=utc_now(),
        )
        session.add(user)
        session.flush()
    elif not user.display_name.strip():
        user.display_name = display_name

    token = AuthToken(user_id=user.id, token=secrets.token_urlsafe(32), created_at=utc_now())
    session.add(token)
    session.commit()
    return token.token, serialize_user(user)


def auth_user_from_token(session: Session, raw_token: str | None) -> User:
    if not raw_token:
        raise PermissionError("Authentication required.")
    token_value = raw_token.removeprefix("Bearer ").strip()
    if not token_value:
        raise PermissionError("Authentication required.")
    user = session.execute(
        select(User)
        .join(AuthToken, AuthToken.user_id == User.id)
        .where(AuthToken.token == token_value)
    ).scalar_one_or_none()
    if user is None:
        raise PermissionError("Invalid or expired token.")
    return user


def update_user_profile(session: Session, user: User, payload: UpdateProfileRequest) -> dict[str, Any]:
    user.display_name = payload.displayName.strip()
    user.affiliation = payload.affiliation.strip()
    user.experience_level = payload.experienceLevel.strip()
    session.commit()
    return serialize_user(user)


def init_database(session: Session) -> None:
    if session.execute(select(func.count(Proof.id))).scalar_one() > 0:
        return
    sync_question_sets(session)


def sync_question_sets(session: Session) -> dict[str, int]:
    desired_questions: set[str] = set()
    desired_paths: set[str] = set()

    existing_questions = {
        question.canonical_key: question
        for question in session.execute(select(Question)).scalars().all()
    }
    existing_proofs = {
        proof.source_path: proof
        for proof in session.execute(select(Proof)).scalars().all()
    }

    for path in source_lean_files():
        rel_path = str(path.relative_to(REPO_ROOT))
        desired_paths.add(rel_path)

        content = path.read_text(encoding="utf-8")
        canonical_key = question_key_for_path(path)
        desired_questions.add(canonical_key)

        question = existing_questions.get(canonical_key)
        if question is None:
            question = Question(
                canonical_key=canonical_key,
                title=humanize_slug(canonical_key),
                slug=canonical_key,
                created_at=utc_now(),
            )
            session.add(question)
            session.flush()
            existing_questions[canonical_key] = question
        else:
            question.title = humanize_slug(canonical_key)
            question.slug = canonical_key

        proof = existing_proofs.get(rel_path)
        if proof is None:
            proof = Proof(
                question_id=question.id,
                title=path.stem,
                label=rel_path,
                author=guess_author(path),
                source_path=rel_path,
                content=content,
                line_count=len(content.splitlines()),
                created_at=utc_now(),
            )
            session.add(proof)
            session.flush()
            existing_proofs[rel_path] = proof
        else:
            proof.question_id = question.id
            proof.title = path.stem
            proof.label = rel_path
            proof.author = guess_author(path)
            proof.content = content
            proof.line_count = len(content.splitlines())

    for source_path, proof in list(existing_proofs.items()):
        if source_path not in desired_paths:
            session.delete(proof)

    session.flush()

    for canonical_key, question in list(existing_questions.items()):
        if canonical_key not in desired_questions:
            remaining_proof_count = session.execute(
                select(func.count(Proof.id)).where(Proof.question_id == question.id)
            ).scalar_one()
            if remaining_proof_count == 0:
                session.delete(question)

    session.commit()

    return {
        "questions": session.execute(select(func.count(Question.id))).scalar_one(),
        "proofs": session.execute(select(func.count(Proof.id))).scalar_one(),
    }


def serialize_lines(text_value: str, start_at: int = 1) -> list[dict[str, Any]]:
    return [{"lineNumber": start_at + index, "text": line} for index, line in enumerate(text_value.splitlines())]


def proof_payload(session: Session, proof_id: int) -> dict[str, Any]:
    proof = fetch_one_dict(
        session,
        """
        SELECT p.*, q.title AS question_title, q.slug AS question_slug
        FROM proofs p
        JOIN questions q ON q.id = p.question_id
        WHERE p.id = :proof_id
        """,
        {"proof_id": proof_id},
    )
    if proof is None:
        raise KeyError(f"Unknown proof id {proof_id}")
    proof["kind"] = "proof"
    proof["entityId"] = proof["id"]
    proof["lines"] = serialize_lines(proof["content"], 1)
    return proof


def random_pair_same_question(session: Session, user_id: int | None = None) -> tuple[int, int] | None:
    user_filter = ""
    params: dict[str, Any] = {}
    if user_id is not None:
        user_filter = """
          AND NOT EXISTS (
            SELECT 1
            FROM preference_evaluations e
            WHERE e.user_id = :user_id
              AND (
                (e.entity_a_proof_id = p1.id AND e.entity_b_proof_id = p2.id)
                OR (e.entity_a_proof_id = p2.id AND e.entity_b_proof_id = p1.id)
              )
          )
        """
        params["user_id"] = user_id

    pairs = fetch_all_dicts(
        session,
        f"""
        SELECT p1.id AS left_id, p2.id AS right_id
        FROM proofs p1
        JOIN proofs p2
          ON p1.question_id = p2.question_id
         AND p1.id < p2.id
        WHERE TRIM(p1.content) != TRIM(p2.content)
          AND TRIM(p1.title) != TRIM(p2.title)
          {user_filter}
        """,
        params,
    )
    if not pairs:
        return None
    pair = random.choice(pairs)
    return pair["left_id"], pair["right_id"]


def build_random_comparison(session: Session, user: User | None = None) -> dict[str, Any]:
    mode = "same_question_proofs"
    pair = random_pair_same_question(session, user.id if user else None)
    if pair is None:
        pair = random_pair_same_question(session)
    if pair is None:
        raise LookupError("No comparison pairs available.")
    a_id, b_id = pair
    a_payload = proof_payload(session, a_id)
    b_payload = proof_payload(session, b_id)

    if random.choice([True, False]):
        a_payload, b_payload = b_payload, a_payload

    return {"mode": mode, "modeLabel": MODE_LABELS[mode], "a": a_payload, "b": b_payload}


def save_preference_evaluation(session: Session, user: User, payload: PreferenceEvaluationCreate) -> int:
    evaluator = payload.evaluator
    proof_ids = {payload.a.entityId, payload.b.entityId}
    if len(proof_ids) != 2:
        raise ValueError("A comparison must contain two different proofs.")
    proof_count = session.execute(select(func.count(Proof.id)).where(Proof.id.in_(list(proof_ids)))).scalar_one()
    if proof_count != 2:
        raise KeyError("Unknown proof id.")
    if evaluator is not None:
        user.affiliation = evaluator.affiliation.strip()
        user.experience_level = evaluator.experienceLevel.strip()

    record = PreferenceEvaluation(
        user_id=user.id,
        entity_a_proof_id=payload.a.entityId,
        entity_b_proof_id=payload.b.entityId,
        evaluator_display_name=(evaluator.displayName if evaluator else user.display_name).strip(),
        general_comment=payload.generalComment.strip(),
        created_at=utc_now(),
    )
    session.add(record)
    session.flush()

    votes = {
        "clarity": payload.preferences.clarity,
        "conciseness": payload.preferences.conciseness,
        "idiomatic_structure": payload.preferences.idiomaticStructure,
        "overall": payload.preferences.overall,
    }
    for criterion, preference in votes.items():
        session.add(
            PreferenceVote(
                evaluation_id=record.id,
                criterion=criterion,
                preference=preference,
                created_at=utc_now(),
            )
        )

    session.commit()
    return record.id


def summary_payload(session: Session) -> dict[str, Any]:
    counts = {
        "questions": session.execute(select(func.count(Question.id))).scalar_one(),
        "proofs": session.execute(select(func.count(Proof.id))).scalar_one(),
        "evaluations": session.execute(select(func.count(PreferenceEvaluation.id))).scalar_one(),
    }
    questions = fetch_all_dicts(
        session,
        """
        SELECT q.title, q.slug, COUNT(p.id) AS proof_count
        FROM questions q
        LEFT JOIN proofs p ON p.question_id = q.id
        GROUP BY q.id, q.title, q.slug
        ORDER BY proof_count DESC, q.title ASC
        """,
    )
    return {"counts": counts, "questions": questions[:20]}


def evaluations_payload(session: Session, limit: int = 100) -> dict[str, Any]:
    rows = fetch_all_dicts(
        session,
        """
        SELECT
          e.id,
          'same_question_proofs' AS mode,
          'proof' AS entity_a_kind,
          'proof' AS entity_b_kind,
          e.evaluator_display_name,
          u.affiliation AS evaluator_affiliation,
          u.experience_level AS evaluator_experience_level,
          e.created_at,
          u.email AS user_email
        FROM preference_evaluations e
        JOIN users u ON u.id = e.user_id
        ORDER BY e.id DESC
        LIMIT :limit_value
        """,
        {"limit_value": limit},
    )
    for row in rows:
        row["votes"] = fetch_all_dicts(
            session,
            """
            SELECT criterion, preference, created_at
            FROM preference_votes
            WHERE evaluation_id = :evaluation_id
            ORDER BY id ASC
            """,
            {"evaluation_id": row["id"]},
        )
    return {"evaluations": rows}
