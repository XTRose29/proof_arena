from __future__ import annotations

import base64
import hashlib
import hmac
import json
import random
import secrets
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from itertools import combinations
from typing import Any

import requests
from sqlalchemy import func, select, text
from sqlalchemy.orm import Session

from .config import (
    META_REVIEW_EVALUATIONS_DIR,
    REPO_ROOT,
    anthropic_api_key,
    anthropic_base_url,
    claude_model,
    cornell_gateway_api_key,
    cornell_gateway_base_url,
    cornell_gateway_model,
    google_client_id,
)
from .models import (
    AuthToken,
    MetaReviewCriterionVote,
    MetaReviewDraft,
    MetaReviewSession,
    MetaReviewVote,
    PreferenceEvaluation,
    PreferenceVote,
    Proof,
    Question,
    User,
)
from .parsing import guess_author, humanize_slug, question_key_for_path, source_lean_files
from .schemas import (
    GoogleAuthRequest,
    LoginRequest,
    MetaReviewDraftRequest,
    MetaReviewGenerateRequest,
    MetaReviewSelectionRequest,
    PreferenceEvaluationCreate,
    RegisterRequest,
    UpdateProfileRequest,
    UserPayload,
)


MODE_LABELS = {
    "same_question_proofs": "Two complete proofs of the same question",
}

RUBRIC_SOURCES = {
    "reuse": "https://raw.githubusercontent.com/TauCetiProject/TauCetiReview/main/rubrics/reuse.md",
    "naming": "https://raw.githubusercontent.com/TauCetiProject/TauCetiReview/main/rubrics/naming.md",
    "documentation": "https://raw.githubusercontent.com/TauCetiProject/TauCetiReview/main/rubrics/documentation.md",
    "proof_quality": "https://raw.githubusercontent.com/TauCetiProject/TauCetiReview/main/rubrics/proof-quality.md",
}
_rubric_cache: str | None = None


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
        "reuse": payload.preferences.reuse,
        "naming": payload.preferences.naming,
        "documentation": payload.preferences.documentation,
        "proof_quality": payload.preferences.proofQuality,
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


def database_proof_options(session: Session, limit: int = 1000) -> list[dict[str, Any]]:
    return fetch_all_dicts(
        session,
        """
        SELECT
          p.id,
          p.title,
          p.author,
          p.line_count AS lineCount,
          q.title AS questionTitle
        FROM proofs p
        JOIN questions q ON q.id = p.question_id
        ORDER BY q.title ASC, p.title ASC
        LIMIT :limit_value
        """,
        {"limit_value": limit},
    )


def _rubric_text() -> str:
    global _rubric_cache
    if _rubric_cache is not None:
        return _rubric_cache

    sections: list[str] = []
    try:
        for name, url in RUBRIC_SOURCES.items():
            response = requests.get(url, timeout=20)
            response.raise_for_status()
            sections.append(f"# {name.replace('_', ' ').title()}\n{response.text.strip()}")
    except requests.RequestException as exc:
        raise ValueError("Could not load the review rubric. Please try again.") from exc

    _rubric_cache = "\n\n".join(sections)
    return _rubric_cache


def _evaluation_prompt(proof_content: str, rubric_text: str) -> str:
    return f"""You are an expert Lean proof reviewer. Review the Lean source below using the supplied rubric.

Write a concise, evidence-based evaluation. Do not assess mathematical correctness beyond what is visible in the code. Every reason should point to observable code choices. Do not invent errors, library facts, or theorem intent.

Return only valid JSON with this exact shape:
{{
  "reuse": {{"verdict": "strong|adequate|needs_work", "reason": "one or two sentences"}},
  "naming": {{"verdict": "strong|adequate|needs_work", "reason": "one or two sentences"}},
  "documentation": {{"verdict": "strong|adequate|needs_work", "reason": "one or two sentences"}},
  "proof_quality": {{"verdict": "strong|adequate|needs_work", "reason": "one or two sentences"}},
  "overall": {{"verdict": "strong|adequate|needs_work", "reason": "one or two sentences"}},
  "summary": "one short overall takeaway"
}}

Rubric:
{rubric_text}

Lean source:
```lean
{proof_content}
```"""


def _messages_url() -> str:
    base_url = anthropic_base_url()
    return f"{base_url}/messages" if base_url.endswith("/v1") else f"{base_url}/v1/messages"


def _chat_completions_url() -> str:
    base_url = cornell_gateway_base_url()
    return f"{base_url}/chat/completions" if base_url.endswith("/v1") else f"{base_url}/v1/chat/completions"


def _parse_evaluation(content: str) -> dict[str, Any]:
    cleaned = content.strip()
    if cleaned.startswith("```"):
        cleaned = cleaned.split("\n", 1)[1] if "\n" in cleaned else ""
        cleaned = cleaned.rsplit("```", 1)[0].strip()
    try:
        evaluation = json.loads(cleaned)
    except json.JSONDecodeError as exc:
        raise ValueError("The model returned an invalid evaluation. Please generate another pair.") from exc

    if not isinstance(evaluation, dict):
        raise ValueError("The model returned an invalid evaluation. Please generate another pair.")

    normalized: dict[str, Any] = {}
    for criterion in (*RUBRIC_SOURCES.keys(), "overall"):
        item = evaluation.get(criterion)
        if not isinstance(item, dict):
            raise ValueError("The model returned an incomplete evaluation. Please generate another pair.")
        verdict = str(item.get("verdict", "")).strip().lower()
        reason = str(item.get("reason", "")).strip()
        if verdict not in {"strong", "adequate", "needs_work"} or not reason:
            raise ValueError("The model returned an incomplete evaluation. Please generate another pair.")
        normalized[criterion] = {"verdict": verdict, "reason": reason[:1200]}

    summary = str(evaluation.get("summary", "")).strip()
    if not summary:
        raise ValueError("The model returned an incomplete evaluation. Please generate another pair.")
    normalized["summary"] = summary[:1200]
    return normalized


def _local_meta_review_candidates(session: Session) -> list[dict[str, Any]]:
    if not META_REVIEW_EVALUATIONS_DIR.exists():
        return []

    proofs_by_submission = {
        (question_key, proof.title): (proof, question_title)
        for proof, question_key, question_title in session.execute(
            select(Proof, Question.canonical_key, Question.title).join(
                Question,
                Question.id == Proof.question_id,
            )
        ).all()
    }
    candidates: list[dict[str, Any]] = []

    for submission_dir in sorted(META_REVIEW_EVALUATIONS_DIR.glob("*/*")):
        if not submission_dir.is_dir():
            continue
        question_key = submission_dir.parent.name.strip().lower().replace(" ", "_")
        proof_record = proofs_by_submission.get((question_key, submission_dir.name))
        if proof_record is None:
            continue

        evaluations: list[dict[str, Any]] = []
        for evaluation_path in sorted(submission_dir.glob("*.txt")):
            try:
                evaluation = _parse_evaluation(evaluation_path.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                continue
            evaluations.append({"model": evaluation_path.stem, "evaluation": evaluation})

        if len(evaluations) < 2:
            continue
        proof, question_title = proof_record
        candidates.append(
            {
                "proof": proof,
                "question_title": question_title,
                "evaluations": evaluations,
            }
        )

    return candidates


def _meta_review_pair_key(proof_id: int | None, model_a: str, model_b: str) -> tuple[int, str, str] | None:
    if proof_id is None:
        return None
    first_model, second_model = sorted((model_a, model_b))
    return proof_id, first_model, second_model


def _generate_anthropic_evaluation(proof_content: str, rubric_text: str) -> tuple[dict[str, Any], str]:
    api_key = anthropic_api_key()
    model = claude_model()
    if not api_key or not model:
        raise ValueError("Meta review is not configured. Set ANTHROPIC_API_KEY and CLAUDE_MODEL.")

    try:
        response = requests.post(
            _messages_url(),
            headers={
                "content-type": "application/json",
                "x-api-key": api_key,
                "anthropic-version": "2023-06-01",
            },
            json={
                "model": model,
                "max_tokens": 1800,
                "temperature": 0.35,
                "messages": [{"role": "user", "content": _evaluation_prompt(proof_content, rubric_text)}],
            },
            timeout=120,
        )
        response.raise_for_status()
        response_payload = response.json()
    except (requests.RequestException, ValueError) as exc:
        raise ValueError("The model request failed. Please try again.") from exc

    text_blocks = response_payload.get("content", [])
    content = "".join(
        str(block.get("text", ""))
        for block in text_blocks
        if isinstance(block, dict) and block.get("type") == "text"
    )
    if not content:
        raise ValueError("The model returned an empty evaluation. Please generate another pair.")
    return _parse_evaluation(content), model


def _generate_cornell_gateway_evaluation(proof_content: str, rubric_text: str) -> tuple[dict[str, Any], str]:
    api_key = cornell_gateway_api_key()
    base_url = cornell_gateway_base_url()
    model = cornell_gateway_model()
    if not api_key or not base_url or not model:
        raise ValueError(
            "Cornell AI Gateway is not configured. Set CORNELL_AI_GATEWAY_API_KEY, "
            "CORNELL_AI_GATEWAY_BASE_URL, and CORNELL_AI_GATEWAY_MODEL."
        )

    try:
        response = requests.post(
            _chat_completions_url(),
            headers={
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
            },
            json={
                "model": model,
                "max_completion_tokens": 3000,
                "messages": [{"role": "user", "content": _evaluation_prompt(proof_content, rubric_text)}],
                "response_format": {"type": "json_object"},
            },
            timeout=120,
        )
        response.raise_for_status()
        response_payload = response.json()
        content = response_payload["choices"][0]["message"]["content"]
    except (KeyError, IndexError, requests.RequestException, TypeError, ValueError) as exc:
        raise ValueError("The Cornell AI Gateway request failed. Please try again.") from exc

    if not isinstance(content, str) or not content.strip():
        raise ValueError("The Cornell model returned an empty evaluation. Please generate another pair.")
    return _parse_evaluation(content), model


def _generate_evaluation_pair(
    proof_content: str,
    rubric_text: str,
) -> tuple[dict[str, Any], str, dict[str, Any], str]:
    with ThreadPoolExecutor(max_workers=2) as executor:
        anthropic_future = executor.submit(_generate_anthropic_evaluation, proof_content, rubric_text)
        cornell_future = executor.submit(_generate_cornell_gateway_evaluation, proof_content, rubric_text)
        generated = [anthropic_future.result(), cornell_future.result()]

    random.shuffle(generated)
    (evaluation_a, model_a), (evaluation_b, model_b) = generated
    return evaluation_a, model_a, evaluation_b, model_b


def build_meta_review(session: Session, user: User, payload: MetaReviewGenerateRequest) -> dict[str, Any]:
    if payload.proofId is not None:
        proof = proof_payload(session, payload.proofId)
        source_proof_id = payload.proofId
        source_kind = "database"
        question_title = str(proof.get("question_title", "")).strip()
        proof_title = str(proof["title"])
        source_title = f"{question_title} — {proof_title}" if question_title else proof_title
        proof_content = str(proof["content"])
    else:
        source_proof_id = None
        source_kind = "upload"
        source_title = payload.customTitle.strip() or "Uploaded Lean proof"
        proof_content = payload.customProof.strip()

    if not proof_content:
        raise ValueError("The Lean proof cannot be empty.")

    rubric_text = _rubric_text()
    evaluation_a, model_a, evaluation_b, model_b = _generate_evaluation_pair(proof_content, rubric_text)

    record = MetaReviewSession(
        user_id=user.id,
        source_proof_id=source_proof_id,
        source_kind=source_kind,
        source_title=source_title,
        proof_content=proof_content,
        rubric_text=rubric_text,
        evaluation_a=json.dumps(evaluation_a),
        evaluation_b=json.dumps(evaluation_b),
        model_a=model_a,
        model_b=model_b,
        is_featured=False,
        selection_reason="",
        created_at=utc_now(),
        selected_at=None,
    )
    session.add(record)
    session.flush()
    session.add(
        MetaReviewDraft(
            session_id=record.id,
            user_id=user.id,
            choices_json="{}",
            reason="",
            updated_at=utc_now(),
        )
    )
    session.commit()
    return _serialize_meta_review(record)


def build_random_meta_review(
    session: Session,
    user: User,
    exclude_session_id: int | None = None,
) -> dict[str, Any]:
    candidates = _local_meta_review_candidates(session)
    if not candidates:
        raise LookupError("No pre-generated evaluation pairs are available for meta review.")

    available_pair_keys = {
        _meta_review_pair_key(candidate["proof"].id, first["model"], second["model"])
        for candidate in candidates
        for first, second in combinations(candidate["evaluations"], 2)
    }
    if exclude_session_id is None:
        resumable_sessions = session.execute(
            select(MetaReviewSession)
            .join(MetaReviewDraft, MetaReviewDraft.session_id == MetaReviewSession.id)
            .where(MetaReviewDraft.user_id == user.id)
            .order_by(MetaReviewDraft.updated_at.desc(), MetaReviewDraft.id.desc())
        ).scalars().all()
        for resumable in resumable_sessions:
            resumable_key = _meta_review_pair_key(
                resumable.source_proof_id,
                resumable.model_a,
                resumable.model_b,
            )
            if resumable_key in available_pair_keys:
                return _serialize_meta_review_for_user(session, resumable, user)

    excluded_question_id: int | None = None
    excluded_pair_key: tuple[int, str, str] | None = None
    if exclude_session_id is not None:
        excluded_session = session.execute(
            select(MetaReviewSession).where(MetaReviewSession.id == exclude_session_id)
        ).scalar_one_or_none()
        if excluded_session is not None:
            excluded_pair_key = _meta_review_pair_key(
                excluded_session.source_proof_id,
                excluded_session.model_a,
                excluded_session.model_b,
            )
            if excluded_session.source_proof_id is not None:
                excluded_question_id = session.execute(
                    select(Proof.question_id).where(Proof.id == excluded_session.source_proof_id)
                ).scalar_one_or_none()

    reviewed_pair_keys = {
        pair_key
        for proof_id, model_a, model_b in session.execute(
            select(
                MetaReviewSession.source_proof_id,
                MetaReviewSession.model_a,
                MetaReviewSession.model_b,
            )
            .join(MetaReviewVote, MetaReviewVote.session_id == MetaReviewSession.id)
            .where(MetaReviewVote.user_id == user.id)
        ).all()
        if (pair_key := _meta_review_pair_key(proof_id, model_a, model_b)) is not None
    }

    available_pairs: list[dict[str, Any]] = []
    for candidate in candidates:
        proof = candidate["proof"]
        for first, second in combinations(candidate["evaluations"], 2):
            pair_key = _meta_review_pair_key(proof.id, first["model"], second["model"])
            if pair_key in reviewed_pair_keys or pair_key == excluded_pair_key:
                continue
            available_pairs.append({"candidate": candidate, "evaluations": [first, second]})

    if excluded_question_id is not None:
        other_question_pairs = [
            pair
            for pair in available_pairs
            if pair["candidate"]["proof"].question_id != excluded_question_id
        ]
        if other_question_pairs:
            available_pairs = other_question_pairs

    if not available_pairs:
        raise LookupError("You have reviewed all available meta-review pairs.")

    selected_pair = random.choice(available_pairs)
    candidate = selected_pair["candidate"]
    proof = candidate["proof"]
    first, second = selected_pair["evaluations"]
    if random.choice((True, False)):
        first, second = second, first

    record = MetaReviewSession(
        user_id=user.id,
        source_proof_id=proof.id,
        source_kind="database",
        source_title=f"{candidate['question_title']} — {proof.title}",
        proof_content=proof.content,
        rubric_text="Pre-generated with the Proof Arena reuse, naming, documentation, proof-quality, and overall rubrics.",
        evaluation_a=json.dumps(first["evaluation"], ensure_ascii=False),
        evaluation_b=json.dumps(second["evaluation"], ensure_ascii=False),
        model_a=first["model"],
        model_b=second["model"],
        is_featured=False,
        selection_reason="",
        created_at=utc_now(),
        selected_at=None,
    )
    session.add(record)
    session.flush()
    session.add(
        MetaReviewDraft(
            session_id=record.id,
            user_id=user.id,
            choices_json="{}",
            reason="",
            updated_at=utc_now(),
        )
    )
    session.commit()
    return _serialize_meta_review_for_user(session, record, user)


def _serialize_meta_review(record: MetaReviewSession) -> dict[str, Any]:
    return {
        "sessionId": record.id,
        "source": {
            "kind": record.source_kind,
            "title": record.source_title,
            "proof": record.proof_content,
        },
        "a": json.loads(record.evaluation_a),
        "b": json.loads(record.evaluation_b),
        "draft": {"choices": {}, "reason": ""},
        "submitted": False,
    }


def _serialize_meta_review_for_user(
    session: Session,
    record: MetaReviewSession,
    user: User,
) -> dict[str, Any]:
    payload = _serialize_meta_review(record)
    vote = session.execute(
        select(MetaReviewVote).where(
            MetaReviewVote.session_id == record.id,
            MetaReviewVote.user_id == user.id,
        )
    ).scalar_one_or_none()
    if vote is not None:
        criterion_votes = session.execute(
            select(MetaReviewCriterionVote).where(MetaReviewCriterionVote.vote_id == vote.id)
        ).scalars().all()
        payload["submitted"] = True
        payload["draft"] = {
            "choices": {
                ("proofQuality" if item.criterion == "proof_quality" else item.criterion): item.choice
                for item in criterion_votes
            },
            "reason": vote.reason,
        }
        return payload

    draft = session.execute(
        select(MetaReviewDraft).where(
            MetaReviewDraft.session_id == record.id,
            MetaReviewDraft.user_id == user.id,
        )
    ).scalar_one_or_none()
    if draft is not None:
        payload["draft"] = {"choices": json.loads(draft.choices_json), "reason": draft.reason}
    return payload


def _meta_review_system_user(session: Session) -> User:
    email = "meta-review@proof-arena.local"
    user = session.execute(select(User).where(User.email == email)).scalar_one_or_none()
    if user is None:
        user = User(
            email=email,
            display_name="Proof Arena Meta Review",
            affiliation="",
            experience_level="",
            password_hash="system_meta_review",
            password_salt="system_meta_review",
            created_at=utc_now(),
        )
        session.add(user)
        session.flush()
    return user


def build_featured_meta_review(session: Session) -> dict[str, Any]:
    existing = session.execute(
        select(MetaReviewSession)
        .where(MetaReviewSession.is_featured.is_(True))
        .order_by(MetaReviewSession.id.desc())
    ).scalars().first()
    if existing is not None:
        return _serialize_meta_review(existing)

    proof = session.execute(
        select(Proof)
        .where(func.length(func.trim(Proof.content)) > 0)
        .order_by(Proof.line_count.asc(), Proof.id.asc())
    ).scalars().first()
    if proof is None:
        raise LookupError("No proofs are available for the featured meta review.")

    rubric_text = _rubric_text()
    evaluation_a, model_a, evaluation_b, model_b = _generate_evaluation_pair(proof.content, rubric_text)
    record = MetaReviewSession(
        user_id=_meta_review_system_user(session).id,
        source_proof_id=proof.id,
        source_kind="database",
        source_title=proof.title,
        proof_content=proof.content,
        rubric_text=rubric_text,
        evaluation_a=json.dumps(evaluation_a),
        evaluation_b=json.dumps(evaluation_b),
        model_a=model_a,
        model_b=model_b,
        is_featured=True,
        selection_reason="",
        created_at=utc_now(),
        selected_at=None,
    )
    session.add(record)
    session.commit()
    return _serialize_meta_review(record)


def featured_meta_review(session: Session, user: User | None = None) -> dict[str, Any]:
    record = session.execute(
        select(MetaReviewSession)
        .where(MetaReviewSession.is_featured.is_(True))
        .order_by(MetaReviewSession.id.desc())
    ).scalars().first()
    if record is None:
        raise LookupError("The featured meta review has not been generated yet.")
    return _serialize_meta_review_for_user(session, record, user) if user is not None else _serialize_meta_review(record)


def save_meta_review_draft(
    session: Session,
    user: User,
    session_id: int,
    payload: MetaReviewDraftRequest,
) -> None:
    record = session.execute(
        select(MetaReviewSession).where(MetaReviewSession.id == session_id)
    ).scalar_one_or_none()
    if record is None:
        raise KeyError("Unknown meta-review session.")
    submitted = session.execute(
        select(MetaReviewVote).where(
            MetaReviewVote.session_id == record.id,
            MetaReviewVote.user_id == user.id,
        )
    ).scalar_one_or_none()
    if submitted is not None:
        raise ValueError("This meta-review pair is locked and cannot be changed.")

    choices = {
        key: value
        for key, value in payload.choices.model_dump().items()
        if value is not None
    }
    draft = session.execute(
        select(MetaReviewDraft).where(
            MetaReviewDraft.session_id == record.id,
            MetaReviewDraft.user_id == user.id,
        )
    ).scalar_one_or_none()
    if draft is None:
        draft = MetaReviewDraft(
            session_id=record.id,
            user_id=user.id,
            choices_json=json.dumps(choices),
            reason=payload.reason.strip(),
            updated_at=utc_now(),
        )
        session.add(draft)
    else:
        draft.choices_json = json.dumps(choices)
        draft.reason = payload.reason.strip()
        draft.updated_at = utc_now()
    session.commit()


def save_meta_review_selection(
    session: Session,
    user: User,
    session_id: int,
    payload: MetaReviewSelectionRequest,
) -> None:
    record = session.execute(
        select(MetaReviewSession).where(MetaReviewSession.id == session_id)
    ).scalar_one_or_none()
    if record is None:
        raise KeyError("Unknown meta-review session.")
    vote = session.execute(
        select(MetaReviewVote).where(
            MetaReviewVote.session_id == record.id,
            MetaReviewVote.user_id == user.id,
        )
    ).scalar_one_or_none()
    if vote is not None:
        raise ValueError("This meta-review choice has already been recorded.")

    session.add(
        MetaReviewVote(
            session_id=record.id,
            user_id=user.id,
            choice=payload.choices.overall,
            reason=payload.reason.strip(),
            created_at=utc_now(),
        )
    )
    session.flush()
    vote = session.execute(
        select(MetaReviewVote).where(
            MetaReviewVote.session_id == record.id,
            MetaReviewVote.user_id == user.id,
        )
    ).scalar_one()
    for client_criterion, choice in payload.choices.model_dump().items():
        session.add(
            MetaReviewCriterionVote(
                vote_id=vote.id,
                criterion="proof_quality" if client_criterion == "proofQuality" else client_criterion,
                choice=choice,
                created_at=utc_now(),
            )
        )
    draft = session.execute(
        select(MetaReviewDraft).where(
            MetaReviewDraft.session_id == record.id,
            MetaReviewDraft.user_id == user.id,
        )
    ).scalar_one_or_none()
    if draft is not None:
        session.delete(draft)
    session.commit()


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
