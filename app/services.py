from __future__ import annotations

import base64
import hashlib
import hmac
import json
import random
import re
import secrets
from datetime import datetime, timezone
from typing import Any

from sqlalchemy import func, select, text
from sqlalchemy.orm import Session

from .config import REPO_ROOT, google_client_id
from .models import (
    AuthToken,
    Node,
    PreferenceEvaluation,
    PreferenceVote,
    Proof,
    Question,
    User,
)
from .parsing import guess_author, humanize_slug, parse_nodes, question_key_for_path, source_lean_files
from .schemas import GoogleAuthRequest, LoginRequest, PreferenceEvaluationCreate, RegisterRequest, UpdateProfileRequest, UserPayload


MODE_LABELS = {
    "same_question_proofs": "Two complete proofs of the same question",
    "same_question_nodes": "Node-to-node comparison for the same question",
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


def _sync_nodes_for_proof(session: Session, proof: Proof, parsed_nodes: list[Any]) -> int:
    existing_nodes = session.execute(select(Node).where(Node.proof_id == proof.id)).scalars().all()
    existing_by_ordinal = {node.ordinal: node for node in existing_nodes}
    desired_ordinals = {node.ordinal for node in parsed_nodes}

    for parsed_node in parsed_nodes:
        existing = existing_by_ordinal.get(parsed_node.ordinal)
        if existing is None:
            session.add(
                Node(
                    proof_id=proof.id,
                    question_id=proof.question_id,
                    ordinal=parsed_node.ordinal,
                    name=parsed_node.name,
                    node_type=parsed_node.node_type,
                    declaration_kind=parsed_node.declaration_kind,
                    declaration_name=parsed_node.declaration_name,
                    inputs_json=json.dumps(parsed_node.inputs),
                    natural_language=parsed_node.natural,
                    nl_proof=parsed_node.nl_proof,
                    code=parsed_node.code,
                    start_line=parsed_node.start_line,
                    end_line=parsed_node.end_line,
                    created_at=utc_now(),
                )
            )
            continue

        existing.question_id = proof.question_id
        existing.name = parsed_node.name
        existing.node_type = parsed_node.node_type
        existing.declaration_kind = parsed_node.declaration_kind
        existing.declaration_name = parsed_node.declaration_name
        existing.inputs_json = json.dumps(parsed_node.inputs)
        existing.natural_language = parsed_node.natural
        existing.nl_proof = parsed_node.nl_proof
        existing.code = parsed_node.code
        existing.start_line = parsed_node.start_line
        existing.end_line = parsed_node.end_line

    for existing in existing_nodes:
        if existing.ordinal not in desired_ordinals:
            session.delete(existing)

    return len(parsed_nodes)


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
        parsed_nodes = parse_nodes(content)
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
                node_count=len(parsed_nodes),
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
            proof.node_count = len(parsed_nodes)

        proof.node_count = _sync_nodes_for_proof(session, proof, parsed_nodes)

    for source_path, proof in list(existing_proofs.items()):
        if source_path not in desired_paths:
            for node in session.execute(select(Node).where(Node.proof_id == proof.id)).scalars().all():
                session.delete(node)
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
        "nodes": session.execute(select(func.count(Node.id))).scalar_one(),
    }


def serialize_lines(text_value: str, start_at: int = 1) -> list[dict[str, Any]]:
    return [{"lineNumber": start_at + index, "text": line} for index, line in enumerate(text_value.splitlines())]


def normalize_text_for_compare(text_value: str) -> str:
    return re.sub(r"\s+", " ", text_value).strip()


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


def node_payload(session: Session, node_id: int) -> dict[str, Any]:
    node = fetch_one_dict(
        session,
        """
        SELECT n.*, p.author, p.source_path, q.title AS question_title, q.slug AS question_slug
        FROM nodes n
        JOIN proofs p ON p.id = n.proof_id
        JOIN questions q ON q.id = n.question_id
        WHERE n.id = :node_id
        """,
        {"node_id": node_id},
    )
    if node is None:
        raise KeyError(f"Unknown node id {node_id}")
    node["kind"] = "node"
    node["entityId"] = node["id"]
    node["inputs"] = json.loads(node["inputs_json"])
    node["lines"] = serialize_lines(node["code"], node["start_line"])
    return node


def random_pair_same_question(session: Session) -> tuple[int, int] | None:
    pairs = fetch_all_dicts(
        session,
        """
        SELECT p1.id AS left_id, p2.id AS right_id
        FROM proofs p1
        JOIN proofs p2
          ON p1.question_id = p2.question_id
         AND p1.id < p2.id
        WHERE TRIM(p1.content) != TRIM(p2.content)
          AND TRIM(p1.title) != TRIM(p2.title)
        """,
    )
    if not pairs:
        return None
    pair = random.choice(pairs)
    return pair["left_id"], pair["right_id"]


def random_pair_different_questions(session: Session) -> tuple[int, int] | None:
    pairs = fetch_all_dicts(
        session,
        """
        SELECT p1.id AS left_id, p2.id AS right_id
        FROM proofs p1
        JOIN proofs p2
          ON p1.question_id != p2.question_id
         AND p1.id < p2.id
        WHERE TRIM(p1.content) != TRIM(p2.content)
          AND TRIM(p1.title) != TRIM(p2.title)
        """,
    )
    if not pairs:
        return None
    pair = random.choice(pairs)
    return pair["left_id"], pair["right_id"]


def _filter_node_pairs(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        pair for pair in pairs
        if normalize_text_for_compare(
            " | ".join(
                [
                    pair["left_name"] or "",
                    pair["left_type"] or "",
                    pair["left_natural"] or "",
                    pair["left_nl_proof"] or "",
                    pair["left_decl_name"] or "",
                    pair["left_code"].split(":=")[0],
                ]
            )
        )
        != normalize_text_for_compare(
            " | ".join(
                [
                    pair["right_name"] or "",
                    pair["right_type"] or "",
                    pair["right_natural"] or "",
                    pair["right_nl_proof"] or "",
                    pair["right_decl_name"] or "",
                    pair["right_code"].split(":=")[0],
                ]
            )
        )
    ]


def random_pair_same_node_same_question(session: Session, user_id: int | None = None) -> tuple[int, int] | None:
    pairs = fetch_all_dicts(
        session,
        """
        SELECT
          n1.id AS left_id,
          n2.id AS right_id,
          n1.name AS left_name,
          n2.name AS right_name,
          n1.node_type AS left_type,
          n2.node_type AS right_type,
          n1.natural_language AS left_natural,
          n2.natural_language AS right_natural,
          n1.nl_proof AS left_nl_proof,
          n2.nl_proof AS right_nl_proof,
          n1.declaration_name AS left_decl_name,
          n2.declaration_name AS right_decl_name,
          n1.code AS left_code,
          n2.code AS right_code
        FROM nodes n1
        JOIN nodes n2
         ON n1.question_id = n2.question_id
         AND n1.name = n2.name
         AND n1.id < n2.id
         AND n1.proof_id != n2.proof_id
        JOIN proofs p1 ON p1.id = n1.proof_id
        JOIN proofs p2 ON p2.id = n2.proof_id
        WHERE TRIM(n1.code) != ''
          AND TRIM(n2.code) != ''
          AND TRIM(n1.code) != TRIM(n2.code)
          AND p1.source_path != p2.source_path
          AND (
            :user_id IS NULL
            OR NOT EXISTS (
              SELECT 1
              FROM preference_evaluations e
              WHERE e.user_id = :user_id
                AND e.entity_a_kind = 'node'
                AND e.entity_b_kind = 'node'
                AND (
                  (e.entity_a_node_id = n1.id AND e.entity_b_node_id = n2.id)
                  OR (e.entity_a_node_id = n2.id AND e.entity_b_node_id = n1.id)
                )
            )
          )
        """,
        {"user_id": user_id},
    )
    filtered_pairs = _filter_node_pairs(pairs)
    if not filtered_pairs:
        return None
    pair = random.choice(filtered_pairs)
    return pair["left_id"], pair["right_id"]


def random_pair_same_kind(session: Session) -> tuple[int, int] | None:
    pairs = fetch_all_dicts(
        session,
        """
        SELECT
          n1.id AS left_id,
          n2.id AS right_id,
          n1.name AS left_name,
          n2.name AS right_name,
          n1.node_type AS left_type,
          n2.node_type AS right_type,
          n1.natural_language AS left_natural,
          n2.natural_language AS right_natural,
          n1.nl_proof AS left_nl_proof,
          n2.nl_proof AS right_nl_proof,
          n1.declaration_name AS left_decl_name,
          n2.declaration_name AS right_decl_name,
          n1.code AS left_code,
          n2.code AS right_code
        FROM nodes n1
        JOIN nodes n2
          ON n1.node_type = n2.node_type
         AND n1.id < n2.id
        WHERE TRIM(n1.code) != ''
          AND TRIM(n2.code) != ''
          AND TRIM(n1.code) != TRIM(n2.code)
          AND COALESCE(TRIM(n1.name), '') != COALESCE(TRIM(n2.name), '')
          AND COALESCE(TRIM(n1.declaration_name), '') != COALESCE(TRIM(n2.declaration_name), '')
        """,
    )
    filtered_pairs = _filter_node_pairs(pairs)
    if not filtered_pairs:
        return None
    pair = random.choice(filtered_pairs)
    return pair["left_id"], pair["right_id"]


def _entity_fields(kind: str, entity_id: int) -> tuple[int | None, int | None]:
    if kind == "proof":
        return entity_id, None
    return None, entity_id


def build_random_comparison(session: Session, user: User | None = None) -> dict[str, Any]:
    pair = random_pair_same_node_same_question(session, user.id if user else None)
    if pair is None:
        raise LookupError("No comparison pairs available.")

    mode = "same_question_nodes"
    label = MODE_LABELS[mode]
    a_id, b_id = pair
    a_payload = node_payload(session, a_id)
    b_payload = node_payload(session, b_id)

    if random.choice([True, False]):
        a_payload, b_payload = b_payload, a_payload

    return {"mode": mode, "modeLabel": label, "a": a_payload, "b": b_payload}


def save_preference_evaluation(session: Session, user: User, payload: PreferenceEvaluationCreate) -> int:
    a_proof_id, a_node_id = _entity_fields(payload.a.kind, payload.a.entityId)
    b_proof_id, b_node_id = _entity_fields(payload.b.kind, payload.b.entityId)
    evaluator = payload.evaluator

    record = PreferenceEvaluation(
        user_id=user.id,
        mode=payload.mode,
        entity_a_kind=payload.a.kind,
        entity_b_kind=payload.b.kind,
        entity_a_proof_id=a_proof_id,
        entity_b_proof_id=b_proof_id,
        entity_a_node_id=a_node_id,
        entity_b_node_id=b_node_id,
        evaluator_display_name=(evaluator.displayName if evaluator else user.display_name).strip(),
        evaluator_affiliation=(evaluator.affiliation if evaluator else user.affiliation).strip(),
        evaluator_experience_level=(evaluator.experienceLevel if evaluator else user.experience_level).strip(),
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
        "nodes": session.execute(select(func.count(Node.id))).scalar_one(),
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
          e.mode,
          e.entity_a_kind,
          e.entity_b_kind,
          e.evaluator_display_name,
          e.evaluator_affiliation,
          e.evaluator_experience_level,
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
