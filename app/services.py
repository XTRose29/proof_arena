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

from .config import REPO_ROOT
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
from .schemas import LoginRequest, PreferenceEvaluationCreate, RegisterRequest, UserPayload


MODE_LABELS = {
    "option1": "Two complete proofs of the same question",
    "option2": "Two complete proofs of different questions",
    "option3": "The same node of the same question",
    "option4": "Two random nodes of the same kind",
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


def init_database(session: Session) -> None:
    if session.execute(select(func.count(Proof.id))).scalar_one() > 0:
        return
    import_question_sets(session, replace_existing=False)


def import_question_sets(session: Session, replace_existing: bool = True) -> dict[str, int]:
    if replace_existing:
        session.query(PreferenceVote).delete()
        session.query(PreferenceEvaluation).delete()
        session.query(Node).delete()
        session.query(Proof).delete()
        session.query(Question).delete()
        session.flush()

    question_ids: dict[str, int] = {}
    proof_count = 0
    node_count = 0

    for path in source_lean_files():
        rel_path = path.relative_to(REPO_ROOT)
        content = path.read_text(encoding="utf-8")
        nodes = parse_nodes(content)
        canonical_key = question_key_for_path(path)
        question = session.execute(select(Question).where(Question.canonical_key == canonical_key)).scalar_one_or_none()
        if question is None:
            question = Question(
                canonical_key=canonical_key,
                title=humanize_slug(canonical_key),
                slug=canonical_key,
                created_at=utc_now(),
            )
            session.add(question)
            session.flush()
        question_ids[canonical_key] = question.id

        proof = Proof(
            question_id=question.id,
            title=path.stem,
            label=str(rel_path),
            author=guess_author(path),
            source_path=str(rel_path),
            content=content,
            line_count=len(content.splitlines()),
            node_count=len(nodes),
            created_at=utc_now(),
        )
        session.add(proof)
        session.flush()
        proof_count += 1

        for node in nodes:
            session.add(
                Node(
                    proof_id=proof.id,
                    question_id=question.id,
                    ordinal=node.ordinal,
                    name=node.name,
                    node_type=node.node_type,
                    declaration_kind=node.declaration_kind,
                    declaration_name=node.declaration_name,
                    inputs_json=json.dumps(node.inputs),
                    natural_language=node.natural,
                    nl_proof=node.nl_proof,
                    code=node.code,
                    start_line=node.start_line,
                    end_line=node.end_line,
                    created_at=utc_now(),
                )
            )
            node_count += 1
    session.commit()
    return {"questions": len(question_ids), "proofs": proof_count, "nodes": node_count}


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


def random_pair_same_node_same_question(session: Session) -> tuple[int, int] | None:
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
        WHERE TRIM(n1.code) != ''
          AND TRIM(n2.code) != ''
          AND TRIM(n1.code) != TRIM(n2.code)
        """,
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


def build_random_comparison(session: Session) -> dict[str, Any]:
    candidates: list[tuple[str, tuple[int, int], str]] = []

    for mode, label, pair_fn in (
        ("option1", MODE_LABELS["option1"], random_pair_same_question),
        ("option2", MODE_LABELS["option2"], random_pair_different_questions),
        ("option3", MODE_LABELS["option3"], random_pair_same_node_same_question),
        ("option4", MODE_LABELS["option4"], random_pair_same_kind),
    ):
        pair = pair_fn(session)
        if pair is not None:
            candidates.append((mode, pair, label))

    if not candidates:
        raise LookupError("No comparison pairs available.")

    mode, pair, label = random.choice(candidates)
    a_id, b_id = pair
    a_payload = proof_payload(session, a_id) if mode in {"option1", "option2"} else node_payload(session, a_id)
    b_payload = proof_payload(session, b_id) if mode in {"option1", "option2"} else node_payload(session, b_id)

    if random.choice([True, False]):
        a_payload, b_payload = b_payload, a_payload

    return {"mode": mode, "modeLabel": label, "a": a_payload, "b": b_payload}


def save_preference_evaluation(session: Session, user: User, payload: PreferenceEvaluationCreate) -> int:
    a_proof_id, a_node_id = _entity_fields(payload.a.kind, payload.a.entityId)
    b_proof_id, b_node_id = _entity_fields(payload.b.kind, payload.b.entityId)

    record = PreferenceEvaluation(
        user_id=user.id,
        mode=payload.mode,
        entity_a_kind=payload.a.kind,
        entity_b_kind=payload.b.kind,
        entity_a_proof_id=a_proof_id,
        entity_b_proof_id=b_proof_id,
        entity_a_node_id=a_node_id,
        entity_b_node_id=b_node_id,
        evaluator_display_name=user.display_name.strip(),
        evaluator_affiliation=user.affiliation.strip(),
        evaluator_experience_level=user.experience_level.strip(),
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
