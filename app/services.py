from __future__ import annotations

import json
import random
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from sqlalchemy import func, select, text
from sqlalchemy.orm import Session

from .config import REPO_ROOT
from .models import EvaluationSession, LineComment, Node, Proof, Question, SideEvaluation
from .parsing import guess_author, humanize_slug, parse_nodes, question_key_for_path, source_lean_files
from .schemas import EvaluationCreate


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def fetch_one_dict(session: Session, query: str, params: dict[str, Any]) -> dict[str, Any] | None:
    row = session.execute(text(query), params).mappings().first()
    return dict(row) if row else None


def fetch_all_dicts(session: Session, query: str, params: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    result = session.execute(text(query), params or {}).mappings().all()
    return [dict(row) for row in result]


def init_database(session: Session) -> None:
    if session.execute(select(func.count(Proof.id))).scalar_one() > 0:
        return
    import_question_sets(session, replace_existing=False)


def import_question_sets(session: Session, replace_existing: bool = True) -> dict[str, int]:
    if replace_existing:
        session.query(LineComment).delete()
        session.query(SideEvaluation).delete()
        session.query(EvaluationSession).delete()
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
    return {
        "questions": len(question_ids),
        "proofs": proof_count,
        "nodes": node_count,
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
        SELECT n.*, p.label AS proof_label, p.author, p.source_path, q.title AS question_title, q.slug AS question_slug
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


def build_comparison(session: Session, mode: str) -> dict[str, Any]:
    if mode == "option1":
        pair = random_pair_same_question(session)
        if pair is None:
            raise LookupError("No same-question proof pairs available.")
        left_id, right_id = pair
        left = proof_payload(session, left_id)
        right = proof_payload(session, right_id)
    elif mode == "option2":
        pair = random_pair_different_questions(session)
        if pair is None:
            raise LookupError("No different-question proof pairs available.")
        left_id, right_id = pair
        left = proof_payload(session, left_id)
        right = proof_payload(session, right_id)
    elif mode == "option3":
        pair = random_pair_same_node_same_question(session)
        if pair is None:
            raise LookupError("No same-node same-question pairs available across different files.")
        left_id, right_id = pair
        left = node_payload(session, left_id)
        right = node_payload(session, right_id)
    elif mode == "option4":
        pair = random_pair_same_kind(session)
        if pair is None:
            raise LookupError("No same-kind node pairs available.")
        left_id, right_id = pair
        left = node_payload(session, left_id)
        right = node_payload(session, right_id)
    else:
        raise ValueError("Unknown mode")
    return {"mode": mode, "left": left, "right": right}


def save_evaluation(session: Session, payload: EvaluationCreate) -> int:
    def entity_fields(side_payload: Any) -> tuple[str, int | None, int | None]:
        if side_payload.kind == "proof":
            return "proof", int(side_payload.entityId), None
        return "node", None, int(side_payload.entityId)

    left_kind, left_proof_id, left_node_id = entity_fields(payload.left)
    right_kind, right_proof_id, right_node_id = entity_fields(payload.right)

    record = EvaluationSession(
        mode=payload.mode,
        left_kind=left_kind,
        right_kind=right_kind,
        left_proof_id=left_proof_id,
        right_proof_id=right_proof_id,
        left_node_id=left_node_id,
        right_node_id=right_node_id,
        created_at=utc_now(),
    )
    session.add(record)
    session.flush()

    for side_name, side_payload in (("left", payload.left), ("right", payload.right)):
        scores = side_payload.scores
        side_record = SideEvaluation(
            session_id=record.id,
            side=side_name,
            clarity=scores.clarity,
            conciseness=scores.conciseness,
            idiomatic_structure=scores.idiomaticStructure,
            fidelity_to_nl=scores.fidelityToNl,
            overall_score=scores.overall,
            general_comment=side_payload.generalComment.strip(),
            created_at=utc_now(),
        )
        session.add(side_record)
        session.flush()

        for comment in side_payload.lineComments:
            text_value = comment.comment.strip()
            if not text_value:
                continue
            session.add(
                LineComment(
                    side_evaluation_id=side_record.id,
                    line_number=comment.lineNumber,
                    selected_text=comment.selectedText,
                    comment_text=text_value,
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
        "evaluations": session.execute(select(func.count(EvaluationSession.id))).scalar_one(),
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
          s.id,
          s.mode,
          s.left_kind,
          s.right_kind,
          s.created_at,
          lp.source_path AS left_proof_path,
          rp.source_path AS right_proof_path,
          ln.name AS left_node_name,
          rn.name AS right_node_name,
          ql.title AS left_question_title,
          qr.title AS right_question_title
        FROM evaluation_sessions s
        LEFT JOIN proofs lp ON lp.id = s.left_proof_id
        LEFT JOIN proofs rp ON rp.id = s.right_proof_id
        LEFT JOIN nodes ln ON ln.id = s.left_node_id
        LEFT JOIN nodes rn ON rn.id = s.right_node_id
        LEFT JOIN questions ql ON ql.id = COALESCE(lp.question_id, ln.question_id)
        LEFT JOIN questions qr ON qr.id = COALESCE(rp.question_id, rn.question_id)
        ORDER BY s.id DESC
        LIMIT :limit_value
        """,
        {"limit_value": limit},
    )
    sessions: list[dict[str, Any]] = []
    for row in rows:
        side_rows = fetch_all_dicts(
            session,
            """
            SELECT id, side, clarity, conciseness, idiomatic_structure,
                   fidelity_to_nl, overall_score, general_comment, created_at
            FROM side_evaluations
            WHERE session_id = :session_id
            ORDER BY side ASC
            """,
            {"session_id": row["id"]},
        )
        for side_row in side_rows:
            comments = fetch_all_dicts(
                session,
                """
                SELECT line_number, selected_text, comment_text, created_at
                FROM line_comments
                WHERE side_evaluation_id = :side_evaluation_id
                ORDER BY id ASC
                """,
                {"side_evaluation_id": side_row["id"]},
            )
            side_row["line_comments"] = comments
        row["side_evaluations"] = side_rows
        sessions.append(row)
    return {"evaluations": sessions}
