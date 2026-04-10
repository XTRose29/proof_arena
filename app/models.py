from __future__ import annotations

from sqlalchemy import CheckConstraint, ForeignKey, Index, Integer, Text
from sqlalchemy.orm import Mapped, mapped_column, relationship

from .database import Base


class Question(Base):
    __tablename__ = "questions"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    canonical_key: Mapped[str] = mapped_column(Text, unique=True, nullable=False)
    title: Mapped[str] = mapped_column(Text, nullable=False)
    slug: Mapped[str] = mapped_column(Text, unique=True, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)

    proofs: Mapped[list["Proof"]] = relationship(back_populates="question", cascade="all, delete-orphan")
    nodes: Mapped[list["Node"]] = relationship(back_populates="question", cascade="all, delete-orphan")


class Proof(Base):
    __tablename__ = "proofs"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    question_id: Mapped[int] = mapped_column(ForeignKey("questions.id", ondelete="CASCADE"), nullable=False)
    title: Mapped[str] = mapped_column(Text, nullable=False)
    label: Mapped[str] = mapped_column(Text, nullable=False)
    author: Mapped[str | None] = mapped_column(Text)
    source_path: Mapped[str] = mapped_column(Text, unique=True, nullable=False)
    content: Mapped[str] = mapped_column(Text, nullable=False)
    line_count: Mapped[int] = mapped_column(Integer, nullable=False)
    node_count: Mapped[int] = mapped_column(Integer, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)

    question: Mapped[Question] = relationship(back_populates="proofs")
    nodes: Mapped[list["Node"]] = relationship(back_populates="proof", cascade="all, delete-orphan")


class Node(Base):
    __tablename__ = "nodes"
    __table_args__ = (
        Index("idx_nodes_question_id", "question_id"),
        Index("idx_nodes_proof_id", "proof_id"),
        Index("idx_nodes_name_type", "name", "node_type"),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    proof_id: Mapped[int] = mapped_column(ForeignKey("proofs.id", ondelete="CASCADE"), nullable=False)
    question_id: Mapped[int] = mapped_column(ForeignKey("questions.id", ondelete="CASCADE"), nullable=False)
    ordinal: Mapped[int] = mapped_column(Integer, nullable=False)
    name: Mapped[str] = mapped_column(Text, nullable=False)
    node_type: Mapped[str] = mapped_column(Text, nullable=False)
    declaration_kind: Mapped[str | None] = mapped_column(Text)
    declaration_name: Mapped[str | None] = mapped_column(Text)
    inputs_json: Mapped[str] = mapped_column(Text, nullable=False)
    natural_language: Mapped[str] = mapped_column(Text, nullable=False)
    nl_proof: Mapped[str] = mapped_column(Text, nullable=False)
    code: Mapped[str] = mapped_column(Text, nullable=False)
    start_line: Mapped[int] = mapped_column(Integer, nullable=False)
    end_line: Mapped[int] = mapped_column(Integer, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)

    proof: Mapped[Proof] = relationship(back_populates="nodes")
    question: Mapped[Question] = relationship(back_populates="nodes")


class EvaluationSession(Base):
    __tablename__ = "evaluation_sessions"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    mode: Mapped[str] = mapped_column(Text, nullable=False)
    left_kind: Mapped[str] = mapped_column(Text, nullable=False)
    right_kind: Mapped[str] = mapped_column(Text, nullable=False)
    left_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    right_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    left_node_id: Mapped[int | None] = mapped_column(ForeignKey("nodes.id", ondelete="SET NULL"))
    right_node_id: Mapped[int | None] = mapped_column(ForeignKey("nodes.id", ondelete="SET NULL"))
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class SideEvaluation(Base):
    __tablename__ = "side_evaluations"
    __table_args__ = (
        CheckConstraint("side IN ('left', 'right')", name="ck_side_evaluations_side"),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    session_id: Mapped[int] = mapped_column(ForeignKey("evaluation_sessions.id", ondelete="CASCADE"), nullable=False)
    side: Mapped[str] = mapped_column(Text, nullable=False)
    clarity: Mapped[int] = mapped_column(Integer, nullable=False)
    conciseness: Mapped[int] = mapped_column(Integer, nullable=False)
    idiomatic_structure: Mapped[int] = mapped_column(Integer, nullable=False)
    fidelity_to_nl: Mapped[int] = mapped_column(Integer, nullable=False)
    overall_score: Mapped[int] = mapped_column(Integer, nullable=False)
    general_comment: Mapped[str] = mapped_column(Text, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class LineComment(Base):
    __tablename__ = "line_comments"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    side_evaluation_id: Mapped[int] = mapped_column(ForeignKey("side_evaluations.id", ondelete="CASCADE"), nullable=False)
    line_number: Mapped[int] = mapped_column(Integer, nullable=False)
    selected_text: Mapped[str] = mapped_column(Text, nullable=False)
    comment_text: Mapped[str] = mapped_column(Text, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


Index("idx_proofs_question_id", Proof.question_id)
