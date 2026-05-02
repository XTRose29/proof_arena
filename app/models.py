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


class User(Base):
    __tablename__ = "users"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    email: Mapped[str] = mapped_column(Text, unique=True, nullable=False)
    display_name: Mapped[str] = mapped_column(Text, nullable=False)
    password_hash: Mapped[str] = mapped_column(Text, nullable=False)
    password_salt: Mapped[str] = mapped_column(Text, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class AuthToken(Base):
    __tablename__ = "auth_tokens"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    token: Mapped[str] = mapped_column(Text, unique=True, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class PreferenceEvaluation(Base):
    __tablename__ = "preference_evaluations"
    __table_args__ = (
        Index("idx_preference_evaluations_user_id", "user_id"),
        Index("idx_preference_evaluations_user_node_a", "user_id", "entity_a_node_id"),
        Index("idx_preference_evaluations_user_node_b", "user_id", "entity_b_node_id"),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    mode: Mapped[str] = mapped_column(Text, nullable=False)
    entity_a_kind: Mapped[str] = mapped_column(Text, nullable=False)
    entity_b_kind: Mapped[str] = mapped_column(Text, nullable=False)
    entity_a_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    entity_b_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    entity_a_node_id: Mapped[int | None] = mapped_column(ForeignKey("nodes.id", ondelete="SET NULL"))
    entity_b_node_id: Mapped[int | None] = mapped_column(ForeignKey("nodes.id", ondelete="SET NULL"))
    evaluator_display_name: Mapped[str] = mapped_column(Text, nullable=False)
    evaluator_affiliation: Mapped[str] = mapped_column(Text, nullable=False)
    evaluator_experience_level: Mapped[str] = mapped_column(Text, nullable=False)
    general_comment: Mapped[str] = mapped_column(Text, nullable=False, default="")
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class PreferenceVote(Base):
    __tablename__ = "preference_votes"
    __table_args__ = (
        Index("idx_preference_votes_evaluation_id", "evaluation_id"),
        CheckConstraint(
            "criterion IN ('clarity', 'conciseness', 'idiomatic_structure', 'overall')",
            name="ck_preference_votes_criterion",
        ),
        CheckConstraint(
            "preference IN ('a_way_better', 'a_better', 'no_difference', 'b_better', 'b_way_better')",
            name="ck_preference_votes_preference",
        ),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    evaluation_id: Mapped[int] = mapped_column(
        ForeignKey("preference_evaluations.id", ondelete="CASCADE"),
        nullable=False,
    )
    criterion: Mapped[str] = mapped_column(Text, nullable=False)
    preference: Mapped[str] = mapped_column(Text, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


Index("idx_proofs_question_id", Proof.question_id)
