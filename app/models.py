from __future__ import annotations

from sqlalchemy import Boolean, CheckConstraint, ForeignKey, Index, Integer, Text, UniqueConstraint
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
    created_at: Mapped[str] = mapped_column(Text, nullable=False)

    question: Mapped[Question] = relationship(back_populates="proofs")


class User(Base):
    __tablename__ = "users"

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    email: Mapped[str] = mapped_column(Text, unique=True, nullable=False)
    display_name: Mapped[str] = mapped_column(Text, nullable=False)
    affiliation: Mapped[str] = mapped_column(Text, nullable=False, default="")
    experience_level: Mapped[str] = mapped_column(Text, nullable=False, default="")
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
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    entity_a_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    entity_b_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    evaluator_display_name: Mapped[str] = mapped_column(Text, nullable=False)
    general_comment: Mapped[str] = mapped_column(Text, nullable=False, default="")
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class PreferenceVote(Base):
    __tablename__ = "preference_votes"
    __table_args__ = (
        Index("idx_preference_votes_evaluation_id", "evaluation_id"),
        CheckConstraint(
            "criterion IN ('reuse', 'naming', 'documentation', 'proof_quality', 'overall')",
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


class MetaReviewSession(Base):
    __tablename__ = "meta_review_sessions"
    __table_args__ = (
        Index("idx_meta_review_sessions_user_id", "user_id"),
        Index("idx_meta_review_sessions_featured", "is_featured"),
        CheckConstraint(
            "source_kind IN ('database', 'upload')",
            name="ck_meta_review_sessions_source_kind",
        ),
        CheckConstraint(
            "selected_evaluation IN ('a', 'b', 'tie') OR selected_evaluation IS NULL",
            name="ck_meta_review_sessions_selected_evaluation",
        ),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    source_proof_id: Mapped[int | None] = mapped_column(ForeignKey("proofs.id", ondelete="SET NULL"))
    source_kind: Mapped[str] = mapped_column(Text, nullable=False)
    source_title: Mapped[str] = mapped_column(Text, nullable=False)
    proof_content: Mapped[str] = mapped_column(Text, nullable=False)
    rubric_text: Mapped[str] = mapped_column(Text, nullable=False)
    evaluation_a: Mapped[str] = mapped_column(Text, nullable=False)
    evaluation_b: Mapped[str] = mapped_column(Text, nullable=False)
    model_a: Mapped[str] = mapped_column(Text, nullable=False)
    model_b: Mapped[str] = mapped_column(Text, nullable=False)
    is_featured: Mapped[bool] = mapped_column(Boolean, nullable=False, default=False)
    selected_evaluation: Mapped[str | None] = mapped_column(Text)
    selection_reason: Mapped[str] = mapped_column(Text, nullable=False, default="")
    created_at: Mapped[str] = mapped_column(Text, nullable=False)
    selected_at: Mapped[str | None] = mapped_column(Text)


class MetaReviewVote(Base):
    __tablename__ = "meta_review_votes"
    __table_args__ = (
        Index("idx_meta_review_votes_session_id", "session_id"),
        Index("idx_meta_review_votes_user_id", "user_id"),
        UniqueConstraint("session_id", "user_id", name="uq_meta_review_votes_session_user"),
        CheckConstraint(
            "choice IN ('a', 'b', 'tie')",
            name="ck_meta_review_votes_choice",
        ),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    session_id: Mapped[int] = mapped_column(
        ForeignKey("meta_review_sessions.id", ondelete="CASCADE"),
        nullable=False,
    )
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    choice: Mapped[str] = mapped_column(Text, nullable=False)
    reason: Mapped[str] = mapped_column(Text, nullable=False, default="")
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class MetaReviewCriterionVote(Base):
    __tablename__ = "meta_review_criterion_votes"
    __table_args__ = (
        Index("idx_meta_review_criterion_votes_vote_id", "vote_id"),
        UniqueConstraint("vote_id", "criterion", name="uq_meta_review_criterion_vote"),
        CheckConstraint(
            "criterion IN ('reuse', 'naming', 'documentation', 'proof_quality', 'overall')",
            name="ck_meta_review_criterion_votes_criterion",
        ),
        CheckConstraint(
            "choice IN ('a', 'b', 'tie')",
            name="ck_meta_review_criterion_votes_choice",
        ),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    vote_id: Mapped[int] = mapped_column(
        ForeignKey("meta_review_votes.id", ondelete="CASCADE"),
        nullable=False,
    )
    criterion: Mapped[str] = mapped_column(Text, nullable=False)
    choice: Mapped[str] = mapped_column(Text, nullable=False)
    created_at: Mapped[str] = mapped_column(Text, nullable=False)


class MetaReviewDraft(Base):
    __tablename__ = "meta_review_drafts"
    __table_args__ = (
        Index("idx_meta_review_drafts_session_id", "session_id"),
        Index("idx_meta_review_drafts_user_id", "user_id"),
        UniqueConstraint("session_id", "user_id", name="uq_meta_review_drafts_session_user"),
    )

    id: Mapped[int] = mapped_column(Integer, primary_key=True, autoincrement=True)
    session_id: Mapped[int] = mapped_column(
        ForeignKey("meta_review_sessions.id", ondelete="CASCADE"),
        nullable=False,
    )
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    choices_json: Mapped[str] = mapped_column(Text, nullable=False, default="{}")
    reason: Mapped[str] = mapped_column(Text, nullable=False, default="")
    updated_at: Mapped[str] = mapped_column(Text, nullable=False)


Index("idx_proofs_question_id", Proof.question_id)
