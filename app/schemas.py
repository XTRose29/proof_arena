from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, Field, model_validator


PreferenceValue = Literal["a_way_better", "a_better", "no_difference", "b_better", "b_way_better"]
MetaReviewChoice = Literal["a", "b", "tie"]


class RegisterRequest(BaseModel):
    email: str = Field(min_length=3, max_length=320)
    password: str = Field(min_length=8, max_length=200)
    displayName: str = Field(min_length=1, max_length=200)
    affiliation: str = Field(default="", max_length=200)
    experienceLevel: str = Field(default="", max_length=200)


class LoginRequest(BaseModel):
    email: str = Field(min_length=3, max_length=320)
    password: str = Field(min_length=1, max_length=200)


class GoogleAuthRequest(BaseModel):
    credential: str = Field(min_length=1, max_length=8000)


class UpdateProfileRequest(BaseModel):
    displayName: str = Field(min_length=1, max_length=200)
    affiliation: str = Field(default="", max_length=200)
    experienceLevel: str = Field(default="", max_length=200)


class UserPayload(BaseModel):
    id: int
    email: str
    displayName: str
    affiliation: str
    experienceLevel: str


class AuthResponse(BaseModel):
    token: str
    user: UserPayload


class EvaluationMetaIn(BaseModel):
    displayName: str = Field(min_length=1, max_length=200)
    affiliation: str = Field(default="", max_length=200)
    experienceLevel: str = Field(default="", max_length=200)


class ComparisonEntityRef(BaseModel):
    kind: Literal["proof"]
    entityId: int


class PreferenceScoresIn(BaseModel):
    reuse: PreferenceValue
    naming: PreferenceValue
    documentation: PreferenceValue
    proofQuality: PreferenceValue
    overall: PreferenceValue


class PreferenceEvaluationCreate(BaseModel):
    mode: Literal["same_question_proofs"]
    a: ComparisonEntityRef
    b: ComparisonEntityRef
    preferences: PreferenceScoresIn
    evaluator: EvaluationMetaIn | None = None
    generalComment: str = Field(default="", max_length=5000)


class MetaReviewGenerateRequest(BaseModel):
    proofId: int | None = Field(default=None, ge=1)
    customTitle: str = Field(default="Uploaded Lean proof", max_length=300)
    customProof: str = Field(default="", max_length=80000)

    @model_validator(mode="after")
    def has_exactly_one_source(self) -> "MetaReviewGenerateRequest":
        has_database_proof = self.proofId is not None
        has_uploaded_proof = bool(self.customProof.strip())
        if has_database_proof == has_uploaded_proof:
            raise ValueError("Provide either a database proof or uploaded Lean text.")
        return self


class MetaReviewDraftChoices(BaseModel):
    reuse: MetaReviewChoice | None = None
    naming: MetaReviewChoice | None = None
    documentation: MetaReviewChoice | None = None
    proofQuality: MetaReviewChoice | None = None
    overall: MetaReviewChoice | None = None


class MetaReviewChoices(BaseModel):
    reuse: MetaReviewChoice
    naming: MetaReviewChoice
    documentation: MetaReviewChoice
    proofQuality: MetaReviewChoice
    overall: MetaReviewChoice


class MetaReviewDraftRequest(BaseModel):
    choices: MetaReviewDraftChoices
    reason: str = Field(default="", max_length=5000)


class MetaReviewSelectionRequest(BaseModel):
    choices: MetaReviewChoices
    reason: str = Field(default="", max_length=5000)
