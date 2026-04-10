from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, Field


PreferenceValue = Literal["a_way_better", "a_better", "no_difference", "b_better", "b_way_better"]


class RegisterRequest(BaseModel):
    email: str = Field(min_length=3, max_length=320)
    password: str = Field(min_length=8, max_length=200)
    displayName: str = Field(min_length=1, max_length=200)
    affiliation: str = Field(default="", max_length=200)
    experienceLevel: str = Field(default="", max_length=200)


class LoginRequest(BaseModel):
    email: str = Field(min_length=3, max_length=320)
    password: str = Field(min_length=1, max_length=200)


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
    kind: Literal["proof", "node"]
    entityId: int


class PreferenceScoresIn(BaseModel):
    clarity: PreferenceValue
    conciseness: PreferenceValue
    idiomaticStructure: PreferenceValue
    overall: PreferenceValue


class PreferenceEvaluationCreate(BaseModel):
    mode: str
    a: ComparisonEntityRef
    b: ComparisonEntityRef
    preferences: PreferenceScoresIn
    generalComment: str = Field(default="", max_length=5000)
