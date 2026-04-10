from __future__ import annotations

from pydantic import BaseModel, Field


class ScoresIn(BaseModel):
    clarity: int = Field(ge=1, le=5)
    conciseness: int = Field(ge=1, le=5)
    idiomaticStructure: int = Field(ge=1, le=5)
    fidelityToNl: int = Field(ge=1, le=5)
    overall: int = Field(ge=1, le=5)


class LineCommentIn(BaseModel):
    lineNumber: int
    selectedText: str = ""
    comment: str


class EvaluationSideIn(BaseModel):
    kind: str
    entityId: int
    scores: ScoresIn
    generalComment: str = ""
    lineComments: list[LineCommentIn] = Field(default_factory=list)


class EvaluationCreate(BaseModel):
    mode: str
    left: EvaluationSideIn
    right: EvaluationSideIn
