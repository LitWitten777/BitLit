"""
src/crucible/justification.py
Justification records for Crucible operator outputs.

Author: EngA
Version: 0.1.0
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


class JustificationStatus(str, Enum):
    SUPPORTED   = "supported"
    CONTESTED   = "contested"
    REFUTED     = "refuted"
    PENDING     = "pending"


@dataclass
class Justification:
    """
    Records why a Crucible operator produced a given output.
    Stored in CrucibleContext.justifications and surfaced in traces.
    """
    justification_id: str
    operator: str
    input_ids: list[str]
    output_id: str
    context_id: str
    elapsed_ms: float
    status: JustificationStatus = JustificationStatus.PENDING
    notes: str = ""
    confidence: float = 1.0
    counterexample_id: Optional[str] = None

    def to_dict(self) -> dict:
        return {
            "justification_id": self.justification_id,
            "operator": self.operator,
            "input_ids": self.input_ids,
            "output_id": self.output_id,
            "context_id": self.context_id,
            "elapsed_ms": round(self.elapsed_ms, 2),
            "status": self.status.value,
            "notes": self.notes,
            "confidence": self.confidence,
            "counterexample_id": self.counterexample_id,
        }


@dataclass
class JustificationChain:
    """
    An ordered chain of Justifications constituting a proof or derivation path.
    """
    chain_id: str
    justifications: list[Justification] = field(default_factory=list)

    def append(self, j: Justification) -> None:
        self.justifications.append(j)

    def is_valid(self) -> bool:
        return all(
            j.status in (JustificationStatus.SUPPORTED, JustificationStatus.PENDING)
            for j in self.justifications
        )

    def to_dict(self) -> dict:
        return {
            "chain_id": self.chain_id,
            "valid": self.is_valid(),
            "steps": [j.to_dict() for j in self.justifications],
        }
