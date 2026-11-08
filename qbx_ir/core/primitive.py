"""
Primitive types for QBX-IR.

- Strand: a labeled line in the braid.
- Generator: σ_i^{±1} — the atomic braid operation.
- Crossing: a resolved crossing between two specific strands (used in views).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Optional, Tuple


@dataclass(frozen=True)
class Strand:
    """
    A single strand in the braid.

    The strand ID is 1-indexed and refers to the initial (bottom) position.
    """

    id: int
    particle_type: str = "line"
    state: Optional[str] = None
    orientation: int = 1  # +1 (time-up) or -1 (time-down)
    geometry: Optional[Tuple[float, ...]] = None  # optional E8 coordinate

    def __post_init__(self):
        if self.id < 1:
            raise ValueError(f"Strand id must be ≥ 1, got {self.id}")
        if self.orientation not in (-1, 1):
            raise ValueError(f"Orientation must be ±1, got {self.orientation}")


@dataclass(frozen=True)
class Generator:
    """
    A single braid generator σ_i^{sign}.

    - index (i): crosses strands at positions i and i+1 (1-indexed)
    - sign: +1 for σ_i, -1 for σ_i⁻¹
    """

    index: int
    sign: int

    def __post_init__(self):
        if self.index < 1:
            raise ValueError(f"Generator index must be ≥ 1, got {self.index}")
        if self.sign not in (-1, 1):
            raise ValueError(f"Generator sign must be ±1, got {self.sign}")

    def inverse(self) -> "Generator":
        return Generator(self.index, -self.sign)

    def to_short(self) -> int:
        """Short form: positive int for σ_i, negative for σ_i⁻¹."""
        return self.sign * self.index

    def __str__(self) -> str:
        if self.sign == 1:
            return f"σ_{self.index}"
        return f"σ_{self.index}⁻¹"

    def __repr__(self) -> str:
        return f"Generator(index={self.index}, sign={self.sign})"

    @classmethod
    def from_short(cls, n: int) -> "Generator":
        """Build from short form: +i → σ_i, -i → σ_i⁻¹."""
        if n == 0:
            raise ValueError("Generator short form cannot be 0")
        return cls(abs(n), 1 if n > 0 else -1)


@dataclass
class Crossing:
    """
    A resolved crossing between two specific strands.

    Unlike Generator (which is symbolic), a Crossing knows the actual
    strand IDs involved. Used by views that need strand-level detail.
    """

    left_strand_id: int
    right_strand_id: int
    sign: int
    r_label: Optional[Tuple[str, str, str]] = None  # (a, b, c) fusion channel
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __str__(self) -> str:
        op = "×" if self.sign == 1 else "×⁻¹"
        return f"({self.left_strand_id} {op} {self.right_strand_id})"
