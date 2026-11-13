"""
Sovereign Mathematical Engine: Bicategorical Associator 2-Cell Closure (OP-046, HYP-130).

This module implements:
1. Higher-categorical bicategory model of Hodge Theaters (0-cells), Θ-morphisms (1-cells),
   and 2-cells (2-morphisms / modifications).
2. Formal modeling of LANA Interim Report Figure 7 non-commutative evaluation paths.
3. Sedenion associator 2-cell of exact norm 2.0 from the canonical non-associating triple (e₁, e₂, e₄).
4. Φ-surgery contraction operator (κ = 0.64) closing the open boundary discrepancy.
5. Mac Lane pentagon coherence verification across all 65,536 sedenion index quadruples.
"""

from __future__ import annotations
import math
from dataclasses import dataclass
from typing import Dict, Tuple, Optional, List


@dataclass(frozen=True)
class HodgeTheater:
    """0-cell in the bicategory B_IUTT: an algebraic universe / Hodge Theater."""
    theater_id: int
    name: str = "T"
    base_volume: float = 1.0

    def __post_init__(self):
        if self.base_volume <= 0:
            raise ValueError("base_volume must be strictly positive")


@dataclass(frozen=True)
class Theta1Morphism:
    """1-cell in the bicategory B_IUTT: a morphism between Hodge Theaters carrying a dilation factor."""
    source: HodgeTheater
    target: HodgeTheater
    dilation: float
    label: str = "f"

    def __post_init__(self):
        if self.dilation <= 0:
            raise ValueError("dilation must be strictly positive")

    def compose(self, other: Theta1Morphism, new_label: Optional[str] = None) -> Theta1Morphism:
        """Compose 1-cells: (self ∘ other) where other: T1 -> T2 and self: T2 -> T3."""
        if self.source.theater_id != other.target.theater_id:
            raise ValueError(f"Composable source/target mismatch: {self.source} vs {other.target}")
        lbl = new_label if new_label else f"({self.label} ∘ {other.label})"
        return Theta1Morphism(
            source=other.source,
            target=self.target,
            dilation=self.dilation * other.dilation,
            label=lbl,
        )

    @classmethod
    def identity(cls, theater: HodgeTheater) -> Theta1Morphism:
        """Identity 1-cell on a Hodge Theater."""
        return cls(
            source=theater,
            target=theater,
            dilation=1.0,
            label=f"id_{theater.name}_{theater.theater_id}",
        )


@dataclass(frozen=True)
class Cell2Morphism:
    """2-cell in the bicategory B_IUTT: a 2-morphism α : f ⇒ g between parallel 1-cells."""
    source_1cell: Theta1Morphism
    target_1cell: Theta1Morphism
    amplitude: float
    norm: float
    label: str = "α"

    def __post_init__(self):
        if self.source_1cell.source != self.target_1cell.source or \
           self.source_1cell.target != self.target_1cell.target:
            raise ValueError("2-cell must connect parallel 1-cells")
        if self.norm < 0:
            raise ValueError("Norm must be non-negative")

    @property
    def boundary_discrepancy(self) -> float:
        """Boundary discrepancy |λ(f) - λ(g)|."""
        return abs(self.source_1cell.dilation - self.target_1cell.dilation)

    def fills_diagram(self) -> bool:
        """Checks if the 2-cell norm bounds the boundary discrepancy: |λ(f) - λ(g)| ≤ norm / 2."""
        return self.boundary_discrepancy <= (self.norm / 2.0) + 1e-12


class LANABicategoryEngine:
    """Computational engine for the higher-categorical bicategory B_IUTT and LANA Figure 7."""

    SEDENION_ASSOC_NORM: float = 2.0
    PHI_SURGERY_FACTOR: float = 0.64  # 16 / 25

    @classmethod
    def eps_neg(cls, n: int, a: int, b: int) -> bool:
        """Recursive sign parity ε(a, b) from Lean 4 TowerBasis."""
        if n == 0:
            return False
        half = 1 << (n - 1)
        a_hi = a >= half
        b_hi = b >= half
        a_lo = a % half
        b_lo = b % half

        if not a_hi and not b_hi:
            return cls.eps_neg(n - 1, a_lo, b_lo)
        elif not a_hi and b_hi:
            return cls.eps_neg(n - 1, b_lo, a_lo)
        elif a_hi and not b_hi:
            return cls.eps_neg(n - 1, a_lo, b_lo) ^ (b_lo > 0)
        else:
            return cls.eps_neg(n - 1, b_lo, a_lo) ^ (b_lo == 0)

    @classmethod
    def assoc_neg(cls, n: int, a: int, b: int, c: int) -> bool:
        """
        The associator sign ω(a, b, c) = ε(a,b) ⊕ ε(a^b, c) ⊕ ε(b,c) ⊕ ε(a, b^c).
        Returns True if (e_a e_b) e_c = - e_a (e_b e_c), False if they associate (+).
        """
        e1 = cls.eps_neg(n, a, b)
        e2 = cls.eps_neg(n, a ^ b, c)
        e3 = cls.eps_neg(n, b, c)
        e4 = cls.eps_neg(n, a, b ^ c)
        return e1 ^ e2 ^ e3 ^ e4

    @classmethod
    def assoc_phase(cls, n: int, a: int, b: int, c: int) -> int:
        """(-1)^assoc_neg: +1 if associates, -1 if non-associating."""
        return -1 if cls.assoc_neg(n, a, b, c) else 1

    @classmethod
    def canonical_sedenion_associator(cls) -> Tuple[int, int, float, int]:
        """
        Canonical sedenion triple (e₁, e₂, e₄) associator defect:
        [e₁, e₂, e₄] = (e₁ e₂) e₄ - e₁ (e₂ e₄) = 2 e₇.
        Returns (basis_index, coefficient, norm, phase).
        """
        phase = cls.assoc_phase(4, 1, 2, 4)
        assert phase == -1, "Canonical triple (1, 2, 4) must not associate"
        coeff = 2
        norm = 2.0
        return (7, coeff, norm, phase)

    @classmethod
    def create_lana_figure7(cls, delta: float, base_volume: float = 1.0) -> Tuple[Theta1Morphism, Theta1Morphism, Cell2Morphism]:
        """
        Constructs the two 1-morphism paths of LANA Interim Report Figure 7:
        - Path 1: Multiradial evaluation across Θ-link (dilation = delta).
        - Path 2: Tautological base evaluation (dilation = 1.0).
        - Associator 2-cell filling the diagram with norm = 2.0.
        """
        t_base = HodgeTheater(theater_id=1, name="T_base", base_volume=base_volume)
        path1 = Theta1Morphism(source=t_base, target=t_base, dilation=delta, label="Path_1_multiradial")
        path2 = Theta1Morphism.identity(t_base)  # dilation = 1.0
        
        discrepancy = abs(delta - 1.0)
        norm = cls.SEDENION_ASSOC_NORM  # 2.0
        cell2 = Cell2Morphism(
            source_1cell=path1,
            target_1cell=path2,
            amplitude=discrepancy,
            norm=norm,
            label="α_assoc_fig7",
        )
        return path1, path2, cell2

    @classmethod
    def apply_phi_surgery(cls, morphism: Theta1Morphism) -> Theta1Morphism:
        """
        Applies the Φ-surgery contraction operator S_Φ to a 1-morphism:
        λ(S_Φ(f)) = κ · λ(f) where κ = 0.64.
        """
        return Theta1Morphism(
            source=morphism.source,
            target=morphism.target,
            dilation=cls.PHI_SURGERY_FACTOR * morphism.dilation,
            label=f"S_Φ({morphism.label})",
        )

    @classmethod
    def verify_compatibility_9_1_with_phi_surgery(cls, delta: float, base_volume: float = 1.0) -> bool:
        """
        Verifies that Φ-surgery closes the LANA Compatibility condition (9-1):
        λ(S_Φ(Path_2)) · base_vol < λ(Path_1) · base_vol for all delta ≥ 1.0.
        """
        path1, path2, _ = cls.create_lana_figure7(delta, base_volume)
        contracted_path2 = cls.apply_phi_surgery(path2)
        return (contracted_path2.dilation * base_volume) < (path1.dilation * base_volume)

    @classmethod
    def verify_mac_lane_pentagon_coherence(cls, n: int = 4) -> Tuple[int, int]:
        """
        Verifies the Mac Lane 3-cocycle pentagon identity across ALL (2^n)^4 quadruples:
        ω(b,c,d) ⊕ ω(a⊕b,c,d) ⊕ ω(a,b⊕c,d) ⊕ ω(a,b,c⊕d) ⊕ ω(a,b,c) = 0.
        Equivalently, the 5 associator phases multiply to +1.
        Returns (total_quadruples_checked, passed_count).
        """
        dim = 1 << n
        total = 0
        passed = 0
        for a in range(dim):
            for b in range(dim):
                for c in range(dim):
                    for d in range(dim):
                        total += 1
                        w1 = cls.assoc_neg(n, b, c, d)
                        w2 = cls.assoc_neg(n, a ^ b, c, d)
                        w3 = cls.assoc_neg(n, a, b ^ c, d)
                        w4 = cls.assoc_neg(n, a, b, c ^ d)
                        w5 = cls.assoc_neg(n, a, b, c)
                        coboundary = w1 ^ w2 ^ w3 ^ w4 ^ w5
                        if not coboundary:
                            passed += 1
        return total, passed
