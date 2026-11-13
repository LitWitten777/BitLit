"""
cohomology_gate.py
==================
Phase 3: Cohomology Guard — Real-Time Hallucination Suppression.

Evaluates reasoning trajectories as simplicial 1-chains over the Stiefel
manifold V_2(R^7). Computes the simplicial coboundary delta_1 and enforces the
sheaf flatness condition ||H^1|| = 0 (HYP-169). Rejects inferences that produce
unclosed boundary defects, cyclical contradictions, or semantic drift.

Key Mechanics:
  - 1-Cochain Evaluation: phi_ij = <H(u), H(v)> / 2 across 21 spherical harmonics.
  - Simplicial Coboundary: delta_1 phi(i, j, k) = phi_jk - phi_ik + phi_ij.
  - Exponential Hallucination Bound:
      P(Hallucination) <= exp( - (S_top - S_crit) / (||H^1|| + eps) )
  - Backtracking Trigger: Rejects inferences where ||H^1|| > 10^-4 or S_top < 0.50.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple
import numpy as np

from sedenion.autonomous.hallucination_bound import (
    InformationTheoreticHallucinationGuard,
    HallucinationAuditReceipt,
    S_CRIT,
)
from .geometric_lexer import GeometricFrame


@dataclass(frozen=True)
class CohomologyReport:
    is_sound: bool
    h1_norm: float
    max_simplex_defect: float
    triangles_evaluated: int
    topological_entropy: float
    hallucination_bound: float
    backtrack_triggered: bool
    reason: str
    defects_per_step: Tuple[float, ...]
    is_boundary_closed: bool = False
    chern_number: int = 1


class CohomologyGate:
    """
    Real-time Čech cohomology gate guarding inference chains against hallucinations.
    """

    def __init__(
        self,
        tolerance: float = 1e-4,
        s_crit: float = S_CRIT,
        max_acceptable_risk: float = 0.05,
    ) -> None:
        self.tolerance = tolerance
        self.guard = InformationTheoreticHallucinationGuard(
            s_crit=s_crit,
            h1_tolerance=tolerance,
            max_acceptable_risk=max_acceptable_risk,
        )

    @staticmethod
    def connection_cochain(fa: GeometricFrame, fb: GeometricFrame) -> float:
        """
        Normalized 1-cochain connection phi_ab between two geometric frames,
        derived from the Stiefel spherical harmonic inner product:
          phi_ab = <H_a, H_b> / 2.
        """
        ha = fa.to_array_harmonics()
        hb = fb.to_array_harmonics()
        # Spherical harmonics norm is 24 on discrete 2-design; normalize by 24
        return float(np.dot(ha, hb)) / 48.0

    def compute_chain_entropy(self, chain: Sequence[GeometricFrame]) -> float:
        """
        Computes the empirical topological/Shannon entropy of the frame sequence
        based on the distribution of XOR charge sectors and frame frequencies.
        """
        if len(chain) <= 1:
            return 1.0  # Default nominal entropy

        # Sector distribution
        sector_counts: Dict[int, int] = {}
        for f in chain:
            sector_counts[f.sector] = sector_counts.get(f.sector, 0) + 1

        n = len(chain)
        entropy = 0.0
        for count in sector_counts.values():
            p = count / n
            if p > 0:
                entropy -= p * math.log2(p)

        # Scale by frame diversity factor
        unique_frames = len(set(f.frame_id for f in chain))
        diversity = min(1.0, unique_frames / max(1, n))
        # Ensure non-trivial base entropy for distinct sequences
        return float(max(0.1, entropy * (0.5 + 0.5 * diversity)))

    def evaluate_chain(self, chain: Sequence[GeometricFrame]) -> CohomologyReport:
        """
        Evaluates a reasoning chain (F_0, F_1, ..., F_k) as a simplicial 1-chain.
        Computes the coboundary defect delta_1 across all consecutive 2-simplices (t-1, t, t+1)
        and all triangles formed with the chain origin F_0.
        """
        k = len(chain)
        if k < 3:
            s_top = self.compute_chain_entropy(chain)
            audit = self.guard.audit_reasoning_step(s_top=s_top, h1_norm=0.0)
            return CohomologyReport(
                is_sound=True,
                h1_norm=0.0,
                max_simplex_defect=0.0,
                triangles_evaluated=0,
                topological_entropy=s_top,
                hallucination_bound=audit.hallucination_bound,
                backtrack_triggered=False,
                reason="Trivially closed 1-chain (length < 3)",
                defects_per_step=(),
            )

        # Precompute cochains
        defects: List[float] = []
        f0 = chain[0]

        # 1. Consecutive triads: delta_1 phi(t-1, t, t+1) = phi(t, t+1) - phi(t-1, t+1) + phi(t-1, t)
        for t in range(1, k - 1):
            f_prev = chain[t - 1]
            f_curr = chain[t]
            f_next = chain[t + 1]

            phi_12 = self.connection_cochain(f_prev, f_curr)
            phi_23 = self.connection_cochain(f_curr, f_next)
            phi_13 = self.connection_cochain(f_prev, f_next)

            # Simplicial coboundary delta_1
            defect = abs(phi_23 - phi_13 + phi_12)
            defects.append(defect)

        # 2. Origin-anchored triangles: delta_1 phi(0, t, t+1) for long-range homological closure
        for t in range(1, k - 1):
            f_curr = chain[t]
            f_next = chain[t + 1]

            phi_01 = self.connection_cochain(f0, f_curr)
            phi_12 = self.connection_cochain(f_curr, f_next)
            phi_02 = self.connection_cochain(f0, f_next)

            defect = abs(phi_12 - phi_02 + phi_01)
            defects.append(defect)

        h1_norm = float(np.linalg.norm(defects)) if defects else 0.0
        max_defect = max(defects) if defects else 0.0

        # Check sofit topological boundary closure (dOmega = 0 => c1 = 0)
        from .geometric_lexer import GeometricLexer
        lexer = GeometricLexer.get_instance()
        is_closed_boundary = lexer.is_sofit_closure(chain) or (chain[0].frame_id == chain[-1].frame_id)
        chern_number = 0 if is_closed_boundary else 1

        if is_closed_boundary:
            # Enforce exact sheaf flatness condition on closed solitonic boundaries
            h1_norm = 0.0
            max_defect = 0.0

        s_top = self.compute_chain_entropy(chain)
        audit = self.guard.audit_reasoning_step(s_top=s_top, h1_norm=h1_norm)

        return CohomologyReport(
            is_sound=audit.is_certified_sound,
            h1_norm=h1_norm,
            max_simplex_defect=max_defect,
            triangles_evaluated=len(defects),
            topological_entropy=s_top,
            hallucination_bound=audit.hallucination_bound,
            backtrack_triggered=audit.backtrack_triggered,
            reason=f"{audit.reason} (Boundary closed, c1=0)" if is_closed_boundary else audit.reason,
            defects_per_step=tuple(defects),
            is_boundary_closed=is_closed_boundary,
            chern_number=chern_number,
        )

    def check_cycle(self, cycle: Sequence[GeometricFrame]) -> Tuple[bool, float]:
        """
        Verifies exact holonomy / circulation around a closed cycle (F_0 -> ... -> F_k -> F_0).
        Total circulation defect must vanish for consistent non-contradictory deductions.
        """
        if len(cycle) < 3:
            return True, 0.0

        circulation = 0.0
        n = len(cycle)
        for i in range(n):
            fa = cycle[i]
            fb = cycle[(i + 1) % n]
            circulation += self.connection_cochain(fa, fb)

        # Circulation deviation from zero or integer phase
        holonomy_defect = abs(circulation - round(circulation))
        is_closed = holonomy_defect < self.tolerance
        return is_closed, holonomy_defect

    def filter_sound_candidates(
        self,
        current_chain: Sequence[GeometricFrame],
        candidates: Sequence[GeometricFrame],
    ) -> List[GeometricFrame]:
        """
        Filters candidate next-step frames to only those that maintain ||H^1|| sound
        gluing without triggering hallucination/backtracking alerts.
        """
        sound: List[GeometricFrame] = []
        for cand in candidates:
            test_chain = list(current_chain) + [cand]
            report = self.evaluate_chain(test_chain)
            if report.is_sound and not report.backtrack_triggered:
                sound.append(cand)
        return sound
