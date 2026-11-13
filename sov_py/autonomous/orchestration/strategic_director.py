"""
Strategic Epistemic Director (Tier 1 Orchestrator).

Directs the scientific discovery search agenda by computing the hyperbolic-epistemic gradient:
Φ(H) = w_void · d_void(z_H) + w_entropy · S(ρ_H) + w_harm · V_harm(H) + w_k · Complexity(K_H)

Prioritizes conjectures situated in unmapped hyperbolic voids on 𝔻² with maximal
Bloch epistemic uncertainty S(ρ) and multi-scale k-profile complexity.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import math
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

from ..hypothesis_generator import CandidateHypothesis
from ..persistence import ReasoningStore
from ..poincare_bloch_steerer import (
    BlochEpistemicState,
    HarmonicSpectralVoidDetector,
    KProfileVector,
    PoincareManifold,
    PoincarePoint,
)


@dataclass
class ScoredEpistemicTarget:
    hypothesis: CandidateHypothesis
    score: float
    void_distance: float
    entropy_bits: float
    harmonic_void: float
    k_complexity: float
    poincare_coord: Tuple[float, float]


class StrategicEpistemicDirector:
    """Strategic orchestrator steering exploration across hyperbolic voids and epistemic entropy."""

    def __init__(
        self,
        store: Optional[ReasoningStore] = None,
        w_void: float = 2.0,
        w_entropy: float = 3.0,
        w_harm: float = 1.5,
        w_k: float = 1.0,
    ):
        self.store = store or ReasoningStore("data/reasoning_store.db")
        self.w_void = w_void
        self.w_entropy = w_entropy
        self.w_harm = w_harm
        self.w_k = w_k

        self.manifold = PoincareManifold()
        self.bloch_states: Dict[str, BlochEpistemicState] = {}
        self.k_profiles: Dict[str, KProfileVector] = {}
        self.harmonic_detector = HarmonicSpectralVoidDetector()

    def _hash_to_poincare_coords(self, text: str) -> Tuple[float, float]:
        """Deterministically map a hypothesis statement to coordinates in 𝔻."""
        h = hashlib.sha256(text.encode("utf-8")).digest()
        # Derive angle θ ∈ [0, 2π) and radius r ∈ [0.1, 0.85]
        u1 = int.from_bytes(h[:4], "big") / 0xFFFFFFFF
        u2 = int.from_bytes(h[4:8], "big") / 0xFFFFFFFF
        theta = 2.0 * math.pi * u1
        r = 0.15 + 0.70 * u2
        return float(r * math.cos(theta)), float(r * math.sin(theta))

    def register_hypothesis(
        self,
        hyp: CandidateHypothesis,
        status: str = "OPEN",
        k_profile: Optional[KProfileVector] = None,
    ) -> PoincarePoint:
        """Register hypothesis into the hyperbolic manifold and Bloch state tracker."""
        px, py = self._hash_to_poincare_coords(hyp.statement)
        point = self.manifold.add_point(
            hyp.id,
            px,
            py,
            metadata={"category": hyp.category, "predicate": hyp.predicate},
        )

        if hyp.id not in self.bloch_states:
            state = BlochEpistemicState()
            if status in ("PROVED", "CONFIRMED"):
                state.update_with_evidence("PROVED", 1.0)
            elif status in ("FALSIFIED", "REFUTED"):
                state.update_with_evidence("REFUTED", 1.0)
            self.bloch_states[hyp.id] = state

        if k_profile is not None:
            self.k_profiles[hyp.id] = k_profile
        elif hyp.id not in self.k_profiles:
            # Extract basic k-profile heuristic
            dim = hyp.parameters.get("dimension", 16)
            k_tower = dim if isinstance(dim, int) else 16
            self.k_profiles[hyp.id] = KProfileVector(
                k_rank=2 if "rank" in hyp.predicate else 1,
                k_wl=2 if "isomorphism" in hyp.statement else 1,
                k_tower=k_tower,
                k_topo=1 if "cohomology" in hyp.statement else 0,
            )

        return point

    def record_verification_result(self, hyp_id: str, status: str) -> None:
        """Update Bloch epistemic state upon verification outcome."""
        if hyp_id in self.bloch_states:
            self.bloch_states[hyp_id].update_with_evidence(status, confidence=0.95)

    def prioritize_candidates(
        self,
        candidates: List[CandidateHypothesis],
        top_k: int = 5,
    ) -> List[ScoredEpistemicTarget]:
        """Rank candidate hypotheses according to the epistemic gradient."""
        if not candidates:
            return []

        # 1. Register unmapped candidates
        for c in candidates:
            if c.id not in self.manifold.points:
                self.register_hypothesis(c)

        # 2. Build adjacency matrix for harmonic density
        node_ids = list(self.manifold.points.keys())
        n = len(node_ids)
        adj = np.zeros((n, n), dtype=float)
        for i in range(n):
            for j in range(i + 1, n):
                p_i = self.manifold.points[node_ids[i]]
                p_j = self.manifold.points[node_ids[j]]
                d_ij = p_i.hyperbolic_distance_to(p_j)
                # Gaussian affinity in hyperbolic distance
                affinity = math.exp(-0.5 * (d_ij ** 2))
                if affinity > 0.05:
                    adj[i, j] = affinity
                    adj[j, i] = affinity

        harmonic_void_scores = self.harmonic_detector.compute_harmonic_void_scores(adj, node_ids)

        # 3. Compute score Φ(H) for each candidate
        scored: List[ScoredEpistemicTarget] = []
        for c in candidates:
            p = self.manifold.get_point(c.id)
            if p is None:
                continue

            # Void distance: distance to nearest already confirmed theorem
            neighbors = self.manifold.find_nearest_neighbors(p, k=3)
            # Exclude self
            ext_neighbors = [d for nid, d in neighbors if nid != c.id]
            d_void = ext_neighbors[0] if ext_neighbors else 3.0

            # Bloch entropy
            bloch = self.bloch_states.get(c.id, BlochEpistemicState())
            s_entropy = bloch.von_neumann_entropy

            # Harmonic void
            h_void = harmonic_void_scores.get(c.id, 0.5)

            # k-profile
            kp = self.k_profiles.get(c.id, KProfileVector())
            k_comp = kp.aggregate_complexity

            # Total score
            phi = (
                self.w_void * d_void
                + self.w_entropy * s_entropy
                + self.w_harm * h_void
                + self.w_k * k_comp
            )

            scored.append(
                ScoredEpistemicTarget(
                    hypothesis=c,
                    score=float(phi),
                    void_distance=float(d_void),
                    entropy_bits=float(s_entropy),
                    harmonic_void=float(h_void),
                    k_complexity=float(k_comp),
                    poincare_coord=(p.x, p.y),
                )
            )

        scored.sort(key=lambda t: t.score, reverse=True)
        return scored[:top_k]
