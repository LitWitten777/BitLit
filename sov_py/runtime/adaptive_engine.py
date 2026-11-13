"""
adaptive_engine.py
==================
Phase 5: Hypernetwork Adaptation — Live Data-to-Weights Learning.

Replaces frozen weights and expanding context windows with online Bayesian
belief updating over low-rank latent codes and Curtis 35 MOG nodal basins.
Snaps continuous representations onto the E_8 root lattice using the
Conway-Sloane O(d) Closest Vector Problem (CVP) algorithm.

Key Mechanics:
  - Conway-Sloane E_8 / D_8 CVP Snapping: Integer/half-integer quantization d^2 = 2.
  - Curtis 35 MOG Basins: Nodal energy ratio E(P_k) partitioning into 35 attractors.
  - Online Bayesian Data-to-Weights: Recursive parameter updating amortizing memory
    into active operator weights.
  - Certified Negentropy State: Tracks information gain and precision matrix trace.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple
import numpy as np

from sedenion.polytope.gosset_logic import GossetLogicSynthesizer
from .geometric_lexer import GeometricFrame


@dataclass(frozen=True)
class AdaptationReceipt:
    step: int
    dominant_mog_basin: int
    basin_energy_ratio: float
    e8_lattice_point: Tuple[float, ...]
    innovation_norm: float
    weight_norm: float
    total_negentropy: float


class MOGSemanticBasins:
    """
    Evaluates semantic attractors across the Curtis 35 Miracle Octad Generator
    (MOG) tetrad partitions of {0..7}.
    """

    def __init__(self) -> None:
        self.partitions = self._generate_curtis_35()
        assert len(self.partitions) == 35

    @staticmethod
    def _generate_curtis_35() -> List[Tuple[Tuple[int, ...], Tuple[int, ...]]]:
        """Generate 35 unordered complementary 4-element tetrad pairs of {0..7}."""
        seen: set[frozenset] = set()
        parts = []
        for combo in itertools.combinations(range(8), 4):
            t1 = tuple(sorted(combo))
            t2 = tuple(sorted(set(range(8)) - set(t1)))
            key = frozenset([frozenset(t1), frozenset(t2)])
            if key not in seen:
                seen.add(key)
                parts.append((t1, t2))
        return parts

    def compute_energy_ratio(self, vec8: Sequence[float], k: int) -> float:
        """
        Nodal energy ratio:
          E(P_k) = (sum_{i in T1} v_i^2) / (sum_{j in T2} v_j^2 + eps)
        """
        if not 0 <= k < 35:
            raise IndexError(f"Basin index {k} out of range [0, 34]")
        t1, t2 = self.partitions[k]
        eps = 1e-12
        num = sum(vec8[i] ** 2 for i in t1)
        den = sum(vec8[j] ** 2 for j in t2) + eps
        return float(num / den)

    def classify_basin(self, vec: Sequence[float]) -> Tuple[int, float]:
        """
        Determines which of the 35 canonical symmetry basins the state belongs to.
        If vector length is not 8, takes the first 8 components or pads with 0.
        """
        v8 = list(vec[:8]) + [0.0] * max(0, 8 - len(vec))
        ratios = [self.compute_energy_ratio(v8, k) for k in range(35)]
        best_k = int(np.argmax(ratios))
        return best_k, float(ratios[best_k])

    @staticmethod
    def antipodal_dual(vec: Sequence[float]) -> np.ndarray:
        """Exact antipodal involution (v -> -v) on the semantic manifold."""
        return -np.array(vec, dtype=float)


class ConwaySloaneCVP:
    """
    O(d) closest-vector decoding onto the self-dual E_8 lattice:
      E_8 = D_8 U (D_8 + 1/2 * 1).
    """

    @staticmethod
    def snap_to_e8(vec8: Sequence[float]) -> Tuple[float, ...]:
        """Snaps an 8D vector to the nearest E_8 lattice point in O(d) time."""
        return GossetLogicSynthesizer.snap_to_e8_lattice(vec8)


class AdaptiveHypernetworkEngine:
    """
    Online Bayesian belief updater adapting operator weights dynamically
    from streaming geometric observations without static context window decay.
    """

    def __init__(
        self,
        dim_in: int = 21,
        dim_out: int = 21,
        learning_rate: float = 0.05,
        prior_variance: float = 1.0,
    ) -> None:
        self.dim_in = dim_in
        self.dim_out = dim_out
        self.lr = learning_rate

        # Active operator weight matrix W in R^(dim_out x dim_in)
        self.W = np.eye(dim_out, dim_in, dtype=float) * 0.1
        # Online Bayesian precision matrix P in R^(dim_in x dim_in)
        self.P = np.eye(dim_in, dtype=float) * prior_variance

        self.mog = MOGSemanticBasins()
        self.step_count = 0
        self.total_negentropy = 0.0

    def update_from_transition(
        self,
        current_frame: GeometricFrame,
        target_frame: GeometricFrame,
    ) -> AdaptationReceipt:
        """
        Observes a state transition (current -> target) in GNL and compiles
        the geometric relationship directly into operator weights via online
        Bayesian recursive least-squares.
        """
        self.step_count += 1
        x = current_frame.to_array_harmonics()
        y = target_frame.to_array_harmonics()

        # 1. Conway-Sloane E_8 snapping of the 8D dominant projection (first 7 coords + norm)
        sub_8 = list(x[:7]) + [float(np.linalg.norm(x))]
        e8_point = ConwaySloaneCVP.snap_to_e8(sub_8)

        # 2. Curtis 35 MOG Basin Classification
        basin_k, basin_ratio = self.mog.classify_basin(sub_8)

        # 3. Online Bayesian Kalman update: e = y - W x
        pred = self.W @ x
        innovation = y - pred
        innov_norm = float(np.linalg.norm(innovation))

        # Gain vector K = P x / (1 + x^T P x)
        Px = self.P @ x
        denom = 1.0 + float(x.T @ Px)
        K = Px / denom

        # Weight update: W <- W + e K^T
        self.W += self.lr * np.outer(innovation, K)

        # Precision update: P <- P - K x^T P
        self.P -= np.outer(K, x) @ self.P

        # Negentropy accumulation: log-precision trace increment
        prec_trace = float(np.trace(self.P))
        negentropy_delta = max(0.0, float(math.log1p(max(0.0, 1.0 / (innov_norm + 1e-6)))))
        self.total_negentropy += negentropy_delta

        return AdaptationReceipt(
            step=self.step_count,
            dominant_mog_basin=basin_k,
            basin_energy_ratio=basin_ratio,
            e8_lattice_point=e8_point,
            innovation_norm=innov_norm,
            weight_norm=float(np.linalg.norm(self.W)),
            total_negentropy=self.total_negentropy,
        )

    def predict_next_harmonic(self, current_frame: GeometricFrame) -> np.ndarray:
        """Projects current frame harmonics forward through adapted operator weights."""
        x = current_frame.to_array_harmonics()
        return self.W @ x
