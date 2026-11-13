"""
src/sedenion/polytope/geometric_reasoner.py
=============================================================================
Sublattice Geometric Reasoner & E8 Weyl Forward Chaining.
Implements non-propositional logical syllogisms, Conway-Sloane E8 CVP analogy
solving, hyperplane reflection forward chaining, and antipodal contradiction checks.
=============================================================================
"""

import math
import itertools
from typing import Any, Dict, List, Optional, Sequence, Tuple
import numpy as np


class SublatticeReasoner:
    """
    Geometric reasoner operating over the E8 root system and lattice.
    Transforms symbolic logic into continuous and discrete geometric invariants:
    - Syllogisms as minimal root-distance steps (d = sqrt(2)).
    - Forward-chaining deduction as Weyl reflections across hyperplanes.
    - Contradictions as antipodal vector cancellations.
    - Analogies as closest vector problem (CVP) projections in E8.
    """

    def __init__(self):
        self._roots = self._generate_e8_roots()
        self._root_norms = np.sum(self._roots ** 2, axis=1)

    @staticmethod
    def _generate_e8_roots() -> np.ndarray:
        """Generate 240 minimal roots of the E8 lattice (norm squared = 2)."""
        roots = []
        # 112 D8 integer roots
        for i, j in itertools.combinations(range(8), 2):
            for s1 in (-1.0, 1.0):
                for s2 in (-1.0, 1.0):
                    v = np.zeros(8, dtype=float)
                    v[i] = s1
                    v[j] = s2
                    roots.append(v)

        # 128 half-integer spinor roots
        for signs in itertools.product((-0.5, 0.5), repeat=8):
            if sum(1 for s in signs if s < 0) % 2 == 0:
                roots.append(np.array(signs, dtype=float))

        return np.array(roots, dtype=float)

    @property
    def roots(self) -> np.ndarray:
        return self._roots

    @staticmethod
    def cvp_d8(x: np.ndarray) -> np.ndarray:
        """
        Conway-Sloane Closest Vector Problem (CVP) for D8 lattice:
        Integer vectors with even sum.
        """
        f = np.round(x)
        if np.sum(f) % 2 != 0:
            diffs = np.abs(x - f)
            worst_idx = int(np.argmax(diffs))
            f[worst_idx] += 1.0 if x[worst_idx] >= f[worst_idx] else -1.0
        return f

    def cvp_e8(self, x: Sequence[float]) -> List[float]:
        """
        Conway-Sloane Fast CVP for E8 lattice:
        E8 = D8 U (D8 + 1/2 * 1)
        """
        arr = np.array(x, dtype=float)
        p1 = self.cvp_d8(arr)
        shifted = arr - 0.5
        p2 = self.cvp_d8(shifted) + 0.5

        d1 = np.sum((arr - p1) ** 2)
        d2 = np.sum((arr - p2) ** 2)

        return (p1 if d1 <= d2 else p2).tolist()

    # Alias for convenience
    snap_to_e8 = cvp_e8

    def snap_to_nearest_root(self, x: Sequence[float]) -> List[float]:
        """Find the nearest of the 240 minimal E8 roots to vector x."""
        arr = np.array(x, dtype=float)
        dists = np.sum((self._roots - arr) ** 2, axis=1)
        best_idx = int(np.argmin(dists))
        return self._roots[best_idx].tolist()

    def check_contradiction(self, v1: Sequence[float], v2: Sequence[float], tol: float = 1e-5) -> bool:
        """
        Check if two vectors are strictly contradictory (antipodal opposite: v1 + v2 = 0).
        For normalized roots, <v1, v2> = -2.
        """
        if len(v1) != len(v2):
            return False
        arr1 = np.array(v1, dtype=float)
        arr2 = np.array(v2, dtype=float)
        return float(np.linalg.norm(arr1 + arr2)) < tol

    def evaluate_syllogism(
        self,
        major: Sequence[float],
        minor: Sequence[float],
        conclusion: Sequence[float],
        tol: float = 0.05
    ) -> Dict[str, Any]:
        """
        Evaluate a syllogism Major -> Minor -> Conclusion in E8.
        A valid syllogism step is a contiguous edge walk where each step length
        is exactly sqrt(2) (<u, v> = 1.0).
        """
        m = np.array(major, dtype=float)
        n = np.array(minor, dtype=float)
        c = np.array(conclusion, dtype=float)

        step1 = n - m
        step2 = c - n
        dist1 = float(np.linalg.norm(step1))
        dist2 = float(np.linalg.norm(step2))
        total_dist = float(np.linalg.norm(c - m))

        inner1 = float(np.dot(m, n))
        inner2 = float(np.dot(n, c))

        step1_valid = abs(dist1 - math.sqrt(2.0)) < tol
        step2_valid = abs(dist2 - math.sqrt(2.0)) < tol
        valid = step1_valid and step2_valid

        return {
            "valid": valid,
            "step1_valid": step1_valid,
            "step2_valid": step2_valid,
            "step1_dist": dist1,
            "step2_dist": dist2,
            "total_dist": total_dist,
            "inner_major_minor": inner1,
            "inner_minor_conclusion": inner2,
            "contradiction": self.check_contradiction(m, c)
        }

    def forward_chain_step(
        self,
        fact: Sequence[float],
        rule_root: Sequence[float]
    ) -> Tuple[List[float], Dict[str, Any]]:
        """
        Execute forward-chaining deduction as a Weyl reflection across hyperplane root alpha:
        s_alpha(v) = v - 2 * (<v, alpha> / <alpha, alpha>) * alpha
        For norm-2 roots: s_alpha(v) = v - <v, alpha> * alpha
        """
        v = np.array(fact, dtype=float)
        alpha = np.array(rule_root, dtype=float)

        norm_sq = float(np.dot(alpha, alpha))
        if norm_sq < 1e-9:
            raise ValueError("Rule root cannot be zero vector.")

        inner = float(np.dot(v, alpha))
        # Rule activates when inner != 0
        reflected = v - (2.0 * inner / norm_sq) * alpha

        trace = {
            "activated": abs(inner) > 1e-9,
            "inner_product": inner,
            "input_norm": float(np.linalg.norm(v)),
            "output_norm": float(np.linalg.norm(reflected)),
            "orthogonal": abs(inner) < 1e-9
        }

        return reflected.tolist(), trace

    def solve_analogy(
        self,
        a: Sequence[float],
        b: Sequence[float],
        c: Sequence[float],
        target: str = "root"
    ) -> List[float]:
        """
        Solve geometric analogy A : B :: C : D via parallelogram offset D = C + (B - A)
        projected onto E8.
        """
        arr_a = np.array(a, dtype=float)
        arr_b = np.array(b, dtype=float)
        arr_c = np.array(c, dtype=float)

        d_raw = arr_c + (arr_b - arr_a)

        if target == "root":
            return self.snap_to_nearest_root(d_raw)
        elif target == "lattice":
            return self.cvp_e8(d_raw)
        else:
            raise ValueError(f"Unknown target mode '{target}'. Must be 'root' or 'lattice'.")

    def reason_analogy(
        self,
        a: Sequence[float],
        b: Sequence[float],
        c: Sequence[float],
        target: str = "root"
    ) -> List[float]:
        """
        Alias / wrapper for parallelogram completion analogy A : B :: C : D.
        """
        return self.solve_analogy(a, b, c, target=target)

    def reason_metaphor(
        self,
        source: Sequence[float],
        target: Sequence[float],
        void_type: str = "deep"
    ) -> Dict[str, Any]:
        """
        Synthesize conceptual metaphor between source and target in E8 voids.
        In E8 geometry:
        - Deep holes (voids) occur at distance r = 1 from lattice points (e.g. coset (1/2, 1/2, ..., 1/2)).
        - Shallow holes occur at distance r = 1/sqrt(2) ≈ 0.7071.
        The blended concept lies in the void manifold between both domains.
        """
        s = np.array(source, dtype=float)
        t = np.array(target, dtype=float)

        # Midpoint blend in ambient space
        midpoint = 0.5 * (s + t)

        # Project towards nearest void center
        # Deep void center perturbation: coset shift
        deep_void_center = np.floor(midpoint) + 0.5
        # Shallow void: perturbation towards quarter-integer
        shallow_void_center = np.round(midpoint * 2.0) / 2.0

        if void_type == "deep":
            void_attractor = deep_void_center
            expected_radius = 1.0
        elif void_type == "shallow":
            void_attractor = shallow_void_center
            expected_radius = 1.0 / math.sqrt(2.0)
        else:
            raise ValueError(f"Unknown void_type '{void_type}'. Must be 'deep' or 'shallow'.")

        # Blend vector towards void attractor
        blended = 0.5 * (midpoint + void_attractor)
        nearest_root = self.snap_to_nearest_root(blended)
        nearest_lattice = self.cvp_e8(blended)

        dist_to_source = float(np.linalg.norm(blended - s))
        dist_to_target = float(np.linalg.norm(blended - t))
        dist_to_root = float(np.linalg.norm(blended - np.array(nearest_root)))

        return {
            "blended_coordinates": blended.tolist(),
            "void_type": void_type,
            "expected_void_radius": expected_radius,
            "nearest_e8_root": nearest_root,
            "nearest_e8_lattice_point": nearest_lattice,
            "distance_to_source": dist_to_source,
            "distance_to_target": dist_to_target,
            "distance_to_nearest_root": dist_to_root,
        }
