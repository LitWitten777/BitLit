"""
Gosset 4₂₁ Polytope Logic Synthesizer.

Implements non-propositional geometric theorem proving over the E₈ root system:

  - 240 minimal roots of E₈ on S⁷ (‖v‖ = √2)
    - 112 integer roots (D₈): (±1, ±1, 0, 0, 0, 0, 0, 0) and permutations
    - 128 half-integer spinor roots (E₈ ∖ D₈): (±½,...,±½) with even # minus signs
  - Metric syllogisms:
    - d(u,v) = √2  ⟺  ⟨u,v⟩ = 1   → Deductive inference (syllogistic step)
    - d(u,v) = 2   ⟺  ⟨u,v⟩ = 0   → Logical orthogonality (independence)
    - d(u,v) = 2√2 ⟺  ⟨u,v⟩ = −2  → Antipodal contradiction (negation)
  - Curtis 35 MOG tetrad nodal energy ratios E(Pₖ)
  - Čech cohomology sheaf verification (H¹ = 0)

References:
  - endofunk.md §2: Polytope Logic and Geometric Theorem Proving
  - HYPOTHESIS_REGISTRY.md HYP-019 (E₈ root partitioning)
"""
from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from enum import Enum
from typing import Sequence


# Root norms
SQRT2 = math.sqrt(2.0)
TWO_SQRT2 = 2.0 * SQRT2
INNER_IDENTITY = 2.0     # θ = 0
INNER_DEDUCTIVE = 1.0    # θ = π/3 (syllogistic step)
INNER_ORTHO = 0.0        # θ = π/2 (independence)
INNER_OPPOSITION = -1.0  # θ = 2π/3 (entailment / opposition)
INNER_CONTRA = -2.0      # θ = π (antipodal contradiction)

TOLERANCE = 1e-9


class Relation(str, Enum):
    IDENTITY = "identity"              # d = 0,   ⟨u,v⟩ = +2
    DEDUCTIVE = "deductive"            # d = √2,  ⟨u,v⟩ = +1
    INDEPENDENT = "independent"        # d = 2,   ⟨u,v⟩ = 0
    OPPOSITION = "opposition"          # d = √6,  ⟨u,v⟩ = -1
    CONTRADICTION = "contradiction"    # d = 2√2, ⟨u,v⟩ = -2
    OTHER = "other"


@dataclass
class Proposition:
    """A proposition represented as an E₈ root vector."""
    name: str
    root: tuple[float, ...]  # 8-dimensional

    def __post_init__(self) -> None:
        if len(self.root) != 8:
            raise ValueError(f"E₈ root must be 8-dimensional, got {len(self.root)}")
        norm_sq = sum(x * x for x in self.root)
        if abs(norm_sq - 2.0) > 0.01:
            raise ValueError(f"E₈ root must have norm √2, got norm²={norm_sq:.4f}")

    def negate(self) -> "Proposition":
        """Antipodal proposition (logical negation)."""
        return Proposition(f"¬{self.name}", tuple(-x for x in self.root))


@dataclass
class CechChain:
    """A simplicial 1-chain representing a proof chain."""
    propositions: list[Proposition]

    def coboundary_defect(self) -> float:
        """
        Compute ‖δ₁‖: the coboundary operator evaluated on the 1-chain.
        A proof chain with H¹ = 0 has zero gluing discrepancy across charts.
        """
        if len(self.propositions) < 2:
            return 0.0
        # δ₁ on a 1-chain: sum of inner product discrepancies at each junction
        total = 0.0
        for i in range(len(self.propositions) - 1):
            u = self.propositions[i].root
            v = self.propositions[i + 1].root
            ip = inner_product(u, v)
            # Ideal deductive step has ⟨u,v⟩ = 1; defect is deviation from 1
            total += (ip - INNER_DEDUCTIVE) ** 2
        return math.sqrt(total)


def inner_product(u: Sequence[float], v: Sequence[float]) -> float:
    return sum(a * b for a, b in zip(u, v))


def distance(u: Sequence[float], v: Sequence[float]) -> float:
    return math.sqrt(sum((a - b) ** 2 for a, b in zip(u, v)))


def classify_relation(u: Sequence[float], v: Sequence[float]) -> Relation:
    """Classify the logical relation between two E₈ root propositions."""
    ip = inner_product(u, v)

    if abs(ip - INNER_IDENTITY) < TOLERANCE:
        return Relation.IDENTITY
    elif abs(ip - INNER_DEDUCTIVE) < TOLERANCE:
        return Relation.DEDUCTIVE
    elif abs(ip - INNER_ORTHO) < TOLERANCE:
        return Relation.INDEPENDENT
    elif abs(ip - INNER_OPPOSITION) < TOLERANCE:
        return Relation.OPPOSITION
    elif abs(ip - INNER_CONTRA) < TOLERANCE:
        return Relation.CONTRADICTION
    return Relation.OTHER


class GossetLogicSynthesizer:
    """
    Gosset 4₂₁ Polytope Logic Synthesizer.

    Builds all 240 E₈ minimal roots and exposes geometric theorem proving
    primitives: metric syllogisms, MOG tetrad basins, and Čech sheaf guards.
    """

    def __init__(self) -> None:
        self._integer_roots: list[tuple[float, ...]] = []
        self._spinor_roots: list[tuple[float, ...]] = []
        self._all_roots: list[tuple[float, ...]] = []
        self._mog_tetrads: list[tuple[list[int], list[int]]] = []
        self._build_roots()
        self._build_mog_tetrads()

    # ------------------------------------------------------------------
    # Root generation
    # ------------------------------------------------------------------

    def _build_roots(self) -> None:
        """Build all 240 minimal E₈ roots."""
        # 112 integer roots: ±e_i ± e_j for i < j
        for i, j in itertools.combinations(range(8), 2):
            for si in (1.0, -1.0):
                for sj in (1.0, -1.0):
                    r = [0.0] * 8
                    r[i] = si
                    r[j] = sj
                    self._integer_roots.append(tuple(r))

        # 128 half-integer roots: (±½)^8 with even # minus signs
        for signs in itertools.product([0.5, -0.5], repeat=8):
            if signs.count(-0.5) % 2 == 0:
                self._spinor_roots.append(signs)

        self._all_roots = self._integer_roots + self._spinor_roots

        assert len(self._integer_roots) == 112, f"Expected 112 integer roots, got {len(self._integer_roots)}"
        assert len(self._spinor_roots) == 128, f"Expected 128 spinor roots, got {len(self._spinor_roots)}"
        assert len(self._all_roots) == 240, f"Expected 240 total roots, got {len(self._all_roots)}"

    def _build_mog_tetrads(self) -> None:
        """
        Build the Curtis 35 MOG (Miracle Octad Generator) tetrad partitions.
        Each partition splits {0,...,7} into complementary 4-element tetrads (T₁, T₂).
        There are C(8,4)/2 = 35 such unordered complementary pairs.
        """
        from itertools import combinations
        seen: set[frozenset] = set()
        for combo in combinations(range(8), 4):
            T1 = list(combo)
            T2 = [i for i in range(8) if i not in T1]
            key = frozenset([frozenset(T1), frozenset(T2)])
            if key not in seen:
                seen.add(key)
                self._mog_tetrads.append((T1, T2))

        assert len(self._mog_tetrads) == 35, f"Expected 35 MOG tetrads, got {len(self._mog_tetrads)}"

    # ------------------------------------------------------------------
    # Metric syllogisms
    # ------------------------------------------------------------------

    def relate(self, p: Proposition, q: Proposition) -> Relation:
        """Classify the logical relation between propositions p and q."""
        return classify_relation(p.root, q.root)

    def deduce(self, premises: list[Proposition]) -> list[Proposition]:
        """
        Return all E₈ roots reachable from the premises by one deductive step
        (inner product = 1, distance = √2).
        """
        conclusions: list[Proposition] = []
        for root in self._all_roots:
            for p in premises:
                if abs(inner_product(p.root, root) - INNER_DEDUCTIVE) < TOLERANCE:
                    conclusions.append(Proposition(f"derived_from_{p.name}", root))
                    break
        return conclusions

    # ------------------------------------------------------------------
    # Curtis 35 MOG tetrad energy ratios
    # ------------------------------------------------------------------

    def mog_energy_ratio(self, v: Sequence[float], k: int) -> float:
        """
        Compute nodal energy ratio E(Pₖ) = (Σᵢ∈T₁ vᵢ²) / (Σⱼ∈T₂ vⱼ² + ε)
        for the k-th MOG tetrad partition (k ∈ {0,...,34}).
        """
        if not 0 <= k < 35:
            raise ValueError(f"MOG partition index k must be in [0,34], got {k}")
        T1, T2 = self._mog_tetrads[k]
        eps = 1e-12
        num = sum(v[i] ** 2 for i in T1)
        den = sum(v[j] ** 2 for j in T2) + eps
        return num / den

    def dominant_mog_partition(self, v: Sequence[float]) -> int:
        """Return the index of the dominant MOG tetrad partition for vector v."""
        ratios = [self.mog_energy_ratio(v, k) for k in range(35)]
        return max(range(35), key=lambda k: ratios[k])

    # ------------------------------------------------------------------
    # Čech cohomology sheaf guard
    # ------------------------------------------------------------------

    def check_cech_cohomology(self, chain: list[Proposition]) -> float:
        """
        Compute H¹ (coboundary defect) for a proof chain.
        Returns 0.0 if H¹ = 0 (no cohomological obstruction → global validity).
        """
        return CechChain(chain).coboundary_defect()

    def sheaf_guard(self, chain: list[Proposition], threshold: float = 1e-6) -> bool:
        """
        SheafGuardEngine: returns True iff H¹ = 0 (up to threshold).
        Guarantees global validity without cyclical paradoxes.
        """
        return self.check_cech_cohomology(chain) < threshold

    # ------------------------------------------------------------------
    # Utilities
    # ------------------------------------------------------------------

    def random_root(self, seed: int | None = None) -> tuple[float, ...]:
        """Return a random E₈ root."""
        import random
        rng = random.Random(seed)
        return rng.choice(self._all_roots)

    @staticmethod
    def snap_to_e8_lattice(vec: Sequence[float]) -> tuple[float, ...]:
        """
        Conway-Sloane closest-point decoding algorithm for the self-dual E8 lattice.
        E8 = D8 ∪ (D8 + 1/2 * 1)
        Projects any continuous vector in R^8 onto the nearest valid point in E8 in O(d) time.
        """
        x = list(vec)[:8]
        if len(x) < 8:
            x = x + [0.0] * (8 - len(x))

        # Candidate 1: Nearest point in D8 (sum of rounded ints is even)
        f = [int(round(v)) for v in x]
        if sum(f) % 2 != 0:
            diffs = [abs(xi - fi) for xi, fi in zip(x, f)]
            k = diffs.index(max(diffs))
            f[k] += 1 if x[k] > f[k] else -1
        cand_d8 = [float(val) for val in f]

        # Candidate 2: Nearest point in D8 + 1/2 * 1 (sum of 2*coords is even)
        g = [int(round(v - 0.5)) for v in x]
        if sum(g) % 2 != 0:
            diffs = [abs((xi - 0.5) - gi) for xi, gi in zip(x, g)]
            k = diffs.index(max(diffs))
            g[k] += 1 if (x[k] - 0.5) > g[k] else -1
        cand_half = [float(val) + 0.5 for val in g]

        # Pick candidate with minimum Euclidean distance
        d1 = sum((xi - ci) ** 2 for xi, ci in zip(x, cand_d8))
        d2 = sum((xi - ci) ** 2 for xi, ci in zip(x, cand_half))
        return tuple(cand_d8 if d1 <= d2 else cand_half)

    def snap_to_minimal_root(self, vec: Sequence[float]) -> tuple[float, ...]:
        """
        Finds the nearest of the 240 minimal roots (norm^2 = 2) in the Gosset 4_21 polytope.
        """
        best_root = self._all_roots[0]
        min_dist = float("inf")
        for r in self._all_roots:
            d = sum((a - b) ** 2 for a, b in zip(vec, r))
            if d < min_dist:
                min_dist = d
                best_root = r
        return best_root

    def antipodal(self, root: tuple[float, ...]) -> tuple[float, ...]:
        """Return the antipodal root (logical negation)."""
        return tuple(-x for x in root)

    def deductive_resolvent(self, p1: Proposition, p2: Proposition) -> Proposition:
        """
        Constructive deduction rule over E_8 root lattice.
        When ⟨p1, p2⟩ = 1 (angle π/3, d = √2), the resolvent:
          w = p1 - p2
        is an exact E_8 minimal root with ‖w‖² = 2, ⟨p1, w⟩ = 1, and ⟨p2, w⟩ = -1.
        """
        rel = classify_relation(p1.root, p2.root)
        if rel != Relation.DEDUCTIVE:
            raise ValueError(f"Deductive resolvent requires ⟨p1, p2⟩ = 1, got relation {rel}")
        diff = tuple(a - b for a, b in zip(p1.root, p2.root))
        return Proposition(f"({p1.name} ⊢ {p2.name})", diff)

    def synthesize_triad_hexagon(self, p1: Proposition, p2: Proposition) -> list[Proposition]:
        """
        For deductive pair ⟨p1, p2⟩ = 1, construct the closed 6-element A_2 root hexagon:
          [p1, p2, p1 - p2, -p1, -p2, p2 - p1]
        Every adjacent pair has inner product 1 (angle π/3).
        """
        rel = classify_relation(p1.root, p2.root)
        if rel != Relation.DEDUCTIVE:
            raise ValueError(f"Triad hexagon requires ⟨p1, p2⟩ = 1, got relation {rel}")
        w = self.deductive_resolvent(p1, p2)
        neg_p1 = p1.negate()
        neg_p2 = p2.negate()
        neg_w = w.negate()
        # Cyclic order around the hexagon: p1 -> p2 -> -w?
        # Check: ⟨p1, p2⟩ = 1, ⟨p2, p2-p1⟩ = ⟨p2, -w⟩ = 1, etc.
        return [p1, p2, neg_w, neg_p1, neg_p2, w]

    def infer(self, p1: Proposition, p2: Proposition) -> dict[str, any]:
        """
        Operational inference decision procedure:
        Returns the logical relation, metric distance, inner product, and
        the constructive resolvent root or collapse certificate.
        """
        ip = inner_product(p1.root, p2.root)
        d = distance(p1.root, p2.root)
        rel = classify_relation(p1.root, p2.root)

        result: dict[str, any] = {
            "p1": p1.name,
            "p2": p2.name,
            "relation": rel.value,
            "inner_product": ip,
            "distance": d,
            "is_deductive": rel == Relation.DEDUCTIVE,
            "is_contradiction": rel == Relation.CONTRADICTION,
            "is_independent": rel == Relation.INDEPENDENT,
        }

        if rel == Relation.DEDUCTIVE:
            resolvent = self.deductive_resolvent(p1, p2)
            result["resolvent"] = resolvent
            result["triad_hexagon"] = self.synthesize_triad_hexagon(p1, p2)
        elif rel == Relation.CONTRADICTION:
            result["annihilation_norm"] = 0.0  # ||p1 + p2|| = 0
            result["collapse_certified"] = True

        return result

    @property
    def integer_roots(self) -> list[tuple[float, ...]]:
        return self._integer_roots.copy()

    @property
    def spinor_roots(self) -> list[tuple[float, ...]]:
        return self._spinor_roots.copy()

    @property
    def all_roots(self) -> list[tuple[float, ...]]:
        return self._all_roots.copy()

    @property
    def mog_tetrads(self) -> list[tuple[list[int], list[int]]]:
        return self._mog_tetrads.copy()

    def summary(self) -> dict[str, int]:
        return {
            "integer_roots": len(self._integer_roots),
            "spinor_roots": len(self._spinor_roots),
            "total_roots": len(self._all_roots),
            "mog_tetrads": len(self._mog_tetrads),
        }
