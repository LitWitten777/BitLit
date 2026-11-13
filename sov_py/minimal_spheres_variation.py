r"""
Second Variation of 2-Spheres in the 2n-Sphere: Morse Index and Nullity Bounds.

Grounding: Gavin Ball and Jesse Madnick (Sep 15, 2026),
"The second variation of 2-spheres in the 2n-sphere",
arXiv:2609.17887v1 [math.DG].

Key Mathematical Theorems and Invariants:
1. Calabi-Chern-Barbosa Quantized Area:
   Area(f) = 2 \pi (n(n+1) + a_n), where a_n = \sum_{j=1}^n b_j \ge 0.
   Minimum area: Area_min(S^2 \to S^{2n}) = 2\pi n(n + 1).

2. Morse Index Bounds for S^2 \to S^{2n} (Theorem 1.1):
   (n - 2) * Area(f)/\pi + n(n + 3) \le Ind(f) \le (n - 1) * Area(f)/\pi - n(n - 1).
   Sharp Lower Bound:
   Ind(f) \ge n(n - 1)(2n + 1), with equality iff twistor-equivalent to Boruvka sphere.

3. Nullity Bounds for S^2 \to S^{2n} (Theorem 1.2):
   Area(f)/\pi + 2(n^2 - 3) - 2 b_1 \le Null(f) \le Area(f)/\pi + 2(n^2 - 3) - 2 b_1 + 4 R(f),
   where R(f) = \sum_{j=1}^{n-1} (n - j) b_j.
   Sharp Lower Bound:
   Null(f) \ge (2n + 3)(2n - 2), with equality iff twistor-equivalent to Boruvka sphere.

4. Unbranched Equality Case:
   When R(f) = 0 (b_1 = ... = b_{n-1} = 0):
   Ind(f) = (n - 1) * Area(f)/\pi - n,
   Null(f) = Area(f)/\pi + 2(n^2 - 3).

5. Elliptic Curve Bounds (g = 1, Theorem 1.3 / 1.4 specialization, Lemma 6.6):
   Ind(f) \le (n - 1) * Area(f)/\pi,
   Ind(f) \ge 2(n - 1)(n + 1) + 2 * binom(n, 2) for n \ge 3.
"""

from dataclasses import dataclass
from typing import List, Tuple, Optional
import math


@dataclass(frozen=True)
class MinimalSphere2n:
    """Represents a linearly full branched minimal 2-sphere in S^{2n}."""
    n: int                         # half ambient dimension S^{2n}
    ramifications: List[int]       # [b_1, b_2, ..., b_n] ramification degrees

    def __post_init__(self):
        assert self.n >= 2, "n must be >= 2"
        assert len(self.ramifications) == self.n, f"Must provide {self.n} ramification indices"
        assert all(b >= 0 for b in self.ramifications), "Ramifications must be non-negative"

    @property
    def b1(self) -> int:
        return self.ramifications[0]

    @property
    def an(self) -> int:
        r"""Total ramification a_n = sum_{j=1}^n b_j."""
        return sum(self.ramifications)

    @property
    def intermediate_ramification(self) -> int:
        r"""R(f) = sum_{j=1}^{n-1} (n - j) b_j."""
        return sum((self.n - j) * self.ramifications[j - 1] for j in range(1, self.n))

    @property
    def area_over_pi(self) -> int:
        r"""Area(f) / \pi = 2 * (n*(n + 1) + a_n)."""
        return 2 * (self.n * (self.n + 1) + self.an)

    def index_bounds(self) -> Tuple[int, int]:
        r"""Theorem 1.1: (n - 2)*Area/pi + n(n+3) <= Ind(f) <= (n - 1)*Area/pi - n(n-1)."""
        A = self.area_over_pi
        lower = (self.n - 2) * A + self.n * (self.n + 3)
        upper = (self.n - 1) * A - self.n * (self.n - 1)
        return lower, upper

    def nullity_bounds(self) -> Tuple[int, int]:
        r"""Theorem 1.2: Area/pi + 2(n^2 - 3) - 2b_1 <= Null(f) <= Area/pi + 2(n^2-3) - 2b_1 + 4R(f)."""
        A = self.area_over_pi
        base = A + 2 * (self.n**2 - 3) - 2 * self.b1
        lower = base
        upper = base + 4 * self.intermediate_ramification
        return lower, upper

    def is_boruvka_equivalent(self) -> bool:
        """Boruvka sphere has all b_j = 0."""
        return all(b == 0 for b in self.ramifications)


def boruvka_index(n: int) -> int:
    """Sharp minimal index: n(n - 1)(2n + 1)."""
    return n * (n - 1) * (2 * n + 1)


def boruvka_nullity(n: int) -> int:
    """Sharp minimal nullity: (2n + 3)(2n - 2)."""
    return (2 * n + 3) * (2 * n - 2)


def boruvka_area_over_pi(n: int) -> int:
    r"""Area_min / \pi = 2n(n + 1)."""
    return 2 * n * (n + 1)


def verify_boruvka_equality(n: int) -> bool:
    """Verify that for Boruvka sphere (all b_j=0), lower index bound equals n(n-1)(2n+1)
    and lower nullity bound equals (2n+3)(2n-2)."""
    sph = MinimalSphere2n(n=n, ramifications=[0] * n)
    lower_idx, upper_idx = sph.index_bounds()
    lower_null, upper_null = sph.nullity_bounds()

    target_idx = boruvka_index(n)
    target_null = boruvka_nullity(n)

    idx_matches = (lower_idx == target_idx)
    null_matches = (lower_null == target_null)

    return idx_matches and null_matches
