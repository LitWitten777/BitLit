"""
Fano Plane and PSL(2,7) Geometry.

Models the Fano plane PG(2, 2) with:
- 7 points: {0, 1, 2, 3, 4, 5, 6} (corresponding to imaginary octonion basis e_1..e_7)
- 7 lines (each with 3 points)
- Automorphism group PSL(2,7) ≅ GL(3,2) of order 168
"""

import itertools

# Standard cyclic presentation of the 7 Fano lines on points {0, 1, 2, 3, 4, 5, 6}:
# (i, i+1, i+3) mod 7
FANO_LINES: list[frozenset[int]] = [
    frozenset({0, 1, 3}),
    frozenset({1, 2, 4}),
    frozenset({2, 3, 5}),
    frozenset({3, 4, 6}),
    frozenset({4, 5, 0}),
    frozenset({5, 6, 1}),
    frozenset({6, 0, 2}),
]


class FanoPlane:
    """Fano Plane PG(2,2) representation."""

    def __init__(self, lines: list[frozenset[int]] | None = None):
        self.points: list[int] = list(range(7))
        self.lines: list[frozenset[int]] = lines or FANO_LINES
        self.line_set: set[frozenset[int]] = set(self.lines)

    def is_line(self, triple: set[int]) -> bool:
        return frozenset(triple) in self.line_set

    def line_through(self, p1: int, p2: int) -> frozenset[int]:
        """Returns the unique line passing through two distinct points."""
        if p1 == p2:
            raise ValueError(f"Points must be distinct, got ({p1}, {p2})")
        for line in self.lines:
            if p1 in line and p2 in line:
                return line
        raise RuntimeError(f"No line found containing {p1} and {p2}")

    def third_point(self, p1: int, p2: int) -> int:
        """Returns the third point on the line containing p1 and p2."""
        line = self.line_through(p1, p2)
        remaining = line - {p1, p2}
        return next(iter(remaining))

    def get_flags(self) -> list[tuple[int, frozenset[int]]]:
        """Returns the 21 incident point-line pairs (flags)."""
        flags = []
        for line in self.lines:
            for p in line:
                flags.append((p, line))
        return flags


class PSL2_7:
    """
    Automorphism group of the Fano plane PG(2,2),
    isomorphic to PSL(2,7) and GL(3,2), of order 168.
    """

    def __init__(self, fano: FanoPlane | None = None):
        self.fano = fano or FanoPlane()
        self.elements: list[tuple[int, ...]] = self._generate_automorphisms()

    def _generate_automorphisms(self) -> list[tuple[int, ...]]:
        """Finds all permutations of {0..6} that preserve the set of Fano lines."""
        autos = []
        for p in itertools.permutations(range(7)):
            is_auto = True
            for line in self.fano.lines:
                mapped_line = frozenset(p[pt] for pt in line)
                if mapped_line not in self.fano.line_set:
                    is_auto = False
                    break
            if is_auto:
                autos.append(p)
        return autos

    def __len__(self) -> int:
        return len(self.elements)

    def compose(self, p1: tuple[int, ...], p2: tuple[int, ...]) -> tuple[int, ...]:
        """Composes permutations (p1 ∘ p2)(x) = p1(p2(x))."""
        return tuple(p1[p2[i]] for i in range(7))

    def identity(self) -> tuple[int, ...]:
        return tuple(range(7))

    def inverse(self, p: tuple[int, ...]) -> tuple[int, ...]:
        inv = [0] * 7
        for i, val in enumerate(p):
            inv[val] = i
        return tuple(inv)
