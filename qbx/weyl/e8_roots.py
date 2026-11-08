"""
E8 root system.

The E8 root system consists of 240 roots in R^8:

- 112 "integer" roots:  ±e_i ± e_j   (i < j)
- 128 "half-integer" roots:  (±1/2, ..., ±1/2)  with an even number of minus signs

All roots have norm squared 2.
"""

from __future__ import annotations

from itertools import combinations
from typing import FrozenSet, List, Tuple


def _build_integer_roots() -> List[Tuple[float, ...]]:
    roots = []
    for i, j in combinations(range(8), 2):
        for si in (1.0, -1.0):
            for sj in (1.0, -1.0):
                v = [0.0] * 8
                v[i] = si
                v[j] = sj
                roots.append(tuple(v))
    return roots


def _build_half_integer_roots() -> List[Tuple[float, ...]]:
    roots = []
    # 8 positions, each ±1/2, even number of minus signs.
    for mask in range(256):
        bits = [(mask >> k) & 1 for k in range(8)]
        # even number of 1s == even number of minus signs
        if sum(bits) % 2 != 0:
            continue
        v = tuple(0.5 if b == 0 else -0.5 for b in bits)
        roots.append(v)
    return roots


E8_ROOTS: List[Tuple[float, ...]] = _build_integer_roots() + _build_half_integer_roots()
E8_ROOTS_SET: FrozenSet[Tuple[float, ...]] = frozenset(E8_ROOTS)

assert len(E8_ROOTS) == 240, f"Expected 240 E8 roots, got {len(E8_ROOTS)}"
assert len(E8_ROOTS_SET) == 240, "Duplicate roots detected!"


def is_e8_root(v: Tuple[float, ...]) -> bool:
    """Check whether v (8-tuple) is an E8 root (norm² = 2 and in the lattice)."""
    if len(v) != 8:
        return False
    return tuple(v) in E8_ROOTS_SET


def inner_product(a: Tuple[float, ...], b: Tuple[float, ...]) -> float:
    return float(sum(x * y for x, y in zip(a, b)))


def norm_squared(v: Tuple[float, ...]) -> float:
    return float(sum(x * x for x in v))


# Simple smoke test
if __name__ == "__main__":
    norms = {round(norm_squared(r), 6) for r in E8_ROOTS}
    print(f"E8 roots: {len(E8_ROOTS)}")
    print(f"Unique norm² values: {norms}")
    assert norms == {2.0}
    print("OK")
