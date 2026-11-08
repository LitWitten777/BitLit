"""Volume profiles of carriers that can be enumerated exactly.

Carrier notation (descriptor field ``carrier``):

* ``hypercube(n)``   -- {0,1}^n, Hamming distance            (Lean: ``hypercube``)
* ``lattice(k)``     -- Z^k, l1 distance                      (Lean: ``lattice``)
* ``torus(m,n)``     -- Z/m x Z/n, l1 distance mod periods; developed as lattice(2)
* ``cycle(m)``       -- Z/m; developed as lattice(1)
* ``tree(b)``        -- infinite rooted b-ary tree, tree distance (Lean: ``tree`` for b = 2)
* ``finite(N)``      -- a finite set of N states (only boundedness is known)
* ``free(X)``        -- free monoid / word space over an alphabet of size X (= tree(X))
* ``product(A;B)``   -- product with the sum metric
"""

from __future__ import annotations

import math
import re
from functools import lru_cache
from typing import Callable, List, Optional, Tuple

_CARRIER = re.compile(r"^\s*([a-z_]+)\s*\((.*)\)\s*$")


def parse_carrier(spec: str) -> Tuple[str, List[str]]:
    m = _CARRIER.match(spec)
    if not m:
        raise ValueError(f"bad carrier spec {spec!r}")
    name, args = m.group(1), m.group(2)
    if name == "product":
        return name, _split_top(args, ";")
    return name, [a.strip() for a in args.split(",") if a.strip()]


def _split_top(s: str, sep: str) -> List[str]:
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    out.append(cur.strip())
    return out


def _lattice_sphere(k: int, r: int) -> int:
    """Number of points of Z^k at l1 distance exactly r."""
    if r == 0:
        return 1
    return sum(2 ** i * math.comb(k, i) * math.comb(r - 1, i - 1) for i in range(1, min(k, r) + 1))


def _cycle_sphere(m: int, r: int) -> int:
    if r == 0:
        return 1
    if 2 * r < m:
        return 2
    if 2 * r == m:
        return 1
    return 0


def _convolve(f: Callable[[int], int], g: Callable[[int], int]) -> Callable[[int], int]:
    @lru_cache(maxsize=None)
    def h(r: int) -> int:
        return sum(f(i) * g(r - i) for i in range(r + 1))
    return h


def _sphere_fn(spec: str) -> Callable[[int], int]:
    name, args = parse_carrier(spec)
    if name == "hypercube":
        n = int(args[0])
        return lambda r: math.comb(n, r) if r <= n else 0
    if name == "lattice":
        k = int(args[0])
        return lambda r: _lattice_sphere(k, r)
    if name == "cycle":
        m = int(args[0])
        return lambda r: _cycle_sphere(m, r)
    if name == "torus":
        a, b = int(args[0]), int(args[1])
        return _convolve(lambda r: _cycle_sphere(a, r), lambda r: _cycle_sphere(b, r))
    if name in ("tree", "free"):
        b = int(args[0]) if args else 2
        return lambda r: b ** r
    if name == "product":
        fs = [_sphere_fn(p) for p in args]
        out = fs[0]
        for f in fs[1:]:
            out = _convolve(out, f)
        return out
    raise ValueError(f"cannot enumerate carrier {spec!r}")


def volume_profile(spec: str, radius: int) -> Optional[List[int]]:
    """Ball sizes V(0..radius) about the base point, or None if the carrier is not enumerable."""
    name, args = parse_carrier(spec)
    if name == "finite":
        N = int(args[0])
        return None if N <= 0 else [N] * (radius + 1)  # an upper bound, constant
    try:
        s = _sphere_fn(spec)
    except ValueError:
        return None
    out, acc = [], 0
    for r in range(radius + 1):
        acc += s(r)
        out.append(acc)
    return out


def development(spec: str) -> str:
    """The carrier whose growth defines the curvature (the universal cover for quotients)."""
    name, args = parse_carrier(spec)
    if name == "torus":
        return "lattice(2)"
    if name == "cycle":
        return "lattice(1)"
    if name == "product":
        return "product(" + ";".join(development(a) for a in args) + ")"
    return spec
