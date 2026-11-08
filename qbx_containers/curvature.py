"""Curvature classes and their composition rules.

Curvature is the large-scale (volume-growth) class of a carrier, exactly as in
``QBX/Formal/Foundations/Container.lean``:

* ``positive`` -- bounded volume (closed: compresses everything into structure);
* ``flat``     -- unbounded, at most polynomial volume (translational);
* ``negative`` -- at least exponential volume (growing, hierarchical).

``mixed`` is allowed only for composites, as a record of components; it is resolved to one of the
three by the composition rules below.
"""

from __future__ import annotations

import math
from typing import Dict, Iterable, Optional, Sequence

CURVATURES = ("positive", "flat", "negative")
_RANK = {"positive": 0, "flat": 1, "negative": 2}

# Per-curvature protocol defaults (design document, "What changes about traditional software
# architecture"): how states are addressed and how time is kept.
ADDRESS_KIND = {"positive": "codeword", "flat": "coordinates", "negative": "path"}
TIME_KIND = {"positive": "layered", "flat": "uniform_steps", "negative": "causal"}

# Operations a container of the given curvature may NOT declare in its algebra, with the reason.
FORBIDDEN_OPS: Dict[str, Dict[str, str]] = {
    "positive": {
        "translation": "a bounded carrier has no free translations (they would leave the carrier)",
        "exponential_capacity": "bounded volume cannot hold unboundedly many states",
        "unbounded_growth": "bounded volume",
    },
    "flat": {
        "exponential_capacity": "polynomial volume: a ball of radius r holds O(r^d) states",
        "unbounded_branching": "polynomial volume",
    },
    "negative": {
        "o1_random_access": "exponential volume at bounded degree: access is by geodesic path",
        "uniform_indexing": "addresses are paths, not uniform indices",
        "translation_invariance": "hyperbolic carriers have no global translation-invariant structure",
    },
}


def check_curvature(c: str) -> str:
    if c not in CURVATURES:
        raise ValueError(f"unknown curvature {c!r}; expected one of {CURVATURES}")
    return c


def compose_product(a: str, b: str) -> str:
    """Product A x B with the sum metric (Lean: ``CurvatureClass.prod``, ``Container.prod_correct``).

    negative absorbs everything, flat absorbs positive, positive x positive = positive.
    """
    check_curvature(a)
    check_curvature(b)
    return a if _RANK[a] >= _RANK[b] else b


def compose_bundle(base: str, fiber: str) -> str:
    """Bundle F -> E -> B.  For the volume-growth class, a bundle with compact structure group and
    bounded connection distortion has the growth of the product, so the total class is the product
    class.  (This is a declared convention for twisted bundles; it is a theorem only for the
    product case, ``Container.prod_correct``.)"""
    return compose_product(base, fiber)


def compose_sum(cs: Iterable[str]) -> str:
    """Disjoint union: volume about the worst component dominates.  (Requires equal algebras,
    which the registry checks.)"""
    cs = [check_curvature(c) for c in cs]
    if not cs:
        raise ValueError("empty sum")
    return max(cs, key=_RANK.__getitem__)


def classify_profile(volumes: Sequence[int], *, tail: int = 4) -> str:
    """Heuristic classification of a *finite prefix* V(0..R) of a volume profile.

    Exact classification needs the whole profile (that is what the Lean statement checks); this
    reads the tail: constant tail -> positive; ratio V(r+1)/V(r) staying >= 1.5 -> negative;
    otherwise flat.  Used only as a runtime sanity check on enumerable carriers.
    """
    v = list(volumes)
    if len(v) < tail + 1:
        raise ValueError("need at least tail+1 radii")
    end = v[-(tail + 1):]
    if all(x == end[0] for x in end):
        return "positive"
    ratios = [end[i + 1] / end[i] for i in range(tail) if end[i] > 0]
    if ratios and min(ratios) >= 1.5:
        return "negative"
    return "flat"


def can_embed(source_volumes: Sequence[int], target_volumes: Sequence[int],
              stretch: int = 1) -> Optional[int]:
    """Volume obstruction to a ``stretch``-Lipschitz injective embedding of the source ball
    family into the target: it needs ``V_target(stretch * r) >= V_source(r)`` for every r.
    Returns the first radius r at which the target is too small, or None if no obstruction is
    visible in the given prefixes.  (E.g. a 2^20-leaf tree into a flat container of diameter 40.)
    """
    for r, vs in enumerate(source_volumes):
        idx = min(stretch * r, len(target_volumes) - 1)
        if target_volumes[idx] < vs:
            return r
    return None


def hamming_ball(n: int, r: int) -> int:
    return sum(math.comb(n, i) for i in range(min(r, n) + 1))
