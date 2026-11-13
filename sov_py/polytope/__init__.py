"""
Polytope Logic Synthesis Package — E8 root lattice & Gosset 4_21 geometry.
"""

from .gosset_logic import (
    CechChain,
    GossetLogicSynthesizer,
    Proposition,
    Relation,
    classify_relation,
    distance,
    inner_product,
)

__all__ = [
    "GossetLogicSynthesizer",
    "Proposition",
    "Relation",
    "CechChain",
    "classify_relation",
    "inner_product",
    "distance",
]
