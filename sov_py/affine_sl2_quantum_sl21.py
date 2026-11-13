r"""affine_sl2_quantum_sl21.py — Affine sl2 at Admissible Levels and Quantum sl2|1
==================================================================================
Grounding: Thomas Creutzig and Simon Lentner (Sep 11, 2026),
"Affine sl2 at admissible levels and quantum sl2|1", arXiv:2609.12895v1.

Key Invariants:
1. Admissible levels for affine sl2:
   k = -2 + u / v, with u >= 2, v >= 1, gcd(u, v) = 1.
2. Sugawara central charge:
   c(k) = 3k / (k + 2) = 3 - 6v / u.
3. Dual Coxeter number of sl2:
   h^\vee = 2, so k + h^\vee = u / v.
4. Quantum root of unity order:
   Order of q^2 in U_q(sl(2|1)) is u * v.
"""

from __future__ import annotations
import math
from typing import Dict, List, Tuple
from fractions import Fraction


def admissible_level(u: int, v: int) -> Fraction:
    """Compute admissible level k = -2 + u/v."""
    if u < 2 or v < 1:
        raise ValueError("Admissible levels require u >= 2 and v >= 1.")
    if math.gcd(u, v) != 1:
        raise ValueError("u and v must be coprime.")
    return Fraction(-2) + Fraction(u, v)


def central_charge(u: int, v: int) -> Fraction:
    """Compute Sugawara central charge c(k) = 3 - 6v / u."""
    return Fraction(3) - Fraction(6 * v, u)


def root_of_unity_order(u: int, v: int) -> int:
    """Order of q^2 where q = exp(i * pi / (u * v))."""
    return u * v


def dual_coxeter_shifted_level(u: int, v: int) -> Fraction:
    """Shifted level k + h^\vee = k + 2 = u / v."""
    k = admissible_level(u, v)
    return k + 2


def hyp246_master_verification() -> Tuple[bool, Dict[str, any]]:
    """Master verification of HYP-246 algebraic invariants."""
    # 1. Level k=1: u=3, v=1 -> c = 3 - 6/3 = 1
    k1 = admissible_level(3, 1)
    assert k1 == 1
    assert central_charge(3, 1) == 1
    assert root_of_unity_order(3, 1) == 3

    # 2. Fractional admissible level: u=2, v=3 -> k = -4/3, c = 3 - 18/2 = -6
    k_43 = admissible_level(2, 3)
    assert k_43 == Fraction(-4, 3)
    assert central_charge(2, 3) == -6
    assert root_of_unity_order(2, 3) == 6

    # 3. Fractional admissible level: u=3, v=2 -> k = -1/2, c = 3 - 12/3 = -1
    k_12 = admissible_level(3, 2)
    assert k_12 == Fraction(-1, 2)
    assert central_charge(3, 2) == -1
    assert root_of_unity_order(3, 2) == 6

    # 4. Shifted level identity: k + 2 == u / v
    assert dual_coxeter_shifted_level(2, 3) == Fraction(2, 3)
    assert dual_coxeter_shifted_level(3, 2) == Fraction(3, 2)

    results = {
        "k_1_central_charge": int(central_charge(3, 1)),
        "k_minus_4_3_central_charge": int(central_charge(2, 3)),
        "k_minus_1_2_central_charge": int(central_charge(3, 2)),
        "shifted_level_verified": True,
    }
    return True, results
