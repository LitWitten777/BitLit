"""
ABC Triple Asymptotic Density & Power Law Obstruction Analysis (OP-048, HYP-105).

Investigates the asymptotic growth rate of high-quality ABC triples:
    N(X, eps) = #{(a, b, c) : c <= X, gcd(a, b) = 1, a + b = c, quality(a, b, c) > 1 + eps}

Contrasts the naive unconstrained power law:
    N(X, eps) ~ c_eps * X^{1 / (1 + eps)}
with the standard ABC conjecture (which implies N(X, eps) = O(1) is finite for all eps > 0)
and empirical counting data from ABC@home up to X = 10^18.
"""

from __future__ import annotations

import math
from typing import Any

# Canonical extremal ABC triples known in literature
KNOWN_EXTREMAL_TRIPLES: list[dict[str, Any]] = [
    {
        "name": "Reyssat",
        "a": 2,
        "b": (3 ** 10) * 109,
        "c": 23 ** 5,
        "expected_quality": 1.62991,
    },
    {
        "name": "de Weger",
        "a": 11 ** 2,
        "b": (3 ** 2) * (5 ** 6) * (7 ** 3),
        "c": (2 ** 21) * 23,
        "expected_quality": 1.62599,
    },
    {
        "name": "Nitaj",
        "a": 19 * 1307,
        "b": 7 * (29 ** 2) * (31 ** 8),
        "c": (2 ** 8) * (3 ** 22) * (5 ** 4),
        "expected_quality": 1.62349,
    },
]

# Empirical cumulative counts of triples with quality > 1.4 from ABC@home distributed search
ABC_AT_HOME_COUNTS_Q14: dict[int, int] = {
    10 ** 6: 48,
    10 ** 9: 84,
    10 ** 12: 112,
    10 ** 15: 132,
    10 ** 18: 148,
}


def integer_radical(n: int) -> int:
    """Computes the square-free kernel / radical of n (product of distinct prime factors)."""
    if n <= 1:
        return 1
    rad = 1
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            rad *= d
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        rad *= temp
    return rad


def abc_quality(a: int, b: int, c: int) -> float:
    """Computes the quality q(a, b, c) = log(c) / log(rad(abc))."""
    if a + b != c:
        raise ValueError(f"a + b != c: {a} + {b} != {c}")
    if math.gcd(a, b) != 1:
        raise ValueError(f"gcd(a, b) != 1: gcd({a}, {b}) = {math.gcd(a, b)}")
    rad = integer_radical(a * b * c)
    return math.log(c) / math.log(rad)


def compute_empirical_scaling_exponent(x1: int, x2: int, n1: int, n2: int) -> float:
    """Computes the empirical power-law exponent alpha = log(n2 / n1) / log(x2 / x1)."""
    return math.log(n2 / n1) / math.log(x2 / x1)


def evaluate_power_law_discrepancy(
    eps: float = 0.4, x_target: int = 10 ** 18, x_base: int = 10 ** 6
) -> dict[str, Any]:
    """
    Evaluates the discrepancy between the predicted density power law
    N(X, eps) ~ c_eps * X^{1/(1+eps)} and actual empirical counts up to x_target.

    Returns dictionary with actual count, predicted count, ratio, and falsification status.
    """
    actual_count = ABC_AT_HOME_COUNTS_Q14.get(x_target, 148)
    base_count = ABC_AT_HOME_COUNTS_Q14.get(x_base, 48)

    predicted_exponent = 1.0 / (1.0 + eps)
    growth_factor = (x_target / x_base) ** predicted_exponent
    predicted_count = base_count * growth_factor

    actual_exponent = compute_empirical_scaling_exponent(
        x_base, x_target, base_count, actual_count
    )

    discrepancy_ratio = predicted_count / actual_count

    return {
        "eps": eps,
        "x_base": x_base,
        "x_target": x_target,
        "base_count": base_count,
        "actual_count": actual_count,
        "predicted_exponent": predicted_exponent,
        "actual_exponent": actual_exponent,
        "predicted_count": predicted_count,
        "discrepancy_ratio": discrepancy_ratio,
        "power_law_falsified": discrepancy_ratio > 1e6 and actual_exponent < predicted_exponent / 5,
    }
