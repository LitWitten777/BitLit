r"""
src/sedenion/eisenstein_filter.py — Eisenstein Norm Sieve & Casimir Spectral Filter.

Implements the arithmetic filter based on the binary quadratic form:
    4 * \lambda(p, q) + 28 = (2p + 3q + 5)^2 + 3(q + 1)^2

Where:
    u = 2p + 3q + 5
    v = q + 1
    N = u^2 + 3*v^2 = 4*(\lambda + 7)

An integer \lambda >= 0 is a Laplace-Beltrami Casimir eigenvalue on V_2(R^7)
if and only if \lambda + 7 is the field norm of an Eisenstein integer in Z[\omega]
satisfying the admissible cone condition:
    v >= 1,  u >= 3v + 2,  u \equiv v (mod 2).

Provides O(1) necessary sieve pre-filtering and exact representation enumeration.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import List


@dataclass(frozen=True)
class CasimirRepresentation:
    """A pair of highest weights (p, q) achieving a Casimir eigenvalue."""

    p: int
    q: int
    eigenvalue: int
    u: int
    v: int
    norm: int


class EisensteinNormFilter:
    r"""
    Sieve and solver for the binary quadratic form u^2 + 3v^2 representing
    Casimir eigenvalues \lambda(p, q) = p^2 + 3pq + 3q^2 + 5p + 9q.
    """

    @staticmethod
    def is_eisenstein_norm_candidate(m: int) -> bool:
        r"""
        Necessary condition: An integer M can be written as a norm in Z[\omega]
        (i.e. x^2 + xy + y^2 or u^2 + 3v^2 / 4) only if every prime factor
        p \equiv 2 (mod 3) occurs with an even exponent.
        """
        if m < 7:
            return False

        temp = m
        # Factor out 2
        count2 = 0
        while temp % 2 == 0:
            count2 += 1
            temp //= 2
        if count2 % 2 != 0:
            return False

        # Factor out odd primes
        d = 3
        while d * d <= temp:
            if temp % d == 0:
                cnt = 0
                while temp % d == 0:
                    cnt += 1
                    temp //= d
                if d % 3 == 2 and cnt % 2 != 0:
                    return False
            d += 2
        if temp > 1:
            if temp % 3 == 2:
                return False

        return True

    @classmethod
    def filter_casimir_candidate(cls, lam: int) -> bool:
        """
        Rapid pre-filter checking if `lam` could be a Casimir eigenvalue.
        Runs in O(sqrt(M)) time.
        """
        if lam < 0:
            return False
        if lam == 0:
            return True
        m = lam + 7
        return cls.is_eisenstein_norm_candidate(m)

    @classmethod
    def solve_representations(cls, lam: int) -> List[CasimirRepresentation]:
        """
        Finds all highest weight pairs (p, q) such that:
            stiefel_eigenvalue(p, q) == lam.
        """
        if lam < 0:
            return []
        if not cls.filter_casimir_candidate(lam):
            return []

        m = lam + 7
        n_target = 4 * m  # u^2 + 3*v^2 = 4*m

        results: List[CasimirRepresentation] = []
        max_v = int(math.isqrt(n_target // 3))

        for v in range(1, max_v + 1):
            rem = n_target - 3 * v * v
            if rem < 0:
                break
            u = int(math.isqrt(rem))
            if u * u != rem:
                continue

            # Check cone constraints
            if u >= 3 * v + 2 and (u % 2 == v % 2):
                p = (u - 3 * v - 2) // 2
                q = v - 1
                results.append(
                    CasimirRepresentation(
                        p=p,
                        q=q,
                        eigenvalue=lam,
                        u=u,
                        v=v,
                        norm=n_target,
                    )
                )

        return results

    @classmethod
    def multiplicity(cls, lam: int) -> int:
        """Returns the number of distinct highest weight pairs (p, q) for eigenvalue `lam`."""
        return len(cls.solve_representations(lam))

    @staticmethod
    def casimir_formula(p: int, q: int) -> int:
        r"""Computes the Casimir eigenvalue \lambda(p, q) = p^2 + 3pq + 3q^2 + 5p + 9q."""
        return p * p + 3 * p * q + 3 * q * q + 5 * p + 9 * q
