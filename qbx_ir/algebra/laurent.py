"""
Exact Laurent polynomials in one variable with rational coefficients.

Used by the polynomial invariants (Kauffman bracket, Jones, Burau,
Alexander).  Kept dependency-free on purpose.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, Iterable, List, Tuple, Union

Number = Union[int, Fraction]


class Laurent:
    """Σ c_k x^k with finitely many non-zero c_k ∈ ℚ, k ∈ ℤ."""

    __slots__ = ("coeffs",)

    def __init__(self, coeffs: Union[Dict[int, Number], None] = None):
        self.coeffs: Dict[int, Fraction] = {}
        if coeffs:
            for k, v in coeffs.items():
                v = Fraction(v)
                if v != 0:
                    self.coeffs[int(k)] = v

    # ---- constructors ----------------------------------------------------

    @classmethod
    def const(cls, c: Number) -> "Laurent":
        return cls({0: c})

    @classmethod
    def monomial(cls, k: int, c: Number = 1) -> "Laurent":
        return cls({k: c})

    @staticmethod
    def _coerce(other) -> "Laurent":
        if isinstance(other, Laurent):
            return other
        return Laurent.const(other)

    # ---- arithmetic ------------------------------------------------------

    def __add__(self, other) -> "Laurent":
        other = self._coerce(other)
        out = dict(self.coeffs)
        for k, v in other.coeffs.items():
            out[k] = out.get(k, 0) + v
        return Laurent(out)

    __radd__ = __add__

    def __neg__(self) -> "Laurent":
        return Laurent({k: -v for k, v in self.coeffs.items()})

    def __sub__(self, other) -> "Laurent":
        return self + (-self._coerce(other))

    def __rsub__(self, other) -> "Laurent":
        return self._coerce(other) - self

    def __mul__(self, other) -> "Laurent":
        other = self._coerce(other)
        out: Dict[int, Fraction] = {}
        for k1, v1 in self.coeffs.items():
            for k2, v2 in other.coeffs.items():
                out[k1 + k2] = out.get(k1 + k2, 0) + v1 * v2
        return Laurent(out)

    __rmul__ = __mul__

    def __pow__(self, e: int) -> "Laurent":
        if e < 0:
            if len(self.coeffs) != 1:
                raise ValueError("only monomials can be inverted")
            (k, v), = self.coeffs.items()
            return Laurent({k * e: Fraction(1) / v ** (-e)})
        result = Laurent.const(1)
        base = self
        while e:
            if e & 1:
                result = result * base
            base = base * base
            e >>= 1
        return result

    def __eq__(self, other) -> bool:
        return self.coeffs == self._coerce(other).coeffs

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.coeffs.items())))

    # ---- queries ---------------------------------------------------------

    def is_zero(self) -> bool:
        return not self.coeffs

    def min_degree(self) -> int:
        return min(self.coeffs) if self.coeffs else 0

    def max_degree(self) -> int:
        return max(self.coeffs) if self.coeffs else 0

    def shift(self, k: int) -> "Laurent":
        return Laurent({e + k: v for e, v in self.coeffs.items()})

    def substitute_power(self, m: int) -> "Laurent":
        """x ↦ x^m."""
        return Laurent({e * m: v for e, v in self.coeffs.items()})

    def evaluate(self, x: complex) -> complex:
        return sum(complex(v) * x ** e for e, v in self.coeffs.items())

    def items(self) -> List[Tuple[int, Fraction]]:
        return sorted(self.coeffs.items())

    def to_int_dict(self) -> Dict[int, int]:
        out = {}
        for k, v in self.items():
            if v.denominator != 1:
                raise ValueError("non-integer coefficient")
            out[k] = int(v)
        return out

    def divmod_exact(self, other: "Laurent") -> "Laurent":
        """Exact division self / other; raises if not divisible."""
        if other.is_zero():
            raise ZeroDivisionError
        if self.is_zero():
            return Laurent()
        a_shift, b_shift = self.min_degree(), other.min_degree()
        a = [self.coeffs.get(a_shift + i, Fraction(0))
             for i in range(self.max_degree() - a_shift + 1)]
        b = [other.coeffs.get(b_shift + i, Fraction(0))
             for i in range(other.max_degree() - b_shift + 1)]
        if len(a) < len(b):
            raise ValueError("not exactly divisible")
        q = [Fraction(0)] * (len(a) - len(b) + 1)
        rem = list(a)
        for i in range(len(q) - 1, -1, -1):
            c = rem[i + len(b) - 1] / b[-1]
            q[i] = c
            for j, bj in enumerate(b):
                rem[i + j] -= c * bj
        if any(r != 0 for r in rem):
            raise ValueError("not exactly divisible")
        return Laurent({i + a_shift - b_shift: c for i, c in enumerate(q)})

    def normalize_unit(self) -> "Laurent":
        """Representative up to ±x^k: lowest degree 0, positive lowest coefficient."""
        if self.is_zero():
            return self
        p = self.shift(-self.min_degree())
        if p.coeffs[0] < 0:
            p = -p
        return p

    def format(self, var: str = "t", half: bool = False) -> str:
        """Human-readable; if half=True, exponents are in units of 1/2."""
        if not self.coeffs:
            return "0"
        parts = []
        for k, v in sorted(self.coeffs.items(), reverse=True):
            if half:
                exp = f"{k // 2}" if k % 2 == 0 else f"{k}/2"
            else:
                exp = str(k)
            if k == 0:
                mono = ""
            elif exp == "1":
                mono = var
            else:
                mono = f"{var}^{exp}"
            mag = abs(v)
            coef = "" if (mag == 1 and mono) else str(mag)
            term = coef + mono
            sign = "-" if v < 0 else "+"
            parts.append((sign, term))
        s = ("-" if parts[0][0] == "-" else "") + parts[0][1]
        for sign, term in parts[1:]:
            s += f" {sign} {term}"
        return s

    def __repr__(self) -> str:
        return f"Laurent({self.format('x')})"

    __str__ = lambda self: self.format("x")  # noqa: E731


def det(matrix: List[List[Laurent]]) -> Laurent:
    """Determinant by memoised cofactor expansion (fine for size ≤ ~10)."""
    m = len(matrix)
    if m == 0:
        return Laurent.const(1)
    memo: Dict[Tuple[int, int], Laurent] = {}

    def rec(row: int, mask: int) -> Laurent:
        if row == m:
            return Laurent.const(1)
        key = (row, mask)
        if key in memo:
            return memo[key]
        total = Laurent()
        sign_count = 0
        for col in range(m):
            if mask & (1 << col):
                continue
            entry = matrix[row][col]
            if not entry.is_zero():
                term = entry * rec(row + 1, mask | (1 << col))
                total = total + (term if sign_count % 2 == 0 else -term)
            sign_count += 1
        memo[key] = total
        return total

    return rec(0, 0)


def identity_matrix(m: int) -> List[List[Laurent]]:
    return [[Laurent.const(1 if i == j else 0) for j in range(m)] for i in range(m)]


def matmul(a: List[List[Laurent]], b: List[List[Laurent]]) -> List[List[Laurent]]:
    m, k, n = len(a), len(b), len(b[0]) if b else 0
    out = []
    for i in range(m):
        row = []
        for j in range(n):
            s = Laurent()
            for x in range(k):
                if not a[i][x].is_zero() and not b[x][j].is_zero():
                    s = s + a[i][x] * b[x][j]
            row.append(s)
        out.append(row)
    return out


def from_iterable(pairs: Iterable[Tuple[int, Number]]) -> Laurent:
    out: Dict[int, Fraction] = {}
    for k, v in pairs:
        out[k] = out.get(k, 0) + Fraction(v)
    return Laurent(out)
