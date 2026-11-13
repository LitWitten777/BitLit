"""
Sedenion Cross-Octet Stratification.

Generates the 256 cross-octet vectors of the form:
    v = s1 * e_i + s2 * e_{8+j}  for i, j in {0..7}, s1, s2 in {+1, -1}
and stratifies them into:
    - 168 zero divisors
    - 88 non-zero-divisors

Optimized using fast_algebra.fast_annihilate_cross_octet() for O(1) checks
instead of O(n²) full sedenion multiplications.
"""

from dataclasses import dataclass

from .algebra import Sedenion
from .exceptions import SignError
from .fast_algebra import fast_annihilate_cross_octet, fast_is_cross_octet_zd, fast_xor_charge


@dataclass(frozen=True)
class CrossOctetVector:
    """
    Represents a normalized cross-octet vector of the form:
    v = s1*e_i + s2*e_{8+j}
    where i, j in {0..7} and s1, s2 in {+1, -1}.

    Properties:
        key: Tuple (i, j, s1, s2) for hashing/comparison
        chi: XOR charge (i ^ j) in range 1..7 for zero divisors
    """

    i: int
    j: int
    s1: int
    s2: int
    sedenion: Sedenion

    def __post_init__(self) -> None:
        """Validate input ranges and signs."""
        if not (0 <= self.i < 8):
            raise ValueError(f"Index i must be in 0..7, got {self.i}")
        if not (0 <= self.j < 8):
            raise ValueError(f"Index j must be in 0..7, got {self.j}")
        if self.s1 not in (1, -1):
            raise SignError(f"s1 must be +1 or -1, got {self.s1}")
        if self.s2 not in (1, -1):
            raise SignError(f"s2 must be +1 or -1, got {self.s2}")

    @property
    def key(self) -> tuple[int, int, int, int]:
        """Return canonical tuple key for hashing."""
        return (self.i, self.j, self.s1, self.s2)

    @property
    def chi(self) -> int:
        """Compute XOR charge chi = i ^ j (conserved under annihilation)."""
        return fast_xor_charge(self.i, self.j)

    def __repr__(self) -> str:
        s1_str = "" if self.s1 == 1 else "-"
        s2_str = "+" if self.s2 == 1 else "-"
        return f"{s1_str}e_{self.i} {s2_str} e_{8 + self.j}"


def generate_cross_octet_vectors() -> list[CrossOctetVector]:
    """Generates all 256 cross-octet sedenion vectors."""
    vectors = []
    for i in range(8):
        for j in range(8):
            for s1 in (1, -1):
                for s2 in (1, -1):
                    coords = [0] * 16
                    coords[i] = s1
                    coords[8 + j] = s2
                    sed = Sedenion(coords)
                    vectors.append(CrossOctetVector(i=i, j=j, s1=s1, s2=s2, sedenion=sed))
    return vectors


def stratify_cross_octet(
    vectors: list[CrossOctetVector] | None = None,
) -> tuple[
    list[CrossOctetVector], list[CrossOctetVector], dict[CrossOctetVector, list[CrossOctetVector]]
]:
    """
    Partitions cross-octet vectors into (zero_divisors, non_zero_divisors, annihilator_map).

    Uses O(1) fast algebra checks instead of O(n²) full sedenion multiplications.
    Complexity: O(n²) calls but each call is O(1) bitwise ops instead of O(16) mults.

    Args:
        vectors: Optional pre-generated list of cross-octet vectors

    Returns:
        Tuple of (zero_divisors list, non_zero_divisors list, annihilator map dict)

    The annihilator map maps each zero divisor to the list of cross-octet vectors it annihilates.
    """
    if vectors is None:
        vectors = generate_cross_octet_vectors()

    # Pre-filter: identify zero divisors using O(1) check
    # Theorem: cross-octet vector is ZD iff i != 0 and j != 0 and i != j
    zero_divisor_candidates = [v for v in vectors if fast_is_cross_octet_zd(v.i, v.j)]

    n = len(zero_divisor_candidates)
    annihilators: dict[CrossOctetVector, list[CrossOctetVector]] = {
        v: [] for v in zero_divisor_candidates
    }

    # Find all annihilation pairs using O(1) fast check
    # Only need to check ZD candidates against each other
    for idx_u in range(n):
        u = zero_divisor_candidates[idx_u]
        for idx_w in range(n):
            w = zero_divisor_candidates[idx_w]
            # Fast O(1) annihilation check without full sedenion multiplication
            if fast_annihilate_cross_octet(u.i, u.j, u.s1, u.s2, w.i, w.j, w.s1, w.s2):
                annihilators[u].append(w)

    # Filter to actual zero divisors (those with at least one annihilator)
    zero_divisors = [v for v in zero_divisor_candidates if len(annihilators[v]) > 0]

    # Non-zero-divisors are everything else
    zd_set = {v.key for v in zero_divisors}
    non_zero_divisors = [v for v in vectors if v.key not in zd_set]
    return zero_divisors, non_zero_divisors, annihilators


def triangular_number(n: int) -> int:
    """Computes the n-th triangular number T_n = n * (n + 1) // 2."""
    if n < 0:
        raise ValueError(f"n must be non-negative, got {n}")
    return n * (n + 1) // 2


def nicomachus_cube_sum(n: int) -> int:
    """Computes ∑_{k=1}^n k^3 via Nicomachus's Theorem: (T_n)^2."""
    t = triangular_number(n)
    return t * t


def nicomachus_block(n: int) -> list[int]:
    """Generates the n consecutive odd numbers whose sum is n^3.

    The n-th block is centered at n^2:
        [n(n - 1) + 1 + 2k  for k in range(n)]
    """
    if n <= 0:
        raise ValueError(f"n must be positive, got {n}")
    start = n * (n - 1) + 1
    return [start + 2 * k for k in range(n)]


def cross_half_zd_triangular(dimension: int) -> int:
    """Computes cross-half zero divisors via the 8-fold triangular formula:
    ZDs(D) = (D - 2)(D - 4) = 8 * T_{(D / 2) - 2}
    """
    if dimension < 4 or (dimension & (dimension - 1)) != 0:
        raise ValueError(f"Dimension must be a power of 2 >= 4, got {dimension}")
    half = dimension // 2
    if half < 2:
        return 0
    return 8 * triangular_number(half - 2)
