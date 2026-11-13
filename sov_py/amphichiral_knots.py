r"""
Amphichiral Knot Odd Braid Index Invariant, Dihedral Symmetry Classification & 3-Braid Palindromes (HYP-237).

Grounded in:
- Hyungseok Jung (2026):
  "Amphichiral Knots: Odd Braid Index and Symmetry Classification in the Three-Braid Case"
  (/data/mind/cognition/library/Amphichiral Knots_ Odd Braid Index and Symmetry Classification in the Three-Braid Case .pdf)
- Alexander Stoimenow (2002):
  "Göttingen questions on braid index and achirality"
- Dynnikov & Prasolov (2013):
  "Braid index and Jones conjecture", Theorem 9.

Key Mathematical Invariants:
1. Stoimenow Conjecture Settlement (Theorem A):
   The braid index b(K) of every amphichiral knot K is strictly odd:
       b(K) \equiv 1 \pmod 2.
   There are NO amphichiral knots of even braid index.
   Proof mechanism:
   - By Dynnikov-Prasolov resolution of the Jones conjecture, all minimal-strand braid
     representatives have the same exponent sum e(\beta).
   - Since mirroring negates exponent sum e(m(\beta)) = -e(\beta) while preserving
     minimal strand count, amphichirality forces e(\beta) = 0.
   - Since e(\beta) = \sum \varepsilon_j \equiv \ell \pmod 2, word length \ell is even.
   - The permutation homomorphism \pi: B_n \to S_n has sgn(\pi(\beta)) = (-1)^\ell = +1.
   - But for a knot, \pi(\beta) is an n-cycle, with signature sgn(\pi(\beta)) = (-1)^{n-1}.
   - Thus +1 = (-1)^{n-1} \implies n - 1 is even \implies n = b(K) is ODD.

2. Dihedral Action on Alternating 3-Braid Standard Forms:
   For word c = (a_1, b_1, ..., a_n, b_n) with a_i, b_i \ge 1, the 3-braid is:
       \beta_c = \sigma_1^{a_1} \sigma_2^{-b_1} \cdots \sigma_1^{a_n} \sigma_2^{-b_n}.
   The dihedral group D_{4n} acts on c by:
       - Rotation \rho: left shift by 1 position (c_1, ..., c_{2n}) \mapsto (c_2, ..., c_{2n}, c_1)
       - Reflection \tau: reversal (c_1, ..., c_{2n}) \mapsto (c_{2n}, ..., c_1).
   Conjugacy classes in B_3 correspond bijectively to \langle \rho^2 \rangle-orbits.
   The quotient group D_{4n} / \langle \rho^2 \rangle \cong Z_2 \times Z_2 \cong G = {1, m, r, mr}.

3. Complete 3-Braid Symmetry Classification (Theorems B & C):
   A prime knot K of braid index 3 in alternating standard form is:
   - Fully amphichiral (FA, Sym(K) = G): c is a palindrome and has odd period (e.g. 4_1, c=(1,1,1,1));
     or c admits a non-degenerate flype (rotation of (k, 1, 1, k) for k \ge 2, e.g. 6_3, c=(2,1,1,2)).
   - Positive amphichiral (+A, Sym(K) = {1, m}): c has odd period, but is not a palindrome (e.g. 14a_18676, c=(1,2,4,1,2,4)).
   - Negative amphichiral (-A, Sym(K) = {1, mr}): c is a palindrome, but has even period (e.g. 8_17, c=(2,1,1,1,1,2)).
   - Chiral: neither condition holds.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Union, Any


@dataclass(frozen=True)
class AmphichiralParityAudit:
    braid_index: int
    exponent_sum: int
    word_length_even: bool
    permutation_sgn: int
    n_cycle_sgn: int
    parity_consistent: bool
    is_amphichiral_admissible: bool


def audit_amphichiral_braid_index_parity(n: int) -> AmphichiralParityAudit:
    """
    Evaluates whether an amphichiral knot can have braid index n,
    following the Dynnikov-Prasolov / Jung parity reduction:
    - Minimal exponent sum e(beta) = 0.
    - Word length ell = sum |eps| is even -> sgn(pi(beta)) = (-1)^ell = +1.
    - pi(beta) is an n-cycle -> sgn(pi(beta)) = (-1)^(n - 1).
    - Consistency: +1 = (-1)^(n - 1) iff n is odd.
    """
    if n < 1:
        raise ValueError(f"Braid index must be >= 1, got {n}")

    exponent_sum = 0  # Amphichirality forces minimal writhe 0
    word_length_even = True
    perm_sgn = 1  # (-1)^even = +1
    cycle_sgn = 1 if (n - 1) % 2 == 0 else -1

    consistent = (perm_sgn == cycle_sgn)
    admissible = (n % 2 == 1)

    return AmphichiralParityAudit(
        braid_index=n,
        exponent_sum=exponent_sum,
        word_length_even=word_length_even,
        permutation_sgn=perm_sgn,
        n_cycle_sgn=cycle_sgn,
        parity_consistent=consistent,
        is_amphichiral_admissible=admissible,
    )


def compute_word_period(c: Tuple[int, ...]) -> int:
    """
    Computes the minimal period p of the word c:
    the smallest p in {1, ..., L} such that c[i] == c[(i + p) % L] for all i.
    """
    L = len(c)
    for p in range(1, L + 1):
        if L % p == 0:
            if all(c[i] == c[(i + p) % L] for i in range(L)):
                return p
    return L


def check_word_palindrome(c: Tuple[int, ...]) -> Tuple[bool, int]:
    """
    Checks if c is a palindrome modulo the subgroup of even shifts <rho^2>:
    i.e., whether tau(c) = rho^{2j}(c) for some j in {0, ..., n-1}.
    Returns (is_palindrome, j) where j is the even shift index, or (False, -1).
    """
    L = len(c)
    rev = c[::-1]
    for j in range(0, L, 2):
        # rho^{2j}(c) shifts left by 2j
        shifted = c[j:] + c[:j]
        if rev == shifted:
            return True, j
    return False, -1


def check_non_degenerate_flype(c: Tuple[int, ...]) -> Tuple[bool, int]:
    """
    Checks if c is a cyclic rotation of (k, 1, 1, k) for some k >= 2.
    Under Theorem 4.19, this corresponds to the non-degenerate flype exception
    in Birman-Menasco classification (e.g. knot 6_3 with c = (2, 1, 1, 2)).
    """
    L = len(c)
    if L != 4:
        return False, 0

    # Look for rotations of (k, 1, 1, k)
    for shift in range(4):
        rot = c[shift:] + c[:shift]
        if rot[1] == 1 and rot[2] == 1 and rot[0] == rot[3] and rot[0] >= 2:
            return True, rot[0]
    return False, 0


@dataclass(frozen=True)
class ThreeBraidSymmetryClassification:
    word: Tuple[int, ...]
    length: int
    period: int
    has_odd_period: bool
    is_palindrome: bool
    palindrome_shift: int
    has_flype: bool
    symmetry_type: str  # "FA", "+A", "-A", or "Chiral"
    symmetry_group: str  # "G", "{1, m}", "{1, mr}", or "{1}"
    is_amphichiral: bool


def classify_3braid_amphichirality(c: Union[List[int], Tuple[int, ...]]) -> ThreeBraidSymmetryClassification:
    """
    Classifies a prime alternating 3-braid knot encoded by word c = (a_1, b_1, ..., a_n, b_n).
    Implements Theorems B & C of Hyungseok Jung (2026).
    """
    t_c = tuple(c)
    L = len(t_c)
    if L % 2 != 0:
        raise ValueError(f"Alternating standard word must have even length 2n, got {L}")
    if any(x < 1 for x in t_c):
        raise ValueError("Word entries must be positive integers >= 1")

    p = compute_word_period(t_c)
    has_odd_p = (p % 2 == 1)
    is_palin, shift = check_word_palindrome(t_c)
    has_flype, flype_k = check_non_degenerate_flype(t_c)

    # Classification logic:
    # If it has a non-degenerate flype, it is fully amphichiral (Theorem 4.19)
    if has_flype:
        sym_type = "FA"
        sym_group = "G"
        is_amphi = True
    elif is_palin and has_odd_p:
        sym_type = "FA"  # Fully amphichiral (Case i)
        sym_group = "G"
        is_amphi = True
    elif has_odd_p and not is_palin:
        sym_type = "+A"  # Positive amphichiral (Case ii)
        sym_group = "{1, m}"
        is_amphi = True
    elif is_palin and not has_odd_p:
        sym_type = "-A"  # Negative amphichiral (Case iii)
        sym_group = "{1, mr}"
        is_amphi = True
    else:
        sym_type = "Chiral"
        sym_group = "{1}"
        is_amphi = False

    return ThreeBraidSymmetryClassification(
        word=t_c,
        length=L,
        period=p,
        has_odd_period=has_odd_p,
        is_palindrome=is_palin,
        palindrome_shift=shift,
        has_flype=has_flype,
        symmetry_type=sym_type,
        symmetry_group=sym_group,
        is_amphichiral=is_amphi,
    )


def dihedral_quotient_group_orders(n: int) -> Dict[str, int]:
    """
    Calculates the orders of the dihedral group D_{4n}, the rotation normal subgroup
    <rho^2> of order n, and the quotient group G = D_{4n} / <rho^2> of order 4.
    """
    if n < 1:
        raise ValueError(f"n must be >= 1, got {n}")
    order_d4n = 4 * n
    order_kernel = n
    order_quotient = order_d4n // order_kernel
    return {
        "D_4n": order_d4n,
        "ker_phi": order_kernel,
        "G": order_quotient,
    }
