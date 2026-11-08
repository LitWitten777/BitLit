"""
Algebraic invariants of a braid:

- permutation: how strands are permuted by the braid (B_n → S_n)
- writhe / exponent sum: sum of crossing signs (B_n → ℤ, the abelianisation)
- closure_components: the link components of the braid closure
- linking_matrix / linking_number: pairwise linking numbers of the closure

All of these are invariants of the braid group element (they are preserved
by the rewrite rules R01–R03; this is machine-checked in the Lean library
``QBX/Formal``).
"""

from __future__ import annotations

from typing import Dict, List, Tuple

from qbx_ir.core.braid import Braid


def permutation(braid: Braid) -> Tuple[int, ...]:
    """
    Return the permutation induced by the braid.

    Convention: perm[i] = the strand (initial position) that ends up at
    physical position i+1 (1-indexed) after applying the braid.

    Result is a tuple of length strand_count.
    """
    n = braid.strand_count
    positions = list(range(1, n + 1))  # positions[p-1] = strand at position p
    for g in braid.word:
        i = g.index
        positions[i - 1], positions[i] = positions[i], positions[i - 1]
    return tuple(positions)


def permutation_one_line(braid: Braid) -> List[int]:
    """perm_one_line[i] = final position of initial strand i+1 (1-indexed)."""
    n = braid.strand_count
    p = permutation(braid)
    result = [0] * n
    for j, s in enumerate(p):
        result[s - 1] = j + 1
    return result


def writhe(braid: Braid) -> int:
    """Sum of the signs of all crossings (= exponent sum of the word)."""
    return sum(g.sign for g in braid.word)


exponent_sum = writhe


def closure_components(braid: Braid) -> List[List[int]]:
    """
    Components of the closure of the braid, as lists of strand ids
    (initial positions).  These are the cycles of the permutation.
    """
    dest = permutation_one_line(braid)
    n = braid.strand_count
    seen = [False] * n
    comps: List[List[int]] = []
    for start in range(1, n + 1):
        if seen[start - 1]:
            continue
        comp = []
        cur = start
        while not seen[cur - 1]:
            seen[cur - 1] = True
            comp.append(cur)
            cur = dest[cur - 1]
        comps.append(comp)
    return comps


def component_count(braid: Braid) -> int:
    return len(closure_components(braid))


def linking_matrix(braid: Braid) -> Dict[Tuple[int, int], int]:
    """
    Pairwise linking numbers lk(C_a, C_b), a < b, of the closure components
    (indexed by position in :func:`closure_components`).  lk is half the sum
    of the signs of crossings between the two components.
    """
    comps = closure_components(braid)
    comp_of = {}
    for idx, c in enumerate(comps):
        for s in c:
            comp_of[s] = idx
    totals: Dict[Tuple[int, int], int] = {
        (a, b): 0 for a in range(len(comps)) for b in range(a + 1, len(comps))
    }
    for c in braid.crossings():
        a, b = comp_of[c.left_strand_id], comp_of[c.right_strand_id]
        if a == b:
            continue
        key = (min(a, b), max(a, b))
        totals[key] += c.sign
    # Crossings between two closed components come in even total.
    return {k: v // 2 for k, v in totals.items()}


def linking_number(braid: Braid) -> int:
    """
    Total linking number of the closure: Σ_{a<b} lk(C_a, C_b).
    It is 0 when the closure is a knot (one component).
    """
    return sum(linking_matrix(braid).values())


def is_positive(braid: Braid) -> bool:
    """True iff every generator has positive sign."""
    return all(g.sign > 0 for g in braid.word)


def is_pure(braid: Braid) -> bool:
    """True iff the braid induces the identity permutation."""
    return permutation(braid) == tuple(range(1, braid.strand_count + 1))
