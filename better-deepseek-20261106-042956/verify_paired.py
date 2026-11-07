#!/usr/bin/env python3
"""
verify_paired.py — reproduce the FINDINGS.md joint-view identifiability numbers.

For each of the 84 primitive sedenion zero divisors (de Marrais' assessors), computes:
  * CD rank of y ↦ y ·_CD k       (expect 12; from the 4-dim sedenion right annihilator)
  * Clifford rank of y ↦ y ·_Cliff k  (8 or 16, per `psi_cliff`)
  * Joint rank of the paired view     (16 or 14)

Reports the classification counts (48 with joint rank 16, 36 with joint rank 14).
Runs in pure Python with exact rational arithmetic; no dependencies.

Self-contained — no imports from the `hypercube` package.
"""
from fractions import Fraction
from collections import Counter
import sys

# --------------------------------------------------------------------- sign functions

def psi_cd(n, a, b):
    """CD sign: e_a ·_CD e_b = psi_cd(n,a,b) · e_{a XOR b}. Recursive, from cd_sign in
    hashrounds2.py."""
    if n == 0:
        return 1
    h = 1 << (n - 1)
    a0, a1 = a & (h - 1), a >> (n - 1)
    b0, b1 = b & (h - 1), b >> (n - 1)
    cj = 1 if b0 == 0 else -1
    if not a1 and not b1:
        return psi_cd(n - 1, a0, b0)
    if not a1:
        return psi_cd(n - 1, b0, a0)
    if not b1:
        return psi_cd(n - 1, a0, b0) * cj
    return -cj * psi_cd(n - 1, b0, a0)

def psi_cliff(n, a, b):
    """Clifford sign: e_a ·_Cliff e_b = psi_cliff(n,a,b) · e_{a XOR b}. From `psi_cliff` in
    hashrounds2.py."""
    s = 0
    for i in range(n):
        for j in range(n):
            if i > j and (a >> i) & 1 and (b >> j) & 1:
                s += 1
    s += bin(a & b).count("1")
    return -1 if s % 2 else 1

# --------------------------------------------------------------------- right-mult matrices

def right_mult_matrix(n, k_coeffs, sign):
    """M with (M · y)_c = (y · k)_c under the given sign function `sign(n,a,b)`."""
    N = 2 ** n
    M = [[Fraction(0)] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if k_coeffs[b] == 0:
                continue
            c = a ^ b
            M[c][a] += sign(n, a, b) * k_coeffs[b]
    return M

# --------------------------------------------------------------------- exact rank over ℚ

def rank_q(M):
    """Exact rank over ℚ via Gaussian elimination."""
    M = [[Fraction(x) for x in row] for row in M]
    m, n = len(M), len(M[0]) if M else 0
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(r + 1, m):
            if M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

# --------------------------------------------------------------------- the 84 assessors

def assessor_triples():
    """The 84 pairs (i, j, s) with 1≤i≤7, 9≤j≤15, j≠i+8, s=+1 or -1."""
    return [(i, j, s)
            for i in range(1, 8)
            for j in range(9, 16)
            if j != i + 8
            for s in (1, -1)]

def key_vector(n, i, j, s):
    """e_i + s·e_j as a coefficient vector on 2^n coordinates."""
    N = 2 ** n
    k = [0] * N
    k[i] = 1
    k[j] = s
    return k

# --------------------------------------------------------------------- main

def main():
    n = 4
    N = 2 ** n
    triples = assessor_triples()
    assert len(triples) == 84, f"expected 84 assessors, got {len(triples)}"

    rows = []
    for (i, j, s) in triples:
        k = key_vector(n, i, j, s)
        CD = right_mult_matrix(n, k, psi_cd)
        CF = right_mult_matrix(n, k, psi_cliff)
        stacked = [CD[c] for c in range(N)] + [CF[c] for c in range(N)]  # 32 x N
        rCD = rank_q(CD)
        rCF = rank_q(CF)
        rST = rank_q(stacked)
        rows.append((i, j, s, rCD, rCF, rST))

    cd_hist = Counter(r[3] for r in rows)
    cf_hist = Counter(r[4] for r in rows)
    st_hist = Counter(r[5] for r in rows)

    print(f"84 assessors (i ∈ [1,7], j ∈ [9,15], j ≠ i+8, s ∈ {{±1}})")
    print(f"  CD rank histogram:              {dict(sorted(cd_hist.items()))}")
    print(f"  Clifford rank histogram:        {dict(sorted(cf_hist.items()))}")
    print(f"  Joint (stacked) rank histogram: {dict(sorted(st_hist.items()))}")
    print()
    print("Expected (FINDINGS.md):")
    print("  CD rank histogram:              {12: 84}")
    print("  Clifford rank histogram:        {8: 48, 16: 36}")
    print("  Joint (stacked) rank histogram: {16: 48, 14: 36}")
    print()

    ok = (cd_hist == Counter({12: 84}) and
          cf_hist == Counter({8: 48, 16: 36}) and
          st_hist == Counter({16: 48, 14: 36}))

    if ok:
        print("✓ FINDINGS classification reproduced exactly.")
        return 0
    else:
        print("✗ Classification does not match; see histograms above.")
        return 1

if __name__ == "__main__":
    sys.exit(main())
