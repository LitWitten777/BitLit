"""Pentagon checksum for Cayley-Dickson products.

    python3 -m hypercube.cdcheck 1 2 4 8            check one word (basis indices e_1 e_2 e_4 e_8)
    python3 -m hypercube.cdcheck --fuzz [N]         N random words (default 100000) on manifold.cd.mul
    python3 -m hypercube.cdcheck --mutants          which injected multiplication bugs the check sees

A *word* is a sequence of basis indices i_1 ... i_m at level n (dimension 2^n).  cdcheck(word):
  1. structure: every product e_i e_j computed by the routine is +-e_(i xor j) (coefficient +-1,
     nothing else non-zero);
  2. pentagon: for every window (a, b, c, d) of 4 consecutive letters, the associator phases
     w(x,y,z) = s with (e_x e_y) e_z = s * e_x (e_y e_z), computed from the routine's own triple
     products, satisfy  w(b,c,d) w(a^b,c,d) w(a,b^c,d) w(a,b,c^d) w(a,b,c) = +1.
  strict=True also compares each sign with the reference recursion `manifold.cd.fsgn`
  (Lean `fsgn`, `basis_mul` in RequestProject/Manifold/CDTower.lean).

Proved: the pentagon identity (`signCoboundary_pentagon`,
sovereign/RequestProject/SedenionCocycle.lean; `assocPhase_pentagon`,
sovereign/Sovereign/Algebra/TowerCocycle.lean).  Once the structure check passes, every phase is
the coboundary of a +-1 sign table, so a correct routine never fails the pentagon: false-positive
rate 0 by proof.  The same proof cuts the other way: ANY +-1 sign table passes, so the pentagon
alone cannot see sign-table bugs.  It catches bugs that break the e_i e_j = +-e_(i xor j)
structure; `strict` catches sign bugs.  See `--mutants`.

Integration: `manifold/cd.py` calls `debug_check` on every `mul` when the environment variable
Q6_CDCHECK=1 is set (debug mode); a violation raises CDCheckError -- it is a bug, not a signal.
"""

import random
import sys

from manifold import cd


class CDCheckError(AssertionError):
    pass


def _level(word):
    m = max(list(word) + [1])
    return max(1, m.bit_length())


def cdcheck(word, n=None, mulf=None, strict=False):
    """Check one word; returns {'ok', 'violations', 'pentagons'}."""
    mulf = mulf or cd.raw_mul
    word = list(word)
    n = n or _level(word)
    N = 2 ** n
    e = lambda i: cd.basis(n, i)
    pair = {}
    bad = []

    def prod(i, j):
        if (i, j) not in pair:
            v = mulf(e(i), e(j))
            k = i ^ j
            ok = len(v) == N and v[k] in (1, -1) and all(t == 0 for m, t in enumerate(v) if m != k)
            if not ok:
                bad.append(("structure", i, j))
            elif strict and v[k] != cd.fsgn(n, i, j):
                bad.append(("sign", i, j))
            pair[(i, j)] = v
        return pair[(i, j)]

    def phase(x, y, z):
        L = mulf(prod(x, y), e(z))
        R = mulf(e(x), prod(y, z))
        k = x ^ y ^ z
        if L[k] in (1, -1) and R[k] in (1, -1) and \
                all(L[m] == 0 and R[m] == 0 for m in range(N) if m != k):
            return L[k] * R[k]
        bad.append(("associator", x, y, z))
        return 0

    for i, j in zip(word, word[1:]):
        prod(i, j)
    npent = 0
    for a, b, c, d in zip(word, word[1:], word[2:], word[3:]):
        p = phase(b, c, d) * phase(a ^ b, c, d) * phase(a, b ^ c, d) * phase(a, b, c ^ d) * phase(a, b, c)
        npent += 1
        if p != 1:
            bad.append(("pentagon", a, b, c, d))
    return {"ok": not bad, "violations": bad, "pentagons": npent, "level": n}


_rng = random.Random(0)


def debug_check(n, mulf):
    """Called by manifold.cd.mul in debug mode: one random 4-letter word at level n."""
    if n < 1:
        return
    w = [_rng.randrange(2 ** n) for _ in range(4)]
    r = cdcheck(w, n, mulf)
    if not r["ok"]:
        raise CDCheckError(f"CD product failed the pentagon checksum at level {n}, word {w}: "
                           f"{r['violations'][:3]}")


def fuzz(nwords=100_000, seed=20261025, mulf=None, strict=False, levels=(2, 3, 4), heavy=(5, 6),
         heavy_words=2000):
    rnd = random.Random(seed)
    fails = total = pent = 0
    plan = [(rnd.choice(levels), rnd.randint(4, 8)) for _ in range(nwords - heavy_words * len(heavy))]
    plan += [(n, 4) for n in heavy for _ in range(heavy_words)]
    for n, m in plan:
        w = [rnd.randrange(2 ** n) for _ in range(m)]
        r = cdcheck(w, n, mulf, strict)
        total += 1
        pent += r["pentagons"]
        fails += not r["ok"]
    return {"words": total, "pentagons": pent, "violations": fails}


# ------------------------------------------------------------------ injected bugs (mutants)

def _mut_sign_flip(x, y):
    """One wrong entry in the sign table: e_1 e_2 negated (levels >= 2)."""
    r = cd.raw_mul(x, y)
    if len(x) >= 4 and x[1] and y[2] and sum(map(abs, x)) == 1 and sum(map(abs, y)) == 1:
        r = [-t for t in r]
    return r


def _mut_no_conj(x, y):
    """Formula bug: (a, b)(c, d) = (ac - d b, d a + b conj c) -- conj(d) dropped."""
    if len(x) == 1:
        return [x[0] * y[0]]
    h = len(x) // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return cd.sub(_mut_no_conj(a, c), _mut_no_conj(d, b)) + cd.add(_mut_no_conj(d, a), _mut_no_conj(b, cd.conj(c)))


def _mut_swap_order(x, y):
    """Formula bug: second component d a + conj(c) b instead of d a + b conj(c)."""
    if len(x) == 1:
        return [x[0] * y[0]]
    h = len(x) // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return cd.sub(_mut_swap_order(a, c), _mut_swap_order(cd.conj(d), b)) + \
        cd.add(_mut_swap_order(d, a), _mut_swap_order(cd.conj(c), b))


def _mut_index(x, y):
    """Index bug: halves of the result swapped whenever the top bit of both inputs is set."""
    r = cd.raw_mul(x, y)
    h = len(r) // 2
    if h and any(x[h:]) and any(y[h:]):
        r = r[h:] + r[:h]
    return r


def _mut_scale(x, y):
    """Scaling bug: the first component is doubled."""
    r = cd.raw_mul(x, y)
    h = len(r) // 2
    return [2 * t for t in r[:h]] + r[h:] if h else r


def _mut_leak(x, y):
    """Leak bug: a stray +1 added to coordinate 0 when the product lands on the top basis element."""
    r = cd.raw_mul(x, y)
    if len(r) > 1 and r[-1] != 0:
        r = list(r)
        r[0] += 1
    return r


MUTANTS = {"sign table: one entry negated": _mut_sign_flip,
           "formula: conj(d) dropped": _mut_no_conj,
           "formula: b conj(c) -> conj(c) b": _mut_swap_order,
           "index: result halves swapped": _mut_index,
           "scale: first half doubled": _mut_scale,
           "leak: stray coefficient": _mut_leak}


def mutants(nwords=3000, seed=1):
    rows = []
    for name, f in MUTANTS.items():
        res = {}
        for strict in (False, True):
            r = fuzz(nwords, seed, f, strict, levels=(2, 3, 4), heavy=(), heavy_words=0)
            res[strict] = r["violations"] / r["words"]
        rows.append((name, res[False], res[True]))
    return rows


def main(argv):
    if not argv or argv[0] == "--fuzz":
        n = int(argv[1]) if len(argv) > 1 else 100_000
        r = fuzz(n)
        print(f"cdcheck fuzz on manifold.cd.mul: {r['words']} words (levels 2-4, lengths 4-8; plus "
              f"2000 words each at levels 5, 6), {r['pentagons']} pentagons, {r['violations']} violations "
              f"-> false-positive rate {r['violations'] / r['words']:.6f}")
        r = fuzz(20_000, seed=7, strict=True, heavy_words=200)
        print(f"strict mode (signs vs fsgn): {r['words']} words, {r['violations']} violations")
    elif argv[0] == "--mutants":
        print(f"{'injected bug':38s} {'caught (pentagon)':>18s} {'caught (strict)':>16s}   (fraction of 3000 fuzzed words)")
        for name, a, b in mutants():
            print(f"{name:38s} {a:18.3f} {b:16.3f}")
    else:
        w = [int(t) for t in argv if not t.startswith("--")]
        r = cdcheck(w, strict="--strict" in argv)
        print(r)
        if not r["ok"]:
            raise SystemExit(1)


if __name__ == "__main__":
    main(sys.argv[1:])
