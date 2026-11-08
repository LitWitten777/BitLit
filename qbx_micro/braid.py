"""The six channels of the resonance machine, in exact or bounded arithmetic.

A braid on n strands is a list of nonzero integers: +i is sigma_i, -i is its
inverse (1 <= i <= n-1).  Words are read left to right.

Channels (Lean source of each fact in brackets; all in `QBX/Formal/MultiProver/`):

  fold        permutation of the strands                      (complete on B_n via Garside, Fold*.lean)
  link        closure components, linking numbers, writhe     (LinkChannel)
  anchor      unreduced Burau matrix, exact over F_p at
              several values of t (a Schwartz-Zippel fingerprint
              of the matrix over Z[t, 1/t])                    (BurauFaithful, anchor channel)
  harmonic    resonance pattern of reduced Burau on |t| = 1   (HarmonicSweep, resonance_iff_trace)
  oscillator  Kauffman bracket / Jones polynomial, exact in
              Z[A, 1/A] (spin-chain Temperley-Lieb model)     (OscillatorChannel, JonesMarkov)
  clifford    rotor product tau(beta) in Cl(0, n), exact:
              tau_k = (1 + c_{k+1} c_k)/sqrt2                  (CliffordChannel: tau_braid, Setup.rep)

Every reading is a function of the braid-group element, so two words with
different readings in any channel are different braids.  The converse is not
claimed: equal readings in the five non-fold channels do not prove equality.

Integrity checks (`integrity`) re-derive facts proved in Lean from the computed
readings; a failure means the computation was corrupted, not that a theorem is
false:
  * Clifford norm   N rev(N) = 2^k              (word_norm: tau tau^dagger = 1)
  * Clifford->fold  N c_j rev(N) = +-2^k c_pi(j) (word_conj, perm_eq_of_word_eq)
  * Clifford parity N is even                     (word_mem_even)
  * Burau det       det = (-t)^writhe            (block [[1-t, t], [1, 0]] has det -t)
  * Burau at t = 1  equals the permutation matrix

Dependency-free; runs under MicroPython (uses only `math` and builtin complex).
"""

import math

from . import cliff


def check_word(n, word):
    for g in word:
        if g == 0 or abs(g) >= n:
            raise ValueError("letter %d out of range for %d strands" % (g, n))


def inverse(word):
    return [-g for g in reversed(word)]


# ----------------------------------------------------------------------------- fold / link

def fold(n, word):
    """pos[p] = strand (initial position, 0-based) at position p at the end."""
    pos = list(range(n))
    for g in word:
        i = abs(g)
        pos[i - 1], pos[i] = pos[i], pos[i - 1]
    return tuple(pos)


def writhe(word):
    return sum(1 if g > 0 else -1 for g in word)


def components(n, word):
    """Component label of each strand: cycles of the closure permutation."""
    pos = fold(n, word)
    nxt = [0] * n  # strand starting at p ends at position q: nxt[p] = q
    for q, s in enumerate(pos):
        nxt[s] = q
    comp = [-1] * n
    c = 0
    for s in range(n):
        if comp[s] < 0:
            x = s
            while comp[x] < 0:
                comp[x] = c
                x = nxt[x]
            c += 1
    return comp, c


def link(n, word):
    """(number of components, linking numbers lk(a,b) for a < b, writhe)."""
    comp, c = components(n, word)
    twice = {}
    pos = list(range(n))
    for g in word:
        i = abs(g)
        a, b = comp[pos[i - 1]], comp[pos[i]]
        if a != b:
            key = (min(a, b), max(a, b))
            twice[key] = twice.get(key, 0) + (1 if g > 0 else -1)
        pos[i - 1], pos[i] = pos[i], pos[i - 1]
    lk = tuple(twice.get((a, b), 0) // 2 for a in range(c) for b in range(a + 1, c))
    return (c, lk, writhe(word))


# ----------------------------------------------------------------------------- anchor (Burau)

P61 = (1 << 61) - 1          # a Mersenne prime
ANCHOR_POINTS = (P61 - 1, 2, 3, 5)   # t = -1, 2, 3, 5 in F_p


def burau_mod(n, word, t, p=P61):
    """Unreduced Burau matrix over F_p at t (row-vector convention, left-to-right).

    sigma_i acts on columns i-1, i by [[1-t, t], [1, 0]], its inverse by
    [[0, 1], [1/t, 1 - 1/t]].  Right multiplication touches two columns only, so
    the cost is O(n) per letter.
    """
    t %= p
    ti = pow(t, p - 2, p)
    m = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    for g in word:
        i = abs(g)
        a, b = i - 1, i
        for row in m:
            x, y = row[a], row[b]
            if g > 0:
                row[a], row[b] = (x * (1 - t) + y) % p, (x * t) % p
            else:
                row[a], row[b] = (y * ti) % p, (x + y * (1 - ti)) % p
    return m


def det_mod(m, p=P61):
    m = [row[:] for row in m]
    n = len(m)
    d = 1
    for c in range(n):
        piv = None
        for r in range(c, n):
            if m[r][c] % p:
                piv = r
                break
        if piv is None:
            return 0
        if piv != c:
            m[c], m[piv] = m[piv], m[c]
            d = -d
        d = d * m[c][c] % p
        inv = pow(m[c][c], p - 2, p)
        for r in range(c + 1, n):
            f = m[r][c] * inv % p
            if f:
                for k in range(c, n):
                    m[r][k] = (m[r][k] - f * m[c][k]) % p
    return d % p


def anchor(n, word, points=ANCHOR_POINTS, p=P61):
    """Burau matrices over F_p at each point, flattened."""
    return tuple(tuple(x for row in burau_mod(n, word, t, p) for x in row) for t in points)


# ----------------------------------------------------------------------------- harmonic

SWEEP = 24


def burau_cyclic(n, word, N=SWEEP):
    """Unreduced Burau matrix over the group ring Z[x]/(x^N - 1), t -> x, exactly.

    t is invertible there (t^-1 = x^(N-1)), so this is a homomorphism of B_n:
    the result depends only on the braid, not on the word.  Each entry is a list
    of N integers; evaluating at x = e^{2 pi i k/N} gives the Burau matrix at
    every point of the harmonic grid at once.
    """
    def rot(v, k):
        k %= N
        return v[-k:] + v[:-k] if k else v[:]

    zero = [0] * N
    one = [1] + [0] * (N - 1)
    m = [[one[:] if r == c else zero[:] for c in range(n)] for r in range(n)]
    for g in word:
        i = abs(g)
        a, b = i - 1, i
        for row in m:
            x, y = row[a], row[b]
            if g > 0:   # (x, y) -> (x (1 - t) + y, x t)
                xt = rot(x, 1)
                row[a] = [x[j] - xt[j] + y[j] for j in range(N)]
                row[b] = xt
            else:       # (x, y) -> (y t^-1, x + y (1 - t^-1))
                yti = rot(y, -1)
                row[a] = yti
                row[b] = [x[j] + y[j] - yti[j] for j in range(N)]
    return m


def _bits(m):
    big = 0
    for row in m:
        for v in row:
            for c in v:
                if c:
                    big = max(big, cliff.bitlen(abs(c)))
    return big


def evaluate_cyclic(m, k, N=SWEEP, shift=0):
    """The exact matrix at x = e^{2 pi i k / N}, divided by 2^shift (deterministic)."""
    tab = [complex(math.cos(2 * math.pi * j * k / N), math.sin(2 * math.pi * j * k / N))
           for j in range(N)]
    out = []
    for row in m:
        r = []
        for v in row:
            z = 0j
            for j in range(N):
                c = v[j]
                if c:
                    z += (c >> shift if c >= 0 else -((-c) >> shift)) * tab[j]
            r.append(z)
        out.append(r)
    return out


def charpoly(m):
    """Coefficients c_0..c_n (c_n = 1) of det(x I - m), Faddeev-LeVerrier."""
    n = len(m)
    coeffs = [0j] * (n + 1)
    coeffs[n] = 1
    mk = [[0j] * n for _ in range(n)]
    for k in range(1, n + 1):
        prev = [row[:] for row in mk]
        for i in range(n):
            prev[i][i] += coeffs[n - k + 1]
        mk = [[sum(m[i][l] * prev[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        tr = sum(mk[i][i] for i in range(n))
        coeffs[n - k] = -tr / k
    return coeffs


def roots(coeffs, iters=400):
    """All roots of a monic polynomial (Durand-Kerner)."""
    n = len(coeffs) - 1
    if n == 0:
        return []
    z = [complex(0.4, 0.9) ** k for k in range(n)]

    def ev(x):
        v = 0j
        for c in reversed(coeffs):
            v = v * x + c
        return v

    for _ in range(iters):
        nz = []
        for i in range(n):
            den = 1 + 0j
            for j in range(n):
                if j != i:
                    den *= z[i] - z[j]
            nz.append(z[i] - ev(z[i]) / den if den != 0 else z[i] + 1e-9)
        z = nz
    return z


def deflate_one(coeffs):
    """Divide a monic polynomial by (x - 1) (synthetic division)."""
    n = len(coeffs) - 1
    out = [0j] * n
    acc = 0j
    for k in range(n, 0, -1):
        acc = coeffs[k] + acc
        out[k - 1] = acc
    return out


def max_entry(m):
    return max(abs(z) for row in m for z in row)


def _resonant_matrix(n, mk, tol=1e-7, bound=1e8):
    if max_entry(mk) > bound:
        return None
    if n == 3:
        return abs(mk[0][0] + mk[1][1] + mk[2][2] - 1) <= 2 + 1e-9
    return any(abs(abs(z) - 1) < tol for z in roots(deflate_one(charpoly(mk))))


def harmonic(n, word, points=SWEEP):
    """Resonance pattern on theta_k = 2 pi k / points: does reduced Burau at
    t = e^{i theta_k} have an eigenvalue on |z| = 1?

    Computed from the exact matrix `burau_cyclic`, so the pattern is a function
    of the braid (not of the word or of rounding along it).  The unreduced
    matrix is reduced Burau plus a trivial summand (eigenvalue 1), which is
    divided out; for n = 3 the trace criterion |tr| <= 2 (`resonance_iff_trace`)
    is used.  An entry above 1e8 gives None: double precision cannot then
    decide modulus exactly 1.  Only k <= points/2 is computed; the pattern is
    symmetric (`two_pi_sub_mem_resonanceSet`).
    """
    if n < 2:
        return tuple(False for _ in range(points))
    m = burau_cyclic(n, word, points)
    if _bits(m) > 900:
        return tuple(None for _ in range(points))
    half = [_resonant_matrix(n, evaluate_cyclic(m, k, points)) for k in range(points // 2 + 1)]
    return tuple(half[k] if k <= points // 2 else half[points - k] for k in range(points))


def resonant(n, word, theta_index, points=SWEEP):
    """Resonance at the single grid point theta = 2 pi theta_index / points."""
    return harmonic(n, word, points)[theta_index % points]


def entropy_bound(n, word, points=SWEEP):
    """max over the grid of log(spectral radius of reduced Burau at |t| = 1).

    The Burau estimate (Kolev; Band-Boyland) says this is a lower bound for the
    topological entropy of the braid's mapping class.  The bound is not
    formalised in this project; it is reported as a complexity score.  Computed
    from the exact matrix, renormalised by a power of two before the floating
    point eigenvalue step, so long words do not overflow.
    """
    if n < 2:
        return 0.0
    m = burau_cyclic(n, word, points)
    shift = max(0, _bits(m) - 60)
    best = 0.0
    for k in range(1, points // 2 + 1):
        mk = evaluate_cyclic(m, k, points, shift)
        b = max_entry(mk)
        if b == 0:
            continue
        mk = [[z / b for z in row] for row in mk]
        r = max([abs(z) for z in roots(charpoly(mk))] or [1.0]) * b
        if r > 0:
            best = max(best, math.log(r) + shift * math.log(2))
    return best


# ----------------------------------------------------------------------------- oscillator (exact)

def _padd(x, y, s=1):
    out = dict(x)
    for k, v in y.items():
        out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}


def _pshift(x, e, c=1):
    return {k + e: c * v for k, v in x.items()}


def kauffman_bracket(n, word):
    """<closure> in Z[A, 1/A] as {exponent: coefficient}, with <O> = d = -A^2 - A^-2.

    Spin-chain model: sigma_i -> A + A^{-1} e_i, e_i acts on sites i-1, i by
    e|01> = q|01> - |10>, e|10> = -|01> + q^{-1}|10>, q = -A^2; the Markov
    weight is h = diag(q, q^{-1}) per site.  Cost 4^n * len: small n only.
    """
    dim = 1 << n
    total = {}
    for basis in range(dim):
        vec = {basis: {0: 1}}
        for g in reversed(word):
            i = abs(g)
            a_exp, b_exp = (1, -1) if g > 0 else (-1, 1)   # coefficient of 1 and of e
            lo, hi = 1 << (i - 1), 1 << i
            new = {}
            for s, poly in vec.items():
                new[s] = _padd(new.get(s, {}), _pshift(poly, a_exp))
                bl, bh = bool(s & lo), bool(s & hi)
                if bl != bh:
                    sw = s ^ lo ^ hi
                    # site i-1 is the low bit; |ab> means (site i-1, site i) = (a, b)
                    if bh:   # state |0 1> (low 0, high 1): e -> q|01> - |10>, q = -A^2
                        new[s] = _padd(new.get(s, {}), _pshift(poly, b_exp + 2, -1))
                        new[sw] = _padd(new.get(sw, {}), _pshift(poly, b_exp, -1))
                    else:    # state |1 0>: e -> -|01> + q^{-1}|10>, q^{-1} = -A^{-2}
                        new[sw] = _padd(new.get(sw, {}), _pshift(poly, b_exp, -1))
                        new[s] = _padd(new.get(s, {}), _pshift(poly, b_exp - 2, -1))
            vec = {k: v for k, v in new.items() if v}
        diag = vec.get(basis)
        if diag:
            # weight prod over sites: q = -A^2 for a 0 site, q^{-1} = -A^{-2} for a 1 site
            ones = cliff.popcount(basis)
            zeros = n - ones
            sign = -1 if (n & 1) else 1
            total = _padd(total, _pshift(diag, 2 * zeros - 2 * ones, sign))
    return total


def jones(n, word):
    """Jones polynomial of the closure in powers of A, normalised to V(unknot) = 1.

    V = (-A^3)^{-w} <closure> / d; substitute t = A^{-4} (see `jones_in_t`).
    """
    br = kauffman_bracket(n, word)
    w = writhe(word)
    return _pdiv_d(_pshift(br, -3 * w, -1 if (w & 1) else 1))


def _pdiv_d(v):
    """Exact division by d = -(A^2 + A^-2); raises if the remainder is nonzero."""
    v = dict(v)
    if not v:
        return {}
    floor = min(v)
    out = {}
    while v:
        top = max(v)
        if top - 2 < floor + 2 - 4:
            raise ValueError("not divisible by d")
        c = v[top]
        e = top - 2
        out[e] = -c
        # subtract (-c A^e) * (-(A^2 + A^-2)) = c A^(e+2) + c A^(e-2)
        v = _padd(v, {e + 2: c, e - 2: c}, -1)
        if v and min(v) < floor:
            raise ValueError("not divisible by d")
    return {k: c for k, c in out.items() if c}


def jones_in_t(n, word):
    """Jones polynomial as {exponent of t: coefficient}.  Exponents are
    half-integers for links with an even number of components; those are
    returned as floats, integral exponents as ints."""
    out = {}
    for k, c in jones(n, word).items():
        e = -k / 4
        out[int(e) if e == int(e) else e] = c
    return out


def osc_A(r):
    """A = e^{i pi (r+1) / (2r)}, so that A^2 = -q with q = e^{i pi / r}: the
    convention t^(1/2) = -1/q of `qbx_ir.quantum.representation.jones_from_quantum_trace`."""
    th = math.pi * (r + 1) / (2 * r)
    return complex(math.cos(th), math.sin(th))


def jones_at(n, word, r):
    """Jones value at q = e^{i pi / r} (convention A^2 = -q, see `osc_A`)."""
    a = osc_A(r)
    return sum(c * a ** k for k, c in jones(n, word).items())


def bracket_at(n, word, a):
    """The Kauffman bracket evaluated at a complex number A (same model as
    `kauffman_bracket`, scalar arithmetic: cost 4^n * len, no polynomial growth)."""
    q, qi = -a * a, -1 / (a * a)
    ai = 1 / a
    dim = 1 << n
    total = 0j
    for basis in range(dim):
        vec = {basis: 1 + 0j}
        for g in reversed(word):
            i = abs(g)
            c1, ce = (a, ai) if g > 0 else (ai, a)
            lo, hi = 1 << (i - 1), 1 << i
            new = {}
            for s, z in vec.items():
                new[s] = new.get(s, 0j) + c1 * z
                if bool(s & lo) != bool(s & hi):
                    sw = s ^ lo ^ hi
                    if s & hi:
                        new[s] = new.get(s, 0j) + ce * q * z
                    else:
                        new[s] = new.get(s, 0j) + ce * qi * z
                    new[sw] = new.get(sw, 0j) - ce * z
            vec = new
        z = vec.get(basis, 0j)
        ones = cliff.popcount(basis)
        total += z * q ** (n - ones) * qi ** ones
    return total


def jones_numeric(n, word, r):
    """Jones value at q = e^{i pi / r} (A^2 = -q) without building the polynomial."""
    a = osc_A(r)
    d = -a * a - 1 / (a * a)
    w = writhe(word)
    return (-a ** 3) ** (-w) * bracket_at(n, word, a) / d


P_OSC = 2305843009213690801   # prime, p = 1 (mod 840): contains 4r-th roots of unity for r = 3, 5, 6, 7


def _prime_factors(m):
    out, d = [], 2
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        out.append(m)
    return out


def root_of_unity_mod(order, p=P_OSC):
    """The first primitive `order`-th root of unity in F_p, searching h = 2, 3, ..."""
    if (p - 1) % order:
        raise ValueError("F_p has no primitive %d-th root of unity" % order)
    qs = _prime_factors(order)
    h = 2
    while True:
        w = pow(h, (p - 1) // order, p)
        if all(pow(w, order // q, p) != 1 for q in qs):
            return w
        h += 1


def oscillator_mod(n, word, r, p=P_OSC):
    """Image of d * V(closure) under a ring map Z[zeta_{4r}] -> F_p.

    In the complex picture A = zeta^(r+1) with zeta = e^{i pi/(2r)}, so A^2 = -q,
    q = e^{i pi/r} (the convention of `jones_at`).  (-A^3)^{-w} <closure> = d V
    lies in Z[zeta_{4r}]; this function computes its image under the ring
    homomorphism sending zeta to a primitive 4r-th root of unity omega in F_p,
    exactly (no rounding).  Equal braids give equal values; different values
    prove that the closures differ.
    """
    a = pow(root_of_unity_mod(4 * r, p), r + 1, p)
    ai = pow(a, p - 2, p)
    q, qi = (-a * a) % p, (-ai * ai) % p
    dim = 1 << n
    total = 0
    for basis in range(dim):
        vec = {basis: 1}
        for g in reversed(word):
            i = abs(g)
            c1, ce = (a, ai) if g > 0 else (ai, a)
            lo, hi = 1 << (i - 1), 1 << i
            new = {}
            for s, z in vec.items():
                new[s] = (new.get(s, 0) + c1 * z) % p
                if bool(s & lo) != bool(s & hi):
                    sw = s ^ lo ^ hi
                    new[s] = (new[s] + ce * (q if s & hi else qi) * z) % p
                    new[sw] = (new.get(sw, 0) - ce * z) % p
            vec = new
        z = vec.get(basis, 0)
        ones = cliff.popcount(basis)
        total = (total + z * pow(q, n - ones, p) * pow(qi, ones, p)) % p
    w = writhe(word)
    m3 = (-pow(a, 3, p)) % p
    return total * pow(m3, (-w) % (p - 1), p) % p


# ----------------------------------------------------------------------------- clifford

def _sig(n):
    return tuple([-1] * n)


def clifford(n, word):
    """(N, k) with tau(beta) = N / sqrt2^k in Cl(0, n), N integral, k minimal.

    tau_k = (1 + c_{k+1} c_k)/sqrt2 and tau_k^{-1} = (1 - c_{k+1} c_k)/sqrt2.
    Canonical: since sqrt2 is irrational, N / sqrt2^k = N' / sqrt2^k' with
    k, k' minimal forces k = k' and N = N'.
    """
    sig = _sig(n)
    num = {0: 1}
    for g in word:
        i = abs(g)
        _, mask = cliff.blade_product(1 << i, 1 << (i - 1), sig)
        s, _ = cliff.blade_product(1 << i, 1 << (i - 1), sig)
        if g < 0:
            s = -s
        num = cliff.add(num, cliff.gp(num, {mask: s}, sig))
    k = len(word)
    while k >= 2 and num and all(v % 2 == 0 for v in num.values()):
        num = {m: v // 2 for m, v in num.items()}
        k -= 2
    return num, k


def clifford_key(n, word):
    num, k = clifford(n, word)
    return (k, tuple(sorted(num.items())))


# ----------------------------------------------------------------------------- integrity

def integrity(n, word):
    """Re-derive Lean-proved identities from the readings; dict name -> bool."""
    sig = _sig(n)
    out = {}
    num, k = clifford(n, word)
    norm = cliff.gp(num, cliff.reverse(num), sig)
    out["clifford_norm"] = norm == {0: 1 << k}
    out["clifford_even"] = cliff.is_even(num)
    pos = fold(n, word)
    ok = True
    for j in range(n):
        conj = cliff.gp(cliff.gp(num, cliff.gen(j), sig), cliff.reverse(num), sig)
        if len(conj) != 1:
            ok = False
            break
        (mask, c), = conj.items()
        if abs(c) != 1 << k or cliff.popcount(mask) != 1:
            ok = False
            break
        # R c_j R^dagger = +-2^k c_pos[j]: the rightmost letter acts first, so the
        # generator index follows the fold reading `pos` itself.
        if pos[j] != cliff.bitlen(mask) - 1:
            ok = False
            break
    out["clifford_fold"] = ok
    w = writhe(word)
    good = True
    for t in (2, 3, 5):
        d = det_mod(burau_mod(n, word, t))
        expect = pow((-t) % P61, w % (P61 - 1), P61)
        good = good and d == expect
    out["burau_det"] = good
    m1 = burau_mod(n, word, 1)
    perm_ok = all(m1[r][c] == (1 if pos[c] == r else 0) for r in range(n) for c in range(n))
    if not perm_ok:
        perm_ok = all(m1[r][c] == (1 if pos[r] == c else 0) for r in range(n) for c in range(n))
    out["burau_perm"] = perm_ok
    return out


def reading(n, word, oscillator=True):
    """All six readings (oscillator exact only when `oscillator` and n small)."""
    check_word(n, word)
    out = {
        "fold": fold(n, word),
        "link": link(n, word),
        "anchor": anchor(n, word),
        "harmonic": harmonic(n, word),
        "clifford": clifford_key(n, word),
    }
    if oscillator:
        out["oscillator"] = tuple(sorted(jones(n, word).items()))
    return out
