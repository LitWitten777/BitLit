"""Hash rounds II: several cocycles, sliding windows, error correction, shortcuts.

    python3 -m hypercube.hashrounds2 run [--quick]     all tests, report to stdout
    python3 -m hypercube.hashrounds2 C1                one test (C1..C4, W1, W2, E1..E3, S1..S4)

Plan, predictions and decision rules: docs/PREREG_HASH_ROUNDS_II_2026-10-25.md (committed before the
first run).  Proved counterparts: RequestProject/HashRoundsCocycle.lean,
RequestProject/HashRoundsShortcut.lean, RequestProject/HashRoundsCodes.lean.

Needs numpy.  Reuses the CD product and exact linear algebra of hypercube/hashrounds.py.
"""

import hashlib
import math
import random
import sys
import time

import numpy as np

from . import erase
from .hashrounds import cmul, cconj, norm2, rank_mod, solve_mod, right_mult_matrix, P61
from .mirror import LABEL
from .store_heal import CODE, heal

SEED = 20261025


def say(*a):
    print(*a, flush=True)


def obj(v):
    return np.array([int(t) for t in v], dtype=object)


# ----------------------------------------------------------------------------------------------
# twisted products e_a e_b = psi(a, b) e_(a xor b)
# ----------------------------------------------------------------------------------------------

def tmul(psi, x, y):
    """Twisted product on the last axis (broadcasting); psi is an N x N array of +-1."""
    N = psi.shape[0]
    idx = np.arange(N)
    shape = np.broadcast_shapes(x.shape, y.shape)
    out = np.zeros(shape, dtype=object if (x.dtype == object or y.dtype == object) else np.int64)
    for i in range(N):
        out[..., i ^ idx] += psi[i].astype(out.dtype) * x[..., i:i + 1] * y
    return out


def psi_cd(n):
    N = 2 ** n
    E = np.eye(N, dtype=np.int64)
    T = np.zeros((N, N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            v = cmul(E[i], E[j])
            T[i, j] = v[i ^ j]
            assert abs(T[i, j]) == 1 and np.count_nonzero(v) == 1
    return T


def psi_cliff(n):
    N = 2 ** n
    T = np.zeros((N, N), dtype=np.int64)
    for a in range(N):
        for b in range(N):
            s = sum(1 for i in range(n) for j in range(n) if i > j and (a >> i) & 1 and (b >> j) & 1)
            s += bin(a & b).count("1")
            T[a, b] = -1 if s % 2 else 1
    return T


def psi_triv(n):
    return np.ones((2 ** n, 2 ** n), dtype=np.int64)


def rand_gauge(n, rng):
    f = np.array([1] + [rng.choice((-1, 1)) for _ in range(2 ** n - 1)], dtype=np.int64)
    return f


def gauged(psi, f):
    N = psi.shape[0]
    idx = np.arange(N)
    return psi * f[:, None] * f[None, :] * f[idx[:, None] ^ idx[None, :]]


def psi_rand(n, rng):
    N = 2 ** n
    T = np.array([[rng.choice((-1, 1)) for _ in range(N)] for _ in range(N)], dtype=np.int64)
    T[0, :] = 1
    T[:, 0] = 1
    return T


def cochains(n):
    rng = random.Random(SEED + n)
    cd_ = psi_cd(n)
    f = rand_gauge(n, rng)
    return {"TRIV": psi_triv(n), "CLIFF": psi_cliff(n), "CD": cd_, "CDg": gauged(cd_, f),
            "RAND": psi_rand(n, rng)}, f


def assoc_phase(psi):
    N = psi.shape[0]
    a, b, c = np.meshgrid(np.arange(N), np.arange(N), np.arange(N), indexing="ij")
    return psi[a, b] * psi[a ^ b, c] * psi[b, c] * psi[a, b ^ c]


def tright_matrix(psi, k):
    """M with M @ x = x ._psi k."""
    N = psi.shape[0]
    E = np.eye(N, dtype=object)
    return np.array([tmul(psi, E[j], k) for j in range(N)], dtype=object).T


# ----------------------------------------------------------------------------------------------
# Angle 1: several cocycles
# ----------------------------------------------------------------------------------------------

def C1(quick=False):
    say("== C1  associator census and pentagon, five cochains, n = 2..5")
    rng = random.Random(SEED)
    out = {}
    say("   n   cochain  frac(w=-1)   prediction                 pentagon checks  violations")
    for n in range(2, 6):
        N = 2 ** n
        chains, _ = cochains(n)
        for name, psi in chains.items():
            w = assoc_phase(psi)
            frac = float((w == -1).mean())
            if n <= 4 and not quick:
                A, B, C, D = np.meshgrid(*(np.arange(N),) * 4, indexing="ij")
                A, B, C, D = A.ravel(), B.ravel(), C.ravel(), D.ravel()
            else:
                m = 20000 if not quick else 2000
                A, B, C, D = (np.array([rng.randrange(N) for _ in range(m)]) for _ in range(4))
            p = w[B, C, D] * w[A ^ B, C, D] * w[A, B ^ C, D] * w[A, B, C ^ D] * w[A, B, C]
            viol = int((p != 1).sum())
            pred = {"TRIV": "0", "CLIFF": "0", "RAND": f"{0.5 * ((N - 1) / N) ** 3:.3f} +- 0.05"}.get(
                name, {2: "0", 3: f"{168 / 512:.4f}"}.get(n, "> 0"))
            say(f"   {n}   {name:6s}   {frac:.4f}      {pred:24s}   {len(A):8d}        {viol}")
            out[(n, name)] = (frac, viol)
    for n in range(2, 6):
        assert out[(n, "CD")][0] == out[(n, "CDg")][0]
    return out


def C2(quick=False):
    say("== C2  gauge equivalence through 8 rounds (n = 4): H_CDg(D_f x; D_f k) = D_f H_CD(x; k)")
    rng = random.Random(SEED)
    trials = 40 if quick else 200
    n, N = 4, 16
    psi = psi_cd(n)
    ident = rank_eq = 0
    for _ in range(trials):
        f = rand_gauge(n, rng)
        psig = gauged(psi, f)
        x = obj([rng.randint(-3, 3) for _ in range(N)])
        ks = []
        while len(ks) < 8:
            k = obj([rng.randint(-3, 3) for _ in range(N)])
            if any(k):
                ks.append(k)
        fo = f.astype(object)
        y, yg = x, fo * x
        M, Mg = np.eye(N, dtype=object), np.eye(N, dtype=object)
        for k in ks:
            y = tmul(psi, y, k)
            yg = tmul(psig, yg, fo * k)
            M = tright_matrix(psi, k).dot(M)
            Mg = tright_matrix(psig, fo * k).dot(Mg)
        ident += list(yg) == list(fo * y)
        rank_eq += rank_mod(M.tolist()) == rank_mod(Mg.tolist())
    say(f"   identity exact: {ident}/{trials};  equal ranks: {rank_eq}/{trials}")
    return {"identity": (ident, trials), "rank": (rank_eq, trials)}


def C3(quick=False):
    say("== C3  8 rounds x -> x ._psi k per cochain: full rank, combined-key real-part leak")
    rng = random.Random(SEED)
    trials = 40 if quick else 200
    out = {}
    say("   n   cochain  full-rank   combined-key Re leak")
    for n in (2, 3, 4):
        N = 2 ** n
        chains, _ = cochains(n)
        for name, psi in chains.items():
            fr = lk = 0
            for _ in range(trials):
                ks = []
                while len(ks) < 8:
                    k = obj([rng.randint(-3, 3) for _ in range(N)])
                    if any(k):
                        ks.append(k)
                M = np.eye(N, dtype=object)
                for k in ks:
                    M = tright_matrix(psi, k).dot(M)
                fr += rank_mod(M.tolist()) == N
                K = ks[-1]
                for k in reversed(ks[:-1]):
                    K = tmul(psi, k, K)
                good = True
                for _ in range(4):
                    x = obj([rng.randint(-3, 3) for _ in range(N)])
                    y = x
                    for k in ks:
                        y = tmul(psi, y, k)
                    good &= y[0] == tmul(psi, x, K)[0]
                lk += good
            out[(n, name)] = (fr / trials, lk / trials)
            say(f"   {n}   {name:6s}   {fr:3d}/{trials}     {lk:3d}/{trials}")
    return out


def C4(quick=False):
    say("== C4  two cocycle views of one zero-divisor key (n = 4, the 84 census elements)")
    chains, _ = cochains(4)
    res = {nm: [] for nm in ("CLIFF", "CDg", "RAND")}
    base = []
    for i in range(84):
        k = obj(erase.zd(i)[0])
        Mcd = tright_matrix(chains["CD"], k)
        assert Mcd.tolist() == right_mult_matrix(list(k)).tolist()
        base.append(rank_mod(Mcd.tolist()))
        for nm in res:
            M2 = tright_matrix(chains[nm], k)
            res[nm].append((rank_mod(M2.tolist()), rank_mod(np.vstack([Mcd, M2]).tolist())))
    hist = lambda v: dict(sorted({r: v.count(r) for r in set(v)}.items()))
    say(f"   CD rank of x -> x k: {hist(base)}")
    for nm, v in res.items():
        say(f"   second view {nm:5s}: own rank {hist([a for a, _ in v])}; stacked rank {hist([b for _, b in v])}")
    return {"CD": base, **res}


# ----------------------------------------------------------------------------------------------
# Angle 2: sliding windows
# ----------------------------------------------------------------------------------------------

def W1(quick=False):
    say("== W1  rolling-window product: P_(t+1) = (conj(x_t) P_t) x_(t+w) / |x_t|^2 vs recompute")
    rng = random.Random(SEED)
    streams = 25 if quick else 100
    L = 40
    out = {}
    say("   n   w=2      w=3      w=4      (streams with every update exact)")
    for n in range(0, 6):
        N = 2 ** n
        row = []
        for w in (2, 3, 4):
            ok = 0
            for _ in range(streams):
                xs = []
                while len(xs) < L:
                    v = obj([rng.randint(-3, 3) for _ in range(N)])
                    if any(v):
                        xs.append(v)

                def prod(t):
                    P = xs[t]
                    for j in range(1, w):
                        P = cmul(P, xs[t + j])
                    return P
                P = prod(0)
                good = True
                for t in range(L - w):
                    q = cmul(cconj(xs[t]), P)
                    nn = int(norm2(xs[t]))
                    if any(int(v) % nn for v in q):
                        good = False
                        break
                    P = cmul(obj([int(v) // nn for v in q]), xs[t + w])
                    if list(P) != list(prod(t + 1)):
                        good = False
                        break
                ok += good
            row.append(ok)
        out[n] = row
        say(f"   {n}   " + "   ".join(f"{v:3d}/{streams}" for v in row))
    return out


def inv_mod256(M):
    n = len(M)
    A = [[int(v) % 256 for v in row] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c] % 2), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        iv = pow(A[c][c], -1, 256)
        A[c] = [v * iv % 256 for v in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]
                A[i] = [(u - f * v) % 256 for u, v in zip(A[i], A[c])]
    return np.array([row[n:] for row in A], dtype=np.int64)


def W2(quick=False):
    say("== W2  causal sliding-window sedenion hash mod 256: y_t = sum_(j<4) x_(t-j) c_j")
    rng = np.random.default_rng(SEED)
    streams = 40 if quick else 200
    L, w = 32, 4
    out = {}
    for parity in ("odd", "even"):
        rec = inc = 0
        for _ in range(streams):
            c = rng.integers(0, 256, (w, 16)).astype(np.int64)
            if (int((c[0] * c[0]).sum()) % 2 == 1) != (parity == "odd"):
                c[0, 0] ^= 1
            X = rng.integers(0, 256, (L, 16)).astype(np.int64)

            def hash_all(X):
                Y = np.zeros_like(X)
                for t in range(L):
                    for j in range(w):
                        if t - j >= 0:
                            Y[t] = (Y[t] + cmul(X[t - j], c[j])) % 256
                return Y
            Y = hash_all(X)
            R0 = right_mult_matrix(list(c[0]))           # x c0 = R0 @ x
            Rinv = inv_mod256(R0.tolist())
            ok = Rinv is not None
            if ok:
                Z = np.zeros_like(X)
                for t in range(L):
                    rhs = Y[t].copy()
                    for j in range(1, w):
                        if t - j >= 0:
                            rhs = (rhs - cmul(Z[t - j], c[j])) % 256
                    Z[t] = Rinv.dot(rhs) % 256
                ok = bool((Z == X).all())
            rec += ok
            # incremental: change x_s, recompute only y_s .. y_(s+3)
            s = int(rng.integers(0, L))
            X2 = X.copy()
            X2[s] = rng.integers(0, 256, 16)
            Y2 = Y.copy()
            for t in range(s, min(L, s + w)):
                Y2[t] = 0
                for j in range(w):
                    if t - j >= 0:
                        Y2[t] = (Y2[t] + cmul(X2[t - j], c[j])) % 256
            inc += bool((Y2 == hash_all(X2)).all())
        out[parity] = (rec, inc, streams)
        say(f"   c0 {parity:4s} norm: causal decoder exact {rec}/{streams};  incremental = full {inc}/{streams}")
    return out


# ----------------------------------------------------------------------------------------------
# Angle 3: error correction
# ----------------------------------------------------------------------------------------------

def solve_any_mod(A, b, p=P61):
    """Some solution of A x = b mod p (free variables 0), or None if inconsistent."""
    rows, cols = len(A), len(A[0])
    M = [[int(v) % p for v in row] + [int(bb) % p] for row, bb in zip(A, b)]
    piv_cols, r = [], 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = pow(M[r][c], p - 2, p)
        M[r] = [v * iv % p for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(u - f * v) % p for u, v in zip(M[i], M[r])]
        piv_cols.append(c)
        r += 1
    if any(M[i][cols] for i in range(r, rows)):
        return None
    x = [0] * cols
    for i, c in enumerate(piv_cols):
        x[c] = M[i][cols]
    return x


def interp(xs, ys, k, p=P61):
    """Coefficients (degree < k) through k points."""
    A = [[pow(x, j, p) for j in range(k)] for x in xs]
    return solve_mod(A, ys, p)


def polydiv(num, den, p=P61):
    num = num[:]
    out = [0] * max(1, len(num) - len(den) + 1)
    iv = pow(den[-1], p - 2, p)
    for i in range(len(num) - len(den), -1, -1):
        q = num[i + len(den) - 1] * iv % p
        out[i] = q
        for j, d in enumerate(den):
            num[i + j] = (num[i + j] - q * d) % p
    return out, num[:len(den) - 1]


def berlekamp_welch(xs, ys, k, e, p=P61):
    """Message polynomial (k coefficients) or None."""
    A, b = [], []
    for x, y in zip(xs, ys):
        row = [(-y * pow(x, j, p)) % p for j in range(e)] + [pow(x, j, p) for j in range(k + e)]
        A.append(row)
        b.append(y * pow(x, e, p) % p)
    sol = solve_any_mod(A, b, p)
    if sol is None:
        return None
    E = sol[:e] + [1]
    Q = sol[e:]
    P, rem = polydiv(Q, E, p)
    if any(rem) or any(P[k:]):
        return None
    return (P + [0] * k)[:k]


def E1(quick=False):
    say("== E1  polynomial-coded linear rounds over GF(p): k = 4 inputs, n = 12 workers")
    rng = random.Random(SEED)
    trials = 30 if quick else 200
    k, nw, p = 4, 12, P61
    pts = list(range(1, nw + 1))
    out = {}
    cases = [("level 2", 2, False), ("level 3", 3, False), ("level 4", 4, False), ("level 4, zero-divisor first round", 4, True)]
    say("   case                               erasures(8)  e=0  e=1  e=2  e=3  e=4  e=5   recover X")
    for name, n, zd in cases:
        N = 2 ** n
        er_ok, X_ok = 0, 0
        e_ok = [0] * 6
        for _ in range(trials):
            ks = []
            if zd:
                ks.append(list(erase.zd(rng.randrange(84))[0]))
            while len(ks) < 8:
                kk = [rng.randint(-3, 3) for _ in range(N)]
                if any(kk):
                    ks.append(kk)
            M = np.eye(N, dtype=object)
            for kk in ks:
                M = right_mult_matrix(kk).dot(M)
            Mi = [[int(v) % p for v in row] for row in M.tolist()]
            X = [[rng.randrange(p) for _ in range(N)] for _ in range(k)]
            MX = [[sum(a * b for a, b in zip(row, Xj)) % p for row in Mi] for Xj in X]
            share = [[sum(X[j][c] * pow(z, j, p) for j in range(k)) % p for c in range(N)] for z in pts]
            resp = [[sum(a * b for a, b in zip(row, s)) % p for row in Mi] for s in share]
            # (a) erasures: keep 4 random workers
            keep = rng.sample(range(nw), k)
            dec = [interp([pts[i] for i in keep], [resp[i][c] for i in keep], k) for c in range(N)]
            er_ok += all(dec[c][j] == MX[j][c] for c in range(N) for j in range(k))
            # (b) errors
            for e in range(6):
                bad = set(rng.sample(range(nw), e))
                rr = [[rng.randrange(p) for _ in range(N)] if i in bad else resp[i] for i in range(nw)]
                good = True
                for c in range(N):
                    P = berlekamp_welch(pts, [rr[i][c] for i in range(nw)], k, (nw - k) // 2)
                    if P is None or any(P[j] != MX[j][c] for j in range(k)):
                        good = False
                        break
                e_ok[e] += good
            # (c) recover X itself from M X
            X_ok += all(solve_mod(Mi, MX[j]) == X[j] for j in range(k))
        out[name] = (er_ok, e_ok, X_ok, trials)
        say(f"   {name:34s} {er_ok:4d}/{trials}   " + " ".join(f"{v:4d}" for v in e_ok) + f"   {X_ok:4d}/{trials}")
    return out


def store_word(v):
    w = 0
    for r in range(9):
        w |= CODE[LABEL[r][v]] << (6 * r)
    return w


def pair_decode(a, b, r=0, s=1):
    for u in range(64):
        if LABEL[r][u] == a and LABEL[s][u] == b:
            return u
    return 0


def E2(quick=False):
    say("== E2  the 9-shard store under many flips: minimum distance, ML vs pair decoding")
    W = [store_word(v) for v in range(64)]
    dm = {}
    for m in range(2, 10):
        mask = (1 << (6 * m)) - 1
        dm[m] = min(bin((W[v] ^ W[u]) & mask).count("1") for v in range(64) for u in range(v))
    say("   minimum distance d_m (first m shards): " + ", ".join(f"m={m}: {d}" for m, d in dm.items())
        + "   (prediction >= 3(m-1))")
    rng = random.Random(SEED)
    reps = 400 if quick else 2000
    rows = []
    say("   t   ML (9 shards)   pair decoder (shards 0,1)")
    for t in range(0, 17):
        ml = pr = 0
        for _ in range(reps):
            v = rng.randrange(64)
            err = 0
            for pos in rng.sample(range(54), t):
                err |= 1 << pos
            y = W[v] ^ err
            best = min(range(64), key=lambda u: (bin(W[u] ^ y).count("1"), u))
            ml += best == v
            pr += pair_decode(heal(y & 63), heal((y >> 6) & 63)) == v
        rows.append((t, ml, pr))
        say(f"   {t:2d}  {ml:5d}/{reps}      {pr:5d}/{reps}")
    return {"dm": dm, "rows": rows, "reps": reps}


G1, G2 = 0b111, 0b101


def conv_encode(bits):
    s, out = 0, []
    for u in bits + [0, 0]:
        reg = (u << 2) | s
        out.append(bin(reg & G1).count("1") & 1)
        out.append(bin(reg & G2).count("1") & 1)
        s = reg >> 1
    return out


def viterbi(rx, nbits):
    INF = 10 ** 9
    metric = [0, INF, INF, INF]
    paths = [[], None, None, None]
    T = nbits + 2
    for t in range(T):
        new_m = [INF] * 4
        new_p = [None] * 4
        for s in range(4):
            if metric[s] >= INF:
                continue
            for u in ((0, 1) if t < nbits else (0,)):
                reg = (u << 2) | s
                o1 = bin(reg & G1).count("1") & 1
                o2 = bin(reg & G2).count("1") & 1
                ns = reg >> 1
                m = metric[s] + (o1 != rx[2 * t]) + (o2 != rx[2 * t + 1])
                if m < new_m[ns]:
                    new_m[ns] = m
                    new_p[ns] = paths[s] + [u]
        metric, paths = new_m, new_p
    return paths[0][:nbits]


def E3(quick=False):
    say("== E3  rate-1/2 convolutional code (7,5), window 3, Viterbi; 64-bit messages, 132-bit codewords")
    rng = random.Random(SEED)
    nb = 64
    L = 2 * (nb + 2)
    out = {}
    pats = {1: [(i,) for i in range(L)], 2: [(i, j) for i in range(L) for j in range(i)]}
    if quick:
        pats[2] = pats[2][::10]
    m3 = 2000 if quick else 20000
    pats[3] = [tuple(rng.sample(range(L), 3)) for _ in range(m3)]
    for wgt, plist in pats.items():
        fail = 0
        for pat in plist:
            msg = [rng.randrange(2) for _ in range(nb)]
            cw = conv_encode(msg)
            for i in pat:
                cw[i] ^= 1
            fail += viterbi(cw, nb) != msg
        out[wgt] = (fail, len(plist))
        say(f"   weight {wgt}: {fail} failures / {len(plist)} patterns" + (" (exhaustive)" if wgt < 3 and not quick else ""))
    return out


# ----------------------------------------------------------------------------------------------
# Angle 4: shortcuts
# ----------------------------------------------------------------------------------------------

def S1(quick=False):
    say("== S1  same key r times: replay vs closed form a_r (x k) + b_r x")
    rng = random.Random(SEED)
    trials = 40 if quick else 200
    rs = (2, 3, 4, 8, 16, 64)
    out = {}
    say("   n   " + "  ".join(f"r={r:<3d}" for r in rs) + "   (trials exact)")
    for n in range(0, 7):
        N = 2 ** n
        X = np.array([[rng.randint(-3, 3) for _ in range(N)] for _ in range(trials)], dtype=object)
        K = np.array([[rng.randint(-3, 3) for _ in range(N)] for _ in range(trials)], dtype=object)
        re2 = 2 * K[:, 0]
        nk = norm2(K)
        XK = cmul(X, K)
        a, b = np.ones(trials, dtype=object), np.zeros(trials, dtype=object)   # r = 1
        Y = XK
        cnt = {}
        for r in range(2, max(rs) + 1):
            Y = cmul(Y, K)
            a, b = re2 * a + b, -nk * a
            if r in rs:
                Z = a[:, None] * XK + b[:, None] * X
                cnt[r] = int(sum(1 for t in range(trials) if list(Y[t]) == list(Z[t])))
        out[n] = cnt
        say(f"   {n}   " + "  ".join(f"{cnt[r]:5d}" for r in rs))
    return out


def S2(quick=False):
    say("== S2  8 rounds: composed-matrix shortcut and single combined key")
    rng = random.Random(SEED)
    trials = 40 if quick else 200
    out = {}
    say("   n   matrix = replay   chain = x * H(1)")
    for n in range(0, 7):
        N = 2 ** n
        mat = one = 0
        for _ in range(trials):
            ks = []
            while len(ks) < 8:
                kk = obj([rng.randint(-3, 3) for _ in range(N)])
                if any(kk):
                    ks.append(kk)
            E = np.eye(N, dtype=object)
            Hb = E.copy()
            for kk in ks:
                Hb = cmul(Hb, kk[None, :])
            M = Hb.T                                     # columns H(e_j); H linear
            x = obj([rng.randint(-3, 3) for _ in range(N)])
            y = x
            for kk in ks:
                y = cmul(y, kk)
            mat += list(M.dot(x)) == list(y)
            K = Hb[0]                                    # H(1)
            one += all(list(Hb[j]) == list(cmul(E[j], K)) for j in range(N))
        out[n] = (mat, one, trials)
        say(f"   {n}   {mat:4d}/{trials}         {one:4d}/{trials}")
    return out


def fb_table(b):
    return [int.from_bytes(hashlib.sha256(x.to_bytes(4, "big")).digest()[:4], "big") >> (32 - b)
            for x in range(1 << b)]


def brent(f, x0):
    power = lam = 1
    tort, hare = x0, f[x0]
    while tort != hare:
        if power == lam:
            tort, power, lam = hare, power * 2, 0
        hare = f[hare]
        lam += 1
    tort = hare = x0
    for _ in range(lam):
        hare = f[hare]
    mu = 0
    while tort != hare:
        tort, hare, mu = f[tort], f[hare], mu + 1
    return mu, lam


def memo_rho(f, x0):
    seen, x, i = {}, x0, 0
    while x not in seen:
        seen[x] = i
        x, i = f[x], i + 1
    return seen[x], i - seen[x]


def S3(quick=False):
    say("== S3  cycle detection on f_b = first b bits of SHA-256: Brent (O(1) memory) vs dictionary")
    rng = random.Random(SEED)
    out = {}
    say("   b    agree        mean tail  mean cycle  mean rho   sqrt(pi N/2)  ratio")
    for b in ((12, 16) if quick else (12, 16, 20)):
        f = fb_table(b)
        N = 1 << b
        starts = [rng.randrange(N) for _ in range(200 if quick else 1000)]
        agree, tails, cyc = 0, [], []
        for x0 in starts:
            br = brent(f, x0)
            me = memo_rho(f, x0)
            agree += br == me
            tails.append(me[0])
            cyc.append(me[1])
        mt, mc = sum(tails) / len(tails), sum(cyc) / len(cyc)
        th = math.sqrt(math.pi * N / 2)
        out[b] = (agree, len(starts), mt, mc, (mt + mc) / th)
        say(f"   {b:2d}   {agree}/{len(starts)}   {mt:9.1f}  {mc:9.1f}  {mt + mc:9.1f}  {th:9.1f}    {(mt + mc) / th:.2f}")
    return out


def S4(quick=False):
    say("== S4  cohomology census at n = 2: normalised +-1 cochains, associative ones, gauge classes")
    N = 4
    cells = [(a, b) for a in range(1, N) for b in range(1, N)]
    cocycles = []
    for m in range(1 << 9):
        T = np.ones((N, N), dtype=np.int64)
        for i, (a, b) in enumerate(cells):
            if (m >> i) & 1:
                T[a, b] = -1
        if (assoc_phase(T) == 1).all():
            cocycles.append(T)
    gauges = [np.array([1, (g & 1) and -1 or 1, (g & 2) and -1 or 1, (g & 4) and -1 or 1]) for g in range(8)]
    key = lambda T: T.tobytes()
    classes = []
    for T in cocycles:
        orb = {key(gauged(T, f)) for f in gauges}
        if not any(key(T) in c for c in classes):
            classes.append(orb)
    cdk, clk = key(psi_cd(2)), key(psi_cliff(2))
    same = any(cdk in c and clk in c for c in classes)
    comm = sum(1 for T in cocycles if (T == T.T).all())
    say(f"   normalised cochains: 512;  associative (w = 1): {len(cocycles)};  gauge classes: {len(classes)}")
    say(f"   orbit sizes: {sorted(len(c) for c in classes)};  commutative associative tables: {comm}")
    say(f"   CD (n=2) and CLIFF (n=2) in the same class: {same}")
    return {"cocycles": len(cocycles), "classes": len(classes), "same": same, "comm": comm}


TESTS = {"C1": C1, "C2": C2, "C3": C3, "C4": C4, "W1": W1, "W2": W2, "E1": E1, "E2": E2, "E3": E3,
         "S1": S1, "S2": S2, "S3": S3, "S4": S4}


def main(argv):
    quick = "--quick" in argv
    args = [a for a in argv if not a.startswith("--")]
    if not args or args[0] == "run":
        names = list(TESTS)
    else:
        names = args
    say(f"hash rounds II  (seed {SEED}{', quick' if quick else ''})")
    for nm in names:
        t0 = time.time()
        TESTS[nm](quick)
        say(f"   [{nm}: {time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main(sys.argv[1:])
