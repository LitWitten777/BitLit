"""How much information survives rounds of hashing, and how much the house tools get back.

    python3 -m hypercube.hashrounds run [--quick]      all tests T0..T8, report to stdout
    python3 -m hypercube.hashrounds T4                 one test (T0 .. T8)

Plan, predictions and decision rules: docs/PREREG_HASH_ROUNDS_2026-10-25.md (committed before the
first run).  Proved counterparts: RequestProject/HashRounds.lean and RequestProject/HashRoundsLamb.lean.

Two quantities are kept apart:
* what is THERE: how many inputs a perfect decoder could separate (the image size of the chain;
  `recovered_card_le_image`, `recovered_le_bottleneck`, `ceiling_attained`);
* what the TOOLS GET BACK: measured on held-out samples against a shuffled control.

Needs numpy.
"""

import hashlib
import math
import random
import sys

import numpy as np

from manifold import cd
from . import erase
from . import store_heal as SH
from .cdcheck import cdcheck
from .dht import bucket
from .mirror import LABEL

SEED = 20261025
P61 = (1 << 61) - 1


def say(*a):
    print(*a, flush=True)


# ----------------------------------------------------------------------------------------------
# Cayley-Dickson product on arrays (same doubling rule as manifold/cd.py and CDTower.lean)
# ----------------------------------------------------------------------------------------------

def cconj(x):
    N = x.shape[-1]
    if N == 1:
        return x.copy()
    h = N // 2
    return np.concatenate([cconj(x[..., :h]), -x[..., h:]], axis=-1)


def cmul(x, y):
    """(a, b)(c, d) = (ac - conj(d) b, d a + b conj(c)), on the last axis, broadcasting."""
    N = x.shape[-1]
    if N == 1:
        return x * y
    h = N // 2
    a, b, c, d = x[..., :h], x[..., h:], y[..., :h], y[..., h:]
    return np.concatenate([cmul(a, c) - cmul(cconj(d), b), cmul(d, a) + cmul(b, cconj(c))], axis=-1)


def norm2(x):
    return (x * x).sum(axis=-1)


# ----------------------------------------------------------------------------------------------
# exact linear algebra mod a large prime (rank over Q for small integer matrices, w.h.p.)
# ----------------------------------------------------------------------------------------------

def rank_mod(M, p=P61):
    A = [[int(v) % p for v in row] for row in M]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [v * inv % p for v in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(u - f * v) % p for u, v in zip(A[i], A[r])]
        r += 1
    return r


def solve_mod(M, y, p=P61):
    """Unique solution of M x = y mod p, or None if M is singular."""
    n = len(M)
    A = [[int(v) % p for v in row] + [int(b) % p] for row, b in zip(M, y)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c]), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = pow(A[c][c], p - 2, p)
        A[c] = [v * inv % p for v in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]
                A[i] = [(u - f * v) % p for u, v in zip(A[i], A[c])]
    return [A[i][n] for i in range(n)]


def right_mult_matrix(k):
    """M with M @ x = x * k (columns e_j * k)."""
    N = len(k)
    E = np.eye(N, dtype=object)
    return np.array([cmul(E[j], np.array(k, dtype=object)) for j in range(N)], dtype=object).T


def left_mult_matrix(k):
    N = len(k)
    E = np.eye(N, dtype=object)
    return np.array([cmul(np.array(k, dtype=object), E[j]) for j in range(N)], dtype=object).T


# ----------------------------------------------------------------------------------------------
# T0: the product used by the hashes passes the pentagon checksum (and the strict sign check)
# ----------------------------------------------------------------------------------------------

def T0(quick=False):
    say("== T0  sanity: the array CD product = manifold.cd.mul, and passes the pentagon checksum")
    rnd = random.Random(SEED)
    for n in range(0, 7):
        N = 2 ** n
        for _ in range(20):
            x = [rnd.randint(-9, 9) for _ in range(N)]
            y = [rnd.randint(-9, 9) for _ in range(N)]
            assert list(cmul(np.array(x, dtype=object), np.array(y, dtype=object))) == cd.mul(x, y)
    mulf = lambda x, y: [int(v) for v in cmul(np.array(x, dtype=np.int64), np.array(y, dtype=np.int64))]
    tot = viol = 0
    for n in range(2, 7):
        for _ in range(30 if quick else 200):
            w = [rnd.randrange(2 ** n) for _ in range(6)]
            r = cdcheck(w, n, mulf, strict=True)
            tot += r["pentagons"]
            viol += len(r["violations"])
    say(f"   array product == manifold.cd.mul at levels 0..6 (20 random pairs each): ok")
    say(f"   pentagon + strict sign check (levels 2..6): {tot} pentagons, {viol} violations")
    return {"pentagons": tot, "violations": viol}


# ----------------------------------------------------------------------------------------------
# T1: ceiling decay of an iterated truncated hash (exhaustive)
# ----------------------------------------------------------------------------------------------

def trunc_hash_table(b):
    return np.array([int.from_bytes(hashlib.sha256(x.to_bytes(4, "big")).digest()[:4], "big") >> (32 - b)
                     for x in range(1 << b)], dtype=np.int64)


def T1(quick=False):
    say("== T1  ceiling decay of f_b = first b bits of SHA-256, iterated (exhaustive over 2^b inputs)")
    out = {}
    for b in ((6, 12) if quick else (6, 12, 16)):
        f = trunc_hash_table(b)
        N = 1 << b
        cur = np.arange(N)            # f^r applied to every input
        t = 1.0
        rows = []
        for r in range(1, 33):
            cur = f[cur]
            img = np.unique(cur)
            t = 1 - math.exp(-t)
            # the preimage decoder: g(y) = smallest x with f^r(x) = y
            g = {}
            for x, y in enumerate(cur.tolist()):
                g.setdefault(y, x)
            rec = sum(1 for x, y in enumerate(cur.tolist()) if g[y] == x)
            assert rec == len(img)    # ceiling_attained: exactly #image inputs recovered
            rows.append((r, len(img), math.log2(len(img)), t * N, (len(img) / N) / t - 1))
        out[b] = rows
        say(f"   b = {b}:  r  |image|  bits   random-mapping   rel.dev")
        for r, im, bits, pred, dev in rows:
            if r <= 10 or r in (16, 24, 32):
                say(f"        {r:3d} {im:7d} {bits:6.2f} {pred:10.1f}   {dev:+.3f}")
    say("   every row: the preimage decoder recovered exactly |image| inputs (ceiling attained)")
    return out


# ----------------------------------------------------------------------------------------------
# T2: the tools as rounds
# ----------------------------------------------------------------------------------------------

def T2(quick=False):
    say("== T2  the tools as rounds (exhaustive on the 64 cells) + store endurance")
    one = [len({LABEL[r][v] for v in range(64)}) for r in range(9)]
    two = [len({(LABEL[r][v], LABEL[s][v]) for v in range(64)}) for r in range(9) for s in range(9) if r < s]
    bk = len({bucket(v) for v in range(64)})
    bks = len({bucket(hashlib.sha256(bytes([v])).digest()[0] & 63) for v in range(64)})
    say(f"   one store shard: image sizes {sorted(set(one))} (Lean one_shard_ceiling: <= 8)")
    say(f"   two store shards: image sizes {sorted(set(two))} over all 36 pairs (two_views_determine: 64)")
    say(f"   GF(8) bucket: image {bk} (bucket_ceiling: <= 10);  bucket(cell(SHA-256(v))): image {bks}")
    rnd = random.Random(SEED)
    runs, ok = (10 if quick else 50), 0
    for _ in range(runs):
        data = bytes(rnd.randrange(256) for _ in range(4096))
        cur = data
        for _ in range(8):
            shards, ncell = SH.encode_shards(cur)
            keep = rnd.sample(range(9), 2)
            kept = {}
            for r in keep:
                sh = bytearray(shards[r])
                i = rnd.randrange(len(sh))
                sh[i] ^= 1 << rnd.randrange(8)
                kept[r] = bytes(sh)
            cur = SH.decode_shards(kept, ncell, len(cur))
        ok += cur == data
    say(f"   endurance: {ok}/{runs} runs exact after 8 rounds of encode -> keep 2 of 9 -> flip 1 bit each -> heal+decode")
    return {"one": one, "two": two, "bucket": bk, "bucket_sha": bks, "endurance": (ok, runs)}


# ----------------------------------------------------------------------------------------------
# T4: CD linear rounds per level
# ----------------------------------------------------------------------------------------------

def T4(quick=False):
    say("== T4  CD linear rounds x -> x k_r, 8 rounds, levels 0..6")
    rnd = random.Random(SEED)
    trials = 40 if quick else 200
    res = {}
    say("   n  dim  conj-trick  linear-solve  norm-leak  real-part-leak   (exact-recovery / leak rates)")
    for n in range(0, 7):
        N = 2 ** n
        c_ok = l_ok = n_ok = re_ok = 0
        for _ in range(trials):
            x = np.array([rnd.randint(-5, 5) for _ in range(N)], dtype=object)
            ks = []
            while len(ks) < 8:
                k = np.array([rnd.randint(-3, 3) for _ in range(N)], dtype=object)
                if any(k):
                    ks.append(k)
            y = x
            for k in ks:
                y = cmul(y, k)
            # (a) conjugate trick, backwards
            z, good = y, True
            for k in reversed(ks):
                w = cmul(z, cconj(k))
                nk = int(norm2(k))
                if any(int(v) % nk for v in w):
                    good = False
                    break
                z = np.array([int(v) // nk for v in w], dtype=object)
            c_ok += good and list(z) == list(x)
            # (b) exact linear solve mod p
            M = np.eye(N, dtype=object)
            for k in ks:
                M = right_mult_matrix(k).dot(M)
            sol = solve_mod(M.tolist(), list(y))
            l_ok += sol is not None and sol == [int(v) % P61 for v in x]
            # norm leak and real-part leak
            n_ok += int(norm2(y)) == int(norm2(x)) * math.prod(int(norm2(k)) for k in ks)
            K = np.zeros(N, dtype=object)
            K[0] = 1
            for k in reversed(ks):
                K = cmul(k, K)
            re_ok += int(y[0]) == int(cmul(x, K)[0])
        res[n] = (c_ok, l_ok, n_ok, re_ok, trials)
        say(f"   {n}  {N:3d}   {c_ok:4d}/{trials}    {l_ok:4d}/{trials}     {n_ok:4d}/{trials}    {re_ok:4d}/{trials}")
    return res


# ----------------------------------------------------------------------------------------------
# T5: zero-divisor erasure through rounds
# ----------------------------------------------------------------------------------------------

def T5(quick=False):
    say("== T5  zero-divisor erasure through rounds (sedenions, left multiplication), rank of the chain")
    rnd = random.Random(SEED)
    zds = [erase.zd(i)[0] for i in range(84)]
    trials = 40 if quick else 200
    out = {}
    for mode in ("distinct", "repeated", "interleaved"):
        hist = [[] for _ in range(8)]
        for _ in range(trials):
            M = np.eye(16, dtype=object)
            z0 = rnd.choice(zds)
            for r in range(8):
                if mode == "distinct":
                    k = rnd.choice(zds)
                elif mode == "repeated":
                    k = z0
                else:
                    k = rnd.choice(zds) if r % 2 == 0 else [rnd.randint(-3, 3) for _ in range(16)]
                M = left_mult_matrix(k).dot(M)
                hist[r].append(rank_mod(M.tolist()))
        out[mode] = hist
        summ = "  ".join(f"r{r+1}:{min(h)}-{max(h)} (mean {sum(h)/len(h):.2f})" for r, h in enumerate(hist))
        mono = all(a >= b for t in range(trials) for a, b in zip([h[t] for h in hist], [h[t] for h in hist][1:]))
        say(f"   {mode:11s} {summ}   non-increasing in every trial: {mono}")
    return out


# ----------------------------------------------------------------------------------------------
# T6: Lamb vector channel
# ----------------------------------------------------------------------------------------------

def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def dot(a, b):
    return sum(p * q for p, q in zip(a, b))


def cross_matrix(k):
    return [[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]]


def embV(v):
    s = np.zeros(16, dtype=object)
    s[1:4] = v
    return s


def T6(quick=False):
    say("== T6  Lamb vector channel")
    rnd = random.Random(SEED)
    trials = 40 if quick else 200
    rv = lambda: [rnd.randint(-5, 5) for _ in range(3)]
    out = {}
    for mode in ("generic", "perpendicular"):
        hist = [[] for _ in range(8)]
        for _ in range(trials):
            M = np.eye(3, dtype=object)
            prev = None
            for r in range(8):
                while True:
                    k = rv()
                    if mode == "perpendicular" and prev is not None:
                        k = cross(prev, rv())
                    if any(k) and (prev is None or mode == "perpendicular" or dot(prev, k) != 0):
                        break
                M = np.array(cross_matrix(k), dtype=object).dot(M)
                hist[r].append(rank_mod(M.tolist()))
                prev = k
        out[mode] = hist
        say(f"   rounds x -> k_r x x, {mode:13s} keys: rank by round " +
            " ".join(f"{min(h)}-{max(h)}" for h in hist))
    # (b) commutator -> Lamb vector -> part of u orthogonal to omega
    comm_ok = perp_ok = 0
    for _ in range(trials):
        w, u = rv(), rv()
        if not any(w):
            w = [1, 0, 0]
        c = cmul(embV(w), embV(u)) - cmul(embV(u), embV(w))
        L = [int(v) // 2 for v in c[1:4]]
        comm_ok += L == cross(w, u) and all(int(v) % 2 == 0 for v in c[1:4]) and not any(np.delete(c, [1, 2, 3]))
        nw = dot(w, w)
        u_perp_scaled = [nw * ui - dot(w, u) * wi for ui, wi in zip(u, w)]     # |w|^2 u_perp
        perp_ok += cross(L, w) == u_perp_scaled
    say(f"   commutator wu - uw = 2(w x u) in slots e1..e3, nothing else: {comm_ok}/{trials}")
    say(f"   (w x u) x w = |w|^2 u_perp (2 of 3 dims of u recovered exactly): {perp_ok}/{trials}")
    # (c) associator detector [x, e4, k] = -2 x x k in e5..e7
    e4 = np.zeros(16, dtype=object)
    e4[4] = 1
    det_ok = zero_rand = zero_aligned = 0
    for _ in range(trials):
        a, b = rv(), rv()
        A = cmul(cmul(embV(a), e4), embV(b)) - cmul(embV(a), cmul(e4, embV(b)))
        expect = np.zeros(16, dtype=object)
        expect[5:8] = [-2 * t for t in cross(a, b)]
        det_ok += list(A) == list(expect)
        zero_rand += not any(A) and any(cross(a, b))
        c = rnd.randint(-4, 4)
        A2 = cmul(cmul(embV(a), e4), embV([c * t for t in a])) - cmul(embV(a), cmul(e4, embV([c * t for t in a])))
        zero_aligned += not any(A2)
    say(f"   associator [a, e4, b] = -2 (a x b) in e5..e7: {det_ok}/{trials};  "
        f"zero for non-parallel pairs: {zero_rand}/{trials};  zero for aligned pairs: {zero_aligned}/{trials}")
    out.update(comm=comm_ok, perp=perp_ok, assoc=det_ok, zero_rand=zero_rand, zero_aligned=zero_aligned)
    return out


# ----------------------------------------------------------------------------------------------
# hashes for T7
# ----------------------------------------------------------------------------------------------

_krng = np.random.default_rng(SEED)
CD_KEYS = _krng.integers(0, 256, (8, 16)).astype(np.int64)
# added after the first run (deviation, see report): the same keys with coordinate 0 adjusted so
# that every key has odd norm; then x -> x k is a bijection of (Z/256)^16 (measured in T7).
CD_KEYS_ODD = CD_KEYS.copy()
for _k in CD_KEYS_ODD:
    if int((_k * _k).sum()) % 2 == 0:
        _k[0] ^= 1


def cd_hash(kind, r):
    def H(bits):
        x = np.packbits(bits, axis=1).astype(np.int64)            # (N, 16) bytes = sedenion
        for t in range(r):
            k = CD_KEYS_ODD[t] if kind == "CDlinodd" else CD_KEYS[t]
            if kind in ("CDlin", "CDlinodd"):
                x = cmul(x, k) % 256
            elif kind == "CDsq":
                x = (cmul(x, x) + k) % 256
            else:
                x = np.roll((cmul(x, k) % 256) ^ (cmul(x, x) % 256), 1, axis=1)
        return np.unpackbits(x.astype(np.uint8), axis=1)
    return H


K256 = np.array([
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2],
    dtype=np.uint32)
IV = np.array([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
               0x5be0cd19], dtype=np.uint32)


def rotr(x, n):
    return (x >> np.uint32(n)) | (x << np.uint32(32 - n))


def S0(a): return rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
def S1(e): return rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
def s0(w): return rotr(w, 7) ^ rotr(w, 18) ^ (w >> np.uint32(3))
def s1(w): return rotr(w, 17) ^ rotr(w, 19) ^ (w >> np.uint32(10))
def ch(e, f, g): return (e & f) ^ (~e & g)
def maj(a, b, c): return (a & b) ^ (a & c) ^ (b & c)


def sha_rounds(W, r):
    """State after r rounds of the SHA-256 compression function (no feed-forward); W: (N, 16) uint32."""
    with np.errstate(over="ignore"):
        Wl = [W[:, t] for t in range(16)]
        for t in range(16, max(r, 16)):
            Wl.append(s1(Wl[t - 2]) + Wl[t - 7] + s0(Wl[t - 15]) + Wl[t - 16])
        n = W.shape[0]
        a, b, c, d, e, f, g, h = [np.full(n, v, dtype=np.uint32) for v in IV]
        for t in range(r):
            T1 = h + S1(e) + ch(e, f, g) + K256[t] + Wl[t]
            T2 = S0(a) + maj(a, b, c)
            h, g, f, e, d, c, b, a = g, f, e, d + T1, c, b, a, T1 + T2
        return np.stack([a, b, c, d, e, f, g, h], axis=1)


def words_to_bits(X):
    return np.unpackbits(X.astype(">u4").view(np.uint8), axis=1)


def bits_to_words(bits, nw):
    return np.packbits(bits, axis=1).view(">u4").astype(np.uint32).reshape(-1, nw)


def sha_hash(r):
    def H(bits):
        W = np.zeros((bits.shape[0], 16), dtype=np.uint32)
        W[:, :2] = bits_to_words(bits, 2)
        return words_to_bits(sha_rounds(W, r))
    return H


def sha256_selfcheck():
    """Full 64 rounds + feed-forward on the padded empty message = SHA-256('')."""
    W = np.zeros((1, 16), dtype=np.uint32)
    W[0, 0] = 0x80000000
    st = (sha_rounds(W, 64)[0].astype(np.uint64) + IV.astype(np.uint64)) % (1 << 32)
    return b"".join(int(v).to_bytes(4, "big") for v in st) == hashlib.sha256(b"").digest()


# ----------------------------------------------------------------------------------------------
# measurements
# ----------------------------------------------------------------------------------------------

def v2(a, k=8):
    return k if a % (1 << k) == 0 else (a & -a).bit_length() - 1


def image_bits_mod2k(M, k=8):
    """log2 of the image size of x -> M x on (Z/2^k)^n (Smith form over the local ring Z/2^k)."""
    q = 1 << k
    A = [[int(v) % q for v in row] for row in M]
    n, m = len(A), len(A[0])
    total, r = 0, 0
    while r < min(n, m):
        best = min(((v2(A[i][j], k), i, j) for i in range(r, n) for j in range(r, m)), default=(k, 0, 0))
        v, i, j = best
        if v >= k:
            break
        A[r], A[i] = A[i], A[r]
        for row in A:
            row[r], row[j] = row[j], row[r]
        u = A[r][r] >> v
        uinv = pow(u, -1, q)
        for i2 in range(r + 1, n):
            if A[i2][r]:
                f = (A[i2][r] >> v) * uinv % q
                A[i2] = [(a - f * b) % q for a, b in zip(A[i2], A[r])]
        for j2 in range(r + 1, m):
            if A[r][j2]:
                f = (A[r][j2] >> v) * uinv % q
                for row in A:
                    row[j2] = (row[j2] - f * row[r]) % q
        total += k - v
        r += 1
    return total


def solve_mod256(M, y):
    """Solve M x = y over Z/256 when M is invertible (odd pivots); None otherwise."""
    n = len(M)
    A = [[int(v) % 256 for v in row] + [int(b) % 256] for row, b in zip(M, y)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c] % 2), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        inv = pow(A[c][c], -1, 256)
        A[c] = [v * inv % 256 for v in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * b) % 256 for a, b in zip(A[i], A[c])]
    return [A[i][n] for i in range(n)]


def cdlin_algebraic(r, rng, n=200, kind="CDlin"):
    """CDlin with known keys: exact image size (bits) and exact recovery rate by solving mod 256."""
    keys = CD_KEYS_ODD if kind == "CDlinodd" else CD_KEYS
    M = np.eye(16, dtype=np.int64)
    for t in range(r):
        Rk = np.array([cmul(np.eye(16, dtype=np.int64)[j], keys[t]) for j in range(16)]).T % 256
        M = (Rk @ M) % 256
    bits = image_bits_mod2k(M.tolist())
    x = rng.integers(0, 256, (n, 16)).astype(np.int64)
    y = np.packbits(cd_hash(kind, r)(np.unpackbits(x.astype(np.uint8), axis=1)), axis=1).astype(np.int64)
    ok = 0
    for xi, yi in zip(x, y):
        sol = solve_mod256(M.tolist(), yi.tolist())
        ok += sol is not None and sol == xi.tolist()
    return bits, ok, n


def H2(p):
    p = min(max(p, 1e-12), 1 - 1e-12)
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def gf2_affine_bits(X, Y, ntest=512):
    """Number of output bits that are an exact affine GF(2) function of the input bits."""
    nin = X.shape[1]
    ntr = nin + 64
    A = np.concatenate([X[:ntr], np.ones((ntr, 1), np.uint8), Y[:ntr]], axis=1).astype(bool)
    rows, piv_cols, r = A.shape[0], [], 0
    for c in range(nin + 1):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + nz[0]
        A[[r, p]] = A[[p, r]]
        mask = A[:, c].copy()
        mask[r] = False
        A[mask] ^= A[r]
        piv_cols.append(c)
        r += 1
        if r == rows:
            break
    consistent = ~A[r:, nin + 1:].any(axis=0)
    sol = np.zeros((nin + 1, Y.shape[1]), dtype=bool)
    for i, c in enumerate(piv_cols):
        sol[c] = A[i, nin + 1:]
    Xt = np.concatenate([X[-ntest:], np.ones((ntest, 1), np.uint8)], axis=1).astype(np.int64)
    pred = (Xt @ sol.astype(np.int64)) % 2
    ok = (pred == Y[-ntest:]).all(axis=0) & consistent
    return int(ok.sum())


def mutual_info(a, b, na, nb):
    joint = np.bincount(a * nb + b, minlength=na * nb).reshape(na, nb) / len(a)
    pa, pb = joint.sum(1, keepdims=True), joint.sum(0, keepdims=True)
    nz = joint > 0
    return float((joint[nz] * np.log2(joint[nz] / (pa @ pb)[nz])).sum())


def measure(H, nin, N, rng, shuffles):
    X = rng.integers(0, 2, (2 * N, nin), dtype=np.uint8)
    Y = H(X)
    nout = Y.shape[1]
    Xs, Ys = 2.0 * X - 1, 2.0 * Y - 1
    Xtr, Xte, Ytr, Yte = Xs[:N], Xs[N:], Ys[:N], Ys[N:]
    # M1 avalanche
    nav = min(N, 1024)
    flips = np.zeros((nin, nout))
    base = Y[:nav]
    for i in range(nin):
        Xf = X[:nav].copy()
        Xf[:, i] ^= 1
        flips[i] = (H(Xf) != base).mean(axis=0)
    av_mean, av_dev = float(flips.mean()), float(np.abs(flips - 0.5).max())
    # M2 Walsh correlation, M4 recovered bits (best single output bit chosen on train)
    def corr_stats(Ytr_, Yte_):
        Ctr = (Xtr.T @ Ytr_) / N
        Cte = (Xte.T @ Yte_) / N
        j = np.abs(Ctr).argmax(axis=1)
        sgn = np.sign(Ctr[np.arange(nin), j])
        acc = (1 + sgn * Cte[np.arange(nin), j]) / 2
        return float(np.abs(Ctr).max()), acc
    maxc, acc = corr_stats(Ytr, Yte)
    null_c, null_acc = [], []
    for _ in range(shuffles):
        p = rng.permutation(N)
        q = rng.permutation(N)
        c_, a_ = corr_stats(Ytr[p], Yte[q])
        null_c.append(c_)
        null_acc.append(float((a_ - 0.5).max()))
    c_floor = float(np.quantile(null_c, 0.99))
    a_floor = float(np.quantile(null_acc, 0.99))
    rec = acc - 0.5 > a_floor
    rec_bits = float(sum(1 - H2(a) for a in acc[rec]))
    # M3 affine bits
    aff = gf2_affine_bits(X, Y)
    # M5 Hopf / mirror features
    cin = (np.packbits(X[:N, :6], axis=1)[:, 0] >> 2).astype(np.int64)
    cout = (np.packbits(Y[:N, :6], axis=1)[:, 0] >> 2).astype(np.int64)
    btab = np.array([bucket(v) for v in range(64)])
    ltab = np.array([LABEL[0][v] for v in range(64)])
    feats = {}
    for name, tab, nb in (("bucket", btab, 10), ("shard0", ltab, 8)):
        fo = tab[cout]
        mi = mutual_info(cin, fo, 64, nb)
        nulls = [mutual_info(cin, fo[rng.permutation(N)], 64, nb) for _ in range(shuffles)]
        feats[name] = (mi - float(np.mean(nulls)), mi > float(np.quantile(nulls, 0.99)))
    # M7 distinct outputs among the 2N samples (collisions = information provably destroyed)
    distinct = len(np.unique(np.packbits(Y, axis=1), axis=0))
    return {"distinct": distinct, "nsamp": 2 * N, "av_mean": av_mean, "av_dev": av_dev, "maxc": maxc, "c_floor": c_floor,
            "affine": aff, "rec_bits": rec_bits, "rec_count": int(rec.sum()), "lambda_irred": int(nin - rec.sum()),
            "obstr_min": float(1 - acc.max()), "feats": feats, "nin": nin, "nout": nout}


def T7(quick=False):
    say("== T7 (+T3)  statistical leakage per round; Lambda-obstruction profile per input bit")
    assert sha256_selfcheck(), "SHA-256 round implementation does not match hashlib"
    say("   SHA-256 round implementation: 64 rounds + feed-forward reproduce hashlib SHA-256('')")
    N = 1 << (11 if quick else 14)
    shuffles = 20 if quick else 100
    rng = np.random.default_rng(SEED)
    out = {}
    plans = [("CDlin", 128, range(1, 9)), ("CDlinodd", 128, range(1, 9)), ("CDsq", 128, range(1, 9)), ("CDmix", 128, range(1, 9)),
             ("SHA256", 64, list(range(1, 17)) + [20, 24])]
    for name, nin, rounds in plans:
        say(f"   {name}: r | aval mean, max|p-.5| | max|corr| (floor) | affine out-bits | recovered bits "
            f"(#bits / Lambda-irreducible) | min obstruction | Hopf bucket MI, shard0 MI (excess bits, *=above floor) | distinct outputs"
            + (" | Re leak" if name.startswith("CD") else "") + (" | algebraic decoder" if name in ("CDlin", "CDlinodd") else ""))
        for r in rounds:
            H = sha_hash(r) if name == "SHA256" else cd_hash(name, r)
            m = measure(H, nin, N, rng, shuffles)
            line = (f"      {r:2d} | {m['av_mean']:.3f} {m['av_dev']:.3f} | {m['maxc']:.3f} ({m['c_floor']:.3f}) | "
                    f"{m['affine']:3d}/{m['nout']} | {m['rec_bits']:7.2f} ({m['rec_count']}/{m['lambda_irred']}) | "
                    f"{m['obstr_min']:.3f} | " +
                    ", ".join(f"{v[0]:+.4f}{'*' if v[1] else ''}" for v in m["feats"].values()) +
                    f" | distinct {m['distinct']}/{m['nsamp']}")
            if name.startswith("CD"):
                line += f" | Re leak {re_leak(name, r, rng)}"
            if name in ("CDlin", "CDlinodd"):
                bits, ok, n = cdlin_algebraic(r, rng, kind=name)
                line += f" | image {bits}/128 bits, solve-mod-256 recovery {ok}/{n}"
            say(line)
            out[(name, r)] = m
    return out


def re_leak(kind, r, rng, n=2000):
    """M6: fraction of samples with Re(H(x)) == Re(x K) mod 256, K = k1 (k2 (... k_r))."""
    x = rng.integers(0, 256, (n, 16)).astype(np.int64)
    y = np.packbits(cd_hash(kind, r)(np.unpackbits(x.astype(np.uint8), axis=1)), axis=1).astype(np.int64)
    keys = CD_KEYS_ODD if kind == "CDlinodd" else CD_KEYS
    K = np.zeros(16, dtype=np.int64)
    K[0] = 1
    for t in reversed(range(r)):
        K = cmul(keys[t], K) % 256
    pred = cmul(x, K)[:, 0] % 256
    return f"{float((pred == y[:, 0]).mean()):.3f}"


# ----------------------------------------------------------------------------------------------
# T3 demo: obstruction depends on the decoder (octonion round)
# ----------------------------------------------------------------------------------------------

def T3(quick=False):
    say("== T3  Lambda-obstruction depends on the decoder (octonion round x -> x k, 3-bit coordinates)")
    rnd = random.Random(SEED)
    k = np.array([rnd.randint(-3, 3) for _ in range(8)], dtype=object)
    while not any(k):
        k = np.array([rnd.randint(-3, 3) for _ in range(8)], dtype=object)
    nk = int(norm2(k))
    xs = [np.array([rnd.randint(0, 7) for _ in range(8)], dtype=object) for _ in range(2000)]
    exact = lambda y: tuple(int(v) // nk for v in cmul(y, cconj(k)))
    shifted = lambda y: tuple((t + 1) % 8 if i == 0 else t for i, t in enumerate(exact(y)))
    for name, g in (("exact inverse y -> y conj(k)/|k|^2", exact), ("shifted decoder (sigma o g)", shifted)):
        obs = [sum(1 for x in xs if (int(x[i // 3]) >> (i % 3) & 1) != (g(cmul(x, k))[i // 3] >> (i % 3) & 1))
               for i in range(24)]
        anyobs = sum(1 for x in xs if g(cmul(x, k)) != tuple(int(v) for v in x))
        say(f"   {name}: per-bit obstruction sizes {sorted(set(obs))}; inputs in some obstruction {anyobs}/{len(xs)}")


# ----------------------------------------------------------------------------------------------
# T8: exact inversion of reduced SHA-256 in the T7 input model
# ----------------------------------------------------------------------------------------------

def invert_sha(state, r):
    """Recover (W0, W1) from the state after r <= 16 rounds (W2..W15 = 0). W1 is None if r = 1."""
    with np.errstate(over="ignore"):
        a, b, c, d, e, f, g, h = [state[:, i].copy() for i in range(8)]
        for t in range(r - 1, -1, -1):
            pa, pb, pc, pe, pf, pg = b, c, d, f, g, h        # state before round t (all but d, h)
            T2 = S0(pa) + maj(pa, pb, pc)
            T1 = a - T2
            pd = e - T1
            if t >= 2:
                ph = T1 - S1(pe) - ch(pe, pf, pg) - K256[t]   # W_t = 0
                Wt = None
            else:
                ph = np.full_like(a, IV[7] if t == 0 else IV[6])  # state before round 1 has h = IV.g
                Wt = T1 - ph - S1(pe) - ch(pe, pf, pg) - K256[t]
                if t == 1:
                    W1 = Wt
                else:
                    W0 = Wt
            a, b, c, d, e, f, g, h = pa, pb, pc, pd, pe, pf, pg, ph
        return W0, (W1 if r >= 2 else None)


def T8(quick=False):
    say("== T8  exact inversion of reduced SHA-256 (input = W0, W1; W2..W15 = 0), r = 1..16")
    rng = np.random.default_rng(SEED)
    n = 200 if quick else 1000
    res = {}
    for r in range(1, 17):
        W = np.zeros((n, 16), dtype=np.uint32)
        W[:, :2] = rng.integers(0, 1 << 32, (n, 2), dtype=np.uint64).astype(np.uint32)
        W0, W1 = invert_sha(sha_rounds(W, r), r)
        ok0 = int((W0 == W[:, 0]).sum())
        ok1 = int((W1 == W[:, 1]).sum()) if W1 is not None else 0
        both = int(((W0 == W[:, 0]) & (W1 == W[:, 1])).sum()) if W1 is not None else 0
        res[r] = (ok0, ok1, both, n)
        say(f"   r = {r:2d}: W0 recovered {ok0}/{n}, W1 recovered {ok1}/{n}, full 64-bit input {both}/{n}")
    return res


TESTS = {"T0": T0, "T1": T1, "T2": T2, "T3": T3, "T4": T4, "T5": T5, "T6": T6, "T7": T7, "T8": T8}


def main(argv):
    quick = "--quick" in argv
    names = [a for a in argv if a in TESTS] or (list(TESTS) if "run" in argv else [])
    if not names:
        print(__doc__)
        return
    for t in names:
        TESTS[t](quick)


if __name__ == "__main__":
    main(sys.argv[1:])
