"""9-way bucket DHT on the GF(8) Hopf fibres.

    python3 -m hypercube.dht selftest
    python3 -m hypercube.dht bench [--keys 100000] [--nodes 9]

A key is hashed to a cell c = SHA-256(key)[0] mod 64.  Its bucket is the GF(8) Hopf base point
    bucket(c) = dlog(c) mod 9   (0..8)   and bucket(0) = 9   (the zero cell).
Placement unit = bucket: a node owns whole buckets, so cells related by GF(8) multiplication
(c and c*k, k in GF(8)*) always live on the same node.

Proved (Lean, RequestProject/BucketInvariance.lean): `bucketInvariant` -- for c != 0 and
k in GF(8)*, bucket(c * k) = bucket(c); via `dlog_gmul` (logs add mod 63) and `dlog_F8`
(dlog k = 0 mod 9 on GF(8)*).  The distribution and rebalance numbers are measured.

`rebalance` is greedy: when a node joins it takes units from the most loaded nodes while that
lowers the imbalance; when a node leaves its units go to the least loaded nodes.  With only 10
bucket units the placement is coarse; `mode="cell"` (64 cell units, no orbit co-location) is the
finer comparison.
"""

import hashlib
import math
import sys
from collections import defaultdict

from .hopf import DLOG, F8, gmul

ZERO_BUCKET = 9


def bucket(c):
    return ZERO_BUCKET if c == 0 else DLOG[c] % 9


def cell_of(key):
    return hashlib.sha256(key.encode() if isinstance(key, str) else key).digest()[0] & 63


class DHT:
    def __init__(self, nodes, mode="bucket"):
        self.mode = mode
        self.units = list(range(10)) if mode == "bucket" else list(range(64))
        self.store = {u: {} for u in self.units}            # unit -> {key: value}
        self.owner = {}
        nodes = list(nodes)
        for i, u in enumerate(self.units):                  # bucket i -> node i (i < #nodes)
            self.owner[u] = nodes[i % len(nodes)]
        self.nodes = set(nodes)

    def unit(self, key):
        c = cell_of(key)
        return bucket(c) if self.mode == "bucket" else c

    def put(self, key, val):
        self.store[self.unit(key)][key] = val

    def get(self, key):
        return self.store[self.unit(key)].get(key)

    def node_of(self, key):
        return self.owner[self.unit(key)]

    def loads(self):
        L = {n: 0 for n in self.nodes}
        for u in self.units:
            if self.owner[u] in L:
                L[self.owner[u]] += len(self.store[u])
        return L

    def rebalance(self, join=None, leave=None):
        """Add node `join` / remove node `leave`; returns the number of keys moved."""
        moved = 0
        if join is not None:
            self.nodes.add(join)
            while True:
                L = self.loads()
                donor = max((n for n in L if n != join), key=lambda n: L[n])
                cands = [u for u in self.units if self.owner[u] == donor
                         and L[join] + len(self.store[u]) < L[donor]]
                if not cands:
                    break
                u = max(cands, key=lambda u: len(self.store[u]))
                if len(self.store[u]) == 0 or L[join] + len(self.store[u]) >= L[donor]:
                    break
                self.owner[u] = join
                moved += len(self.store[u])
        if leave is not None:
            self.nodes.discard(leave)
            for u in sorted(self.units, key=lambda u: -len(self.store[u])):
                if self.owner[u] == leave:
                    L = self.loads()
                    self.owner[u] = min(self.nodes, key=lambda n: L[n])
                    moved += len(self.store[u])
        return moved


def selftest():
    # the proved invariance, re-checked on the Python tables
    for c in range(1, 64):
        for k in F8[1:]:
            assert bucket(gmul(c, k)) == bucket(c)
            assert DLOG[gmul(c, k)] == (DLOG[c] + DLOG[k]) % 63
    assert all(DLOG[k] % 9 == 0 for k in F8[1:])
    assert sorted(sum(bucket(c) == b for c in range(64)) for b in range(10)) == [1] + [7] * 9
    d = DHT([f"n{i}" for i in range(9)])
    for i in range(2000):
        d.put(f"k{i}", i)
    d.rebalance(join="n9")
    d.rebalance(leave="n3")
    assert all(d.get(f"k{i}") == i for i in range(2000))
    print("dht selftest: ok (bucket(c*k) = bucket(c) for all 63 x 7 pairs; buckets 9 x 7 cells + zero; "
          "put/get survive join and leave)")


def bench(nkeys=100_000, nnodes=9):
    out = [f"DHT benchmark: {nkeys} keys 'key-<i>', {nnodes} nodes"]
    keys = [f"key-{i}" for i in range(nkeys)]
    counts = defaultdict(int)
    for k in keys:
        counts[bucket(cell_of(k))] += 1
    exp = {b: nkeys * (7 / 64 if b < 9 else 1 / 64) for b in range(10)}
    chi = sum((counts[b] - exp[b]) ** 2 / exp[b] for b in range(10))
    fib = [counts[b] for b in range(9)]
    out.append("keys per bucket (0..8 fibres, 9 = zero cell): " + ", ".join(str(counts[b]) for b in range(10)))
    out.append(f"expected: {nkeys * 7 / 64:.0f} per fibre bucket, {nkeys / 64:.0f} in the zero bucket; "
               f"chi^2 = {chi:.2f} on 9 df (5% critical value 16.92); fibre buckets max/min = "
               f"{max(fib) / min(fib):.4f}")
    for mode in ("bucket", "cell"):
        d = DHT([f"n{i}" for i in range(nnodes)], mode)
        for i, k in enumerate(keys):
            d.put(k, i)
        before = d.loads()
        moved = d.rebalance(join=f"n{nnodes}")
        after = d.loads()
        L = sorted(after.values())
        out.append(f"[{mode} units] join 1 node: moved {moved} keys = {moved / nkeys:.2%}; "
                   f"loads before max/min {max(before.values())}/{min(before.values())}, "
                   f"after max/min {L[-1]}/{L[0]} (ideal {nkeys / (nnodes + 1):.0f} each, ideal move "
                   f"{1 / (nnodes + 1):.2%})")
        assert all(d.get(k) == i for i, k in enumerate(keys[:1000]))
        moved_l = d.rebalance(leave="n0")
        out.append(f"[{mode} units] then 1 node leaves: moved {moved_l} keys = {moved_l / nkeys:.2%}")
    h = [int.from_bytes(hashlib.sha256(k.encode()).digest()[:8], "big") for k in keys]
    naive = sum((x % nnodes) != (x % (nnodes + 1)) for x in h)
    out.append(f"[baseline] hash mod N, N = {nnodes} -> {nnodes + 1}: moved {naive / nkeys:.2%}")
    return "\n".join(out)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m hypercube.dht")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("selftest")
    b = sub.add_parser("bench"); b.add_argument("--keys", type=int, default=100_000)
    b.add_argument("--nodes", type=int, default=9)
    a = ap.parse_args(argv)
    if a.cmd == "bench":
        print(bench(a.keys, a.nodes))
    else:
        selftest()


if __name__ == "__main__":
    main(sys.argv[1:])
