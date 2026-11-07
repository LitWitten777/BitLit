"""Mirror archive: a file as 9 shards on the GF(8) Hopf fibres; any 2 shards restore it.

    python3 -m hypercube.archive pack <file> --out <dir>      9 shards + manifest.json
    python3 -m hypercube.archive unpack <dir> --out <file>    restore from any 2 intact shards
    python3 -m hypercube.archive damage <dir> --shards k      delete k random shards (demo)
    python3 -m hypercube.archive selftest                     200 random files x all 36 pairs

The bytes are read as 6-bit cells (MSB first, zero padded).  Shard r stores, for every cell v,
the 3-bit label of the view v ^ W_r (W_r = GF(8) fibre r plus 0), packed 8 labels per 3 bytes:
each shard is half the size of the file, the archive is 4.5x.

Proved (Lean, RequestProject/MirrorCode.lean): `two_views_determine`, `two_views_realised`,
`view_card` -- any two different mirrors recover each cell, one mirror leaves 8 candidates.
Not proved (ordinary code): the byte <-> cell packing, the shard file format, the manifest.
Standard library only; the inner loops run through `bytes.translate` and big-integer XOR.
"""

import hashlib
import json
import os
import random
import sys
from functools import lru_cache

from .mirror import DECODE, LABEL

FORMAT = "q6-mirror-archive/1"
NSHARDS = 9


# ---------------------------------------------------------------- bit packing (C-speed loops)

def _xor_streams(parts, n):
    acc = 0
    for p in parts:
        acc ^= int.from_bytes(p, "big")
    return acc.to_bytes(n, "big")


def _group(w):
    """(symbols per group, bytes per group) for w-bit symbols."""
    g = 8 // _gcd(w, 8)
    return g, g * w // 8


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


@lru_cache(maxsize=None)
def _tables(w):
    """T[(k, j)][s]: contribution of symbol value s at group position k to output byte j."""
    g, nb = _group(w)
    T = {}
    for k in range(g):
        for i in range(w):                      # bit i of the symbol, MSB first
            p = k * w + i                       # global bit position in the group, MSB first
            j, b = divmod(p, 8)
            T.setdefault((k, j), [0] * 256)
            for s in range(256):
                if s >> (w - 1 - i) & 1:
                    T[(k, j)][s] |= 1 << (7 - b)
    return g, nb, {key: bytes(v) for key, v in T.items()}


def pack(symbols, w):
    """One w-bit symbol per byte -> tightly packed bytes (zero padded to a whole group)."""
    g, nb, T = _tables(w)
    symbols = bytes(symbols) + bytes(-len(symbols) % g)
    n = len(symbols) // g
    out = bytearray(n * nb)
    for j in range(nb):
        parts = [symbols[k::g].translate(T[(k, jj)]) for (k, jj) in T if jj == j]
        out[j::nb] = _xor_streams(parts, n)
    return bytes(out)


def unpack(data, w, count):
    """Inverse of `pack`: tightly packed bytes -> `count` w-bit symbols, one per byte."""
    g, nb, U = _untables(w)
    data = bytes(data) + bytes(-len(data) % nb)
    n = len(data) // nb
    out = bytearray(n * g)
    for k in range(g):
        out[k::g] = _xor_streams([data[j::nb].translate(t) for j, t in U[k]], n)
    return bytes(out[:count])


@lru_cache(maxsize=None)
def _untables(w):
    """U[k] = [(j, table)]: byte j of a group contributes table[byte] to symbol k."""
    g, nb = _group(w)
    U = []
    for k in range(g):
        acc = {}
        for i in range(w):
            j, b = divmod(k * w + i, 8)
            t = acc.setdefault(j, [0] * 256)
            for x in range(256):
                t[x] |= ((x >> (7 - b)) & 1) << (w - 1 - i)
        U.append([(j, bytes(t)) for j, t in acc.items()])
    return g, nb, U


# ---------------------------------------------------------------- the mirror code on streams

LABEL_TAB = [bytes(LABEL[r][v & 63] for v in range(256)) for r in range(NSHARDS)]


def cells_of(data):
    """bytes -> 6-bit cells (one per byte), MSB first, as hypercube.mirror._cells."""
    ncell = (8 * len(data) + 5) // 6
    return unpack(data, 6, ncell)


def bytes_of(cells, n):
    return pack(cells, 6)[:n]


def label_stream(cells, r):
    """The 3-bit view labels of mirror r, one per byte."""
    return cells.translate(LABEL_TAB[r])


def decode_labels(r, a, s, b):
    """Two label streams (mirrors r != s) -> cells, through the proved two-view decoder."""
    combo, shift = _pair_tables(r, s)
    joined = _xor_streams([a, b.translate(shift)], len(a))
    return joined.translate(combo)


@lru_cache(maxsize=None)
def _pair_tables(r, s):
    table = DECODE[(r, s)]
    combo = bytes(table.get((x & 7, x >> 3 & 7), 0) for x in range(256))
    shift = bytes((x & 7) << 3 for x in range(256))
    return combo, shift


def encode_shards(data):
    cells = cells_of(data)
    return [pack(label_stream(cells, r), 3) for r in range(NSHARDS)], len(cells)


def decode_shards(shards, ncell, size):
    """shards: dict mirror -> packed shard bytes (any 2 used)."""
    (r, A), (s, B) = sorted(shards.items())[:2]
    a, b = unpack(A, 3, ncell), unpack(B, 3, ncell)
    return bytes_of(decode_labels(r, a, s, b), size)


# ---------------------------------------------------------------- files

def sha256(b):
    return hashlib.sha256(b).hexdigest()


def shard_name(r):
    return f"shard_{r}.q6m"


def pack_file(path, out):
    with open(path, "rb") as f:
        data = f.read()
    shards, ncell = encode_shards(data)
    os.makedirs(out, exist_ok=True)
    entries = []
    for r, sh in enumerate(shards):
        with open(os.path.join(out, shard_name(r)), "wb") as f:
            f.write(sh)
        entries.append({"mirror": r, "file": shard_name(r), "size": len(sh), "sha256": sha256(sh)})
    manifest = {"format": FORMAT, "name": os.path.basename(path), "size": len(data),
                "sha256": sha256(data), "cells": ncell, "shards": entries,
                "rule": "any 2 of the 9 shards restore the file (Lean: two_views_determine)"}
    with open(os.path.join(out, "manifest.json"), "w") as f:
        json.dump(manifest, f, indent=2)
    return manifest


def unpack_dir(d, out):
    with open(os.path.join(d, "manifest.json")) as f:
        m = json.load(f)
    good, bad = {}, []
    for e in m["shards"]:
        p = os.path.join(d, e["file"])
        if not os.path.exists(p):
            continue
        with open(p, "rb") as f:
            b = f.read()
        if sha256(b) == e["sha256"]:
            good[e["mirror"]] = b
        else:
            bad.append(e["mirror"])
    if len(good) < 2:
        raise SystemExit(f"only {len(good)} intact shard(s) ({sorted(good)}); need 2")
    use = dict(sorted(good.items())[:2])
    data = decode_shards(use, m["cells"], m["size"])
    ok = sha256(data) == m["sha256"]
    with open(out, "wb") as f:
        f.write(data)
    return {"intact": sorted(good), "corrupt": bad, "used": sorted(use), "sha256_ok": ok,
            "sha256": sha256(data)}


def damage(d, k, seed=None):
    present = [r for r in range(NSHARDS) if os.path.exists(os.path.join(d, shard_name(r)))]
    kill = random.Random(seed).sample(present, min(k, len(present)))
    for r in kill:
        os.remove(os.path.join(d, shard_name(r)))
    return sorted(kill)


# ---------------------------------------------------------------- selftest

def selftest(nfiles=200, seed=20261025):
    # the proved facts, re-checked on the Python tables
    for r in range(NSHARDS):
        for v in range(64):
            assert sum(LABEL[r][w] == LABEL[r][v] for w in range(64)) == 8           # view_card
    for (r, s), table in DECODE.items():
        assert len(table) == 64                     # two_views_determine / two_views_realised
    rnd = random.Random(seed)
    for t in range(nfiles):
        data = bytes(rnd.randrange(256) for _ in range(rnd.choice([0, 1, 2, 3, 5, 7,
                                                                    rnd.randrange(4000)])))
        assert bytes_of(cells_of(data), len(data)) == data
        shards, ncell = encode_shards(data)
        assert all(2 * len(sh) <= len(data) + 6 for sh in shards)   # half size, up to padding
        for r in range(NSHARDS):
            for s in range(r + 1, NSHARDS):
                assert decode_shards({r: shards[r], s: shards[s]}, ncell, len(data)) == data
    print(f"archive selftest: ok ({nfiles} random files x all 36 shard pairs round-trip)")


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m hypercube.archive")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pack"); p.add_argument("file"); p.add_argument("--out", required=True)
    u = sub.add_parser("unpack"); u.add_argument("dir"); u.add_argument("--out", required=True)
    g = sub.add_parser("damage"); g.add_argument("dir"); g.add_argument("--shards", type=int, required=True)
    g.add_argument("--seed", type=int, default=None)
    sub.add_parser("selftest")
    a = ap.parse_args(argv)
    if a.cmd == "pack":
        m = pack_file(a.file, a.out)
        print(f"packed {m['name']}: {m['size']} bytes, sha256 {m['sha256']}")
        print(f"  9 shards x {m['shards'][0]['size']} bytes -> {a.out}/ (+ manifest.json)")
    elif a.cmd == "unpack":
        r = unpack_dir(a.dir, a.out)
        print(f"intact shards {r['intact']}, corrupt {r['corrupt']}, used {r['used']}")
        print(f"wrote {a.out}: sha256 {r['sha256']}  {'MATCH' if r['sha256_ok'] else 'MISMATCH'}")
        if not r["sha256_ok"]:
            raise SystemExit(1)
    elif a.cmd == "damage":
        print(f"destroyed shards {damage(a.dir, a.shards, a.seed)}")
    else:
        selftest()


if __name__ == "__main__":
    main(sys.argv[1:])
