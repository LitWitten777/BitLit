"""Self-healing store: mirror code (lose any 7 of 9 shards) x [6,3,3] code (fix 1 bit per word).

    python3 -m hypercube.store_heal pack <file> --out <dir>     9 shards + manifest.json
    python3 -m hypercube.store_heal unpack <dir> --out <file>   heal each shard, decode from 2
    python3 -m hypercube.store_heal damage <dir> --shards k [--flip 1]
                                                                delete k shards, flip bits in the rest
    python3 -m hypercube.store_heal selftest
    python3 -m hypercube.store_heal demo [<file>]                pack -> lose 7 -> flip 1 bit each -> unpack

Encoding of one 6-bit cell v: shard r stores the 6-bit codeword enc(label_r(v)), where
label_r(v) is the 3-bit view label of mirror r (hypercube.mirror) and enc is the [6,3,3] code of
manifold/heal.py.  Codewords are packed 4 per 3 bytes, so each shard has the size of the file
(9x in total) and every bit of a shard belongs to exactly one codeword.

Proved (Lean, RequestProject/HealMirror.lean, `healMirrorCorrect`): for any two different shards,
each codeword with at most one flipped bit, heal-then-mirror-decode returns the original cell.
A single flipped bit anywhere in a shard is one flip in one codeword, so it is covered.
Not proved: byte <-> cell packing, file format, manifest.  Two flips in one codeword are only
detected (`double_error_detected`), not corrected; the decoder may then return a wrong cell.
"""

import hashlib
import json
import os
import random
import sys

from . import archive as A
from .mirror import LABEL

NSHARDS = 9
FORMAT = "q6-heal-mirror-store/1"

GEN = (35, 21, 14)
CODE = [(35 if d & 1 else 0) ^ (21 if d & 2 else 0) ^ (14 if d & 4 else 0) for d in range(8)]
assert CODE == [0, 35, 21, 54, 14, 45, 27, 56]                     # Lean `code_eq`


def _dist(a, b):
    return bin(a ^ b).count("1")


def heal(v):
    """Lean `Manifold.Heal.heal`: first codeword at distance <= 1, else <= 2, else 0."""
    for lim in (1, 2):
        for d in range(8):
            if _dist(CODE[d], v) <= lim:
                return d
    return 0


ENC_TAB = [bytes(CODE[LABEL[r][v & 63]] for v in range(256)) for r in range(NSHARDS)]
HEAL_TAB = bytes(heal(v & 63) for v in range(256))
DIRTY_TAB = bytes(0 if (v & 63) in CODE else 1 for v in range(256))


def encode_shards(data):
    cells = A.cells_of(data)
    return [A.pack(cells.translate(ENC_TAB[r]), 6) for r in range(NSHARDS)], len(cells)


def heal_shard(sh, ncell):
    """Packed shard -> (3-bit labels, number of codewords that needed repair)."""
    words = A.unpack(sh, 6, ncell)
    return words.translate(HEAL_TAB), sum(words.translate(DIRTY_TAB))


def decode_shards(shards, ncell, size):
    """shards: dict mirror -> packed shard (any 2 used, after healing)."""
    (r, X), (s, Y) = sorted(shards.items())[:2]
    a, _ = heal_shard(X, ncell)
    b, _ = heal_shard(Y, ncell)
    return A.bytes_of(A.decode_labels(r, a, s, b), size)


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def shard_name(r):
    return f"shard_{r}.q6h"


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
    m = {"format": FORMAT, "name": os.path.basename(path), "size": len(data), "sha256": sha256(data),
         "cells": ncell, "shards": entries,
         "rule": "any 2 shards, each codeword with <= 1 flipped bit, restore the file "
                 "(Lean: healMirrorCorrect)"}
    with open(os.path.join(out, "manifest.json"), "w") as f:
        json.dump(m, f, indent=2)
    return m


def unpack_dir(d, out):
    with open(os.path.join(d, "manifest.json")) as f:
        m = json.load(f)
    present, clean = {}, []
    for e in m["shards"]:
        p = os.path.join(d, e["file"])
        if os.path.exists(p):
            with open(p, "rb") as f:
                b = f.read()
            if len(b) == e["size"]:
                present[e["mirror"]] = b
                if sha256(b) == e["sha256"]:
                    clean.append(e["mirror"])
    if len(present) < 2:
        raise SystemExit(f"only {len(present)} shard(s) present; need 2")
    order = sorted(present, key=lambda r: (r not in clean, r))[:2]   # prefer untouched shards
    repaired = {r: heal_shard(present[r], m["cells"])[1] for r in order}
    data = decode_shards({r: present[r] for r in order}, m["cells"], m["size"])
    with open(out, "wb") as f:
        f.write(data)
    return {"present": sorted(present), "checksum_ok": sorted(clean), "used": order,
            "repaired_words": repaired, "sha256": sha256(data), "sha256_ok": sha256(data) == m["sha256"]}


def flip_bit(path, rnd):
    with open(path, "rb") as f:
        b = bytearray(f.read())
    if not b:
        return None
    i = rnd.randrange(8 * len(b))
    b[i // 8] ^= 1 << (i % 8)
    with open(path, "wb") as f:
        f.write(b)
    return i


def damage(d, k, flip=0, seed=None):
    rnd = random.Random(seed)
    present = [r for r in range(NSHARDS) if os.path.exists(os.path.join(d, shard_name(r)))]
    kill = sorted(rnd.sample(present, min(k, len(present))))
    for r in kill:
        os.remove(os.path.join(d, shard_name(r)))
    flips = {}
    for r in present:
        if r not in kill:
            flips[r] = [flip_bit(os.path.join(d, shard_name(r)), rnd) for _ in range(flip)]
    return kill, flips


def _flip(sh, rnd, nbits):
    b = bytearray(sh)
    for i in rnd.sample(range(8 * len(b)), min(nbits, 8 * len(b))):
        b[i // 8] ^= 1 << (i % 8)
    return bytes(b)


def _flip_every_word(sh, ncell, rnd):
    """One random flipped bit in every codeword of a shard (the full guarantee)."""
    words = bytearray(A.unpack(sh, 6, ncell))
    for i in range(len(words)):
        words[i] ^= 1 << rnd.randrange(6)
    return A.pack(bytes(words), 6)[:len(sh)]


def selftest(nfiles=200, seed=20261025):
    for d in range(8):                                            # Lean `heal_single_error`
        assert heal(CODE[d]) == d and all(heal(CODE[d] ^ (1 << i)) == d for i in range(6))
    from manifold import heal as MH
    assert all(MH.heal(v)[0] == heal(v) for v in range(64))       # same decoder as manifold/heal.py
    for r in range(NSHARDS):                                      # the composed finite check
        for s in range(NSHARDS):
            if r == s:
                continue
            for v in range(64):
                for i in range(-1, 6):
                    for j in range(-1, 6):
                        x = CODE[LABEL[r][v]] ^ (1 << i if i >= 0 else 0)
                        y = CODE[LABEL[s][v]] ^ (1 << j if j >= 0 else 0)
                        assert A.DECODE[(r, s)][(heal(x), heal(y))] == v
    rnd = random.Random(seed)
    runs = 0
    for _ in range(nfiles):
        data = bytes(rnd.randrange(256) for _ in range(rnd.randrange(1, 3000)))
        shards, ncell = encode_shards(data)
        for lost in range(8):
            keep = rnd.sample(range(NSHARDS), NSHARDS - lost)
            for nflip in (0, 1):
                surv = {r: _flip(shards[r], rnd, nflip) for r in keep}
                pair = dict(rnd.sample(sorted(surv.items()), 2))
                assert decode_shards(pair, ncell, len(data)) == data
                runs += 1
        r, s = rnd.sample(range(NSHARDS), 2)                      # one flip in EVERY codeword
        pair = {r: _flip_every_word(shards[r], ncell, rnd), s: _flip_every_word(shards[s], ncell, rnd)}
        assert decode_shards(pair, ncell, len(data)) == data
        runs += 1
    print(f"store_heal selftest: ok (finite check 72 ordered pairs x 64 cells x 7 x 7 error patterns; "
          f"{runs} file round trips: {nfiles} files x 0..7 lost shards x 0/1 flipped bit per survivor, "
          f"plus 1 flip in every codeword of 2 shards)")


def demo(path="sources/bible.tar.lzma", out="/tmp/q6heal", seed=7):
    import shutil
    shutil.rmtree(out, ignore_errors=True)
    m = pack_file(path, out)
    print(f"packed {m['name']}: {m['size']} bytes, sha256 {m['sha256']}; 9 shards x {m['shards'][0]['size']} bytes")
    kill, flips = damage(out, 7, flip=1, seed=seed)
    print(f"lost shards {kill}; flipped bit (bit index) in survivors: {flips}")
    r = unpack_dir(out, out + ".restored")
    print(f"used shards {r['used']}, checksum-clean before healing: {r['checksum_ok']}, "
          f"repaired codewords: {r['repaired_words']}")
    print(f"restored sha256 {r['sha256']}  {'MATCH' if r['sha256_ok'] else 'MISMATCH'}")
    return r["sha256_ok"]


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m hypercube.store_heal")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pack"); p.add_argument("file"); p.add_argument("--out", required=True)
    u = sub.add_parser("unpack"); u.add_argument("dir"); u.add_argument("--out", required=True)
    g = sub.add_parser("damage"); g.add_argument("dir"); g.add_argument("--shards", type=int, required=True)
    g.add_argument("--flip", type=int, default=0); g.add_argument("--seed", type=int, default=None)
    sub.add_parser("selftest")
    dm = sub.add_parser("demo"); dm.add_argument("file", nargs="?", default="sources/bible.tar.lzma")
    a = ap.parse_args(argv)
    if a.cmd == "pack":
        m = pack_file(a.file, a.out)
        print(f"packed {m['name']}: {m['size']} bytes -> 9 shards x {m['shards'][0]['size']} bytes in {a.out}/")
    elif a.cmd == "unpack":
        r = unpack_dir(a.dir, a.out)
        print(json.dumps(r, indent=1))
        if not r["sha256_ok"]:
            raise SystemExit(1)
    elif a.cmd == "damage":
        kill, flips = damage(a.dir, a.shards, a.flip, a.seed)
        print(f"deleted {kill}; flipped bits {flips}")
    elif a.cmd == "demo":
        if not demo(a.file):
            raise SystemExit(1)
    else:
        selftest()


if __name__ == "__main__":
    main(sys.argv[1:])
