"""The mirror code: 9 GF(8) Hopf fibres of Q6 as a "lose any 7 of 9" storage code.

Each GF(8) fibre W_r (r = 0..8, plus the zero cell) is a 3-dim XOR subspace of the 64 cells.
Mirror r sees a cell v only up to W_r: its *view* is the coset v ^ W_r, i.e. 3 of the 6 bits.
Any two different mirrors see complementary halves, so any 2 views recover v exactly.

Proved counterparts (Lean, RequestProject/MirrorCode.lean, namespace HypercubeHopf):
  view_card            one view leaves exactly 8 candidates
  two_views_determine  two views from different mirrors determine the cell
  two_views_realised   every pair of views (one per mirror) comes from exactly one cell
The byte <-> 6-bit packing and the file format below are ordinary code, not proved.

Usage:  python3 -m hypercube.mirror selftest
        python3 -m hypercube.mirror demo "some text"
Standard library only.
"""

import os
import random
import sys

from .hopf import fiber

W = [frozenset([0] + fiber(9, r)) for r in range(9)]  # the 9 mirrors (3-dim subspaces)


def _coset_labels(r):
    """label[v] in 0..7: which coset of W_r contains v (cosets numbered by smallest element)."""
    reps = sorted({min(v ^ w for w in W[r]) for v in range(64)})
    return {v: reps.index(min(v ^ w for w in W[r])) for v in range(64)}


LABEL = [_coset_labels(r) for r in range(9)]
# DECODE[(r, s)][(a, b)] = the unique cell with label a in mirror r and label b in mirror s
DECODE = {(r, s): {(LABEL[r][v], LABEL[s][v]): v for v in range(64)}
          for r in range(9) for s in range(9) if r != s}


def encode_cell(v):
    """The 9 three-bit shares of a 6-bit cell."""
    return [LABEL[r][v] for r in range(9)]


def decode_cell(shares):
    """shares: dict mirror -> 3-bit label; needs any 2 mirrors."""
    (r, a), (s, b) = list(shares.items())[:2]
    return DECODE[(r, s)][(a, b)]


def _cells(data):
    bits = "".join(f"{x:08b}" for x in data)
    bits += "0" * (-len(bits) % 6)
    return [int(bits[i:i + 6], 2) for i in range(0, len(bits), 6)]


def _bytes(cells, n):
    bits = "".join(f"{c:06b}" for c in cells)
    return bytes(int(bits[i:i + 8], 2) for i in range(0, 8 * n, 8))


def encode(data):
    """bytes -> 9 share streams (lists of 3-bit labels).  Each stream is half the data size."""
    cells = _cells(data)
    return [[LABEL[r][v] for v in cells] for r in range(9)], len(data)


def decode(streams, n):
    """streams: dict mirror -> share stream (any 2 suffice); n: original byte length."""
    (r, A), (s, B) = list(streams.items())[:2]
    table = DECODE[(r, s)]
    return _bytes([table[(a, b)] for a, b in zip(A, B)], n)


def selftest():
    # the three proved facts, re-checked exhaustively on the Python tables
    for r in range(9):
        for v in range(64):
            assert sum(LABEL[r][w] == LABEL[r][v] for w in range(64)) == 8      # view_card
    for (r, s), table in DECODE.items():
        assert len(table) == 64                     # two_views_determine + two_views_realised
        for v in range(64):
            assert decode_cell({r: LABEL[r][v], s: LABEL[s][v]}) == v
    rnd = random.Random(0)
    for _ in range(200):
        data = os.urandom(rnd.randrange(0, 200))
        streams, n = encode(data)
        keep = rnd.sample(range(9), 2)
        assert decode({k: streams[k] for k in keep}, n) == data
    print("mirror selftest: ok (9 mirrors, 36 mirror pairs x 64 cells, 200 random round trips)")


def demo(text):
    data = text.encode()
    streams, n = encode(data)
    keep = random.sample(range(9), 2)
    print(f"{n} bytes -> 9 mirrors x {len(streams[0])} three-bit shares "
          f"(each mirror holds half the data; total 4.5x)")
    print(f"destroyed mirrors {sorted(set(range(9)) - set(keep))}, kept {sorted(keep)}")
    print("recovered:", decode({k: streams[k] for k in keep}, n).decode())


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if cmd == "demo":
        demo(" ".join(sys.argv[2:]) or "In the beginning")
    else:
        selftest()
