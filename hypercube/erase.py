"""Selective erasure with sedenion zero divisors (a deliberately LOSSY, irreversible filter).

    python3 -m hypercube.erase list                              the 84 two-term zero divisors
    python3 -m hypercube.erase notch <in> <out> --zd <index> [--side left|right]
    python3 -m hypercube.erase selftest

Each 16-byte frame y (bytes 0..255 as integer coordinates) is a sedenion; `notch` replaces it by
x * y (or y * x with --side right), where x = e_i + s e_j is zero divisor #index of the census in
`manifold.cd.zero_divisor_census(4)`.  Output coordinates lie in [-510, 510] and are written as
int16 (little-endian) after a one-line JSON header, so the output is twice the input size.

What happens to a frame (measured for all 84, see `selftest`):
* the 4-dimensional kernel ker(L_x) = {y : x y = 0} is destroyed: its component cannot be
  recovered from x y by any method (frames differing by a kernel vector give the same output);
* nothing else is lost: L_x has rank 12, its non-zero singular values are sqrt(2) (8 times) and
  2 (4 times), so the component of y orthogonal to the kernel is recovered exactly by the
  pseudo-inverse.
Use it only when irreversible deletion of one 4-D sector per 16-D frame is wanted.

Proved (Lean, RequestProject/Manifold/CDTower.lean): the census -- 84 two-term zero divisors,
42 assessors, 336 annihilating pairs, each killing exactly 4 two-term elements (`each_kills_four`).
Measured, not proved: the kernel dimension 4 / rank 12 / singular values for every one of the 84,
and the loss figures on actual data.  Needs numpy.
"""

import json
import sys
from functools import lru_cache

import numpy as np

from manifold import cd

MAGIC = b"ZDN1\n"


@lru_cache(maxsize=1)
def census():
    return tuple(cd.zero_divisor_census(4)["list"])


def zd(index):
    i, j, s = census()[index]
    return cd.two_term(4, i, j, s), (i, j, s)


def mult_matrix(x, side="left"):
    """M with M @ y = x*y (left) or y*x (right), from the actual CD product."""
    cols = [cd.mul(x, cd.basis(4, k)) if side == "left" else cd.mul(cd.basis(4, k), x) for k in range(16)]
    return np.array(cols, dtype=np.int64).T


def kernel_basis(M, tol=1e-9):
    _, sv, Vt = np.linalg.svd(M.astype(float))
    return Vt[sv < tol] if len(sv) == 16 else Vt[len(sv):]


def analyse(M):
    sv = np.linalg.svd(M.astype(float), compute_uv=False)
    rank = int((sv > 1e-9).sum())
    return rank, sorted(np.round(sv ** 2, 9).tolist())


def frames_of(data):
    pad = -len(data) % 16
    return np.frombuffer(data + bytes(pad), dtype=np.uint8).astype(np.int64).reshape(-1, 16)


def notch(data, index, side="left"):
    x, ijs = zd(index)
    M = mult_matrix(x, side)
    Y = frames_of(data)
    Z = Y @ M.T
    K = kernel_basis(M)
    Yc = Y.astype(float)
    dropped = Yc @ K.T @ K                                   # component in ker(L_x): destroyed
    kept = Yc - dropped
    rec = Z.astype(float) @ np.linalg.pinv(M.astype(float)).T
    stats = {"zd_index": index, "zd": f"e{ijs[0]} {'+' if ijs[2] > 0 else '-'} e{ijs[1]}", "side": side,
             "frames": int(len(Y)), "rank_of_map": analyse(M)[0],
             "rank_of_output_frames": int(np.linalg.matrix_rank(Z.astype(float))) if len(Z) else 0,
             "energy_dropped_fraction": float((dropped ** 2).sum() / max(1e-12, (Yc ** 2).sum())),
             "kept_part_recovered_exactly": bool(np.allclose(rec, kept, atol=1e-6))}
    head = json.dumps({"size": len(data), **stats}).encode()
    return MAGIC + head + b"\n" + Z.astype("<i2").tobytes(), stats


def selftest(seed=20261025):
    rng = np.random.default_rng(seed)
    zds = census()
    assert len(zds) == 84                                   # Lean `two_term_zero_divisor_count`
    spectra = set()
    for idx in range(84):
        x, _ = zd(idx)
        for side in ("left", "right"):
            M = mult_matrix(x, side)
            rank, sv2 = analyse(M)
            assert rank == 12, (idx, side, rank)            # dropped = 16 - 12 = 4 dimensions
            spectra.add(tuple(sv2))
            K = kernel_basis(M)
            assert K.shape == (4, 16) and np.allclose(K @ M.T, 0)
            Y = rng.integers(0, 256, (200, 16)).astype(float)
            kept = Y - Y @ K.T @ K
            rec = (Y @ M.T) @ np.linalg.pinv(M.astype(float)).T
            assert np.allclose(rec, kept, atol=1e-6)          # no other loss
            assert np.allclose((Y + 37.0 * K[0]) @ M.T, Y @ M.T)  # the kernel part is unrecoverable
    assert spectra == {tuple([0.0] * 4 + [2.0] * 8 + [4.0] * 4)}
    print("erase selftest: ok -- all 84 zero divisors, left and right: rank 12, dropped exactly 4 "
          "dimensions, squared singular values 0^4 2^8 4^4; the other 12 dimensions recovered exactly "
          "by the pseudo-inverse (200 random frames each); kernel shifts are invisible in the output")


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m hypercube.erase")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list")
    n = sub.add_parser("notch"); n.add_argument("inp"); n.add_argument("out")
    n.add_argument("--zd", type=int, required=True); n.add_argument("--side", default="left", choices=["left", "right"])
    sub.add_parser("selftest")
    a = ap.parse_args(argv)
    if a.cmd == "list":
        for k, (i, j, s) in enumerate(census()):
            print(k, f"e{i} {'+' if s > 0 else '-'} e{j}")
    elif a.cmd == "notch":
        data = open(a.inp, "rb").read()
        blob, st = notch(data, a.zd, a.side)
        open(a.out, "wb").write(blob)
        print(json.dumps(st, indent=1))
    else:
        selftest()


if __name__ == "__main__":
    main(sys.argv[1:])
