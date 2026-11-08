#!/usr/bin/env python3
"""
Measure the two numbers that decide whether chunking and Kelly allocation pay off.

A. Chunked phase vs reconstruction phase of the scheduler (per braid):
   chunk map (parallelisable), merge (⌈log₂ k⌉ rounds), and the reconstruction of
   the non-homomorphic channels (Garside NF, linking, Jones values on the whole
   word; resonance pattern from the combined Burau matrix).  Reports the share
   of the reconstruction with 1 and with W workers for the chunk map.

B. Kelly-allocated graduated prover vs the plain verdict on claim streams:
   wall time, fold runs and which channel decided.

Usage:
  PYTHONPATH=src python3 scripts/bench_scheduler.py [--quick] [--workers W] [--csv FILE]

Single-threaded; run it on an otherwise idle machine.  Timings are wall-clock
measurements of this implementation on this machine, not proved facts.
"""

from __future__ import annotations

import argparse
import platform
import random
import time

from qbx_ir import Braid
from qbx_ir.algebra.kelly_scheduler import KellyMultiProver, timed_scheduled_reading
from qbx_ir.algebra.multiprover import verdict


def random_word(rng, n, length):
    return [rng.choice([i for i in range(-(n - 1), n) if i != 0]) for _ in range(length)]


def equal_variant(rng, n, word):
    w = list(word)
    for _ in range(3):
        i = rng.randrange(0, len(w) + 1)
        g = rng.randrange(1, n)
        w[i:i] = [g, -g]
    if n >= 3:
        i = rng.randrange(0, len(w) + 1)
        w[i:i] = [1, 2, 1, -2, -1, -2]
    return w


def part_a(sizes, chunk, workers, rows):
    print(f"## A. Chunked phase vs reconstruction (chunk size {chunk})\n")
    print("| n | L | chunks | map s | max chunk s | merge s | fold s | link s | osc s | harm s "
          f"| recon share (1 core) | recon share ({workers} cores) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    rng = random.Random(1)
    for n, L in sizes:
        b = Braid.from_short_form(n, random_word(rng, n, L))
        t = timed_scheduled_reading(b, chunk)
        r = t.reconstruct
        f1, fw = t.reconstruct_fraction(1), t.reconstruct_fraction(workers)
        print(f"| {n} | {L} | {t.chunks} | {t.chunk_map:.3f} | {t.chunk_max:.3f} | {t.merge:.3f} "
              f"| {r['fold']:.3f} | {r['link']:.4f} | {r['oscillator']:.3f} | {r['harmonic']:.3f} "
              f"| {100 * f1:.0f}% | {100 * fw:.0f}% |", flush=True)
        rows.append(("A", n, L, t.chunks, t.chunk_map, t.chunk_max, t.merge, r["fold"], r["link"],
                     r["oscillator"], r["harmonic"], f1, fw))
    print()


def part_b(streams, rows):
    print("## B. Kelly-allocated graduated prover vs plain verdict\n")
    print("| stream | claims | plain s | Kelly s | speed-up | fold runs | decided by |")
    print("|---|---|---|---|---|---|---|")
    for name, n, L, count, p_true in streams:
        rng = random.Random(hash(name) & 0xFFFF)
        claims = []
        for _ in range(count):
            w = random_word(rng, n, L)
            if rng.random() < p_true:
                claims.append((Braid.from_short_form(n, w),
                               Braid.from_short_form(n, equal_variant(rng, n, w))))
            else:
                claims.append((Braid.from_short_form(n, w),
                               Braid.from_short_form(n, random_word(rng, n, L))))
        t0 = time.perf_counter()
        plain = [verdict(a, b).verdict for a, b in claims]
        t_plain = time.perf_counter() - t0
        prover = KellyMultiProver()
        by = {}
        t0 = time.perf_counter()
        kelly = []
        for a, b in claims:
            r = prover.decide(a, b)
            kelly.append(r.verdict)
            by[r.decided_by] = by.get(r.decided_by, 0) + 1
        t_kelly = time.perf_counter() - t0
        assert kelly == plain, "graduated answers must equal the verdict"
        dec = ", ".join(f"{k} {v}" for k, v in sorted(by.items()))
        print(f"| {name} | {count} | {t_plain:.2f} | {t_kelly:.2f} | {t_plain / t_kelly:.1f}× "
              f"| {prover.fold_runs} | {dec} |", flush=True)
        rows.append(("B", name, n, L, count, t_plain, t_kelly, prover.fold_runs, dec))
    print()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--chunk", type=int, default=64)
    ap.add_argument("--csv")
    args = ap.parse_args()
    print(f"python {platform.python_version()} on {platform.machine()}, "
          f"{time.strftime('%Y-%m-%d')}\n")
    if args.quick:
        sizes = [(3, 200), (4, 200)]
        streams = [("mixed n=3 L=60", 3, 60, 10, 0.5)]
    else:
        sizes = [(3, 200), (3, 800), (3, 1600), (4, 200), (4, 800), (4, 1600),
                 (5, 200), (5, 800)]
        streams = [
            ("false claims n=3 L=150", 3, 150, 30, 0.0),
            ("true claims n=3 L=150", 3, 150, 30, 1.0),
            ("mixed n=3 L=150", 3, 150, 30, 0.5),
            ("mixed n=4 L=150", 4, 150, 30, 0.5),
        ]
    rows = []
    part_a(sizes, args.chunk, args.workers, rows)
    part_b(streams, rows)
    if args.csv:
        with open(args.csv, "w") as fh:
            for r in rows:
                fh.write(",".join(str(x) for x in r) + "\n")


if __name__ == "__main__":
    main()
