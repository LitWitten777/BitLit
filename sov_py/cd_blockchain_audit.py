
#!/usr/bin/env python3
"""
blockchain_cd_audit.py — Charge-sector and Ramanujan-mixing audit of Bitcoin mainnet blocks.

Tests whether the Cayley-Dickson tower structure is physically realized in
blockchain consensus dynamics. Three tests:

  1. Charge-sector classification: project each block to a 16D sedenion state,
     compute XOR charge, check for clustering.
  2. Ramanujan mixing rate: transition matrix between charge sectors, compare
     spectral gap to the Ramanujan prediction (λ₂/d = 1/2 for D=16).
  3. ζ-trajectory: plot sedenion zero-divisor distance over known events.

Usage:
  python blockchain_cd_audit.py /path/to/blocks/
  python blockchain_cd_audit.py data/blockchain/blocks (configure symlink)/ --epoch all

If no path is given, runs in synthetic mode with random states to verify
the pipeline.
"""

from __future__ import annotations

import argparse
import hashlib
import struct
import sys
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

# ---------------------------------------------------------------------------
# Sedenion utilities (minimal, self-contained)
# ---------------------------------------------------------------------------

# 16x16 sign table for the CD tower at level 4 (sedenions).
# epsNeg(a, b) = sign such that e_a · e_b = epsNeg(a,b) · e_{a ^ b}
# Computed by the recursive doubling rule.

def _eps_neg(n: int, a: int, b: int) -> int:
    """Sign factor for e_a · e_b in the CD algebra of dimension 2^n.
    Returns +1 or -1. a, b < 2^n."""
    if a == 0:
        return 1
    if b == 0:
        return 1
    if a == b:
        return -1
    # Recursive doubling: split indices at the top bit
    half = 1 << (n - 1)
    a_hi = (a & half) >> (n - 1)
    b_hi = (b & half) >> (n - 1)
    a_lo = a & (half - 1)
    b_lo = b & (half - 1)
    if a_hi == 0 and b_hi == 0:
        return _eps_neg(n - 1, a_lo, b_lo)
    if a_hi == 0 and b_hi == 1:
        return _eps_neg(n - 1, a_lo, b_lo)
    if a_hi == 1 and b_hi == 0:
        # (0, x) · (y, 0) = (0, x · y) with sign from the conjugate
        return -_eps_neg(n - 1, a_lo, b_lo) if b_lo != 0 else 1
    if a_hi == 1 and b_hi == 1:
        # (0, x) · (0, y) = (-y · x, 0)
        return -_eps_neg(n - 1, b_lo, a_lo)
    return 1


def sedenion_product(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Product of two sedenions (16-dim vectors)."""
    assert a.shape == (16,) and b.shape == (16,)
    out = np.zeros(16, dtype=np.int64)
    for i in range(16):
        if a[i] == 0:
            continue
        for j in range(16):
            if b[j] == 0:
                continue
            k = i ^ j
            sign = _eps_neg(4, i, j)
            out[k] += sign * a[i] * b[j]
    return out


def xor_charge(v: np.ndarray) -> int:
    """The XOR charge of a cross-half sedenion state.

    For a cross-half state v = s1 e_i + s2 e_{8+j}, the charge is i ^ j.
    For general states, we compute the charge of the dominant cross-half
    component.
    """
    # Find the two largest-magnitude indices
    idx = np.argsort(np.abs(v))[::-1]
    i_candidates = [k for k in idx if k < 8]
    j_candidates = [k for k in idx if k >= 8]
    if not i_candidates or not j_candidates:
        return 0
    i = i_candidates[0]
    j = j_candidates[0] - 8
    return i ^ j


# Zero-divisor basis (168 vectors for the D=16 cross-octet ZD locus)
# Precomputed from HYP-001/HYP-002. For the audit, we use a fast check
# against the algebraic criterion.

def is_zero_divisor_pair(u: np.ndarray, w: np.ndarray) -> bool:
    """Check whether u · w = 0 in the sedenion algebra."""
    return bool(np.all(sedenion_product(u, w) == 0))


def zd_distance(v: np.ndarray, zd_basis: np.ndarray) -> float:
    """Minimum algebraic distance from v to the zero-divisor locus.

    ζ = min_{W ∈ ZD} ||v · W|| / (||v|| · ||W||)
    """
    v = v.astype(np.int64)
    if not np.any(v):
        return 0.0
    best = float("inf")
    for w in zd_basis:
        prod = sedenion_product(v, w)
        num = np.linalg.norm(prod)
        den = np.linalg.norm(v) * np.linalg.norm(w)
        if den > 0:
            best = min(best, num / den)
    return float(best)


def build_zd_basis() -> np.ndarray:
    """Build the 168 cross-half sedenion zero divisors.

    A cross-half vector v = s1 e_i + s2 e_{8+j} is a zero divisor iff
    i ≠ 0, j ≠ 0, i ≠ j (HYP-001 / HYP-049).
    """
    basis = []
    for i in range(1, 8):
        for j in range(1, 8):
            if i == j:
                continue
            for s1 in (1, -1):
                for s2 in (1, -1):
                    v = np.zeros(16, dtype=np.int64)
                    v[i] = s1
                    v[8 + j] = s2
                    basis.append(v)
    return np.array(basis, dtype=np.int64)


# ---------------------------------------------------------------------------
# Bitcoin block parsing (minimal)
# ---------------------------------------------------------------------------

def parse_block_header(raw: bytes) -> dict:
    """Parse a Bitcoin block header (80 bytes)."""
    if len(raw) < 80:
        return {}
    version = struct.unpack("<I", raw[0:4])[0]
    prev_hash = raw[4:36][::-1].hex()
    merkle_root = raw[36:68][::-1].hex()
    timestamp = struct.unpack("<I", raw[68:72])[0]
    bits = struct.unpack("<I", raw[72:76])[0]
    nonce = struct.unpack("<I", raw[76:80])[0]
    return {
        "version": version,
        "prev_hash": prev_hash,
        "merkle_root": merkle_root,
        "timestamp": timestamp,
        "bits": bits,
        "nonce": nonce,
        "header_hash": hashlib.sha256(
            hashlib.sha256(raw[:80]).digest()
        ).hexdigest(),
    }


def block_to_sedenion(header: dict) -> np.ndarray:
    """Lift a block header to a 16D sedenion state.

    The mapping is a modeling choice. We use:
      - i, j indices: the first 2 bytes of the header hash (mod 7, +1)
      - sign: the parity of the nonce
      - amplitude: the timestamp modulo a small integer
    """
    h = header.get("header_hash", "0" * 64)
    # Take the first 4 bytes of the hash for the index
    b0 = int(h[0:2], 16) % 7 + 1
    b1 = int(h[2:4], 16) % 7 + 1
    if b1 == b0:
        b1 = (b1 % 7) + 1
    s1 = 1 if header.get("nonce", 0) % 2 == 0 else -1
    s2 = 1 if (header.get("version", 1) & 1) == 1 else -1
    amp = 1 + (header.get("timestamp", 0) % 3)
    v = np.zeros(16, dtype=np.int64)
    v[b0] = s1 * amp
    v[8 + b1] = s2 * amp
    return v


def read_blocks_from_file(path: Path, limit: int = 10000) -> list[dict]:
    """Read Bitcoin block headers from a blk*.dat file."""
    blocks = []
    try:
        with open(path, "rb") as f:
            # Bitcoin block files use a magic prefix 0xF9BEB4D9 for mainnet
            magic = b"\xf9\xbe\xb4\xd9"
            data = f.read()
            pos = 0
            while len(blocks) < limit:
                idx = data.find(magic, pos)
                if idx == -1:
                    break
                # Read the 4-byte length, then the block
                if idx + 8 > len(data):
                    break
                size = struct.unpack("<I", data[idx + 4 : idx + 8])[0]
                if idx + 8 + size > len(data):
                    break
                block_raw = data[idx + 8 : idx + 8 + size]
                header = parse_block_header(block_raw[:80])
                if header:
                    blocks.append(header)
                pos = idx + 8 + size
    except Exception as e:
        print(f"  Error reading {path}: {e}")
    return blocks


# ---------------------------------------------------------------------------
# Test 1 — Charge-sector classification
# ---------------------------------------------------------------------------

def audit_charge_distribution(states: list[np.ndarray]) -> dict:
    print("=" * 68)
    print("[1] Charge-sector distribution")
    print("=" * 68)

    charges = [xor_charge(v) for v in states]
    counter = Counter(charges)

    print(f"  Total states: {len(states)}")
    print(f"  Charge distribution:")
    for chi in sorted(counter):
        pct = 100 * counter[chi] / len(states)
        bar = "#" * int(pct / 2)
        print(f"    χ = {chi:2d}: {counter[chi]:5d} ({pct:5.1f}%)  {bar}")

    # Uniformity test: chi-squared against uniform over non-zero charges
    nonzero_counts = [counter.get(chi, 0) for chi in range(1, 8)]
    expected = sum(nonzero_counts) / 7
    chi2 = sum((c - expected) ** 2 / expected for c in nonzero_counts if expected > 0)
    print(f"\n  χ² against uniform over {{1..7}}: {chi2:.2f}")
    print(f"  (critical value at p=0.05, df=6: 12.59)")

    structured = chi2 > 12.59
    print(f"  {'STRUCTURED' if structured else 'CONSISTENT WITH UNIFORM'}")

    return {
        "counts": dict(counter),
        "chi2": float(chi2),
        "structured": structured,
    }


# ---------------------------------------------------------------------------
# Test 2 — Ramanujan mixing rate
# ---------------------------------------------------------------------------

def audit_ramanujan_mixing(states: list[np.ndarray]) -> dict:
    print()
    print("=" * 68)
    print("[2] Ramanujan mixing rate")
    print("=" * 68)

    charges = [xor_charge(v) for v in states if xor_charge(v) != 0]
    if len(charges) < 100:
        print("  Not enough non-zero charge transitions")
        return {"error": "insufficient data"}

    # Build 7x7 transition matrix over consecutive non-zero charges
    T = np.zeros((7, 7))
    for i in range(len(charges) - 1):
        a = charges[i] - 1  # 1..7 → 0..6
        b = charges[i + 1] - 1
        if 0 <= a < 7 and 0 <= b < 7:
            T[a, b] += 1

    # Row-normalize
    row_sums = T.sum(axis=1, keepdims=True)
    T_norm = np.where(row_sums > 0, T / row_sums, 0)

    # Eigenvalues
    eigs = np.sort(np.abs(np.linalg.eigvals(T_norm)))[::-1]
    print(f"  Transition matrix eigenvalues (|λ|):")
    for i, lam in enumerate(eigs):
        print(f"    λ_{i} = {lam:.4f}")

    # The Ramanujan prediction for the 8-regular Ramanujan graph:
    # λ₂ / d = 4 / 8 = 0.5
    predicted_ratio = 0.5
    actual_ratio = eigs[1] if len(eigs) > 1 else float("nan")
    print(f"\n  Ramanujan prediction: λ₂ / d = 4 / 8 = {predicted_ratio:.4f}")
    print(f"  Observed λ₂: {actual_ratio:.4f}")

    if not np.isnan(actual_ratio):
        deviation = abs(actual_ratio - predicted_ratio)
        matches = deviation < 0.15
        print(f"  Deviation from prediction: {deviation:.4f}")
        print(f"  {'MATCHES Ramanujan prediction' if matches else 'DOES NOT match'}")

    return {
        "eigenvalues": eigs.tolist(),
        "predicted": predicted_ratio,
        "observed_lambda2": float(actual_ratio),
        "matches": bool(matches) if not np.isnan(actual_ratio) else False,
    }


# ---------------------------------------------------------------------------
# Test 3 — ζ trajectory
# ---------------------------------------------------------------------------

def audit_zeta_trajectory(
    states: list[np.ndarray], zd_basis: np.ndarray, window: int = 50
) -> dict:
    print()
    print("=" * 68)
    print("[3] ζ trajectory (zero-divisor distance)")
    print("=" * 68)

    zetas = []
    for v in states:
        zetas.append(zd_distance(v, zd_basis))

    zetas = np.array(zetas)
    print(f"  ζ statistics:")
    print(f"    min:  {zetas.min():.4f}")
    print(f"    max:  {zetas.max():.4f}")
    print(f"    mean: {zetas.mean():.4f}")
    print(f"    std:  {zetas.std():.4f}")

    # Check for zero-divisor proximity events
    low_zeta_events = np.sum(zetas < 0.1)
    print(f"  ζ < 0.1 events: {low_zeta_events} / {len(zetas)}")

    # Check for ζ = 0 (exact zero divisor)
    exact_zd = np.sum(zetas == 0)
    print(f"  ζ = 0 events: {exact_zd}")

    # Sample the trajectory for visualization
    n_samples = min(20, len(zetas))
    sample_indices = np.linspace(0, len(zetas) - 1, n_samples, dtype=int)
    print(f"\n  ζ trajectory (sampled):")
    for idx in sample_indices:
        bar = "#" * int(zetas[idx] * 40)
        print(f"    block {idx:5d}: ζ = {zetas[idx]:.4f}  {bar}")

    return {
        "min": float(zetas.min()),
        "max": float(zetas.max()),
        "mean": float(zetas.mean()),
        "std": float(zetas.std()),
        "low_zeta_events": int(low_zeta_events),
        "exact_zd": int(exact_zd),
    }


# ---------------------------------------------------------------------------
# Synthetic mode
# ---------------------------------------------------------------------------

def synthetic_states(n: int = 1000) -> list[np.ndarray]:
    """Generate synthetic sedenion states for pipeline verification."""
    rng = np.random.default_rng(42)
    states = []
    for _ in range(n):
        i = rng.integers(1, 8)
        j = rng.integers(1, 8)
        if i == j:
            j = (j % 7) + 1
        s1 = rng.choice([-1, 1])
        s2 = rng.choice([-1, 1])
        v = np.zeros(16, dtype=np.int64)
        v[i] = s1
        v[8 + j] = s2
        states.append(v)
    return states


# ---------------------------------------------------------------------------
# Epoch Definitions
# ---------------------------------------------------------------------------

EPOCHS = {
    "genesis": {
        "name": "Genesis / Early (2009-2012)",
        "ts_min": 1230950400,
        "ts_max": 1354116000,
        "sample_files": ["blk00000.dat", "blk00001.dat"],
    },
    "halving1": {
        "name": "Halving 1 (2012-2016)",
        "ts_min": 1354116000,
        "ts_max": 1468080000,
        "sample_files": ["blk00400.dat", "blk00500.dat"],
    },
    "segwit": {
        "name": "Halving 2 / SegWit (2016-2020)",
        "ts_min": 1468080000,
        "ts_max": 1589212800,
        "sample_files": ["blk00900.dat", "blk01000.dat"],
    },
    "ordinals": {
        "name": "Halving 3 / Ordinals / Taproot (2020-2024)",
        "ts_min": 1589212800,
        "ts_max": 1713571200,
        "sample_files": ["blk02800.dat", "blk03000.dat"],
    },
}


def classify_epoch(timestamp: int) -> str:
    for ep_key, ep in EPOCHS.items():
        if ep["ts_min"] <= timestamp < ep["ts_max"]:
            return ep_key
    if timestamp >= 1713571200:
        return "halving4"
    return "unknown"


def audit_single_epoch(name: str, blocks: list[dict], zd_basis: list[np.ndarray]) -> dict:
    print("\n" + "=" * 68)
    print(f"EPOCH AUDIT: {name} (N = {len(blocks)} blocks)")
    print("=" * 68)
    states = [block_to_sedenion(b) for b in blocks]
    r1 = audit_charge_distribution(states)
    r2 = audit_ramanujan_mixing(states)
    r3 = audit_zeta_trajectory(states, zd_basis)
    return {
        "epoch": name,
        "blocks_count": len(blocks),
        "chi2": r1["chi2"],
        "structured": r1["structured"],
        "dominant_charge": max(r1["counts"], key=r1["counts"].get) if r1["counts"] else None,
        "observed_lambda2": r2.get("observed_lambda2", None),
        "min_zeta": r3["min"],
        "mean_zeta": r3["mean"],
        "exact_zd": r3["exact_zd"],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("blocks_path", nargs="?", default=None,
                        help="Path to Bitcoin blocks directory (blk*.dat files)")
    parser.add_argument("--limit", type=int, default=2000,
                        help="Max blocks to read per file")
    parser.add_argument("--epoch", default="all",
                        choices=["all", "genesis", "halving1", "segwit", "ordinals"],
                        help="Select specific epoch or 'all' for cross-epoch segmentation")
    parser.add_argument("--synthetic", action="store_true",
                        help="Use synthetic states instead of real blockchain data")
    args = parser.parse_args()

    print()
    print("╔" + "═" * 66 + "╗")
    print("║" + "  Blockchain CD Audit — Multi-Epoch Segmentation & Dynamics".ljust(66) + "║")
    print("╚" + "═" * 66 + "╝")
    print()

    zd_basis = build_zd_basis()
    print(f"  ZD basis size: {len(zd_basis)} (expected 168)")

    if args.synthetic or args.blocks_path is None:
        print("  Mode: SYNTHETIC (no blockchain data provided)")
        states = synthetic_states(1000)
        r1 = audit_charge_distribution(states)
        r2 = audit_ramanujan_mixing(states)
        r3 = audit_zeta_trajectory(states, zd_basis)
        return 0

    blocks_path = Path(args.blocks_path)
    if not blocks_path.exists():
        print(f"  ERROR: path {blocks_path} does not exist")
        return 1

    print(f"  Mode: REAL BLOCKCHAIN DATA (Epoch: {args.epoch.upper()})")
    print(f"  Source: {blocks_path}")

    epochs_to_run = list(EPOCHS.keys()) if args.epoch == "all" else [args.epoch]
    epoch_results = []

    for ep_key in epochs_to_run:
        ep_info = EPOCHS[ep_key]
        ep_blocks = []
        for fn in ep_info["sample_files"]:
            fp = blocks_path / fn
            if fp.exists():
                print(f"    Reading {fn} ({ep_info['name']})...")
                b_list = read_blocks_from_file(fp, limit=args.limit)
                ep_blocks.extend(b_list)

        if not ep_blocks:
            print(f"    Warning: No blocks found for {ep_info['name']}")
            continue

        res = audit_single_epoch(ep_info["name"], ep_blocks, zd_basis)
        epoch_results.append(res)

    print("\n" + "=" * 78)
    print("CROSS-EPOCH HISTORICAL TRAJECTORY SUMMARY")
    print("=" * 78)
    print(f"{'Epoch':<32} | {'Blocks':<6} | {'χ²':<7} | {'Dom χ':<5} | {'Min ζ':<6} | {'Mean ζ':<6} | {'ZD'}")
    print("-" * 78)
    for r in epoch_results:
        print(f"{r['epoch']:<32} | {r['blocks_count']:<6} | {r['chi2']:<7.2f} | {r['dominant_charge']:<5} | {r['min_zeta']:<6.4f} | {r['mean_zeta']:<6.4f} | {r['exact_zd']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())


# Pytest discovery suppression
test_charge_distribution = audit_charge_distribution
test_ramanujan_mixing = audit_ramanujan_mixing
test_zeta_trajectory = audit_zeta_trajectory
test_charge_distribution.__test__ = False
test_ramanujan_mixing.__test__ = False
test_zeta_trajectory.__test__ = False
