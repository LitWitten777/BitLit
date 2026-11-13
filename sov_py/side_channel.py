"""
Side-Channel Timing & Cache-Footprint Analysis for Sedenion Permutations (OP-054, HYP-104).

Analyzes data-dependent memory accesses, cache line footprints, and timing variance
correlated with secret key Hamming weight in the AVX2 C implementation of the Ramanujan sponge:

1. Theoretical Cache Line Footprint:
   - SE_ADJ_168: 168 * 8 * 2 = 2,688 bytes = 42 cache lines (64 bytes/line).
   - SE_ZDS_168: 168 * 8 = 1,344 bytes = 21 cache lines.
   - SE_SIGN_16: 16 * 16 = 256 bytes = 4 cache lines.
   - Total secret-dependent table memory = 4,288 bytes across 67 cache lines.

2. Empirical Timing Variance & Correlation:
   - Measures CPU cycle variance using RDTSC across Hamming weights W in {0, 64, 128, 192, 256}.
   - Detects timing delta exceeding the 3-sigma falsification threshold (z > 3.0).
   - Evaluates Pearson correlation r(HW, cycles) < -0.5.
"""

from __future__ import annotations

import math
import subprocess
from pathlib import Path
from typing import Any

C_DIR = Path(__file__).resolve().parent.parent / "c"
SRC_C = C_DIR / "sedenion_engine.h"


def get_cache_footprint() -> dict[str, Any]:
    """
    Computes the exact memory size and cache line footprint (at 64 bytes/line)
    for all data-dependent tables accessed during se_sponge_permute.
    """
    line_size = 64
    adj_bytes = 168 * 8 * 2  # uint16_t SE_ADJ_168[168][8]
    zds_bytes = 168 * 8      # SedenionVec SE_ZDS_168[168] (8 bytes per struct)
    sign_bytes = 16 * 16     # int8_t SE_SIGN_16[16][16]
    total_bytes = adj_bytes + zds_bytes + sign_bytes

    return {
        "cache_line_size": line_size,
        "adj_table_bytes": adj_bytes,
        "adj_table_cache_lines": math.ceil(adj_bytes / line_size),
        "zds_table_bytes": zds_bytes,
        "zds_table_cache_lines": math.ceil(zds_bytes / line_size),
        "sign_table_bytes": sign_bytes,
        "sign_table_cache_lines": math.ceil(sign_bytes / line_size),
        "total_secret_table_bytes": total_bytes,
        "total_cache_lines": math.ceil(total_bytes / line_size),
        "is_single_cache_line": total_bytes <= line_size,
    }


def measure_timing_by_hamming_weight(
    weights: list[int] | None = None,
    samples_per_weight: int = 20000,
    binary_path: Path | None = None,
) -> dict[str, Any]:
    """
    Compiles and executes a native RDTSC benchmark measuring timing distribution
    across different Hamming weights of the secret input state.

    Returns dictionary with means, stds, pairwise z-scores, Pearson r, and falsification status.
    """
    if weights is None:
        weights = [0, 64, 128, 192, 256]

    bench_bin = binary_path or Path("/tmp/sedenion_side_channel_bench")
    c_source = f"""#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "{SRC_C}"

static inline uint64_t rdtsc(void) {{
    uint32_t lo, hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}}

int main(void) {{
    const int N_WEIGHTS = {len(weights)};
    int weights[{len(weights)}] = {{{", ".join(str(w) for w in weights)}}};
    const int SAMPLES = {samples_per_weight};

    uint8_t dummy[32] = {{0}};
    for (int i = 0; i < 2000; i++) se_sponge_permute(dummy, 32, 24);

    for (int w = 0; w < N_WEIGHTS; w++) {{
        int target_hw = weights[w];
        double sum = 0, sum_sq = 0;

        for (int i = 0; i < SAMPLES; i++) {{
            uint8_t s[32];
            memset(s, 0, 32);
            int set_bits = 0;
            for (int b = 0; b < 256 && set_bits < target_hw; b++) {{
                s[b / 8] |= (1 << (b % 8));
                set_bits++;
            }}

            uint64_t st = rdtsc();
            se_sponge_permute(s, 32, 24);
            uint64_t en = rdtsc();

            double elapsed = (double)(en - st);
            sum += elapsed;
            sum_sq += elapsed * elapsed;
        }}

        double mean = sum / SAMPLES;
        double std = sqrt((sum_sq - sum * sum / SAMPLES) / (SAMPLES - 1));
        printf("RESULT %d %.2f %.2f\\n", target_hw, mean, std);
    }}
    return 0;
}}
"""
    tmp_c = Path("/tmp/side_channel_bench.c")
    tmp_c.write_text(c_source, encoding="utf-8")

    compile_cmd = [
        "gcc", "-O3", "-mavx2", f"-I{C_DIR}", "-lm",
        str(tmp_c), "-o", str(bench_bin)
    ]
    comp_res = subprocess.run(compile_cmd, capture_output=True, text=True)
    if comp_res.returncode != 0:
        raise RuntimeError(f"Failed to compile side-channel benchmark: {comp_res.stderr}")

    run_res = subprocess.run([str(bench_bin)], capture_output=True, text=True)
    if run_res.returncode != 0:
        raise RuntimeError(f"Failed to run benchmark: {run_res.stderr}")

    means: dict[int, float] = {}
    stds: dict[int, float] = {}
    for line in run_res.stdout.strip().splitlines():
        if line.startswith("RESULT"):
            parts = line.split()
            hw = int(parts[1])
            m = float(parts[2])
            s = float(parts[3])
            means[hw] = m
            stds[hw] = s

    # Compute pairwise z-scores
    max_z = 0.0
    max_delta = 0.0
    hw_list = list(means.keys())
    for i in range(len(hw_list)):
        for j in range(i + 1, len(hw_list)):
            hw1, hw2 = hw_list[i], hw_list[j]
            delta = abs(means[hw1] - means[hw2])
            pooled_se = math.sqrt(
                (stds[hw1] ** 2) / samples_per_weight
                + (stds[hw2] ** 2) / samples_per_weight
            )
            z = delta / pooled_se if pooled_se > 0 else 0.0
            if z > max_z:
                max_z = z
                max_delta = delta

    # Pearson correlation r(HW, mean_cycles)
    n = len(hw_list)
    sum_x = sum(hw_list)
    sum_y = sum(means[hw] for hw in hw_list)
    sum_xy = sum(hw * means[hw] for hw in hw_list)
    sum_xx = sum(hw * hw for hw in hw_list)
    sum_yy = sum(means[hw] ** 2 for hw in hw_list)
    denom = math.sqrt((n * sum_xx - sum_x ** 2) * (n * sum_yy - sum_y ** 2))
    r = (n * sum_xy - sum_x * sum_y) / denom if denom > 0 else 0.0

    return {
        "weights": hw_list,
        "means": means,
        "stds": stds,
        "max_delta_cycles": max_delta,
        "max_sigma": max_z,
        "pearson_r": r,
        "falsification_threshold_sigma": 3.0,
        "is_falsified": max_z > 3.0,
    }
