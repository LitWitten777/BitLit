/*
 * sedenion_simd.c — High-Performance SIMD Vectorized Annihilation Engine
 * Validates AVX2 / SSSE3 / ARM Neon vectorization across the 168-node graph.
 * Benchmarks annihilation throughput against scalar baselines.
 */

#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "sedenion_engine.h"

static inline double get_time_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 987654321ULL;

static inline uint32_t fast_rand(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 17;
    rng_state ^= rng_state << 5;
    return (uint32_t)rng_state;
}

/*
 * Exhaustive Self-Test:
 * Compares canonical se_annihilate, scalar SoA16, SSSE3 SoA16, and AVX2 SoA32
 * across all 168 x 168 = 28,224 pairs and against SE_ADJ_168 table.
 */
static int run_exhaustive_test(bool verbose) {
    if (verbose) {
        printf("======================================================================\n");
        printf("SOVEREIGN C ENGINE: SIMD VECTOR EXHAUSTIVE VERIFICATION\n");
#if defined(SE_HAS_AVX2)
        printf("Active Architecture: AVX2 256-bit SIMD enabled\n");
#elif defined(SE_HAS_SSSE3)
        printf("Active Architecture: SSSE3 128-bit SIMD enabled\n");
#elif defined(SE_HAS_NEON)
        printf("Active Architecture: ARM Neon 128-bit SIMD enabled\n");
#else
        printf("Active Architecture: Portable Scalar fallback\n");
#endif
        printf("======================================================================\n");
    }

    SedenionSoA16 blocks16[11];
    se_pack_zds_soa16(blocks16);

#if defined(SE_HAS_AVX2)
    SedenionSoA32 blocks32[6];
    se_pack_zds_soa32(blocks32);
#endif

    uint32_t canonical_edges = 0;
    uint32_t scalar16_edges = 0;
#if defined(SE_HAS_SSSE3)
    uint32_t ssse3_edges = 0;
#endif
#if defined(SE_HAS_AVX2)
    uint32_t avx2_edges = 0;
#endif

    /* 1. Test all 28,224 pairs individually */
    for (uint16_t u_idx = 0; u_idx < SE_NUM_ZDS; u_idx++) {
        const SedenionVec* u = &SE_ZDS_168[u_idx];

        /* Test against 11 SoA16 blocks */
        for (int b = 0; b < 11; b++) {
            uint16_t m_scalar = se_annihilate_scalar_16(u, &blocks16[b]);
#if defined(SE_HAS_SSSE3)
            uint16_t m_ssse3 = se_annihilate_ssse3_1x16(u, &blocks16[b]);
            if (m_scalar != m_ssse3) {
                fprintf(stderr, "[FAIL] Discrepancy between scalar (%u) and SSSE3 (%u) at u=%u, block=%d\n",
                        m_scalar, m_ssse3, u_idx, b);
                return 1;
            }
#endif
            for (int s = 0; s < 16; s++) {
                uint16_t w_idx = blocks16[b].global_idx[s];
                if (w_idx >= SE_NUM_ZDS) continue;
                const SedenionVec* w = &SE_ZDS_168[w_idx];

                bool can = se_annihilate(u, w);
                bool sc = (m_scalar & (1 << s)) != 0;

                if (can != sc) {
                    fprintf(stderr, "[FAIL] Pair (%u, %u) mismatch: canonical=%d, scalar16=%d\n",
                            u_idx, w_idx, can, sc);
                    return 1;
                }

                if (can) {
                    canonical_edges++;
                    scalar16_edges++;
#if defined(SE_HAS_SSSE3)
                    ssse3_edges++;
#endif
                }
            }
        }

#if defined(SE_HAS_AVX2)
        /* Test against 6 SoA32 blocks */
        for (int b = 0; b < 6; b++) {
            uint32_t m_avx2 = se_annihilate_avx2_1x32(u, &blocks32[b]);
            for (int s = 0; s < 32; s++) {
                uint16_t w_idx = blocks32[b].global_idx[s];
                if (w_idx >= SE_NUM_ZDS) continue;
                const SedenionVec* w = &SE_ZDS_168[w_idx];

                bool can = se_annihilate(u, w);
                bool av = (m_avx2 & (1U << s)) != 0;

                if (can != av) {
                    fprintf(stderr, "[FAIL] Pair (%u, %u) AVX2 mismatch: canonical=%d, avx2=%d\n",
                            u_idx, w_idx, can, av);
                    return 1;
                }
                if (av) avx2_edges++;
            }
        }
#endif
    }

    if (canonical_edges != 1344) {
        fprintf(stderr, "[FAIL] Expected 1344 edges, got %u\n", canonical_edges);
        return 1;
    }
    if (scalar16_edges != 1344) {
        fprintf(stderr, "[FAIL] Scalar SoA16 edges count: %u\n", scalar16_edges);
        return 1;
    }
#if defined(SE_HAS_SSSE3)
    if (ssse3_edges != 1344) {
        fprintf(stderr, "[FAIL] SSSE3 edges count: %u\n", ssse3_edges);
        return 1;
    }
#endif
#if defined(SE_HAS_AVX2)
    if (avx2_edges != 1344) {
        fprintf(stderr, "[FAIL] AVX2 edges count: %u\n", avx2_edges);
        return 1;
    }
#endif

    /* 2. Test high-level se_find_neighbors_simd across all 168 nodes */
    for (uint16_t u_idx = 0; u_idx < SE_NUM_ZDS; u_idx++) {
        const SedenionVec* u = &SE_ZDS_168[u_idx];
        uint16_t neighbors[SE_DEGREE];

#if defined(SE_HAS_AVX2)
        uint8_t count = se_find_neighbors_simd(u, blocks32, true, neighbors);
#else
        uint8_t count = se_find_neighbors_simd(u, blocks16, false, neighbors);
#endif

        if (count != SE_DEGREE) {
            fprintf(stderr, "[FAIL] Node %u expected %u neighbors, got %u\n", u_idx, SE_DEGREE, count);
            return 1;
        }

        /* Check that every returned neighbor is in SE_ADJ_168 */
        for (int k = 0; k < SE_DEGREE; k++) {
            uint16_t n = neighbors[k];
            bool found = false;
            for (int adj = 0; adj < SE_DEGREE; adj++) {
                if (SE_ADJ_168[u_idx][adj] == n) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                fprintf(stderr, "[FAIL] Node %u neighbor %u not in SE_ADJ_168 table\n", u_idx, n);
                return 1;
            }
        }
    }

    if (verbose) {
        printf("[SELF-TEST PASS] Exhaustively tested all 28,224 pairs!\n");
        printf("  - Canonical se_annihilate: 1344 edges verified\n");
        printf("  - SoA16 Scalar:            1344 edges verified\n");
#if defined(SE_HAS_SSSE3)
        printf("  - SoA16 SSSE3 (128-bit):   1344 edges verified\n");
#endif
#if defined(SE_HAS_AVX2)
        printf("  - SoA32 AVX2 (256-bit):    1344 edges verified\n");
#endif
        printf("  - High-level neighbor finder: 100%% exact match for all 168 nodes\n");
    }
    return 0;
}

/*
 * Micro-benchmarks comparing throughput across engines.
 */
static void run_benchmarks(uint32_t iterations, bool json_output) {
    SedenionSoA16 blocks16[11];
    se_pack_zds_soa16(blocks16);

#if defined(SE_HAS_AVX2)
    SedenionSoA32 blocks32[6];
    se_pack_zds_soa32(blocks32);
#endif

    /* Warm-up */
    volatile uint32_t dummy = 0;
    for (uint32_t i = 0; i < 10000; i++) {
        uint16_t u_idx = (uint16_t)(fast_rand() % SE_NUM_ZDS);
        uint16_t w_idx = (uint16_t)(fast_rand() % SE_NUM_ZDS);
        dummy += se_annihilate(&SE_ZDS_168[u_idx], &SE_ZDS_168[w_idx]);
    }
    (void)dummy;

    /* Benchmark 1: Canonical Single-Pair Annihilation */
    double t0 = get_time_sec();
    uint32_t hits_canonical = 0;
    for (uint32_t i = 0; i < iterations; i++) {
        uint16_t u_idx = (uint16_t)(fast_rand() % SE_NUM_ZDS);
        uint16_t w_idx = (uint16_t)(fast_rand() % SE_NUM_ZDS);
        hits_canonical += se_annihilate(&SE_ZDS_168[u_idx], &SE_ZDS_168[w_idx]);
    }
    (void)hits_canonical;
    double t_canonical = get_time_sec() - t0;
    double ops_canonical = (double)iterations / t_canonical;

    /* Benchmark 2: SIMD Scanning of all 168 nodes per query */
    uint32_t scan_iterations = iterations / 10;
    if (scan_iterations < 10000) scan_iterations = 10000;

    double t1 = get_time_sec();
    uint32_t hits_simd = 0;
    uint16_t neighbors[SE_DEGREE];
    for (uint32_t i = 0; i < scan_iterations; i++) {
        uint16_t u_idx = (uint16_t)(fast_rand() % SE_NUM_ZDS);
        const SedenionVec* u = &SE_ZDS_168[u_idx];
#if defined(SE_HAS_AVX2)
        hits_simd += se_find_neighbors_simd(u, blocks32, true, neighbors);
#else
        hits_simd += se_find_neighbors_simd(u, blocks16, false, neighbors);
#endif
    }
    (void)hits_simd;
    double t_simd = get_time_sec() - t1;
    /* Each scan iteration evaluates 168 candidate pairs */
    double total_simd_pairs = (double)scan_iterations * 168.0;
    double ops_simd = total_simd_pairs / t_simd;
    double scans_per_sec = (double)scan_iterations / t_simd;

#if defined(SE_HAS_AVX2)
    /* Benchmark 3: Direct AVX2 32-way raw kernel throughput */
    double t2 = get_time_sec();
    uint32_t avx2_masks = 0;
    uint32_t block_iterations = iterations * 2;
    for (uint32_t i = 0; i < block_iterations; i++) {
        uint16_t u_idx = (uint16_t)(fast_rand() % SE_NUM_ZDS);
        int b = (int)(fast_rand() % 6);
        avx2_masks += se_annihilate_avx2_1x32(&SE_ZDS_168[u_idx], &blocks32[b]);
    }
    (void)avx2_masks;
    double t_avx2 = get_time_sec() - t2;
    double total_avx2_pairs = (double)block_iterations * 32.0;
    double ops_avx2_kernel = total_avx2_pairs / t_avx2;
#endif

    if (json_output) {
        printf("{\n");
        printf("  \"iterations\": %u,\n", iterations);
        printf("  \"canonical_pairs_per_sec\": %.2f,\n", ops_canonical);
        printf("  \"simd_graph_scans_per_sec\": %.2f,\n", scans_per_sec);
        printf("  \"simd_equivalent_pairs_per_sec\": %.2f,\n", ops_simd);
#if defined(SE_HAS_AVX2)
        printf("  \"avx2_kernel_pairs_per_sec\": %.2f,\n", ops_avx2_kernel);
        printf("  \"avx2_speedup\": %.2f,\n", ops_avx2_kernel / ops_canonical);
#endif
        printf("  \"simd_scan_speedup\": %.2f\n", ops_simd / ops_canonical);
        printf("}\n");
    } else {
        printf("\n======================================================================\n");
        printf("SIMD PERFORMANCE BENCHMARK REPORT\n");
        printf("======================================================================\n");
        printf("Iterations: %u\n", iterations);
        printf("Canonical Pair Annihilation:   %14.2f pairs/sec  (%6.2f ns/pair)\n",
               ops_canonical, 1e9 / ops_canonical);
        printf("SIMD 168-Node Graph Scanner:   %14.2f scans/sec  (%6.2f ns/scan)\n",
               scans_per_sec, 1e9 / scans_per_sec);
        printf("SIMD Equivalent Pair Rate:     %14.2f pairs/sec  (%6.2f ns/pair)\n",
               ops_simd, 1e9 / ops_simd);
#if defined(SE_HAS_AVX2)
        printf("AVX2 32-way Kernel Rate:       %14.2f pairs/sec  (%6.2f ns/pair)\n",
               ops_avx2_kernel, 1e9 / ops_avx2_kernel);
        printf("Speedup (AVX2 Kernel vs Scalar): %12.2fx acceleration\n",
               ops_avx2_kernel / ops_canonical);
#endif
        printf("Speedup (SIMD Scanner vs Scalar):%12.2fx acceleration\n",
               ops_simd / ops_canonical);
        printf("======================================================================\n");
    }
}

int main(int argc, char** argv) {
    bool run_test = true;
    bool run_bench = false;
    bool json_mode = false;
    uint32_t bench_iters = 2000000;

    for (int a = 1; a < argc; a++) {
        if (strcmp(argv[a], "--test") == 0) {
            run_test = true;
        } else if (strcmp(argv[a], "--bench") == 0 || strcmp(argv[a], "-b") == 0) {
            run_bench = true;
            if (a + 1 < argc && argv[a + 1][0] != '-') {
                bench_iters = (uint32_t)strtoul(argv[++a], NULL, 10);
            }
        } else if (strcmp(argv[a], "--json") == 0) {
            json_mode = true;
        } else if (strcmp(argv[a], "--help") == 0 || strcmp(argv[a], "-h") == 0) {
            printf("Usage: %s [--test] [--bench [iters]] [--json]\n", argv[0]);
            return 0;
        }
    }

    if (run_test) {
        int res = run_exhaustive_test(!json_mode);
        if (res != 0) return res;
    }

    if (run_bench) {
        run_benchmarks(bench_iters, json_mode);
    }

    return 0;
}
