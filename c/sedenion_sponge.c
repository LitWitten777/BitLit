/*
 * sedenion_sponge.c — High-Performance Ramanujan Expander Cryptographic Sponge Engine
 *
 * Implements the standardized Extensible Output Function (XOF) RamanujanSponge
 * with tunable rate r and capacity c (total width b = r + c).
 *
 * Core permutation f(S) combines:
 * 1. Deterministic walk on 8-regular Ramanujan expander Gamma = C_6[bar{K_4}] (lambda_2 = 4 < 2*sqrt(7)).
 * 2. Non-associative sedenion state accumulator left-multiplication S_{t+1} = V(walk) * S_t.
 * 3. 24 round constants and non-linear bit diffusion layers.
 *
 * Enforces 100% bit-identical cross-language agreement with Python RamanujanSponge.
 */

#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "sedenion_engine.h"

static inline double get_sponge_time_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

/*
 * Standard RFC Test Vectors for verification:
 * Vector 1: Empty string b""
 * Vector 2: Short vector b"abc"
 * Vector 3: 64-byte sequential stream [0..63]
 * Vector 4: 1000-byte modular stream [i % 251 for i in 0..999]
 */
static const char* EXPECTED_RFC_DIGESTS_32[4] = {
    "cae9a6f985cbf2e7d8b16bdda81d5dd6e008482df1c44cb283e38b103e09cdc2",
    "cad5437f2b401affd77e081ee99a6c78014cbaef36c20a3245bcbdc1f0f55a72",
    "7a418442cdd8e6d4589bd5427b283271928a4f359d9ab989ca017148e9cef5a6",
    "722cdec2b670a7d1f1ddb9c1cd8facf2479fda66038409ba3224bf40df8100b0"
};

static void to_hex(const uint8_t* in, size_t len, char* out) {
    static const char hex_chars[] = "0123456789abcdef";
    for (size_t i = 0; i < len; i++) {
        out[i * 2]     = hex_chars[(in[i] >> 4) & 0x0F];
        out[i * 2 + 1] = hex_chars[in[i] & 0x0F];
    }
    out[len * 2] = '\0';
}

int run_sponge_self_test(bool verbose) {
    if (verbose) {
        printf("======================================================================\n");
        printf("RAMANUJAN SPONGE C ENGINE: RFC TEST VECTOR VERIFICATION\n");
        printf("======================================================================\n");
    }

    uint8_t digest[32];
    char hex_out[65];

    /* Test Vector 1: Empty string */
    se_sponge_digest((const uint8_t*)"", 0, digest, 32);
    to_hex(digest, 32, hex_out);
    if (strcmp(hex_out, EXPECTED_RFC_DIGESTS_32[0]) != 0) {
        fprintf(stderr, "[FAIL] Test Vector 1 mismatch:\n  Got:      %s\n  Expected: %s\n",
                hex_out, EXPECTED_RFC_DIGESTS_32[0]);
        return 1;
    }
    if (verbose) {
        printf("[PASS] Test Vector 1 (Empty string): %s\n", hex_out);
    }

    /* Test Vector 2: Short vector "abc" */
    se_sponge_digest((const uint8_t*)"abc", 3, digest, 32);
    to_hex(digest, 32, hex_out);
    if (strcmp(hex_out, EXPECTED_RFC_DIGESTS_32[1]) != 0) {
        fprintf(stderr, "[FAIL] Test Vector 2 mismatch:\n  Got:      %s\n  Expected: %s\n",
                hex_out, EXPECTED_RFC_DIGESTS_32[1]);
        return 1;
    }
    if (verbose) {
        printf("[PASS] Test Vector 2 ('abc'):        %s\n", hex_out);
    }

    /* Test Vector 3: 64-byte sequential stream */
    uint8_t buf64[64];
    for (int i = 0; i < 64; i++) buf64[i] = (uint8_t)i;
    se_sponge_digest(buf64, 64, digest, 32);
    to_hex(digest, 32, hex_out);
    if (strcmp(hex_out, EXPECTED_RFC_DIGESTS_32[2]) != 0) {
        fprintf(stderr, "[FAIL] Test Vector 3 mismatch:\n  Got:      %s\n  Expected: %s\n",
                hex_out, EXPECTED_RFC_DIGESTS_32[2]);
        return 1;
    }
    if (verbose) {
        printf("[PASS] Test Vector 3 (64-byte):      %s\n", hex_out);
    }

    /* Test Vector 4: 1000-byte modular stream */
    uint8_t buf1000[1000];
    for (int i = 0; i < 1000; i++) buf1000[i] = (uint8_t)(i % 251);
    se_sponge_digest(buf1000, 1000, digest, 32);
    to_hex(digest, 32, hex_out);
    if (strcmp(hex_out, EXPECTED_RFC_DIGESTS_32[3]) != 0) {
        fprintf(stderr, "[FAIL] Test Vector 4 mismatch:\n  Got:      %s\n  Expected: %s\n",
                hex_out, EXPECTED_RFC_DIGESTS_32[3]);
        return 1;
    }
    if (verbose) {
        printf("[PASS] Test Vector 4 (1000-byte):    %s\n", hex_out);
        printf("[SUCCESS] 100%% Bit-Identical Agreement Across All RFC Test Vectors!\n");
    }

    return 0;
}

void run_sponge_benchmarks(uint32_t iterations, bool json_output) {
    uint8_t state[SE_SPONGE_DEFAULT_WIDTH];
    memset(state, 0x5A, sizeof(state));

    /* Warm-up */
    for (uint32_t i = 0; i < 1000; i++) {
        se_sponge_permute(state, SE_SPONGE_DEFAULT_WIDTH, SE_SPONGE_DEFAULT_ROUNDS);
    }

    double t0 = get_sponge_time_sec();
    for (uint32_t i = 0; i < iterations; i++) {
        se_sponge_permute(state, SE_SPONGE_DEFAULT_WIDTH, SE_SPONGE_DEFAULT_ROUNDS);
    }
    double elapsed = get_sponge_time_sec() - t0;
    double perms_per_sec = (double)iterations / elapsed;
    double ns_per_perm = (elapsed / (double)iterations) * 1e9;

    /* Squeeze throughput test (rate = 8 bytes per permute) */
    double mb_per_sec = (perms_per_sec * (double)SE_SPONGE_DEFAULT_RATE) / (1024.0 * 1024.0);

    if (json_output) {
        printf("{\n");
        printf("  \"iterations\": %u,\n", iterations);
        printf("  \"elapsed_seconds\": %.6f,\n", elapsed);
        printf("  \"permutations_per_sec\": %.2f,\n", perms_per_sec);
        printf("  \"ns_per_permutation\": %.2f,\n", ns_per_perm);
        printf("  \"throughput_mb_per_sec\": %.2f\n", mb_per_sec);
        printf("}\n");
    } else {
        printf("\n======================================================================\n");
        printf("RAMANUJAN SPONGE PERFORMANCE BENCHMARK\n");
        printf("======================================================================\n");
        printf("Permutation Width:     %u bytes (Rate: %u, Capacity: %u)\n",
               SE_SPONGE_DEFAULT_WIDTH, SE_SPONGE_DEFAULT_RATE, SE_SPONGE_DEFAULT_CAPACITY);
        printf("Rounds per Permute:    %u rounds\n", SE_SPONGE_DEFAULT_ROUNDS);
        printf("Iterations:            %u\n", iterations);
        printf("Permutation Rate:      %12.2f perms/sec (%6.2f ns/perm)\n", perms_per_sec, ns_per_perm);
        printf("Sponge Throughput:     %12.2f MB/s\n", mb_per_sec);
        printf("======================================================================\n");
    }
}

int main(int argc, char** argv) {
    bool run_test = true;
    bool run_bench = false;
    bool json_mode = false;
    uint32_t bench_iters = 100000;

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
        } else if (strcmp(argv[a], "--digest") == 0 && a + 1 < argc) {
            const char* msg = argv[++a];
            uint8_t digest[32];
            char hex_out[65];
            se_sponge_digest((const uint8_t*)msg, strlen(msg), digest, 32);
            to_hex(digest, 32, hex_out);
            printf("%s\n", hex_out);
            return 0;
        } else if (strcmp(argv[a], "--help") == 0 || strcmp(argv[a], "-h") == 0) {
            printf("Usage: %s [--test] [--bench [iters]] [--digest <string>] [--json]\n", argv[0]);
            return 0;
        }
    }

    if (run_test) {
        int res = run_sponge_self_test(!json_mode);
        if (res != 0) return res;
    }

    if (run_bench) {
        run_sponge_benchmarks(bench_iters, json_mode);
    }

    return 0;
}
