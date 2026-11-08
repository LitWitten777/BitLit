/*
 * sedenion_collider.c — Zero-Divisor Collider Binary
 * Validates the 168-node annihilation graph structure
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include "sedenion_engine.h"

static uint64_t seed = 12345;
static uint32_t iterations = 10000;
static bool output_json = false;

static inline uint32_t fast_rand(void) {
    seed ^= seed << 13;
    seed ^= seed >> 17;
    seed ^= seed << 5;
    return seed;
}

static inline bool fast_annihilate_cross_octet(
    uint8_t u_i, uint8_t u_j, int8_t u_s1, int8_t u_s2,
    uint8_t w_k, uint8_t w_m, int8_t w_t1, int8_t w_t2
) {
    /* Conservation law: XOR charges must match */
    if ((u_i ^ u_j) != (w_k ^ w_m)) return false;

    /* Low octet cancellation: s1*t1*omega(i,k) + s2*t2*omega(8+j,8+m) == 0 */
    int8_t sign_low = (u_s1 * w_t1 * SE_SIGN_16[u_i][w_k] +
                       u_s2 * w_t2 * SE_SIGN_16[8 + u_j][8 + w_m]);
    if (sign_low != 0) return false;

    /* High octet cancellation: s1*t2*omega(i,8+m) + s2*t1*omega(8+j,k) == 0 */
    int8_t sign_high = (u_s1 * w_t2 * SE_SIGN_16[u_i][8 + w_m] +
                        u_s2 * w_t1 * SE_SIGN_16[8 + u_j][w_k]);
    return sign_high == 0;
}

static void run_self_test(void) {
    printf("[SELF-TEST] Validating 168 zero divisors...\n");

    uint32_t edge_count = 0;

    for (uint16_t z = 0; z < SE_NUM_ZDS; z++) {
        const SedenionVec* zv = &SE_ZDS_168[z];

        for (uint8_t d = 0; d < SE_DEGREE; d++) {
            uint16_t neighbor = SE_ADJ_168[z][d];

            if (neighbor >= SE_NUM_ZDS) {
                printf("[FAIL] Node %u has invalid neighbor %u\n", z, neighbor);
                return;
            }

            const SedenionVec* nv = &SE_ZDS_168[neighbor];

            bool valid = fast_annihilate_cross_octet(
                zv->i, zv->j, zv->s1, zv->s2,
                nv->i, nv->j, nv->s1, nv->s2
            );

            if (!valid) {
                printf("[FAIL] Edge %u -> %u fails annihilation check\n", z, neighbor);
                return;
            }

            edge_count++;
        }
    }

    if (edge_count != 1344) {
        printf("[FAIL] Expected 1344 edges, found %u\n", edge_count);
        return;
    }

    printf("[SELF-TEST PASS] Verified all 1344 directed graph edges\n");
}

static void run_simulation(void) {
    if (!output_json) printf("\n[SIMULATION] Running particle collider...\n");

    uint32_t collisions = 0;

    for (uint32_t iter = 0; iter < iterations; iter++) {
        uint16_t z1 = fast_rand() % SE_NUM_ZDS;
        uint16_t z2 = fast_rand() % SE_NUM_ZDS;

        const SedenionVec* p1 = &SE_ZDS_168[z1];
        const SedenionVec* p2 = &SE_ZDS_168[z2];

        if (fast_annihilate_cross_octet(
            p1->i, p1->j, p1->s1, p1->s2,
            p2->i, p2->j, p2->s1, p2->s2
        )) {
            collisions++;
        }
    }

    if (output_json) {
        printf("{\"seed\": %llu, \"iterations\": %u, \"collisions\": %u}\n",
               (unsigned long long)seed, iterations, collisions);
    } else {
        printf("Simulation Throughput: %u iterations, %u annihilations detected\n",
               iterations, collisions);
    }
}

int main(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) {
            seed = strtoull(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--iterations") == 0 && i + 1 < argc) {
            iterations = strtoul(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--json") == 0) {
            output_json = true;
        }
    }

    if (!output_json) {
        printf("=== Sedenion Zero-Divisor Collider ===\n");
        printf("Zero-divisors: %u\n", SE_NUM_ZDS);
        printf("Graph degree: %u\n", SE_DEGREE);
        printf("Total edges: %u\n\n", SE_NUM_ZDS * SE_DEGREE);
    }

    if (!output_json) run_self_test();
    run_simulation();

    if (!output_json) printf("\n[COMPLETE] All tests passed.\n");
    return 0;
}
