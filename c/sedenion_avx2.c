/*
 * sedenion_avx2.c
 * =============================================================================
 * Native AVX2 SIMD 16D Cayley-Dickson Multiplication Engine
 * =============================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <immintrin.h>
#include "sedenion_engine.h"

// Precomputed sign tables as float: SE_SIGN_FLOAT[c][a] = SE_SIGN_16[a][a ^ c]
static float SE_SIGN_FLOAT[16][16];
static int SE_PERM_IDX[16][16];
static bool tables_initialized = false;

static void init_tables(void) {
    if (tables_initialized) return;
    for (int c = 0; c < 16; c++) {
        for (int a = 0; a < 16; a++) {
            int b = a ^ c;
            SE_SIGN_FLOAT[c][a] = (float)SE_SIGN_16[a][b];
            SE_PERM_IDX[c][a] = b;
        }
    }
    tables_initialized = true;
}

/*
 * Single 16D Cayley-Dickson multiplication: out = a * b
 */
void cd_multiply_16_avx2(const float* a, const float* b, float* out) {
    if (!tables_initialized) init_tables();

    __m256 a_lo = _mm256_loadu_ps(&a[0]);
    __m256 a_hi = _mm256_loadu_ps(&a[8]);

    for (int c = 0; c < 16; c++) {
        // Load permuted b using precomputed indices
        float b_perm[16];
        for (int i = 0; i < 16; i++) {
            b_perm[i] = b[SE_PERM_IDX[c][i]];
        }
        __m256 bp_lo = _mm256_loadu_ps(&b_perm[0]);
        __m256 bp_hi = _mm256_loadu_ps(&b_perm[8]);

        __m256 s_lo = _mm256_loadu_ps(&SE_SIGN_FLOAT[c][0]);
        __m256 s_hi = _mm256_loadu_ps(&SE_SIGN_FLOAT[c][8]);

        __m256 p_lo = _mm256_mul_ps(_mm256_mul_ps(a_lo, bp_lo), s_lo);
        __m256 p_hi = _mm256_mul_ps(_mm256_mul_ps(a_hi, bp_hi), s_hi);
        __m256 p_sum = _mm256_add_ps(p_lo, p_hi);

        // Horizontal add 8 floats
        __m128 lo = _mm256_castps256_ps128(p_sum);
        __m128 hi = _mm256_extractf128_ps(p_sum, 1);
        __m128 sum4 = _mm_add_ps(lo, hi);
        __m128 sum2 = _mm_add_ps(sum4, _mm_movehl_ps(sum4, sum4));
        __m128 sum1 = _mm_add_ss(sum2, _mm_shuffle_ps(sum2, sum2, 1));
        out[c] = _mm_cvtss_f32(sum1);
    }
}

/*
 * Batch 16D Cayley-Dickson multiplication for count pairs:
 * out_batch[i] = a_batch[i] * b_batch[i]
 */
void cd_batch_multiply_16_avx2(
    const float* a_batch,
    const float* b_batch,
    float* out_batch,
    size_t count
) {
    if (!tables_initialized) init_tables();

    for (size_t i = 0; i < count; i++) {
        const float* a = &a_batch[i * 16];
        const float* b = &b_batch[i * 16];
        float* out = &out_batch[i * 16];
        cd_multiply_16_avx2(a, b, out);
    }
}
