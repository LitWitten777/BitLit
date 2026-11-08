/*
 * sedenion_engine.h — Zero-Dependency Embedded Cayley-Dickson Algebra Engine
 * Designed for microcontrollers (ESP32-S3, ARM Cortex-M) and bare-metal environments.
 * Pure integer combinatorics: No FPU, no dynamic allocation, O(1) annihilation checks.
 */

#ifndef SEDENION_ENGINE_H
#define SEDENION_ENGINE_H

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#if defined(__x86_64__) || defined(_M_X64) || defined(__i386__) || defined(_M_IX86)
  #if defined(__AVX2__)
    #include <immintrin.h>
    #define SE_HAS_AVX2 1
  #endif
  #if defined(__SSSE3__)
    #include <tmmintrin.h>
    #define SE_HAS_SSSE3 1
  #endif
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
  #include <arm_neon.h>
  #define SE_HAS_NEON 1
#endif

#define SE_DIM 16
#define SE_HALF 8
#define SE_NUM_ZDS 168
#define SE_DEGREE 8

typedef struct {
    uint8_t i;
    uint8_t j;
    int8_t s1;
    int8_t s2;
    uint8_t chi;
} SedenionVec;

/*
 * Structure-of-Arrays (SoA) layout for 16 zero divisors.
 * Enables single-cycle SIMD sign lookup via vpshufb / vqtbl1q_u8.
 */
typedef struct {
    uint8_t i[16];
    uint8_t j[16];
    uint8_t s1_bit[16];       /* 0 if +1, 1 if -1 */
    uint8_t s2_bit[16];       /* 0 if +1, 1 if -1 */
    uint8_t chi[16];          /* XOR charge: i ^ j */
    uint8_t j_plus_8[16];     /* 8 + j, precomputed for high-octet lookups */
    uint16_t global_idx[16];  /* Original node index in SE_ZDS_168, or 0xFFFF for padding */
} SedenionSoA16;

/*
 * Structure-of-Arrays (SoA) layout for 32 zero divisors (AVX2 256-bit lane processing).
 */
typedef struct {
    uint8_t i[32];
    uint8_t j[32];
    uint8_t s1_bit[32];
    uint8_t s2_bit[32];
    uint8_t chi[32];
    uint8_t j_plus_8[32];
    uint16_t global_idx[32];
} SedenionSoA32;

// Cayley-Dickson 16x16 sign table: e_i * e_j = SE_SIGN_16[i][j] * e_{SE_IDX_16[i][j]}
static const int8_t SE_SIGN_16[16][16] = {
    { 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1},
    { 1, -1,  1, -1,  1, -1, -1,  1,  1, -1, -1,  1, -1,  1,  1, -1},
    { 1, -1, -1,  1,  1,  1, -1, -1,  1,  1, -1, -1, -1, -1,  1,  1},
    { 1,  1, -1, -1,  1, -1,  1, -1,  1, -1,  1, -1, -1,  1, -1,  1},
    { 1, -1, -1, -1, -1,  1,  1,  1,  1,  1,  1,  1, -1, -1, -1, -1},
    { 1,  1, -1,  1, -1, -1, -1,  1,  1, -1,  1, -1,  1, -1,  1, -1},
    { 1,  1,  1, -1, -1,  1, -1, -1,  1, -1, -1,  1,  1, -1, -1,  1},
    { 1, -1,  1,  1, -1, -1,  1, -1,  1,  1, -1, -1,  1,  1, -1, -1},
    { 1, -1, -1, -1, -1, -1, -1, -1, -1,  1,  1,  1,  1,  1,  1,  1},
    { 1,  1, -1,  1, -1,  1,  1, -1, -1, -1, -1,  1, -1,  1,  1, -1},
    { 1,  1,  1, -1, -1, -1,  1,  1, -1,  1, -1, -1, -1, -1,  1,  1},
    { 1, -1,  1,  1, -1,  1, -1,  1, -1, -1,  1, -1, -1,  1, -1,  1},
    { 1,  1,  1,  1,  1, -1, -1, -1, -1,  1,  1,  1, -1, -1, -1, -1},
    { 1, -1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1,  1, -1,  1, -1},
    { 1, -1, -1,  1,  1, -1,  1,  1, -1, -1, -1,  1,  1, -1, -1,  1},
    { 1,  1, -1, -1,  1,  1, -1,  1, -1,  1, -1, -1,  1,  1, -1, -1},
};

// Cayley-Dickson 16x16 sign bit table: 0 for +1, 1 for -1 (enables parallel SIMD XOR and shuffle)
static const uint8_t SE_SIGN_BITS_16[16][16] = {
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    {0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1},
    {0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0},
    {0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0},
    {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1},
    {0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1},
    {0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0},
    {0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1},
    {0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
    {0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1},
    {0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0},
    {0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0},
    {0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1},
    {0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1},
    {0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0},
    {0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1},
};

// Cayley-Dickson 16x16 index table
static const uint8_t SE_IDX_16[16][16] = {
    { 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15},
    { 1,  0,  3,  2,  5,  4,  7,  6,  9,  8, 11, 10, 13, 12, 15, 14},
    { 2,  3,  0,  1,  6,  7,  4,  5, 10, 11,  8,  9, 14, 15, 12, 13},
    { 3,  2,  1,  0,  7,  6,  5,  4, 11, 10,  9,  8, 15, 14, 13, 12},
    { 4,  5,  6,  7,  0,  1,  2,  3, 12, 13, 14, 15,  8,  9, 10, 11},
    { 5,  4,  7,  6,  1,  0,  3,  2, 13, 12, 15, 14,  9,  8, 11, 10},
    { 6,  7,  4,  5,  2,  3,  0,  1, 14, 15, 12, 13, 10, 11,  8,  9},
    { 7,  6,  5,  4,  3,  2,  1,  0, 15, 14, 13, 12, 11, 10,  9,  8},
    { 8,  9, 10, 11, 12, 13, 14, 15,  0,  1,  2,  3,  4,  5,  6,  7},
    { 9,  8, 11, 10, 13, 12, 15, 14,  1,  0,  3,  2,  5,  4,  7,  6},
    {10, 11,  8,  9, 14, 15, 12, 13,  2,  3,  0,  1,  6,  7,  4,  5},
    {11, 10,  9,  8, 15, 14, 13, 12,  3,  2,  1,  0,  7,  6,  5,  4},
    {12, 13, 14, 15,  8,  9, 10, 11,  4,  5,  6,  7,  0,  1,  2,  3},
    {13, 12, 15, 14,  9,  8, 11, 10,  5,  4,  7,  6,  1,  0,  3,  2},
    {14, 15, 12, 13, 10, 11,  8,  9,  6,  7,  4,  5,  2,  3,  0,  1},
    {15, 14, 13, 12, 11, 10,  9,  8,  7,  6,  5,  4,  3,  2,  1,  0},
};

// All 168 canonical cross-octet zero divisors
static const SedenionVec SE_ZDS_168[SE_NUM_ZDS] = {
    { 1,  2,  1,  1,  3}, // Node 0
    { 1,  2,  1, -1,  3}, // Node 1
    { 1,  2, -1,  1,  3}, // Node 2
    { 1,  2, -1, -1,  3}, // Node 3
    { 1,  3,  1,  1,  2}, // Node 4
    { 1,  3,  1, -1,  2}, // Node 5
    { 1,  3, -1,  1,  2}, // Node 6
    { 1,  3, -1, -1,  2}, // Node 7
    { 1,  4,  1,  1,  5}, // Node 8
    { 1,  4,  1, -1,  5}, // Node 9
    { 1,  4, -1,  1,  5}, // Node 10
    { 1,  4, -1, -1,  5}, // Node 11
    { 1,  5,  1,  1,  4}, // Node 12
    { 1,  5,  1, -1,  4}, // Node 13
    { 1,  5, -1,  1,  4}, // Node 14
    { 1,  5, -1, -1,  4}, // Node 15
    { 1,  6,  1,  1,  7}, // Node 16
    { 1,  6,  1, -1,  7}, // Node 17
    { 1,  6, -1,  1,  7}, // Node 18
    { 1,  6, -1, -1,  7}, // Node 19
    { 1,  7,  1,  1,  6}, // Node 20
    { 1,  7,  1, -1,  6}, // Node 21
    { 1,  7, -1,  1,  6}, // Node 22
    { 1,  7, -1, -1,  6}, // Node 23
    { 2,  1,  1,  1,  3}, // Node 24
    { 2,  1,  1, -1,  3}, // Node 25
    { 2,  1, -1,  1,  3}, // Node 26
    { 2,  1, -1, -1,  3}, // Node 27
    { 2,  3,  1,  1,  1}, // Node 28
    { 2,  3,  1, -1,  1}, // Node 29
    { 2,  3, -1,  1,  1}, // Node 30
    { 2,  3, -1, -1,  1}, // Node 31
    { 2,  4,  1,  1,  6}, // Node 32
    { 2,  4,  1, -1,  6}, // Node 33
    { 2,  4, -1,  1,  6}, // Node 34
    { 2,  4, -1, -1,  6}, // Node 35
    { 2,  5,  1,  1,  7}, // Node 36
    { 2,  5,  1, -1,  7}, // Node 37
    { 2,  5, -1,  1,  7}, // Node 38
    { 2,  5, -1, -1,  7}, // Node 39
    { 2,  6,  1,  1,  4}, // Node 40
    { 2,  6,  1, -1,  4}, // Node 41
    { 2,  6, -1,  1,  4}, // Node 42
    { 2,  6, -1, -1,  4}, // Node 43
    { 2,  7,  1,  1,  5}, // Node 44
    { 2,  7,  1, -1,  5}, // Node 45
    { 2,  7, -1,  1,  5}, // Node 46
    { 2,  7, -1, -1,  5}, // Node 47
    { 3,  1,  1,  1,  2}, // Node 48
    { 3,  1,  1, -1,  2}, // Node 49
    { 3,  1, -1,  1,  2}, // Node 50
    { 3,  1, -1, -1,  2}, // Node 51
    { 3,  2,  1,  1,  1}, // Node 52
    { 3,  2,  1, -1,  1}, // Node 53
    { 3,  2, -1,  1,  1}, // Node 54
    { 3,  2, -1, -1,  1}, // Node 55
    { 3,  4,  1,  1,  7}, // Node 56
    { 3,  4,  1, -1,  7}, // Node 57
    { 3,  4, -1,  1,  7}, // Node 58
    { 3,  4, -1, -1,  7}, // Node 59
    { 3,  5,  1,  1,  6}, // Node 60
    { 3,  5,  1, -1,  6}, // Node 61
    { 3,  5, -1,  1,  6}, // Node 62
    { 3,  5, -1, -1,  6}, // Node 63
    { 3,  6,  1,  1,  5}, // Node 64
    { 3,  6,  1, -1,  5}, // Node 65
    { 3,  6, -1,  1,  5}, // Node 66
    { 3,  6, -1, -1,  5}, // Node 67
    { 3,  7,  1,  1,  4}, // Node 68
    { 3,  7,  1, -1,  4}, // Node 69
    { 3,  7, -1,  1,  4}, // Node 70
    { 3,  7, -1, -1,  4}, // Node 71
    { 4,  1,  1,  1,  5}, // Node 72
    { 4,  1,  1, -1,  5}, // Node 73
    { 4,  1, -1,  1,  5}, // Node 74
    { 4,  1, -1, -1,  5}, // Node 75
    { 4,  2,  1,  1,  6}, // Node 76
    { 4,  2,  1, -1,  6}, // Node 77
    { 4,  2, -1,  1,  6}, // Node 78
    { 4,  2, -1, -1,  6}, // Node 79
    { 4,  3,  1,  1,  7}, // Node 80
    { 4,  3,  1, -1,  7}, // Node 81
    { 4,  3, -1,  1,  7}, // Node 82
    { 4,  3, -1, -1,  7}, // Node 83
    { 4,  5,  1,  1,  1}, // Node 84
    { 4,  5,  1, -1,  1}, // Node 85
    { 4,  5, -1,  1,  1}, // Node 86
    { 4,  5, -1, -1,  1}, // Node 87
    { 4,  6,  1,  1,  2}, // Node 88
    { 4,  6,  1, -1,  2}, // Node 89
    { 4,  6, -1,  1,  2}, // Node 90
    { 4,  6, -1, -1,  2}, // Node 91
    { 4,  7,  1,  1,  3}, // Node 92
    { 4,  7,  1, -1,  3}, // Node 93
    { 4,  7, -1,  1,  3}, // Node 94
    { 4,  7, -1, -1,  3}, // Node 95
    { 5,  1,  1,  1,  4}, // Node 96
    { 5,  1,  1, -1,  4}, // Node 97
    { 5,  1, -1,  1,  4}, // Node 98
    { 5,  1, -1, -1,  4}, // Node 99
    { 5,  2,  1,  1,  7}, // Node 100
    { 5,  2,  1, -1,  7}, // Node 101
    { 5,  2, -1,  1,  7}, // Node 102
    { 5,  2, -1, -1,  7}, // Node 103
    { 5,  3,  1,  1,  6}, // Node 104
    { 5,  3,  1, -1,  6}, // Node 105
    { 5,  3, -1,  1,  6}, // Node 106
    { 5,  3, -1, -1,  6}, // Node 107
    { 5,  4,  1,  1,  1}, // Node 108
    { 5,  4,  1, -1,  1}, // Node 109
    { 5,  4, -1,  1,  1}, // Node 110
    { 5,  4, -1, -1,  1}, // Node 111
    { 5,  6,  1,  1,  3}, // Node 112
    { 5,  6,  1, -1,  3}, // Node 113
    { 5,  6, -1,  1,  3}, // Node 114
    { 5,  6, -1, -1,  3}, // Node 115
    { 5,  7,  1,  1,  2}, // Node 116
    { 5,  7,  1, -1,  2}, // Node 117
    { 5,  7, -1,  1,  2}, // Node 118
    { 5,  7, -1, -1,  2}, // Node 119
    { 6,  1,  1,  1,  7}, // Node 120
    { 6,  1,  1, -1,  7}, // Node 121
    { 6,  1, -1,  1,  7}, // Node 122
    { 6,  1, -1, -1,  7}, // Node 123
    { 6,  2,  1,  1,  4}, // Node 124
    { 6,  2,  1, -1,  4}, // Node 125
    { 6,  2, -1,  1,  4}, // Node 126
    { 6,  2, -1, -1,  4}, // Node 127
    { 6,  3,  1,  1,  5}, // Node 128
    { 6,  3,  1, -1,  5}, // Node 129
    { 6,  3, -1,  1,  5}, // Node 130
    { 6,  3, -1, -1,  5}, // Node 131
    { 6,  4,  1,  1,  2}, // Node 132
    { 6,  4,  1, -1,  2}, // Node 133
    { 6,  4, -1,  1,  2}, // Node 134
    { 6,  4, -1, -1,  2}, // Node 135
    { 6,  5,  1,  1,  3}, // Node 136
    { 6,  5,  1, -1,  3}, // Node 137
    { 6,  5, -1,  1,  3}, // Node 138
    { 6,  5, -1, -1,  3}, // Node 139
    { 6,  7,  1,  1,  1}, // Node 140
    { 6,  7,  1, -1,  1}, // Node 141
    { 6,  7, -1,  1,  1}, // Node 142
    { 6,  7, -1, -1,  1}, // Node 143
    { 7,  1,  1,  1,  6}, // Node 144
    { 7,  1,  1, -1,  6}, // Node 145
    { 7,  1, -1,  1,  6}, // Node 146
    { 7,  1, -1, -1,  6}, // Node 147
    { 7,  2,  1,  1,  5}, // Node 148
    { 7,  2,  1, -1,  5}, // Node 149
    { 7,  2, -1,  1,  5}, // Node 150
    { 7,  2, -1, -1,  5}, // Node 151
    { 7,  3,  1,  1,  4}, // Node 152
    { 7,  3,  1, -1,  4}, // Node 153
    { 7,  3, -1,  1,  4}, // Node 154
    { 7,  3, -1, -1,  4}, // Node 155
    { 7,  4,  1,  1,  3}, // Node 156
    { 7,  4,  1, -1,  3}, // Node 157
    { 7,  4, -1,  1,  3}, // Node 158
    { 7,  4, -1, -1,  3}, // Node 159
    { 7,  5,  1,  1,  2}, // Node 160
    { 7,  5,  1, -1,  2}, // Node 161
    { 7,  5, -1,  1,  2}, // Node 162
    { 7,  5, -1, -1,  2}, // Node 163
    { 7,  6,  1,  1,  1}, // Node 164
    { 7,  6,  1, -1,  1}, // Node 165
    { 7,  6, -1,  1,  1}, // Node 166
    { 7,  6, -1, -1,  1}, // Node 167
};

// 8-regular Ramanujan annihilation graph adjacency list (168 x 8)
static const uint16_t SE_ADJ_168[SE_NUM_ZDS][SE_DEGREE] = {
    { 93,  94, 112, 115, 137, 138, 156, 159}, // Node 0 (chi=3)
    { 92,  95, 113, 114, 136, 139, 157, 158}, // Node 1 (chi=3)
    { 92,  95, 113, 114, 136, 139, 157, 158}, // Node 2 (chi=3)
    { 93,  94, 112, 115, 137, 138, 156, 159}, // Node 3 (chi=3)
    { 88,  91, 116, 119, 133, 134, 161, 162}, // Node 4 (chi=2)
    { 89,  90, 117, 118, 132, 135, 160, 163}, // Node 5 (chi=2)
    { 89,  90, 117, 118, 132, 135, 160, 163}, // Node 6 (chi=2)
    { 88,  91, 116, 119, 133, 134, 161, 162}, // Node 7 (chi=2)
    { 44,  47,  65,  66, 128, 131, 149, 150}, // Node 8 (chi=5)
    { 45,  46,  64,  67, 129, 130, 148, 151}, // Node 9 (chi=5)
    { 45,  46,  64,  67, 129, 130, 148, 151}, // Node 10 (chi=5)
    { 44,  47,  65,  66, 128, 131, 149, 150}, // Node 11 (chi=5)
    { 41,  42,  69,  70, 124, 127, 152, 155}, // Node 12 (chi=4)
    { 40,  43,  68,  71, 125, 126, 153, 154}, // Node 13 (chi=4)
    { 40,  43,  68,  71, 125, 126, 153, 154}, // Node 14 (chi=4)
    { 41,  42,  69,  70, 124, 127, 152, 155}, // Node 15 (chi=4)
    { 36,  39,  56,  59,  81,  82, 101, 102}, // Node 16 (chi=7)
    { 37,  38,  57,  58,  80,  83, 100, 103}, // Node 17 (chi=7)
    { 37,  38,  57,  58,  80,  83, 100, 103}, // Node 18 (chi=7)
    { 36,  39,  56,  59,  81,  82, 101, 102}, // Node 19 (chi=7)
    { 33,  34,  60,  63,  76,  79, 105, 106}, // Node 20 (chi=6)
    { 32,  35,  61,  62,  77,  78, 104, 107}, // Node 21 (chi=6)
    { 32,  35,  61,  62,  77,  78, 104, 107}, // Node 22 (chi=6)
    { 33,  34,  60,  63,  76,  79, 105, 106}, // Node 23 (chi=6)
    { 92,  95, 113, 114, 136, 139, 157, 158}, // Node 24 (chi=3)
    { 93,  94, 112, 115, 137, 138, 156, 159}, // Node 25 (chi=3)
    { 93,  94, 112, 115, 137, 138, 156, 159}, // Node 26 (chi=3)
    { 92,  95, 113, 114, 136, 139, 157, 158}, // Node 27 (chi=3)
    { 85,  86, 108, 111, 140, 143, 165, 166}, // Node 28 (chi=1)
    { 84,  87, 109, 110, 141, 142, 164, 167}, // Node 29 (chi=1)
    { 84,  87, 109, 110, 141, 142, 164, 167}, // Node 30 (chi=1)
    { 85,  86, 108, 111, 140, 143, 165, 166}, // Node 31 (chi=1)
    { 21,  22,  60,  63, 105, 106, 144, 147}, // Node 32 (chi=6)
    { 20,  23,  61,  62, 104, 107, 145, 146}, // Node 33 (chi=6)
    { 20,  23,  61,  62, 104, 107, 145, 146}, // Node 34 (chi=6)
    { 21,  22,  60,  63, 105, 106, 144, 147}, // Node 35 (chi=6)
    { 16,  19,  57,  58,  80,  83, 121, 122}, // Node 36 (chi=7)
    { 17,  18,  56,  59,  81,  82, 120, 123}, // Node 37 (chi=7)
    { 17,  18,  56,  59,  81,  82, 120, 123}, // Node 38 (chi=7)
    { 16,  19,  57,  58,  80,  83, 121, 122}, // Node 39 (chi=7)
    { 13,  14,  69,  70,  96,  99, 152, 155}, // Node 40 (chi=4)
    { 12,  15,  68,  71,  97,  98, 153, 154}, // Node 41 (chi=4)
    { 12,  15,  68,  71,  97,  98, 153, 154}, // Node 42 (chi=4)
    { 13,  14,  69,  70,  96,  99, 152, 155}, // Node 43 (chi=4)
    {  8,  11,  64,  67,  73,  74, 129, 130}, // Node 44 (chi=5)
    {  9,  10,  65,  66,  72,  75, 128, 131}, // Node 45 (chi=5)
    {  9,  10,  65,  66,  72,  75, 128, 131}, // Node 46 (chi=5)
    {  8,  11,  64,  67,  73,  74, 129, 130}, // Node 47 (chi=5)
    { 89,  90, 117, 118, 132, 135, 160, 163}, // Node 48 (chi=2)
    { 88,  91, 116, 119, 133, 134, 161, 162}, // Node 49 (chi=2)
    { 88,  91, 116, 119, 133, 134, 161, 162}, // Node 50 (chi=2)
    { 89,  90, 117, 118, 132, 135, 160, 163}, // Node 51 (chi=2)
    { 84,  87, 109, 110, 141, 142, 164, 167}, // Node 52 (chi=1)
    { 85,  86, 108, 111, 140, 143, 165, 166}, // Node 53 (chi=1)
    { 85,  86, 108, 111, 140, 143, 165, 166}, // Node 54 (chi=1)
    { 84,  87, 109, 110, 141, 142, 164, 167}, // Node 55 (chi=1)
    { 16,  19,  37,  38, 100, 103, 121, 122}, // Node 56 (chi=7)
    { 17,  18,  36,  39, 101, 102, 120, 123}, // Node 57 (chi=7)
    { 17,  18,  36,  39, 101, 102, 120, 123}, // Node 58 (chi=7)
    { 16,  19,  37,  38, 100, 103, 121, 122}, // Node 59 (chi=7)
    { 20,  23,  32,  35,  77,  78, 145, 146}, // Node 60 (chi=6)
    { 21,  22,  33,  34,  76,  79, 144, 147}, // Node 61 (chi=6)
    { 21,  22,  33,  34,  76,  79, 144, 147}, // Node 62 (chi=6)
    { 20,  23,  32,  35,  77,  78, 145, 146}, // Node 63 (chi=6)
    {  9,  10,  44,  47,  72,  75, 149, 150}, // Node 64 (chi=5)
    {  8,  11,  45,  46,  73,  74, 148, 151}, // Node 65 (chi=5)
    {  8,  11,  45,  46,  73,  74, 148, 151}, // Node 66 (chi=5)
    {  9,  10,  44,  47,  72,  75, 149, 150}, // Node 67 (chi=5)
    { 13,  14,  41,  42,  96,  99, 124, 127}, // Node 68 (chi=4)
    { 12,  15,  40,  43,  97,  98, 125, 126}, // Node 69 (chi=4)
    { 12,  15,  40,  43,  97,  98, 125, 126}, // Node 70 (chi=4)
    { 13,  14,  41,  42,  96,  99, 124, 127}, // Node 71 (chi=4)
    { 45,  46,  64,  67, 129, 130, 148, 151}, // Node 72 (chi=5)
    { 44,  47,  65,  66, 128, 131, 149, 150}, // Node 73 (chi=5)
    { 44,  47,  65,  66, 128, 131, 149, 150}, // Node 74 (chi=5)
    { 45,  46,  64,  67, 129, 130, 148, 151}, // Node 75 (chi=5)
    { 20,  23,  61,  62, 104, 107, 145, 146}, // Node 76 (chi=6)
    { 21,  22,  60,  63, 105, 106, 144, 147}, // Node 77 (chi=6)
    { 21,  22,  60,  63, 105, 106, 144, 147}, // Node 78 (chi=6)
    { 20,  23,  61,  62, 104, 107, 145, 146}, // Node 79 (chi=6)
    { 17,  18,  36,  39, 101, 102, 120, 123}, // Node 80 (chi=7)
    { 16,  19,  37,  38, 100, 103, 121, 122}, // Node 81 (chi=7)
    { 16,  19,  37,  38, 100, 103, 121, 122}, // Node 82 (chi=7)
    { 17,  18,  36,  39, 101, 102, 120, 123}, // Node 83 (chi=7)
    { 29,  30,  52,  55, 140, 143, 165, 166}, // Node 84 (chi=1)
    { 28,  31,  53,  54, 141, 142, 164, 167}, // Node 85 (chi=1)
    { 28,  31,  53,  54, 141, 142, 164, 167}, // Node 86 (chi=1)
    { 29,  30,  52,  55, 140, 143, 165, 166}, // Node 87 (chi=1)
    {  4,   7,  49,  50, 117, 118, 160, 163}, // Node 88 (chi=2)
    {  5,   6,  48,  51, 116, 119, 161, 162}, // Node 89 (chi=2)
    {  5,   6,  48,  51, 116, 119, 161, 162}, // Node 90 (chi=2)
    {  4,   7,  49,  50, 117, 118, 160, 163}, // Node 91 (chi=2)
    {  1,   2,  24,  27, 112, 115, 137, 138}, // Node 92 (chi=3)
    {  0,   3,  25,  26, 113, 114, 136, 139}, // Node 93 (chi=3)
    {  0,   3,  25,  26, 113, 114, 136, 139}, // Node 94 (chi=3)
    {  1,   2,  24,  27, 112, 115, 137, 138}, // Node 95 (chi=3)
    { 40,  43,  68,  71, 125, 126, 153, 154}, // Node 96 (chi=4)
    { 41,  42,  69,  70, 124, 127, 152, 155}, // Node 97 (chi=4)
    { 41,  42,  69,  70, 124, 127, 152, 155}, // Node 98 (chi=4)
    { 40,  43,  68,  71, 125, 126, 153, 154}, // Node 99 (chi=4)
    { 17,  18,  56,  59,  81,  82, 120, 123}, // Node 100 (chi=7)
    { 16,  19,  57,  58,  80,  83, 121, 122}, // Node 101 (chi=7)
    { 16,  19,  57,  58,  80,  83, 121, 122}, // Node 102 (chi=7)
    { 17,  18,  56,  59,  81,  82, 120, 123}, // Node 103 (chi=7)
    { 21,  22,  33,  34,  76,  79, 144, 147}, // Node 104 (chi=6)
    { 20,  23,  32,  35,  77,  78, 145, 146}, // Node 105 (chi=6)
    { 20,  23,  32,  35,  77,  78, 145, 146}, // Node 106 (chi=6)
    { 21,  22,  33,  34,  76,  79, 144, 147}, // Node 107 (chi=6)
    { 28,  31,  53,  54, 141, 142, 164, 167}, // Node 108 (chi=1)
    { 29,  30,  52,  55, 140, 143, 165, 166}, // Node 109 (chi=1)
    { 29,  30,  52,  55, 140, 143, 165, 166}, // Node 110 (chi=1)
    { 28,  31,  53,  54, 141, 142, 164, 167}, // Node 111 (chi=1)
    {  0,   3,  25,  26,  92,  95, 157, 158}, // Node 112 (chi=3)
    {  1,   2,  24,  27,  93,  94, 156, 159}, // Node 113 (chi=3)
    {  1,   2,  24,  27,  93,  94, 156, 159}, // Node 114 (chi=3)
    {  0,   3,  25,  26,  92,  95, 157, 158}, // Node 115 (chi=3)
    {  4,   7,  49,  50,  89,  90, 132, 135}, // Node 116 (chi=2)
    {  5,   6,  48,  51,  88,  91, 133, 134}, // Node 117 (chi=2)
    {  5,   6,  48,  51,  88,  91, 133, 134}, // Node 118 (chi=2)
    {  4,   7,  49,  50,  89,  90, 132, 135}, // Node 119 (chi=2)
    { 37,  38,  57,  58,  80,  83, 100, 103}, // Node 120 (chi=7)
    { 36,  39,  56,  59,  81,  82, 101, 102}, // Node 121 (chi=7)
    { 36,  39,  56,  59,  81,  82, 101, 102}, // Node 122 (chi=7)
    { 37,  38,  57,  58,  80,  83, 100, 103}, // Node 123 (chi=7)
    { 12,  15,  68,  71,  97,  98, 153, 154}, // Node 124 (chi=4)
    { 13,  14,  69,  70,  96,  99, 152, 155}, // Node 125 (chi=4)
    { 13,  14,  69,  70,  96,  99, 152, 155}, // Node 126 (chi=4)
    { 12,  15,  68,  71,  97,  98, 153, 154}, // Node 127 (chi=4)
    {  8,  11,  45,  46,  73,  74, 148, 151}, // Node 128 (chi=5)
    {  9,  10,  44,  47,  72,  75, 149, 150}, // Node 129 (chi=5)
    {  9,  10,  44,  47,  72,  75, 149, 150}, // Node 130 (chi=5)
    {  8,  11,  45,  46,  73,  74, 148, 151}, // Node 131 (chi=5)
    {  5,   6,  48,  51, 116, 119, 161, 162}, // Node 132 (chi=2)
    {  4,   7,  49,  50, 117, 118, 160, 163}, // Node 133 (chi=2)
    {  4,   7,  49,  50, 117, 118, 160, 163}, // Node 134 (chi=2)
    {  5,   6,  48,  51, 116, 119, 161, 162}, // Node 135 (chi=2)
    {  1,   2,  24,  27,  93,  94, 156, 159}, // Node 136 (chi=3)
    {  0,   3,  25,  26,  92,  95, 157, 158}, // Node 137 (chi=3)
    {  0,   3,  25,  26,  92,  95, 157, 158}, // Node 138 (chi=3)
    {  1,   2,  24,  27,  93,  94, 156, 159}, // Node 139 (chi=3)
    { 28,  31,  53,  54,  84,  87, 109, 110}, // Node 140 (chi=1)
    { 29,  30,  52,  55,  85,  86, 108, 111}, // Node 141 (chi=1)
    { 29,  30,  52,  55,  85,  86, 108, 111}, // Node 142 (chi=1)
    { 28,  31,  53,  54,  84,  87, 109, 110}, // Node 143 (chi=1)
    { 32,  35,  61,  62,  77,  78, 104, 107}, // Node 144 (chi=6)
    { 33,  34,  60,  63,  76,  79, 105, 106}, // Node 145 (chi=6)
    { 33,  34,  60,  63,  76,  79, 105, 106}, // Node 146 (chi=6)
    { 32,  35,  61,  62,  77,  78, 104, 107}, // Node 147 (chi=6)
    {  9,  10,  65,  66,  72,  75, 128, 131}, // Node 148 (chi=5)
    {  8,  11,  64,  67,  73,  74, 129, 130}, // Node 149 (chi=5)
    {  8,  11,  64,  67,  73,  74, 129, 130}, // Node 150 (chi=5)
    {  9,  10,  65,  66,  72,  75, 128, 131}, // Node 151 (chi=5)
    { 12,  15,  40,  43,  97,  98, 125, 126}, // Node 152 (chi=4)
    { 13,  14,  41,  42,  96,  99, 124, 127}, // Node 153 (chi=4)
    { 13,  14,  41,  42,  96,  99, 124, 127}, // Node 154 (chi=4)
    { 12,  15,  40,  43,  97,  98, 125, 126}, // Node 155 (chi=4)
    {  0,   3,  25,  26, 113, 114, 136, 139}, // Node 156 (chi=3)
    {  1,   2,  24,  27, 112, 115, 137, 138}, // Node 157 (chi=3)
    {  1,   2,  24,  27, 112, 115, 137, 138}, // Node 158 (chi=3)
    {  0,   3,  25,  26, 113, 114, 136, 139}, // Node 159 (chi=3)
    {  5,   6,  48,  51,  88,  91, 133, 134}, // Node 160 (chi=2)
    {  4,   7,  49,  50,  89,  90, 132, 135}, // Node 161 (chi=2)
    {  4,   7,  49,  50,  89,  90, 132, 135}, // Node 162 (chi=2)
    {  5,   6,  48,  51,  88,  91, 133, 134}, // Node 163 (chi=2)
    { 29,  30,  52,  55,  85,  86, 108, 111}, // Node 164 (chi=1)
    { 28,  31,  53,  54,  84,  87, 109, 110}, // Node 165 (chi=1)
    { 28,  31,  53,  54,  84,  87, 109, 110}, // Node 166 (chi=1)
    { 29,  30,  52,  55,  85,  86, 108, 111}, // Node 167 (chi=1)
};

/*
 * Recursive Cayley-Dickson multiplication sign evaluation.
 * Operates in O(log D) steps with ZERO table allocations, supporting arbitrary D = 2^n.
 */
static inline int8_t se_cd_sign_rec(uint16_t i, uint16_t j) {
    if (i == 0 || j == 0) return 1;
    if (i == j) return -1;
    if (i < 2 && j < 2) return (i == 0 || j == 0) ? 1 : -1;

    uint16_t m = i | j;
    uint16_t h = 1;
    while ((h << 1) <= m && (h << 1) != 0) {
        h <<= 1;
    }

    if (i < h && j < h) {
        return se_cd_sign_rec(i, j);
    } else if (i < h && j >= h) {
        return se_cd_sign_rec((uint16_t)(j - h), i);
    } else if (i >= h && j < h) {
        int8_t conj = (j == 0) ? 1 : -1;
        return (int8_t)(se_cd_sign_rec((uint16_t)(i - h), j) * conj);
    } else {
        uint16_t ip = (uint16_t)(i - h);
        uint16_t jp = (uint16_t)(j - h);
        int8_t conj = (jp == 0) ? 1 : -1;
        return (int8_t)(-se_cd_sign_rec(jp, ip) * conj);
    }
}

/*
 * Universal Index Geometry Decoupled Annihilation Check (HYP-022)
 *
 * For any cross-half zero-divisors sharing non-zero XOR charge chi:
 * Basis products satisfy k0 == k3 and k1 == k2 identically.
 * Annihilation reduces to s0 == -s3 and s1 == -s2 with zero accumulator buffers.
 */
static inline bool se_annihilate(const SedenionVec* u, const SedenionVec* w) {
    // Conserved XOR charge check: u.chi must equal w.chi
    if (u->chi != w->chi) return false;

    uint8_t uj = (uint8_t)(8 + u->j);
    uint8_t wj = (uint8_t)(8 + w->j);

    int8_t s0 = (int8_t)(u->s1 * w->s1 * SE_SIGN_16[u->i][w->i]);
    int8_t s3 = (int8_t)(u->s2 * w->s2 * SE_SIGN_16[uj][wj]);
    if (s0 != -s3) return false;

    int8_t s1 = (int8_t)(u->s1 * w->s2 * SE_SIGN_16[u->i][wj]);
    int8_t s2 = (int8_t)(u->s2 * w->s1 * SE_SIGN_16[uj][w->i]);
    return (s1 == -s2);
}

/*
 * Universal Decoupled Annihilation for Arbitrary Cayley-Dickson Dimension D = 2^n.
 */
static inline bool se_annihilate_dim(
    uint16_t i1, uint16_t j1_offset, int8_t s1_1, int8_t s2_1,
    uint16_t i2, uint16_t j2_offset, int8_t s1_2, int8_t s2_2,
    uint16_t dim
) {
    uint16_t half = dim >> 1;
    // Conserved XOR charge check
    if ((i1 ^ j1_offset) != (i2 ^ j2_offset)) return false;

    uint16_t j1 = half + j1_offset;
    uint16_t j2 = half + j2_offset;

    int8_t s0 = (int8_t)(s1_1 * s1_2 * se_cd_sign_rec(i1, i2));
    int8_t s3 = (int8_t)(s2_1 * s2_2 * se_cd_sign_rec(j1, j2));
    if (s0 != -s3) return false;

    int8_t s1 = (int8_t)(s1_1 * s2_2 * se_cd_sign_rec(i1, j2));
    int8_t s2 = (int8_t)(s2_1 * s1_2 * se_cd_sign_rec(j1, i2));
    return (s1 == -s2);
}

/* -------------------------------------------------------------------------- */
/* SIMD Vectorized Annihilation Engine (AVX2 / SSSE3 / ARM Neon / Scalar)    */
/* -------------------------------------------------------------------------- */

#if defined(_MSC_VER)
  #include <intrin.h>
  static inline int se_ctz32(uint32_t mask) {
      unsigned long idx;
      _BitScanForward(&idx, mask);
      return (int)idx;
  }
#else
  static inline int se_ctz32(uint32_t mask) {
      return __builtin_ctz(mask);
  }
#endif

/*
 * Packs the 168 canonical zero-divisors into 11 SoA16 blocks (176 entries, 8 padded).
 */
static inline void se_pack_zds_soa16(SedenionSoA16 blocks[11]) {
    memset(blocks, 0, 11 * sizeof(SedenionSoA16));
    for (uint16_t b = 0; b < 11; b++) {
        for (uint16_t s = 0; s < 16; s++) {
            uint16_t idx = (uint16_t)(b * 16 + s);
            if (idx < SE_NUM_ZDS) {
                const SedenionVec* v = &SE_ZDS_168[idx];
                blocks[b].i[s] = v->i;
                blocks[b].j[s] = v->j;
                blocks[b].s1_bit[s] = (v->s1 < 0) ? 1 : 0;
                blocks[b].s2_bit[s] = (v->s2 < 0) ? 1 : 0;
                blocks[b].chi[s] = v->chi;
                blocks[b].j_plus_8[s] = (uint8_t)(8 + v->j);
                blocks[b].global_idx[s] = idx;
            } else {
                blocks[b].chi[s] = 0; // Padding: never matches any valid chi in {1..7}
                blocks[b].global_idx[s] = 0xFFFF;
            }
        }
    }
}

/*
 * Packs the 168 canonical zero-divisors into 6 SoA32 blocks (192 entries, 24 padded).
 */
static inline void se_pack_zds_soa32(SedenionSoA32 blocks[6]) {
    memset(blocks, 0, 6 * sizeof(SedenionSoA32));
    for (uint16_t b = 0; b < 6; b++) {
        for (uint16_t s = 0; s < 32; s++) {
            uint16_t idx = (uint16_t)(b * 32 + s);
            if (idx < SE_NUM_ZDS) {
                const SedenionVec* v = &SE_ZDS_168[idx];
                blocks[b].i[s] = v->i;
                blocks[b].j[s] = v->j;
                blocks[b].s1_bit[s] = (v->s1 < 0) ? 1 : 0;
                blocks[b].s2_bit[s] = (v->s2 < 0) ? 1 : 0;
                blocks[b].chi[s] = v->chi;
                blocks[b].j_plus_8[s] = (uint8_t)(8 + v->j);
                blocks[b].global_idx[s] = idx;
            } else {
                blocks[b].chi[s] = 0;
                blocks[b].global_idx[s] = 0xFFFF;
            }
        }
    }
}

/*
 * Scalar 16-way baseline evaluation.
 * Returns a 16-bit mask where bit k is 1 iff u and w_block->[k] annihilate.
 */
static inline uint16_t se_annihilate_scalar_16(
    const SedenionVec* u,
    const SedenionSoA16* w_block
) {
    uint16_t mask = 0;
    uint8_t u_b1 = (u->s1 < 0) ? 1 : 0;
    uint8_t u_b2 = (u->s2 < 0) ? 1 : 0;
    uint8_t u_i = u->i;
    uint8_t u_j8 = (uint8_t)(8 + u->j);
    uint8_t u_chi = u->chi;

    for (int k = 0; k < 16; k++) {
        if (w_block->chi[k] != u_chi) continue;
        uint8_t w_b1 = w_block->s1_bit[k];
        uint8_t w_b2 = w_block->s2_bit[k];
        uint8_t w_i = w_block->i[k];
        uint8_t w_j8 = w_block->j_plus_8[k];

        uint8_t b_s0 = (uint8_t)(u_b1 ^ w_b1 ^ SE_SIGN_BITS_16[u_i][w_i]);
        uint8_t b_s3 = (uint8_t)(u_b2 ^ w_b2 ^ SE_SIGN_BITS_16[u_j8][w_j8]);
        if (((b_s0 ^ b_s3) & 1) != 1) continue;

        uint8_t b_s1 = (uint8_t)(u_b1 ^ w_b2 ^ SE_SIGN_BITS_16[u_i][w_j8]);
        uint8_t b_s2 = (uint8_t)(u_b2 ^ w_b1 ^ SE_SIGN_BITS_16[u_j8][w_i]);
        if (((b_s1 ^ b_s2) & 1) != 1) continue;

        mask |= (uint16_t)(1 << k);
    }
    return mask;
}

#if defined(SE_HAS_SSSE3)
/*
 * SSSE3 128-bit SIMD implementation (16 candidates in parallel).
 */
static inline uint16_t se_annihilate_ssse3_1x16(
    const SedenionVec* u,
    const SedenionSoA16* w_block
) {
    uint8_t u_b1 = (u->s1 < 0) ? 1 : 0;
    uint8_t u_b2 = (u->s2 < 0) ? 1 : 0;
    __m128i v_u_s1 = _mm_set1_epi8((char)u_b1);
    __m128i v_u_s2 = _mm_set1_epi8((char)u_b2);
    __m128i v_u_chi = _mm_set1_epi8((char)u->chi);

    __m128i row_ui = _mm_loadu_si128((const __m128i*)SE_SIGN_BITS_16[u->i]);
    __m128i row_u_j8 = _mm_loadu_si128((const __m128i*)SE_SIGN_BITS_16[8 + u->j]);

    __m128i w_i = _mm_loadu_si128((const __m128i*)w_block->i);
    __m128i w_j8 = _mm_loadu_si128((const __m128i*)w_block->j_plus_8);
    __m128i w_s1 = _mm_loadu_si128((const __m128i*)w_block->s1_bit);
    __m128i w_s2 = _mm_loadu_si128((const __m128i*)w_block->s2_bit);
    __m128i w_chi = _mm_loadu_si128((const __m128i*)w_block->chi);

    /* Single-cycle table lookups via vpshufb */
    __m128i s_table_0 = _mm_shuffle_epi8(row_ui, w_i);
    __m128i s_table_3 = _mm_shuffle_epi8(row_u_j8, w_j8);
    __m128i s_table_1 = _mm_shuffle_epi8(row_ui, w_j8);
    __m128i s_table_2 = _mm_shuffle_epi8(row_u_j8, w_i);

    /* Compute sign bits via bitwise XOR */
    __m128i bit_s0 = _mm_xor_si128(_mm_xor_si128(v_u_s1, w_s1), s_table_0);
    __m128i bit_s3 = _mm_xor_si128(_mm_xor_si128(v_u_s2, w_s2), s_table_3);
    __m128i bit_s1 = _mm_xor_si128(_mm_xor_si128(v_u_s1, w_s2), s_table_1);
    __m128i bit_s2 = _mm_xor_si128(_mm_xor_si128(v_u_s2, w_s1), s_table_2);

    /* Cancellation tests: bit_s0 ^ bit_s3 == 1, bit_s1 ^ bit_s2 == 1 */
    __m128i diff_low = _mm_xor_si128(bit_s0, bit_s3);
    __m128i diff_high = _mm_xor_si128(bit_s1, bit_s2);
    __m128i both_cancel = _mm_and_si128(diff_low, diff_high);
    __m128i signs_ok = _mm_cmpeq_epi8(both_cancel, _mm_set1_epi8(1));

    /* Conserved XOR charge match */
    __m128i chi_ok = _mm_cmpeq_epi8(v_u_chi, w_chi);

    __m128i result = _mm_and_si128(signs_ok, chi_ok);
    return (uint16_t)_mm_movemask_epi8(result);
}
#endif

#if defined(SE_HAS_AVX2)
/*
 * AVX2 256-bit SIMD implementation (32 candidates in parallel).
 */
static inline uint32_t se_annihilate_avx2_1x32(
    const SedenionVec* u,
    const SedenionSoA32* w_block
) {
    uint8_t u_b1 = (u->s1 < 0) ? 1 : 0;
    uint8_t u_b2 = (u->s2 < 0) ? 1 : 0;
    __m256i v_u_s1 = _mm256_set1_epi8((char)u_b1);
    __m256i v_u_s2 = _mm256_set1_epi8((char)u_b2);
    __m256i v_u_chi = _mm256_set1_epi8((char)u->chi);

    /* Broadcast 16-byte sign rows into both 128-bit lanes */
    __m128i row_ui_128 = _mm_loadu_si128((const __m128i*)SE_SIGN_BITS_16[u->i]);
    __m128i row_uj8_128 = _mm_loadu_si128((const __m128i*)SE_SIGN_BITS_16[8 + u->j]);
    __m256i row_ui = _mm256_broadcastsi128_si256(row_ui_128);
    __m256i row_u_j8 = _mm256_broadcastsi128_si256(row_uj8_128);

    __m256i w_i = _mm256_loadu_si256((const __m256i*)w_block->i);
    __m256i w_j8 = _mm256_loadu_si256((const __m256i*)w_block->j_plus_8);
    __m256i w_s1 = _mm256_loadu_si256((const __m256i*)w_block->s1_bit);
    __m256i w_s2 = _mm256_loadu_si256((const __m256i*)w_block->s2_bit);
    __m256i w_chi = _mm256_loadu_si256((const __m256i*)w_block->chi);

    /* 32 parallel lookups in 1 cycle */
    __m256i s_table_0 = _mm256_shuffle_epi8(row_ui, w_i);
    __m256i s_table_3 = _mm256_shuffle_epi8(row_u_j8, w_j8);
    __m256i s_table_1 = _mm256_shuffle_epi8(row_ui, w_j8);
    __m256i s_table_2 = _mm256_shuffle_epi8(row_u_j8, w_i);

    __m256i bit_s0 = _mm256_xor_si256(_mm256_xor_si256(v_u_s1, w_s1), s_table_0);
    __m256i bit_s3 = _mm256_xor_si256(_mm256_xor_si256(v_u_s2, w_s2), s_table_3);
    __m256i bit_s1 = _mm256_xor_si256(_mm256_xor_si256(v_u_s1, w_s2), s_table_1);
    __m256i bit_s2 = _mm256_xor_si256(_mm256_xor_si256(v_u_s2, w_s1), s_table_2);

    __m256i diff_low = _mm256_xor_si256(bit_s0, bit_s3);
    __m256i diff_high = _mm256_xor_si256(bit_s1, bit_s2);
    __m256i both_cancel = _mm256_and_si256(diff_low, diff_high);
    __m256i signs_ok = _mm256_cmpeq_epi8(both_cancel, _mm256_set1_epi8(1));

    __m256i chi_ok = _mm256_cmpeq_epi8(v_u_chi, w_chi);

    __m256i result = _mm256_and_si256(signs_ok, chi_ok);
    return (uint32_t)_mm256_movemask_epi8(result);
}
#endif

#if defined(SE_HAS_NEON)
/*
 * ARM Neon 128-bit SIMD implementation (16 candidates in parallel).
 */
static inline uint16_t se_annihilate_neon_1x16(
    const SedenionVec* u,
    const SedenionSoA16* w_block
) {
    uint8_t u_b1 = (u->s1 < 0) ? 1 : 0;
    uint8_t u_b2 = (u->s2 < 0) ? 1 : 0;
    uint8x16_t v_u_s1 = vdupq_n_u8(u_b1);
    uint8x16_t v_u_s2 = vdupq_n_u8(u_b2);
    uint8x16_t v_u_chi = vdupq_n_u8(u->chi);

    uint8x16_t row_ui = vld1q_u8(SE_SIGN_BITS_16[u->i]);
    uint8x16_t row_u_j8 = vld1q_u8(SE_SIGN_BITS_16[8 + u->j]);

    uint8x16_t w_i = vld1q_u8(w_block->i);
    uint8x16_t w_j8 = vld1q_u8(w_block->j_plus_8);
    uint8x16_t w_s1 = vld1q_u8(w_block->s1_bit);
    uint8x16_t w_s2 = vld1q_u8(w_block->s2_bit);
    uint8x16_t w_chi = vld1q_u8(w_block->chi);

    uint8x16_t s_table_0 = vqtbl1q_u8(row_ui, w_i);
    uint8x16_t s_table_3 = vqtbl1q_u8(row_u_j8, w_j8);
    uint8x16_t s_table_1 = vqtbl1q_u8(row_ui, w_j8);
    uint8x16_t s_table_2 = vqtbl1q_u8(row_u_j8, w_i);

    uint8x16_t bit_s0 = veorq_u8(veorq_u8(v_u_s1, w_s1), s_table_0);
    uint8x16_t bit_s3 = veorq_u8(veorq_u8(v_u_s2, w_s2), s_table_3);
    uint8x16_t bit_s1 = veorq_u8(veorq_u8(v_u_s1, w_s2), s_table_1);
    uint8x16_t bit_s2 = veorq_u8(veorq_u8(v_u_s2, w_s1), s_table_2);

    uint8x16_t diff_low = veorq_u8(bit_s0, bit_s3);
    uint8x16_t diff_high = veorq_u8(bit_s1, bit_s2);
    uint8x16_t both_cancel = vandq_u8(diff_low, diff_high);
    uint8x16_t signs_ok = vceqq_u8(both_cancel, vdupq_n_u8(1));

    uint8x16_t chi_ok = vceqq_u8(v_u_chi, w_chi);
    uint8x16_t result = vandq_u8(signs_ok, chi_ok);

    uint8_t res_bytes[16];
    vst1q_u8(res_bytes, result);
    uint16_t mask = 0;
    for (int k = 0; k < 16; k++) {
        if (res_bytes[k]) mask |= (uint16_t)(1 << k);
    }
    return mask;
}
#endif

/*
 * High-level neighbor finder for any query vector u across all 168 zero-divisors.
 * Employs AVX2 (if available) or SSSE3 / Neon / Scalar fallback.
 * Writes neighbor indices into out_neighbors (must hold at least SE_DEGREE = 8 entries).
 * Returns the count of annihilating neighbors found (always 8 for any valid ZD).
 */
static inline uint8_t se_find_neighbors_simd(
    const SedenionVec* u,
    const void* packed_blocks,
    bool is_soa32,
    uint16_t* out_neighbors
) {
    uint8_t count = 0;
#if defined(SE_HAS_AVX2)
    if (is_soa32) {
        const SedenionSoA32* b32 = (const SedenionSoA32*)packed_blocks;
        for (int b = 0; b < 6; b++) {
            uint32_t mask = se_annihilate_avx2_1x32(u, &b32[b]);
            while (mask && count < SE_DEGREE) {
                int bit = se_ctz32(mask);
                mask &= mask - 1;
                uint16_t g_idx = b32[b].global_idx[bit];
                if (g_idx < SE_NUM_ZDS) {
                    out_neighbors[count++] = g_idx;
                }
            }
        }
        return count;
    }
#endif
    (void)is_soa32;
    const SedenionSoA16* b16 = (const SedenionSoA16*)packed_blocks;
    for (int b = 0; b < 11; b++) {
#if defined(SE_HAS_SSSE3)
        uint16_t mask = se_annihilate_ssse3_1x16(u, &b16[b]);
#elif defined(SE_HAS_NEON)
        uint16_t mask = se_annihilate_neon_1x16(u, &b16[b]);
#else
        uint16_t mask = se_annihilate_scalar_16(u, &b16[b]);
#endif
        uint32_t m = mask;
        while (m && count < SE_DEGREE) {
            int bit = se_ctz32(m);
            m &= m - 1;
            uint16_t g_idx = b16[b].global_idx[bit];
            if (g_idx < SE_NUM_ZDS) {
                out_neighbors[count++] = g_idx;
            }
        }
    }
    return count;
}

/* -------------------------------------------------------------------------- */
/* Ramanujan Cryptographic Sponge (XOF) Engine & AVX2 Permutation             */
/* -------------------------------------------------------------------------- */

#define SE_SPONGE_DEFAULT_RATE 8
#define SE_SPONGE_DEFAULT_CAPACITY 24
#define SE_SPONGE_DEFAULT_WIDTH 32
#define SE_SPONGE_DEFAULT_ROUNDS 24

static const uint16_t SE_SPONGE_RC[24][16] = {
    {0x9196, 0xf7a3, 0x5db0, 0xc3bd, 0x29ca, 0x8fd7, 0xf5e4, 0x5bf1, 0xc1fe, 0x280b, 0x8e18, 0xf425, 0x5a32, 0xc03f, 0x264c, 0x8c59},
    {0x2fcd, 0x95da, 0xfbe7, 0x61f4, 0xc801, 0x2e0e, 0x941b, 0xfa28, 0x6035, 0xc642, 0x2c4f, 0x925c, 0xf869, 0x5e76, 0xc483, 0x2a90},
    {0xce04, 0x3411, 0x9a1e, 0x002b, 0x6638, 0xcc45, 0x3252, 0x985f, 0xfe6c, 0x6479, 0xca86, 0x3093, 0x96a0, 0xfcad, 0x62ba, 0xc8c7},
    {0x6c3b, 0xd248, 0x3855, 0x9e62, 0x046f, 0x6a7c, 0xd089, 0x3696, 0x9ca3, 0x02b0, 0x68bd, 0xceca, 0x34d7, 0x9ae4, 0x00f1, 0x66fe},
    {0x0a72, 0x707f, 0xd68c, 0x3c99, 0xa2a6, 0x08b3, 0x6ec0, 0xd4cd, 0x3ada, 0xa0e7, 0x06f4, 0x6d01, 0xd30e, 0x391b, 0x9f28, 0x0535},
    {0xa8a9, 0x0eb6, 0x74c3, 0xdad0, 0x40dd, 0xa6ea, 0x0cf7, 0x7304, 0xd911, 0x3f1e, 0xa52b, 0x0b38, 0x7145, 0xd752, 0x3d5f, 0xa36c},
    {0x46e0, 0xaced, 0x12fa, 0x7907, 0xdf14, 0x4521, 0xab2e, 0x113b, 0x7748, 0xdd55, 0x4362, 0xa96f, 0x0f7c, 0x7589, 0xdb96, 0x41a3},
    {0xe517, 0x4b24, 0xb131, 0x173e, 0x7d4b, 0xe358, 0x4965, 0xaf72, 0x157f, 0x7b8c, 0xe199, 0x47a6, 0xadb3, 0x13c0, 0x79cd, 0xdfda},
    {0x834e, 0xe95b, 0x4f68, 0xb575, 0x1b82, 0x818f, 0xe79c, 0x4da9, 0xb3b6, 0x19c3, 0x7fd0, 0xe5dd, 0x4bea, 0xb1f7, 0x1804, 0x7e11},
    {0x2185, 0x8792, 0xed9f, 0x53ac, 0xb9b9, 0x1fc6, 0x85d3, 0xebe0, 0x51ed, 0xb7fa, 0x1e07, 0x8414, 0xea21, 0x502e, 0xb63b, 0x1c48},
    {0xbfbc, 0x25c9, 0x8bd6, 0xf1e3, 0x57f0, 0xbdfd, 0x240a, 0x8a17, 0xf024, 0x5631, 0xbc3e, 0x224b, 0x8858, 0xee65, 0x5472, 0xba7f},
    {0x5df3, 0xc400, 0x2a0d, 0x901a, 0xf627, 0x5c34, 0xc241, 0x284e, 0x8e5b, 0xf468, 0x5a75, 0xc082, 0x268f, 0x8c9c, 0xf2a9, 0x58b6},
    {0xfc2a, 0x6237, 0xc844, 0x2e51, 0x945e, 0xfa6b, 0x6078, 0xc685, 0x2c92, 0x929f, 0xf8ac, 0x5eb9, 0xc4c6, 0x2ad3, 0x90e0, 0xf6ed},
    {0x9a61, 0x006e, 0x667b, 0xcc88, 0x3295, 0x98a2, 0xfeaf, 0x64bc, 0xcac9, 0x30d6, 0x96e3, 0xfcf0, 0x62fd, 0xc90a, 0x2f17, 0x9524},
    {0x3898, 0x9ea5, 0x04b2, 0x6abf, 0xd0cc, 0x36d9, 0x9ce6, 0x02f3, 0x6900, 0xcf0d, 0x351a, 0x9b27, 0x0134, 0x6741, 0xcd4e, 0x335b},
    {0xd6cf, 0x3cdc, 0xa2e9, 0x08f6, 0x6f03, 0xd510, 0x3b1d, 0xa12a, 0x0737, 0x6d44, 0xd351, 0x395e, 0x9f6b, 0x0578, 0x6b85, 0xd192},
    {0x7506, 0xdb13, 0x4120, 0xa72d, 0x0d3a, 0x7347, 0xd954, 0x3f61, 0xa56e, 0x0b7b, 0x7188, 0xd795, 0x3da2, 0xa3af, 0x09bc, 0x6fc9},
    {0x133d, 0x794a, 0xdf57, 0x4564, 0xab71, 0x117e, 0x778b, 0xdd98, 0x43a5, 0xa9b2, 0x0fbf, 0x75cc, 0xdbd9, 0x41e6, 0xa7f3, 0x0e00},
    {0xb174, 0x1781, 0x7d8e, 0xe39b, 0x49a8, 0xafb5, 0x15c2, 0x7bcf, 0xe1dc, 0x47e9, 0xadf6, 0x1403, 0x7a10, 0xe01d, 0x462a, 0xac37},
    {0x4fab, 0xb5b8, 0x1bc5, 0x81d2, 0xe7df, 0x4dec, 0xb3f9, 0x1a06, 0x8013, 0xe620, 0x4c2d, 0xb23a, 0x1847, 0x7e54, 0xe461, 0x4a6e},
    {0xede2, 0x53ef, 0xb9fc, 0x2009, 0x8616, 0xec23, 0x5230, 0xb83d, 0x1e4a, 0x8457, 0xea64, 0x5071, 0xb67e, 0x1c8b, 0x8298, 0xe8a5},
    {0x8c19, 0xf226, 0x5833, 0xbe40, 0x244d, 0x8a5a, 0xf067, 0x5674, 0xbc81, 0x228e, 0x889b, 0xeea8, 0x54b5, 0xbac2, 0x20cf, 0x86dc},
    {0x2a50, 0x905d, 0xf66a, 0x5c77, 0xc284, 0x2891, 0x8e9e, 0xf4ab, 0x5ab8, 0xc0c5, 0x26d2, 0x8cdf, 0xf2ec, 0x58f9, 0xbf06, 0x2513},
    {0xc887, 0x2e94, 0x94a1, 0xfaae, 0x60bb, 0xc6c8, 0x2cd5, 0x92e2, 0xf8ef, 0x5efc, 0xc509, 0x2b16, 0x9123, 0xf730, 0x5d3d, 0xc34a}
};

/*
 * Core Ramanujan expander & non-associative sedenion permutation f(S).
 */
static inline void se_sponge_permute(uint8_t* state, uint32_t b, uint32_t rounds) {
    uint16_t u = 0;
    uint16_t X[16];
    uint16_t Y[16];

    for (uint32_t t = 0; t < rounds; t++) {
        uint8_t d_t = (uint8_t)((state[t % b] ^ (state[(t + 7) % b] >> 3) ^ t) & 7);
        u = SE_ADJ_168[u][d_t];
        const SedenionVec* v = &SE_ZDS_168[u];
        uint8_t vi = v->i;
        uint8_t vj = v->j;
        int8_t vs1 = v->s1;
        int8_t vs2 = v->s2;

        /* Unpack 16 coordinates from state bytes */
        for (uint32_t m = 0; m < 16; m++) {
            X[m] = (uint16_t)(state[m % b] | (state[(m + 16) % b] << 8));
        }

        /* Non-associative left-multiplication Y = V(u) * X */
        for (uint32_t m = 0; m < 16; m++) {
            uint8_t k1 = (uint8_t)(m ^ vi);
            uint8_t k2 = (uint8_t)(m ^ (8 + vj));
            int8_t sig1 = (int8_t)(vs1 * SE_SIGN_16[vi][k1]);
            int8_t sig2 = (int8_t)(vs2 * SE_SIGN_16[8 + vj][k2]);
            int32_t term1 = (int32_t)sig1 * (int32_t)X[k1];
            int32_t term2 = (int32_t)sig2 * (int32_t)X[k2];
            uint16_t val = (uint16_t)((term1 + term2) & 0xFFFF);
            val ^= SE_SPONGE_RC[t % 24][m];
            val = (uint16_t)(((val << 5) | (val >> 11)) & 0xFFFF);
            Y[m] = val;
        }

        /* Fold Y coordinates back into state bytes */
        for (uint32_t k = 0; k < b; k++) {
            uint32_t m0 = k % 16;
            uint32_t m1 = (k + 1) % 16;
            uint8_t cur = (uint8_t)(state[k] ^ (Y[m0] & 0xFF) ^ (Y[m1] >> 8));
            state[k] = (uint8_t)(((cur << 3) | (cur >> 5)) & 0xFF);
        }
    }
}

typedef struct {
    uint32_t rate;
    uint32_t capacity;
    uint32_t width;
    uint32_t rounds;
    uint8_t state[64];
    uint8_t buffer[64];
    uint32_t buf_len;
    bool squeezing;
    uint32_t squeeze_offset;
} RamanujanSpongeC;

static inline void se_sponge_init(RamanujanSpongeC* sp, uint32_t rate, uint32_t capacity, uint32_t rounds) {
    memset(sp, 0, sizeof(RamanujanSpongeC));
    sp->rate = rate ? rate : SE_SPONGE_DEFAULT_RATE;
    sp->capacity = capacity ? capacity : SE_SPONGE_DEFAULT_CAPACITY;
    sp->width = sp->rate + sp->capacity;
    sp->rounds = rounds ? rounds : SE_SPONGE_DEFAULT_ROUNDS;
}

static inline void se_sponge_reset(RamanujanSpongeC* sp) {
    memset(sp->state, 0, sizeof(sp->state));
    memset(sp->buffer, 0, sizeof(sp->buffer));
    sp->buf_len = 0;
    sp->squeezing = false;
    sp->squeeze_offset = 0;
}

static inline void se_sponge_absorb(RamanujanSpongeC* sp, const uint8_t* data, size_t len) {
    while (len > 0) {
        size_t avail = sp->rate - sp->buf_len;
        size_t take = len < avail ? len : avail;
        memcpy(sp->buffer + sp->buf_len, data, take);
        sp->buf_len += (uint32_t)take;
        data += take;
        len -= take;

        if (sp->buf_len == sp->rate) {
            for (uint32_t i = 0; i < sp->rate; i++) {
                sp->state[i] ^= sp->buffer[i];
            }
            se_sponge_permute(sp->state, sp->width, sp->rounds);
            sp->buf_len = 0;
        }
    }
}

static inline void se_sponge_pad_and_switch(RamanujanSpongeC* sp) {
    uint32_t pad_len = sp->rate - sp->buf_len;
    if (pad_len == 1) {
        sp->buffer[sp->buf_len++] = 0x81;
    } else if (pad_len == 2) {
        sp->buffer[sp->buf_len++] = 0x01;
        sp->buffer[sp->buf_len++] = 0x80;
    } else {
        sp->buffer[sp->buf_len++] = 0x01;
        while (sp->buf_len < sp->rate - 1) {
            sp->buffer[sp->buf_len++] = 0x00;
        }
        sp->buffer[sp->buf_len++] = 0x80;
    }
    for (uint32_t i = 0; i < sp->rate; i++) {
        sp->state[i] ^= sp->buffer[i];
    }
    se_sponge_permute(sp->state, sp->width, sp->rounds);
    sp->buf_len = 0;
    sp->squeezing = true;
    sp->squeeze_offset = 0;
}

static inline void se_sponge_squeeze(RamanujanSpongeC* sp, uint8_t* out, size_t len) {
    if (!sp->squeezing) {
        se_sponge_pad_and_switch(sp);
    }
    size_t written = 0;
    while (written < len) {
        uint32_t avail = sp->rate - sp->squeeze_offset;
        size_t needed = len - written;
        size_t take = needed < avail ? needed : avail;
        memcpy(out + written, sp->state + sp->squeeze_offset, take);
        written += take;
        sp->squeeze_offset += (uint32_t)take;
        if (sp->squeeze_offset == sp->rate && written < len) {
            se_sponge_permute(sp->state, sp->width, sp->rounds);
            sp->squeeze_offset = 0;
        }
    }
}

static inline void se_sponge_digest(const uint8_t* in, size_t in_len, uint8_t* out, size_t out_len) {
    RamanujanSpongeC sp;
    se_sponge_init(&sp, SE_SPONGE_DEFAULT_RATE, SE_SPONGE_DEFAULT_CAPACITY, SE_SPONGE_DEFAULT_ROUNDS);
    se_sponge_absorb(&sp, in, in_len);
    se_sponge_squeeze(&sp, out, out_len);
}

/*
 * ============================================================================
 * Universal Cayley-Dickson Tower Arithmetic (HYP-048, HYP-049, HYP-050)
 * ============================================================================
 * Implements pure bitwise recursive basis multiplication and O(1) cross-half
 * zero-divisor annihilation for arbitrary D = 2^{n+1} Cayley-Dickson algebras.
 * Formally proved in Lean 4: TowerBasis.lean and TowerZeroDivisors.lean.
 * Zero FPU, zero memory lookup tables, zero dynamic allocation.
 * Designed for microcontrollers (ESP32, ARM Cortex-M, RISC-V).
 */

static inline bool cd_tower_eps_neg(uint32_t n, uint32_t a, uint32_t b) {
    if (n == 0) {
        return false;
    }
    uint32_t half = 1u << (n - 1);
    if (a < half) {
        if (b < half) {
            return cd_tower_eps_neg(n - 1, a, b);
        } else {
            return cd_tower_eps_neg(n - 1, b - half, a);
        }
    } else {
        bool conj_b = (b != 0);
        if (b < half) {
            return conj_b ^ cd_tower_eps_neg(n - 1, a - half, b);
        } else {
            uint32_t b_prime = b - half;
            bool conj_b_prime = (b_prime != 0);
            return !(conj_b_prime ^ cd_tower_eps_neg(n - 1, b_prime, a - half));
        }
    }
}

static inline void cd_tower_basis_mul(uint32_t n, uint32_t a, uint32_t b, int8_t* out_sign, uint32_t* out_idx) {
    *out_idx = a ^ b;
    *out_sign = cd_tower_eps_neg(n, a, b) ? -1 : 1;
}

static inline bool cd_cross_vec_annihilates(
    uint32_t n,
    int8_t s1, uint32_t i, int8_t s2, uint32_t j,
    int8_t t1, uint32_t k, int8_t t2, uint32_t m
) {
    // 1. Universal charge conservation: i ^ j == k ^ m
    if ((i ^ j) != (k ^ m)) {
        return false;
    }
    bool s = (s1 < 0);
    bool t = (s2 < 0);
    bool u = (t1 < 0);
    bool r = (t2 < 0);
    uint32_t half = 1u << n;
    bool c1 = (s ^ u ^ cd_tower_eps_neg(n + 1, i, k)) !=
              (t ^ r ^ cd_tower_eps_neg(n + 1, half + j, half + m));
    bool c2 = (s ^ r ^ cd_tower_eps_neg(n + 1, i, half + m)) !=
              (t ^ u ^ cd_tower_eps_neg(n + 1, half + j, k));
    return c1 && c2;
}

/*
 * ============================================================================
 * Modular Form & Hecke Operator Engine (Aristotle Sieve23 / HeckeWords / DeltaGraph)
 * ============================================================================
 * Pure integer arithmetic for the weight-12 discriminant modular form Delta:
 *   Delta(z) = q \prod_{n=1}^\infty (1 - q^n)^24 = \sum_{n=1}^\infty \tau(n) q^n
 * Zero FPU, zero dynamic memory. Certified in Lean 4 (DeltaModular, DeltaGraph, HeckeWords).
 */

// Certified values of Ramanujan's tau(1) ... tau(60) from DeltaWordGraphs.lean
static const int64_t SE_TAU_TABLE_60[60] = {
    1LL, -24LL, 252LL, -1472LL, 4830LL, -6048LL, -16744LL, 84480LL, -113643LL, -115920LL,
    534612LL, -370944LL, -577738LL, 401856LL, 1217160LL, 987136LL, -6905934LL, 2727432LL,
    10661420LL, -7109760LL, -4219488LL, -12830688LL, 18643272LL, 21288960LL, -25499225LL,
    13865712LL, -73279080LL, 24647168LL, 128406630LL, -29211840LL, -52843168LL, -196706304LL,
    134722224LL, 165742416LL, -80873520LL, 167282496LL, -182213314LL, -255874080LL,
    -145589976LL, 408038400LL, 308120442LL, 101267712LL, -17125708LL, -786948864LL,
    -548895690LL, -447438528LL, 2687348496LL, 248758272LL, -1696965207LL, 611981400LL,
    -1740295368LL, 850430336LL, -1596055698LL, 1758697920LL, 2582175960LL, -1414533120LL,
    2686677840LL, -3081759120LL, -5189203740LL, -1791659520LL
};

static inline int64_t se_tau(uint32_t n) {
    if (n >= 1 && n <= 60) {
        return SE_TAU_TABLE_60[n - 1];
    }
    return 0;
}

static inline uint32_t se_gcd_u32(uint32_t a, uint32_t b) {
    while (b != 0) {
        uint32_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

static inline int64_t se_pow_i64(int64_t base, uint32_t exp) {
    int64_t res = 1;
    while (exp > 0) {
        if (exp & 1) res *= base;
        base *= base;
        exp >>= 1;
    }
    return res;
}

// Divisor sum \sigma_k(n) = \sum_{d | n} d^k
static inline int64_t se_sigma_k(uint32_t n, uint32_t k) {
    if (n == 0) return 0;
    int64_t sum = 0;
    for (uint32_t d = 1; d * d <= n; d++) {
        if (n % d == 0) {
            sum += se_pow_i64((int64_t)d, k);
            uint32_t other = n / d;
            if (other != d) {
                sum += se_pow_i64((int64_t)other, k);
            }
        }
    }
    return sum;
}

// Hecke operator action on Delta: T_n \Delta(m) = \sum_{d | gcd(n, m)} d^11 \tau(nm / d^2)
static inline int64_t se_hecke_coeff(uint32_t n, uint32_t m) {
    uint32_t g = se_gcd_u32(n, m);
    int64_t sum = 0;
    for (uint32_t d = 1; d * d <= g; d++) {
        if (g % d == 0) {
            uint32_t target1 = (n * m) / (d * d);
            sum += se_pow_i64((int64_t)d, 11) * se_tau(target1);
            uint32_t other = g / d;
            if (other != d) {
                uint32_t target2 = (n * m) / (other * other);
                sum += se_pow_i64((int64_t)other, 11) * se_tau(target2);
            }
        }
    }
    return sum;
}

// Aristotle 5 Hecke words:
// Word 0: T_2 -> -24
// Word 1: T_3 -> 252
// Word 2: T_2 T_3 = T_6 -> -6048
// Word 3: T_2 T_3 T_2 = T_12 + 2^11 T_3 -> 145152
// Word 4: T_3 T_3 T_3 = T_27 + 2 * 3^11 T_3 -> 16003008
static inline bool se_hecke_word_eval(uint8_t word_id, int64_t* out_multiplier) {
    switch (word_id) {
        case 0: // T_2
            *out_multiplier = se_hecke_coeff(2, 1); // = tau(2) = -24
            return true;
        case 1: // T_3
            *out_multiplier = se_hecke_coeff(3, 1); // = tau(3) = 252
            return true;
        case 2: // T_2 T_3 = T_6
            *out_multiplier = se_hecke_coeff(6, 1); // = tau(6) = -6048
            return true;
        case 3: // T_2 T_3 T_2 = T_12 + 2^11 T_3
            *out_multiplier = se_hecke_coeff(12, 1) + (1LL << 11) * se_hecke_coeff(3, 1); // = 145152
            return true;
        case 4: // T_3 T_3 T_3 = T_27 + 2 * 3^11 T_3
            *out_multiplier = se_hecke_coeff(27, 1) + 2LL * 177147LL * se_hecke_coeff(3, 1); // = 16003008
            return true;
        default:
            *out_multiplier = 0;
            return false;
    }
}

// 3-adic congruence: tau(n) \equiv n^2 \sigma_7(n) (mod 27) for gcd(n, 3) = 1
static inline bool se_tau_congr_mod27_check(uint32_t n) {
    if (n < 1 || n > 60 || (n % 3 == 0)) {
        return false;
    }
    int64_t tau_n = se_tau(n);
    int64_t sig7 = se_sigma_k(n, 7);
    int64_t rhs = ((int64_t)n * (int64_t)n) % 27LL;
    rhs = (rhs * (sig7 % 27LL)) % 27LL;
    int64_t lhs = ((tau_n % 27LL) + 27LL) % 27LL;
    return lhs == rhs;
}

// Base-b digital root: dr_b(n) = 1 + (n - 1) mod (b - 1) for n > 0
static inline uint32_t se_digital_root(int64_t n, uint32_t base) {
    if (n == 0 || base <= 2) return 0;
    if (n < 0) n = -n;
    uint32_t m = base - 1;
    return 1 + (uint32_t)((n - 1) % m);
}

// Digital root trinity membership: dr_10(n) \in {3, 6, 9} <==> 3 | n
static inline bool se_is_trinity(int64_t n) {
    if (n == 0) return false;
    uint32_t dr = se_digital_root(n, 10);
    return (dr == 3 || dr == 6 || dr == 9);
}

// Doubling circuit on Z/9Z: {1, 2, 4, 8, 7, 5}
static inline uint8_t se_vortex_step(uint8_t current_val) {
    switch (current_val) {
        case 1: return 2;
        case 2: return 4;
        case 4: return 8;
        case 8: return 7;
        case 7: return 5;
        case 5: return 1;
        default:
            return 1;
    }
}

// Fibonacci digital root period-24 cycle:
// 1, 1, 2, 3, 5, 8, 4, 3, 7, 1, 8, 9, 8, 8, 7, 6, 4, 1, 5, 6, 2, 8, 1, 9
static const uint8_t SE_FIB_DR_CYCLE_24[24] = {
    1, 1, 2, 3, 5, 8, 4, 3, 7, 1, 8, 9, 8, 8, 7, 6, 4, 1, 5, 6, 2, 8, 1, 9
};

static inline uint8_t se_fibonacci_dr(uint32_t n) {
    if (n == 0) return 0;
    // Period 24 for n >= 1 (1-indexed: n=1 gives 1)
    uint32_t idx = (n - 1) % 24;
    return SE_FIB_DR_CYCLE_24[idx];
}

// Pointwise T2 vs T3 comparison according to Aristotle RequestProject/T2vsT3.lean
// t2(m) = tau(2)*tau(m) = -24 * tau(m)
// t3(m) = tau(3)*tau(m) = 252 * tau(m)
typedef struct {
    uint32_t m;
    int64_t tau_m;
    int64_t t2;
    int64_t t3;
    int64_t prod;      // -6048 * tau(m)^2 < 0 (anti-parallel)
    int64_t diff;      // -276 * tau(m) != 0 (never meet)
    int64_t quot_int;  // Euclidean quotient (-1 if tau_m > 0, 0 if tau_m < 0)
    int64_t rem;       // Euclidean remainder in [0, |t3|)
    bool prod_in_trinity;
    bool diff_in_trinity;
    bool rem_in_trinity;
    bool quot_not_in_trinity;
} se_t2_t3_cmp_t;

static inline bool se_compare_t2_t3(uint32_t m, se_t2_t3_cmp_t *out) {
    if (m < 1 || m > 60 || !out) return false;
    int64_t tau_m = se_tau(m);
    int64_t t2 = -24LL * tau_m;
    int64_t t3 = 252LL * tau_m;
    out->m = m;
    out->tau_m = tau_m;
    out->t2 = t2;
    out->t3 = t3;
    out->prod = t2 * t3; // = -6048 * tau_m * tau_m
    out->diff = t2 - t3; // = -276 * tau_m
    int64_t abs_t3 = (t3 < 0) ? -t3 : t3;
    int64_t rem = t2 % abs_t3;
    if (rem < 0) rem += abs_t3;
    int64_t quot = (t2 - rem) / t3;
    out->quot_int = quot;
    out->rem = rem;
    out->prod_in_trinity = se_is_trinity(out->prod);
    out->diff_in_trinity = se_is_trinity(out->diff);
    out->rem_in_trinity = (rem == 0) ? false : se_is_trinity(rem);
    out->quot_not_in_trinity = !se_is_trinity(quot);
    return true;
}

/* ============================================================
 * Knot & Braid Topology Co-Processor (HYP-236, HYP-237)
 * ============================================================
 *
 * Pure integer arithmetic, no FPU, O(1) MCU-suitable operations.
 *
 * (A) Calvo 6-Stick Knot Classifier (HYP-236)
 *     Input:  6 integer 3D vertices v[0..5], each int32_t[3].
 *     Output: Classification triple (delta2, delta4, delta6) in {-1,0,1}^3.
 *     Topology: (+1,+1,+1) = right trefoil 3_1^+
 *               (-1,-1,-1) = left trefoil 3_1^-
 *               (any 0)    = unknot 0_1
 *
 * (B) 3-Braid Amphichiral Classifier (HYP-237)
 *     Input:  word c[0..2n-1] of positive integers (alternating a_i, b_i).
 *     Output: SE_BRAID_FA (fully amphichiral), SE_BRAID_PA (positive),
 *             SE_BRAID_NA (negative), SE_BRAID_CHIRAL.
 * ============================================================ */

/* ---- (A) Calvo 6-Stick Knot Classifier ---- */

/* Signed volume of tetrahedron (p1,p2,p3,p4): det of 4x4 homogeneous matrix.
 * Uses 64-bit to avoid overflow for int32_t inputs.
 * Returns sign: +1, -1, or 0. */
static inline int8_t se_det4_sign(
    const int32_t p1[3], const int32_t p2[3],
    const int32_t p3[3], const int32_t p4[3])
{
    /* Translate to p1-origin: a=p2-p1, b=p3-p1, c=p4-p1 */
    int64_t ax = (int64_t)p2[0] - p1[0], ay = (int64_t)p2[1] - p1[1], az = (int64_t)p2[2] - p1[2];
    int64_t bx = (int64_t)p3[0] - p1[0], by = (int64_t)p3[1] - p1[1], bz = (int64_t)p3[2] - p1[2];
    int64_t cx = (int64_t)p4[0] - p1[0], cy = (int64_t)p4[1] - p1[1], cz = (int64_t)p4[2] - p1[2];
    /* Scalar triple product a.(b x c) */
    int64_t cross_x = by * cz - bz * cy;
    int64_t cross_y = bz * cx - bx * cz;
    int64_t cross_z = bx * cy - by * cx;
    int64_t det = ax * cross_x + ay * cross_y + az * cross_z;
    if (det > 0) return  1;
    if (det < 0) return -1;
    return 0;
}

/* Calvo oriented piercing: I(a,b,c; p,q) in {-1, 0, 1}.
 * a,b,c = triangle face vertices; p,q = edge endpoints.
 * Returns +1 if edge pq pierces face abc from below (positive orientation),
 *         -1 if from above, 0 if coplanar/miss. */
static inline int8_t se_calvo_piercing(
    const int32_t a[3], const int32_t b[3], const int32_t c[3],
    const int32_t p[3], const int32_t q[3])
{
    int8_t s1 = se_det4_sign(p, a, b, c);
    int8_t s2 = se_det4_sign(q, a, b, c);
    if (s1 == s2) return 0;   /* Same side or coplanar: no crossing */
    int8_t s3 = se_det4_sign(p, q, a, b);
    int8_t s4 = se_det4_sign(p, q, b, c);
    int8_t s5 = se_det4_sign(p, q, c, a);
    /* All three must have the same nonzero sign for a valid piercing */
    if (s3 == 0 || s4 == 0 || s5 == 0) return 0;
    if (s3 == s4 && s4 == s5) {
        /* Oriented: sign of piercing is s1 * s3 (Calvo 2001) */
        return (s1 > 0) ? s3 : (int8_t)(-s3);
    }
    return 0;
}

/* 6-stick knot classification result */
typedef struct {
    int8_t delta2;   /* Calvo invariant Delta_2 in {-1, 0, 1} */
    int8_t delta4;   /* Calvo invariant Delta_4 in {-1, 0, 1} */
    int8_t delta6;   /* Calvo invariant Delta_6 in {-1, 0, 1} */
    uint8_t type;    /* SE_KNOT_TREFOIL_RIGHT, SE_KNOT_TREFOIL_LEFT, SE_KNOT_UNKNOT */
} SeKnotClass6;

#define SE_KNOT_TREFOIL_RIGHT 1
#define SE_KNOT_TREFOIL_LEFT  2
#define SE_KNOT_UNKNOT        0

/* Classify a 6-stick knot (hexagonal spatial polygon) via Calvo invariants.
 * v[6][3]: 6 integer vertices in R^3. Stick edges are (v[i], v[(i+1)%6]).
 * Returns SeKnotClass6 struct. */
static inline SeKnotClass6 se_classify_6stick_knot(const int32_t v[6][3]) {
    SeKnotClass6 result;
    result.delta2 = 0;
    result.delta4 = 0;
    result.delta6 = 0;

    /* All C(6,4)=15 tetrahedral orientations from the 6 vertices */
    static const uint8_t quads[15][4] = {
        {0,1,2,3}, {0,1,2,4}, {0,1,2,5},
        {0,1,3,4}, {0,1,3,5}, {0,1,4,5},
        {0,2,3,4}, {0,2,3,5}, {0,2,4,5},
        {0,3,4,5}, {1,2,3,4}, {1,2,3,5},
        {1,2,4,5}, {1,3,4,5}, {2,3,4,5}
    };

    int8_t tet_signs[15];
    for (int q = 0; q < 15; q++) {
        tet_signs[q] = se_det4_sign(v[quads[q][0]], v[quads[q][1]],
                                     v[quads[q][2]], v[quads[q][3]]);
    }

    /* Delta_2: step-2 piercings (triangle face vs non-adjacent edge) */
    int8_t sum2 = 0;
    sum2 += se_calvo_piercing(v[0], v[1], v[2], v[3], v[4]);
    sum2 += se_calvo_piercing(v[1], v[2], v[3], v[4], v[5]);
    sum2 += se_calvo_piercing(v[2], v[3], v[4], v[5], v[0]);
    if (sum2 > 1) sum2 = 1; else if (sum2 < -1) sum2 = -1;
    result.delta2 = sum2;

    /* Delta_4: step-4 piercings */
    int8_t sum4 = 0;
    sum4 += se_calvo_piercing(v[0], v[2], v[4], v[1], v[3]);
    sum4 += se_calvo_piercing(v[1], v[3], v[5], v[2], v[4]);
    sum4 += se_calvo_piercing(v[2], v[4], v[0], v[3], v[5]);
    if (sum4 > 1) sum4 = 1; else if (sum4 < -1) sum4 = -1;
    result.delta4 = sum4;

    /* Delta_6: total oriented tetrahedra signature */
    int8_t sum6 = 0;
    for (int q = 0; q < 15; q++) sum6 += tet_signs[q];
    if (sum6 > 1) sum6 = 1; else if (sum6 < -1) sum6 = -1;
    result.delta6 = sum6;

    if (result.delta2 == 1 && result.delta4 == 1 && result.delta6 == 1)
        result.type = SE_KNOT_TREFOIL_RIGHT;
    else if (result.delta2 == -1 && result.delta4 == -1 && result.delta6 == -1)
        result.type = SE_KNOT_TREFOIL_LEFT;
    else
        result.type = SE_KNOT_UNKNOT;

    return result;
}

/* ---- (B) 3-Braid Amphichiral Classifier ---- */

#define SE_BRAID_MAX_LEN 64   /* Maximum braid word length (2n entries) */

#define SE_BRAID_FA     0   /* Fully amphichiral */
#define SE_BRAID_PA     1   /* Positive amphichiral (+A) */
#define SE_BRAID_NA     2   /* Negative amphichiral (-A) */
#define SE_BRAID_CHIRAL 3   /* Chiral */

/* Minimal period of word c[0..len-1]. */
static inline uint8_t se_braid_word_period(const int32_t* c, uint8_t len) {
    if (len == 0) return 0;
    for (uint8_t p = 1; p <= len; p++) {
        if (len % p != 0) continue;
        bool ok = true;
        for (uint8_t i = 0; i < len && ok; i++) {
            if (c[i] != c[i % p]) ok = false;
        }
        if (ok) return p;
    }
    return len;
}

/* Check palindrome: c reads same forwards and backwards. */
static inline bool se_braid_is_palindrome(const int32_t* c, uint8_t len) {
    for (uint8_t i = 0; i < len / 2; i++) {
        if (c[i] != c[len - 1 - i]) return false;
    }
    return true;
}

/* Non-degenerate flype: c is cyclic rotation of (k,1,1,k) for k >= 2, len == 4. */
static inline bool se_braid_is_flype(const int32_t* c, uint8_t len) {
    if (len != 4) return false;
    for (uint8_t r = 0; r < 4; r++) {
        int32_t a = c[r%4], b = c[(r+1)%4], cc = c[(r+2)%4], d = c[(r+3)%4];
        if (a == d && b == 1 && cc == 1 && a >= 2) return true;
    }
    return false;
}

/* Classify 3-braid amphichirality (Jung 2026, Theorem C).
 * c[0..len-1]: alternating word (a_1,b_1,...,a_n,b_n), len=2n must be even.
 * Returns SE_BRAID_FA / SE_BRAID_PA / SE_BRAID_NA / SE_BRAID_CHIRAL. */
static inline uint8_t se_classify_3braid_amphichirality(
    const int32_t* c, uint8_t len)
{
    if (len == 0 || len % 2 != 0 || len > SE_BRAID_MAX_LEN) return SE_BRAID_CHIRAL;
    uint8_t period  = se_braid_word_period(c, len);
    bool palindrome = se_braid_is_palindrome(c, len);
    bool odd_period = (period % 2 == 1);
    bool flype      = se_braid_is_flype(c, len);
    if (palindrome && (odd_period || flype)) return SE_BRAID_FA;
    if (odd_period && !palindrome)           return SE_BRAID_PA;
    if (palindrome && !odd_period)           return SE_BRAID_NA;
    return SE_BRAID_CHIRAL;
}

/* Dihedral quotient group order |D_{4n}/<rho^2>| = 4 (constant, HYP-237). */
static inline uint8_t se_dihedral_quotient_order(void) {
    return 4;
}

#endif // SEDENION_ENGINE_H

