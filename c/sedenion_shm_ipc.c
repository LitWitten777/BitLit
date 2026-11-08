/*
 * src/c/sedenion_shm_ipc.c
 * =============================================================================
 * Sovereign High-Performance Zero-GC Binary Shared-Memory IPC Implementation.
 * =============================================================================
 */

#include "sedenion_shm_ipc.h"
#include <string.h>
#include <immintrin.h>

// Static assert for 58-byte packet constraint
_Static_assert(sizeof(SovereignStatePacket58) == 58, "SovereignStatePacket58 must be exactly 58 bytes");

// CRC-16-CCITT (Polynomial 0x1021, init 0xFFFF)
uint16_t sov_crc16(const uint8_t* data, size_t len) {
    uint16_t crc = 0xFFFF;
    for (size_t i = 0; i < len; i++) {
        crc ^= (uint16_t)data[i] << 8;
        for (int j = 0; j < 8; j++) {
            if (crc & 0x8000) {
                crc = (crc << 1) ^ 0x1021;
            } else {
                crc = crc << 1;
            }
        }
    }
    return crc;
}

uint16_t float_to_fp16(float f) {
#if defined(__F16C__)
    return (uint16_t)_cvtss_sh(f, 0);
#else
    // Software fallback
    uint32_t x;
    memcpy(&x, &f, 4);
    uint16_t sign = (x >> 16) & 0x8000;
    int32_t exp = ((x >> 23) & 0xFF) - 127 + 15;
    uint32_t mant = x & 0x7FFFFF;
    if (exp <= 0) {
        return sign;
    } else if (exp >= 31) {
        return sign | 0x7C00;
    }
    return sign | (exp << 10) | (mant >> 13);
#endif
}

float fp16_to_float(uint16_t h) {
#if defined(__F16C__)
    return _cvtsh_ss(h);
#else
    uint32_t sign = (h & 0x8000) << 16;
    uint32_t exp = (h >> 10) & 0x1F;
    uint32_t mant = h & 0x03FF;
    uint32_t f_bits;
    if (exp == 0) {
        f_bits = sign;
    } else if (exp == 31) {
        f_bits = sign | 0x7F800000 | (mant << 13);
    } else {
        f_bits = sign | ((exp + 127 - 15) << 23) | (mant << 13);
    }
    float f;
    memcpy(&f, &f_bits, 4);
    return f;
#endif
}

void float_batch_to_fp16_16(const float* in_f32, uint16_t* out_fp16) {
#if defined(__AVX2__) && defined(__F16C__)
    __m256 v0 = _mm256_loadu_ps(&in_f32[0]);
    __m256 v1 = _mm256_loadu_ps(&in_f32[8]);
    __m128i h0 = _mm256_cvtps_ph(v0, 0);
    __m128i h1 = _mm256_cvtps_ph(v1, 0);
    _mm_storeu_si128((__m128i*)&out_fp16[0], h0);
    _mm_storeu_si128((__m128i*)&out_fp16[8], h1);
#else
    for (int i = 0; i < 16; i++) {
        out_fp16[i] = float_to_fp16(in_f32[i]);
    }
#endif
}

void fp16_batch_to_float_16(const uint16_t* in_fp16, float* out_f32) {
#if defined(__AVX2__) && defined(__F16C__)
    __m128i h0 = _mm_loadu_si128((const __m128i*)&in_fp16[0]);
    __m128i h1 = _mm_loadu_si128((const __m128i*)&in_fp16[8]);
    __m256 v0 = _mm256_cvtph_ps(h0);
    __m256 v1 = _mm256_cvtph_ps(h1);
    _mm256_storeu_ps(&out_f32[0], v0);
    _mm256_storeu_ps(&out_f32[8], v1);
#else
    for (int i = 0; i < 16; i++) {
        out_f32[i] = fp16_to_float(in_fp16[i]);
    }
#endif
}

size_t sov_ring_total_bytes(uint32_t capacity) {
    return sizeof(SovereignRingHeader) + (size_t)capacity * sizeof(SovereignStatePacket58);
}

void sov_ring_init(void* buffer, uint32_t capacity) {
    SovereignRingHeader* hdr = (SovereignRingHeader*)buffer;
    hdr->magic = SOV_RING_MAGIC;
    hdr->capacity = capacity;
    hdr->head = 0;
    hdr->tail = 0;
    hdr->total_written = 0;
    hdr->total_dropped = 0;
}

uint32_t sov_ring_count(const void* buffer) {
    const SovereignRingHeader* hdr = (const SovereignRingHeader*)buffer;
    uint32_t head = hdr->head;
    uint32_t tail = hdr->tail;
    if (head >= tail) {
        return head - tail;
    } else {
        return hdr->capacity - (tail - head);
    }
}

bool sov_ring_push(void* buffer, const SovereignStatePacket58* packet) {
    SovereignRingHeader* hdr = (SovereignRingHeader*)buffer;
    uint32_t next_head = (hdr->head + 1) % hdr->capacity;
    if (next_head == hdr->tail) {
        // Buffer is full, drop packet
        hdr->total_dropped++;
        return false;
    }
    SovereignStatePacket58* packets = (SovereignStatePacket58*)((uint8_t*)buffer + sizeof(SovereignRingHeader));
    memcpy(&packets[hdr->head], packet, sizeof(SovereignStatePacket58));
    hdr->head = next_head;
    hdr->total_written++;
    return true;
}

bool sov_ring_pop(void* buffer, SovereignStatePacket58* out_packet) {
    SovereignRingHeader* hdr = (SovereignRingHeader*)buffer;
    if (hdr->head == hdr->tail) {
        // Empty
        return false;
    }
    const SovereignStatePacket58* packets = (const SovereignStatePacket58*)((const uint8_t*)buffer + sizeof(SovereignRingHeader));
    memcpy(out_packet, &packets[hdr->tail], sizeof(SovereignStatePacket58));
    hdr->tail = (hdr->tail + 1) % hdr->capacity;
    return true;
}

void sov_packet_seal(SovereignStatePacket58* packet) {
    packet->magic = SOV_IPC_MAGIC;
    // CRC is computed over the first 56 bytes
    packet->crc16 = sov_crc16((const uint8_t*)packet, 56);
}

bool sov_packet_verify(const SovereignStatePacket58* packet) {
    if (packet->magic != SOV_IPC_MAGIC) {
        return false;
    }
    uint16_t expected_crc = sov_crc16((const uint8_t*)packet, 56);
    return (packet->crc16 == expected_crc);
}
