/*
 * src/c/sedenion_shm_ipc.h
 * =============================================================================
 * Sovereign High-Performance Zero-GC Binary Shared-Memory IPC.
 * Rigid 58-Byte Binary State Packet and Ring Buffer.
 * =============================================================================
 */

#ifndef SEDENION_SHM_IPC_H
#define SEDENION_SHM_IPC_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#define SOV_IPC_MAGIC 0x5356     // 'S', 'V'
#define SOV_RING_MAGIC 0x53565242 // 'SVRB'
#define SOV_PACKET_SIZE 58

#pragma pack(push, 1)
typedef struct {
    uint16_t magic;          // 2 bytes: 0x5356
    uint64_t seq;            // 8 bytes: Monotonic packet sequence counter
    uint16_t state_fp16[16]; // 32 bytes: 16D sedenion state in IEEE 754 half precision
    float lamb_norm;         // 4 bytes: Quenched 16D Lamb vector norm ||L_16||
    float s_diagram;         // 4 bytes: Diagrammatic entropy S_diagram
    uint32_t zd_mask;        // 4 bytes: Zero-divisor active basis mask
    uint16_t flags;          // 2 bytes: Status / quench flags
    uint16_t crc16;          // 2 bytes: CRC16 checksum over first 56 bytes
} SovereignStatePacket58;
#pragma pack(pop)

#pragma pack(push, 1)
typedef struct {
    uint32_t magic;          // 0x53565242 ("SVRB")
    uint32_t capacity;       // Number of packets capacity
    uint32_t head;           // Write pointer (index)
    uint32_t tail;           // Read pointer (index)
    uint64_t total_written;  // Monotonic written count
    uint64_t total_dropped;  // Monotonic drop count (if full)
} SovereignRingHeader;
#pragma pack(pop)

#ifdef __cplusplus
extern "C" {
#endif

// Fast CCITT-16 CRC
uint16_t sov_crc16(const uint8_t* data, size_t len);

// Convert single float to IEEE 754 half-precision uint16_t and vice versa
uint16_t float_to_fp16(float f);
float fp16_to_float(uint16_t h);

// Convert 16 floats to FP16 in batch
void float_batch_to_fp16_16(const float* in_f32, uint16_t* out_fp16);
void fp16_batch_to_float_16(const uint16_t* in_fp16, float* out_f32);

// Ring buffer calculation & lifecycle
size_t sov_ring_total_bytes(uint32_t capacity);
void sov_ring_init(void* buffer, uint32_t capacity);
bool sov_ring_push(void* buffer, const SovereignStatePacket58* packet);
bool sov_ring_pop(void* buffer, SovereignStatePacket58* out_packet);
uint32_t sov_ring_count(const void* buffer);

// Packet construction and validation
void sov_packet_seal(SovereignStatePacket58* packet);
bool sov_packet_verify(const SovereignStatePacket58* packet);

#ifdef __cplusplus
}
#endif

#endif // SEDENION_SHM_IPC_H
