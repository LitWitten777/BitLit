#include <stdio.h>
#include <time.h>
#include "sedenion_xtensa_pie.h"

int main(void) {
    int16_t state[16] = {100, -200, 300, -400, 500, -600, 700, -800,
                         900, -1000, 1100, -1200, 1300, -1400, 1500, -1600};
    int16_t kernel[16] = {16384, 8192, 16384, 8192, 16384, 8192, 16384, 8192,
                          16384, 8192, 16384, 8192, 16384, 8192, 16384, 8192};
    int16_t out[16];

    const uint32_t N = 1000000;
    clock_t start = clock();
    for (uint32_t i = 0; i < N; i++) {
        state[0] = (int16_t)(i & 0x7FFF);
        cd_filter_16_pie_fixed(state, kernel, out);
    }
    clock_t end = clock();

    double sec = (double)(end - start) / CLOCKS_PER_SEC;
    double freq_khz = (N / sec) / 1000.0;
    printf("Xtensa PIE 16D Filter: %.2f kHz (%.2f ms for %u ops)\n", freq_khz, sec * 1000.0, N);
    return (freq_khz > 200.0) ? 0 : 1;
}
