#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t big = __builtin_bswap64(state[0]);
    uint32_t word = __builtin_bswap32((uint32_t)state[1]);
    uint16_t half = __builtin_bswap16((uint16_t)state[2]);
    state[0] = __builtin_bswap64(state[3] + big);
    state[1] = word;
    state[2] = half;
    state[3] = __builtin_bswap64(big ^ word ^ half);
    return big + word + half;
}
