#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t left = __builtin_bswap64(state[0]);
    uint64_t right = __builtin_bswap64(state[2]);
    uint32_t low = __builtin_bswap32((uint32_t)state[1]);
    uint32_t high = __builtin_bswap32((uint32_t)(state[3] >> 32));
    state[0] = left;
    state[1] = low;
    state[2] = right;
    state[3] = high;
    return (left ^ right) + low + high;
}
