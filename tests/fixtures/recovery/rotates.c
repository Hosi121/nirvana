#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t count = state[1] & UINT64_C(63);
    uint64_t left = (state[0] << count) | (state[0] >> ((UINT64_C(0) - count) & UINT64_C(63)));
    uint64_t right = (state[2] >> count) | (state[2] << ((UINT64_C(0) - count) & UINT64_C(63)));
    uint32_t word = (uint32_t)state[3];
    word = (word << 5) | (word >> 27);
    uint16_t half = (uint16_t)state[0];
    half = (uint16_t)((half << 3) | (half >> 13));
    unsigned char byte = (unsigned char)state[2];
    byte = (unsigned char)((byte >> 3) | (byte << 5));
    state[0] = left ^ right;
    state[1] = word;
    state[2] = half;
    state[3] = byte;
    return left + right + word + half + byte;
}
