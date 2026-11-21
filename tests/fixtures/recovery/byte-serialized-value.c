#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    volatile unsigned char *bytes = (volatile unsigned char *)&state[2];
    bytes[0] = (unsigned char)value;
    bytes[1] = (unsigned char)(value >> 8);
    bytes[2] = (unsigned char)(value >> 16);
    bytes[3] = (unsigned char)(value >> 24);
    state[0] = 0;
    uint64_t result = (uint64_t)bytes[0]
        | ((uint64_t)bytes[1] << 8)
        | ((uint64_t)bytes[2] << 16)
        | ((uint64_t)bytes[3] << 24);
    state[3] = result;
    return result;
}
