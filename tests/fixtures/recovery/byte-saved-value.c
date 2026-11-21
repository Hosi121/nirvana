#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    state[2] = value;
    volatile unsigned char *bytes = (volatile unsigned char *)&state[2];
    uint64_t low = bytes[1];
    uint64_t high = bytes[3];
    state[0] = 0;
    state[3] = low;
    return low + (high << 8);
}
