#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    uint64_t count = state[1] & 7;
    while (count != 0) {
        value = value * 33 + count;
        --count;
    }
    value ^= state[3];
    state[2] = value;
    state[0] = 0;
    const volatile unsigned char *bytes =
        (const volatile unsigned char *)&state[2];
    uint64_t result = (uint64_t)bytes[1] + bytes[3];
    state[3] = result;
    return result;
}
