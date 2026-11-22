#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    uint64_t flag = state[1];
    volatile uint64_t *observed = state;
    const volatile unsigned char *bytes =
        (const volatile unsigned char *)&state[2];
    state[2] = value;
    uint64_t result;
    if (flag & 1) {
        result = bytes[1];
        observed[0] = 0;
    } else {
        observed[0] = 1;
        result = bytes[1];
    }
    result += (uint64_t)bytes[3] << 8;
    state[3] = result;
    return result;
}
