#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    volatile uint64_t *observed = state;
    uint64_t value = state[0];
    uint64_t count = state[1] & 3;
    observed[2] = value;
    uint64_t selected;
    if (state[1] & 1) {
        selected = observed[2];
        observed[0] = 0;
    } else {
        observed[0] = 1;
        selected = observed[2];
    }
    observed[3] = selected;
    const volatile unsigned char *bytes =
        (const volatile unsigned char *)&state[3];
    uint64_t result = (uint64_t)bytes[1] + bytes[3];
    while (count != 0) {
        result = result * 33 + count;
        --count;
    }
    state[0] = result;
    return result;
}
