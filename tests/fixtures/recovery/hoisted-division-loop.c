#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t count = state[3] & UINT64_C(7);
    uint64_t value = state[0];
    uint64_t total = state[1];
    volatile uint64_t *output = state;
    for (uint64_t index = 0; index < count; ++index) {
        uint64_t quotient = value / UINT64_C(3);
        uint64_t remainder = value % UINT64_C(3);
        output[1] = quotient;
        output[2] = remainder;
        total += quotient ^ remainder;
        ++value;
    }
    state[1] = total;
    return total;
}
