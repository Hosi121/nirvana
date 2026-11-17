#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    uint64_t limit = (state[3] & UINT64_C(3)) + UINT64_C(1);
    for (uint64_t count = 0; count < limit; ++count) {
        uint64_t observed = state[(value + count) & UINT64_C(3)];
        if ((observed & UINT64_C(3)) == 0) {
            state[1] = value + observed;
            return value ^ state[2];
        } else if ((observed & UINT64_C(3)) == UINT64_C(1)) {
            state[2] += value;
            return value ^ state[2];
        }
        value += observed ^ count;
    }
    state[0] = value;
    return value ^ state[2];
}
