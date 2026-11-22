#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = 0;
    for (uint64_t i = 0; i < 3; ++i) {
        for (uint64_t j = 0; j < 2; ++j) {
            uint64_t x = state[(i + j) & 3];
            if (x & 1) {
                value += x ^ i;
            } else if (x == 0) {
                goto done;
            } else {
                value -= j;
            }
        }
    }
done:
    state[2] ^= value;
    return state[2] + state[3];
}
