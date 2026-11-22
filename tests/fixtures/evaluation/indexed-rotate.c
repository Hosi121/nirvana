#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    for (uint64_t i = 0; i < 4; ++i) {
        uint64_t neighbor = state[(i + 1) & 3];
        state[i] ^= neighbor + i;
    }
    return state[0] + state[3];
}
