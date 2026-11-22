#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t target = (state[0] >> 8) & 255;
    uint64_t value = 0;
    for (uint64_t i = 0; i < 4; ++i) {
        if ((state[i] & 255) == target) {
            value = i + 1;
            break;
        }
        value ^= state[i];
    }
    if (value & 1) {
        state[1] = value;
    } else {
        state[2] = value;
    }
    state[3] = state[1] + state[2];
    return state[3];
}
