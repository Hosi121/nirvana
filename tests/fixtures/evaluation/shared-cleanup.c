#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t result;
    if (state[0] & 1) {
        result = state[1] + 17;
        state[2] ^= state[3];
    } else if (state[0] & 2) {
        result = state[2] + 11;
        state[2] += state[3];
    } else {
        result = state[1] ^ state[2];
        state[2] &= state[3];
    }
    state[3] = state[2] + result;
    state[0] = result;
    return state[3];
}
