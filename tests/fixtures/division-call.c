#include "fixture.h"

__attribute__((noinline)) uint64_t divide_pair(uint64_t numerator, uint64_t denominator) {
    return (numerator / denominator) ^ (numerator % denominator);
}

uint64_t fixture(uint64_t state[4]) {
    if (state[1] == 0) {
        state[3] = 1;
        return 0;
    }
    uint64_t result = divide_pair(state[0], state[1]);
    state[2] = result;
    state[3] = state[0] + result;
    return result ^ state[3];
}
