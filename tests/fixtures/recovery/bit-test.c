#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    uint64_t index = state[1] & UINT64_C(63);
    uint64_t result = state[2];
    if ((value & (UINT64_C(1) << index)) != 0) {
        result ^= state[3];
        state[0] = result + index;
    } else {
        result += value;
        state[1] = result ^ index;
    }
    state[2] = result;
    return result;
}
