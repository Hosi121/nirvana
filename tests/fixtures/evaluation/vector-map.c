#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    for (uint64_t i = 0; i < 4; ++i) {
        state[i] = (state[i] >> 3) ^ (state[i] + UINT64_C(17));
    }
    return state[0] ^ state[1] ^ state[2] ^ state[3];
}
