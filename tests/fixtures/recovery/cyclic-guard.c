#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t index = state[0] & UINT64_C(7);
    uint64_t stop = state[1] & UINT64_C(7);
    uint64_t hash = state[2];
    if (index != stop) {
        do {
            hash = (hash * UINT64_C(33)) ^ index;
            index = (index + UINT64_C(1)) & UINT64_C(7);
        } while (index != stop);
    }
    state[0] = index;
    state[2] = hash;
    state[3] ^= hash;
    return hash + index;
}
