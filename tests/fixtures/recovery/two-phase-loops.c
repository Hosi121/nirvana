#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t first_limit = state[0] & UINT64_C(3);
    uint64_t total = state[1];
    for (uint64_t first = 0; first < first_limit; ++first) {
        total += first * UINT64_C(3) + state[2];
    }
    state[1] = total;

    uint64_t second_limit = (state[2] >> 2) & UINT64_C(3);
    uint64_t hash = state[3];
    for (uint64_t second = 0; second < second_limit; ++second) {
        hash = (hash * UINT64_C(33)) ^ (total + second);
    }
    state[3] = hash;
    return total + hash;
}
