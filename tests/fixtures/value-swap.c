#include <stdint.h>

uint64_t fixture(uint64_t state[4]) {
    uint64_t left = state[0], right = state[1];
    for (uint64_t remaining = state[2] & UINT64_C(7); remaining; --remaining) {
        uint64_t saved = left;
        left = right;
        right = saved;
    }
    state[0] = left;
    state[1] = right;
    return left ^ right;
}
