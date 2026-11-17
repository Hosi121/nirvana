#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    /* Corresponding signed/unsigned types may alias; no integer value cast. */
    const int64_t *signed_state = (const int64_t *)(const void *)state;
    int64_t left = signed_state[0];
    int64_t right = signed_state[1];
    if (left < right) {
        state[2] = UINT64_C(1);
    } else {
        state[2] = UINT64_C(0);
    }
    if (left <= right) {
        state[3] = UINT64_C(1);
    } else {
        state[3] = UINT64_C(0);
    }
    return state[2] | (state[3] << 1);
}
