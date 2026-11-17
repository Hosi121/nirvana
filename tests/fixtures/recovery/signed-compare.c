#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    /* Corresponding signed/unsigned types may alias; no integer value cast. */
    const int64_t *signed_state = (const int64_t *)(const void *)state;
    int64_t left = signed_state[0];
    int64_t right = signed_state[1];
    uint64_t lt = (uint64_t)(left < right);
    uint64_t le = (uint64_t)(left <= right);
    uint64_t gt = (uint64_t)(left > right);
    uint64_t ge = (uint64_t)(left >= right);
    state[2] = lt | (le << 1);
    state[3] = gt | (ge << 1);
    return lt | (le << 1) | (gt << 2) | (ge << 3);
}
