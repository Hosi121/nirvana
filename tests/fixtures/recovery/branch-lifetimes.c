#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t seed = state[0];
    uint64_t selected;
    if ((seed & UINT64_C(1)) != 0) {
        selected = state[1];
    } else {
        selected = state[2];
    }
    state[3] = seed ^ selected;

    uint64_t limit = (selected & UINT64_C(3)) + UINT64_C(1);
    uint64_t total = seed;
    for (uint64_t count = 0; count < limit; ++count) {
        total = (total * UINT64_C(33)) ^ (selected + count);
    }
    state[0] = total;
    state[1] = limit;
    return total + state[3];
}
