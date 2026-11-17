#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t total;
    if ((state[0] & UINT64_C(1)) != 0) {
        total = state[1] + UINT64_C(3);
    } else {
        total = state[2] ^ UINT64_C(9);
    }
    uint64_t limit = state[3] & UINT64_C(7);
    uint64_t index = 0;
    while (index < limit) {
        if ((index & UINT64_C(1)) != 0) {
            total += state[0] & UINT64_C(15);
        } else {
            total ^= index + state[1];
        }
        ++index;
    }
    state[0] = total;
    state[2] = index;
    state[3] = total ^ limit;
    return total + index;
}
