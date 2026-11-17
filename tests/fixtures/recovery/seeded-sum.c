#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t limit = state[0] & UINT64_C(7);
    uint64_t index = 0;
    uint64_t total = state[1];
    while (index < limit) {
        total += index;
        ++index;
    }
    state[1] = limit;
    state[2] = index;
    state[3] = total;
    return total;
}
