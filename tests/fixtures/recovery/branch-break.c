#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t count = 0;
    uint64_t limit = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t total = state[0];
    for (;;) {
        uint64_t value = state[(count + state[1]) & UINT64_C(3)];
        if ((value & UINT64_C(1)) != 0) {
            total += value;
            state[2] = total;
            break;
        } else if ((value & UINT64_C(6)) == UINT64_C(2)) {
            total ^= value;
            state[1] = total;
            break;
        }
        total += count;
        count += UINT64_C(1);
        if (count >= limit) {
            break;
        }
    }
    state[0] = total;
    state[3] = count;
    return total ^ count;
}
