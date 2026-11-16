#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t total = state[0] + (state[3] & UINT64_C(255));
    uint64_t cursor = state[1];
    uint64_t limit = (state[2] & UINT64_C(3)) + UINT64_C(1);
    for (uint64_t step = 0; step < limit; ++step) {
        uint64_t index = (cursor + step) & UINT64_C(3);
        uint64_t observed = state[index];
        if ((observed & UINT64_C(7)) == UINT64_C(3)) {
            total ^= observed;
            goto done;
        }
        total += (observed >> 1) + step;
        if ((total & UINT64_C(15)) == 0) {
            goto keep_cursor;
        }
        cursor += observed ^ step;
        if ((cursor & UINT64_C(31)) == UINT64_C(7)) {
            state[2] = total;
            goto done;
        }
    }
keep_cursor:
    state[1] = cursor;
done:
    state[0] = total;
    state[3] = total ^ state[2] ^ cursor;
    return state[3] + state[1];
}
