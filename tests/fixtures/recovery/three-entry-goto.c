#include "../fixture.h"

/* Three entries into one bounded cycle. Every label consumes the countdown. */
uint64_t fixture(uint64_t state[4]) {
    uint64_t remaining = (state[3] & UINT64_C(7)) + UINT64_C(3);
    uint64_t left = state[0];
    uint64_t right = state[1];
    uint64_t total = state[2];
    if (state[3] & UINT64_C(16)) {
        goto middle;
    }
    if (state[3] & UINT64_C(32)) {
        goto last;
    }
first:
    left += right ^ remaining;
    if (--remaining == 0) {
        goto done;
    }
middle:
    right = (right << 1) ^ total;
    total += left + remaining;
    if (--remaining == 0) {
        goto done;
    }
last:
    total ^= right + remaining;
    left += total >> 3;
    if (--remaining != 0) {
        goto first;
    }
done:
    state[0] = left;
    state[1] = right;
    state[2] = total;
    state[3] = remaining;
    return left ^ right ^ total;
}
