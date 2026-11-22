#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value;
    if (state[0] & 1) {
        goto fail;
    }
    value = state[1] + state[2];
    if (value < state[1]) {
        goto overflow;
    }
    state[2] = value;
    goto done;
overflow:
    state[2] = UINT64_C(0xbad);
fail:
    state[0] |= 2;
done:
    state[3] += state[2];
    return state[3];
}
