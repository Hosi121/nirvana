#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t saved = state[0];
    state[1] = saved;
    state[0] = saved + state[3];
    unsigned char *bytes = (unsigned char *)&state[1];
    bytes[3] = (unsigned char)state[3];
    uint64_t reloaded = state[1];
    if (state[3] & 1)
        state[2] = reloaded + saved;
    else
        state[2] = reloaded ^ saved;
    return state[2] + state[0];
}
