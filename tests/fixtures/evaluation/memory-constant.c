#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t input = state[0];
    state[1] = UINT64_C(0x1020304050607080);
    unsigned char *bytes = (unsigned char *)&state[1];
    bytes[3] = 0xa5;
    uint64_t known = state[1];
    if (state[3] & 1)
        state[2] = input + known;
    else
        state[2] = input ^ known;
    return state[2] + known;
}
