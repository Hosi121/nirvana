#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t *selected;
    if (state[3] & UINT64_C(1)) {
        selected = &state[0];
    } else {
        selected = &state[2];
    }
    uint64_t before = *selected;
    unsigned char *bytes = (unsigned char *)selected;
    bytes[(state[1] >> 3) & UINT64_C(7)] = (unsigned char)(state[2] ^ before);
    uint64_t after = *selected;
    *selected = after + state[1];
    state[3] = before ^ after;
    return *selected ^ state[3];
}
