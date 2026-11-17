#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    union {
        uint64_t whole;
        uint16_t half;
        unsigned char byte;
    } local;
    local.whole = state[0] ^ state[3];
    local.byte = (unsigned char)state[2];
    uint64_t first = local.whole;
    if ((state[1] & UINT64_C(1)) != 0) {
        local.half ^= (uint16_t)(state[2] >> 8);
    } else {
        local.byte ^= (unsigned char)(state[2] >> 8);
    }
    state[0] = local.whole;
    state[3] = first;
    return local.whole + first;
}
