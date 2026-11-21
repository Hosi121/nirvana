#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    unsigned char tag = (unsigned char)((state[0] >> 8) & 31u);
    tag = (unsigned char)(tag | 128u);
    unsigned count = (unsigned)(state[0] & 3u);
    while (count != 0) {
        tag = (unsigned char)(((unsigned)tag + 1u) & 31u);
        tag = (unsigned char)(tag | 128u);
        --count;
    }
    state[1] = (uint64_t)(tag & 128u);
    state[2] = tag;
    return state[0] ^ state[1] ^ state[2];
}
