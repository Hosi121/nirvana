#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t a = state[0] & UINT64_C(65535);
    uint64_t b = state[1] & UINT64_C(65535);
    uint64_t common = 0;
    uint64_t work = 0;
    while (a != 0 && b != 0 && work < 24) {
        if (((a | b) & 1) == 0) {
            a >>= 1;
            b >>= 1;
            ++common;
        } else if ((a & 1) == 0) {
            a >>= 1;
        } else if ((b & 1) == 0) {
            b >>= 1;
        } else if (a > b) {
            a = (a - b) >> 1;
        } else {
            b = (b - a) >> 1;
        }
        ++work;
    }
    state[0] = a;
    state[1] = b;
    state[2] ^= common + work;
    state[3] = (a | b) << common;
    return state[3] ^ state[2];
}
