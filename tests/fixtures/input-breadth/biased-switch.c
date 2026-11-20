#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    int32_t key = (int32_t)(uint32_t)r[0];
    switch (key) {
    case -4: r[1] += r[2]; break;
    case -3: r[1] ^= r[3]; break;
    case -2: r[1] = (r[1] << 9) | (r[1] >> 55); break;
    case -1: r[1] *= UINT64_C(7); break;
    case 0: r[1] -= r[2]; break;
    case 1: r[1] += r[3] * UINT64_C(3); break;
    case 2: r[1] ^= r[2] & r[3]; break;
    case 3: r[1] = r[2] + UINT64_C(11); break;
    case 4: r[1] = (r[1] >> 5) | (r[3] << 59); break;
    default: r[1] ^= r[0]; break;
    }
    return r[1] + r[2];
}
