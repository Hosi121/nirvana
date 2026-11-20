#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    switch (r[0]) {
    case 0: r[1] += r[2]; break;
    case 1: r[1] *= UINT64_C(3); break;
    case 2: r[1] ^= r[3]; break;
    case 3: r[1] = (r[1] << 7) | (r[1] >> 57); break;
    case 4: r[1] -= r[2]; break;
    case 5: r[1] += r[3] * UINT64_C(5); break;
    case 6: r[1] += r[2] ^ r[3]; break;
    case 7: r[1] = (r[1] >> 3) | (r[3] << 61); break;
    case 8: r[1] ^= r[2] & r[3]; break;
    case 9: r[1] += r[2] & UINT64_C(255); break;
    case 10: r[1] = r[2] + UINT64_C(17); break;
    case 11: r[1] = (r[1] ^ r[3]) * UINT64_C(7); break;
    default: r[1] ^= r[0]; break;
    }
    return r[1] ^ r[0] ^ r[2];
}
