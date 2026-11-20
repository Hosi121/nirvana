#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    switch (r[0] & UINT64_C(7)) {
    case 0: r[1] += r[2]; break;
    case 1: r[1] ^= r[3]; break;
    case 2: r[1] *= UINT64_C(5); break;
    case 3: r[1] = (r[1] << 11) | (r[1] >> 53); break;
    case 4:
        switch (r[3] & UINT64_C(7)) {
        case 0: r[1] -= r[2]; break;
        case 1: r[1] += r[2] * UINT64_C(9); break;
        case 2: r[1] ^= r[2] << 3; break;
        case 3: r[1] = (r[1] >> 7) | (r[1] << 57); break;
        case 4: r[1] *= r[2]; break;
        case 5: r[1] |= r[2]; break;
        default: r[1] &= r[2]; break;
        }
        break;
    case 5: r[1] -= r[3]; break;
    default: r[1] += r[3] & UINT64_C(255); break;
    }
    return r[1] ^ r[2];
}
