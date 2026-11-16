#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    switch (r[0] & UINT64_C(7)) {
    case 0:
        r[1] += UINT64_C(10);
        break;
    case 1:
        r[1] ^= UINT64_C(85);
        break;
    case 2:
        r[1] += UINT64_C(3);
        /* fall through */
    case 3:
        r[1] *= UINT64_C(2);
        break;
    case 4:
        return r[2];
    default:
        r[1] = r[3] - r[0];
        break;
    }
    return r[1] + r[2];
}
