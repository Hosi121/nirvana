#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    while (1) {
        ++r[1];
        if (r[0] & UINT64_C(1)) {
            r[2] = UINT64_C(200);
            break;
        }
        if (r[1] >= UINT64_C(3)) {
            r[2] = UINT64_C(100);
            break;
        }
    }
    return r[2] + r[1];
}
