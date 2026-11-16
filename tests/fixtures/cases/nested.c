#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    if (r[0] < UINT64_C(10)) {
        r[1] = r[0] * UINT64_C(3);
    } else if (r[0] & UINT64_C(1)) {
        r[1] = r[0] + UINT64_C(2);
    } else {
        r[1] = r[0] + UINT64_C(1);
    }
    return r[1];
}
