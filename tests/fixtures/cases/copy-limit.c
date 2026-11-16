#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    if (r[0] & UINT64_C(1)) {
        r[2] = UINT64_C(10);
    } else if (r[0] & UINT64_C(2)) {
        r[2] = UINT64_C(20);
    } else if (r[0] & UINT64_C(4)) {
        r[2] = UINT64_C(30);
    } else {
        return UINT64_C(111);
    }
    return r[2] + r[0];
}
