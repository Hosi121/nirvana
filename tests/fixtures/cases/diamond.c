#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    uint64_t value;
    if (r[0] < UINT64_C(10)) {
        value = r[0] * UINT64_C(3);
    } else {
        value = r[0] + UINT64_C(20);
    }
    r[1] = value;
    return value;
}
