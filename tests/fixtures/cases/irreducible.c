#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    r[1] = 0;
    if (r[0] & UINT64_C(1)) {
        goto second;
    }
first:
    --r[0];
second:
    ++r[1];
    if (r[1] < UINT64_C(5)) {
        goto first;
    }
    return r[0] ^ r[1];
}
