#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    uint64_t limit = r[0] & UINT64_C(7);
    uint64_t index = 0;
    uint64_t total = 0;
    while (index < limit) {
        total += index;
        ++index;
    }
    r[1] = limit;
    r[2] = index;
    r[3] = total;
    return total;
}
