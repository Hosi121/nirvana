#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    uint64_t limit = r[0] & UINT64_C(7);
    uint64_t count = 0;
    uint64_t total = 0;
    do {
        total += r[3] + count;
        ++count;
    } while (count < limit);
    r[1] = count;
    r[2] = total;
    return total;
}
