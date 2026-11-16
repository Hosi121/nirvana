#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    uint64_t values[4] = {r[0], r[1], r[2], r[3]};
    uint64_t count = (r[0] & UINT64_C(3)) + UINT64_C(1);
    uint64_t total = 0;
    for (uint64_t index = 0; index < count; ++index) {
        total += values[index] ^ index;
    }
    r[1] = count;
    r[2] = total;
    r[3] = values[count - 1];
    return total;
}
