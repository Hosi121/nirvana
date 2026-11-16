#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    r[0] &= UINT64_C(3);
    r[3] = 0;
    for (r[1] = 0; r[1] < r[0]; ++r[1]) {
        r[2] = 0;
        while (r[2] < UINT64_C(3)) {
            r[3] += r[2];
            ++r[2];
            if (r[2] == UINT64_C(2)) {
                goto done;
            }
        }
    }
done:
    return r[3];
}
