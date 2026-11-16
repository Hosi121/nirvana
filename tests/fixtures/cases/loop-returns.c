#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    r[1] = 0;
    while (1) {
        if (r[0] == 0) {
            return UINT64_C(42);
        }
        ++r[1];
        if (r[1] >= UINT64_C(3)) {
            return r[1] + UINT64_C(7);
        }
    }
}
