#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    if (r[0] == 0) {
        return UINT64_C(42);
    }
    return r[0] + UINT64_C(1);
}
