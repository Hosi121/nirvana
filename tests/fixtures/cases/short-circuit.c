#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    uint64_t checks = 0;
    uint64_t accepted = 0;
    if ((r[0] != 0 && (++checks, r[1] < r[0])) ||
        (r[2] != 0 && (++checks, r[3] == r[2]))) {
        accepted = 1;
    }
    r[0] = checks;
    r[1] = accepted;
    return accepted + checks * UINT64_C(10);
}
