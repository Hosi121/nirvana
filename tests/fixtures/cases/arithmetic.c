#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    r[2] = r[0] + r[1];
    r[3] = r[0] - r[1];
    r[2] *= r[3];
    r[3] = r[0] | r[1];
    r[2] ^= r[3];
    r[3] = r[0] & r[1];
    r[2] <<= r[1] & UINT64_C(63);
    r[3] >>= r[1] & UINT64_C(63);
    r[2] += (r[0] == r[1]) + (r[0] != r[1]);
    r[3] += (r[0] < r[1]) + (r[0] <= r[1]);
    return r[2] ^ r[3];
}
