#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    uint64_t quotient = value / UINT64_C(7);
    uint64_t remainder = value % UINT64_C(7);
    state[1] = quotient;
    state[2] = remainder;
    return quotient ^ remainder;
}
