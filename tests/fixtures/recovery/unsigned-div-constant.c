#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    uint64_t quotient = value / UINT64_C(10);
    uint64_t remainder = value % UINT64_C(10);
    uint32_t word = (uint32_t)state[3];
    state[1] = quotient;
    state[2] = remainder;
    state[3] = (uint64_t)(word / UINT32_C(10)) + (uint64_t)(word % UINT32_C(10));
    return quotient ^ (remainder << 8) ^ state[3];
}
