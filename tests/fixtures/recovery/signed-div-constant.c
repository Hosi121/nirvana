#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    int64_t value = (int64_t)state[0];
    int64_t quotient = value / 10;
    int64_t remainder = value % 10;
    int64_t small = (int32_t)(uint32_t)state[3];
    state[1] = (uint64_t)quotient;
    state[2] = (uint64_t)remainder;
    state[3] = (uint64_t)(small / 10 + small % 10);
    return state[1] ^ (state[2] << 8) ^ state[3];
}
