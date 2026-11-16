#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t index = state[3] & UINT64_C(3);
    uint64_t next = (index + UINT64_C(1)) & UINT64_C(3);
    uint64_t other = (index + UINT64_C(2)) & UINT64_C(3);
    uint64_t before = state[index];
    state[index] = before ^ (state[next] + UINT64_C(65537));
    state[other] += state[index] >> 7;
    return state[index] + state[other] + before;
}
