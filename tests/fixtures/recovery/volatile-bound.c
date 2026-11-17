#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    volatile uint64_t *limit = &state[3];
    uint64_t total = state[1];
    uint64_t index = 0;
    while (index < (*limit & UINT64_C(7))) {
        total += state[index & UINT64_C(3)] ^ index;
        if ((total & UINT64_C(31)) == UINT64_C(13)) {
            break;
        }
        state[2] ^= total;
        ++index;
    }
    state[0] = total;
    state[1] = index;
    return total ^ index ^ state[2];
}
