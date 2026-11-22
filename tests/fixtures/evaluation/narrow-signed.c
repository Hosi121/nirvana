#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    int32_t value = (int32_t)(uint16_t)state[0] - 32768;
    int32_t product = value * 7;
    state[1] = (uint64_t)(product / -31);
    state[2] = (uint64_t)(product % -31);
    state[3] = (uint64_t)(-product);
    return state[1] + state[2] + state[3];
}
