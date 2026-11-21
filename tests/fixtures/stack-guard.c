#include <stdint.h>

uint64_t fixture(uint64_t state[4]) {
    volatile unsigned char buffer[24];
    buffer[0] = (unsigned char)state[0];
    state[1] = buffer[0];
    return state[1] + 3;
}
