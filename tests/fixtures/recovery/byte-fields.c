#include "../fixture.h"

/* Character access permits unaligned, overlapping input fields. Volatile
 * unsigned scalars retain mixed-width stack fields without taking addresses. */
uint64_t fixture(uint64_t state[4]) {
    unsigned char *bytes = (unsigned char *)state;
    volatile uint16_t small = (uint16_t)((uint16_t)bytes[7] | (uint16_t)bytes[8] << 8);
    volatile uint32_t wide = (uint32_t)bytes[13]
                          | (uint32_t)bytes[14] << 8
                          | (uint32_t)bytes[15] << 16
                          | (uint32_t)bytes[16] << 24;
    uint16_t changed = (uint16_t)(small + (uint16_t)state[3]);
    bytes[9] = (unsigned char)changed;
    bytes[10] = (unsigned char)(changed >> 8);
    bytes[10] ^= (unsigned char)wide;
    uint32_t observed = (uint32_t)bytes[8]
                      | (uint32_t)bytes[9] << 8
                      | (uint32_t)bytes[10] << 16
                      | (uint32_t)bytes[11] << 24;
    state[2] = (state[2] ^ observed) + wide;
    return state[1] ^ state[2] ^ small;
}
