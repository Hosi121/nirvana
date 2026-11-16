#include "../fixture.h"

/* Scalars retain word/dword stores; character stores may alias any state word. */
uint64_t fixture(uint64_t state[4]) {
    volatile uint16_t small = (uint16_t)state[0];
    volatile uint32_t wide = (uint32_t)state[1];
    unsigned char *bytes = (unsigned char *)state;
    small = (uint16_t)(((uint32_t)small & UINT32_C(0xff00))
                    | (uint32_t)(state[2] & UINT64_C(255)));
    wide = (uint32_t)(((uint64_t)wide & UINT64_C(0xffff0000)) | (uint64_t)small);
    bytes[1] = (unsigned char)(small >> 8);
    bytes[6] = (unsigned char)wide;
    bytes[7] = (unsigned char)(wide >> 24);
    state[1] = (state[1] & UINT64_C(0xffffffff00000000)) | (uint64_t)wide;
    state[2] = (state[2] & UINT64_C(0xffffffffffff0000)) | (uint64_t)small;
    return (uint64_t)small ^ (uint64_t)wide ^ state[0] ^ state[2];
}
