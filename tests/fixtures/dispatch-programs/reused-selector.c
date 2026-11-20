#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    volatile uint64_t slots[2];
    slots[0] = r[0] & UINT64_C(7);
    slots[1] = r[1];
    switch (slots[0]) {
    case 0: slots[0] = slots[1] + r[2]; break;
    case 1: slots[0] = slots[1] * UINT64_C(5); break;
    case 2: slots[0] = slots[1] ^ r[3]; break;
    case 3: slots[0] = (slots[1] << 7) | (slots[1] >> 57); break;
    case 4: slots[0] = slots[1] - r[2]; break;
    case 5: slots[0] = slots[1] + (r[2] & UINT64_C(255)); break;
    case 6: slots[0] = slots[1] | r[3]; break;
    default: slots[0] = slots[1] & r[2]; break;
    }
    slots[1] = (slots[0] ^ r[2]) & UINT64_C(7);
    switch (slots[1]) {
    case 0: r[1] = slots[0] + UINT64_C(11); break;
    case 1: r[1] = slots[0] ^ UINT64_C(0x55); break;
    case 2: r[1] = slots[0] * UINT64_C(9); break;
    case 3: r[1] = (slots[0] >> 3) | (slots[0] << 61); break;
    case 4: r[1] = slots[0] - r[3]; break;
    case 5: r[1] = slots[0] | r[2]; break;
    case 6: r[1] = slots[0] & r[3]; break;
    default: r[1] = slots[0] ^ r[2]; break;
    }
    r[2] = slots[1];
    return r[1] ^ r[2];
}
