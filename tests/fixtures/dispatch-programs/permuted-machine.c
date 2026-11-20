#include "../fixture.h"

static uint64_t swap_bytes(uint64_t x) {
    x = ((x & UINT64_C(0x00ff00ff00ff00ff)) << 8)
      | ((x >> 8) & UINT64_C(0x00ff00ff00ff00ff));
    x = ((x & UINT64_C(0x0000ffff0000ffff)) << 16)
      | ((x >> 16) & UINT64_C(0x0000ffff0000ffff));
    return (x << 32) | (x >> 32);
}

uint64_t fixture(uint64_t r[4]) {
    uint64_t value = r[1], total = r[2];
    unsigned phase = (unsigned)(r[0] & UINT64_C(7));
    unsigned count = (unsigned)(r[3] & UINT64_C(7)) + 1;
    for (unsigned n = 0; n < count; ++n) {
        value = swap_bytes(value);
        switch (phase) {
        case 0: value += total; break;
        case 1: total ^= value; break;
        case 2: value = (value << 5) | (value >> 59); break;
        case 3: value *= UINT64_C(3); break;
        case 4: total += value ^ UINT64_C(0xa5); break;
        case 5: value -= total; break;
        case 6: total = (total >> 7) | (total << 57); break;
        default: value ^= total + UINT64_C(17); break;
        }
        phase = (unsigned)((phase + (value & UINT64_C(7)) + 1) & 7);
    }
    r[0] = phase; r[1] = value; r[2] = total;
    return value ^ total ^ phase;
}
