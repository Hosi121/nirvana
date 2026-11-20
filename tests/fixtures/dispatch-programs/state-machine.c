#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    unsigned phase = (unsigned)(r[0] & UINT64_C(7));
    unsigned steps = (unsigned)(r[3] & UINT64_C(7)) + 1;
    uint64_t value = r[1], total = r[2];
    for (unsigned n = 0; n < steps; ++n) {
        switch (phase) {
        case 0: value += total; phase = 3; break;
        case 1: total ^= value; phase = 6; break;
        case 2: value = (value << 5) | (value >> 59); phase = 7; break;
        case 3: value *= UINT64_C(3); phase = 1; break;
        case 4: total += value ^ UINT64_C(0xa5); phase = 0; break;
        case 5: value -= total; phase = 2; break;
        case 6: total = (total >> 7) | (total << 57); phase = 5; break;
        default: value ^= total + UINT64_C(17); phase = 4; break;
        }
        phase ^= (unsigned)(value & UINT64_C(3));
    }
    r[0] = phase;
    r[1] = value;
    r[2] = total;
    return value ^ total ^ phase;
}
