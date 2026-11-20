#include "../fixture.h"

static const uint8_t classes[32] = {
    3, 0, 7, 2, 5, 1, 6, 4, 1, 7, 2, 6, 0, 5, 4, 3,
    6, 2, 4, 0, 7, 3, 1, 5, 4, 5, 0, 1, 3, 6, 2, 7
};

uint64_t fixture(uint64_t r[4]) {
    unsigned key = classes[(r[0] ^ r[3]) & UINT64_C(31)];
    uint64_t value = r[1];
    switch (key) {
    case 0: value += r[2] * UINT64_C(3); break;
    case 1: value = (value << 9) | (value >> 55); break;
    case 2: value ^= r[2] + r[3]; break;
    case 3: value -= r[3] * UINT64_C(5); break;
    case 4: value = (value ^ r[2]) * UINT64_C(7); break;
    case 5: value += r[2] & UINT64_C(1023); break;
    case 6: value = (value >> 11) | (r[2] << 53); break;
    default: value = (value | r[2]) ^ r[3]; break;
    }
    r[1] = value;
    r[2] += key;
    return r[1] ^ r[2] ^ r[3];
}
