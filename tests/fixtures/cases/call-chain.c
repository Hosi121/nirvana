#include "../fixture.h"

uint64_t fixture(uint64_t r[4]) {
    uint64_t first = fixture_mix(r[0], r[1]);
    uint64_t second = fixture_mix(first, r[2]);
    r[3] = second;
    return second ^ r[0];
}
