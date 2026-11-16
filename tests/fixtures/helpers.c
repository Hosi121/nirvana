#include "fixture.h"

uint64_t fixture_mix(uint64_t left, uint64_t right) {
    return left * UINT64_C(3) + right;
}
