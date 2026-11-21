#include "../fixture.h"

#define DIVISION_CASE(name, divisor) \
    uint64_t name(uint64_t state[4]) { \
        int64_t value = (int64_t)state[0]; \
        int64_t quotient = value / (divisor); \
        int64_t remainder = value % (divisor); \
        state[1] = (uint64_t)quotient; \
        state[2] = (uint64_t)remainder; \
        return state[1] ^ (state[2] << 8); \
    }

DIVISION_CASE(div_p3, INT64_C(3))
DIVISION_CASE(div_n3, -INT64_C(3))
DIVISION_CASE(div_p5, INT64_C(5))
DIVISION_CASE(div_n5, -INT64_C(5))
DIVISION_CASE(div_p7, INT64_C(7))
DIVISION_CASE(div_n7, -INT64_C(7))
DIVISION_CASE(div_p10, INT64_C(10))
DIVISION_CASE(div_n10, -INT64_C(10))
DIVISION_CASE(div_p11, INT64_C(11))
DIVISION_CASE(div_n11, -INT64_C(11))
DIVISION_CASE(div_p13, INT64_C(13))
DIVISION_CASE(div_n13, -INT64_C(13))
DIVISION_CASE(fixture, INT64_C(15))
DIVISION_CASE(div_n15, -INT64_C(15))
DIVISION_CASE(div_p17, INT64_C(17))
DIVISION_CASE(div_n17, -INT64_C(17))
DIVISION_CASE(div_p19, INT64_C(19))
DIVISION_CASE(div_n19, -INT64_C(19))
DIVISION_CASE(div_p31, INT64_C(31))
DIVISION_CASE(div_n31, -INT64_C(31))
