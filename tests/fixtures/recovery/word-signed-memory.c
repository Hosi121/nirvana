#include "../fixture.h"

#define DIVISION_CASE(name, divisor) \
    uint64_t name(uint64_t state[4]) { \
        int32_t value = (int32_t)state[0]; \
        int32_t quotient = value / (divisor); \
        int32_t remainder = value % (divisor); \
        state[1] = (uint32_t)quotient; \
        state[2] = (uint32_t)remainder; \
        return state[1] ^ (state[2] << 8); \
    }

DIVISION_CASE(div_p3, INT32_C(3))
DIVISION_CASE(div_n3, -INT32_C(3))
DIVISION_CASE(div_p5, INT32_C(5))
DIVISION_CASE(div_n5, -INT32_C(5))
DIVISION_CASE(div_p7, INT32_C(7))
DIVISION_CASE(div_n7, -INT32_C(7))
DIVISION_CASE(div_p10, INT32_C(10))
DIVISION_CASE(div_n10, -INT32_C(10))
DIVISION_CASE(div_p11, INT32_C(11))
DIVISION_CASE(div_n11, -INT32_C(11))
DIVISION_CASE(div_p13, INT32_C(13))
DIVISION_CASE(div_n13, -INT32_C(13))
DIVISION_CASE(fixture, INT32_C(15))
DIVISION_CASE(div_n15, -INT32_C(15))
DIVISION_CASE(div_p17, INT32_C(17))
DIVISION_CASE(div_n17, -INT32_C(17))
DIVISION_CASE(div_p19, INT32_C(19))
DIVISION_CASE(div_n19, -INT32_C(19))
DIVISION_CASE(div_p31, INT32_C(31))
DIVISION_CASE(div_n31, -INT32_C(31))
