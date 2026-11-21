#include <stdint.h>

#define WORDS(N, D) \
    uint32_t q32_p##N(int32_t x) { return (uint32_t)(x / (D)); } \
    uint32_t r32_p##N(int32_t x) { return (uint32_t)(x % (D)); } \
    uint32_t q32_n##N(int32_t x) { return (uint32_t)(x / -(D)); } \
    uint32_t r32_n##N(int32_t x) { return (uint32_t)(x % -(D)); }

WORDS(3, 3)
WORDS(5, 5)
WORDS(7, 7)
WORDS(10, 10)
WORDS(11, 11)
WORDS(13, 13)
WORDS(15, 15)
WORDS(17, 17)
WORDS(19, 19)
WORDS(31, 31)

int64_t wide_p7(int32_t x) { return x / 7; }
int64_t wide_n7(int32_t x) { return x / -7; }
