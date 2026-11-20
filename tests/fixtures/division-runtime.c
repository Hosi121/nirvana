#include <stdint.h>
#include <limits.h>

#if NV_SIGNED && NV_BITS == 64
typedef int64_t number;
#define LOWEST INT64_MIN
#elif NV_SIGNED
typedef int32_t number;
#define LOWEST INT32_MIN
#elif NV_BITS == 64
typedef uint64_t number;
#else
typedef uint32_t number;
#endif

uint64_t fixture(uint64_t *state) {
    number value = (number)state[0], divisor = (number)state[1];
    if (divisor == 0) { state[3] = 1; return 0; }
#if NV_SIGNED
    if (value == LOWEST && divisor == -1) { state[3] = 1; return 0; }
#endif
    state[2] = (uint64_t)(value / divisor);
    state[3] = (uint64_t)(value % divisor);
    return state[2] ^ state[3];
}
