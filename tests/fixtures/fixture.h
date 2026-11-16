#ifndef NIRVANA_FIXTURE_H
#define NIRVANA_FIXTURE_H

#include <stdint.h>

/* Four observable unsigned inputs/outputs, plus a separate return value. */
uint64_t fixture(uint64_t state[4]);

/* Defined in a separate translation unit to retain an external call without LTO. */
uint64_t fixture_mix(uint64_t left, uint64_t right);

#endif
