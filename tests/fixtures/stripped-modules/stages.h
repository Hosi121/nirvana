#ifndef NV_STAGES_H
#define NV_STAGES_H
#include <stdint.h>
uint64_t stage_add(uint64_t value, uint64_t salt);
uint64_t stage_fold(uint64_t value, uint64_t salt);
uint64_t stage_mix(uint64_t value, uint64_t salt);
extern uint64_t (*stage_table[3])(uint64_t, uint64_t);
#endif
