#include "stages.h"
uint64_t (*stage_table[3])(uint64_t, uint64_t) = {
    stage_add, stage_fold, stage_mix
};
