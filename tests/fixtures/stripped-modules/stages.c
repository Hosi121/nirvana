#include "stages.h"
uint64_t stage_add(uint64_t value, uint64_t salt) {
    return value + salt * UINT64_C(3);
}
uint64_t stage_fold(uint64_t value, uint64_t salt) {
    return ((value << 9) | (value >> 55)) ^ salt;
}
uint64_t stage_mix(uint64_t value, uint64_t salt) {
    return (value ^ salt) * UINT64_C(0x100000001b3);
}
