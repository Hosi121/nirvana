#include "stages.h"
uint64_t fixture(uint64_t *s) {
    uint64_t value = s[1], salt = s[2];
    unsigned rounds = (unsigned)(s[3] & 3) + 1;
    for (unsigned i = 0; i < rounds; ++i) {
        switch ((s[0] + i) & 3) {
        case 0: value = stage_add(value, salt); break;
        case 1: value = stage_fold(value, salt); break;
        case 2: value = stage_mix(value, salt); break;
        default: value = stage_table[(value ^ salt) % 3](value, salt); break;
        }
        salt += value & 255;
    }
    s[1] = value;
    s[2] = salt;
    return value ^ salt;
}
