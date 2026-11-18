#include <stdint.h>

struct record {
    uint64_t index;
    uint32_t *items;
    uint64_t next;
    uint64_t seed;
};

uint64_t fixture(struct record *record) {
    uint64_t index = record->index & 7;
    uint32_t value = record->items[index];
    record->items[(index + 1) & 7] = (uint32_t)(value + record->seed);
    record->seed = value;
    return record->items[index] ^ value;
}
