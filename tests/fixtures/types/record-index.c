#include <stdint.h>

struct record {
    uint32_t index;
    uint32_t reserved;
    const uint32_t *items;
};

uint64_t fixture(const struct record *record) {
    return record->items[record->index];
}
