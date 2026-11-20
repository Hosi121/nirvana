#include <stddef.h>
#include <stdint.h>

/* Keep both bodies available while optimizing their arithmetic and loops. */
__attribute__((noinline))
uint64_t lifetime_mix(uint64_t value) {
    uint64_t shifted = value >> 9;
    uint64_t mixed = (value ^ shifted) * UINT64_C(37);
    return mixed + UINT64_C(17);
}

__attribute__((noinline))
uint64_t lifetime_fold(const uint64_t *items, size_t count) {
    uint64_t total = UINT64_C(3);
    for (size_t i = 0; i < count; ++i) {
        uint64_t element = items[i];
        uint64_t contribution;
        if (element & UINT64_C(1)) {
            contribution = element + total;
        } else {
            contribution = element ^ (total >> 1);
        }
        total = lifetime_mix(contribution) + i;
    }
    return total ^ count;
}

int main(void) {
    const uint64_t items[] = { 2, 7, 4, 13 };
    uint64_t actual = lifetime_fold(items, sizeof(items) / sizeof(items[0]));
    uint64_t expected = UINT64_C(3);
    for (size_t i = 0; i < sizeof(items) / sizeof(items[0]); ++i) {
        uint64_t contribution = (items[i] & 1) ? items[i] + expected : items[i] ^ (expected >> 1);
        expected = lifetime_mix(contribution) + i;
    }
    return actual == (expected ^ 4) ? 0 : 1;
}
