#include "../fixture.h"

/* Thirty-two two-bit operations, eight slots, checked full/empty transitions. */
uint64_t fixture(uint64_t state[4]) {
    struct queue { uint64_t values[8]; unsigned head, tail, count; } queue;
    uint64_t operations = state[0], value = state[2], checksum = state[3];
    unsigned limit = (unsigned)(state[1] & 31) + 1, rejected = 0, popped = 0;
    queue.head = 0;
    queue.tail = 0;
    queue.count = 0;
    for (unsigned step = 0; step < limit; ++step) {
        unsigned operation = (unsigned)((operations >> (step * 2)) & 3);
        if (operation == 0 || operation == 3) {
            if (queue.count < 8) {
                queue.values[queue.tail] = value;
                queue.tail = (queue.tail + 1) & 7;
                ++queue.count;
                value = value * 17 + step + 1;
            } else {
                ++rejected;
            }
        } else if (queue.count != 0) {
            if (operation == 1) {
                checksum = checksum * 33 + queue.values[queue.head];
                queue.head = (queue.head + 1) & 7;
                --queue.count;
                ++popped;
            } else {
                checksum ^= queue.values[queue.head];
            }
        } else {
            ++rejected;
        }
    }
    uint64_t front = queue.count ? queue.values[queue.head] : 0;
    state[0] = queue.count;
    state[1] = rejected;
    state[2] = checksum;
    state[3] = value;
    return checksum ^ front ^ ((uint64_t)popped << 32);
}
