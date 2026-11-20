#include "../fixture.h"

/* Eight packed adjacency rows; vertices are discovered before enqueueing. */
uint64_t fixture(uint64_t state[4]) {
    struct entry { unsigned vertex, distance; };
    struct queue { struct entry entries[8]; unsigned head, tail; } queue;
    uint64_t graph = state[0], seed = state[2], order = 0, distances = 0;
    unsigned n = (unsigned)(state[1] & 7) + 1;
    unsigned start = (unsigned)((state[1] >> 3) & 7);
    if (start >= n) start = n - 1;
    unsigned visited = 1u << start, count = 0;
    queue.head = 0;
    queue.tail = 1;
    queue.entries[0].vertex = start;
    queue.entries[0].distance = 0;
    while (queue.head < queue.tail) {
        struct entry current = queue.entries[queue.head++];
        order = (order << 4) | (current.vertex + 1);
        distances += current.distance;
        ++count;
        for (unsigned next = 0; next < n; ++next) {
            unsigned bit = 1u << next;
            if (((graph >> (current.vertex * 8 + next)) & 1) && !(visited & bit)) {
                visited |= bit;
                queue.entries[queue.tail].vertex = next;
                queue.entries[queue.tail].distance = current.distance + 1;
                ++queue.tail;
            }
        }
    }
    state[0] = visited;
    state[1] = count;
    state[2] = order;
    state[3] = distances;
    return seed ^ order ^ distances;
}
