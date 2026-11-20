#include "../fixture.h"

/* Explicit continuation frames reproduce recursive ascending-neighbor DFS. */
uint64_t fixture(uint64_t state[4]) {
    struct frame { unsigned vertex, next; } frames[8];
    uint64_t graph = state[0], seed = state[2];
    unsigned n = (unsigned)(state[1] & 7) + 1;
    unsigned start = (unsigned)((state[1] >> 3) & 7);
    if (start >= n) start = n - 1;
    unsigned visited = 1u << start, count = 1, depth = 1, maximum = 1;
    uint64_t order = start + 1;
    frames[0].vertex = start;
    frames[0].next = 0;
    while (depth != 0) {
        struct frame *frame = &frames[depth - 1];
        if (frame->next == n) {
            --depth;
        } else {
            unsigned next = frame->next++;
            unsigned bit = 1u << next;
            if (((graph >> (frame->vertex * 8 + next)) & 1) && !(visited & bit)) {
                visited |= bit;
                order = (order << 4) | (next + 1);
                ++count;
                frames[depth].vertex = next;
                frames[depth].next = 0;
                ++depth;
                if (depth > maximum) maximum = depth;
            }
        }
    }
    state[0] = visited;
    state[1] = count;
    state[2] = order;
    state[3] = maximum;
    return seed ^ order ^ maximum;
}
