#include "../fixture.h"
#include <stddef.h>

/* Nibble links can form cycles; the externally selected bound is 1..16. */
uint64_t fixture(uint64_t state[4]) {
    struct node { uint64_t value; struct node *next; unsigned tag; } nodes[8];
    uint64_t links = state[0], values = state[2], sum = 0, trace = 0;
    unsigned n = (unsigned)(state[1] & 7) + 1;
    unsigned start = (unsigned)((state[1] >> 3) & 7);
    unsigned limit = (unsigned)(state[3] & 15) + 1;
    if (start >= n) start = n - 1;
    for (unsigned i = 0; i < n; ++i) {
        unsigned next = (unsigned)((links >> (i * 4)) & 15);
        nodes[i].value = ((values >> (i * 8)) & 255) + i;
        nodes[i].next = next < n ? &nodes[next] : NULL;
        nodes[i].tag = i + 1;
    }
    struct node *node = &nodes[start];
    unsigned steps = 0, visited = 0;
    while (node != NULL && steps < limit) {
        sum += node->value;
        trace = trace * 17 + node->tag;
        visited |= 1u << (node->tag - 1);
        ++steps;
        node = node->next;
    }
    state[0] = sum;
    state[1] = steps;
    state[2] = visited;
    state[3] = trace;
    return sum ^ trace ^ (node == NULL ? (UINT64_C(1) << 63) : 0);
}
