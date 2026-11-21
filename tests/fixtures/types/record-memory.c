#include <stdint.h>

struct node {
    uint64_t value;
    struct node *next;
    uint32_t count;
};

/* Keep the pointer Store/Load visible under optimization. */
struct holder {
    struct node *volatile current;
};

uint64_t fixture(struct holder *holder, struct node *node, uint64_t value) {
    node->value = value;
    holder->current = node;
    struct node *current = holder->current;
    current->count += 1;
    return current->count;
}
