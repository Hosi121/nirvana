#include "../fixture.h"
#include <stddef.h>

/* A seven-node balanced BST, with runtime keys and actual child pointers. */
uint64_t fixture(uint64_t state[4]) {
    struct node { uint64_t key; struct node *left, *right; } nodes[7];
    uint64_t base = state[0] & 65535, gap = (state[1] & 15) + 1;
    uint64_t target = state[2], path = state[3], found = 0, key = 0;
    for (unsigned i = 0; i < 7; ++i) {
        unsigned rank = i == 0 ? 3 : (i < 3 ? i * 4 - 3 : (i - 3) * 2);
        nodes[i].key = base + rank * gap;
        nodes[i].left = i < 3 ? &nodes[i * 2 + 1] : NULL;
        nodes[i].right = i < 3 ? &nodes[i * 2 + 2] : NULL;
    }
    struct node *node = &nodes[0];
    unsigned steps = 0;
    while (node != NULL && steps < 7) {
        ++steps;
        path = path * 17 + node->key;
        if (target == node->key) {
            found = 1;
            key = node->key;
            break;
        }
        node = target < node->key ? node->left : node->right;
    }
    state[0] = found;
    state[1] = key;
    state[2] = steps;
    state[3] = path;
    return found ? key + 1 : 0;
}
