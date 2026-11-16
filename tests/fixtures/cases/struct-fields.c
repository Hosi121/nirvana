#include "../fixture.h"

struct pair {
    uint64_t left;
    uint64_t right;
    uint64_t swap;
};

uint64_t fixture(uint64_t r[4]) {
    struct pair pair = {r[0], r[1], r[2] & UINT64_C(1)};
    if (pair.swap) {
        uint64_t temporary = pair.left;
        pair.left = pair.right;
        pair.right = temporary;
    }
    pair.left += UINT64_C(3);
    r[0] = pair.left;
    r[1] = pair.right;
    r[3] = pair.left ^ pair.right;
    return r[3] + r[2];
}
