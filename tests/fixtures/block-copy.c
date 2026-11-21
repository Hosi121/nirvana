#include "fixture.h"

struct block {
    uint64_t words[64];
};

static struct block source_block, destination_block;

__attribute__((noinline)) uint64_t copy_block(struct block *destination, const struct block *source) {
    *destination = *source;
    return destination->words[0] ^ destination->words[63];
}

uint64_t fixture(uint64_t state[4]) {
    uint64_t value = state[0];
    for (uint64_t i = 0; i < 64; ++i) {
        value = value * UINT64_C(6364136223846793005) + i + state[1];
        source_block.words[i] = value;
    }
    uint64_t edge = copy_block(&destination_block, &source_block);
    uint64_t hash = 0;
    for (unsigned i = 0; i < 64; ++i)
        hash = (hash << 7) ^ (hash >> 57) ^ destination_block.words[i];
    state[2] = edge;
    state[3] = hash;
    return edge + hash;
}
