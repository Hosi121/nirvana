#include <stdint.h>

/* Each instruction reads a seeded CF when its masked count is zero. */
#define SHIFT_CARRY(instruction, value, carry, count)                  \
    __asm__ volatile ("xor %k1, %k1\n\t" instruction " %%cl, %0\n\t" \
                      "setb %b1"                                    \
                      : "+r" (value), "=&q" (carry)                  \
                      : "c" (count) : "cc")

uint64_t fixture(uint64_t state[4]) {
    volatile uint64_t *memory = state;
    uint64_t input = memory[0], count = memory[1];
    uint64_t left = input, right = input, arithmetic = input;
    uint32_t left32 = (uint32_t)input, right32 = (uint32_t)input;
    uint32_t arithmetic32 = (uint32_t)input;
    uint64_t c0, c1, c2, c3, c4, c5;
    SHIFT_CARRY("shlq", left, c0, count);
    SHIFT_CARRY("shrq", right, c1, count);
    SHIFT_CARRY("sarq", arithmetic, c2, count);
    SHIFT_CARRY("shll", left32, c3, count);
    SHIFT_CARRY("shrl", right32, c4, count);
    SHIFT_CARRY("sarl", arithmetic32, c5, count);
    memory[0] = left;
    memory[1] = right;
    memory[2] = arithmetic ^ ((uint64_t)left32 << 32)
                          ^ right32 ^ ((uint64_t)arithmetic32 << 16);
    memory[3] = (c0 & 1) | ((c1 & 1) << 1) | ((c2 & 1) << 2)
                        | ((c3 & 1) << 3) | ((c4 & 1) << 4) | ((c5 & 1) << 5);
    return memory[0] ^ memory[1] ^ memory[2] ^ memory[3];
}
