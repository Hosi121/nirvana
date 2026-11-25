#include <stdint.h>

#define VARIABLE_SAR(instruction, value, carry, count)               \
    __asm__ volatile ("xor %k1, %k1\n\t" instruction " %%cl, %0\n\t" \
                      "setb %b1"                                   \
                      : "+q" (value), "=&q" (carry)                 \
                      : "c" (count) : "cc")
#define FIXED_SAR(instruction, value, carry)                         \
    __asm__ volatile ("xor %k1, %k1\n\t" instruction "\n\tsetb %b1"  \
                      : "+q" (value), "=&q" (carry) : : "cc")

uint64_t fixture(uint64_t state[4]) {
    volatile uint64_t *memory = state;
    uint64_t input = memory[0], count = memory[1];
    uint8_t byte = (uint8_t)input, fixed_byte = (uint8_t)input;
    uint16_t word = (uint16_t)input, fixed_word = (uint16_t)input;
    uint64_t c0, c1, c2, c3;
    VARIABLE_SAR("sarb", byte, c0, count);
    VARIABLE_SAR("sarw", word, c1, count);
    FIXED_SAR("sarb $15, %0", fixed_byte, c2);
    FIXED_SAR("sarw $31, %0", fixed_word, c3);
    memory[0] = byte;
    memory[1] = word;
    memory[2] = fixed_byte ^ ((uint64_t)fixed_word << 16);
    memory[3] = (c0 & 1) | ((c1 & 1) << 1)
                        | ((c2 & 1) << 2) | ((c3 & 1) << 3);
    return memory[0] ^ memory[1] ^ memory[2] ^ memory[3];
}
