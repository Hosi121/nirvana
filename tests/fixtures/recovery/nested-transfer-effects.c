#include <stdint.h>

uint64_t fixture(uint64_t state[4]) {
    unsigned char *bytes = (unsigned char *)state;
    uint64_t mode = state[0] & UINT64_C(7);
    uint64_t sum = state[1];
    for (uint64_t outer = 0; outer < UINT64_C(3); ++outer) {
        for (uint64_t middle = 0; middle < UINT64_C(3); ++middle) {
            for (uint64_t inner = 0; inner < UINT64_C(2); ++inner) {
                uint64_t index = (outer + middle + inner) & UINT64_C(3);
                uint64_t before = state[index];
                sum ^= before + outer + middle + inner;
                uint64_t byte = (sum ^ inner) & UINT64_C(31);
                bytes[byte] = (unsigned char)((uint64_t)bytes[byte] ^ sum);
                if ((mode & UINT64_C(1)) != 0 && outer == 0 && inner == 0) {
                    state[1] += sum;
                    goto next_outer;
                }
                if ((mode & UINT64_C(2)) != 0 && middle == UINT64_C(1)) {
                    state[2] ^= sum;
                    goto done;
                }
                if ((mode & UINT64_C(4)) != 0 && outer == UINT64_C(2)) {
                    state[3] = sum;
                    return state[index] + sum;
                }
                state[index] = before + sum;
            }
        }
next_outer:
        state[(outer + UINT64_C(1)) & UINT64_C(3)] ^= sum;
    }
done:
    state[3] += sum;
    return sum ^ state[0];
}
