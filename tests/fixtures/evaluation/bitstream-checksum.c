#include "../fixture.h"

uint64_t fixture(uint64_t state[4]) {
    uint64_t data = state[0];
    uint64_t count = state[1] & 7;
    uint64_t crc = state[2] & UINT64_C(4294967295);
    uint64_t consumed = 0;
    while (consumed < count) {
        crc ^= data & 255;
        for (uint64_t bit = 0; bit < 8; ++bit) {
            if (crc & 1) {
                crc = (crc >> 1) ^ UINT64_C(3988292384);
            } else {
                crc >>= 1;
            }
        }
        data >>= 8;
        ++consumed;
    }
    state[0] = data;
    state[1] = consumed;
    state[2] = crc;
    state[3] += crc;
    return state[3];
}
