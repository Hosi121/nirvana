#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

#ifndef FIXTURE_ENTRY
#define FIXTURE_ENTRY fixture
#endif

uint64_t FIXTURE_ENTRY(uint64_t state[4]);

int main(void) {
    uint64_t state[4];
    int fields;
    while ((fields = scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                          &state[0], &state[1], &state[2], &state[3])) == 4) {
        uint64_t result = FIXTURE_ENTRY(state);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               result, state[0], state[1], state[2], state[3]);
    }
    return fields == EOF ? 0 : 2;
}
