#include <stdint.h>

uint64_t fixture(uint64_t s[4]) {
    uint64_t outer = (s[0] & UINT64_C(3)) + UINT64_C(1);
    uint64_t inner = (s[1] & UINT64_C(3)) + UINT64_C(1);
    uint64_t total = s[2];
    uint64_t mark = s[3];
    for (uint64_t i = 0; i < outer; ++i) {
        for (uint64_t j = 0; j < inner; ++j) {
            total += s[(i + j) & UINT64_C(3)] ^ (i + UINT64_C(1));
            s[2] = total;
            if (((total ^ mark) & UINT64_C(7)) == 0)
                goto cleanup;
            if ((total & UINT64_C(3)) == UINT64_C(1)) {
                mark ^= i + j;
                goto next_outer;
            }
            mark += total & UINT64_C(15);
        }
next_outer:
        mark += i + UINT64_C(1);
        s[3] = mark;
    }
cleanup:
    s[2] = total;
    s[3] = mark;
    return total ^ mark;
}
