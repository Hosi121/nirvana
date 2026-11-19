#include <stdio.h>

int fixture(void) {
    int result = puts("first");
    if (result < 0) {
        return puts("failure");
    }
    return puts("success") + result;
}
