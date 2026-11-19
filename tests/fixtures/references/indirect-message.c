#include <stdio.h>

const char *volatile message = "from a relocated pointer";

int fixture(void) {
    return puts(message);
}
