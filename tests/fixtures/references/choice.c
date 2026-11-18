#include <stdio.h>

int fixture(int choice) {
    const char *message = choice ? "first" : "second";
    return puts(message);
}
