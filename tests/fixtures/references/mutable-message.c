#include <stdio.h>

char message[] = "Hello";

int fixture(void) {
    message[0] = 'h';
    return puts(message);
}
