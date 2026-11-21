#include <stdio.h>

int main(void) {
    int a = 7;
    unsigned b = 9;
    unsigned long c = 11;
    long long d = -13;
    signed char e = -2;
    unsigned short f = 17;
    char text[256], cut[64];
    int read = scanf(" %d %u %lx %lld %hhd %hu", &a, &b, &c, &d, &e, &f);
    int length = sprintf(text, "%+d/%u/%#lx/%lld/%hhd/%hu", a, b, c, d, e, f);
    int truncated = snprintf(cut, sizeof(cut), "%s", text);
    printf("read=%d length=%d cut=%d: %s [%s] %*.*s %c %%\n",
           read, length, truncated, text, cut, -7, 3, "prefix", 'Z');
    return read < 0 ? 7 : read;
}
