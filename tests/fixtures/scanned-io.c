#include <stdio.h>

int main(void) {
    char line[80] = "", copy[80], closing[8] = "";
    char left[8] = "LEFT", right[8] = "RIGHT", pair[2] = {'q', 'q'};
    char tail[8] = "TAIL", token[9] = "";
    signed char a = -7;
    unsigned short b = 11;
    long long c = -13;
    printf("read: ");
    fflush(stdout);
    char *got = fgets(line, sizeof(line), stdin);
    int n = sscanf(line, "token:%5[a-z]|%2[}] %hhd %hu %lld %2c %3s",
                   left, right, &a, &b, &c, pair, tail);
    snprintf(copy, sizeof(copy), "%s", line);
    int m = sscanf(copy, "record{%8s%7[}]", token, closing);
    printf("%d/%d %s/%s %d %u %lld %u,%u %s m=%d token=%s close=%s\n",
           got == line, n, left, right, a, b, c,
           (unsigned char)pair[0], (unsigned char)pair[1], tail, m, token, closing);
    return 0;
}
