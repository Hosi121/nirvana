/* Bounded Linux x86-64 integer/string stdio. Guest addresses never become
 * host varargs: each validated conversion has one explicitly typed argument.
 * Default C locale, valid buffers, ordinary nonoverlapping format objects. */
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef NV_GUEST_STDOUT
#define NV_GUEST_STDOUT(s) ((void)(s), stdout)
#endif
#ifndef NV_GUEST_STDIN
#define NV_GUEST_STDIN(s) ((void)(s), stdin)
#endif
#define NV_FORMAT_LIMIT 4096
#define NV_FORMAT_OUTPUT_LIMIT 65536
#define NV_FORMAT_CONVERSIONS 32

static inline unsigned nv_format_unsupported(struct nv_module *s) {
    s->status = 3;
    return 0;
}

/* The imported callee sees its return address at RSP. Integer/pointer
 * arguments occupy six GP slots, followed by eight-byte stack slots. */
static inline uint64_t nv_format_argument(struct nv_module *s, unsigned index) {
    static const unsigned gp[] = {7, 6, 2, 1, 8, 9};
    uint64_t displacement;
    if (index < 6) return s->r[gp[index]];
    displacement = UINT64_C(8) * (index - 5);
    if (s->r[4] > UINT64_MAX - displacement) {
        s->status = 1; s->fault_address = s->r[4];
        s->fault_width = 8; s->fault_access = 1;
        longjmp(s->jump, 1);
    }
    return nv_read(s, s->r[4] + displacement, 8);
}

/* A precision-limited %s can read a prefix without a trailing NUL. */
static inline const char *nv_format_string(struct nv_module *s, uint64_t address,
                                           size_t maximum, size_t *length) {
    uint64_t offset;
    size_t available, count;
    const char *bytes, *zero;
    if (maximum == 0) { *length = 0; return ""; }
    offset = nv_check(s, address, 1, 1);
    available = (size_t)(s->size - offset);
    count = available < maximum ? available : maximum;
    bytes = (const char *)(s->memory + offset);
    zero = (const char *)memchr(bytes, 0, count);
    if (zero) { *length = (size_t)(zero - bytes); return bytes; }
    if (available < maximum) {
        (void)nv_check(s, address, (uint64_t)available + 1, 1);
        *length = 0;
        return ""; /* nv_check has already raised the checked range fault. */
    }
    *length = count;
    return bytes;
}

/* Parse one nonpositional conversion; width/precision may be dynamic for
 * output. Only the accepted grammar is ever handed to a host formatter. */
struct nv_format_spec {
    char text[64], conversion;
    unsigned length; /* 0:int, 1:hh, 2:h, 3:l, 4:ll */
    size_t end;
    int width, precision;
};
static inline unsigned nv_format_number(const char *format, size_t *cursor, int *value) {
    *value = 0;
    while (format[*cursor] >= '0' && format[*cursor] <= '9') {
        int digit = format[(*cursor)++] - '0';
        if (*value > (NV_FORMAT_OUTPUT_LIMIT - digit) / 10) return 0;
        *value = *value * 10 + digit;
    }
    return 1;
}
static inline unsigned nv_format_parse(struct nv_module *s, const char *format,
                                        size_t begin, unsigned input,
                                        unsigned *argument, struct nv_format_spec *spec) {
    size_t at = begin + 1, used = 1, flag_count = 0;
    char flags[8];
    unsigned has_width = 0, has_precision = 0;
    spec->length = 0; spec->width = 0; spec->precision = -1;
    spec->text[0] = '%';
    if (!input) {
        while (format[at] && strchr("-+ #0", format[at])) {
            if (flag_count == sizeof(flags) - 1) return 0;
            flags[flag_count++] = format[at++];
        }
    }
    flags[flag_count] = 0;
    if (!input && format[at] == '*') {
        int32_t width = (int32_t)(uint32_t)nv_format_argument(s, (*argument)++);
        ++at; has_width = 1;
        if (width < -NV_FORMAT_OUTPUT_LIMIT || width > NV_FORMAT_OUTPUT_LIMIT) return 0;
        if (width < 0) {
            if (flag_count == sizeof(flags) - 1) return 0;
            flags[flag_count++] = '-'; flags[flag_count] = 0;
            width = -width;
        }
        spec->width = width;
    } else if (format[at] >= '0' && format[at] <= '9') {
        has_width = 1;
        if (!nv_format_number(format, &at, &spec->width)) return 0;
        if (input && spec->width == 0) return 0;
    }
    if (!input && format[at] == '.') {
        ++at; has_precision = 1; spec->precision = 0;
        if (format[at] == '*') {
            spec->precision = (int32_t)(uint32_t)nv_format_argument(s, (*argument)++);
            ++at;
            if (spec->precision > NV_FORMAT_OUTPUT_LIMIT) return 0;
            if (spec->precision < 0) has_precision = 0;
        } else if (!nv_format_number(format, &at, &spec->precision)) return 0;
    }
    if (format[at] == 'h') {
        ++at; spec->length = 2;
        if (format[at] == 'h') { ++at; spec->length = 1; }
    } else if (format[at] == 'l') {
        ++at; spec->length = 3;
        if (format[at] == 'l') { ++at; spec->length = 4; }
    }
    spec->conversion = format[at];
    if (!spec->conversion || !strchr(input ? "diuoxX" : "diuoxXcs", spec->conversion)) return 0;
    if ((spec->conversion == 'c' || spec->conversion == 's') && spec->length) return 0;
    if (spec->conversion == 'c' && has_precision) return 0;
    /* C only defines '-' for strings/chars, '+'/' ' for signed conversions,
     * '#' for octal/hex, and zero padding for integer conversions. */
    for (size_t i = 0; i < flag_count; ++i) {
        char flag = flags[i], conversion = spec->conversion;
        if ((flag == '+' || flag == ' ') && !strchr("di", conversion)) return 0;
        if (flag == '#' && !strchr("oxX", conversion)) return 0;
        if (flag == '0' && !strchr("diuoxX", conversion)) return 0;
    }
    spec->end = at + 1;
    memcpy(spec->text + used, flags, flag_count); used += flag_count;
    if (has_width) used += (size_t)snprintf(spec->text + used, sizeof(spec->text) - used, "%d", spec->width);
    if (has_precision) used += (size_t)snprintf(spec->text + used, sizeof(spec->text) - used, ".%d", spec->precision);
    if (input) {
        const char *length = spec->length == 1 ? "hh" : spec->length == 2 ? "h" : spec->length == 3 ? "l" : spec->length == 4 ? "ll" : "";
        size_t n = strlen(length); memcpy(spec->text + used, length, n); used += n;
    } else if (strchr("diuoxX", spec->conversion)) {
        spec->text[used++] = 'l'; spec->text[used++] = 'l';
    }
    spec->text[used++] = spec->conversion; spec->text[used] = 0;
    return 1;
}

static inline unsigned nv_format_output(struct nv_module *s, const char *format,
                                         unsigned argument, char *output, size_t *size) {
    size_t at = 0, used = 0;
    unsigned conversions = 0;
    while (format[at]) {
        struct nv_format_spec spec;
        uint64_t value;
        int count;
        if (format[at] != '%' || format[at + 1] == '%') {
            if (used == NV_FORMAT_OUTPUT_LIMIT) return 0;
            output[used++] = format[at++];
            if (output[used - 1] == '%') ++at;
            continue;
        }
        if (++conversions > NV_FORMAT_CONVERSIONS ||
            !nv_format_parse(s, format, at, 0, &argument, &spec)) return 0;
        value = nv_format_argument(s, argument++);
        if (spec.conversion == 's') {
            size_t length;
            const char *string = nv_format_string(s, value,
                spec.precision < 0 ? SIZE_MAX : (size_t)spec.precision, &length);
            /* With a precision the host formatter also accepts a non-NUL
             * prefix; otherwise nv_format_string established termination. */
            count = snprintf(output + used, NV_FORMAT_OUTPUT_LIMIT + 1 - used, spec.text, string);
        } else if (spec.conversion == 'c') {
            count = snprintf(output + used, NV_FORMAT_OUTPUT_LIMIT + 1 - used, spec.text, (int)(uint8_t)value);
        } else if (strchr("di", spec.conversion)) {
            int64_t signed_value = spec.length == 1 ? (int8_t)value : spec.length == 2 ? (int16_t)value : spec.length >= 3 ? (int64_t)value : (int32_t)value;
            count = snprintf(output + used, NV_FORMAT_OUTPUT_LIMIT + 1 - used, spec.text, (long long)signed_value);
        } else {
            uint64_t unsigned_value = spec.length == 1 ? (uint8_t)value : spec.length == 2 ? (uint16_t)value : spec.length >= 3 ? value : (uint32_t)value;
            count = snprintf(output + used, NV_FORMAT_OUTPUT_LIMIT + 1 - used, spec.text, (unsigned long long)unsigned_value);
        }
        if (count < 0 || (size_t)count > NV_FORMAT_OUTPUT_LIMIT - used) return 0;
        used += (size_t)count; at = spec.end;
    }
    output[used] = 0; *size = used;
    return 1;
}

struct nv_scan_conversion { struct nv_format_spec spec; unsigned argument; };
static inline unsigned nv_format_input(struct nv_module *s, const char *format, int *result) {
    struct nv_scan_conversion conversions[NV_FORMAT_CONVERSIONS];
    unsigned count = 0, argument = 1, index = 0;
    size_t at = 0;
    FILE *stream;
    /* Validate the complete grammar before consuming input. Destinations are
     * checked at their conversion, so earlier assignments can alias later
     * stack arguments without freezing their old pointer values. */
    while (format[at]) {
        if (format[at] != '%' || format[at + 1] == '%') {
            if (format[at++] == '%') ++at;
        } else {
            struct nv_scan_conversion *conversion;
            if (count == NV_FORMAT_CONVERSIONS) return 0;
            conversion = &conversions[count++];
            if (!nv_format_parse(s, format, at, 1, &argument, &conversion->spec)) return 0;
            conversion->argument = argument++;
            at = conversion->spec.end;
        }
    }
    stream = NV_GUEST_STDIN(s);
    if (!stream) return 0;
    at = 0; *result = 0;
    while (format[at]) {
        int ch, matched;
        uint64_t value = 0, destination;
        struct nv_scan_conversion *conversion;
        unsigned width;
        if (isspace((unsigned char)format[at])) {
            do { ch = fgetc(stream); } while (ch != EOF && isspace((unsigned char)ch));
            if (ch != EOF) (void)ungetc(ch, stream);
            ++at; continue;
        }
        if (format[at] != '%' || format[at + 1] == '%') {
            ch = fgetc(stream);
            if (ch != (unsigned char)format[at]) {
                if (ch != EOF) (void)ungetc(ch, stream);
                else if (*result == 0) *result = EOF;
                return 1;
            }
            if (format[at++] == '%') ++at;
            continue;
        }
        conversion = &conversions[index++];
        width = conversion->spec.length == 1 ? 1 : conversion->spec.length == 2 ? 2 : conversion->spec.length >= 3 ? 8 : 4;
        destination = nv_format_argument(s, conversion->argument);
        (void)nv_check(s, destination, width, 2);
        /* Separate typed locals avoid pointer punning and variadic type UB. */
#define NV_SCAN_TYPED(type) do { type item = 0; matched = fscanf(stream, conversion->spec.text, &item); value = (uint64_t)item; } while (0)
        if (strchr("di", conversion->spec.conversion)) {
            switch (conversion->spec.length) {
            case 1: NV_SCAN_TYPED(signed char); break;
            case 2: NV_SCAN_TYPED(short); break;
            case 3: NV_SCAN_TYPED(long); break;
            case 4: NV_SCAN_TYPED(long long); break;
            default: NV_SCAN_TYPED(int); break;
            }
        } else {
            switch (conversion->spec.length) {
            case 1: NV_SCAN_TYPED(unsigned char); break;
            case 2: NV_SCAN_TYPED(unsigned short); break;
            case 3: NV_SCAN_TYPED(unsigned long); break;
            case 4: NV_SCAN_TYPED(unsigned long long); break;
            default: NV_SCAN_TYPED(unsigned int); break;
            }
        }
#undef NV_SCAN_TYPED
        if (matched != 1) {
            if (matched == EOF && *result == 0) *result = EOF;
            return 1;
        }
        nv_write(s, destination, width, value);
        ++*result; at = conversion->spec.end;
    }
    return 1;
}

static inline unsigned nv_formatted_call(struct nv_module *s, const char *name, int *result) {
    char format[NV_FORMAT_LIMIT + 1], output[NV_FORMAT_OUTPUT_LIMIT + 1];
    uint64_t format_address, destination = 0, capacity = UINT64_MAX;
    uint64_t object_size = UINT64_MAX;
    unsigned argument = 1;
    unsigned printing = !strcmp(name, "printf") || !strcmp(name, "__printf_chk");
    size_t length, size;
    const char *string;
    FILE *stream;
    if (!strcmp(name, "putchar")) {
        stream = NV_GUEST_STDOUT(s);
        if (!stream) return nv_format_unsupported(s);
        *result = fputc((int)(uint8_t)s->r[7], stream);
        return 1;
    }
    if (!strcmp(name, "sprintf") || !strcmp(name, "snprintf")) {
        destination = s->r[7]; argument = 2;
        if (!strcmp(name, "snprintf")) { capacity = s->r[6]; argument = 3; }
    } else if (!strcmp(name, "__printf_chk")) argument = 2;
    else if (!strcmp(name, "__sprintf_chk")) {
        destination = s->r[7]; object_size = s->r[2]; argument = 4;
    } else if (!strcmp(name, "__snprintf_chk")) {
        destination = s->r[7]; capacity = s->r[6]; object_size = s->r[1]; argument = 5;
        if (capacity > object_size) return nv_format_unsupported(s);
    }
    format_address = nv_format_argument(s, argument - 1);
    string = nv_format_string(s, format_address, NV_FORMAT_LIMIT + 1, &length);
    if (length > NV_FORMAT_LIMIT) return nv_format_unsupported(s);
    memcpy(format, string, length); format[length] = 0;
    if (!strcmp(name, "scanf") || !strcmp(name, "__isoc99_scanf")) {
        if (!nv_format_input(s, format, result)) return nv_format_unsupported(s);
        return 1;
    }
    if (!nv_format_output(s, format, argument, output, &size)) return nv_format_unsupported(s);
    if (printing) {
        stream = NV_GUEST_STDOUT(s);
        if (!stream) return nv_format_unsupported(s);
        *result = fwrite(output, 1, size, stream) == size ? (int)size : -1;
    } else if (capacity) {
        size_t copied = capacity - 1 < size ? (size_t)(capacity - 1) : size;
        if (copied + 1 > object_size) return nv_format_unsupported(s);
        uint64_t offset = nv_check(s, destination, copied + 1, 2);
        memcpy(s->memory + offset, output, copied); s->memory[offset + copied] = 0;
        *result = (int)size;
    } else *result = (int)size;
    return 1;
}
