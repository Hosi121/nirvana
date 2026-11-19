#include "http_server.h"

int http_header_name_byte(uint32_t byte) {
    return (byte >= 'a' && byte <= 'z') || (byte >= 'A' && byte <= 'Z') ||
           (byte >= '0' && byte <= '9') || byte == '-';
}

int http_header_value_byte(uint32_t byte) {
    return byte == '\t' || (byte >= 32u && byte < 127u);
}

int http_request_complete(const char *bytes, size_t length) {
    size_t i;
    for (i = 3; i < length; ++i) {
        if (bytes[i - 3] == '\r' && bytes[i - 2] == '\n' &&
            bytes[i - 1] == '\r' && bytes[i] == '\n') {
            return 1;
        }
    }
    return 0;
}

int http_parse_request(const char *bytes, size_t length,
                       struct http_request *request) {
    static const char version_prefix[] = "HTTP/1.";
    size_t cursor = 0;
    size_t count = 0;
    size_t i;
    request->header_count = 0;
    if (length > HTTP_REQUEST_CAPACITY) {
        return 0;
    }
    while (cursor < length && bytes[cursor] != ' ') {
        unsigned char byte = (unsigned char)bytes[cursor++];
        if (byte < 'A' || byte > 'Z' || count + 1 >= sizeof(request->method)) {
            return 0;
        }
        request->method[count++] = (char)byte;
    }
    if (count == 0 || cursor == length) {
        return 0;
    }
    request->method[count] = '\0';
    ++cursor;
    count = 0;
    while (cursor < length && bytes[cursor] != ' ') {
        unsigned char byte = (unsigned char)bytes[cursor++];
        if (byte < 33u || byte >= 127u || count + 1 >= sizeof(request->path)) {
            return 0;
        }
        request->path[count++] = (char)byte;
    }
    if (count == 0 || request->path[0] != '/' || cursor == length) {
        return 0;
    }
    request->path[count] = '\0';
    ++cursor;
    if (length - cursor < 10u) {
        return 0;
    }
    for (i = 0; i < sizeof(version_prefix) - 1; ++i) {
        if (bytes[cursor++] != version_prefix[i]) {
            return 0;
        }
    }
    if ((bytes[cursor] != '0' && bytes[cursor] != '1') ||
        bytes[cursor + 1] != '\r' || bytes[cursor + 2] != '\n') {
        return 0;
    }
    cursor += 3;
    while (cursor + 1 < length) {
        size_t name_length = 0;
        if (bytes[cursor] == '\r' && bytes[cursor + 1] == '\n') {
            return cursor + 2 == length;
        }
        while (cursor < length && bytes[cursor] != ':') {
            if (!http_header_name_byte((unsigned char)bytes[cursor++])) {
                return 0;
            }
            ++name_length;
        }
        if (name_length == 0 || cursor == length) {
            return 0;
        }
        ++cursor;
        while (cursor < length && bytes[cursor] != '\r') {
            if (!http_header_value_byte((unsigned char)bytes[cursor++])) {
                return 0;
            }
        }
        if (cursor + 1 >= length || bytes[cursor + 1] != '\n') {
            return 0;
        }
        cursor += 2;
        ++request->header_count;
    }
    return 0;
}
