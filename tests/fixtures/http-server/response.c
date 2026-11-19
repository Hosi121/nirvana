#include "http_server.h"

#include <stdio.h>

int http_status_is_error(uint32_t status) {
    return status >= 400u && status < 600u;
}

const char *http_reason_phrase(unsigned status) {
    switch (status) {
        case 200u: return "OK";
        case 400u: return "Bad Request";
        case 404u: return "Not Found";
        case 405u: return "Method Not Allowed";
        default: return "Internal Server Error";
    }
}

void http_health_handler(const struct http_request *request,
                         struct http_response *response) {
    (void)request;
    response->status = 200u;
    response->content_type = "text/plain";
    response->body = "ok\n";
    response->body_length = 3u;
}

void http_metrics_handler(const struct http_request *request,
                          struct http_response *response) {
    (void)request;
    response->status = 200u;
    response->content_type = "text/plain; version=0.0.4";
    response->body = "requests_total 1\n";
    response->body_length = 17u;
}

void http_error_response(unsigned status, struct http_response *response) {
    response->status = status;
    response->content_type = "text/plain";
    if (status == 404u) {
        response->body = "not found\n";
        response->body_length = 10u;
    } else if (status == 405u) {
        response->body = "method not allowed\n";
        response->body_length = 19u;
    } else {
        response->status = 400u;
        response->body = "bad request\n";
        response->body_length = 12u;
    }
}

static int append_text(char *output, size_t capacity, size_t *length,
                       const char *text) {
    while (*text != '\0') {
        if (*length == capacity) {
            return 0;
        }
        output[(*length)++] = *text++;
    }
    return 1;
}

static int append_decimal(char *output, size_t capacity, size_t *length,
                          size_t value) {
    char digits[3u * sizeof(size_t)];
    size_t count = 0;
    do {
        digits[count++] = (char)('0' + value % 10u);
        value /= 10u;
    } while (value != 0);
    if (count > capacity - *length) {
        return 0;
    }
    while (count != 0) {
        output[(*length)++] = digits[--count];
    }
    return 1;
}

size_t http_render_response(const struct http_response *response,
                            char *output, size_t capacity) {
    size_t length = 0;
    size_t i;
    if (!append_text(output, capacity, &length, "HTTP/1.1 ") ||
        !append_decimal(output, capacity, &length, response->status) ||
        !append_text(output, capacity, &length, " ") ||
        !append_text(output, capacity, &length, http_reason_phrase(response->status)) ||
        !append_text(output, capacity, &length, "\r\nContent-Type: ") ||
        !append_text(output, capacity, &length, response->content_type) ||
        !append_text(output, capacity, &length, "\r\nContent-Length: ") ||
        !append_decimal(output, capacity, &length, response->body_length) ||
        !append_text(output, capacity, &length, "\r\nConnection: close\r\n\r\n") ||
        response->body_length > capacity - length) {
        return 0;
    }
    for (i = 0; i < response->body_length; ++i) {
        output[length++] = response->body[i];
    }
    return length;
}

/* Selectable puts-only leaf; not called during the native port announcement. */
int http_server_banner(void) {
    return puts("nirvana modular HTTP fixture");
}
