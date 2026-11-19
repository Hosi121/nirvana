#ifndef NIRVANA_HTTP_SERVER_H
#define NIRVANA_HTTP_SERVER_H

#include <stddef.h>
#include <stdint.h>

/* Keep sized, separately selectable function symbols at both optimization levels. */
#if defined(__GNUC__) || defined(__clang__)
#define HTTP_LEAF __attribute__((noinline))
#else
#define HTTP_LEAF
#endif

#define HTTP_REQUEST_CAPACITY 1024u
#define HTTP_PATH_CAPACITY 128u
#define HTTP_RESPONSE_CAPACITY 2048u

struct http_request {
    char method[8];
    char path[HTTP_PATH_CAPACITY];
    unsigned header_count;
};

struct http_response {
    unsigned status;
    const char *content_type;
    const char *body;
    size_t body_length;
};

typedef void (*http_handler)(const struct http_request *, struct http_response *);

struct http_route {
    const char *path;
    http_handler handler;
};

extern const struct http_route http_routes[2];

HTTP_LEAF int http_header_name_byte(uint32_t byte);
HTTP_LEAF int http_header_value_byte(uint32_t byte);
HTTP_LEAF int http_request_complete(const char *bytes, size_t length);
HTTP_LEAF int http_parse_request(const char *bytes, size_t length,
                                 struct http_request *request);
HTTP_LEAF int http_path_equal(const char *left, const char *right);
HTTP_LEAF void http_dispatch(const struct http_request *request,
                             struct http_response *response);
HTTP_LEAF void http_health_handler(const struct http_request *request,
                                   struct http_response *response);
HTTP_LEAF void http_metrics_handler(const struct http_request *request,
                                    struct http_response *response);
HTTP_LEAF void http_error_response(unsigned status, struct http_response *response);
HTTP_LEAF int http_status_is_error(uint32_t status);
HTTP_LEAF const char *http_reason_phrase(unsigned status);
HTTP_LEAF size_t http_render_response(const struct http_response *response,
                                      char *output, size_t capacity);
HTTP_LEAF int http_server_banner(void);
HTTP_LEAF int http_read_request(int client, char *bytes, size_t capacity,
                                size_t *length);
HTTP_LEAF int http_serve_once(void);

#endif
