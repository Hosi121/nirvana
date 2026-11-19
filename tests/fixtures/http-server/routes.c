#include "http_server.h"

int http_path_equal(const char *left, const char *right) {
    size_t cursor = 0;
    while (left[cursor] != '\0' && left[cursor] == right[cursor]) {
        ++cursor;
    }
    return left[cursor] == right[cursor];
}

void http_dispatch(const struct http_request *request, struct http_response *response) {
    size_t i;
    if (!http_path_equal(request->method, "GET")) {
        http_error_response(405u, response);
        return;
    }
    for (i = 0; i < sizeof(http_routes) / sizeof(http_routes[0]); ++i) {
        if (http_path_equal(request->path, http_routes[i].path)) {
            http_routes[i].handler(request, response);
            return;
        }
    }
    http_error_response(404u, response);
}
