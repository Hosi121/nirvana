#define _POSIX_C_SOURCE 200809L
#include "http_server.h"

#include <arpa/inet.h>
#include <errno.h>
#include <poll.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

static int write_all(int descriptor, const char *bytes, size_t length) {
    size_t sent = 0;
    while (sent < length) {
        ssize_t result = write(descriptor, bytes + sent, length - sent);
        if (result < 0 && errno == EINTR) {
            continue;
        }
        if (result <= 0) {
            return 0;
        }
        sent += (size_t)result;
    }
    return 1;
}

static void finish_response(int client) {
    char discarded[256];
    size_t remaining = HTTP_REQUEST_CAPACITY * 8u;
    /* Send FIN, then consume bounded trailing input before close. Unread
       request bytes at close can reset TCP and discard the error response. */
    if (shutdown(client, SHUT_WR) != 0) {
        return;
    }
    while (remaining != 0) {
        size_t capacity = remaining < sizeof(discarded) ? remaining : sizeof(discarded);
        ssize_t received = recv(client, discarded, capacity, 0);
        if (received < 0 && errno == EINTR) {
            continue;
        }
        if (received <= 0) {
            return;
        }
        remaining -= (size_t)received;
    }
}

static int announce_port(unsigned port) {
    char digits[8];
    char line[8];
    size_t count = 0;
    size_t i;
    do {
        digits[count++] = (char)('0' + port % 10u);
        port /= 10u;
    } while (port != 0);
    for (i = 0; i < count; ++i) {
        line[i] = digits[count - i - 1];
    }
    line[count] = '\n';
    return write_all(STDOUT_FILENO, line, count + 1);
}

int http_read_request(int client, char *bytes, size_t capacity, size_t *length) {
    *length = 0;
    while (*length < capacity) {
        ssize_t received = recv(client, bytes + *length, capacity - *length, 0);
        if (received < 0 && errno == EINTR) {
            continue;
        }
        if (received <= 0) {
            return 0;
        }
        *length += (size_t)received;
        if (http_request_complete(bytes, *length)) {
            return 1;
        }
    }
    return 0;
}

int http_serve_once(void) {
    int listener = -1;
    int client = -1;
    int exit_code = 1;
    struct sockaddr_in address = {0};
    socklen_t address_length = sizeof(address);
    struct pollfd ready;
    struct timeval timeout = {3, 0};
    char input[HTTP_REQUEST_CAPACITY];
    char output[HTTP_RESPONSE_CAPACITY];
    struct http_request request;
    struct http_response response;
    size_t input_length;
    size_t output_length;
    listener = socket(AF_INET, SOCK_STREAM, 0);
    if (listener < 0) {
        goto cleanup;
    }
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    address.sin_port = htons(0);
    if (bind(listener, (const struct sockaddr *)&address, sizeof(address)) != 0 ||
        getsockname(listener, (struct sockaddr *)&address, &address_length) != 0 ||
        listen(listener, 1) != 0 || !announce_port(ntohs(address.sin_port))) {
        goto cleanup;
    }
    ready.fd = listener;
    ready.events = POLLIN;
    ready.revents = 0;
    if (poll(&ready, 1, 3000) <= 0) {
        goto cleanup;
    }
    client = accept(listener, NULL, NULL);
    if (client < 0 ||
        setsockopt(client, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(timeout)) != 0 ||
        setsockopt(client, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof(timeout)) != 0) {
        goto cleanup;
    }
    if (http_read_request(client, input, sizeof(input), &input_length) &&
        http_parse_request(input, input_length, &request)) {
        http_dispatch(&request, &response);
    } else {
        http_error_response(400u, &response);
    }
    output_length = http_render_response(&response, output, sizeof(output));
    if (output_length != 0 && write_all(client, output, output_length)) {
        exit_code = 0;
        finish_response(client);
    }
cleanup:
    if (client >= 0) {
        (void)close(client);
    }
    if (listener >= 0) {
        (void)close(listener);
    }
    return exit_code;
}
