/* Linux x86-64 POSIX bridge for checked, byte-addressed guest RAM.
 * Emit _POSIX_C_SOURCE=200809L before ANY headers in the containing C file.
 * This implements a valid-buffer model: bad guest ranges are checked faults,
 * not an attempt to reproduce native EFAULT or partially completed I/O.
 */
#include <arpa/inet.h>
#include <errno.h>
#include <limits.h>
#include <poll.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "nv_posix_call requires the Linux x86-64 ABI"
#endif

_Static_assert(sizeof(int) == 4 && sizeof(long) == 8, "Linux integer ABI");
_Static_assert(sizeof(ssize_t) == 8 && sizeof(socklen_t) == 4, "Linux socket ABI");
_Static_assert(sizeof(struct pollfd) == 8 && offsetof(struct pollfd, events) == 4 &&
               offsetof(struct pollfd, revents) == 6, "Linux pollfd ABI");
_Static_assert(sizeof(struct timeval) == 16 &&
               offsetof(struct timeval, tv_usec) == 8, "Linux timeval ABI");
_Static_assert(sizeof(struct sockaddr_storage) == 128, "Linux sockaddr storage");

/* A deliberate adapter resource limit, reported as unsupported, not ENOMEM.
 * The fixture only polls one descriptor. Count arithmetic never wraps. */
#define NV_POSIX_MAX_POLL_FDS UINT64_C(65536)

static inline unsigned nv_posix_unsupported(struct nv_module *s) {
    s->status = 3;
    return 0;
}

static inline uint8_t *nv_posix_bytes(struct nv_module *s, uint64_t address,
                                     uint64_t width, unsigned access) {
    /* NULL is a permitted empty I/O buffer; non-NULL empty ranges must be
     * inside the closed guest interval, as required by nv_check. */
    if (address == 0 && width == 0) return NULL;
    return s->memory + nv_check(s, address, width, access);
}

static inline unsigned nv_posix_finish(struct nv_module *s, uint64_t value,
                                       int saved_errno, unsigned failed) {
    static const unsigned volatile_gp[] = {0, 1, 2, 6, 7, 8, 9, 10, 11};
    size_t i;
    for (i = 0; i < sizeof(volatile_gp) / sizeof(volatile_gp[0]); ++i)
        s->r[volatile_gp[i]] = 0;
    for (i = 16; i <= 20; ++i) s->r[i] = 0;
    for (i = 32; i <= 63; ++i) s->r[i] = 0;
    s->r[0] = value;
    /* Success leaves the guest bytes written by the syscall in place, even
     * when an output buffer aliases errno. Failure copyout order is syscall
     * output bytes, socklen/revents, then errno. Its range was prechecked. */
    if (failed) nv_write(s, s->errno_address, 4, (uint32_t)saved_errno);
    return 1;
}

static inline unsigned nv_posix_call(struct nv_module *s, const char *name) {
    /* SysV function ABI, NOT the syscall ABI: argument four is RCX/r1.
     * Snapshot every argument before any caller-clobbered register changes. */
    const uint64_t a0 = s->r[7], a1 = s->r[6], a2 = s->r[2];
    const uint64_t a3 = s->r[1], a4 = s->r[8], a5 = s->r[9];
    int result, saved_errno, entry_errno;
    (void)a5;
    if (strcmp(name, "socket") && strcmp(name, "bind") &&
        strcmp(name, "getsockname") && strcmp(name, "listen") &&
        strcmp(name, "poll") && strcmp(name, "accept") &&
        strcmp(name, "setsockopt") && strcmp(name, "recv") &&
        strcmp(name, "write") && strcmp(name, "shutdown") &&
        strcmp(name, "close") && strcmp(name, "__errno_location") &&
        strcmp(name, "htons") && strcmp(name, "ntohs") &&
        strcmp(name, "htonl") && strcmp(name, "ntohl") &&
        strcmp(name, "puts"))
        return nv_posix_unsupported(s);

    (void)nv_check(s, s->errno_address, 4, 2);
    entry_errno = (int32_t)(uint32_t)nv_read(s, s->errno_address, 4);
    errno = entry_errno;

    if (!strcmp(name, "__errno_location"))
        return nv_posix_finish(s, s->errno_address, errno, 0);
    if (!strcmp(name, "htons"))
        return nv_posix_finish(s, htons((uint16_t)a0), errno, 0);
    if (!strcmp(name, "ntohs"))
        return nv_posix_finish(s, ntohs((uint16_t)a0), errno, 0);
    if (!strcmp(name, "htonl"))
        return nv_posix_finish(s, htonl((uint32_t)a0), errno, 0);
    if (!strcmp(name, "ntohl"))
        return nv_posix_finish(s, ntohl((uint32_t)a0), errno, 0);

    if (!strcmp(name, "socket")) {
        result = socket((int32_t)a0, (int32_t)a1, (int32_t)a2);
    } else if (!strcmp(name, "listen")) {
        result = listen((int32_t)a0, (int32_t)a1);
    } else if (!strcmp(name, "shutdown")) {
        result = shutdown((int32_t)a0, (int32_t)a1);
    } else if (!strcmp(name, "close")) {
        result = close((int32_t)a0);
    } else if (!strcmp(name, "bind")) {
        struct sockaddr_storage address;
        const uint32_t length = (uint32_t)a2;
        const uint8_t *source;
        /* socklen_t is 32 bits even though the argument register is 64. */
        if (length > sizeof(address)) return nv_posix_unsupported(s);
        source = nv_posix_bytes(s, a1, length, 1);
        memset(&address, 0, sizeof(address));
        if (length) memcpy(&address, source, length);
        result = bind((int32_t)a0,
                      a1 ? (const struct sockaddr *)&address : NULL, length);
    } else if (!strcmp(name, "getsockname") || !strcmp(name, "accept")) {
        struct sockaddr_storage address;
        const int accepting = !strcmp(name, "accept");
        uint32_t capacity;
        socklen_t length;
        uint8_t *destination;
        size_t copied;
        /* Linux ignores the length pointer completely for accept(fd,NULL,*). */
        if (accepting && a1 == 0) {
            result = accept((int32_t)a0, NULL, NULL);
            saved_errno = errno;
            return nv_posix_finish(s, (uint32_t)result, saved_errno, result < 0);
        }
        (void)nv_check(s, a2, 4, 2);
        capacity = (uint32_t)nv_read(s, a2, 4);
        if (capacity > sizeof(address)) return nv_posix_unsupported(s);
        destination = nv_posix_bytes(s, a1, capacity, 2);
        length = (socklen_t)capacity;
        memset(&address, 0, sizeof(address));
        result = accepting
            ? accept((int32_t)a0, (struct sockaddr *)&address, &length)
            : getsockname((int32_t)a0,
                          a1 ? (struct sockaddr *)&address : NULL, &length);
        saved_errno = errno;
        if (result >= 0) {
            copied = length < capacity ? length : capacity;
            if (copied) memcpy(destination, &address, copied);
            /* Capture capacity before copyout: addr and addrlen may alias. */
            nv_write(s, a2, 4, length);
        }
        return nv_posix_finish(s, (uint32_t)result, saved_errno, result < 0);
    } else if (!strcmp(name, "setsockopt")) {
        struct timeval timeout;
        const uint32_t length = (uint32_t)a4;
        /* Only the fixture's SOL_SOCKET timeval options are supported.
         * Other option payloads require an explicit ABI marshal extension. */
        if ((int32_t)a1 != SOL_SOCKET ||
            ((int32_t)a2 != SO_RCVTIMEO && (int32_t)a2 != SO_SNDTIMEO) ||
            length != 16)
            return nv_posix_unsupported(s);
        (void)nv_check(s, a3, length, 1);
        timeout.tv_sec = (int64_t)nv_read(s, a3, 8);
        timeout.tv_usec = (int64_t)nv_read(s, a3 + 8, 8);
        result = setsockopt((int32_t)a0, (int32_t)a1, (int32_t)a2,
                            &timeout, sizeof(timeout));
    } else if (!strcmp(name, "poll")) {
        struct pollfd *fds = NULL;
        uint64_t i;
        if (a1 > NV_POSIX_MAX_POLL_FDS) return nv_posix_unsupported(s);
        (void)nv_posix_bytes(s, a0, a1 * 8, 1);
        (void)nv_posix_bytes(s, a0, a1 * 8, 2);
        if (a1) {
            fds = (struct pollfd *)malloc((size_t)a1 * sizeof(*fds));
            if (!fds) return nv_posix_finish(s, UINT32_MAX, ENOMEM, 1);
            for (i = 0; i < a1; ++i) {
                fds[i].fd = (int32_t)(uint32_t)nv_read(s, a0 + i * 8, 4);
                fds[i].events = (int16_t)(uint16_t)nv_read(s, a0 + i * 8 + 4, 2);
                fds[i].revents = (int16_t)(uint16_t)nv_read(s, a0 + i * 8 + 6, 2);
            }
        }
        /* Internal allocation must not change errno seen by a successful
         * poll, which itself normally leaves errno unchanged. */
        errno = entry_errno;
        result = poll(fds, (nfds_t)a1, (int32_t)a2);
        saved_errno = errno;
        for (i = 0; i < a1; ++i)
            nv_write(s, a0 + i * 8 + 6, 2, (uint16_t)fds[i].revents);
        free(fds);
        return nv_posix_finish(s, (uint32_t)result, saved_errno, result < 0);
    } else if (!strcmp(name, "recv") || !strcmp(name, "write")) {
        const int receiving = !strcmp(name, "recv");
        uint8_t *buffer;
        ssize_t count;
        if (a2 > (uint64_t)SSIZE_MAX) return nv_posix_unsupported(s);
        buffer = nv_posix_bytes(s, a1, a2, receiving ? 2 : 1);
        count = receiving
            ? recv((int32_t)a0, buffer, (size_t)a2, (int32_t)a3)
            : write((int32_t)a0, buffer, (size_t)a2);
        saved_errno = errno;
        return nv_posix_finish(s, (uint64_t)(int64_t)count, saved_errno, count < 0);
    } else { /* puts: the whitelist above makes this branch exhaustive. */
        const uint64_t offset = nv_check(s, a0, 1, 1);
        const size_t available = (size_t)(s->size - offset);
        const char *string = (const char *)(s->memory + offset);
        if (!memchr(string, 0, available)) {
            (void)nv_check(s, a0 + available, 1, 1);
            return nv_posix_unsupported(s); /* unreachable after checked fault */
        }
        result = puts(string);
    }
    saved_errno = errno;
    /* C functions returning int write EAX, zero extending the upper half. */
    return nv_posix_finish(s, (uint32_t)result, saved_errno, result < 0);
}
