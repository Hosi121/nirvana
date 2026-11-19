//! Standalone ABI harness: deliberately independent of lifting and C emission.
//! Real network I/O uses an ephemeral loopback listener and bounded waits only.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "nirvana-module-posix-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn linux_posix_bridge_obeys_checked_guest_abi_at_o0_and_o2() {
    let scratch = Scratch::new();
    let source = scratch.0.join("posix.c");
    std::fs::write(
        &source,
        [PRELUDE, include_str!("../src/module_emit/posix.h"), HARNESS].concat(),
    )
    .unwrap();
    for optimization in ["-O0", "-O2"] {
        let executable = scratch.0.join(optimization);
        let compiled = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                optimization,
            ])
            .arg(&source)
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "C compilation {optimization}: {}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let mut child = Command::new(&executable)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        let timed_out = loop {
            if child.try_wait().unwrap().is_some() {
                break false;
            }
            if Instant::now() >= deadline {
                let _ = child.kill();
                break true;
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        let output = child.wait_with_output().unwrap();
        assert!(!timed_out, "bounded C POSIX harness timed out");
        assert!(
            output.status.success(),
            "C harness {optimization}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "guest puts\nposix ABI and bounded loopback checks passed\n"
        );
    }
}

const PRELUDE: &str = r#"#define _POSIX_C_SOURCE 200809L
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

struct nv_module {
    uint64_t r[80];
    uint8_t *memory;
    uint64_t base, size, pc, errno_address, instructions_left, imports_left, started;
    unsigned status;
    uint64_t fault_address, fault_width;
    unsigned fault_access;
    jmp_buf jump;
};

static inline uint64_t nv_check(struct nv_module *s, uint64_t address,
                                uint64_t width, unsigned access) {
    if (address < s->base || width > s->size ||
        address - s->base > s->size - width) {
        s->status = 1;
        s->fault_address = address;
        s->fault_width = width;
        s->fault_access = access;
        longjmp(s->jump, 1);
    }
    return address - s->base;
}

static inline uint64_t nv_read(struct nv_module *s, uint64_t address,
                               unsigned width) {
    uint64_t offset = nv_check(s, address, width, 1), result = 0;
    unsigned i;
    for (i = 0; i < width; ++i) result |= (uint64_t)s->memory[offset + i] << (8 * i);
    return result;
}

static inline void nv_write(struct nv_module *s, uint64_t address,
                            unsigned width, uint64_t value) {
    uint64_t offset = nv_check(s, address, width, 2);
    unsigned i;
    for (i = 0; i < width; ++i) s->memory[offset + i] = (uint8_t)(value >> (8 * i));
}

/* Count only adapter host calls. A checked fault must happen before these.
 * Declarations are already included, so macros cannot rewrite libc headers. */
static unsigned host_calls;
static int counted_socket(int domain, int type, int protocol) {
    ++host_calls;
    return socket(domain, type, protocol);
}
static int counted_bind(int fd, const struct sockaddr *address, socklen_t length) {
    ++host_calls;
    return bind(fd, address, length);
}
static int counted_getsockname(int fd, struct sockaddr *address, socklen_t *length) {
    ++host_calls;
    return getsockname(fd, address, length);
}
static int counted_accept(int fd, struct sockaddr *address, socklen_t *length) {
    ++host_calls;
    return accept(fd, address, length);
}
static int counted_setsockopt(int fd, int level, int option, const void *value,
                              socklen_t length) {
    ++host_calls;
    return setsockopt(fd, level, option, value, length);
}
static int counted_poll(struct pollfd *fds, nfds_t count, int timeout) {
    ++host_calls;
    return poll(fds, count, timeout);
}
static ssize_t counted_recv(int fd, void *buffer, size_t length, int flags) {
    ++host_calls;
    return recv(fd, buffer, length, flags);
}
static ssize_t counted_write(int fd, const void *buffer, size_t length) {
    ++host_calls;
    return write(fd, buffer, length);
}
#define socket counted_socket
#define bind counted_bind
#define getsockname counted_getsockname
#define accept counted_accept
#define setsockopt counted_setsockopt
#define poll counted_poll
#define recv counted_recv
#define write counted_write
"#;

const HARNESS: &str = r#"
#undef socket
#undef bind
#undef getsockname
#undef accept
#undef setsockopt
#undef poll
#undef recv
#undef write

static struct nv_module state;
static uint8_t ram[65536];
static unsigned fault_calls;
static volatile sig_atomic_t alarm_seen;

#define BASE UINT64_C(0x100000)
#define ADDRESS (BASE + 64)
#define LENGTH (BASE + 256)
#define POLL (BASE + 320)
#define TIMEOUT (BASE + 384)
#define BUFFER (BASE + 1024)
#define CHECK(expression) do { \
    if (!(expression)) { \
        fprintf(stderr, "line %d: %s (rax=%llu errno=%llu status=%u)\n", \
                __LINE__, #expression, (unsigned long long)state.r[0], \
                (unsigned long long)nv_read(&state, state.errno_address, 4), \
                state.status); \
        result = 1; goto cleanup; \
    } \
} while (0)

static void arguments(uint64_t a0, uint64_t a1, uint64_t a2,
                      uint64_t a3, uint64_t a4) {
    state.r[7] = a0; state.r[6] = a1; state.r[2] = a2;
    state.r[1] = a3; state.r[8] = a4; state.r[9] = UINT64_C(0xbadcafe);
    state.status = 0;
}

static unsigned invoke(const char *name, uint64_t a0, uint64_t a1, uint64_t a2,
                       uint64_t a3, uint64_t a4) {
    arguments(a0, a1, a2, a3, a4);
    return nv_posix_call(&state, name);
}

static int faults_before_host(const char *name, uint64_t a0, uint64_t a1,
                              uint64_t a2, uint64_t a3, uint64_t a4,
                              uint64_t address, uint64_t width,
                              unsigned access) {
    arguments(a0, a1, a2, a3, a4);
    fault_calls = host_calls;
    if (!setjmp(state.jump)) {
        (void)nv_posix_call(&state, name);
        return 0;
    }
    return state.status == 1 && state.fault_address == address &&
           state.fault_width == width && state.fault_access == access &&
           host_calls == fault_calls;
}

static void on_alarm(int number) {
    (void)number;
    alarm_seen = 1;
}

static int arm_alarm(void) {
    struct itimerval timer;
    memset(&timer, 0, sizeof(timer));
    timer.it_value.tv_usec = 50000;
    alarm_seen = 0;
    return setitimer(ITIMER_REAL, &timer, NULL);
}

int main(void) {
    int result = 0, listener = -1, client = -1, accepted = -1, accepted2 = -1;
    int pipes[2] = {-1, -1}, signaled = 0;
    uint64_t saved[80];
    unsigned i, before;
    struct sockaddr_in local, peer;
    struct sigaction action, old_action;
    struct itimerval stopped;
    struct timeval native_timeout = {1, 0};
    struct pollfd oracle_poll;
    socklen_t native_length;
    uint32_t payload = UINT32_C(0x12345678);
    int native_result, native_errno_result;
    char host_buffer[8192];
    ssize_t count;

    memset(&state, 0, sizeof(state));
    state.memory = ram; state.base = BASE; state.size = sizeof(ram);
    state.errno_address = BASE + sizeof(ram) - 8;
    nv_write(&state, state.errno_address, 4, EDOM);
    nv_write(&state, state.errno_address + 4, 4, UINT32_C(0xaabbccdd));
    for (i = 0; i < 80; ++i) state.r[i] = UINT64_C(0x1234000000000000) + i;
    memcpy(saved, state.r, sizeof(saved));
    errno = 0;
    CHECK(nv_posix_call(&state, "__errno_location") == 1);
    CHECK(state.r[0] == state.errno_address);
    CHECK(nv_read(&state, state.errno_address, 4) == EDOM && errno == EDOM);
    for (i = 1; i < 80; ++i) {
        int clobbered = i == 1 || i == 2 || i == 6 || i == 7 ||
            (i >= 8 && i <= 11) || (i >= 16 && i <= 20) || (i >= 32 && i <= 63);
        CHECK(state.r[i] == (clobbered ? 0 : saved[i]));
    }
    CHECK(invoke("htons", UINT64_C(0xffff00001234), 0, 0, 0, 0));
    CHECK(state.r[0] == 0x3412);
    CHECK(invoke("ntohs", 0x3412, 0, 0, 0, 0) && state.r[0] == 0x1234);
    CHECK(invoke("htonl", UINT64_C(0xabcd000012345678), 0, 0, 0, 0));
    CHECK(state.r[0] == UINT64_C(0x78563412));
    CHECK(invoke("ntohl", UINT64_C(0x78563412), 0, 0, 0, 0));
    CHECK(state.r[0] == UINT64_C(0x12345678));
    CHECK(nv_read(&state, state.errno_address, 4) == EDOM);
    CHECK(nv_read(&state, state.errno_address + 4, 4) == UINT32_C(0xaabbccdd));
    before = host_calls;
    CHECK(!invoke("system", 0, 0, 0, 0, 0) && state.status == 3);
    CHECK(!invoke("setsockopt", -1, SOL_SOCKET, SO_REUSEADDR, BUFFER, 4));
    CHECK(state.status == 3 && host_calls == before);
    CHECK(!invoke("poll", 0, NV_POSIX_MAX_POLL_FDS + 1, 0, 0, 0));
    CHECK(state.status == 3 && host_calls == before);
    CHECK(!invoke("recv", -1, BUFFER, UINT64_MAX, 0, 0));
    CHECK(state.status == 3 && host_calls == before);

    CHECK(faults_before_host("recv", -1, BASE + sizeof(ram), 1, 0, 0,
                            BASE + sizeof(ram), 1, 2));
    CHECK(faults_before_host("write", -1, BASE - 1, 0, 0, 0,
                            BASE - 1, 0, 1));
    CHECK(faults_before_host("poll", BASE + sizeof(ram) - 7, 1, 0, 0, 0,
                            BASE + sizeof(ram) - 7, 8, 1));
    CHECK(faults_before_host("setsockopt", -1, SOL_SOCKET, SO_RCVTIMEO,
                            BASE + sizeof(ram) - 8, 16,
                            BASE + sizeof(ram) - 8, 16, 1));
    CHECK(faults_before_host("bind", -1, BASE + sizeof(ram) - 8, 16, 0, 0,
                            BASE + sizeof(ram) - 8, 16, 1));
    nv_write(&state, LENGTH, 4, 16);
    CHECK(faults_before_host("getsockname", -1, BASE + sizeof(ram) - 8,
                            LENGTH, 0, 0, BASE + sizeof(ram) - 8, 16, 2));
    CHECK(faults_before_host("accept", -1, BASE + sizeof(ram) - 8,
                            LENGTH, 0, 0, BASE + sizeof(ram) - 8, 16, 2));
    ram[sizeof(ram) - 1] = 'x';
    CHECK(faults_before_host("puts", BASE + sizeof(ram) - 1, 0, 0, 0, 0,
                            BASE + sizeof(ram), 1, 1));
    CHECK(invoke("poll", 0, 0, 0, 0, 0) && state.r[0] == 0);
    CHECK(invoke("poll", BASE + sizeof(ram), 0, 0, 0, 0) && state.r[0] == 0);
    CHECK(invoke("close", UINT64_MAX, 0, 0, 0, 0));
    CHECK(state.r[0] == UINT32_MAX && nv_read(&state, state.errno_address, 4) == EBADF);
    CHECK(invoke("recv", UINT64_MAX, 0, 0, 0, 0));
    CHECK(state.r[0] == UINT64_MAX && nv_read(&state, state.errno_address, 4) == EBADF);
    CHECK(invoke("write", UINT64_MAX, 0, 0, 0, 0));
    CHECK(state.r[0] == UINT64_MAX && nv_read(&state, state.errno_address, 4) == EBADF);
    CHECK(invoke("accept", UINT64_MAX, 0, UINT64_MAX, 0, 0));
    CHECK(state.r[0] == UINT32_MAX && nv_read(&state, state.errno_address, 4) == EBADF);

    /* Fill a nonblocking pipe, drain one PIPE_BUF, then force a short write. */
    CHECK(pipe(pipes) == 0);
    CHECK(fcntl(pipes[1], F_SETFL, O_NONBLOCK) == 0);
    memset(host_buffer, 'p', sizeof(host_buffer));
    for (i = 0; i < 128; ++i) {
        count = write(pipes[1], host_buffer, 4096);
        if (count < 0) break;
        CHECK(count == 4096);
    }
    CHECK(i > 0 && i < 128 && errno == EAGAIN);
    CHECK(read(pipes[0], host_buffer, 4096) == 4096);
    memset(ram + (BUFFER - BASE), 'p', 8192);
    CHECK(invoke("write", pipes[1], BUFFER, 8192, 0, 0));
    CHECK(state.r[0] == 4096);
    CHECK(invoke("write", pipes[1], 0, 0, 0, 0) && state.r[0] == 0);
    CHECK(invoke("write", pipes[1], BASE + sizeof(ram), 0, 0, 0) && state.r[0] == 0);
    close(pipes[0]); pipes[0] = -1;
    close(pipes[1]); pipes[1] = -1;

    /* The adapter's socket/bind/getsockname/listen paths create no fixed port. */
    CHECK(invoke("socket", AF_INET, SOCK_STREAM, 0, 0, 0));
    listener = (int32_t)state.r[0];
    CHECK(listener >= 0);
    memset(&local, 0, sizeof(local));
    local.sin_family = AF_INET; local.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    memcpy(ram + (ADDRESS - BASE), &local, sizeof(local));
    CHECK(invoke("bind", listener, ADDRESS, sizeof(local), 0, 0) && state.r[0] == 0);
    nv_write(&state, LENGTH, 4, sizeof(local));
    CHECK(invoke("getsockname", listener, ADDRESS, LENGTH, 0, 0) && state.r[0] == 0);
    CHECK(nv_read(&state, LENGTH, 4) == sizeof(local));
    memcpy(&local, ram + (ADDRESS - BASE), sizeof(local));
    CHECK(local.sin_addr.s_addr == htonl(INADDR_LOOPBACK) && local.sin_port != 0);
    CHECK(invoke("listen", listener, 2, 0, 0, 0) && state.r[0] == 0);

    /* Truncated and aliased sockaddr output follows byte-copy then len-copy. */
    memset(ram + (ADDRESS - BASE), 0xa5, 32);
    nv_write(&state, LENGTH, 4, 3);
    CHECK(invoke("getsockname", listener, ADDRESS, LENGTH, 0, 0) && state.r[0] == 0);
    CHECK(nv_read(&state, LENGTH, 4) == sizeof(local));
    CHECK(memcmp(ram + (ADDRESS - BASE), &local, 3) == 0);
    CHECK(ram[ADDRESS - BASE + 3] == 0xa5);
    nv_write(&state, ADDRESS + 4, 4, sizeof(local));
    CHECK(invoke("getsockname", listener, ADDRESS, ADDRESS + 4, 0, 0));
    CHECK(state.r[0] == 0 && nv_read(&state, ADDRESS + 4, 4) == sizeof(local));
    CHECK(memcmp(ram + (ADDRESS - BASE), &local, 4) == 0);
    nv_write(&state, LENGTH, 4, 0);
    CHECK(invoke("getsockname", listener, 0, LENGTH, 0, 0) && state.r[0] == 0);
    CHECK(nv_read(&state, LENGTH, 4) == sizeof(local));
    nv_write(&state, LENGTH, 4, 129);
    before = host_calls;
    CHECK(!invoke("getsockname", listener, ADDRESS, LENGTH, 0, 0));
    CHECK(state.status == 3 && host_calls == before);

    client = socket(AF_INET, SOCK_STREAM, 0);
    CHECK(client >= 0);
    CHECK(setsockopt(client, SOL_SOCKET, SO_RCVTIMEO, &native_timeout, sizeof(native_timeout)) == 0);
    CHECK(connect(client, (const struct sockaddr *)&local, sizeof(local)) == 0);
    nv_write(&state, POLL, 4, (uint32_t)listener);
    nv_write(&state, POLL + 4, 2, POLLIN);
    nv_write(&state, POLL + 6, 2, 0x7777);
    CHECK(invoke("poll", POLL, 1, 1000, 0, 0) && state.r[0] == 1);
    CHECK(nv_read(&state, POLL + 6, 2) & POLLIN);
    CHECK(nv_read(&state, POLL, 4) == (uint32_t)listener);
    CHECK(nv_read(&state, POLL + 4, 2) == POLLIN);
    CHECK(invoke("accept", listener, 0, UINT64_MAX, 0, 0));
    accepted = (int32_t)state.r[0];
    CHECK(accepted >= 0);
    nv_write(&state, TIMEOUT, 8, 0);
    nv_write(&state, TIMEOUT + 8, 8, 200000);
    CHECK(invoke("setsockopt", accepted, SOL_SOCKET, SO_RCVTIMEO, TIMEOUT, 16));
    CHECK(state.r[0] == 0);
    CHECK(invoke("setsockopt", accepted, SOL_SOCKET, SO_SNDTIMEO, TIMEOUT, 16));
    CHECK(state.r[0] == 0);
    native_length = sizeof(native_timeout);
    CHECK(getsockopt(accepted, SOL_SOCKET, SO_RCVTIMEO, &native_timeout, &native_length) == 0);
    CHECK(native_timeout.tv_sec == 0 && native_timeout.tv_usec >= 200000);
    nv_write(&state, TIMEOUT + 8, 8, UINT64_MAX);
    CHECK(invoke("setsockopt", accepted, SOL_SOCKET, SO_RCVTIMEO, TIMEOUT, 16));
    CHECK(state.r[0] == UINT32_MAX && nv_read(&state, state.errno_address, 4) == EDOM);
    nv_write(&state, TIMEOUT + 8, 8, 200000);

    /* Independent native oracle: errno itself is a valid recv output buffer.
     * A successful libc syscall leaves the received errno bytes in place. */
    CHECK(write(client, &payload, sizeof(payload)) == (ssize_t)sizeof(payload));
    errno = EDOM;
    count = recv(accepted, &errno, sizeof(errno), MSG_WAITALL);
    native_errno_result = errno;
    CHECK(count == (ssize_t)sizeof(errno) && native_errno_result == (int)payload);
    CHECK(write(client, &payload, sizeof(payload)) == (ssize_t)sizeof(payload));
    nv_write(&state, state.errno_address, 4, EDOM);
    CHECK(invoke("recv", accepted, state.errno_address, sizeof(errno), MSG_WAITALL, 0));
    CHECK(state.r[0] == sizeof(errno));
    CHECK(nv_read(&state, state.errno_address, 4) == (uint32_t)native_errno_result);
    CHECK(invoke("__errno_location", 0, 0, 0, 0, 0));
    CHECK(state.r[0] == state.errno_address);
    CHECK(invoke("htonl", 0x80, 0, 0, 0, 0) && state.r[0] == UINT32_C(0x80000000));
    CHECK(nv_read(&state, state.errno_address, 4) == (uint32_t)native_errno_result);

    /* Partial overlap preserves the part of errno not written by recv. */
    CHECK(write(client, &payload, 2) == 2);
    errno = 0x43210000;
    count = recv(accepted, &errno, 2, MSG_WAITALL);
    native_errno_result = errno;
    CHECK(count == 2 && native_errno_result == 0x43215678);
    CHECK(write(client, &payload, 2) == 2);
    nv_write(&state, state.errno_address, 4, 0x43210000);
    CHECK(invoke("recv", accepted, state.errno_address, 2, MSG_WAITALL, 0));
    CHECK(state.r[0] == 2);
    CHECK(nv_read(&state, state.errno_address, 4) == (uint32_t)native_errno_result);
    errno = EDOM;
    count = recv(-1, &errno, sizeof(errno), 0);
    native_errno_result = errno;
    CHECK(count == -1 && native_errno_result == EBADF);
    nv_write(&state, state.errno_address, 4, EDOM);
    CHECK(invoke("recv", UINT64_MAX, state.errno_address, sizeof(errno), 0, 0));
    CHECK(state.r[0] == UINT64_MAX);
    CHECK(nv_read(&state, state.errno_address, 4) == (uint32_t)native_errno_result);

    /* Native sockaddr bytes can overwrite errno too; four bytes fit the
     * actual native errno object, without touching neighboring TLS state. */
    native_length = sizeof(errno);
    errno = EDOM;
    native_result = getsockname(listener, (struct sockaddr *)&errno, &native_length);
    native_errno_result = errno;
    CHECK(native_result == 0 && native_length == sizeof(local));
    nv_write(&state, LENGTH, 4, sizeof(errno));
    nv_write(&state, state.errno_address, 4, EDOM);
    CHECK(invoke("getsockname", listener, state.errno_address, LENGTH, 0, 0));
    CHECK(state.r[0] == 0 && nv_read(&state, LENGTH, 4) == sizeof(local));
    CHECK(nv_read(&state, state.errno_address, 4) == (uint32_t)native_errno_result);
    /* socklen_t is Linux unsigned int, the corresponding alias-safe type. */
    errno = 3;
    native_result = getsockname(listener, (struct sockaddr *)&peer, (socklen_t *)&errno);
    native_errno_result = errno;
    CHECK(native_result == 0 && native_errno_result == (int)sizeof(local));
    nv_write(&state, state.errno_address, 4, 3);
    CHECK(invoke("getsockname", listener, ADDRESS, state.errno_address, 0, 0));
    CHECK(state.r[0] == 0 && nv_read(&state, state.errno_address, 4) == (uint32_t)native_errno_result);
    CHECK(memcmp(ram + (ADDRESS - BASE), &peer, 3) == 0);

    /* Real native poll gives the output oracle. Place guest revents over
     * errno's low half, preserving its high half on successful copyout. */
    oracle_poll.fd = -1; oracle_poll.events = POLLIN; oracle_poll.revents = 0x1234;
    CHECK(poll(&oracle_poll, 1, 0) == 0 && oracle_poll.revents == 0);
    nv_write(&state, state.errno_address - 6, 4, UINT32_MAX);
    nv_write(&state, state.errno_address - 2, 2, POLLIN);
    nv_write(&state, state.errno_address, 4, 0x77771234);
    CHECK(invoke("poll", state.errno_address - 6, 1, 0, 0, 0) && state.r[0] == 0);
    CHECK(nv_read(&state, state.errno_address, 4) ==
          (UINT32_C(0x77770000) | (uint16_t)oracle_poll.revents));

    memset(&action, 0, sizeof(action));
    action.sa_handler = on_alarm;
    CHECK(sigemptyset(&action.sa_mask) == 0);
    CHECK(sigaction(SIGALRM, &action, &old_action) == 0);
    signaled = 1;
    CHECK(arm_alarm() == 0);
    nv_write(&state, state.errno_address, 4, 0x77771234);
    CHECK(invoke("poll", state.errno_address - 6, 1, 1000, 0, 0));
    CHECK(alarm_seen && state.r[0] == UINT32_MAX);
    CHECK(nv_read(&state, state.errno_address, 4) == EINTR);
    CHECK(arm_alarm() == 0);
    CHECK(invoke("recv", accepted, BUFFER, 16, 0, 0));
    CHECK(alarm_seen && state.r[0] == UINT64_MAX);
    CHECK(nv_read(&state, state.errno_address, 4) == EINTR);
    CHECK(invoke("recv", accepted, BUFFER, 16, MSG_DONTWAIT, 0));
    CHECK(state.r[0] == UINT64_MAX && nv_read(&state, state.errno_address, 4) == EAGAIN);

    CHECK(write(client, "abc", 3) == 3);
    ram[BUFFER - BASE + 3] = 0xa5;
    CHECK(invoke("recv", accepted, BUFFER, 16, 0, 0) && state.r[0] == 3);
    CHECK(memcmp(ram + (BUFFER - BASE), "abc", 3) == 0);
    CHECK(ram[BUFFER - BASE + 3] == 0xa5);
    CHECK(invoke("recv", accepted, 0, 0, MSG_DONTWAIT, 0));
    /* Linux recv(connected, NULL, 0, MSG_DONTWAIT) can report EAGAIN when empty. */
    CHECK(state.r[0] == 0 || (state.r[0] == UINT64_MAX &&
          nv_read(&state, state.errno_address, 4) == EAGAIN));
    memcpy(ram + (BUFFER - BASE), "reply", 5);
    CHECK(invoke("write", accepted, BUFFER, 5, 0, 0) && state.r[0] == 5);
    CHECK(recv(client, host_buffer, 5, MSG_WAITALL) == 5);
    CHECK(memcmp(host_buffer, "reply", 5) == 0);
    CHECK(invoke("shutdown", accepted, SHUT_WR, 0, 0, 0) && state.r[0] == 0);
    CHECK(recv(client, host_buffer, 1, 0) == 0);
    CHECK(shutdown(client, SHUT_WR) == 0);
    CHECK(invoke("recv", accepted, BUFFER, 16, 0, 0) && state.r[0] == 0);
    CHECK(invoke("recv", accepted, 0, 0, 0, 0) && state.r[0] == 0);
    CHECK(invoke("close", accepted, 0, 0, 0, 0) && state.r[0] == 0);
    accepted = -1;
    close(client); client = -1;

    /* Also marshal a non-NULL accept address and a zero-capacity output. */
    client = socket(AF_INET, SOCK_STREAM, 0);
    CHECK(client >= 0 && connect(client, (const struct sockaddr *)&local, sizeof(local)) == 0);
    nv_write(&state, LENGTH, 4, sizeof(peer));
    CHECK(invoke("accept", listener, ADDRESS, LENGTH, 0, 0));
    accepted2 = (int32_t)state.r[0];
    CHECK(accepted2 >= 0 && nv_read(&state, LENGTH, 4) == sizeof(peer));
    memcpy(&peer, ram + (ADDRESS - BASE), sizeof(peer));
    CHECK(peer.sin_family == AF_INET && peer.sin_addr.s_addr == htonl(INADDR_LOOPBACK));
    CHECK(invoke("close", accepted2, 0, 0, 0, 0) && state.r[0] == 0);
    accepted2 = -1;
    close(client); client = -1;
    client = socket(AF_INET, SOCK_STREAM, 0);
    CHECK(client >= 0 && connect(client, (const struct sockaddr *)&local, sizeof(local)) == 0);
    nv_write(&state, LENGTH, 4, 0);
    ram[ADDRESS - BASE] = 0xa5;
    CHECK(invoke("accept", listener, ADDRESS, LENGTH, 0, 0));
    accepted2 = (int32_t)state.r[0];
    CHECK(accepted2 >= 0 && nv_read(&state, LENGTH, 4) == sizeof(peer));
    CHECK(ram[ADDRESS - BASE] == 0xa5);
    CHECK(invoke("close", accepted2, 0, 0, 0, 0) && state.r[0] == 0);
    accepted2 = -1;
    close(client); client = -1;
    CHECK(invoke("close", listener, 0, 0, 0, 0) && state.r[0] == 0);
    listener = -1;
    memcpy(ram + (BUFFER - BASE), "guest puts", 11);
    CHECK(invoke("puts", BUFFER, 0, 0, 0, 0) && (int32_t)state.r[0] >= 0);
    puts("posix ABI and bounded loopback checks passed");

cleanup:
    memset(&stopped, 0, sizeof(stopped));
    (void)setitimer(ITIMER_REAL, &stopped, NULL);
    if (signaled) (void)sigaction(SIGALRM, &old_action, NULL);
    if (accepted2 >= 0) close(accepted2);
    if (accepted >= 0) close(accepted);
    if (client >= 0) close(client);
    if (listener >= 0) close(listener);
    if (pipes[0] >= 0) close(pipes[0]);
    if (pipes[1] >= 0) close(pipes[1]);
    return result;
}
"#;
