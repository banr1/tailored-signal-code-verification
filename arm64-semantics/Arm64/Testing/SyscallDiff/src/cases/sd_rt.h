// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

/*
 * sd_rt.h: freestanding runtime for the per-behavior SyscallDiff case binaries.
 *
 * Every `src/cases/<name>.c` includes this header, defines `int sd_main(int argc, char **argv)`,
 * and is compiled by `scripts/syscall-diff-cases` into one static `ET_EXEC` AArch64 ELF
 * `bin/<name>.elf` (no libc, no PIE, `-mgeneral-regs-only`).
 *
 * Conventions (checked by `Arm64/Testing/Regression/SyscallDiff.lean`, `syscallCaseTable`):
 *   - `SD_EXPECT(label, got, want)` prints `label=<got>\n` to stdout and records a failure on
 *     stderr when `got != want`. `want` is the Linux 7.3 result (raw syscall return; errors are
 *     `-errno`).
 *   - `SD_SHOW(label, v)` prints `label=<v>\n` without an expectation (only for values that are
 *     deterministic in both runners, e.g. byte contents written by the case itself).
 *   - `sd_main`'s return value is ignored; the process exits via `exit_group(sd_failures ? 1 : 0)`
 *     unless the case calls `sd_exit_group` / `sd_exit` / a signal itself.
 * The harness then compares exit status, signal, stdout and stderr byte-for-byte between
 * `qemu-aarch64` and the Lean model, and also checks the exit status against the table.
 */
#ifndef SD_RT_H
#define SD_RT_H

typedef unsigned long u64;
typedef long i64;
typedef unsigned int u32;
typedef int i32;
typedef unsigned char u8;

/* Syscall numbers (`include/uapi/asm-generic/unistd.h`). */
#define SYS_fcntl 25
#define SYS_ioctl 29
#define SYS_openat 56
#define SYS_close 57
#define SYS_lseek 62
#define SYS_read 63
#define SYS_write 64
#define SYS_readv 65
#define SYS_writev 66
#define SYS_pread64 67
#define SYS_ppoll 73
#define SYS_fstat 80
#define SYS_exit 93
#define SYS_exit_group 94
#define SYS_set_tid_address 96
#define SYS_clock_gettime 113
#define SYS_sched_getaffinity 123
#define SYS_tkill 130
#define SYS_tgkill 131
#define SYS_sigaltstack 132
#define SYS_rt_sigaction 134
#define SYS_rt_sigprocmask 135
#define SYS_getpid 172
#define SYS_gettid 178
#define SYS_brk 214
#define SYS_munmap 215
#define SYS_mremap 216
#define SYS_mmap 222
#define SYS_mprotect 226
#define SYS_madvise 233
#define SYS_getrandom 278

/* errno values (`include/uapi/asm-generic/errno-base.h`). */
#define EPERM 1
#define ENOENT 2
#define ESRCH 3
#define EINTR 4
#define EIO 5
#define EBADF 9
#define EAGAIN 11
#define ENOMEM 12
#define EACCES 13
#define EFAULT 14
#define EEXIST 17
#define ENOTDIR 20
#define EISDIR 21
#define EINVAL 22
#define EMFILE 24
#define ENOTTY 25
#define EFBIG 27
#define ESPIPE 29
#define ERANGE 34
#define ENAMETOOLONG 36
#define ENOSYS 38

/* Flags and constants (AArch64 uapi). */
#define AT_FDCWD (-100)
#define O_RDONLY 0x0
#define O_WRONLY 0x1
#define O_RDWR 0x2
#define O_CREAT 0x40
#define O_EXCL 0x80
#define O_TRUNC 0x200
#define O_APPEND 0x400
#define O_DIRECTORY 0x4000
#define O_CLOEXEC 0x80000
#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2
#define F_GETFD 1
#define F_SETFD 2
#define FD_CLOEXEC 1
#define PROT_NONE 0x0
#define PROT_READ 0x1
#define PROT_WRITE 0x2
#define PROT_EXEC 0x4
#define MAP_SHARED 0x01
#define MAP_PRIVATE 0x02
#define MAP_FIXED 0x10
#define MAP_ANONYMOUS 0x20
#define MAP_FIXED_NOREPLACE 0x100000
#define MREMAP_MAYMOVE 1
#define MREMAP_FIXED 2
#define MADV_NORMAL 0
#define MADV_RANDOM 1
#define MADV_SEQUENTIAL 2
#define MADV_WILLNEED 3
#define MADV_DONTNEED 4
#define MADV_FREE 8
#define CLOCK_REALTIME 0
#define CLOCK_MONOTONIC 1
#define GRND_NONBLOCK 0x1
#define GRND_RANDOM 0x2
#define GRND_INSECURE 0x4
#define SIG_BLOCK 0
#define SIG_UNBLOCK 1
#define SIG_SETMASK 2
#define SIGABRT 6
#define SIGKILL 9
#define SIGUSR1 10
#define SIGSEGV 11
#define SIGTERM 15
#define SIGSTOP 19
#define SS_ONSTACK 1
#define SS_DISABLE 2
#define POLLIN 0x001
#define POLLOUT 0x004
#define POLLNVAL 0x020
#define PAGE 4096UL

struct sd_iovec {
  void *base;
  u64 len;
};
struct sd_timespec {
  i64 sec;
  i64 nsec;
};
struct sd_pollfd {
  i32 fd;
  short events;
  short revents;
};

/* Raw `svc #0` wrappers: x8 = nr, x0..x5 = args, x0 = return. */
static inline i64 sd_sys6(u64 nr, u64 a0, u64 a1, u64 a2, u64 a3, u64 a4, u64 a5) {
  register u64 x8 __asm__("x8") = nr;
  register u64 x0 __asm__("x0") = a0;
  register u64 x1 __asm__("x1") = a1;
  register u64 x2 __asm__("x2") = a2;
  register u64 x3 __asm__("x3") = a3;
  register u64 x4 __asm__("x4") = a4;
  register u64 x5 __asm__("x5") = a5;
  __asm__ volatile("svc #0"
                   : "+r"(x0)
                   : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5)
                   : "memory");
  return (i64)x0;
}
#define sd_sys0(n) sd_sys6((n), 0, 0, 0, 0, 0, 0)
#define sd_sys1(n, a) sd_sys6((n), (u64)(a), 0, 0, 0, 0, 0)
#define sd_sys2(n, a, b) sd_sys6((n), (u64)(a), (u64)(b), 0, 0, 0, 0)
#define sd_sys3(n, a, b, c) sd_sys6((n), (u64)(a), (u64)(b), (u64)(c), 0, 0, 0)
#define sd_sys4(n, a, b, c, d) sd_sys6((n), (u64)(a), (u64)(b), (u64)(c), (u64)(d), 0, 0)
#define sd_sys5(n, a, b, c, d, e) \
  sd_sys6((n), (u64)(a), (u64)(b), (u64)(c), (u64)(d), (u64)(e), 0)
#define sd_sys(n, a, b, c, d, e, f) \
  sd_sys6((n), (u64)(a), (u64)(b), (u64)(c), (u64)(d), (u64)(e), (u64)(f))

static inline i64 sd_write(int fd, const void *p, u64 n) { return sd_sys3(SYS_write, fd, p, n); }
static inline i64 sd_read(int fd, void *p, u64 n) { return sd_sys3(SYS_read, fd, p, n); }
static inline i64 sd_openat(int dfd, const char *path, u64 flags, u64 mode) {
  return sd_sys4(SYS_openat, (i64)dfd, path, flags, mode);
}
static inline i64 sd_close(int fd) { return sd_sys1(SYS_close, (i64)fd); }
static inline i64 sd_lseek(int fd, i64 off, int whence) {
  return sd_sys3(SYS_lseek, (i64)fd, off, whence);
}
static inline i64 sd_mmap(u64 addr, u64 len, u64 prot, u64 flags, i64 fd, u64 off) {
  return sd_sys(SYS_mmap, addr, len, prot, flags, fd, off);
}
static inline i64 sd_munmap(u64 addr, u64 len) { return sd_sys2(SYS_munmap, addr, len); }
static inline i64 sd_brk(u64 addr) { return sd_sys1(SYS_brk, addr); }

__attribute__((noreturn)) static inline void sd_exit_group(int code) {
  sd_sys1(SYS_exit_group, (i64)code);
  __builtin_unreachable();
}
__attribute__((noreturn)) static inline void sd_exit(int code) {
  sd_sys1(SYS_exit, (i64)code);
  __builtin_unreachable();
}

/* Byte helpers (no libc: `-fno-builtin` keeps the compiler from emitting memcpy/memset calls). */
static inline u64 sd_strlen(const char *s) {
  u64 n = 0;
  while (s[n]) n++;
  return n;
}
static inline void sd_memset(void *p, int c, u64 n) {
  volatile u8 *d = (volatile u8 *)p;
  for (u64 i = 0; i < n; i++) d[i] = (u8)c;
}
static inline int sd_memeq(const void *a, const void *b, u64 n) {
  const u8 *x = (const u8 *)a, *y = (const u8 *)b;
  for (u64 i = 0; i < n; i++)
    if (x[i] != y[i]) return 0;
  return 1;
}

/* Output helpers. */
static int sd_failures;

static inline void sd_puts_fd(int fd, const char *s) { sd_write(fd, s, sd_strlen(s)); }
static inline void sd_puts(const char *s) { sd_puts_fd(1, s); }

static inline void sd_put_i64_fd(int fd, i64 v) {
  char buf[24];
  int i = 23;
  u64 u = v < 0 ? (u64)0 - (u64)v : (u64)v;
  buf[i] = 0;
  do {
    buf[--i] = (char)('0' + (u % 10));
    u /= 10;
  } while (u);
  if (v < 0) buf[--i] = '-';
  sd_puts_fd(fd, buf + i);
}

static inline void sd_put_hex_fd(int fd, u64 v) {
  char buf[19];
  buf[0] = '0';
  buf[1] = 'x';
  for (int i = 0; i < 16; i++) {
    int nib = (int)((v >> (60 - 4 * i)) & 0xf);
    buf[2 + i] = (char)(nib < 10 ? '0' + nib : 'a' + nib - 10);
  }
  buf[18] = 0;
  sd_puts_fd(fd, buf);
}

static inline void sd_show(const char *label, i64 v) {
  sd_puts(label);
  sd_puts("=");
  sd_put_i64_fd(1, v);
  sd_puts("\n");
}

static inline void sd_show_hex(const char *label, u64 v) {
  sd_puts(label);
  sd_puts("=");
  sd_put_hex_fd(1, v);
  sd_puts("\n");
}

static inline void sd_expect(const char *label, i64 got, i64 want) {
  sd_show(label, got);
  if (got != want) {
    sd_failures++;
    sd_puts_fd(2, "FAIL ");
    sd_puts_fd(2, label);
    sd_puts_fd(2, ": got ");
    sd_put_i64_fd(2, got);
    sd_puts_fd(2, " want ");
    sd_put_i64_fd(2, want);
    sd_puts_fd(2, "\n");
  }
}

/* `SD_CHECK(label, cond)`: boolean property (e.g. `ret > 0`), printed as `label=1/0`. */
static inline void sd_check(const char *label, int cond) { sd_expect(label, cond ? 1 : 0, 1); }

#define SD_EXPECT(label, got, want) sd_expect((label), (i64)(got), (i64)(want))
#define SD_SHOW(label, v) sd_show((label), (i64)(v))
#define SD_CHECK(label, cond) sd_check((label), (cond))

int sd_main(int argc, char **argv);

/* `_start`: x0 = sp (argc, argv...). Never returns. */
__attribute__((used, noreturn)) void sd_entry(u64 *sp) {
  int argc = (int)sp[0];
  char **argv = (char **)(sp + 1);
  sd_main(argc, argv);
  sd_exit_group(sd_failures ? 1 : 0);
}

__asm__(".text\n"
        ".global _start\n"
        ".type _start, %function\n"
        "_start:\n"
        "  mov x0, sp\n"
        "  bl sd_entry\n"
        "  brk #0\n");

#endif /* SD_RT_H */
