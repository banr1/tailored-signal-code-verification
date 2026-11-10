// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! JSON schema for `expected_vectors.json` and AArch64 Linux syscall census table (`[TEST ONLY]`).

use serde::{Deserialize, Serialize};

/// Top-level serialized differential suite consumed by `Arm64/Testing/Regression/ProcessE2E.lean`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProcessE2ESuite {
    pub schema_version: u32,
    pub qemu_version: String,
    pub rustc_version: String,
    pub target_triple: String,
    pub programs: Vec<ProgramSummary>,
    pub cases: Vec<VectorCase>,
}

/// Per-binary metadata and aggregated QEMU `-strace` syscall census.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgramSummary {
    pub name: String,
    pub source: String,
    pub elf_path: String,
    pub size_bytes: u64,
    pub sha256: String,
    pub entry_va: String,
    pub runtime_flavor: String,
    pub description: String,
    pub syscalls_observed: Vec<SyscallCount>,
}

/// Count and modeling status of a single Linux AArch64 syscall observed under `qemu-aarch64 -strace`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyscallCount {
    pub name: String,
    pub nr: Option<u32>,
    pub modeled: bool,
    pub calls: usize,
}

/// Classification of how a case behaves between real Linux (`qemu-aarch64`) and Lean `runElf`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CaseCategory {
    /// Linux and Lean `runElf` agree completely on exit code, `stdout`, `stderr`, and watched files.
    Match,
    /// Host OS returns live entropy on QEMU; Lean `runElf` replays deterministic `Oracle.getrandom`.
    EntropyNondeterministic,
    /// Program uses an unmodeled syscall/flag or instruction and fails closed in Lean (`Exception`).
    UnmodeledTrap,
    /// Both Linux and Lean complete, or Lean exits cleanly when Linux signals: true model divergence.
    Divergence,
}

/// Initial regular file supplied to both QEMU's temporary `cwd` and `ProcessInputs.files`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FileEntry {
    pub path: String,
    pub hex: String,
}

/// Post-execution snapshot of a watched path in QEMU's temporary `cwd`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PostFileEntry {
    pub path: String,
    pub exists: bool,
    pub hex: String,
}

/// Recorded execution result from `qemu-aarch64 -0 <argv0> -D <log> -strace`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct QemuOutcome {
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub stdout_hex: String,
    pub stdout_utf8: Option<String>,
    pub stdout_len: usize,
    pub stderr_hex: String,
    pub stderr_utf8: Option<String>,
    pub nondeterministic_stdout: bool,
    pub normalized_tid_in_stderr: bool,
    pub post_files: Vec<PostFileEntry>,
    pub syscalls: Vec<SyscallCount>,
}

/// Expected Lean `runElf` / `runElfByteArrayFast` terminal outcome for machine-checked verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedLean {
    /// `"exited"`, `"exception"`, or `"halted"`.
    pub kind: String,
    pub lean_exit_code: Option<u64>,
    pub syscall_nr: Option<u64>,
    pub syscall_name: Option<String>,
    pub exception_substr: Option<String>,
    pub notes: String,
}

/// Complete differential test vector for a single invocation of a guest ELF binary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VectorCase {
    pub id: String,
    pub program: String,
    pub elf_path: String,
    pub category: CaseCategory,
    pub args: Vec<String>,
    pub envp: Vec<String>,
    pub stdin_hex: String,
    pub stdin_utf8_preview: Option<String>,
    pub pre_dirs: Vec<String>,
    pub initial_files: Vec<FileEntry>,
    pub watched_files: Vec<String>,
    /// When `true`, `ProcessE2E.lean` also runs unaccelerated `Arm64.Process.runElf` directly.
    pub use_ref_runner: bool,
    pub qemu: QemuOutcome,
    pub expected_lean: ExpectedLean,
}

/// Map QEMU `-strace` AArch64 syscall names to `(aarch64_nr, modeled_in_lean_eval)`.
///
/// Matches `Arm64/Trusted/Syscalls.lean` (`execSyscall` / `ModeledSyscall` — 31 modeled syscalls).
/// Note that `mmap` (`222`; anonymous private `PROT_READ | PROT_WRITE` or `PROT_NONE` with
/// optional `MAP_STACK = 0x20022`, plus `MAP_FIXED` (`0x32`) with `PROT_NONE` only), `mremap`
/// (`216`; `MREMAP_MAYMOVE` on uniform `PROT_READ | PROT_WRITE` ranges), `mprotect` (`226`),
/// `madvise` (`233`), `ppoll` (`73`; zero-timeout `events = 0` probes on `fd ∈ {0, 1, 2}`),
/// `sigaltstack` (`132`; `MINSIGSTKSZ = 5120`), `rt_sigaction` (`134`; `SIG_DFL` / `SIG_IGN` plus
/// custom `sa_handler` strictly for `SIGSEGV` and `SIGBUS`), and `fcntl` (`25`; `F_GETFD` and
/// `F_SETFD` only) model concrete subsets and fail closed with `.Exception` on other flags/commands.
pub fn aarch64_syscall_info(name: &str) -> (Option<u32>, bool) {
    match name {
        "getcwd" => (Some(17), false),
        "eventfd2" => (Some(19), false),
        "epoll_create1" => (Some(20), false),
        "dup" => (Some(23), false),
        "dup3" => (Some(24), false),
        "fcntl" => (Some(25), true),
        "ioctl" => (Some(29), true),
        "mkdirat" => (Some(34), false),
        "unlinkat" => (Some(35), false),
        "symlinkat" => (Some(36), false),
        "linkat" => (Some(37), false),
        "renameat" => (Some(38), false),
        "statfs" => (Some(43), false),
        "fstatfs" => (Some(44), false),
        "truncate" => (Some(45), false),
        "ftruncate" => (Some(46), false),
        "fallocate" => (Some(47), false),
        "faccessat" => (Some(48), false),
        "chdir" => (Some(49), false),
        "fchdir" => (Some(50), false),
        "fchmod" => (Some(52), false),
        "fchmodat" => (Some(53), false),
        "fchownat" => (Some(54), false),
        "fchown" => (Some(55), false),
        "openat" => (Some(56), true),
        "close" => (Some(57), true),
        "pipe2" => (Some(59), false),
        "getdents64" => (Some(61), false),
        "lseek" => (Some(62), true),
        "read" => (Some(63), true),
        "write" => (Some(64), true),
        "readv" => (Some(65), true),
        "writev" => (Some(66), true),
        "pread64" => (Some(67), true),
        "pwrite64" => (Some(68), false),
        "sendfile" => (Some(71), false),
        "pselect6" => (Some(72), false),
        "ppoll" => (Some(73), true),
        "readlinkat" => (Some(78), false),
        "newfstatat" | "fstatat" => (Some(79), false),
        "fstat" => (Some(80), true),
        "sync" => (Some(81), false),
        "fsync" => (Some(82), false),
        "fdatasync" => (Some(83), false),
        "exit" => (Some(93), true),
        "exit_group" => (Some(94), true),
        "waitid" => (Some(95), false),
        "set_tid_address" => (Some(96), true),
        "futex" => (Some(98), false),
        "set_robust_list" => (Some(99), false),
        "get_robust_list" => (Some(100), false),
        "nanosleep" => (Some(101), false),
        "clock_gettime" => (Some(113), true),
        "clock_getres" => (Some(114), false),
        "clock_nanosleep" => (Some(115), false),
        "sched_setaffinity" => (Some(122), false),
        "sched_getaffinity" => (Some(123), true),
        "sched_yield" => (Some(124), false),
        "kill" => (Some(129), false),
        "tkill" => (Some(130), true),
        "tgkill" => (Some(131), true),
        "sigaltstack" => (Some(132), true),
        "rt_sigsuspend" => (Some(133), false),
        "rt_sigaction" => (Some(134), true),
        "rt_sigprocmask" => (Some(135), true),
        "rt_sigpending" => (Some(136), false),
        "rt_sigtimedwait" => (Some(137), false),
        "rt_sigreturn" => (Some(139), false),
        "uname" => (Some(160), false),
        "getrlimit" => (Some(163), false),
        "setrlimit" => (Some(164), false),
        "getrusage" => (Some(165), false),
        "gettimeofday" => (Some(169), false),
        "getpid" => (Some(172), true),
        "getppid" => (Some(173), false),
        "getuid" => (Some(174), false),
        "geteuid" => (Some(175), false),
        "getgid" => (Some(176), false),
        "getegid" => (Some(177), false),
        "gettid" => (Some(178), true),
        "sysinfo" => (Some(179), false),
        "socket" => (Some(198), false),
        "connect" => (Some(203), false),
        "brk" => (Some(214), true),
        "munmap" => (Some(215), true),
        "mremap" => (Some(216), true),
        "clone" => (Some(220), false),
        "execve" => (Some(221), false),
        "mmap" => (Some(222), true),
        "fadvise64" => (Some(223), false),
        "mprotect" => (Some(226), true),
        "msync" => (Some(227), false),
        "madvise" => (Some(233), true),
        "wait4" => (Some(260), false),
        "prlimit64" => (Some(261), false),
        "renameat2" => (Some(276), false),
        "getrandom" => (Some(278), true),
        "memfd_create" => (Some(279), false),
        "copy_file_range" => (Some(285), false),
        "statx" => (Some(291), false),
        "rseq" => (Some(293), false),
        "clone3" => (Some(435), false),
        "close_range" => (Some(436), false),
        "openat2" => (Some(437), false),
        "faccessat2" => (Some(439), false),
        _ => (None, false),
    }
}

/// Map a Linux AArch64 (`asm-generic/unistd.h`) syscall number to its canonical name.
pub fn aarch64_syscall_name(nr: u64) -> Option<&'static str> {
    match nr {
        17 => Some("getcwd"),
        19 => Some("eventfd2"),
        20 => Some("epoll_create1"),
        23 => Some("dup"),
        24 => Some("dup3"),
        25 => Some("fcntl"),
        29 => Some("ioctl"),
        34 => Some("mkdirat"),
        35 => Some("unlinkat"),
        36 => Some("symlinkat"),
        37 => Some("linkat"),
        38 => Some("renameat"),
        43 => Some("statfs"),
        44 => Some("fstatfs"),
        45 => Some("truncate"),
        46 => Some("ftruncate"),
        47 => Some("fallocate"),
        48 => Some("faccessat"),
        49 => Some("chdir"),
        50 => Some("fchdir"),
        52 => Some("fchmod"),
        53 => Some("fchmodat"),
        54 => Some("fchownat"),
        55 => Some("fchown"),
        56 => Some("openat"),
        57 => Some("close"),
        59 => Some("pipe2"),
        61 => Some("getdents64"),
        62 => Some("lseek"),
        63 => Some("read"),
        64 => Some("write"),
        65 => Some("readv"),
        66 => Some("writev"),
        67 => Some("pread64"),
        68 => Some("pwrite64"),
        71 => Some("sendfile"),
        72 => Some("pselect6"),
        73 => Some("ppoll"),
        78 => Some("readlinkat"),
        79 => Some("newfstatat"),
        80 => Some("fstat"),
        81 => Some("sync"),
        82 => Some("fsync"),
        83 => Some("fdatasync"),
        93 => Some("exit"),
        94 => Some("exit_group"),
        95 => Some("waitid"),
        96 => Some("set_tid_address"),
        98 => Some("futex"),
        99 => Some("set_robust_list"),
        100 => Some("get_robust_list"),
        101 => Some("nanosleep"),
        113 => Some("clock_gettime"),
        114 => Some("clock_getres"),
        115 => Some("clock_nanosleep"),
        122 => Some("sched_setaffinity"),
        123 => Some("sched_getaffinity"),
        124 => Some("sched_yield"),
        129 => Some("kill"),
        130 => Some("tkill"),
        131 => Some("tgkill"),
        132 => Some("sigaltstack"),
        133 => Some("rt_sigsuspend"),
        134 => Some("rt_sigaction"),
        135 => Some("rt_sigprocmask"),
        136 => Some("rt_sigpending"),
        137 => Some("rt_sigtimedwait"),
        139 => Some("rt_sigreturn"),
        160 => Some("uname"),
        163 => Some("getrlimit"),
        164 => Some("setrlimit"),
        165 => Some("getrusage"),
        169 => Some("gettimeofday"),
        172 => Some("getpid"),
        173 => Some("getppid"),
        174 => Some("getuid"),
        175 => Some("geteuid"),
        176 => Some("getgid"),
        177 => Some("getegid"),
        178 => Some("gettid"),
        179 => Some("sysinfo"),
        198 => Some("socket"),
        203 => Some("connect"),
        214 => Some("brk"),
        215 => Some("munmap"),
        216 => Some("mremap"),
        220 => Some("clone"),
        221 => Some("execve"),
        222 => Some("mmap"),
        223 => Some("fadvise64"),
        226 => Some("mprotect"),
        227 => Some("msync"),
        233 => Some("madvise"),
        260 => Some("wait4"),
        261 => Some("prlimit64"),
        276 => Some("renameat2"),
        278 => Some("getrandom"),
        279 => Some("memfd_create"),
        285 => Some("copy_file_range"),
        291 => Some("statx"),
        293 => Some("rseq"),
        435 => Some("clone3"),
        436 => Some("close_range"),
        437 => Some("openat2"),
        439 => Some("faccessat2"),
        _ => None,
    }
}
