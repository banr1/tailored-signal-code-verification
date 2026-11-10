// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Linux AArch64 syscall classification table and fail-closed audit rules for static and dynamic
//! Rust `std` + static musl ELF inventories (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted host audit infrastructure under
//!   `tools/run-trusted-tests`).
//! - **Purpose:** Partition every Linux AArch64 (`asm-generic/unistd.h`) syscall encountered in
//!   static `svc #0` scans or dynamic `qemu-aarch64 -strace` executions into [`SyscallClass`]:
//!   [`SyscallClass::Modeled`], [`SyscallClass::NeedsModel`], or
//!   [`SyscallClass::ProvablyUnreachable`], and reject unclassified syscalls (statically or
//!   dynamically) as well as [`SyscallClass::ProvablyUnreachable`] syscalls reached at run time.
//!
//! # Key Types & Functions
//! - [`SyscallClass`]: Three-bucket classification (`modeled`, `needs_model`,
//!   `provably_unreachable`).
//! - [`SyscallClassification`]: Classification entry pairing number, canonical name, class, and
//!   technical rationale.
//! - [`classify_syscall`]: Total lookup returning `None` on unclassified syscall numbers.
//! - [`audit_static_syscall`] / [`audit_dynamic_syscall`]: Fail-closed audit checks.

use anyhow::{Result, bail};
use serde::{Deserialize, Serialize};

use crate::process_e2e::types::aarch64_syscall_name;

/// Three-way modeling status of a Linux AArch64 syscall in a statically linked `std` CLI binary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SyscallClass {
    /// Covered by the trusted Linux AArch64 syscall semantics in `Arm64/Trusted/Syscalls/` for the
    /// flag and argument subsets used on standard execution paths.
    Modeled,
    /// Reached dynamically by `std` startup or `mallocng` heap growth and requires a new or
    /// extended trusted syscall specification.
    NeedsModel,
    /// Linked statically via `libc` or `std` runtime helpers that are unreachable on
    /// single-threaded, non-aborting execution paths with open standard descriptors `0..=2`.
    ProvablyUnreachable,
}

impl SyscallClass {
    /// Short snake_case label rendered in Markdown and error diagnostics.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Modeled => "modeled",
            Self::NeedsModel => "needs_model",
            Self::ProvablyUnreachable => "provably_unreachable",
        }
    }
}

/// Complete classification record for a known Linux AArch64 syscall number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyscallClassification {
    pub nr: u64,
    pub name: &'static str,
    pub class: SyscallClass,
    pub rationale: &'static str,
}

/// Classify a Linux AArch64 syscall number (`__NR_*`), returning `None` if unclassified.
///
/// The `Modeled` arm corresponds to the 26 handlers in `Arm64/Trusted/Syscalls/` minus
/// `rt_sigaction` (`134`, placed in `NeedsModel` because `Signals.lean` currently handles only
/// `SIGABRT + SIG_DFL` while `std` startup installs `SIGPIPE -> SIG_IGN`) and `tkill` (`130`,
/// placed in `ProvablyUnreachable` because proven non-aborting paths never invoke `abort`/`raise`).
pub fn classify_syscall(nr: u64) -> Option<SyscallClassification> {
    use SyscallClass::{Modeled, NeedsModel, ProvablyUnreachable};

    let (name, class, rationale) = match nr {
        // -------------------------------------------------------------------------------------
        // 1. Modeled in `Arm64/Trusted/Syscalls/` (24 of the 26 entries in `Syscall.standard`)
        // -------------------------------------------------------------------------------------
        25 => (
            "fcntl",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean` (`F_GETFD` / `F_SETFD`).",
        ),
        29 => (
            "ioctl",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean`.",
        ),
        56 => (
            "openat",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean` (`AT_FDCWD` relative paths).",
        ),
        57 => (
            "close",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean`.",
        ),
        62 => (
            "lseek",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean`.",
        ),
        63 => (
            "read",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Stdio.lean` (`stdin` and local files).",
        ),
        64 => (
            "write",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Stdio.lean` (`stdout`, `stderr`, and local files).",
        ),
        67 => (
            "pread64",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean`.",
        ),
        80 => (
            "fstat",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/FileIo.lean` (`encodeLinuxStat`).",
        ),
        93 => (
            "exit",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Stdio.lean`.",
        ),
        94 => (
            "exit_group",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Stdio.lean`.",
        ),
        96 => (
            "set_tid_address",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Misc.lean` (`__init_tp`).",
        ),
        113 => (
            "clock_gettime",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Time.lean`.",
        ),
        123 => (
            "sched_getaffinity",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Misc.lean`.",
        ),
        131 => (
            "tgkill",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Signals.lean`.",
        ),
        132 => (
            "sigaltstack",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Signals.lean` (`do_sigaltstack`).",
        ),
        135 => (
            "rt_sigprocmask",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Signals.lean`.",
        ),
        172 => (
            "getpid",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Misc.lean`.",
        ),
        178 => (
            "gettid",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Misc.lean`.",
        ),
        214 => (
            "brk",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Alloc.lean` (`mallocng` metadata heap).",
        ),
        215 => (
            "munmap",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Alloc.lean`.",
        ),
        222 => (
            "mmap",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Alloc.lean` (anon `RW` and `MAP_FIXED` `PROT_NONE` guard pages).",
        ),
        226 => (
            "mprotect",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Alloc.lean`.",
        ),
        233 => (
            "madvise",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Alloc.lean`.",
        ),
        278 => (
            "getrandom",
            Modeled,
            "Modeled in `Arm64/Trusted/Syscalls/Random.lean` (`std::collections::HashMap` `RandomState`).",
        ),

        // -------------------------------------------------------------------------------------
        // 2. NeedsModel: reached dynamically by `std` startup or `mallocng` buffer growth
        // -------------------------------------------------------------------------------------
        73 => (
            "ppoll",
            NeedsModel,
            "`std` startup `sanitize_standard_fds` (`nfds = 3`, fds `0..=2`, `events = 0`, timeout `{0, 0}`, `sigmask = NULL`).",
        ),
        132 => (
            "sigaltstack",
            NeedsModel,
            "Prebuilt `std` startup/teardown `stack_overflow::imp::{init,cleanup}` installs and tears down the alternate signal stack.",
        ),
        134 => (
            "rt_sigaction",
            NeedsModel,
            "`std` startup `reset_sigpipe` (`SIGPIPE -> SIG_IGN`) and `stack_overflow::imp::init` (`SIGSEGV`/`SIGBUS`); `Signals.lean` only models `SIGABRT + SIG_DFL` and needs a per-signal disposition table.",
        ),
        216 => (
            "mremap",
            NeedsModel,
            "`mallocng` `realloc` of sizeclass-63 large allocations (`>= 131,052 B`, `MREMAP_MAYMOVE`) when growing buffers past 128 KiB.",
        ),

        // -------------------------------------------------------------------------------------
        // 3. ProvablyUnreachable: statically linked, unreachable on single-threaded non-abort runs
        // -------------------------------------------------------------------------------------
        17 => (
            "getcwd",
            ProvablyUnreachable,
            "musl `getcwd()`, linked via prebuilt `std` panic backtrace path resolution; unreachable on proven non-panicking execution paths.",
        ),
        23 => (
            "dup",
            ProvablyUnreachable,
            "musl `dup()`, linked via `std` `sanitize_standard_fds` multi-closed-fd fallback; unreachable when standard descriptors `0..=2` start open.",
        ),
        66 => (
            "writev",
            ProvablyUnreachable,
            "musl `FILE` `__stdio_write`; `std` writes directly via `SYS_write` (`LineWriter` / `BufWriter`), leaving musl `FILE` buffers empty at `__stdio_exit`.",
        ),
        78 => (
            "readlinkat",
            ProvablyUnreachable,
            "musl `readlink()` (`/proc/self/exe`), linked via prebuilt `std` panic backtrace symbolication; unreachable on proven non-panicking execution paths.",
        ),
        79 => (
            "newfstatat",
            ProvablyUnreachable,
            "musl `fstatat` fallback reached only when `SYS_fstat` returns `EBADF` while `fcntl(F_GETFD)` succeeds (`O_PATH` descriptors).",
        ),
        98 => (
            "futex",
            ProvablyUnreachable,
            "Single-threaded execution (`__libc.need_locks == 0`, uncontended `Once` / `Mutex` / `ReentrantLock`).",
        ),
        130 => (
            "tkill",
            ProvablyUnreachable,
            "musl `abort()` / `raise()` (modeled in `Signals.lean`, unreachable on proven non-aborting execution paths).",
        ),
        139 => (
            "rt_sigreturn",
            ProvablyUnreachable,
            "musl `__restore_rt` signal return trampoline (signals are recorded, never delivered).",
        ),
        163 => (
            "getrlimit",
            ProvablyUnreachable,
            "musl `getrlimit()` fallback arm in `sysconf()`; `stack_overflow::init` only queries `_SC_PAGESIZE` via `AT_PAGESZ` in `auxv`.",
        ),
        169 => (
            "gettimeofday",
            ProvablyUnreachable,
            "musl `__clock_gettime` fallback arm when `SYS_clock_gettime` returns `-ENOSYS`; unreachable because `Arm64/Trusted/Syscalls/Time.lean` models `clock_gettime` (`113`) directly.",
        ),
        179 => (
            "sysinfo",
            ProvablyUnreachable,
            "musl `sysconf()` arm for physical-memory queries; `stack_overflow::init` only queries `_SC_PAGESIZE` via `AT_PAGESZ` in `auxv`.",
        ),
        261 => (
            "prlimit64",
            ProvablyUnreachable,
            "musl `getrlimit()` primary syscall in `sysconf()`; `stack_overflow::init` only queries `_SC_PAGESIZE` via `AT_PAGESZ` in `auxv`.",
        ),
        _ => return None,
    };

    Some(SyscallClassification {
        nr,
        name,
        class,
        rationale,
    })
}

/// Fail-closed check for a syscall number resolved statically from an ELF `svc #0` site.
pub fn audit_static_syscall(bin_id: &str, nr: u64) -> Result<SyscallClassification> {
    classify_syscall(nr).ok_or_else(|| {
        let known_name = aarch64_syscall_name(nr).unwrap_or("unknown");
        anyhow::anyhow!(
            "fail-closed static audit: binary `{bin_id}` contains unclassified static `svc #0` \
             syscall {nr} (`{known_name}`)"
        )
    })
}

/// Fail-closed check for a syscall number observed dynamically under `qemu-aarch64 -strace`.
///
/// Rejects both unclassified syscalls and [`SyscallClass::ProvablyUnreachable`] syscalls (unless
/// `allowed_unreachable` explicitly whitelists `nr` for a synthetic host-environment probe such as
/// multi-closed standard descriptors).
pub fn audit_dynamic_syscall(
    scenario_id: &str,
    bin_id: &str,
    nr: u64,
    allowed_unreachable: &[u64],
) -> Result<SyscallClassification> {
    let Some(info) = classify_syscall(nr) else {
        let known_name = aarch64_syscall_name(nr).unwrap_or("unknown");
        bail!(
            "fail-closed dynamic audit: scenario `{scenario_id}` (binary `{bin_id}`) executed \
             unclassified syscall {nr} (`{known_name}`)"
        );
    };
    if info.class == SyscallClass::ProvablyUnreachable && !allowed_unreachable.contains(&nr) {
        bail!(
            "fail-closed dynamic audit: scenario `{scenario_id}` (binary `{bin_id}`) dynamically \
             executed `provably_unreachable` syscall {} (`{}`): {}",
            info.nr,
            info.name,
            info.rationale
        );
    }
    Ok(info)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::process_e2e::types::aarch64_syscall_info;

    #[test]
    fn classified_table_aligns_with_aarch64_name_registry() {
        for nr in 0..=500u64 {
            if let Some(c) = classify_syscall(nr) {
                assert_eq!(
                    aarch64_syscall_name(nr),
                    Some(c.name),
                    "mismatch in canonical name for syscall {nr}"
                );
                let (mapped_nr, modeled_in_tcb) = aarch64_syscall_info(c.name);
                assert_eq!(mapped_nr, Some(nr as u32));
                if c.class == SyscallClass::Modeled {
                    assert!(
                        modeled_in_tcb,
                        "syscall {} ({}) marked Modeled but not modeled in process_e2e table",
                        c.nr, c.name
                    );
                }
            }
        }
    }

    #[test]
    fn dynamic_audit_rejects_provably_unreachable_and_unclassified() {
        for nr in [17u64, 23, 66, 78, 79, 98, 130, 139, 163, 169, 179, 261] {
            let err = audit_dynamic_syscall("scen_probe", "alpha", nr, &[]).unwrap_err();
            assert!(
                err.to_string().contains("provably_unreachable"),
                "unexpected error for {nr}: {err}"
            );
        }
        // Unclassified syscall (e.g. `unlinkat` = 35 or `clone` = 220) fails closed both statically and dynamically.
        assert!(audit_static_syscall("alpha", 35).is_err());
        assert!(audit_dynamic_syscall("scen_probe", "alpha", 35, &[35]).is_err());

        // `Modeled` and `NeedsModel` pass dynamic audit.
        assert_eq!(
            audit_dynamic_syscall("scen_probe", "alpha", 64, &[])
                .unwrap()
                .class,
            SyscallClass::Modeled
        );
        assert_eq!(
            audit_dynamic_syscall("scen_probe", "alpha", 216, &[])
                .unwrap()
                .class,
            SyscallClass::NeedsModel
        );
    }
}
