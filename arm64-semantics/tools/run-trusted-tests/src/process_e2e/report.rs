// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Markdown summary generator for the whole-ELF process differential test suite (`[TEST ONLY]`).

use std::fmt::Write as _;

use super::types::{CaseCategory, ProcessE2ESuite};

/// Render a human-readable Markdown report summarizing binaries, cases, syscall census, and gaps.
pub fn render_markdown_report(suite: &ProcessE2ESuite) -> String {
    let total_cases = suite.cases.len();
    let match_cases = suite
        .cases
        .iter()
        .filter(|c| c.category == CaseCategory::Match)
        .count();
    let entropy_cases = suite
        .cases
        .iter()
        .filter(|c| c.category == CaseCategory::EntropyNondeterministic)
        .count();
    let trap_cases = suite
        .cases
        .iter()
        .filter(|c| c.category == CaseCategory::UnmodeledTrap)
        .count();
    let div_cases = suite
        .cases
        .iter()
        .filter(|c| c.category == CaseCategory::Divergence)
        .count();

    let mut out = String::new();
    let _ = writeln!(
        &mut out,
        "# Whole-ELF Linux Process Differential Test Report (`qemu-aarch64` vs Lean `runElf`)\n"
    );
    let _ = writeln!(
        &mut out,
        "- **Guest Toolchain:** `{}` (`{}` static `ET_EXEC`, `ld.lld`, stripped deterministic build)",
        suite.rustc_version, suite.target_triple
    );
    let _ = writeln!(&mut out, "- **Reference Linux Runner:** `{}`", suite.qemu_version);
    let _ = writeln!(
        &mut out,
        "- **Total Guest Binaries:** **{}** (`1` `#![no_std]` custom `_start`, `9` `#![no_main]` Rust `std` + static musl with `BrkMmapAlloc` (`session_store` using unmodified `std::fs::read`/`write`), `1` zero-shim `#![no_main]` `std` probe, `1` full `fn main()` `std` startup probe)",
        suite.programs.len()
    );
    let _ = writeln!(
        &mut out,
        "- **Total Differential Cases:** **{}** (**{}** exact byte-for-byte matches + **{}** `getrandom` entropy/oracle check, **{}** fail-closed unmodeled syscall/instruction traps, **{}** Linux-vs-Lean semantic divergences)\n",
        total_cases, match_cases, entropy_cases, trap_cases, div_cases
    );

    let _ = writeln!(&mut out, "## 1. Guest Programs & Differential Results\n");
    let _ = writeln!(
        &mut out,
        "| Program | Runtime | ELF Size | SHA-256 (prefix) | Cases | Match / Oracle | Traps | Divergences | Observed Syscalls (`qemu -strace`) |"
    );
    let _ = writeln!(
        &mut out,
        "|---|---|---:|---|---:|---:|---:|---:|---|"
    );

    for p in &suite.programs {
        let p_cases: Vec<_> = suite.cases.iter().filter(|c| c.program == p.name).collect();
        let n_match = p_cases
            .iter()
            .filter(|c| {
                matches!(
                    c.category,
                    CaseCategory::Match | CaseCategory::EntropyNondeterministic
                )
            })
            .count();
        let n_trap = p_cases
            .iter()
            .filter(|c| c.category == CaseCategory::UnmodeledTrap)
            .count();
        let n_div = p_cases
            .iter()
            .filter(|c| c.category == CaseCategory::Divergence)
            .count();
        let census_str = p
            .syscalls_observed
            .iter()
            .map(|sc| {
                let tag = if sc.modeled { "" } else { " **[UNMODELED]**" };
                match sc.nr {
                    Some(nr) => format!("`{}({})`×{}{}", sc.name, nr, sc.calls, tag),
                    None => format!("`{}`×{}{}", sc.name, sc.calls, tag),
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            &mut out,
            "| `{}` | `{}` | {} B | `{}` | {} | {} | {} | {} | {} |",
            p.name,
            p.runtime_flavor,
            p.size_bytes,
            &p.sha256[..12],
            p_cases.len(),
            n_match,
            n_trap,
            n_div,
            census_str
        );
    }

    let _ = writeln!(
        &mut out,
        "\n## 2. Non-Matching Cases: Unmodeled Syscall Traps & Linux-vs-Lean Divergences\n"
    );
    let _ = writeln!(
        &mut out,
        "| Case ID | Category | QEMU Outcome | Lean `runElf` Outcome | Exact Cause / Model Gap |"
    );
    let _ = writeln!(&mut out, "|---|---|---|---|---|");

    for c in suite
        .cases
        .iter()
        .filter(|c| c.category != CaseCategory::Match)
    {
        let cat_str = match c.category {
            CaseCategory::Match => "match",
            CaseCategory::EntropyNondeterministic => "entropy_oracle",
            CaseCategory::UnmodeledTrap => "unmodeled_trap",
            CaseCategory::Divergence => "DIVERGENCE",
        };
        let qemu_desc = match (c.qemu.exit_code, c.qemu.signal) {
            (Some(code), None) => format!("`exit({code})`"),
            (None, Some(sig)) => format!("`signal({sig})`"),
            (code, sig) => format!("`exit={code:?}, sig={sig:?}`"),
        };
        let lean_desc = match c.expected_lean.kind.as_str() {
            "exited" => format!(
                "`.Exited {}`",
                c.expected_lean.lean_exit_code.unwrap_or_default()
            ),
            "halted" => "`.Halted` (`out? = none`)".into(),
            "exception" => match (&c.expected_lean.syscall_name, c.expected_lean.syscall_nr) {
                (Some(name), Some(nr)) => format!(
                    "`.Exception {:?}` (`x8 = {nr}`, `{name}`)",
                    c.expected_lean
                        .exception_substr
                        .as_deref()
                        .unwrap_or("exception")
                ),
                _ => format!(
                    "`.Exception {:?}`",
                    c.expected_lean
                        .exception_substr
                        .as_deref()
                        .unwrap_or("exception")
                ),
            },
            other => other.to_owned(),
        };
        let _ = writeln!(
            &mut out,
            "| `{}` | `{}` | {} | {} | {} |",
            c.id, cat_str, qemu_desc, lean_desc, c.expected_lean.notes
        );
    }

    let _ = writeln!(
        &mut out,
        "\n## 3. All Passing Differential Cases (`qemu-aarch64` == Lean `runElf`)\n"
    );
    let _ = writeln!(
        &mut out,
        "| Case ID | Exit Code | `stdout` (B) | `stderr` (B) | Watched Files | Ref `runElf` | Notes |"
    );
    let _ = writeln!(&mut out, "|---|---:|---:|---:|---:|:---:|---|");
    for c in suite
        .cases
        .iter()
        .filter(|c| c.category == CaseCategory::Match)
    {
        let status_label = match (c.qemu.exit_code, c.qemu.signal) {
            (Some(code), None) => format!("{code}"),
            (None, Some(sig)) => format!("{} (sig {sig})", 128 + sig),
            _ => "-1".to_owned(),
        };
        let _ = writeln!(
            &mut out,
            "| `{}` | `{}` | {} | {} | {} | {} | {} |",
            c.id,
            status_label,
            c.qemu.stdout_len,
            c.qemu.stderr_hex.len() / 2,
            c.watched_files.len(),
            if c.use_ref_runner { "yes" } else { "fast" },
            c.expected_lean.notes
        );
    }

    append_gap_catalog(&mut out);
    out
}

fn append_gap_catalog(out: &mut String) {
    let _ = out.write_str(
        r#"
## 4. Syscall, Allocator, & Filesystem Gap Catalog (Static Musl Rust CLIs)

| ID | Gap / Divergence | Real Linux (`qemu-aarch64`) | Current Lean Semantics (`Arm64/Trusted/`) | Non-TCB Workaround vs Gated TCB Change |
|---|---|---|---|---|
| **G1** | Stock musl `mallocng` guard page `mmap` (`unmodified_std_probe/mallocng_guard_page`) | First `Vec` allocation calls `mmap(page, 4096, PROT_NONE (0x0), MAP_PRIVATE\|MAP_ANONYMOUS\|MAP_FIXED (0x32), -1, 0)` -> succeeds (`exit 0`) | Modeled: `execMmap` (`Arm64/Trusted/ISA/Eval.lean`) accepts `MAP_FIXED` with `PROT_NONE` at a page-aligned, non-frozen `addr >= 65536` and maps zero-filled `PROT_NONE` pages (`exit 0`, matches QEMU) | None needed; `BrkMmapAlloc` (`src/common.rs`) remains for the other probe binaries. |
| **G2 (RESOLVED)** | Musl `open()` calls `SYS_fcntl(fd, F_SETFD, FD_CLOEXEC)` (`unmodified_std_probe/fs_fcntl_cloexec`) | `openat(..., O_CLOEXEC)` -> `fd = 3`, then `fcntl(3, F_SETFD, FD_CLOEXEC)` -> `0` (`exit 0`) | **Modeled in `execFcntl`:** `F_SETFD (2)` returns `0` as a no-op on open `.localFile` descriptors (`FD_CLOEXEC` untracked since no `execve`, and `F_GETFD (1)` traps fail-closed); matches QEMU (`exit 0`) | Resolved in `Arm64/Trusted/ISA/Eval.lean`. |
| **G3 (RESOLVED)** | Normal `fn main()` runtime startup (`std_startup_probe/lang_start`) | Calls `ppoll (73)`, `rt_sigaction (134)` ×5, `sigaltstack (132)` ×3, `mmap MAP_STACK (222)`, `mprotect (226)`, `rt_sigprocmask (135)` (`exit 0`) | **Modeled in `Arm64/Trusted/Syscalls/`:** `ppoll`, `sigaltstack`, `MAP_STACK` `mmap`, `mprotect`, and `SIGSEGV`/`SIGBUS` `rt_sigaction` execute full `std::rt::lang_start` startup and teardown (`exit 0`, matches QEMU) | Resolved in `Arm64/Trusted/Syscalls/Signals.lean` and `Mm/Mmap.lean`. |
| **G4 (FAIL-CLOSED)** | Panics & `abort()` vs `udf` (`panic_gettid`, `panic_formatted`, `abort_sigabrt`, `abort_after_stdout`, `udf_sigill`, `udf1_sigill`) | `panic!` / `abort()` call musl `raise(SIGABRT)` -> `rt_sigprocmask(SIG_BLOCK, &app_mask, ...)` (`135`) -> `tkill (130)` (`SIGABRT`, status `134`); `udf #0`/`#1` raise `SIGILL` | **Fail-closed on non-zero signal masks:** direct `tkill`/`tgkill(SIGABRT)` produces `ExecStatus.Signaled 6#7` (`exitCode = 134`, `signal = some 6`), whereas musl `raise()`'s non-zero `SIG_BLOCK` traps with `.Exception "unmodeled non-zero signal mask in rt_sigprocmask"`, alongside `udf #0` (`.Halted`) and `udf #1` (`.Exception "udf"`) | All unmodeled abort/trap paths fail closed under `ProcessSafeRun` / `ProcessSafeOutcome`. |
| **D1** | `BRK #1` clean-exit divergence (`unmodified_std_probe/brk1_divergence`) | Kernel delivers fatal `SIGTRAP` (`signal = 5`) | `Arm64/Trusted/ISA/Eval.lean` transitions `BRK #1` to `.Exited 101#64` (indistinguishable from `SYS_exit_group(101)`); `BRK #0` sets `.Halted` (`out? = none`) | Exclude `101#64` from `allowedCodes`, and fix `BRK` exception semantics in a separate gated TCB PR. |
| **D2 (RESOLVED)** | `execOpenat` missing parent directories on `O_CREAT` (`session_store/missing_parent_dir_divergence`) | `openat(AT_FDCWD, "signed-pre-keys/1", O_WRONLY\|O_CREAT\|O_TRUNC, 0666)` returns `-ENOENT` (`exit 2`) when `"signed-pre-keys"` is absent | **Modeled in `execOpenat`:** walks ancestor components via `ancestorWalkErrno?` (`-ENOENT` when missing, `-ENOTDIR` when an ancestor is a regular file); matches QEMU (`exit 2`) | Resolved in `Arm64/Trusted/ISA/Eval.lean`. |
| **D3 (RESOLVED)** | `resolveAtPath` `.` / `//` path normalization (`session_store/dot_slash_coins_divergence`) | `openat(AT_FDCWD, "./coins", O_RDONLY)` resolves `"./coins"` to `"coins"` (`exit 0`) | **Modeled in `resolveAtPath`:** `normalizePath` collapses `.` segments and repeated `/`, and `".."` fails closed with `.Exception`; matches QEMU (`exit 0`) | Resolved in `Arm64/Trusted/ISA/Eval.lean` (`".."` intentionally fail-closed). |
| **S1 (RESOLVED)** | Multi-exit-code / signal top-level specs (`Arm64/Trusted/Process/Semantics.lean`) | Multi-exit-code CLIs return `0`, `1`, `2`, or `134` (`SIGABRT`) | **`ElfImageRunsTo` / `ElfRunsTo` (`#577`):** support arbitrary `post : ProcessOutcome → Prop` (including non-zero exit codes and `signal : Option Nat`) and `oom` | Resolved in `Arm64/Trusted/Process/Semantics.lean` and `ProofLib/Process.lean`. |
"#,
    );
}
