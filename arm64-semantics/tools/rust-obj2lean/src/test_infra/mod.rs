// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Test infrastructure (`test_infra`) — `[TEST ONLY]` (`cfg(test)`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (compiled only under `#[cfg(test)]`; not part of the
//!   `rust-obj2lean` binary or TCB, and produces no Lean code).
//! - **Purpose:** Groups differential test harnesses validating `[TCB]` relocation/placement
//!   definitions (`Arm64.Obj.Placed`) and the `[OUTSIDE TCB]` symbolic execution engine against
//!   external reference tools (`ld.lld`, `llvm-mc`, `placed_eval`, and Unicorn `UC_ARCH_ARM64`),
//!   along with shared external-tool discovery and fail-closed (`REQUIRE_LINK_DIFF=1`) helpers.
//!
//! # Key Types & Functions
//! - [`placed_lld_diff`]: 4-layer differential tests comparing `Arm64.Obj.Placed` (`placed_eval`)
//!   and `untrusted_placed` against stock `ld.lld`.
//! - [`symexec_diff`]: Differential tests comparing `symexec::insn_semantics` against Unicorn.
//! - [`Tool`], [`find_lld`], [`find_llvm_mc`], [`require_link_diff`], [`skip_or_panic`]: External
//!   LLVM tool discovery and fail-closed (`REQUIRE_LINK_DIFF=1`) helpers.
//!
//! # When to Read This File
//! - Read this file for external LLVM tool discovery (`LLD`, `LLVM_MC`, `REQUIRE_LINK_DIFF`);
//!   jump to [`placed_lld_diff.rs`](placed_lld_diff.rs) or [`symexec_diff.rs`](symexec_diff.rs)
//!   for the differential test suites themselves.

use std::path::PathBuf;
use std::process::Command;

pub mod placed_lld_diff;
pub mod symexec_diff;

/// An external tool: program plus leading arguments.
pub struct Tool {
    pub prog: PathBuf,
    pub args: Vec<String>,
}

impl Tool {
    pub fn cmd(&self) -> Command {
        let mut c = Command::new(&self.prog);
        c.args(&self.args);
        c
    }
}

/// `$LLD`, `ld.lld` on `PATH`, or `rust-lld -flavor gnu` from the active rustc sysroot.
pub fn find_lld() -> Option<Tool> {
    if let Some(p) = std::env::var_os("LLD") {
        return Some(Tool {
            prog: p.into(),
            args: vec![],
        });
    }
    if let Ok(p) = which::which("ld.lld") {
        return Some(Tool {
            prog: p,
            args: vec![],
        });
    }
    let out = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()?;
    let sysroot = PathBuf::from(String::from_utf8(out.stdout).ok()?.trim());
    let rustlib = std::fs::read_dir(sysroot.join("lib/rustlib")).ok()?;
    rustlib
        .flatten()
        .map(|e| e.path().join("bin/rust-lld"))
        .find(|p| p.is_file())
        .map(|p| Tool {
            prog: p,
            args: vec!["-flavor".into(), "gnu".into()],
        })
}

/// `$LLVM_MC` or `llvm-mc` (including versioned `llvm-mc-{20..16}`) on `PATH`.
pub fn find_llvm_mc() -> Option<Tool> {
    if let Some(p) = std::env::var_os("LLVM_MC") {
        return Some(Tool {
            prog: PathBuf::from(p),
            args: vec![],
        });
    }
    for cand in [
        "llvm-mc",
        "llvm-mc-20",
        "llvm-mc-19",
        "llvm-mc-18",
        "llvm-mc-17",
        "llvm-mc-16",
    ] {
        if let Ok(prog) = which::which(cand) {
            return Some(Tool { prog, args: vec![] });
        }
    }
    None
}

/// Whether differential link tests must fail closed (`REQUIRE_LINK_DIFF=1`) rather than
/// skipping when `ld.lld`, `llvm-mc`, `placed_eval`, `rustc`, or upstream sources are absent.
pub fn require_link_diff() -> bool {
    std::env::var_os("REQUIRE_LINK_DIFF")
        .is_some_and(|v| !v.is_empty() && v != "0" && v != "false")
}

/// Panic if `fail_closed` is enabled; otherwise log a `skipping: ...` message and return
/// `None` so callers can `return`.
pub fn skip_or_panic_if<T>(fail_closed: bool, reason: impl std::fmt::Display) -> Option<T> {
    if fail_closed {
        panic!("REQUIRE_LINK_DIFF=1: refusing to skip link differential test: {reason}");
    }
    eprintln!("skipping: {reason}");
    None
}

/// Panic if [`require_link_diff`] is enabled; otherwise log a `skipping: ...` message and return
/// `None`.
pub fn skip_or_panic<T>(reason: impl std::fmt::Display) -> Option<T> {
    skip_or_panic_if(require_link_diff(), reason)
}

/// Return `llvm-mc`, or skip/panic via [`skip_or_panic`].
pub fn mc_only() -> Option<Tool> {
    match find_llvm_mc() {
        Some(mc) => Some(mc),
        None => skip_or_panic("llvm-mc not found ($LLVM_MC or PATH)"),
    }
}

/// Repository root directory (`../..` from `tools/rust-obj2lean`).
pub fn repo_root() -> PathBuf {
    crate::untrusted_lemmas::index::default_repo_root()
}

#[cfg(test)]
mod tests {
    use super::skip_or_panic_if;

    #[test]
    #[should_panic(expected = "REQUIRE_LINK_DIFF=1: refusing to skip link differential test")]
    fn require_link_diff_refuses_to_skip() {
        let _: Option<()> = skip_or_panic_if(true, "simulated missing llvm-mc");
    }
}
