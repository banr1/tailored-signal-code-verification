// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Specification of the original 12 guest binaries' differential test cases (the 14 workload
//! binaries' cases live in [`super::cases_workloads`]) and QEMU regeneration/drift check
//! (`[TEST ONLY]`).

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use anyhow::{Context, Result, anyhow, bail};

use super::build::{BuiltElfInfo, load_checked_in_elf_infos};
use super::cases_workloads::record_workload_cases;
use super::qemu::{QemuRunRequest, resolve_qemu_aarch64, run_in_qemu};
use super::types::{
    CaseCategory, ExpectedLean, FileEntry, PostFileEntry, ProcessE2ESuite, ProgramSummary,
    SyscallCount, VectorCase,
};
use super::{hex_encode, vectors_path};

pub(super) fn file_bytes(path: &str, data: &[u8]) -> FileEntry {
    FileEntry {
        path: path.to_owned(),
        hex: hex_encode(data),
    }
}

fn post_to_initial(entries: &[PostFileEntry]) -> Vec<FileEntry> {
    entries
        .iter()
        .filter(|e| e.exists)
        .map(|e| FileEntry {
            path: e.path.clone(),
            hex: e.hex.clone(),
        })
        .collect()
}

fn find_post_hex<'a>(entries: &'a [PostFileEntry], path: &str) -> Result<&'a str> {
    entries
        .iter()
        .find(|e| e.path == path && e.exists)
        .map(|e| e.hex.as_str())
        .ok_or_else(|| anyhow!("expected post-run file `{path}` to exist"))
}

fn session_dirs() -> Vec<String> {
    vec![
        "identities".into(),
        "sessions".into(),
        "signed-pre-keys".into(),
        "one-time-pre-keys".into(),
        "public".into(),
        "public/signed-pre-keys".into(),
        "public/one-time-pre-keys".into(),
    ]
}

fn deterministic_coins(seed: u8, len: usize) -> Vec<u8> {
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15 ^ ((seed as u64).wrapping_mul(0xbf58_476d_1ce4_e5b9));
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        out.push((state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 56) as u8);
    }
    out
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run_and_record(
    cases: &mut Vec<VectorCase>,
    repo_root: &Path,
    qemu_bin: &Path,
    id: &str,
    program: &str,
    category: CaseCategory,
    args: Vec<&str>,
    envp: Vec<&str>,
    stdin: &[u8],
    pre_dirs: Vec<String>,
    initial_files: Vec<FileEntry>,
    watched_files: Vec<&str>,
    use_ref_runner: bool,
    nondeterministic_stdout: bool,
    normalize_panic_tid: bool,
    expected_lean: ExpectedLean,
) -> Result<()> {
    let elf_rel = format!("Arm64/Testing/ProcessE2E/bin/{program}.elf");
    let elf_abs = repo_root.join(&elf_rel);
    let args_owned: Vec<String> = args.into_iter().map(str::to_owned).collect();
    let envp_owned: Vec<String> = envp.into_iter().map(str::to_owned).collect();
    let watched_owned: Vec<String> = watched_files.into_iter().map(str::to_owned).collect();

    let qemu = run_in_qemu(&QemuRunRequest {
        qemu_bin,
        elf_abs_path: &elf_abs,
        args: &args_owned,
        envp: &envp_owned,
        stdin,
        pre_dirs: &pre_dirs,
        initial_files: &initial_files,
        watched_files: &watched_owned,
        nondeterministic_stdout,
        normalize_panic_tid,
    })
    .with_context(|| format!("failed running QEMU case `{id}`"))?;

    if category == CaseCategory::Match {
        let code = match (qemu.exit_code, qemu.signal) {
            (Some(c), None) => c as u64,
            (None, Some(sig)) => 128 + sig as u64,
            other => bail!(
                "case `{id}` unexpected QEMU (exit_code, signal) = {other:?}"
            ),
        };
        if expected_lean.lean_exit_code != Some(code) {
            bail!(
                "case `{id}` QEMU status {code} != declared expected code {:?}",
                expected_lean.lean_exit_code
            );
        }
    }

    cases.push(VectorCase {
        id: id.to_owned(),
        program: program.to_owned(),
        elf_path: elf_rel,
        category,
        args: args_owned,
        envp: envp_owned,
        stdin_hex: hex_encode(stdin),
        stdin_utf8_preview: if stdin.len() <= 256 {
            std::str::from_utf8(stdin).ok().map(str::to_owned)
        } else {
            None
        },
        pre_dirs,
        initial_files,
        watched_files: watched_owned,
        use_ref_runner,
        qemu,
        expected_lean,
    });
    Ok(())
}

pub(super) fn exited_match(code: u64, notes: &str) -> ExpectedLean {
    ExpectedLean {
        kind: "exited".into(),
        lean_exit_code: Some(code),
        syscall_nr: None,
        syscall_name: None,
        exception_substr: None,
        notes: notes.into(),
    }
}

/// Run all 99 differential cases under `qemu-aarch64`, aggregate per-binary `-strace` censuses,
/// and either write or drift-check `Arm64/Testing/ProcessE2E/expected_vectors.json`.
pub fn regen_or_check_vectors(
    repo_root: &Path,
    rustc_version_override: Option<&str>,
    elf_infos_override: Option<Vec<BuiltElfInfo>>,
    check_only: bool,
) -> Result<ProcessE2ESuite> {
    let (qemu_bin, qemu_version) = resolve_qemu_aarch64(repo_root)?;
    let elf_infos = match elf_infos_override {
        Some(v) => v,
        None => load_checked_in_elf_infos(repo_root)?,
    };

    let rustc_version = if let Some(v) = rustc_version_override {
        v.to_owned()
    } else if let Ok(raw) = fs::read_to_string(vectors_path(repo_root))
        && let Ok(existing) = serde_json::from_str::<ProcessE2ESuite>(&raw)
    {
        existing.rustc_version
    } else {
        let out = std::process::Command::new("rustc")
            .arg("--version")
            .output()
            .context("failed to query `rustc --version`")?;
        String::from_utf8_lossy(&out.stdout).trim().to_owned()
    };

    let mut cases: Vec<VectorCase> = Vec::with_capacity(99);

    // -------------------------------------------------------------------------
    // 1. nostd_minimal (4 cases — all exercised on both fast & reference runElf)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "nostd_minimal/echo_brk",
        "nostd_minimal",
        CaseCategory::Match,
        vec!["nostd_minimal"],
        vec![],
        b"hello from bare _start + brk!\n",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        exited_match(
            0,
            "Custom `_start` grows heap via `SYS_brk`, reads `stdin`, writes `stdout`, and exits 0.",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "nostd_minimal/exit7",
        "nostd_minimal",
        CaseCategory::Match,
        vec!["nostd_minimal", "exit7"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        exited_match(7, "Custom `_start` inspects `argv[1]` and exits with code 7."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "nostd_minimal/stderr",
        "nostd_minimal",
        CaseCategory::Match,
        vec!["nostd_minimal", "stderr"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        exited_match(
            2,
            "Custom `_start` writes distinct payloads to `fd 1` (`stdout`) and `fd 2` (`stderr`) and exits 2.",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "nostd_minimal/meta",
        "nostd_minimal",
        CaseCategory::Match,
        vec!["nostd", "meta", "extra"],
        vec!["A=1", "B=2"],
        b"",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        exited_match(
            0,
            "Verifies raw initial stack `argc` and `envp` pointer array layout from `[SP]`.",
        ),
    )?;

    // -------------------------------------------------------------------------
    // 2. exit_codes (5 cases — including ref runner cross-check on musl crt1.o)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "exit_codes/ok",
        "exit_codes",
        CaseCategory::Match,
        vec!["exit_codes", "ok"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        exited_match(
            0,
            "Stock musl `_start -> __libc_start_main -> main` returning `0` (also cross-checked against reference `Arm64.Process.runElf`).",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "exit_codes/reject",
        "exit_codes",
        CaseCategory::Match,
        vec!["exit_codes", "reject"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(1, "Returns protocol-rejection exit status `1`."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "exit_codes/bad_args",
        "exit_codes",
        CaseCategory::Match,
        vec!["exit_codes"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(2, "Returns invalid-invocation exit status `2`."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "exit_codes/code_42",
        "exit_codes",
        CaseCategory::Match,
        vec!["exit_codes", "code", "42"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(42, "Parses decimal exit status `42` in Rust `std` and exits `42`."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "exit_codes/code_255",
        "exit_codes",
        CaseCategory::Match,
        vec!["exit_codes", "code", "255"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(255, "Parses maximum 8-bit exit status `255` and exits `255`."),
    )?;

    // -------------------------------------------------------------------------
    // 3. echo_cat (3 cases: empty, all 256 raw byte values, multi-page 9 KiB)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "echo_cat/empty",
        "echo_cat",
        CaseCategory::Match,
        vec!["echo_cat"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Empty `stdin` EOF handling in `io::stdin().read_to_end`."),
    )?;
    let all_256_bytes: Vec<u8> = (0u8..=255u8).collect();
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "echo_cat/all_256_raw_bytes",
        "echo_cat",
        CaseCategory::Match,
        vec!["echo_cat"],
        vec![],
        &all_256_bytes,
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Streams all 256 byte values (`0x00..=0xff`, arbitrary non-UTF-8) lossless."),
    )?;
    let multipage_payload: Vec<u8> = (0..9216).map(|i| ((i * 73 + 19) & 0xff) as u8).collect();
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "echo_cat/multipage_9k",
        "echo_cat",
        CaseCategory::Match,
        vec!["echo_cat"],
        vec![],
        &multipage_payload,
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Streams 9,216 bytes across multiple `SYS_read` chunks and `Vec` reallocations.",
        ),
    )?;

    // -------------------------------------------------------------------------
    // 4. word_count (3 cases)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "word_count/empty",
        "word_count",
        CaseCategory::Match,
        vec!["word_count"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Counts `0 0 0` on empty input."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "word_count/prose_lines",
        "word_count",
        CaseCategory::Match,
        vec!["word_count"],
        vec![],
        b"arm64 process semantics\nstatic musl rust\n\tthird line!\n",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Counts lines, whitespace-delimited words, and byte length."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "word_count/no_trailing_newline",
        "word_count",
        CaseCategory::Match,
        vec!["word_count"],
        vec![],
        b"alpha   beta\tgamma",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Counts words cleanly without trailing newline."),
    )?;

    // -------------------------------------------------------------------------
    // 5. argv_envp (3 cases)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "argv_envp/minimal_empty_env",
        "argv_envp",
        CaseCategory::Match,
        vec!["custom-argv0"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Custom `argv[0]` with zero environment variables (`envc=0`)."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "argv_envp/multi_args_and_env",
        "argv_envp",
        CaseCategory::Match,
        vec!["cli-bin", "--flag", "hello world", "", "a=b=c"],
        vec!["ALPHA=1", "BETA=two=2", "EMPTY=", "PATH=/usr/bin"],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Verifies multi-argument `argv` (including spaces and empty arg) and musl `environ`.",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "argv_envp/address_flags",
        "argv_envp",
        CaseCategory::Match,
        vec!["app", "--peer=alice.1", "--count=0"],
        vec!["LANG=C", "MODE=strict"],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Verifies flag-style `argv` and `environ` propagation."),
    )?;

    // -------------------------------------------------------------------------
    // 6. arith_sort (3 cases)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "arith_sort/signed_extremes",
        "arith_sort",
        CaseCategory::Match,
        vec!["arith_sort"],
        vec![],
        b"42 -7 0 9223372036854775807 -9223372036854775808 42 -1 1000000\n",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Sorts signed `i64` extremes (`i64::MIN`/`MAX`), computes `i64`/`i128` sums & FNV-1a.",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "arith_sort/empty_whitespace",
        "arith_sort",
        CaseCategory::Match,
        vec!["arith_sort"],
        vec![],
        b"   \n\t  \n",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Empty integer list boundary check."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "arith_sort/malformed_token_stderr",
        "arith_sort",
        CaseCategory::Match,
        vec!["arith_sort"],
        vec![],
        b"10 20 not_an_int 30\n",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(2, "Writes diagnostic to `stderr` (`fd 2`) and returns exit code `2`."),
    )?;

    // -------------------------------------------------------------------------
    // 7. btreemap_vec (2 cases: brk-only and brk + anonymous mmap/munmap)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "btreemap_vec/brk_only",
        "btreemap_vec",
        CaseCategory::Match,
        vec!["btreemap_vec", "40"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Hashbrown-free `BTreeMap<String, Vec<u8>>` split/merge/range workload over `SYS_brk`.",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "btreemap_vec/brk_plus_mmap_munmap",
        "btreemap_vec",
        CaseCategory::Match,
        vec!["btreemap_vec", "64", "mmap"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Allocates & unmaps a 32 KiB buffer via `SYS_mmap` + `SYS_munmap` plus 64-entry `BTreeMap`.",
        ),
    )?;

    // -------------------------------------------------------------------------
    // 8. stderr_stdio (2 cases)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "stderr_stdio/interleaved",
        "stderr_stdio",
        CaseCategory::Match,
        vec!["stderr_stdio", "interleave"],
        vec![],
        b"first\nsecond\nthird\nfourth\nfifth\n",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(0, "Interleaves flushed `stdout` (`fd 1`) and `stderr` (`fd 2`) writes."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "stderr_stdio/fail_stderr",
        "stderr_stdio",
        CaseCategory::Match,
        vec!["stderr_stdio", "fail-stderr"],
        vec![],
        b"corrupted-wire-blob",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(1, "Emits error message solely to `stderr` (`stdout` empty) and exits `1`."),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "stderr_stdio/panic_formatted",
        "stderr_stdio",
        CaseCategory::UnmodeledTrap,
        vec!["stderr_stdio", "panic-fmt"],
        vec![],
        b"payload-bytes",
        vec![],
        vec![],
        vec![],
        false,
        false,
        true,
        ExpectedLean {
            kind: "exception".into(),
            lean_exit_code: None,
            syscall_nr: Some(135),
            syscall_name: Some("rt_sigprocmask".into()),
            exception_substr: Some("unmodeled non-zero signal mask in rt_sigprocmask".into()),
            notes: "Heap-allocated formatted `panic!(...)` emits the message on `stderr` and calls musl `abort()` -> `raise(SIGABRT)` -> `rt_sigprocmask(SIG_BLOCK, &app_mask, ...)` (`135`), which fails closed with `.Exception` on non-zero signal masks.".into(),
        },
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "stderr_stdio/abort_after_stdout",
        "stderr_stdio",
        CaseCategory::UnmodeledTrap,
        vec!["stderr_stdio", "abort-flush"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        ExpectedLean {
            kind: "exception".into(),
            lean_exit_code: None,
            syscall_nr: Some(135),
            syscall_name: Some("rt_sigprocmask".into()),
            exception_substr: Some("unmodeled non-zero signal mask in rt_sigprocmask".into()),
            notes: "Flushes `\"before-abort\\n\"` to `stdout` under `BrkMmapAlloc`, then calls `std::process::abort()` -> musl `raise(SIGABRT)` -> `rt_sigprocmask(SIG_BLOCK, &app_mask, ...)` (`135`), which fails closed with `.Exception` on non-zero signal masks.".into(),
        },
    )?;

    // -------------------------------------------------------------------------
    // 9. getrandom_use (2 cases: deterministic conformance + live/oracle raw hex)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "getrandom_use/conformance_check",
        "getrandom_use",
        CaseCategory::Match,
        vec!["getrandom_use", "check"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Verifies `SYS_getrandom` return codes for `0`, `GRND_NONBLOCK`, `len=0`, `-EINVAL`, and `-EFAULT`.",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "getrandom_use/raw_hex",
        "getrandom_use",
        CaseCategory::EntropyNondeterministic,
        vec!["getrandom_use", "raw-hex"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        true,
        false,
        exited_match(
            0,
            "QEMU reads live host OS entropy (32 hex chars + newline); Lean replays both default zero `Oracle` and seeded custom `Oracle.getrandom`.",
        ),
    )?;

    // -------------------------------------------------------------------------
    // 10. session_store (11 cases: full multi-step protocol + VFS divergences)
    // -------------------------------------------------------------------------
    let alice_watched = vec![
        "address",
        "identity-key-pair",
        "registration-id",
        "signed-pre-keys/1",
        "one-time-pre-keys/1",
        "one-time-pre-keys/2",
        "public/identity-key",
        "public/registration-id",
        "public/signed-pre-keys/1",
        "public/one-time-pre-keys/1",
        "public/one-time-pre-keys/2",
    ];
    let coins_alice = deterministic_coins(0x11, 192);
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/keygen_alice",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "keygen", "alice.1", "2"],
        vec![],
        b"UNREAD_STDIN_ON_KEYGEN",
        session_dirs(),
        vec![file_bytes("coins", &coins_alice)],
        alice_watched,
        false,
        false,
        false,
        exited_match(
            0,
            "`keygen alice.1 2` reads `coins` in order, ignores `stdin`, and writes 11 private/public key files across relative subdirectories.",
        ),
    )?;
    let alice_store_after_keygen = post_to_initial(&cases.last().unwrap().qemu.post_files);

    let bob_watched = vec![
        "address",
        "identity-key-pair",
        "registration-id",
        "signed-pre-keys/1",
        "one-time-pre-keys/1",
        "public/identity-key",
        "public/registration-id",
        "public/signed-pre-keys/1",
        "public/one-time-pre-keys/1",
    ];
    let coins_bob = deterministic_coins(0x22, 160);
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/keygen_bob",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "keygen", "bob.1", "1"],
        vec![],
        b"",
        session_dirs(),
        vec![file_bytes("coins", &coins_bob)],
        bob_watched,
        false,
        false,
        false,
        exited_match(
            0,
            "`keygen bob.1 1` initializes Bob's store and public pre-key bundle.",
        ),
    )?;
    let bob_post_keygen = cases.last().unwrap().qemu.post_files.clone();
    let bob_store_after_keygen = post_to_initial(&bob_post_keygen);

    let bob_id_hex = find_post_hex(&bob_post_keygen, "public/identity-key")?.to_owned();
    let bob_reg_hex = find_post_hex(&bob_post_keygen, "public/registration-id")?.to_owned();
    let bob_spk_hex = find_post_hex(&bob_post_keygen, "public/signed-pre-keys/1")?.to_owned();
    let bob_opk_hex = find_post_hex(&bob_post_keygen, "public/one-time-pre-keys/1")?.to_owned();

    // Case 10c: Corrupted bundle signature must return exit 1 AND leave zero files touched!
    let mut bad_bundle_init_files = alice_store_after_keygen.clone();
    bad_bundle_init_files.push(file_bytes("coins", &deterministic_coins(0x33, 64)));
    bad_bundle_init_files.push(FileEntry {
        path: "bundle/identity-key".into(),
        hex: bob_id_hex.clone(),
    });
    bad_bundle_init_files.push(FileEntry {
        path: "bundle/registration-id".into(),
        hex: bob_reg_hex.clone(),
    });
    let mut corrupted_spk = super::hex_decode(&bob_spk_hex)?;
    *corrupted_spk.last_mut().unwrap() ^= 0xff;
    bad_bundle_init_files.push(file_bytes("bundle/signed-pre-key", &corrupted_spk));
    bad_bundle_init_files.push(FileEntry {
        path: "bundle/one-time-pre-key".into(),
        hex: bob_opk_hex.clone(),
    });
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/init_bad_bundle_atomic",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "init", "bob.1", "bundle"],
        vec![],
        b"",
        session_dirs(),
        bad_bundle_init_files,
        vec!["identities/bob", "sessions/bob.1"],
        false,
        false,
        false,
        exited_match(
            1,
            "Invalid pre-key signature returns `exit 1` (`Rejected`) and drops all staged `BTreeMap` mutations without creating `identities/bob` or `sessions/bob.1`.",
        ),
    )?;

    // Case 10d: Valid `init bob.1 bundle` on Alice's store
    let mut valid_init_files = alice_store_after_keygen;
    valid_init_files.push(file_bytes("coins", &deterministic_coins(0x33, 64)));
    valid_init_files.push(FileEntry {
        path: "bundle/identity-key".into(),
        hex: bob_id_hex,
    });
    valid_init_files.push(FileEntry {
        path: "bundle/registration-id".into(),
        hex: bob_reg_hex,
    });
    valid_init_files.push(FileEntry {
        path: "bundle/signed-pre-key".into(),
        hex: bob_spk_hex,
    });
    valid_init_files.push(FileEntry {
        path: "bundle/one-time-pre-key".into(),
        hex: bob_opk_hex,
    });
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/init_alice_to_bob",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "init", "bob.1", "bundle"],
        vec![],
        b"UNREAD_STDIN_ON_INIT",
        session_dirs(),
        valid_init_files,
        vec![
            "address",
            "identity-key-pair",
            "identities/bob",
            "sessions/bob.1",
        ],
        false,
        false,
        false,
        exited_match(
            0,
            "Valid bundle initializes `identities/bob` and 77-byte session record `sessions/bob.1` while ignoring `stdin`.",
        ),
    )?;
    let alice_store_after_init = post_to_initial(&cases.last().unwrap().qemu.post_files);

    // Case 10e: Alice encrypts first message (`send bob.1`)
    let mut alice_send_files = alice_store_after_init;
    alice_send_files.push(file_bytes("coins", &deterministic_coins(0x44, 32)));
    let plaintext = b"Meet at dawn -- stateful prekey session test\n";
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/send_alice_to_bob",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "send", "bob.1"],
        vec![],
        plaintext,
        session_dirs(),
        alice_send_files,
        vec!["sessions/bob.1"],
        false,
        false,
        false,
        exited_match(
            0,
            "Encrypts `stdin` into authenticated PreKey wire message on `stdout` and advances `tx_cnt` in `sessions/bob.1`.",
        ),
    )?;
    let wire_ciphertext = super::hex_decode(&cases.last().unwrap().qemu.stdout_hex)?;

    // Case 10f: Bob decrypts PreKey message (`recv alice.1`) and empties `one-time-pre-keys/1`!
    let mut bob_recv_files = bob_store_after_keygen;
    bob_recv_files.push(file_bytes("coins", &deterministic_coins(0x55, 32)));
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/recv_bob_from_alice",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "recv", "alice.1"],
        vec![],
        &wire_ciphertext,
        session_dirs(),
        bob_recv_files,
        vec![
            "address",
            "identity-key-pair",
            "signed-pre-keys/1",
            "one-time-pre-keys/1",
            "identities/alice",
            "sessions/alice.1",
        ],
        false,
        false,
        false,
        exited_match(
            0,
            "Decrypts wire message to exact plaintext on `stdout`, creates `sessions/alice.1`, and truncates consumed `one-time-pre-keys/1` to `0` bytes (`O_TRUNC`).",
        ),
    )?;
    let bob_store_after_recv = post_to_initial(&cases.last().unwrap().qemu.post_files);

    // Case 10g: Replay of consumed PreKey message is rejected (`exit 1`) because `one-time-pre-keys/1` is 0 bytes!
    let mut bob_replay_files = bob_store_after_recv;
    bob_replay_files.push(file_bytes("coins", &deterministic_coins(0x66, 32)));
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/recv_replay_rejected",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "recv", "alice.1"],
        vec![],
        &wire_ciphertext,
        session_dirs(),
        bob_replay_files,
        vec!["one-time-pre-keys/1", "sessions/alice.1"],
        false,
        false,
        false,
        exited_match(
            1,
            "Replayed PreKey message sees 0-byte `one-time-pre-keys/1`, returns `exit 1` (`Rejected`), and leaves `sessions/alice.1` unchanged.",
        ),
    )?;

    // Case 10h: Invalid CLI invocation -> exit 2
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/bad_cli_args",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "invalid-subcommand"],
        vec![],
        b"",
        session_dirs(),
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(2, "Malformed CLI arguments return exit status `2`."),
    )?;

    // Case 10i: Missing `coins` file -> exit 2
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/missing_coins",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "keygen", "alice.1", "1"],
        vec![],
        b"",
        session_dirs(),
        vec![],
        vec!["address"],
        false,
        false,
        false,
        exited_match(
            2,
            "Missing `coins` file fails `openat` with `-ENOENT` and returns exit status `2` without committing files.",
        ),
    )?;

    // Case 10j: Missing parent directory on `openat(..., O_CREAT)` returns `-ENOENT` (`exit 2`)!
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/missing_parent_dir_divergence",
        "session_store",
        CaseCategory::Match,
        vec!["session_store", "keygen", "alice.1", "1"],
        vec![],
        b"",
        vec![], // NO pre-created subdirectories!
        vec![file_bytes("coins", &coins_alice)],
        vec!["signed-pre-keys/1"],
        false,
        false,
        false,
        exited_match(
            2,
            "`openat(AT_FDCWD, \"signed-pre-keys/1\", O_WRONLY|O_CREAT|O_TRUNC, 0666)` returns `-ENOENT` when parent directory `signed-pre-keys/` is absent (`exit 2`, file not created).",
        ),
    )?;

    // Case 10k: Non-canonical `./coins` path normalization in `resolveAtPath` (`exit 0`)!
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "session_store/dot_slash_coins_divergence",
        "session_store",
        CaseCategory::Match,
        vec![
            "session_store",
            "--coins",
            "./coins",
            "keygen",
            "alice.1",
            "1",
        ],
        vec![],
        b"",
        session_dirs(),
        vec![file_bytes("coins", &coins_alice)],
        vec!["address"],
        false,
        false,
        false,
        exited_match(
            0,
            "`openat(AT_FDCWD, \"./coins\", O_RDONLY)` normalizes `./coins` -> `coins` in `resolveAtPath` and writes store keys identically (`exit 0`).",
        ),
    )?;

    // -------------------------------------------------------------------------
    // 11. std_startup_probe (1 case: full Rust `fn main()` runtime startup)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "std_startup_probe/lang_start",
        "std_startup_probe",
        CaseCategory::Match,
        vec!["std_startup_probe", "hello"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        exited_match(
            0,
            "Full Rust `std::rt::lang_start` executes `set_tid_address` (`96`), `ppoll` (`73`), `rt_sigaction` (`134`), `mmap` `MAP_STACK` (`222`), `mprotect` (`226`), `sigaltstack` (`132`), `write` (`64`), `munmap` (`215`), and `exit_group(0)` (`94`) identically to QEMU (`exit 0`).",
        ),
    )?;

    // -------------------------------------------------------------------------
    // 12. unmodified_std_probe (7 cases: stock std::fs, mallocng, panic, abort, brk/udf)
    // -------------------------------------------------------------------------
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/fs_fcntl_cloexec",
        "unmodified_std_probe",
        CaseCategory::Match,
        vec!["unmodified_std_probe", "fs"],
        vec![],
        b"",
        vec![],
        vec![file_bytes("coins", b"0123456789abcdef")],
        vec!["out"],
        true,
        false,
        false,
        exited_match(
            0,
            "Stock `std::fs::File::open(\"coins\")` + `Read::read` + `std::fs::File::create(\"out\")` + `Write::write_all` (with zero custom allocator or shims) succeeds via modeled `openat(..., O_CLOEXEC)` + `fcntl(fd, F_SETFD, FD_CLOEXEC)` -> `0` (`exit 0`, also verified by reference `Arm64.Process.runElf`; note that `std::fs::read` on stock musl subsequently invokes `mallocng`'s deferred `mmap(MAP_FIXED)` unless a `brk`/`mmap` allocator is installed as in `session_store`).",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/mallocng_guard_page",
        "unmodified_std_probe",
        CaseCategory::Match,
        vec!["unmodified_std_probe", "malloc"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        exited_match(
            0,
            "Stock musl `mallocng` extends `brk` by 2 pages then installs a guard page via `mmap(addr, 4096, PROT_NONE (0), MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED (0x32), -1, 0)`; Lean `execMmap` models the `MAP_FIXED` + `PROT_NONE` guard page (exit `0`).",
        ),
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/panic_gettid",
        "unmodified_std_probe",
        CaseCategory::UnmodeledTrap,
        vec!["unmodified_std_probe", "panic"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        true,
        ExpectedLean {
            kind: "exception".into(),
            lean_exit_code: None,
            syscall_nr: Some(135),
            syscall_name: Some("rt_sigprocmask".into()),
            exception_substr: Some("unmodeled non-zero signal mask in rt_sigprocmask".into()),
            notes: "`panic!(...)` queries `gettid` (`178` -> `SIM_TID = 1`), writes the panic message to `stderr`, and calls musl `abort()` -> `raise(SIGABRT)` -> `rt_sigprocmask(SIG_BLOCK, &app_mask, ...)` (`135`), which fails closed with `.Exception` on non-zero signal masks.".into(),
        },
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/abort_sigabrt",
        "unmodified_std_probe",
        CaseCategory::UnmodeledTrap,
        vec!["unmodified_std_probe", "abort"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        true,
        false,
        false,
        ExpectedLean {
            kind: "exception".into(),
            lean_exit_code: None,
            syscall_nr: Some(135),
            syscall_name: Some("rt_sigprocmask".into()),
            exception_substr: Some("unmodeled non-zero signal mask in rt_sigprocmask".into()),
            notes: "`std::process::abort()` calls musl `abort()` -> `raise(SIGABRT)` -> `rt_sigprocmask(SIG_BLOCK, &app_mask, ...)` (`135`), which fails closed with `.Exception` on non-zero signal masks.".into(),
        },
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/udf_sigill",
        "unmodified_std_probe",
        CaseCategory::Divergence,
        vec!["unmodified_std_probe", "udf"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        ExpectedLean {
            kind: "halted".into(),
            lean_exit_code: None,
            syscall_nr: None,
            syscall_name: None,
            exception_substr: None,
            notes: "`asm!(\"udf #0\")` (`0x00000000`, emitted by `core::intrinsics::abort`) raises `SIGILL` (`signal = 4`) on Linux/QEMU, whereas `Decode.lean` maps `0x00000000` to `none` -> `.Halted` (`out? = none`, distinct from `.Exception \"udf\"`).".into(),
        },
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/udf1_sigill",
        "unmodified_std_probe",
        CaseCategory::UnmodeledTrap,
        vec!["unmodified_std_probe", "udf1"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        ExpectedLean {
            kind: "exception".into(),
            lean_exit_code: None,
            syscall_nr: None,
            syscall_name: None,
            exception_substr: Some("udf".into()),
            notes: "`asm!(\"udf #1\")` (`0x00000001`, non-zero `UDF #imm16`) raises `SIGILL` (`signal = 4`) on Linux/QEMU and decodes to `.udf 1` -> fail-closed `.Exception \"udf\"` in Lean.".into(),
        },
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/brk1_divergence",
        "unmodified_std_probe",
        CaseCategory::Divergence,
        vec!["unmodified_std_probe", "brk1"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        ExpectedLean {
            kind: "exited".into(),
            lean_exit_code: Some(101),
            syscall_nr: None,
            syscall_name: None,
            exception_substr: None,
            notes: "ISA/Process divergence: `asm!(\"brk #1\")` terminates abnormally with `SIGTRAP` (`signal = 5`) on Linux/QEMU, whereas `Eval.lean` transitions `BRK #1` to `.Exited 101#64` (treated by `runElf` / `ProcessExitsWith` as clean exit code `101`).".into(),
        },
    )?;
    run_and_record(
        &mut cases,
        repo_root,
        &qemu_bin,
        "unmodified_std_probe/brk0_halt",
        "unmodified_std_probe",
        CaseCategory::Divergence,
        vec!["unmodified_std_probe", "brk0"],
        vec![],
        b"",
        vec![],
        vec![],
        vec![],
        false,
        false,
        false,
        ExpectedLean {
            kind: "halted".into(),
            lean_exit_code: None,
            syscall_nr: None,
            syscall_name: None,
            exception_substr: None,
            notes: "`asm!(\"brk #0\")` terminates with `SIGTRAP` (`signal = 5`) on Linux/QEMU and transitions to `.Halted` (`out? = none`, distinct from `.Exception`) in Lean.".into(),
        },
    )?;

    // -------------------------------------------------------------------------
    // 13-26. Workload binaries (`base64_codec` .. `collatz_stats`), all `match`.
    // -------------------------------------------------------------------------
    record_workload_cases(&mut cases, repo_root, &qemu_bin)?;

    // Build per-program summaries with aggregated `-strace` syscall counts.
    let mut programs = Vec::with_capacity(elf_infos.len());
    for info in &elf_infos {
        let mut agg: BTreeMap<String, SyscallCount> = BTreeMap::new();
        for c in cases.iter().filter(|c| c.program == info.spec.name) {
            for sc in &c.qemu.syscalls {
                let entry = agg.entry(sc.name.clone()).or_insert_with(|| SyscallCount {
                    name: sc.name.clone(),
                    nr: sc.nr,
                    modeled: sc.modeled,
                    calls: 0,
                });
                entry.calls += sc.calls;
            }
        }
        let mut syscalls_observed: Vec<SyscallCount> = agg.into_values().collect();
        syscalls_observed.sort_by(|a, b| {
            a.nr.unwrap_or(u32::MAX)
                .cmp(&b.nr.unwrap_or(u32::MAX))
                .then_with(|| a.name.cmp(&b.name))
        });

        programs.push(ProgramSummary {
            name: info.spec.name.to_owned(),
            source: info.source_rel.clone(),
            elf_path: info.elf_rel.clone(),
            size_bytes: info.size_bytes,
            sha256: info.sha256.clone(),
            entry_va: format!("0x{:016x}", info.entry_va),
            runtime_flavor: info.spec.runtime_flavor.to_owned(),
            description: info.spec.description.to_owned(),
            syscalls_observed,
        });
    }

    let suite = ProcessE2ESuite {
        schema_version: 1,
        qemu_version,
        rustc_version,
        target_triple: "aarch64-unknown-linux-musl".into(),
        programs,
        cases,
    };

    let mut rendered = serde_json::to_string_pretty(&suite)?;
    rendered.push('\n');
    let out_path = vectors_path(repo_root);

    if check_only {
        let existing = fs::read_to_string(&out_path).with_context(|| {
            format!(
                "missing committed vectors file {} (run `./scripts/process-e2e regen`)",
                out_path.display()
            )
        })?;
        if existing != rendered {
            bail!(
                "{} is out of date with live QEMU execution (run `./scripts/process-e2e regen` to update)",
                out_path.display()
            );
        }
    } else {
        fs::write(&out_path, rendered)?;
    }

    Ok(suite)
}
