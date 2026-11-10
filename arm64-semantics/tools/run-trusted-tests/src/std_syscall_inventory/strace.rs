// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Isolated `qemu-aarch64` scenario runner and fail-closed `-strace` log parser (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted host audit infrastructure under
//!   `tools/run-trusted-tests`).
//! - **Purpose:** Execute static AArch64 ELF binaries under `qemu-aarch64` inside fresh temporary
//!   working directories (with declarative `stdin` payloads, initial files, and closed standard
//!   file descriptors `0..=2` via POSIX `sh` redirections using zero `unsafe` Rust code), and
//!   strictly parse every `-strace` log line into canonical Linux AArch64 syscall numbers.
//!
//! # Key Types & Functions
//! - [`DataKind`]: Declarative byte-stream generator (`empty`, `literal`, `hex`, `repeat_lines`,
//!   `long_line`, `repeat_byte`).
//! - [`ParsedStrace`] / [`SyscallRun`]: Host-independent parsed trace (no PIDs, pointers, or paths).
//! - [`parse_qemu_strace_strict`]: Fail-closed strace parser rejecting unknown or malformed lines.
//! - [`run_scenario_in_qemu`]: Execute one scenario, check exit code and required syscalls, and
//!   return its [`ParsedStrace`].

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::os::unix::process::ExitStatusExt;
use std::path::{Component, Path};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, anyhow, bail};
use serde::{Deserialize, Serialize};

use crate::process_e2e::hex_decode;
use crate::process_e2e::types::{aarch64_syscall_info, aarch64_syscall_name};

fn default_fill_char() -> char {
    'a'
}

fn default_true() -> bool {
    true
}

/// Declarative byte payload specification for scenario `stdin` or initial working-directory files.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DataKind {
    /// Zero-byte input (`"empty"`).
    Empty,
    /// Literal UTF-8 text (`{ "literal": "..." }`).
    Literal(String),
    /// Hexadecimal byte string (`{ "hex": "..." }`).
    Hex(String),
    /// Cycle `lines` (substituting `{i}` with the 0-based line index when present and appending
    /// `'\n'` if absent) until reaching at least `target_bytes`.
    RepeatLines {
        lines: Vec<String>,
        target_bytes: usize,
    },
    /// Single ASCII/UTF-8 line of `len` bytes followed by an optional `'\n'`.
    LongLine {
        len: usize,
        #[serde(default = "default_fill_char")]
        byte: char,
        #[serde(default = "default_true")]
        trailing_newline: bool,
    },
    /// Repeat a single raw byte `len` times (`{ "repeat_byte": { "byte": 65, "len": 4096 } }`).
    RepeatByte {
        byte: u8,
        len: usize,
    },
}

impl Default for DataKind {
    fn default() -> Self {
        Self::Empty
    }
}

impl DataKind {
    /// Deterministically materialize the byte payload in memory.
    pub fn materialize(&self) -> Result<Vec<u8>> {
        match self {
            Self::Empty => Ok(Vec::new()),
            Self::Literal(s) => Ok(s.as_bytes().to_vec()),
            Self::Hex(h) => hex_decode(h),
            Self::RepeatLines {
                lines,
                target_bytes,
            } => {
                if *target_bytes == 0 {
                    return Ok(Vec::new());
                }
                if lines.is_empty() {
                    bail!("`repeat_lines` requires at least one template line when target_bytes > 0");
                }
                let mut buf = Vec::with_capacity(*target_bytes + 128);
                let mut idx = 0usize;
                while buf.len() < *target_bytes {
                    let tmpl = &lines[idx % lines.len()];
                    if tmpl.contains("{i}") {
                        let rendered = tmpl.replace("{i}", &idx.to_string());
                        buf.extend_from_slice(rendered.as_bytes());
                        if !rendered.ends_with('\n') {
                            buf.push(b'\n');
                        }
                    } else {
                        buf.extend_from_slice(tmpl.as_bytes());
                        if !tmpl.ends_with('\n') {
                            buf.push(b'\n');
                        }
                    }
                    idx += 1;
                }
                Ok(buf)
            }
            Self::LongLine {
                len,
                byte,
                trailing_newline,
            } => {
                let mut buf = Vec::with_capacity(len.saturating_add(usize::from(*trailing_newline)));
                if byte.len_utf8() == 1 {
                    buf.resize(*len, *byte as u8);
                } else {
                    let mut encoded = [0u8; 4];
                    let slice = byte.encode_utf8(&mut encoded).as_bytes();
                    while buf.len() < *len {
                        let rem = *len - buf.len();
                        buf.extend_from_slice(&slice[..rem.min(slice.len())]);
                    }
                }
                if *trailing_newline {
                    buf.push(b'\n');
                }
                Ok(buf)
            }
            Self::RepeatByte { byte, len } => Ok(vec![*byte; *len]),
        }
    }
}

/// Declarative file created in a scenario's isolated working directory before launching QEMU.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SetupFileSpec {
    pub rel_path: String,
    pub content_kind: DataKind,
}

/// Run-length compressed consecutive invocations of a single syscall in a dynamic trace.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyscallRun {
    pub nr: u64,
    pub name: String,
    pub calls: usize,
}

/// Host-independent parsed `qemu-aarch64 -strace` output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedStrace {
    pub total_calls: usize,
    /// Distinct syscalls sorted ascending by `(nr, name)` as `(nr, canonical_name, call_count)`.
    pub distinct_counts: Vec<(u64, String, usize)>,
    /// Run-length compressed call sequence preserving execution order without PIDs or pointers.
    pub ordered_runs: Vec<SyscallRun>,
}

/// Parse a `qemu-aarch64` strace log strictly, failing closed on any unknown or unparseable line.
pub fn parse_qemu_strace_strict(trace: &str) -> Result<ParsedStrace> {
    let mut counts: BTreeMap<u64, (String, usize)> = BTreeMap::new();
    let mut ordered_runs: Vec<SyscallRun> = Vec::new();
    let mut total_calls = 0usize;

    for (idx, raw_line) in trace.lines().enumerate() {
        let line_no = idx + 1;
        let line = raw_line.trim_start();
        if line.is_empty() {
            continue;
        }

        let pid_len = line.bytes().take_while(|b| b.is_ascii_digit()).count();
        if pid_len == 0 {
            bail!(
                "fail-closed strace parser: malformed non-syscall line {line_no} in QEMU strace: {raw_line:?}"
            );
        }
        let rest = &line[pid_len..];
        let Some(after_space) = rest.strip_prefix(' ') else {
            bail!(
                "fail-closed strace parser: missing space after PID at line {line_no}: {raw_line:?}"
            );
        };
        if after_space.starts_with("Unknown syscall ") {
            bail!(
                "fail-closed strace parser: QEMU reported unknown syscall at line {line_no}: {raw_line:?}"
            );
        }
        let Some(paren_idx) = after_space.find('(') else {
            bail!(
                "fail-closed strace parser: missing `(` in strace entry at line {line_no}: {raw_line:?}"
            );
        };
        let raw_name = &after_space[..paren_idx];
        let valid_ident = !raw_name.is_empty()
            && raw_name
                .bytes()
                .next()
                .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
            && raw_name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_');
        if !valid_ident {
            bail!(
                "fail-closed strace parser: invalid syscall identifier `{raw_name}` at line {line_no}: {raw_line:?}"
            );
        }

        let (Some(nr_u32), _) = aarch64_syscall_info(raw_name) else {
            bail!(
                "fail-closed strace parser: unrecognized AArch64 syscall `{raw_name}` at line {line_no}: {raw_line:?}"
            );
        };
        let nr = u64::from(nr_u32);
        let canonical = aarch64_syscall_name(nr).unwrap_or(raw_name).to_owned();

        total_calls += 1;
        counts
            .entry(nr)
            .and_modify(|(_, c)| *c += 1)
            .or_insert_with(|| (canonical.clone(), 1));

        if let Some(last) = ordered_runs.last_mut()
            && last.nr == nr
        {
            last.calls += 1;
        } else {
            ordered_runs.push(SyscallRun {
                nr,
                name: canonical,
                calls: 1,
            });
        }
    }

    let distinct_counts = counts
        .into_iter()
        .map(|(nr, (name, calls))| (nr, name, calls))
        .collect();

    Ok(ParsedStrace {
        total_calls,
        distinct_counts,
        ordered_runs,
    })
}

fn validate_safe_rel_path(rel: &str) -> Result<()> {
    let p = Path::new(rel);
    if rel.is_empty() || p.is_absolute() {
        bail!("setup_files rel_path must be a non-empty relative path, got {rel:?}");
    }
    for comp in p.components() {
        match comp {
            Component::Normal(_) | Component::CurDir => {}
            _ => bail!("setup_files rel_path must not escape working directory: {rel:?}"),
        }
    }
    Ok(())
}

/// Parameters for executing a single dynamic scenario under `qemu-aarch64`.
pub struct ScenarioRunParams<'a> {
    pub scenario_id: &'a str,
    pub bin_id: &'a str,
    pub qemu_bin: &'a Path,
    pub elf_abs_path: &'a Path,
    pub argv0: &'a str,
    pub args: &'a [String],
    pub envp: &'a [String],
    pub stdin_kind: &'a DataKind,
    pub setup_files: &'a [SetupFileSpec],
    pub closed_fds: &'a [i32],
    pub expect_exit: i32,
    pub require_dynamic_syscalls: &'a [u64],
}

/// Outcome of executing one scenario under `qemu-aarch64`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicScenarioRun {
    pub exit_code: i32,
    pub parsed: ParsedStrace,
}

/// Normalize and validate `closed_fds` (`⊆ {0, 1, 2}`).
pub fn normalize_closed_fds(raw: &[i32]) -> Result<Vec<i32>> {
    let mut out = Vec::with_capacity(raw.len());
    for &fd in raw {
        if !(0..=2).contains(&fd) {
            bail!("closed_fds entries must be in 0..=2, got {fd}");
        }
        out.push(fd);
    }
    out.sort_unstable();
    out.dedup();
    Ok(out)
}

/// Execute `params` inside a fresh temporary directory and capture its strict QEMU `-strace`.
pub fn run_scenario_in_qemu(params: &ScenarioRunParams<'_>) -> Result<DynamicScenarioRun> {
    let closed_fds = normalize_closed_fds(params.closed_fds)?;

    let work_tmp = tempfile::TempDir::new().context("failed to create scenario working TempDir")?;
    let trace_tmp = tempfile::TempDir::new().context("failed to create scenario strace TempDir")?;
    let strace_path = trace_tmp.path().join("qemu.strace");
    let stdin_path = trace_tmp.path().join("stdin.bin");

    for sf in params.setup_files {
        validate_safe_rel_path(&sf.rel_path)?;
        let dst = work_tmp.path().join(&sf.rel_path);
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent)?;
        }
        let bytes = sf.content_kind.materialize().with_context(|| {
            format!(
                "failed to materialize setup file `{}` for scenario `{}`",
                sf.rel_path, params.scenario_id
            )
        })?;
        fs::write(&dst, &bytes)?;
    }

    let stdin_bytes = params
        .stdin_kind
        .materialize()
        .with_context(|| format!("failed to materialize stdin for scenario `{}`", params.scenario_id))?;
    fs::write(&stdin_path, &stdin_bytes)?;

    let stdin_stdio = if closed_fds.contains(&0) {
        Stdio::null()
    } else {
        Stdio::from(File::open(&stdin_path)?)
    };

    let mut cmd = if closed_fds.is_empty() {
        let mut c = Command::new(params.qemu_bin);
        c.stdin(stdin_stdio)
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .arg("-0")
            .arg(params.argv0)
            .arg("-D")
            .arg(&strace_path)
            .arg("-strace")
            .arg(params.elf_abs_path)
            .args(params.args);
        c
    } else if !closed_fds.contains(&2) {
        // When `fd 2` stays open while `fd 0` and/or `fd 1` are closed, omit `-D` and attach
        // `strace_path` directly to `fd 2`: `qemu-aarch64 -strace` writes to `fd 2` without
        // calling `open()`, ensuring `fd 0`/`fd 1` remain genuinely closed (`POLLNVAL`) in the
        // shared user-mode descriptor table instead of being claimed by QEMU's `-D` log file.
        let mut redirects = String::new();
        for &fd in &closed_fds {
            if !redirects.is_empty() {
                redirects.push(' ');
            }
            if fd == 0 {
                redirects.push_str("0<&-");
            } else {
                redirects.push_str(&format!("{fd}>&-"));
            }
        }
        let script = format!("exec {redirects}; exec \"$@\"");
        let log_file = File::create(&strace_path)?;
        let mut c = Command::new("sh");
        c.stdin(stdin_stdio)
            .stdout(Stdio::null())
            .stderr(Stdio::from(log_file))
            .arg("-c")
            .arg(script)
            .arg("--")
            .arg(params.qemu_bin)
            .arg("-0")
            .arg(params.argv0)
            .arg("-strace")
            .arg(params.elf_abs_path)
            .args(params.args);
        c
    } else {
        // When `fd 2` is closed, pass `-D <strace_path> -strace` and close requested descriptors
        // via POSIX `sh` before `exec`ing `qemu-aarch64` (zero `unsafe` host code).
        let mut redirects = String::new();
        for &fd in &closed_fds {
            if !redirects.is_empty() {
                redirects.push(' ');
            }
            if fd == 0 {
                redirects.push_str("0<&-");
            } else {
                redirects.push_str(&format!("{fd}>&-"));
            }
        }
        let script = format!("exec {redirects}; exec \"$@\"");
        let mut c = Command::new("sh");
        c.stdin(stdin_stdio)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .arg("-c")
            .arg(script)
            .arg("--")
            .arg(params.qemu_bin)
            .arg("-0")
            .arg(params.argv0)
            .arg("-D")
            .arg(&strace_path)
            .arg("-strace")
            .arg(params.elf_abs_path)
            .args(params.args);
        c
    };

    cmd.current_dir(work_tmp.path()).env_clear();
    for entry in params.envp {
        let (k, v) = entry
            .split_once('=')
            .ok_or_else(|| anyhow!("envp entry missing '=': {entry:?}"))?;
        cmd.env(k, v);
    }

    let output = cmd.output().with_context(|| {
        format!(
            "failed to execute QEMU scenario `{}` (`{}`)",
            params.scenario_id,
            params.elf_abs_path.display()
        )
    })?;

    if let Some(sig) = output.status.signal() {
        bail!(
            "scenario `{}` (binary `{}`) terminated by signal {sig} (expected exit code {})",
            params.scenario_id,
            params.bin_id,
            params.expect_exit
        );
    }
    let exit_code = output.status.code().ok_or_else(|| {
        anyhow!(
            "scenario `{}` (binary `{}`) exited without status code",
            params.scenario_id,
            params.bin_id
        )
    })?;
    if exit_code != params.expect_exit {
        let stderr_preview = String::from_utf8_lossy(&output.stderr);
        bail!(
            "scenario `{}` (binary `{}`) exited with code {exit_code}, expected {} (stderr: {:?})",
            params.scenario_id,
            params.bin_id,
            params.expect_exit,
            stderr_preview
        );
    }

    let strace_raw = fs::read_to_string(&strace_path).with_context(|| {
        format!(
            "missing QEMU strace output file for scenario `{}`",
            params.scenario_id
        )
    })?;
    let parsed = parse_qemu_strace_strict(&strace_raw).with_context(|| {
        format!(
            "while parsing QEMU strace for scenario `{}` (binary `{}`)",
            params.scenario_id, params.bin_id
        )
    })?;

    if parsed.total_calls == 0 {
        bail!(
            "scenario `{}` (binary `{}`) produced an empty QEMU strace log",
            params.scenario_id,
            params.bin_id
        );
    }

    for &req_nr in params.require_dynamic_syscalls {
        let present = parsed
            .distinct_counts
            .iter()
            .any(|&(nr, _, calls)| nr == req_nr && calls > 0);
        if !present {
            let req_name = aarch64_syscall_name(req_nr).unwrap_or("unknown");
            let observed: Vec<String> = parsed
                .distinct_counts
                .iter()
                .map(|(nr, name, calls)| format!("{name}({nr})x{calls}"))
                .collect();
            bail!(
                "scenario `{}` (binary `{}`) did not exercise required dynamic syscall {} (`{}`); \
                 observed: [{}]",
                params.scenario_id,
                params.bin_id,
                req_nr,
                req_name,
                observed.join(", ")
            );
        }
    }

    Ok(DynamicScenarioRun { exit_code, parsed })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_strace_parser_extracts_host_independent_counts_and_rle() {
        let log_host_a = "\
991204 set_tid_address(0x23c8f8) = 991204
991204 ppoll(0x7fb27dffd0b8,3,0x7fb27dffd0a0,(nil)) = 0
991204 rt_sigaction(SIGPIPE,0x00007fb27dffcee0,0x00007fb27dffcf00) = 0
991204 brk(NULL) = 0x000000000023d000
991204 brk(0x000000000023f000) = 0x000000000023f000
991204 mremap(140404620169216,135168,266240,1,0,140404620304380) = 70368744177664
991204 exit_group(0)
";
        let log_host_b = "\
42 set_tid_address(0x999999) = 42
42 ppoll(0x7fffffffe000,3,0x7fffffffdff0,(nil)) = 0
42 rt_sigaction(SIGPIPE,0x00007fffffffde00,0x00007fffffffde20) = 0
42 brk(NULL) = 0x000000000023d000
42 brk(0x000000000023f000) = 0x000000000023f000
42 mremap(123456,135168,266240,1,0,654321) = 888888
42 exit_group(0)
";

        let pa = parse_qemu_strace_strict(log_host_a).unwrap();
        let pb = parse_qemu_strace_strict(log_host_b).unwrap();
        // Host PIDs and guest/host pointer values do not leak into `ParsedStrace`.
        assert_eq!(pa, pb);
        assert_eq!(pa.total_calls, 7);
        assert_eq!(
            pa.distinct_counts,
            vec![
                (73, "ppoll".into(), 1),
                (94, "exit_group".into(), 1),
                (96, "set_tid_address".into(), 1),
                (134, "rt_sigaction".into(), 1),
                (214, "brk".into(), 2),
                (216, "mremap".into(), 1),
            ]
        );
        assert_eq!(pa.ordered_runs.len(), 6);
        assert_eq!(
            pa.ordered_runs[3],
            SyscallRun {
                nr: 214,
                name: "brk".into(),
                calls: 2,
            }
        );
    }

    #[test]
    fn strict_strace_parser_fails_closed_on_unknown_or_corrupt_lines() {
        let unknown_nr = "1001 set_tid_address(0x2000) = 1001\n1001 Unknown syscall 999\n";
        assert!(parse_qemu_strace_strict(unknown_nr).is_err());

        let unknown_name = "1001 totally_invented_syscall(0) = 0\n";
        assert!(parse_qemu_strace_strict(unknown_name).is_err());

        let signal_or_noise = "1001 write(1,0x2000,4) = 4\nspurious stdout line\n";
        assert!(parse_qemu_strace_strict(signal_or_noise).is_err());
    }

    #[test]
    fn data_kind_generators_are_deterministic() {
        let rep = DataKind::RepeatLines {
            lines: vec!["SET k_{i} val".into(), "GET k_{i}".into()],
            target_bytes: 64,
        }
        .materialize()
        .unwrap();
        assert!(rep.len() >= 64);
        assert!(rep.starts_with(b"SET k_0 val\nGET k_1\n"));

        let long = DataKind::LongLine {
            len: 4100,
            byte: 'x',
            trailing_newline: true,
        }
        .materialize()
        .unwrap();
        assert_eq!(long.len(), 4101);
        assert_eq!(long[4100], b'\n');
        assert!(long[..4100].iter().all(|&b| b == b'x'));
    }
}
