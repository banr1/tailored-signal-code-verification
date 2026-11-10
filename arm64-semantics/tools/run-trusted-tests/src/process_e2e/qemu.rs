// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Isolated `qemu-aarch64` user-mode execution and `-strace` syscall census parser (`[TEST ONLY]`).

use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, anyhow, bail};

use super::types::{
    FileEntry, PostFileEntry, QemuOutcome, SyscallCount, aarch64_syscall_info,
};
use super::{hex_decode, hex_encode};

/// Resolve the pinned static `qemu-aarch64` binary and return `(binary_path, version_line)`.
pub fn resolve_qemu_aarch64(repo_root: &Path) -> Result<(PathBuf, String)> {
    resolve_qemu_aarch64_with_override(repo_root, None)
}

/// Resolve `qemu-aarch64` from an explicit CLI override, `QEMU_AARCH64`, `scripts/fetch-qemu-aarch64`,
/// or `PATH`, returning `(binary_path, version_line)`.
pub fn resolve_qemu_aarch64_with_override(
    repo_root: &Path,
    explicit_qemu: Option<&Path>,
) -> Result<(PathBuf, String)> {
    let qemu_path = if let Some(explicit) = explicit_qemu {
        if !explicit.is_file() {
            bail!("--qemu points to missing file: {}", explicit.display());
        }
        explicit.to_path_buf()
    } else if let Some(explicit) = std::env::var_os("QEMU_AARCH64") {
        let p = PathBuf::from(explicit);
        if !p.is_file() {
            bail!("QEMU_AARCH64 points to missing file: {}", p.display());
        }
        p
    } else {
        let fetch_script = repo_root.join("scripts").join("fetch-qemu-aarch64");
        if fetch_script.is_file() {
            let out = Command::new(&fetch_script)
                .output()
                .with_context(|| format!("failed to execute {}", fetch_script.display()))?;
            if !out.status.success() {
                bail!(
                    "`scripts/fetch-qemu-aarch64` failed:\n{}",
                    String::from_utf8_lossy(&out.stderr)
                );
            }
            PathBuf::from(String::from_utf8_lossy(&out.stdout).trim())
        } else {
            which::which("qemu-aarch64")
                .context("`qemu-aarch64` not found in PATH and `scripts/fetch-qemu-aarch64` missing")?
        }
    };

    let ver_out = Command::new(&qemu_path)
        .arg("--version")
        .output()
        .with_context(|| format!("failed to execute `{} --version`", qemu_path.display()))?;
    if !ver_out.status.success() {
        bail!("`{} --version` failed", qemu_path.display());
    }
    let ver_line = String::from_utf8_lossy(&ver_out.stdout)
        .lines()
        .next()
        .unwrap_or("qemu-aarch64")
        .trim()
        .to_owned();
    Ok((qemu_path, ver_line))
}

/// Parse a `qemu-aarch64 -D <log> -strace` trace into deterministic per-syscall call counts.
pub fn parse_qemu_strace(trace: &str) -> Vec<SyscallCount> {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for raw_line in trace.lines() {
        let line = raw_line.trim_start();
        let pid_len = line.bytes().take_while(|b| b.is_ascii_digit()).count();
        if pid_len == 0 {
            continue;
        }
        let rest = &line[pid_len..];
        let Some(after_space) = rest.strip_prefix(' ') else {
            continue;
        };
        if let Some(num_str) = after_space.strip_prefix("Unknown syscall ") {
            let digits: String = num_str
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            if !digits.is_empty() {
                *counts.entry(format!("unknown_{digits}")).or_insert(0) += 1;
            }
            continue;
        }
        let Some(paren_idx) = after_space.find('(') else {
            continue;
        };
        let cand = &after_space[..paren_idx];
        if !cand.is_empty()
            && cand
                .bytes()
                .next()
                .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
            && cand
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            *counts.entry(cand.to_owned()).or_insert(0) += 1;
        }
    }

    let mut result: Vec<SyscallCount> = counts
        .into_iter()
        .map(|(name, calls)| {
            let (nr, modeled) = if let Some(raw_nr) = name.strip_prefix("unknown_") {
                (raw_nr.parse::<u32>().ok(), false)
            } else {
                aarch64_syscall_info(&name)
            };
            SyscallCount {
                name,
                nr,
                modeled,
                calls,
            }
        })
        .collect();
    result.sort_by(|a, b| {
        a.nr.unwrap_or(u32::MAX)
            .cmp(&b.nr.unwrap_or(u32::MAX))
            .then_with(|| a.name.cmp(&b.name))
    });
    result
}

/// Normalize host `<PID>` in Rust panic `stderr` output (`thread '<unnamed>' (<PID>) panicked at `)
/// to canonical PID `1` so checked-in vectors are deterministic across host runs.
pub fn normalize_rust_panic_stderr(raw: &[u8]) -> Result<Vec<u8>> {
    let text = std::str::from_utf8(raw).context("panic stderr is not valid UTF-8")?;
    let prefix = "thread '<unnamed>' (";
    let Some(start) = text.find(prefix) else {
        bail!("expected Rust panic prefix `{prefix}` in stderr, got: {text:?}");
    };
    let after_open = start + prefix.len();
    let Some(rel_close) = text[after_open..].find(") panicked at ") else {
        bail!("expected `) panicked at ` after thread TID in stderr, got: {text:?}");
    };
    let tid_slice = &text[after_open..after_open + rel_close];
    if tid_slice.is_empty() || !tid_slice.bytes().all(|b| b.is_ascii_digit()) {
        bail!("expected numeric TID in Rust panic message, got `{tid_slice}`");
    }
    let mut normalized = String::with_capacity(text.len());
    normalized.push_str(&text[..after_open]);
    normalized.push_str("1");
    normalized.push_str(&text[after_open + rel_close..]);
    Ok(normalized.into_bytes())
}

/// Input specification for a single QEMU execution.
pub struct QemuRunRequest<'a> {
    pub qemu_bin: &'a Path,
    pub elf_abs_path: &'a Path,
    pub args: &'a [String],
    pub envp: &'a [String],
    pub stdin: &'a [u8],
    pub pre_dirs: &'a [String],
    pub initial_files: &'a [FileEntry],
    pub watched_files: &'a [String],
    pub nondeterministic_stdout: bool,
    pub normalize_panic_tid: bool,
}

/// Strip the host `qemu-aarch64` user-mode fatal-signal trailer (`qemu: uncaught target signal …\n`)
/// appended to host fd 2 after the guest process terminates by signal.
fn strip_qemu_signal_banner(raw: &[u8]) -> Vec<u8> {
    const MARKER: &[u8] = b"qemu: uncaught target signal ";
    if let Some(pos) = raw.windows(MARKER.len()).rposition(|w| w == MARKER) {
        if raw[pos..].ends_with(b"\n") && !raw[pos..raw.len() - 1].contains(&b'\n') {
            return raw[..pos].to_vec();
        }
    }
    raw.to_vec()
}

/// Execute `req` inside an isolated temporary working directory and capture outcome + `-strace`.
pub fn run_in_qemu(req: &QemuRunRequest<'_>) -> Result<QemuOutcome> {
    if req.args.is_empty() {
        bail!("args must contain at least argv[0]");
    }
    let work_tmp = tempfile::TempDir::new().context("failed to create guest cwd TempDir")?;
    let trace_tmp = tempfile::TempDir::new().context("failed to create strace TempDir")?;
    let strace_path = trace_tmp.path().join("qemu.strace");

    for dir_rel in req.pre_dirs {
        fs::create_dir_all(work_tmp.path().join(dir_rel))?;
    }
    for f in req.initial_files {
        let dst = work_tmp.path().join(&f.path);
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent)?;
        }
        let data = hex_decode(&f.hex)?;
        fs::write(&dst, &data)?;
    }

    let mut cmd = Command::new(req.qemu_bin);
    cmd.current_dir(work_tmp.path())
        .env_clear()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    for entry in req.envp {
        let (k, v) = entry
            .split_once('=')
            .ok_or_else(|| anyhow!("envp entry missing '=': {entry:?}"))?;
        cmd.env(k, v);
    }

    cmd.arg("-0")
        .arg(&req.args[0])
        .arg("-D")
        .arg(&strace_path)
        .arg("-strace")
        .arg(req.elf_abs_path)
        .args(&req.args[1..]);

    let mut child = cmd
        .spawn()
        .with_context(|| format!("failed to spawn {}", req.qemu_bin.display()))?;
    if let Some(mut child_stdin) = child.stdin.take() {
        // Ignore `BrokenPipe` if guest exits without reading `stdin` (e.g. `keygen`, `init`, traps).
        let _ = child_stdin.write_all(req.stdin);
    }
    let output = child.wait_with_output()?;

    let exit_code = output.status.code();
    let signal = output.status.signal();
    let raw_stdout = output.stdout;
    let raw_stderr = output.stderr;

    let stdout_len = raw_stdout.len();
    let (stdout_hex, stdout_utf8) = if req.nondeterministic_stdout {
        if exit_code != Some(0) || signal.is_some() {
            bail!(
                "nondeterministic entropy probe failed on QEMU: exit={exit_code:?} signal={signal:?}"
            );
        }
        if stdout_len != 33
            || raw_stdout.last() != Some(&b'\n')
            || !raw_stdout[..32]
                .iter()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            bail!(
                "unexpected raw-hex output format from QEMU ({stdout_len} B): {:?}",
                String::from_utf8_lossy(&raw_stdout)
            );
        }
        (String::new(), None)
    } else {
        (
            hex_encode(&raw_stdout),
            std::str::from_utf8(&raw_stdout).ok().map(str::to_owned),
        )
    };

    let guest_stderr: Vec<u8> = if signal.is_some() {
        strip_qemu_signal_banner(&raw_stderr)
    } else {
        raw_stderr
    };
    let norm_stderr = if req.normalize_panic_tid {
        normalize_rust_panic_stderr(&guest_stderr)?
    } else {
        guest_stderr
    };
    let stderr_utf8 = std::str::from_utf8(&norm_stderr).ok().map(str::to_owned);
    let stderr_hex = hex_encode(&norm_stderr);

    let mut post_files = Vec::with_capacity(req.watched_files.len());
    for rel in req.watched_files {
        let p = work_tmp.path().join(rel);
        if p.is_file() {
            let bytes = fs::read(&p)?;
            post_files.push(PostFileEntry {
                path: rel.clone(),
                exists: true,
                hex: hex_encode(&bytes),
            });
        } else {
            post_files.push(PostFileEntry {
                path: rel.clone(),
                exists: false,
                hex: String::new(),
            });
        }
    }

    let strace_raw = if strace_path.is_file() {
        fs::read_to_string(&strace_path)?
    } else {
        String::new()
    };
    let syscalls = parse_qemu_strace(&strace_raw);

    Ok(QemuOutcome {
        exit_code,
        signal,
        stdout_hex,
        stdout_utf8,
        stdout_len,
        stderr_hex,
        stderr_utf8,
        nondeterministic_stdout: req.nondeterministic_stdout,
        normalized_tid_in_stderr: req.normalize_panic_tid,
        post_files,
        syscalls,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_strace_counts_and_modeling_status() {
        let sample = "\
2849102 brk(NULL) = 0x0000000000245000
2849102 set_tid_address(0x244ed8) = 2849102
2849102 openat(AT_FDCWD,\"coins\",O_RDONLY|O_LARGEFILE|O_CLOEXEC) = 3
2849102 fcntl(3,F_SETFD,FD_CLOEXEC) = 0
2849102 fstat(3,0x0000007fffffea60) = 0
2849102 read(3,0x245010,33) = 32
2849102 close(3) = 0
2849102 gettid() = 2849102
2849102 write(2,0x245100,48) = 48
2849102 rt_sigprocmask(SIG_UNBLOCK,0x7fffffe900,NULL,8) = 0
2849102 tkill(2849102,SIGABRT) = 0
--- SIGABRT {si_signo=SIGABRT, si_code=SI_TKILL, si_pid=2849102, si_uid=1000} ---
";
        let parsed = parse_qemu_strace(sample);
        let by_name: BTreeMap<&str, &SyscallCount> =
            parsed.iter().map(|s| (s.name.as_str(), s)).collect();
        assert_eq!(by_name.len(), 11);
        assert_eq!(by_name["fcntl"].nr, Some(25));
        assert!(by_name["fcntl"].modeled);
        assert_eq!(by_name["fcntl"].calls, 1);
        assert_eq!(by_name["openat"].nr, Some(56));
        assert!(by_name["openat"].modeled);
        assert_eq!(by_name["gettid"].nr, Some(178));
        assert!(by_name["gettid"].modeled);
        assert_eq!(by_name["tkill"].nr, Some(130));
        assert!(by_name["tkill"].modeled);
    }

    #[test]
    fn normalize_panic_tid_replaces_pid() {
        let raw = b"thread '<unnamed>' (2849102) panicked at /workspace/src/bin/unmodified_std_probe.rs:46:13:\nboom\n";
        let got = normalize_rust_panic_stderr(raw).unwrap();
        assert_eq!(
            std::str::from_utf8(&got).unwrap(),
            "thread '<unnamed>' (1) panicked at /workspace/src/bin/unmodified_std_probe.rs:46:13:\nboom\n"
        );
    }
}
