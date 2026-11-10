// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Pinned Rust `std` binary build profile, toolchain verification, and manifest guards (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — compiles an ordinary safe Rust `std` binary crate into a
//!   deterministic relocatable LTO object and stages the pinned Rust 1.98.1 bundled musl runtime
//!   archives (`crt1.o`, `libc.a`, `libunwind.a`, `compiler_builtins.a`) for [`crate::link`].
//!   Soundness rests on `Arm64.Process.ElfImage.parse` and Lean proofs over the resulting ELF.
//! - **Purpose:** Verifies the exact Rust `1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`,
//!   LLVM `22.1.8`) compiler, `rust-src`, bundled `rust-lld`, and bundled musl 1.2.5 SHA-256
//!   digests; enforces manifest and source-tree guards on `--main-rust <Cargo.toml>` binary
//!   crates; compiles the single-CGU fat-LTO object under `-Zbuild-std=std,panic_abort` and
//!   `-Cpanic=immediate-abort`; and generates AArch64 global-allocator shim bridges when linking
//!   pre-verified `#![no_std]` + `alloc` images.
//!
//! # Key Types & Functions
//! - [`StdToolchain`], [`RustLld`], [`check_std_toolchain`]: toolchain and musl digest checks.
//! - [`RustMainKind`], [`StdBinCrate`], [`classify_rust_manifest`]: manifest parser and guards.
//! - [`std_encoded_rustflags`], [`build_std_main_objects`], [`rust_alloc_bridge_asm`]: build &
//!   bridge helpers.
//!
//! # When to Read This File
//! - Read this file for the pinned `std` toolchain checks, manifest guards, `-Zbuild-std` flags,
//!   and global-allocator bridge assembly.

use crate::link::{
    filter_gnu_archive_obj_members, normalize_gnu_archive_member_names, run_cmd, sha256, tool,
};
use anyhow::{Context, Result, anyhow, bail, ensure};
use object::{Object, ObjectSymbol};
use rust_obj2lean::untrusted_driver;
use serde_json::{Map, Value};
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;

pub const PINNED_RUSTC_RELEASE: &str = "1.98.1";
pub const PINNED_RUSTC_COMMIT: &str = "48a229ceaefd4985c50990b14116b6d856af0985";
pub const PINNED_RUSTC_SHORT_COMMIT: &str = "48a229cea";
pub const PINNED_LLVM_VERSION: &str = "22.1.8";
pub const MUSL_TARGET: &str = "aarch64-unknown-linux-musl";

pub const BUNDLED_CRT1_SHA256: &str =
    "2c8595cff75b182ad59c0278d5f81bed2cf1e51b5bf9324db52142c89dd6479f";
pub const BUNDLED_CRTI_SHA256: &str =
    "b49a67e2e36eed4836023fc26ff9da617e2020a2317aadfeb7971e4cbe612bf7";
pub const BUNDLED_CRTBEGIN_SHA256: &str =
    "522c4ac7628b80df407f1873be18b6b9b398db5be7f9f5586835cdfd189f6a9e";
pub const BUNDLED_LIBC_SHA256: &str =
    "b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f";
pub const BUNDLED_LIBUNWIND_SHA256: &str =
    "06977ce3e033cf2c06fcbac9b25b7c9213c7b4aa09f2a4d4b4427fb809b9f203";
pub const BUNDLED_CRTEND_SHA256: &str =
    "9fd9518f8a0ba537a77c5d5c638ec30efa388a9458c21ad84f5607c535547adb";
pub const BUNDLED_CRTN_SHA256: &str =
    "b2f52a98df83f38814f34f7477aeb629d5e1fb1c1379ef2739cad91ab9ab8734";

pub const SELF_CONTAINED_CHECKSUMS: &[(&str, &str)] = &[
    ("crt1.o", BUNDLED_CRT1_SHA256),
    ("crti.o", BUNDLED_CRTI_SHA256),
    ("crtbegin.o", BUNDLED_CRTBEGIN_SHA256),
    ("libc.a", BUNDLED_LIBC_SHA256),
    ("libunwind.a", BUNDLED_LIBUNWIND_SHA256),
    ("crtend.o", BUNDLED_CRTEND_SHA256),
    ("crtn.o", BUNDLED_CRTN_SHA256),
];

/// Check that every file of [`SELF_CONTAINED_CHECKSUMS`] exists in `dir` with its pinned SHA-256
/// (fails closed on a missing file or any mismatch).
pub fn verify_self_contained_dir(dir: &Path) -> Result<()> {
    for &(file, expected_sha) in SELF_CONTAINED_CHECKSUMS {
        let p = dir.join(file);
        let bytes = std::fs::read(&p).with_context(|| {
            format!(
                "missing bundled musl runtime input {} in {}",
                file,
                dir.display()
            )
        })?;
        let actual_sha = sha256(&bytes);
        ensure!(
            actual_sha == expected_sha,
            "SHA-256 mismatch for bundled {}: expected {}, got {}",
            p.display(),
            expected_sha,
            actual_sha
        );
    }
    Ok(())
}

/// Bundled `rust-lld` linker inside the pinned Rust 1.98.1 sysroot.
#[derive(Debug, Clone)]
pub struct RustLld {
    pub bin: PathBuf,
    pub prefix_args: Vec<String>,
}

impl RustLld {
    pub fn command(&self) -> Command {
        let mut c = Command::new(&self.bin);
        c.args(&self.prefix_args);
        c
    }

    pub fn version(&self) -> Result<String> {
        let mut c = self.command();
        c.arg("--version");
        let s = run_cmd(&mut c)?;
        Ok(s.lines().next().unwrap_or("").trim().to_string())
    }
}

/// Verified Rust 1.98.1 toolchain, `rust-src`, bundled `rust-lld`, and musl `self-contained` dir.
#[derive(Debug, Clone)]
pub struct StdToolchain {
    pub rustc_bin: PathBuf,
    pub rustc_prefix_args: Vec<String>,
    pub cargo_bin: PathBuf,
    pub cargo_prefix_args: Vec<String>,
    pub host_triple: String,
    pub sysroot: PathBuf,
    pub self_contained: PathBuf,
    pub lld: RustLld,
}

fn parse_rustc_vv_fields(vv: &str) -> Option<(&str, &str, &str, &str)> {
    let mut release = None;
    let mut commit = None;
    let mut llvm = None;
    let mut host = None;
    for line in vv.lines() {
        let line = line.trim();
        if let Some(v) = line.strip_prefix("release:") {
            release = Some(v.trim());
        } else if let Some(v) = line.strip_prefix("commit-hash:") {
            commit = Some(v.trim());
        } else if let Some(v) = line.strip_prefix("LLVM version:") {
            llvm = Some(v.trim());
        } else if let Some(v) = line.strip_prefix("host:") {
            host = Some(v.trim());
        }
    }
    Some((release?, commit?, llvm?, host?))
}

fn check_rustc_vv(vv: &str) -> Result<String> {
    let Some((release, commit, llvm, host)) = parse_rustc_vv_fields(vv) else {
        bail!("incomplete `rustc -vV` output:\n{vv}");
    };
    ensure!(
        release == PINNED_RUSTC_RELEASE
            && commit == PINNED_RUSTC_COMMIT
            && llvm == PINNED_LLVM_VERSION,
        "expected rustc {} ({}, LLVM {}), got rustc {} ({}, LLVM {})",
        PINNED_RUSTC_RELEASE,
        PINNED_RUSTC_COMMIT,
        PINNED_LLVM_VERSION,
        release,
        commit,
        llvm
    );
    ensure!(!host.is_empty(), "empty `host:` in `rustc -vV`");
    Ok(host.to_string())
}

fn run_rustc_query(bin: &Path, prefix: &[String], args: &[&str]) -> Result<String> {
    let mut c = Command::new(bin);
    c.args(prefix).args(args);
    run_cmd(&mut c)
}

impl StdToolchain {
    /// Locate and verify the pinned Rust 1.98.1 compiler, `rust-src`, bundled `rust-lld`, and
    /// unmodified `<target-libdir>/self-contained` musl 1.2.5 objects/archives.
    pub fn resolve() -> Result<Self> {
        Self::resolve_with(None)
    }

    /// [`Self::resolve`], but take the musl `self-contained` runtime from `self_contained_dir`
    /// when given (it must hold the same pinned files: [`verify_self_contained_dir`]) instead of
    /// `<target-libdir>/self-contained`.
    pub fn resolve_with(self_contained_dir: Option<&Path>) -> Result<Self> {
        if let Some(dir) = self_contained_dir {
            // Fail on a bad explicit directory before probing the toolchain.
            verify_self_contained_dir(dir)?;
        }
        // Check default `rustc` (`$RUSTC` or `rustc` in `PATH`) first so CI environments without
        // `+1.98.1` rustup shorthand work directly, then fall back to `rustc +1.98.1` via rustup.
        let mut chosen: Option<(PathBuf, Vec<String>, String)> = None;
        let mut first_err: Option<anyhow::Error> = None;

        if let Ok(default_rustc) = tool("RUSTC", "rustc") {
            match run_rustc_query(&default_rustc, &[], &["-vV"]).and_then(|vv| check_rustc_vv(&vv))
            {
                Ok(host) => chosen = Some((default_rustc, Vec::new(), host)),
                Err(e) => first_err = Some(e),
            }
        }

        // Only fall back to `rustc +1.98.1` if `RUSTC` was not explicitly overridden to a
        // mismatched compiler.
        let explicit_rustc = std::env::var_os("RUSTC").is_some_and(|v| !v.is_empty());
        if chosen.is_none()
            && !explicit_rustc
            && let Ok(rustup_rustc) = which::which("rustc")
        {
            let plus = vec![format!("+{PINNED_RUSTC_RELEASE}")];
            match run_rustc_query(&rustup_rustc, &plus, &["-vV"]).and_then(|vv| check_rustc_vv(&vv))
            {
                Ok(host) => chosen = Some((rustup_rustc, plus, host)),
                Err(e) => {
                    if first_err.is_none() {
                        first_err = Some(e);
                    }
                }
            }
        }

        let (probe_rustc, probe_prefix, host_triple) = chosen.ok_or_else(|| {
            first_err.unwrap_or_else(|| {
                anyhow!(
                    "cannot find pinned rustc {PINNED_RUSTC_RELEASE} ({PINNED_RUSTC_COMMIT}, LLVM {PINNED_LLVM_VERSION})"
                )
            })
        })?;

        let sysroot_str = run_rustc_query(&probe_rustc, &probe_prefix, &["--print", "sysroot"])?;
        let sysroot = PathBuf::from(sysroot_str.trim());
        ensure!(
            sysroot.is_dir(),
            "rustc sysroot {} does not exist",
            sysroot.display()
        );

        let target_libdir_str = run_rustc_query(
            &probe_rustc,
            &probe_prefix,
            &["--print", "target-libdir", "--target", MUSL_TARGET],
        )?;
        let target_libdir = PathBuf::from(target_libdir_str.trim());
        let self_contained = match self_contained_dir {
            Some(dir) => dir.to_path_buf(),
            None => target_libdir.join("self-contained"),
        };
        ensure!(
            self_contained.is_dir(),
            "missing musl self-contained directory {} (install target `{MUSL_TARGET}`)",
            self_contained.display()
        );

        verify_self_contained_dir(&self_contained)?;

        let std_manifest = sysroot
            .join("lib")
            .join("rustlib")
            .join("src")
            .join("rust")
            .join("library")
            .join("std")
            .join("Cargo.toml");
        ensure!(
            std_manifest.is_file(),
            "missing `rust-src` component at {} (needed for `-Zbuild-std=std,panic_abort`)",
            std_manifest.display()
        );

        let host_bin = sysroot
            .join("lib")
            .join("rustlib")
            .join(&host_triple)
            .join("bin");
        let gcc_ld = host_bin.join("gcc-ld").join("ld.lld");
        let raw_rust_lld = host_bin.join("rust-lld");
        let lld = if gcc_ld.is_file() {
            RustLld {
                bin: gcc_ld,
                prefix_args: Vec::new(),
            }
        } else if raw_rust_lld.is_file() {
            RustLld {
                bin: raw_rust_lld,
                prefix_args: vec!["-flavor".to_string(), "gnu".to_string()],
            }
        } else {
            bail!(
                "missing bundled `rust-lld` at {} or {}",
                gcc_ld.display(),
                raw_rust_lld.display()
            );
        };

        // Prefer the direct `<sysroot>/bin/{rustc,cargo}` binaries so `cargo` and `rustc` never
        // diverge across rustup shims or channel aliases (e.g. `stable` vs `1.98.1`).
        let direct_rustc = sysroot.join("bin").join("rustc");
        let (rustc_bin, rustc_prefix_args) = if direct_rustc.is_file() {
            (direct_rustc, Vec::new())
        } else {
            (probe_rustc, probe_prefix.clone())
        };

        let direct_cargo = sysroot.join("bin").join("cargo");
        let explicit_cargo = std::env::var_os("CARGO").filter(|v| !v.is_empty());
        let (cargo_bin, cargo_prefix_args) = if let Some(c) = explicit_cargo
            && probe_prefix.is_empty()
        {
            (PathBuf::from(c), Vec::new())
        } else if direct_cargo.is_file() {
            (direct_cargo, Vec::new())
        } else {
            let cargo = tool("CARGO", "cargo")?;
            (cargo, probe_prefix)
        };

        Ok(Self {
            rustc_bin,
            rustc_prefix_args,
            cargo_bin,
            cargo_prefix_args,
            host_triple,
            sysroot,
            self_contained,
            lld,
        })
    }

    /// Resolve `llvm-objcopy`, falling back to `rust-objcopy` bundled in the pinned sysroot.
    pub fn resolve_objcopy(&self) -> Result<PathBuf> {
        if let Ok(p) = tool("LLVM_OBJCOPY", "llvm-objcopy") {
            return Ok(p);
        }
        let bundled = self
            .sysroot
            .join("lib")
            .join("rustlib")
            .join(&self.host_triple)
            .join("bin")
            .join("rust-objcopy");
        if bundled.is_file() {
            return Ok(bundled);
        }
        tool("LLVM_OBJCOPY", "llvm-objcopy")
    }

    pub fn self_contained_pre(&self) -> Vec<PathBuf> {
        ["crt1.o", "crti.o", "crtbegin.o"]
            .into_iter()
            .map(|f| self.self_contained.join(f))
            .collect()
    }

    pub fn self_contained_libc(&self) -> PathBuf {
        self.self_contained.join("libc.a")
    }

    pub fn self_contained_unwind(&self) -> PathBuf {
        self.self_contained.join("libunwind.a")
    }

    pub fn self_contained_post(&self) -> Vec<PathBuf> {
        ["crtend.o", "crtn.o"]
            .into_iter()
            .map(|f| self.self_contained.join(f))
            .collect()
    }

    pub fn std_profile_json(&self) -> Value {
        serde_json::json!({
            "rustc": PINNED_RUSTC_RELEASE,
            "commit": PINNED_RUSTC_COMMIT,
            "llvm": PINNED_LLVM_VERSION,
            "crt1Sha256": BUNDLED_CRT1_SHA256,
            "libcSha256": BUNDLED_LIBC_SHA256,
        })
    }
}

/// Run `--check-std-toolchain` and return its confirmation message.
pub fn check_std_toolchain() -> Result<String> {
    let _tc = StdToolchain::resolve()?;
    Ok(format!(
        "OK: rustc {PINNED_RUSTC_RELEASE} ({PINNED_RUSTC_SHORT_COMMIT}, LLVM {PINNED_LLVM_VERSION}), bundled musl crt1.o + libc.a checksums verified"
    ))
}

// ---------------------------------------------------------------------------
// Minimal self-contained `Cargo.toml` parser & manifest/source guards
// ---------------------------------------------------------------------------

struct TomlParser<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> TomlParser<'a> {
    fn new(s: &'a str) -> Self {
        Self { s, pos: 0 }
    }

    fn peek(&self) -> Option<char> {
        self.s[self.pos..].chars().next()
    }

    fn rest(&self) -> &'a str {
        &self.s[self.pos..]
    }

    fn advance_char(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn skip_ws_inline(&mut self) {
        while let Some(c) = self.peek() {
            if c == ' ' || c == '\t' {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn skip_ws_and_comments(&mut self) {
        loop {
            while let Some(c) = self.peek() {
                if matches!(c, ' ' | '\t' | '\r' | '\n') {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            if self.peek() == Some('#') {
                while let Some(c) = self.advance_char() {
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn skip_line_end(&mut self) -> Result<()> {
        self.skip_ws_inline();
        if self.peek() == Some('#') {
            while let Some(c) = self.advance_char() {
                if c == '\n' {
                    break;
                }
            }
            return Ok(());
        }
        match self.peek() {
            None => Ok(()),
            Some('\n') => {
                self.pos += 1;
                Ok(())
            }
            Some('\r') => {
                self.pos += 1;
                if self.peek() == Some('\n') {
                    self.pos += 1;
                }
                Ok(())
            }
            Some(c) => bail!("unexpected character `{c}` at byte {}", self.pos),
        }
    }

    fn parse_basic_string(&mut self) -> Result<String> {
        let multiline = if self.rest().starts_with("\"\"\"") {
            self.pos += 3;
            if self.rest().starts_with("\r\n") {
                self.pos += 2;
            } else if self.rest().starts_with('\n') {
                self.pos += 1;
            }
            true
        } else {
            ensure!(self.advance_char() == Some('"'), "expected `\"`");
            false
        };
        let mut out = String::new();
        loop {
            if multiline && self.rest().starts_with("\"\"\"") {
                self.pos += 3;
                let mut extra = 0usize;
                while self.peek() == Some('"') && extra < 2 {
                    // Handle up to 2 extra quotes in `"""...""""`
                    out.push('"');
                    self.pos += 1;
                    extra += 1;
                }
                return Ok(out);
            }
            let Some(c) = self.advance_char() else {
                bail!("unterminated TOML string");
            };
            if !multiline && c == '"' {
                return Ok(out);
            }
            if c == '\\' {
                let Some(esc) = self.advance_char() else {
                    bail!("unterminated escape sequence in TOML string");
                };
                match esc {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    'b' => out.push('\u{0008}'),
                    'f' => out.push('\u{000C}'),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    'u' | 'U' => {
                        let len = if esc == 'u' { 4 } else { 8 };
                        ensure!(
                            self.pos + len <= self.s.len(),
                            "short unicode escape in TOML string"
                        );
                        let hex = &self.s[self.pos..self.pos + len];
                        self.pos += len;
                        let code = u32::from_str_radix(hex, 16)
                            .context("invalid unicode escape in TOML string")?;
                        let ch = char::from_u32(code)
                            .ok_or_else(|| anyhow!("invalid unicode scalar in TOML string"))?;
                        out.push(ch);
                    }
                    '\r' | '\n' | ' ' | '\t' if multiline => {
                        while let Some(w) = self.peek() {
                            if matches!(w, ' ' | '\t' | '\r' | '\n') {
                                self.pos += 1;
                            } else {
                                break;
                            }
                        }
                    }
                    other => bail!("unsupported escape `\\{other}` in TOML string"),
                }
            } else {
                out.push(c);
            }
        }
    }

    fn parse_literal_string(&mut self) -> Result<String> {
        let multiline = if self.rest().starts_with("'''") {
            self.pos += 3;
            if self.rest().starts_with("\r\n") {
                self.pos += 2;
            } else if self.rest().starts_with('\n') {
                self.pos += 1;
            }
            true
        } else {
            ensure!(self.advance_char() == Some('\''), "expected `'`");
            false
        };
        let mut out = String::new();
        loop {
            if multiline && self.rest().starts_with("'''") {
                self.pos += 3;
                return Ok(out);
            }
            let Some(c) = self.advance_char() else {
                bail!("unterminated literal TOML string");
            };
            if !multiline && c == '\'' {
                return Ok(out);
            }
            out.push(c);
        }
    }

    fn parse_key_segment(&mut self) -> Result<String> {
        self.skip_ws_inline();
        match self.peek() {
            Some('"') => self.parse_basic_string(),
            Some('\'') => self.parse_literal_string(),
            Some(_) => {
                let start = self.pos;
                while let Some(c) = self.peek() {
                    if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                ensure!(self.pos > start, "expected TOML key at byte {}", self.pos);
                Ok(self.s[start..self.pos].to_string())
            }
            None => bail!("unexpected EOF while reading TOML key"),
        }
    }

    fn parse_dotted_key(&mut self) -> Result<Vec<String>> {
        let mut parts = vec![self.parse_key_segment()?];
        loop {
            self.skip_ws_inline();
            if self.peek() == Some('.') {
                self.pos += 1;
                parts.push(self.parse_key_segment()?);
            } else {
                break;
            }
        }
        Ok(parts)
    }

    fn parse_value(&mut self) -> Result<Value> {
        self.skip_ws_inline();
        match self.peek() {
            Some('"') => Ok(Value::String(self.parse_basic_string()?)),
            Some('\'') => Ok(Value::String(self.parse_literal_string()?)),
            Some('[') => {
                self.pos += 1;
                let mut items = Vec::new();
                loop {
                    self.skip_ws_and_comments();
                    if self.peek() == Some(']') {
                        self.pos += 1;
                        return Ok(Value::Array(items));
                    }
                    items.push(self.parse_value()?);
                    self.skip_ws_and_comments();
                    if self.peek() == Some(',') {
                        self.pos += 1;
                    } else if self.peek() == Some(']') {
                        self.pos += 1;
                        return Ok(Value::Array(items));
                    } else {
                        bail!("expected `,` or `]` in TOML array at byte {}", self.pos);
                    }
                }
            }
            Some('{') => {
                self.pos += 1;
                let mut map = Map::new();
                loop {
                    self.skip_ws_and_comments();
                    if self.peek() == Some('}') {
                        self.pos += 1;
                        return Ok(Value::Object(map));
                    }
                    let key = self.parse_dotted_key()?;
                    self.skip_ws_inline();
                    ensure!(
                        self.advance_char() == Some('='),
                        "expected `=` in inline table at byte {}",
                        self.pos
                    );
                    let val = self.parse_value()?;
                    insert_dotted(&mut map, &key, val)?;
                    self.skip_ws_and_comments();
                    if self.peek() == Some(',') {
                        self.pos += 1;
                    } else if self.peek() == Some('}') {
                        self.pos += 1;
                        return Ok(Value::Object(map));
                    } else {
                        bail!("expected `,` or `}}` in inline table at byte {}", self.pos);
                    }
                }
            }
            Some(_) => {
                let start = self.pos;
                while let Some(c) = self.peek() {
                    if matches!(c, ' ' | '\t' | '\r' | '\n' | '#' | ',' | ']' | '}') {
                        break;
                    }
                    self.pos += c.len_utf8();
                }
                let raw = self.s[start..self.pos].trim();
                ensure!(!raw.is_empty(), "expected TOML value at byte {}", self.pos);
                if raw == "true" {
                    return Ok(Value::Bool(true));
                }
                if raw == "false" {
                    return Ok(Value::Bool(false));
                }
                let clean = raw.replace('_', "");
                if let Some(hex) = clean.strip_prefix("0x") {
                    let v = i64::from_str_radix(hex, 16)
                        .with_context(|| format!("invalid hex integer `{raw}`"))?;
                    return Ok(Value::Number(v.into()));
                }
                if let Some(oct) = clean.strip_prefix("0o") {
                    let v = i64::from_str_radix(oct, 8)
                        .with_context(|| format!("invalid octal integer `{raw}`"))?;
                    return Ok(Value::Number(v.into()));
                }
                if let Some(bin) = clean.strip_prefix("0b") {
                    let v = i64::from_str_radix(bin, 2)
                        .with_context(|| format!("invalid binary integer `{raw}`"))?;
                    return Ok(Value::Number(v.into()));
                }
                if let Ok(v) = clean.parse::<i64>() {
                    return Ok(Value::Number(v.into()));
                }
                if let Ok(f) = clean.parse::<f64>()
                    && let Some(n) = serde_json::Number::from_f64(f)
                {
                    return Ok(Value::Number(n));
                }
                bail!("unsupported TOML literal `{raw}`")
            }
            None => bail!("unexpected EOF while reading TOML value"),
        }
    }
}

fn descend_table_mut<'a>(
    root: &'a mut Map<String, Value>,
    path: &[String],
) -> Result<&'a mut Map<String, Value>> {
    let mut cur = root;
    for seg in path {
        let entry = cur
            .entry(seg.clone())
            .or_insert_with(|| Value::Object(Map::new()));
        cur = match entry {
            Value::Object(m) => m,
            Value::Array(arr) => arr
                .last_mut()
                .and_then(Value::as_object_mut)
                .ok_or_else(|| anyhow!("TOML key `{seg}` collides with non-table array"))?,
            _ => bail!("TOML key `{seg}` collides with scalar value"),
        };
    }
    Ok(cur)
}

fn insert_dotted(target: &mut Map<String, Value>, key: &[String], val: Value) -> Result<()> {
    let (last, parents) = key.split_last().ok_or_else(|| anyhow!("empty TOML key"))?;
    let tbl = descend_table_mut(target, parents)?;
    ensure!(
        !tbl.contains_key(last),
        "duplicate TOML key `{}`",
        key.join(".")
    );
    tbl.insert(last.clone(), val);
    Ok(())
}

/// Parse a `Cargo.toml` document into a nested JSON object tree.
pub fn parse_cargo_toml(input: &str) -> Result<Map<String, Value>> {
    let mut p = TomlParser::new(input);
    let mut root = Map::new();
    let mut current_path: Vec<String> = Vec::new();
    let mut current_is_array = false;

    loop {
        p.skip_ws_and_comments();
        let Some(ch) = p.peek() else { break };
        if ch == '[' {
            p.pos += 1;
            let is_array = if p.peek() == Some('[') {
                p.pos += 1;
                true
            } else {
                false
            };
            let header = p.parse_dotted_key()?;
            p.skip_ws_inline();
            ensure!(
                p.advance_char() == Some(']'),
                "expected `]` closing TOML table header"
            );
            if is_array {
                ensure!(
                    p.advance_char() == Some(']'),
                    "expected `]]` closing TOML array-of-tables header"
                );
                let (last, parents) = header
                    .split_last()
                    .ok_or_else(|| anyhow!("empty `[[...]]` header"))?;
                let parent_tbl = descend_table_mut(&mut root, parents)?;
                let arr = parent_tbl
                    .entry(last.clone())
                    .or_insert_with(|| Value::Array(Vec::new()));
                let Value::Array(vec) = arr else {
                    bail!("`[[{}]]` collides with non-array key", header.join("."));
                };
                vec.push(Value::Object(Map::new()));
            } else {
                let _ = descend_table_mut(&mut root, &header)?;
            }
            p.skip_line_end()?;
            current_path = header;
            current_is_array = is_array;
        } else {
            let key = p.parse_dotted_key()?;
            p.skip_ws_inline();
            ensure!(
                p.advance_char() == Some('='),
                "expected `=` after key `{}`",
                key.join(".")
            );
            let val = p.parse_value()?;
            p.skip_line_end()?;
            let target = if current_is_array {
                let (last, parents) = current_path.split_last().unwrap();
                let parent_tbl = descend_table_mut(&mut root, parents)?;
                parent_tbl
                    .get_mut(last)
                    .and_then(Value::as_array_mut)
                    .and_then(|a| a.last_mut())
                    .and_then(Value::as_object_mut)
                    .ok_or_else(|| anyhow!("internal TOML array-of-tables state error"))?
            } else {
                descend_table_mut(&mut root, &current_path)?
            };
            insert_dotted(target, &key, val)?;
        }
    }
    Ok(root)
}

/// Validated metadata for an ordinary safe Rust `std` binary crate (`--main-rust <Cargo.toml>`).
#[derive(Debug, Clone)]
pub struct StdBinCrate {
    pub manifest_path: PathBuf,
    pub crate_dir: PathBuf,
    pub bin_stem: String,
}

/// Kind of `--main-rust <Cargo.toml>` crate.
#[derive(Debug, Clone)]
pub enum RustMainKind {
    /// Existing `#![no_std]` / custom `staticlib` driver (`[lib] crate-type = ["staticlib"]`).
    Staticlib,
    /// Ordinary safe Rust `std` binary crate (`src/main.rs` or `[[bin]]`).
    StdBin(StdBinCrate),
}

/// Strip Rust `//` line comments, nested `/* ... */` block comments, character literals, and
/// normal/raw string literals (`"..."`, `r#"..."#`) so crate-level `#![...]` attribute checks
/// never match commented-out or string-literal text.
fn strip_rust_comments_and_strings(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'/' && bytes.get(i + 1) == Some(&b'/') {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if bytes[i] == b'/' && bytes.get(i + 1) == Some(&b'*') {
            i += 2;
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                if bytes[i] == b'/' && bytes.get(i + 1) == Some(&b'*') {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'*' && bytes.get(i + 1) == Some(&b'/') {
                    depth -= 1;
                    i += 2;
                } else {
                    if bytes[i] == b'\n' {
                        out.push('\n');
                    }
                    i += 1;
                }
            }
            out.push(' ');
            continue;
        }
        if bytes[i] == b'r' || (bytes[i] == b'b' && bytes.get(i + 1) == Some(&b'r')) {
            let start_hashes = if bytes[i] == b'b' { i + 2 } else { i + 1 };
            let mut hashes = 0usize;
            while bytes.get(start_hashes + hashes) == Some(&b'#') {
                hashes += 1;
            }
            if bytes.get(start_hashes + hashes) == Some(&b'"') {
                i = start_hashes + hashes + 1;
                out.push_str("\"\"");
                'raw_str: while i < bytes.len() {
                    if bytes[i] == b'"' {
                        let mut ok = true;
                        for h in 0..hashes {
                            if bytes.get(i + 1 + h) != Some(&b'#') {
                                ok = false;
                                break;
                            }
                        }
                        if ok {
                            i += 1 + hashes;
                            break 'raw_str;
                        }
                    }
                    i += 1;
                }
                continue;
            }
        }
        if bytes[i] == b'"' {
            i += 1;
            out.push_str("\"\"");
            while i < bytes.len() {
                if bytes[i] == b'\\' {
                    i = (i + 2).min(bytes.len());
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        let ch = src[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn check_no_forbidden_crate_files(dir: &Path, is_root: bool) -> Result<()> {
    for entry in std::fs::read_dir(dir)
        .with_context(|| format!("cannot read crate directory {}", dir.display()))?
    {
        let entry = entry?;
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        let ft = entry.file_type()?;
        if name_str == "target" || name_str == ".git" {
            continue;
        }
        // Exclude `vendor/` directory or symlinks to pre-verified Rust crates.
        if name_str == "vendor" && (ft.is_dir() || ft.is_symlink()) {
            continue;
        }
        let path = entry.path();
        if is_root && name_str == "build.rs" {
            bail!(
                "std binary crate rejects `build.rs` build script at {}",
                path.display()
            );
        }
        if ft.is_dir() {
            check_no_forbidden_crate_files(&path, false)?;
        } else if ft.is_file() || ft.is_symlink() {
            if name_str == "build.rs" {
                bail!("std binary crate rejects `build.rs` at {}", path.display());
            }
            if let Some(ext) = path.extension().and_then(|e| e.to_str())
                && matches!(ext, "c" | "h" | "s" | "S")
            {
                bail!(
                    "std binary crate rejects native C/assembly source {} (`.{ext}`)",
                    path.display()
                );
            }
        }
    }
    Ok(())
}

/// Parse `<Cargo.toml>`, distinguish `staticlib` crates from `std` binary crates, and enforce all
/// manifest and source guards on `std` binary crates.
pub fn classify_rust_manifest(manifest_rel: &Path, repo_root: &Path) -> Result<RustMainKind> {
    let candidate = if manifest_rel.is_absolute() {
        manifest_rel.to_path_buf()
    } else {
        repo_root.join(manifest_rel)
    };
    let manifest_path = std::fs::canonicalize(&candidate)
        .with_context(|| format!("missing --main-rust manifest {}", candidate.display()))?;
    let crate_dir = manifest_path
        .parent()
        .ok_or_else(|| {
            anyhow!(
                "manifest {} has no parent directory",
                manifest_path.display()
            )
        })?
        .to_path_buf();

    let raw_toml = std::fs::read_to_string(&manifest_path)
        .with_context(|| format!("cannot read {}", manifest_path.display()))?;
    let doc = parse_cargo_toml(&raw_toml)
        .with_context(|| format!("invalid TOML in {}", manifest_path.display()))?;

    // 1. Check whether `[lib]` declares `crate-type` containing `"staticlib"`.
    if let Some(lib_tbl) = doc.get("lib").and_then(Value::as_object) {
        let crate_types = lib_tbl
            .get("crate-type")
            .or_else(|| lib_tbl.get("crate_type"))
            .and_then(Value::as_array);
        if crate_types.is_some_and(|arr| arr.iter().any(|v| v.as_str() == Some("staticlib"))) {
            return Ok(RustMainKind::Staticlib);
        }
    }

    // 2. Otherwise it must be a binary crate (`[[bin]]` or `src/main.rs`).
    let pkg_tbl = doc
        .get("package")
        .and_then(Value::as_object)
        .ok_or_else(|| {
            anyhow!(
                "--main-rust manifest {} has no `[package]` table",
                manifest_path.display()
            )
        })?;
    let pkg_name = pkg_tbl
        .get("name")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| {
            anyhow!(
                "--main-rust manifest {} is missing `[package].name`",
                manifest_path.display()
            )
        })?;

    if let Some(build_val) = pkg_tbl.get("build")
        && build_val != &Value::Bool(false)
    {
        bail!(
            "std binary crate {} rejects custom `[package].build = {build_val}`",
            manifest_path.display()
        );
    }

    let (bin_name, entry_source) = if let Some(bins) = doc.get("bin").and_then(Value::as_array) {
        ensure!(
            bins.len() == 1,
            "std binary crate {} must define a single binary target, found {} `[[bin]]` tables",
            manifest_path.display(),
            bins.len()
        );
        let b = bins[0]
            .as_object()
            .ok_or_else(|| anyhow!("invalid `[[bin]]` entry in {}", manifest_path.display()))?;
        let name = b
            .get("name")
            .and_then(Value::as_str)
            .unwrap_or(pkg_name)
            .to_string();
        let rel_path = b
            .get("path")
            .and_then(Value::as_str)
            .unwrap_or("src/main.rs");
        (name, crate_dir.join(rel_path))
    } else {
        let default_main = crate_dir.join("src").join("main.rs");
        ensure!(
            default_main.is_file(),
            "--main-rust manifest {} is neither a `staticlib` `[lib]` crate nor a binary crate (`src/main.rs` or `[[bin]]` missing)",
            manifest_path.display()
        );
        (pkg_name.to_string(), default_main)
    };

    ensure!(
        entry_source.is_file(),
        "std binary entry source {} does not exist",
        entry_source.display()
    );

    // 3. Guard: reject `[patch]` in `Cargo.toml`.
    ensure!(
        !doc.contains_key("patch"),
        "std binary crate {} rejects `[patch]` overrides",
        manifest_path.display()
    );

    // 4. Guard: reject `.cargo/config` or `.cargo/config.toml` in `crate_dir` or ancestors up to
    //    `repo_root` (stopping at `crate_dir` when outside `repo_root`).
    let mut cur: Option<&Path> = Some(&crate_dir);
    let within_repo = crate_dir.starts_with(repo_root);
    while let Some(dir) = cur {
        for cfg_name in ["config", "config.toml"] {
            let cargo_cfg = dir.join(".cargo").join(cfg_name);
            ensure!(
                !cargo_cfg.exists(),
                "std binary crate rejects `.cargo/{cfg_name}` override at {}",
                cargo_cfg.display()
            );
        }
        if !within_repo || dir == repo_root {
            break;
        }
        cur = dir.parent();
    }

    // 5. Guard: reject `build.rs` and `.c`/`.h`/`.s`/`.S` files in `crate_dir` (excluding `vendor/`).
    check_no_forbidden_crate_files(&crate_dir, true)?;

    // 6. Guard: `[profile.release]` must specify `opt-level = 2`, `codegen-units = 1`, and
    //    `lto = "fat"` (or `lto = true`).
    let release = doc
        .get("profile")
        .and_then(Value::as_object)
        .and_then(|p| p.get("release"))
        .and_then(Value::as_object)
        .ok_or_else(|| {
            anyhow!(
                "std binary crate {} must define `[profile.release]` with `opt-level = 2`, `codegen-units = 1`, and `lto = \"fat\"`",
                manifest_path.display()
            )
        })?;

    let opt_ok = release.get("opt-level").and_then(Value::as_i64) == Some(2);
    ensure!(
        opt_ok,
        "std binary crate {} must set `opt-level = 2` in `[profile.release]` (found {:?})",
        manifest_path.display(),
        release.get("opt-level")
    );

    let cgu_ok = release.get("codegen-units").and_then(Value::as_i64) == Some(1);
    ensure!(
        cgu_ok,
        "std binary crate {} must set `codegen-units = 1` in `[profile.release]` (found {:?})",
        manifest_path.display(),
        release.get("codegen-units")
    );

    let lto_ok = matches!(
        release.get("lto"),
        Some(Value::String(s)) if s == "fat"
    ) || release.get("lto") == Some(&Value::Bool(true));
    ensure!(
        lto_ok,
        "std binary crate {} must set `lto = \"fat\"` (or `lto = true`) in `[profile.release]` (found {:?})",
        manifest_path.display(),
        release.get("lto")
    );

    // 7. Guard: entry source must contain `#![forbid(unsafe_code)]` and must NOT contain `#![no_std]`.
    let raw_src = std::fs::read_to_string(&entry_source)
        .with_context(|| format!("cannot read binary entry source {}", entry_source.display()))?;
    let stripped: String = strip_rust_comments_and_strings(&raw_src)
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();
    ensure!(
        !stripped.contains("#![no_std]"),
        "std binary entry source {} must not specify `#![no_std]`",
        entry_source.display()
    );
    ensure!(
        stripped.contains("#![forbid(unsafe_code)]"),
        "std binary entry source {} must specify `#![forbid(unsafe_code)]`",
        entry_source.display()
    );

    Ok(RustMainKind::StdBin(StdBinCrate {
        manifest_path,
        crate_dir,
        bin_stem: bin_name.replace('-', "_"),
    }))
}

// ---------------------------------------------------------------------------
// Deterministic `-Zbuild-std` object compilation & staging
// ---------------------------------------------------------------------------

fn push_remap_pair(remaps: &mut Vec<(PathBuf, String)>, dir: &Path, to: &str) {
    let push_unique = |remaps: &mut Vec<(PathBuf, String)>, p: PathBuf| {
        if !remaps.iter().any(|(existing, _)| existing == &p) {
            remaps.push((p, to.to_string()));
        }
    };
    push_unique(remaps, dir.to_path_buf());
    if let Ok(canon) = std::fs::canonicalize(dir)
        && canon != dir
    {
        push_unique(remaps, canon);
    }
}

/// Build `CARGO_ENCODED_RUSTFLAGS` for the pinned Rust 1.98.1 `std` binary build profile.
pub fn std_encoded_rustflags(
    repo_root: &Path,
    crate_dir: &Path,
    work: &Path,
    cargo_home: Option<&Path>,
    rustup_home: Option<&Path>,
    sysroot: &Path,
) -> String {
    let mut flags = vec![
        "-Zunstable-options".to_string(),
        "-Cpanic=immediate-abort".to_string(),
        "-Crelocation-model=static".to_string(),
        "-Clinker-flavor=gnu-lld".to_string(),
        "-Clinker=rust-lld".to_string(),
        "-Cstrip=debuginfo".to_string(),
        "-Cmetadata=snapstd".to_string(),
    ];
    flags.extend(
        untrusted_driver::config::DETERMINISTIC_CODEGEN_FLAGS
            .iter()
            .map(|s| s.to_string()),
    );

    let mut remaps: Vec<(PathBuf, String)> = Vec::new();
    push_remap_pair(&mut remaps, repo_root, "/src");
    if !crate_dir.starts_with(repo_root) {
        push_remap_pair(&mut remaps, crate_dir, "/src");
    }
    push_remap_pair(&mut remaps, work, "/work");
    if let Some(ch) = cargo_home {
        push_remap_pair(&mut remaps, ch, "/cargo");
    }
    if let Some(rh) = rustup_home {
        push_remap_pair(&mut remaps, rh, "/rustup");
    }
    let rust_src = sysroot.join("lib").join("rustlib").join("src").join("rust");
    let rustc_to = format!("/rustc/{PINNED_RUSTC_COMMIT}");
    push_remap_pair(&mut remaps, &rust_src, &rustc_to);

    // `rustc` applies the last matching `--remap-path-prefix`, so sort ancestor paths before
    // nested paths (e.g. `repo_root` before `work` when `--out-dir` is inside `repo_root`, and
    // `rustup_home` before `sysroot/lib/rustlib/src/rust`).
    let all_dirs: Vec<PathBuf> = remaps.iter().map(|(d, _)| d.clone()).collect();
    remaps.sort_by_cached_key(|(d, _)| {
        all_dirs
            .iter()
            .filter(|other| *other != d && d.starts_with(*other))
            .count()
    });

    for (from, to) in remaps {
        flags.push(format!("--remap-path-prefix={}={to}", from.display()));
    }
    flags.join("\x1f")
}

/// Compile `std_crate` with `-Zbuild-std=std,panic_abort -- --emit=obj` and stage
/// `work/main_rust.o` (weakening any symbol in `image_exports`) and `work/compiler_builtins.a`.
pub fn build_std_main_objects(
    tc: &StdToolchain,
    std_crate: &StdBinCrate,
    repo_root: &Path,
    work: &Path,
    objcopy: &Path,
    image_exports: &HashSet<String>,
) -> Result<(PathBuf, PathBuf)> {
    let target_dir = work.join("rust-target");
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")));
    let rustup_home = std::env::var_os("RUSTUP_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".rustup")));
    let encoded_flags = std_encoded_rustflags(
        repo_root,
        &std_crate.crate_dir,
        work,
        cargo_home.as_deref(),
        rustup_home.as_deref(),
        &tc.sysroot,
    );

    let mut c = Command::new(&tc.cargo_bin);
    c.current_dir(repo_root)
        .args(&tc.cargo_prefix_args)
        .env("RUSTC_BOOTSTRAP", "1")
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("CARGO_ENCODED_RUSTFLAGS", encoded_flags)
        .env_remove("RUSTFLAGS");
    if tc.rustc_prefix_args.is_empty() {
        c.env("RUSTC", &tc.rustc_bin);
    }
    c.args(["rustc", "--manifest-path"])
        .arg(&std_crate.manifest_path)
        .args([
            "--target",
            MUSL_TARGET,
            "--release",
            "--locked",
            "-Zbuild-std=std,panic_abort",
            "--",
            "--emit=obj",
        ]);
    run_cmd(&mut c)?;

    let deps_dir = target_dir.join(MUSL_TARGET).join("release").join("deps");
    let prefix = format!("{}-", std_crate.bin_stem);
    let mut main_objs: Vec<PathBuf> = Vec::new();
    let mut rcgu_objs: Vec<PathBuf> = Vec::new();
    let mut builtins_rlibs: Vec<PathBuf> = Vec::new();

    for entry in std::fs::read_dir(&deps_dir)
        .with_context(|| format!("missing cargo deps dir {}", deps_dir.display()))?
    {
        let p = entry?.path();
        if !p.is_file() {
            continue;
        }
        let Some(name) = p.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if name.starts_with(&prefix) && name.ends_with(".o") {
            if name.ends_with(".rcgu.o") {
                rcgu_objs.push(p);
            } else {
                main_objs.push(p);
            }
        } else if name.starts_with("libcompiler_builtins-") && name.ends_with(".rlib") {
            builtins_rlibs.push(p);
        }
    }
    main_objs.sort();
    rcgu_objs.sort();
    builtins_rlibs.sort();

    let raw_main_o = if main_objs.len() == 1 {
        &main_objs[0]
    } else if main_objs.is_empty() && rcgu_objs.len() == 1 {
        &rcgu_objs[0]
    } else {
        bail!(
            "expected a single emitted LTO object `{prefix}*.o` in {}, found {:?} (rcgu: {:?})",
            deps_dir.display(),
            main_objs,
            rcgu_objs
        );
    };

    ensure!(
        builtins_rlibs.len() == 1,
        "expected a single `libcompiler_builtins-*.rlib` in {}, found {:?}",
        deps_dir.display(),
        builtins_rlibs
    );

    // Stage `work/main_rust.o` with debug stripped and any symbols already exported by pre-verified
    // `images` weakened so calls bind to the pinned image and `--gc-sections` drops duplicates.
    let mut weaken: Vec<String> = Vec::new();
    if !image_exports.is_empty() {
        let raw_bytes = std::fs::read(raw_main_o)?;
        let parsed = object::File::parse(raw_bytes.as_slice())
            .with_context(|| format!("cannot parse emitted object {}", raw_main_o.display()))?;
        for sym in parsed.symbols() {
            if sym.is_undefined() || sym.is_local() {
                continue;
            }
            if let Ok(name) = sym.name()
                && image_exports.contains(name)
            {
                weaken.push(name.to_string());
            }
        }
        weaken.sort();
        weaken.dedup();
    }

    let out_main_o = work.join("main_rust.o");
    let mut oc = Command::new(objcopy);
    oc.arg("--strip-debug");
    for sym in &weaken {
        oc.arg(format!("--weaken-symbol={sym}"));
    }
    run_cmd(oc.arg(raw_main_o).arg(&out_main_o))?;

    // Stage `work/compiler_builtins.a` from `libcompiler_builtins-*.rlib`: drop non-ELF `.rmeta`
    // members first, then strip debug info and normalize member names deterministically.
    let raw_rlib_bytes = std::fs::read(&builtins_rlibs[0])?;
    let obj_only_ar = filter_gnu_archive_obj_members(&raw_rlib_bytes)?;
    let raw_builtins_a = work.join("compiler_builtins.raw.a");
    let out_builtins_a = work.join("compiler_builtins.a");
    std::fs::write(&raw_builtins_a, obj_only_ar)?;
    run_cmd(
        Command::new(objcopy)
            .args(["--enable-deterministic-archives", "--strip-debug"])
            .arg(&raw_builtins_a)
            .arg(&out_builtins_a),
    )?;
    let _ = std::fs::remove_file(&raw_builtins_a);
    let normalized = normalize_gnu_archive_member_names(&std::fs::read(&out_builtins_a)?)?;
    std::fs::write(&out_builtins_a, normalized)?;

    Ok((out_main_o, out_builtins_a))
}

// ---------------------------------------------------------------------------
// Global-allocator extern bridge for `#![no_std]` + `alloc` pre-verified images
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocShimKind {
    NoAllocShimIsUnstableV2,
    Alloc,
    Dealloc,
    Realloc,
    AllocZeroed,
    AllocErrorHandler,
}

/// Match a raw extern symbol name (`_RNvCs<hash>_7___rustc<len>___rust_*` or unmangled
/// `__rust_*`) to its Rust global-allocator shim kind, if any.
pub fn classify_alloc_shim(raw: &str) -> Option<AllocShimKind> {
    if raw == "__rust_no_alloc_shim_is_unstable_v2"
        || raw.ends_with("___rust_no_alloc_shim_is_unstable_v2")
    {
        Some(AllocShimKind::NoAllocShimIsUnstableV2)
    } else if raw == "__rust_alloc" || raw.ends_with("___rust_alloc") {
        Some(AllocShimKind::Alloc)
    } else if raw == "__rust_dealloc" || raw.ends_with("___rust_dealloc") {
        Some(AllocShimKind::Dealloc)
    } else if raw == "__rust_realloc" || raw.ends_with("___rust_realloc") {
        Some(AllocShimKind::Realloc)
    } else if raw == "__rust_alloc_zeroed" || raw.ends_with("___rust_alloc_zeroed") {
        Some(AllocShimKind::AllocZeroed)
    } else if raw == "__rust_alloc_error_handler" || raw.ends_with("___rust_alloc_error_handler") {
        Some(AllocShimKind::AllocErrorHandler)
    } else {
        None
    }
}

/// Return global/weak defined symbol names in an ELF relocatable object.
pub fn defined_nonlocal_symbols(obj_bytes: &[u8]) -> Result<HashSet<String>> {
    let parsed = object::File::parse(obj_bytes).context("cannot parse ELF relocatable object")?;
    let mut out = HashSet::new();
    for s in parsed.symbols() {
        if !s.is_undefined()
            && !s.is_local()
            && let Ok(name) = s.name()
            && !name.is_empty()
        {
            out.insert(name.to_string());
        }
    }
    Ok(out)
}

fn asm_quote(sym: &str) -> String {
    if sym
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'$'))
    {
        sym.to_string()
    } else {
        format!("\"{}\"", sym.replace('\\', "\\\\").replace('"', "\\\""))
    }
}

/// Emit AArch64 assembly bridges forwarding `___rustc::__rust_*` global-allocator shims to
/// `libc.a`'s `malloc` / `posix_memalign` / `free` / `calloc` / `realloc`, matching
/// `std::sys::alloc::unix::System` (`MIN_ALIGN = 16` on AArch64).
pub fn rust_alloc_bridge_asm(raw_syms: &[String]) -> String {
    let mut items: Vec<(&str, AllocShimKind)> = raw_syms
        .iter()
        .filter_map(|s| classify_alloc_shim(s).map(|k| (s.as_str(), k)))
        .collect();
    if items.is_empty() {
        return String::new();
    }
    items.sort_by_key(|(s, _)| *s);
    items.dedup_by_key(|(s, _)| *s);

    let mut asm = String::new();
    let needs_aligned_helper = items.iter().any(|(_, k)| {
        matches!(
            k,
            AllocShimKind::Alloc | AllocShimKind::AllocZeroed | AllocShimKind::Realloc
        )
    });

    if needs_aligned_helper {
        // Shared local helper `(x0 = size, x1 = align) -> x0 = ptr` via `posix_memalign`.
        asm += ".section .text.__snap_aligned_alloc,\"ax\",@progbits\n\
                .p2align 2\n\
                .L__snap_aligned_alloc:\n\
                stp x29, x30, [sp, #-32]!\n\
                mov x29, sp\n\
                str xzr, [sp, #16]\n\
                mov x2, x0\n\
                cmp x1, #8\n\
                mov x8, #8\n\
                csel x1, x1, x8, hi\n\
                add x0, sp, #16\n\
                bl posix_memalign\n\
                ldr x8, [sp, #16]\n\
                cmp w0, #0\n\
                csel x0, x8, xzr, eq\n\
                ldp x29, x30, [sp], #32\n\
                ret\n";
    }

    for (idx, (raw, kind)) in items.into_iter().enumerate() {
        let q = asm_quote(raw);
        asm += &format!(
            ".section .text.__snap_alloc_bridge_{idx},\"ax\",@progbits\n\
             .p2align 2\n\
             .globl {q}\n\
             .type {q},@function\n\
             {q}:\n"
        );
        match kind {
            AllocShimKind::NoAllocShimIsUnstableV2 => {
                asm += "ret\n";
            }
            AllocShimKind::Dealloc => {
                asm += "b free\n";
            }
            AllocShimKind::Alloc => {
                asm += "cmp x1, #16\n\
                        b.hi .L__snap_aligned_alloc\n\
                        cmp x1, x0\n\
                        b.hi .L__snap_aligned_alloc\n\
                        b malloc\n";
            }
            AllocShimKind::AllocZeroed => {
                asm += &format!(
                    "cmp x1, #16\n\
                     b.hi .L__snap_az_slow_{idx}\n\
                     cmp x1, x0\n\
                     b.hi .L__snap_az_slow_{idx}\n\
                     mov x1, #1\n\
                     b calloc\n\
                     .L__snap_az_slow_{idx}:\n\
                     stp x29, x30, [sp, #-32]!\n\
                     mov x29, sp\n\
                     str x19, [sp, #16]\n\
                     mov x19, x0\n\
                     bl .L__snap_aligned_alloc\n\
                     cbz x0, .L__snap_az_done_{idx}\n\
                     mov x1, #0\n\
                     mov x2, x19\n\
                     bl memset\n\
                     .L__snap_az_done_{idx}:\n\
                     ldr x19, [sp, #16]\n\
                     ldp x29, x30, [sp], #32\n\
                     ret\n"
                );
            }
            AllocShimKind::Realloc => {
                asm += &format!(
                    "cmp x2, #16\n\
                     b.hi .L__snap_re_slow_{idx}\n\
                     cmp x2, x3\n\
                     b.hi .L__snap_re_slow_{idx}\n\
                     mov x1, x3\n\
                     b realloc\n\
                     .L__snap_re_slow_{idx}:\n\
                     stp x29, x30, [sp, #-48]!\n\
                     mov x29, sp\n\
                     stp x19, x20, [sp, #16]\n\
                     str x21, [sp, #32]\n\
                     mov x19, x0\n\
                     cmp x1, x3\n\
                     csel x20, x1, x3, lo\n\
                     mov x0, x3\n\
                     mov x1, x2\n\
                     bl .L__snap_aligned_alloc\n\
                     mov x21, x0\n\
                     cbz x0, .L__snap_re_done_{idx}\n\
                     mov x1, x19\n\
                     mov x2, x20\n\
                     bl memcpy\n\
                     mov x0, x19\n\
                     bl free\n\
                     mov x0, x21\n\
                     .L__snap_re_done_{idx}:\n\
                     ldr x21, [sp, #32]\n\
                     ldp x19, x20, [sp, #16]\n\
                     ldp x29, x30, [sp], #48\n\
                     ret\n"
                );
            }
            AllocShimKind::AllocErrorHandler => {
                asm += "brk #0x1\n";
            }
        }
    }
    asm
}
