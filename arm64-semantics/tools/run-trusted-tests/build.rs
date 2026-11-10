// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Cargo build script for `run-trusted-tests` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (compiles and links the Berkeley SoftFloat 3e IEEE-754
//!   oracle and `csrc/softfloat_ffi.c` into `run-trusted-tests`; the Sail Armv9.4-A ISA
//!   simulator is built and linked by the standalone `tools/sail-aarch64` crate).
//! - **Purpose:** Ensures the checksum-verified SoftFloat 3e (`ARM-VFPv2`), TestFloat 3e,
//!   and RISU sources are unpacked in `$ARM64_UPSTREAM_CACHE/fp-tools`, then invokes
//!   `csrc/Makefile` to build `libsoftfloat_armvfpv2.a`, `testfloat_gen`, and
//!   `libsoftfloat_ffi.a`.
//!
//! # Key Types & Functions
//! - `ensure_fp_sources`: Runs `scripts/fetch-upstream-sources.sh fp-tools` if not yet unpacked.
//!
//! # When to Read This File
//! - Read this file when updating SoftFloat 3e / TestFloat 3e build flags.
//! - For Sail Armv9.4-A C compilation, read `tools/sail-aarch64/build.rs` and
//!   `tools/sail-aarch64/csrc/Makefile`.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn upstream_cache_dir() -> PathBuf {
    if let Some(dir) = env::var_os("ARM64_UPSTREAM_CACHE") {
        return PathBuf::from(dir);
    }
    if let Some(xdg) = env::var_os("XDG_CACHE_HOME") {
        return PathBuf::from(xdg).join("arm64-verification-engine");
    }
    let home = env::var_os("HOME").expect("HOME must be set");
    PathBuf::from(home)
        .join(".cache")
        .join("arm64-verification-engine")
}

fn ensure_fp_sources(repo_root: &Path, cache_dir: &Path) -> PathBuf {
    let fp_dir = cache_dir.join("fp-tools");
    let sf_inc = fp_dir.join("softfloat3").join("source").join("include");
    let tf_src = fp_dir.join("testfloat3").join("source");
    let risu_file = fp_dir.join("risu").join("aarch64.risu");
    if !sf_inc.join("softfloat.h").is_file()
        || !tf_src.join("testfloat_gen.c").is_file()
        || !risu_file.is_file()
    {
        let script = repo_root.join("scripts").join("fetch-upstream-sources.sh");
        let status = Command::new(&script)
            .arg("fp-tools")
            .current_dir(repo_root)
            .status()
            .expect("failed to execute `scripts/fetch-upstream-sources.sh fp-tools`");
        assert!(
            status.success(),
            "`scripts/fetch-upstream-sources.sh fp-tools` exited with {status}"
        );
    }
    fp_dir
}

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("tools/run-trusted-tests must be two levels below repo root");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let cache_dir = upstream_cache_dir();
    let fp_dir = ensure_fp_sources(repo_root, &cache_dir);

    let status = Command::new("make")
        .arg("-C")
        .arg(manifest_dir.join("csrc"))
        .arg(format!("FP_TOOLS_DIR={}", fp_dir.display()))
        .arg(format!("OUT_DIR={}", out_dir.display()))
        .status()
        .expect("failed to execute `make -C csrc` in tools/run-trusted-tests");
    assert!(status.success(), "`make -C csrc` exited with {status}");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-search=native={}", fp_dir.display());
    println!("cargo:rustc-link-lib=static=softfloat_ffi");
    println!("cargo:rustc-link-lib=static=softfloat_armvfpv2");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=csrc/Makefile");
    println!("cargo:rerun-if-changed=csrc/softfloat_ffi.c");
}
