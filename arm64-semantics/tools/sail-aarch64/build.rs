// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Cargo build script for `sail-aarch64` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (compiles and links the official Sail Armv9.4-A C model
//!   and `csrc/sail_ffi.c` into the `sail-aarch64` simulator library crate).
//! - **Purpose:** Ensures the checksum-verified Sail Armv9.4-A (`armv9.c`) and Sail 0.17.1
//!   C runtime (`sail.c`, `rts.c`, `sail_failure.c`) are unpacked in `$ARM64_UPSTREAM_CACHE`,
//!   locates `gmp.h` and `libgmp`, and delegates compilation and `ld -r --wrap=...` partial
//!   linking to `csrc/Makefile` to produce a self-contained `libsail_aarch64_ffi.a`.
//!
//! # Key Types & Functions
//! - `ensure_sail_sources`: Runs `scripts/fetch-upstream-sources.sh sail-arm` if not yet unpacked
//!   (or uses `$SAIL_ARMV9_SRC_DIR` if overridden).
//! - `ensure_gmp`: Locates `gmp.h` and `libgmp`.
//!
//! # When to Read This File
//! - Read this file when updating the Sail C snapshot pin or C compiler/linker discovery.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const SAIL_CACHE_ID: &str = "44b10531cb18ebba-b874093312c13dd4";

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

fn ensure_sail_sources(repo_root: &Path, cache_dir: &Path) -> PathBuf {
    if let Some(custom_dir) = env::var_os("SAIL_ARMV9_SRC_DIR") {
        let dir = PathBuf::from(custom_dir);
        assert!(
            dir.join("armv9.c").is_file(),
            "SAIL_ARMV9_SRC_DIR={} does not contain armv9.c",
            dir.display()
        );
        return dir;
    }
    let src_dir = cache_dir
        .join("sail-armv9")
        .join(format!("src-{SAIL_CACHE_ID}"));
    if src_dir.join(".unpacked").is_file() && src_dir.join("armv9.c").is_file() {
        return src_dir;
    }
    let script = repo_root.join("scripts").join("fetch-upstream-sources.sh");
    let status = Command::new(&script)
        .arg("sail-arm")
        .current_dir(repo_root)
        .status()
        .expect("failed to execute `scripts/fetch-upstream-sources.sh sail-arm`");
    assert!(
        status.success(),
        "`scripts/fetch-upstream-sources.sh sail-arm` exited with {status}"
    );
    src_dir
}

fn ensure_gmp(cache_dir: &Path, out_dir: &Path) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let home = env::var_os("HOME").map(PathBuf::from);
    let cached_gmp_root = cache_dir.join("sail-armv9").join("gmp");

    let mut candidate_inc = vec![
        PathBuf::from("/usr/include"),
        PathBuf::from("/usr/include/x86_64-linux-gnu"),
        PathBuf::from("/usr/include/aarch64-linux-gnu"),
    ];
    if let Some(h) = &home {
        candidate_inc.push(h.join(".local/include"));
    }
    candidate_inc.push(cached_gmp_root.join("usr/include"));
    candidate_inc.push(cached_gmp_root.join("usr/include/x86_64-linux-gnu"));
    candidate_inc.push(cached_gmp_root.join("usr/include/aarch64-linux-gnu"));

    let inc_dirs: Vec<PathBuf> = candidate_inc
        .into_iter()
        .filter(|p| p.join("gmp.h").is_file())
        .collect();
    assert!(
        !inc_dirs.is_empty(),
        "gmp.h not found in system include paths, ~/.local/include, or the upstream cache; install libgmp-dev"
    );

    let mut candidate_lib = vec![
        PathBuf::from("/usr/lib/x86_64-linux-gnu"),
        PathBuf::from("/usr/lib/aarch64-linux-gnu"),
        PathBuf::from("/usr/lib64"),
        PathBuf::from("/usr/lib"),
    ];
    if let Some(h) = &home {
        candidate_lib.push(h.join(".local/lib"));
    }
    candidate_lib.push(cached_gmp_root.join("usr/lib/x86_64-linux-gnu"));
    candidate_lib.push(cached_gmp_root.join("usr/lib/aarch64-linux-gnu"));

    let mut lib_dirs: Vec<PathBuf> = candidate_lib
        .iter()
        .filter(|p| p.join("libgmp.so").exists() || p.join("libgmp.a").exists())
        .cloned()
        .collect();

    if lib_dirs.is_empty() {
        for dir in &candidate_lib {
            let so10 = dir.join("libgmp.so.10");
            if so10.exists() {
                let link_path = out_dir.join("libgmp.so");
                let _ = fs::remove_file(&link_path);
                #[cfg(unix)]
                std::os::unix::fs::symlink(&so10, &link_path)
                    .expect("failed to symlink libgmp.so -> libgmp.so.10");
                lib_dirs.push(out_dir.to_path_buf());
                break;
            }
        }
    }
    assert!(
        !lib_dirs.is_empty(),
        "libgmp not found in system library paths or ~/.local/lib; install libgmp-dev"
    );

    (inc_dirs, lib_dirs)
}

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("tools/sail-aarch64 must be two levels below repo root");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let cache_dir = upstream_cache_dir();
    let sail_cache_dir = cache_dir.join("sail-armv9");
    fs::create_dir_all(&sail_cache_dir).expect("failed to create sail-armv9 cache dir");

    let src_dir = ensure_sail_sources(repo_root, &cache_dir);
    let (inc_dirs, lib_dirs) = ensure_gmp(&cache_dir, &out_dir);
    let sail_cache_lib = sail_cache_dir.join(format!("libsail_armv9-{SAIL_CACHE_ID}.a"));

    let extra_inc = inc_dirs
        .iter()
        .map(|d| format!("-I{}", d.display()))
        .collect::<Vec<_>>()
        .join(" ");

    let status = Command::new("make")
        .arg("-C")
        .arg(manifest_dir.join("csrc"))
        .arg(format!("SAIL_SRC_DIR={}", src_dir.display()))
        .arg(format!("SAIL_CACHE_LIB={}", sail_cache_lib.display()))
        .arg(format!("OUT_DIR={}", out_dir.display()))
        .arg(format!("EXTRA_INC={extra_inc}"))
        .status()
        .expect("failed to run `make -C csrc` in tools/sail-aarch64");
    assert!(status.success(), "`make -C csrc` failed with {status}");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    for dir in &lib_dirs {
        println!("cargo:rustc-link-search=native={}", dir.display());
    }
    println!("cargo:rustc-link-lib=static=sail_aarch64_ffi");
    println!("cargo:rustc-link-lib=gmp");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=csrc/Makefile");
    println!("cargo:rerun-if-changed=csrc/sail_ffi.c");
}
