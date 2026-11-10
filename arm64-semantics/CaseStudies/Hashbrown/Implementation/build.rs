// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Reproducible `aarch64-unknown-linux-musl` link step for `hashbrown-cli`.
//!
//! In Rust 1.98.1's prebuilt `aarch64-unknown-linux-musl` sysroot `libc.a`, `__vm_lock` and
//! `__vm_unlock` are garbage-collected by `--gc-sections` in single-threaded binaries, but
//! `pthread_mutex_unlock.lo` carries `U __vm_lock` before section GC, pulling in `vmlock.lo` and
//! letting its strong `T __vm_wait` override `munmap.lo`'s stock single-threaded weak `W __vm_wait`
//! (`ret`, `0xd65f03c0`).
//!
//! Staging sysroot `libc.a` under `$OUT_DIR` (inside Cargo's `target/` directory) with
//! `vmlock.lo`'s `__vm_wait` renamed to `__vmlock_unused_vm_wait` keeps `munmap.lo`'s 1-instruction
//! weak `W __vm_wait` (`ret`) and lets `--gc-sections` drop `vmlock` completely.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn tool_in_sysroot_or_path(sysroot: &Path, host: &str, name: &str) -> PathBuf {
    let candidate = sysroot.join("lib/rustlib").join(host).join("bin").join(name);
    if candidate.exists() {
        candidate
    } else {
        PathBuf::from(name)
    }
}

fn run(cmd: &mut Command, desc: &str) {
    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("failed to spawn {desc}: {e}"));
    assert!(status.success(), "{desc} exited with {status}");
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let target = env::var("TARGET").expect("TARGET");
    if target != "aarch64-unknown-linux-musl" {
        return;
    }

    let host = env::var("HOST").expect("HOST");
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let out = Command::new(&rustc)
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot");
    assert!(out.status.success(), "rustc --print sysroot failed");
    let sysroot = PathBuf::from(
        String::from_utf8(out.stdout)
            .expect("utf8 sysroot")
            .trim(),
    );

    let src_libc = sysroot
        .join("lib/rustlib")
        .join(&target)
        .join("lib/self-contained/libc.a");
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
    let stage_dir = out_dir.join("musl_vmlock_free");
    let _ = fs::remove_dir_all(&stage_dir);
    fs::create_dir_all(&stage_dir).expect("create stage_dir");

    let dst_libc = stage_dir.join("libc.a");
    fs::copy(&src_libc, &dst_libc).expect("copy sysroot libc.a");

    let llvm_ar = tool_in_sysroot_or_path(&sysroot, &host, "llvm-ar");
    let llvm_objcopy = tool_in_sysroot_or_path(&sysroot, &host, "llvm-objcopy");

    run(
        Command::new(&llvm_ar)
            .current_dir(&stage_dir)
            .args(["x", "libc.a", "vmlock.lo"]),
        "llvm-ar x libc.a vmlock.lo",
    );
    run(
        Command::new(&llvm_objcopy)
            .current_dir(&stage_dir)
            .args([
                "--redefine-sym",
                "__vm_wait=__vmlock_unused_vm_wait",
                "vmlock.lo",
            ]),
        "llvm-objcopy --redefine-sym __vm_wait=__vmlock_unused_vm_wait vmlock.lo",
    );
    run(
        Command::new(&llvm_ar)
            .current_dir(&stage_dir)
            .args(["rcsD", "libc.a", "vmlock.lo"]),
        "llvm-ar rcsD libc.a vmlock.lo",
    );
    fs::remove_file(stage_dir.join("vmlock.lo")).expect("remove staged vmlock.lo");

    println!("cargo:rustc-link-search=native={}", stage_dir.display());
}
