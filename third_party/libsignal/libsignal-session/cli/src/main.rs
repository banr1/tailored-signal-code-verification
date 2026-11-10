// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. See
// `third_party/libsignal/README.md`.

//! The `libsignal-cli` executable: the library's `main` (`src/lib.rs`), which musl's
//! `__libc_start_main` calls directly. Rust's own startup (`lang_start`) would make syscalls that
//! the ARM64 process model does not have.

#![no_main]

use libsignal_cli as _;
