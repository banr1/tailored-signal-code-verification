// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `std_startup_probe`: normal Rust `fn main()` (NO `#![no_main]`) on static `aarch64-unknown-linux-musl`.
//!
//! Exercises full `std::rt::lang_start` runtime initialization and teardown so QEMU `-strace`
//! records every syscall emitted before and after `main()`, while Lean `runElf` confirms the first
//! unmodeled startup syscall (`SYS_ppoll = 73` in `sanitize_standard_fds`).

use std::io::{self, Write};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let _ = writeln!(io::stdout(), "std_startup_probe argc={}", args.len());
}
