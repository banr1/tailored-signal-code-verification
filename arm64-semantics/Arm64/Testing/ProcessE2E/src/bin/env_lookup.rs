// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `env_lookup`: `#![no_main]` Rust `std` on static musl querying the initial environment.
//!
//! - `env_lookup NAME...`: prints `NAME=value` via musl `getenv` (`std::env::var_os`) for each
//!   name, or `NAME is unset` on `stderr`; exits `1` if any name is unset.
//! - `env_lookup --sorted`: prints every `environ` entry sorted bytewise plus a count, walking the
//!   raw `environ` array.
//! - No arguments: usage on `stderr` (`exit 2`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args, read_envp};
use std::ffi::{OsStr, c_char, c_int};
use std::io::{self, Write};
use std::os::unix::ffi::OsStrExt;

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mut text = Vec::new();
    let mut err = io::stderr();
    let code = match args.get(1..).unwrap_or(&[]) {
        [] => {
            let _ = err.write_all(b"usage: env_lookup NAME... | --sorted\n");
            return 2;
        }
        [flag] if *flag == b"--sorted" => {
            let mut envs = unsafe { read_envp() };
            envs.sort_unstable();
            for e in &envs {
                text.extend_from_slice(e);
                text.push(b'\n');
            }
            let _ = writeln!(text, "count={}", envs.len());
            0
        }
        names => {
            let mut code = 0;
            for name in names {
                match std::env::var_os(OsStr::from_bytes(name)) {
                    Some(v) => {
                        text.extend_from_slice(name);
                        text.push(b'=');
                        text.extend_from_slice(v.as_bytes());
                        text.push(b'\n');
                    }
                    None => {
                        let _ = err.write_all(name);
                        let _ = err.write_all(b" is unset\n");
                        code = 1;
                    }
                }
            }
            code
        }
    };
    let mut out = io::stdout();
    if out.write_all(&text).and_then(|()| out.flush()).is_err() {
        return 2;
    }
    code
}
