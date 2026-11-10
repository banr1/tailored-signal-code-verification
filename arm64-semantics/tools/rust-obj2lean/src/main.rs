// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Binary entry point for `rust-obj2lean` (`[OUTSIDE TCB]` CLI stub).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** Thin binary wrapper delegating immediately to
//!   [`rust_obj2lean::untrusted_driver::pipeline::cli_main`], which orchestrates both `[TCB]`
//!   extraction/linking (`<ObjName>Obj.lean` + `.bin` sidecars) and `[OUTSIDE TCB]`
//!   lemma/symexec generation (`<ObjName>Code.lean` + per-target `.lean`).
//! - **Purpose:** Invokes `cli_main` and returns its [`std::process::ExitCode`].
//!
//! # When to Read This File
//! - Never; this file is a stub. Read `untrusted_driver/pipeline.rs` for CLI dispatch and
//!   pipeline orchestration.

use std::process::ExitCode;

fn main() -> ExitCode {
    rust_obj2lean::untrusted_driver::pipeline::cli_main()
}
