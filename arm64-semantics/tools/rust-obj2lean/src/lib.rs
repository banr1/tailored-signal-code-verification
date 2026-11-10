// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Object-level `cargo` / `zig cc` -> Lean 4 exporter (`rust-obj2lean`) for AArch64 verification.
//!
//! # Purpose & Trust Role (`[TCB]` + `[OUTSIDE TCB]` Split)
//! Compiles each configured Rust crate or C translation unit to relocatable AArch64 `.o` objects
//! and emits Lean 4 modules separated by trust role:
//! 1. [`trusted_common`] (`[TCB]`): Relocatable-object model (`ObjObject`, `ObjSection`,
//!    `ObjSymbol`, `ObjReloc`, `ExternDecl`, `Extraction`, `ObjModuleMeta`) and SHA-256.
//! 2. [`trusted_extractor`] (`[TCB]`): Pure ELF64 `.o` byte parser (`parse_object`, `parse_c_object`),
//!    symbol/extern collision checks, and pre-link `Obj.ExtractedObj` emission.
//! 3. [`untrusted_placed`] (`[OUTSIDE TCB]`): Layout-generic `PlacedLib` / `MultiPlacedLib` and
//!    placement witness emission.
//! 4. [`untrusted_legacy_linker`] (`[OUTSIDE TCB]`, deprecated): Legacy base-independent static
//!    linker producing `Arm64.Obj.LinkedImage` (`Arm64.Legacy`), gated behind `--legacy-linked-image`.
//! 5. [`untrusted_driver`] (`[OUTSIDE TCB]`): `translation.toml` / CLI config loader, `cargo rustc` /
//!    `zig cc` build orchestration, `.rlib` / `.a` archive unpacking, `root_section_closure`
//!    dead-section reachability selector, and the export pipeline + CLI dispatch
//!    ([`untrusted_driver::pipeline`]).
//! 6. [`untrusted_lemmas`] (`[OUTSIDE TCB]`): A64 instruction decoder, `<ObjName>Code.lean`,
//!    per-target fetch/decode lemmas, `*Index.json`, and `symexec` certificate/trace tooling.
//! 7. `test_infra` (`[TEST ONLY]`, `cfg(test)`): Differential tests against `ld.lld` and Lean.
//!
//! This crate root is module glue only: it declares the modules above and contains no logic, so
//! the `[TCB]` surface of the crate is strictly `trusted_common/` and `trusted_extractor/`
//! (`check-trust-guards` rule `tcb-rust-import` keeps those files free of references to
//! `untrusted_*`, `test_infra`, and non-TCB workspace crates).
//!
//! # When to Read This File
//! - Only to find which module owns a piece of the pipeline; each module has its own header.
//!   CLI dispatch and `--check` diffing live in [`untrusted_driver::pipeline`].

#[cfg(test)]
mod test_infra;
pub mod trusted_common;
pub mod trusted_extractor;
pub mod untrusted_driver;
pub mod untrusted_legacy_linker;
pub mod untrusted_lemmas;
pub mod untrusted_placed;

#[cfg(test)]
mod tests;
