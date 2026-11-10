// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for `proc-snapshot` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` CLI entry point dispatching into `[CASE-STUDIES TCB]` snapshot
//!   modules (`elf`, `rsp`, `snapshot`). The only runner is qemu-aarch64 user mode via its gdbstub.
//! - **Purpose:** Subcommand `snapshot`: run an AArch64 ELF under qemu-user and write
//!   `entry.snapshot.{json,bin}` and `<stop>.snapshot.{json,bin}` (see [`snapshot`]).
//!   Subcommand `dump-state`: format an `entry.snapshot.{json,bin}` into human-readable hex text
//!   (see [`untrusted_dump`]).
//!
//! # Key Types & Functions
//! - [`Cli`], [`Cmd`]: `clap` parser and dispatch.
//!
//! # When to Read This File
//! - Read this file to see CLI flags and subcommand dispatch.

mod elf;
mod rsp;
mod snapshot;
#[cfg(test)]
mod tests;
mod untrusted_dump;

use clap::{Parser, Subcommand};

#[derive(Parser, Debug)]
#[command(
    name = "proc-snapshot",
    about = "Dump AArch64 process snapshots under qemu-aarch64 user mode",
    after_help = "Example:\n  proc-snapshot snapshot --elf prog --qemu \"$(scripts/fetch-qemu-aarch64)\" --out-dir out"
)]
pub struct Cli {
    #[command(subcommand)]
    pub cmd: Cmd,
}

#[derive(Subcommand, Debug)]
pub enum Cmd {
    /// Snapshot an ELF at exec entry and at a stop symbol (default `main`).
    Snapshot(snapshot::SnapshotArgs),
    /// Format an `entry.snapshot.json` into human-readable hex load-state text.
    DumpState(untrusted_dump::DumpStateArgs),
    /// Overwrite bytes at a virtual address in `entry.snapshot.bin` (for negative testing).
    Poke(untrusted_dump::PokeArgs),
}

fn main() -> anyhow::Result<()> {
    match Cli::parse().cmd {
        Cmd::Snapshot(a) => snapshot::run(a),
        Cmd::DumpState(a) => untrusted_dump::run(a),
        Cmd::Poke(a) => untrusted_dump::run_poke(a),
    }
}
