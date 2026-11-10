// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for building the static AArch64 ELF loader corpus, capturing `qemu-aarch64`
//! entry snapshots, and running the Lean `ElfImage.loadState` differential harness (`[TEST ONLY]`).

use std::path::PathBuf;

use anyhow::Result;
use clap::{Parser, Subcommand};
use run_trusted_tests::elf_loader_diff::{
    build_or_check_corpus, regen_or_check_snapshots, run_live_diff_suite, verify_corpus,
};

#[derive(Parser, Debug)]
#[command(
    name = "elf_loader_diff",
    about = "Build static AArch64 ELF corpus, capture qemu-aarch64 entry snapshots, and diff against Lean ElfImage.loadState",
    after_help = "Examples:\n  elf_loader_diff build [--check]\n  elf_loader_diff regen [--check]\n  elf_loader_diff run"
)]
struct Cli {
    /// Repository root directory (defaults to auto-detected workspace root).
    #[arg(long)]
    root: Option<PathBuf>,

    #[command(subcommand)]
    cmd: SubCmd,
}

#[derive(Subcommand, Debug)]
enum SubCmd {
    /// Compile all committed small static AArch64 ELF fixtures in `Arm64/Testing/ElfLoaderDiff/bin/`
    /// (`--check`: rebuild into a temporary directory and require byte-identical output).
    Build {
        #[arg(long)]
        check: bool,
    },
    /// Capture `qemu-aarch64` entry snapshots for the committed corpus and write/check
    /// `Arm64/Testing/ElfLoaderDiff/expected_snapshots.json`.
    Regen {
        #[arg(long)]
        check: bool,
    },
    /// Build the full live multi-compiler corpus (Asm, C zig/musl -O0/-O2, optional gcc/glibc,
    /// Rust no_std + std with TLS & 64 KiB .bss, Go arm64, unusual layouts, and rejected
    /// PIE/dynamic/invalid ELFs), capture `qemu-aarch64` entry snapshots, and run the Lean
    /// `elf_eval --loader-diff` comparison harness.
    Run,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let repo_root = match cli.root {
        Some(r) => r,
        None => run_trusted_tests::default_repo_root(),
    };
    match cli.cmd {
        SubCmd::Build { check: true } => verify_corpus(&repo_root),
        SubCmd::Build { check: false } => build_or_check_corpus(&repo_root, false),
        SubCmd::Regen { check } => regen_or_check_snapshots(&repo_root, check),
        SubCmd::Run => run_live_diff_suite(&repo_root),
    }
}
