// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for generating or drift-checking static (`svc #0`) and dynamic
//! (`qemu-aarch64 -strace`) Linux AArch64 syscall inventories (`[TEST ONLY]`).

use std::path::PathBuf;

use anyhow::Result;
use clap::{Args, Parser, Subcommand};
use run_trusted_tests::std_syscall_inventory::{
    check_inventory_outputs, generate_inventory_from_manifest, write_inventory_outputs,
};

#[derive(Parser, Debug)]
#[command(
    name = "std-syscall-inventory",
    about = "Generate or check static (svc #0) and dynamic (qemu-aarch64 -strace) AArch64 syscall inventories",
    after_help = "Examples:\n  std_syscall_inventory generate --manifest inventory_config.json --json-out inventory.json --md-out inventory.md\n  std_syscall_inventory check --manifest inventory_config.json --json-out inventory.json --md-out inventory.md"
)]
struct Cli {
    /// Repository root directory (defaults to auto-detected workspace root).
    #[arg(long, global = true)]
    root: Option<PathBuf>,

    #[command(subcommand)]
    cmd: ModeCmd,
}

#[derive(Args, Debug, Clone)]
struct InventoryIoArgs {
    /// Declarative JSON manifest listing ELF binaries and QEMU `-strace` scenarios.
    #[arg(long)]
    manifest: PathBuf,

    /// Path to write (in `generate`) or check (in `check`) the deterministic JSON inventory.
    #[arg(long)]
    json_out: PathBuf,

    /// Path to write (in `generate`) or check (in `check`) the deterministic Markdown report.
    #[arg(long)]
    md_out: PathBuf,

    /// Optional explicit path to a `qemu-aarch64` user-mode binary.
    #[arg(long)]
    qemu: Option<PathBuf>,
}

#[derive(Subcommand, Debug)]
enum ModeCmd {
    /// Run static ELF `svc #0` scans + dynamic QEMU `-strace` scenarios and write JSON + Markdown.
    Generate(InventoryIoArgs),
    /// Run static + dynamic inventory in memory and verify zero drift against checked-in outputs.
    Check(InventoryIoArgs),
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let repo_root = cli
        .root
        .unwrap_or_else(run_trusted_tests::default_repo_root);

    match cli.cmd {
        ModeCmd::Generate(args) => {
            let report = generate_inventory_from_manifest(
                &repo_root,
                &args.manifest,
                args.qemu.as_deref(),
            )?;
            write_inventory_outputs(&report, &args.json_out, Some(&args.md_out))?;
            println!(
                "[std-syscall-inventory] Generated inventory ({} binaries, {} scenarios, {} classified syscalls) -> {}, {}",
                report.binaries.len(),
                report.scenarios.len(),
                report.classification_summary.len(),
                args.json_out.display(),
                args.md_out.display(),
            );
        }
        ModeCmd::Check(args) => {
            let report = generate_inventory_from_manifest(
                &repo_root,
                &args.manifest,
                args.qemu.as_deref(),
            )?;
            check_inventory_outputs(&report, &args.json_out, Some(&args.md_out))?;
            println!(
                "[std-syscall-inventory] Drift & fail-closed audit check PASSED ({} binaries, {} scenarios, {} classified syscalls)",
                report.binaries.len(),
                report.scenarios.len(),
                report.classification_summary.len(),
            );
        }
    }
    Ok(())
}
