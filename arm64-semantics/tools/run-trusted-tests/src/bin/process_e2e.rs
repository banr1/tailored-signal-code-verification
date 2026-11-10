// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for building static AArch64 Rust guest ELFs, running QEMU `-strace`
//! differential vector regeneration/drift checks, and emitting summary reports (`[TEST ONLY]`).

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use run_trusted_tests::process_e2e::{
    ProcessE2ESuite, build_or_check_elfs, regen_or_check_vectors, render_markdown_report,
    vectors_path,
};

#[derive(Parser, Debug)]
#[command(
    name = "process_e2e",
    about = "Build static AArch64 Rust process e2e binaries, run QEMU -strace vectors, and check drift",
    after_help = "Examples:\n  process_e2e build --check\n  process_e2e regen --check\n  process_e2e report --out /tmp/process-e2e-report.md"
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
    /// Reproducibly compile all 26 static `ET_EXEC` Rust binaries (or check zero byte drift).
    Build {
        /// Verify that fresh builds match committed `bin/*.elf` byte-for-byte without writing.
        #[arg(long)]
        check: bool,
    },
    /// Execute all cases under `qemu-aarch64 -strace` and write/check `expected_vectors.json`.
    Regen {
        /// Verify that live QEMU outputs and `-strace` censuses match `expected_vectors.json`.
        #[arg(long)]
        check: bool,
    },
    /// Render Markdown summary report from `expected_vectors.json`.
    Report {
        /// Write report to `<OUT>` instead of `stdout`.
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Build ELFs, regenerate QEMU vectors, and optionally write Markdown report.
    All {
        /// Check both ELF reproducibility and QEMU vector equality without modifying files.
        #[arg(long)]
        check: bool,
        /// Optional path to write Markdown report.
        #[arg(long)]
        report_out: Option<PathBuf>,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let root = cli
        .root
        .unwrap_or_else(run_trusted_tests::default_repo_root)
        .canonicalize()
        .context("failed to canonicalize repository root")?;

    match cli.cmd {
        SubCmd::Build { check } => {
            let (rustc_ver, infos) = build_or_check_elfs(&root, check)?;
            println!(
                "[process-e2e] {}: {} static AArch64 ET_EXEC binaries verified ({})",
                if check {
                    "ELF drift check PASSED"
                } else {
                    "Built ELFs"
                },
                infos.len(),
                rustc_ver
            );
            for info in &infos {
                println!(
                    "  {:22} {:7} B  entry=0x{:08x}  sha256={}",
                    info.spec.name,
                    info.size_bytes,
                    info.entry_va,
                    &info.sha256[..16]
                );
            }
        }
        SubCmd::Regen { check } => {
            let suite = regen_or_check_vectors(&root, None, None, check)?;
            println!(
                "[process-e2e] {}: {} programs, {} cases ({})",
                if check {
                    "QEMU vector & strace drift check PASSED"
                } else {
                    "Regenerated expected_vectors.json"
                },
                suite.programs.len(),
                suite.cases.len(),
                suite.qemu_version
            );
        }
        SubCmd::Report { out } => {
            let vpath = vectors_path(&root);
            let raw = fs::read_to_string(&vpath)
                .with_context(|| format!("failed to read {}", vpath.display()))?;
            let suite: ProcessE2ESuite = serde_json::from_str(&raw)?;
            let md = render_markdown_report(&suite);
            if let Some(p) = out {
                fs::write(&p, &md)?;
                println!("[process-e2e] Wrote report to {}", p.display());
            } else {
                print!("{md}");
            }
        }
        SubCmd::All { check, report_out } => {
            let (rustc_ver, infos) = build_or_check_elfs(&root, check)?;
            let suite = regen_or_check_vectors(&root, Some(&rustc_ver), Some(infos), check)?;
            println!(
                "[process-e2e] {}: {} programs, {} cases ({}; {})",
                if check { "Full check PASSED" } else { "All generated" },
                suite.programs.len(),
                suite.cases.len(),
                rustc_ver,
                suite.qemu_version
            );
            if let Some(p) = report_out {
                let md = render_markdown_report(&suite);
                fs::write(&p, &md)?;
                println!("[process-e2e] Wrote report to {}", p.display());
            }
        }
    }
    Ok(())
}
