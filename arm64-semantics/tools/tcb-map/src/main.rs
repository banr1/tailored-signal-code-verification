// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for `tcb-map` (`[AUDIT/LINTER]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[AUDIT/LINTER]` (enforces TCB boundaries and repository trust categories;
//!   not part of the TCB itself).
//! - **Modes:**
//!   - `--tree`: print the repository trust classification tree (`[tcb]`, `[case-studies-tcb]`,
//!     `[proof]`, `[testing]`, `[infra]`, `[doc]`) and per-category code-size totals. Works on an
//!     unbuilt checkout without `Generated/*Obj.lean`.
//!   - `--tree-json` (or `--json`): emit the repository trust hierarchy as pretty-printed JSON.
//!   - `--check-imports`: check only Lean module/package import layering (`check_imports`) and
//!     trusted Rust crate/module self-containment (`tcb_rust_import`).
//!   - `--check` (default when no other mode flag is given): run `--check-imports` +
//!     `unclassified-path` + core role-purity / soundness checks.

use anyhow::Result;
use clap::Parser;
use std::path::PathBuf;
use std::process::ExitCode;
use tcb_map::Workspace;
use tcb_map::discovery::default_repo_root;
use tcb_map::tree::{self, TreeReport};

#[derive(Parser)]
#[command(
    name = "tcb-map",
    about = "Repository trust classification (--tree / --tree-json), import-DAG checker (--check-imports), and core soundness guard (--check)"
)]
struct Cli {
    /// Repository root (defaults to the repo containing this binary).
    #[arg(long)]
    root: Option<PathBuf>,

    /// Print the repository directory hierarchy with `[tcb]`, `[case-studies-tcb]`, `[proof]`,
    /// `[testing]`, `[infra]`, `[doc]`, and `[mixed: ...]` badges and per-category code-size totals.
    #[arg(long)]
    tree: bool,

    /// Emit the repository trust hierarchy as pretty-printed JSON (`fx`-friendly:
    /// `tcb-map --tree-json | fx`).
    #[arg(long = "tree-json", visible_alias = "json")]
    tree_json: bool,

    /// Check only Lean module/package import layering and trusted Rust crate/module imports.
    #[arg(long = "check-imports")]
    check_imports: bool,

    /// Run full `tcb-map` checks (`--check-imports` + `unclassified-path` + core role-purity and
    /// soundness checks). This is the default when neither `--tree`, `--tree-json`, nor
    /// `--check-imports` is passed.
    #[arg(long)]
    check: bool,

    /// Exclude case-study files and modules (`VerifiedLibraries/`, `CaseStudies/`,
    /// `third_party/`, `tools/proc-snapshot/`) from the tree report and checks.
    #[arg(long = "no-case-studies")]
    no_case_studies: bool,

    /// Print the engine (`Arm64`) modules and line counts in the trusted `Spec`/`Theorems`
    /// closure of each `WHOLE_PROCESS_PACKAGES` case study, `FormalRfcs`, and of their union.
    #[arg(long = "whole-process-closure")]
    whole_process_closure: bool,
}

fn main() -> Result<ExitCode> {
    let cli = Cli::parse();
    let root = cli.root.unwrap_or_else(default_repo_root);
    let in_github_actions = std::env::var_os("GITHUB_ACTIONS").is_some();

    // `--tree` and `--tree-json` classify paths and count lines directly from the file tree so
    // they succeed in unbuilt checkouts without `Generated/*Obj.lean` symbol tables on disk,
    // while still failing closed on any `unclassified-path` violation.
    if (cli.tree || cli.tree_json) && !cli.check && !cli.check_imports {
        let report = TreeReport::build_filtered(&root, cli.no_case_studies)?;
        if !report.violations.is_empty() {
            for v in &report.violations {
                let message = format!("[{}]: {}", v.rule, v.text);
                if in_github_actions {
                    println!("::error file={},line={}::{}", v.path, v.line, message);
                }
                eprintln!("{}:{}: {}", v.path, v.line, message);
            }
            eprintln!(
                "\nTrust guard FAILED: {} violation(s) in repository trust tree.",
                report.violations.len(),
            );
            return Ok(ExitCode::FAILURE);
        }
        if cli.tree_json {
            println!("{}", report.to_json_pretty());
        } else {
            print!("{}", report.render());
        }
        return Ok(ExitCode::SUCCESS);
    }

    let ws = Workspace::load_filtered(&root, cli.no_case_studies)?;

    if cli.whole_process_closure {
        let mut union = std::collections::BTreeSet::new();
        for &pkg in tcb_map::policy::WHOLE_PROCESS_PACKAGES {
            let closure = ws.whole_process_trusted_closure(pkg);
            let (n, lines) = ws.engine_closure_lines(closure.keys());
            println!("CaseStudies/{pkg}: {n} engine modules, {lines} lines");
            union.extend(closure.into_keys());
        }
        let rfc_closure = ws.formal_rfcs_trusted_closure();
        let (n, lines) = ws.engine_closure_lines(rfc_closure.keys());
        println!("FormalRfcs: {n} engine modules, {lines} lines");
        union.extend(rfc_closure.into_keys());
        let (n, lines) = ws.engine_closure_lines(union.iter());
        println!("union: {n} engine modules, {lines} lines");
        for name in union.iter().filter(|n| n.starts_with("Arm64")) {
            println!("  {name}");
        }
        return Ok(ExitCode::SUCCESS);
    }

    if cli.check_imports && !cli.check {
        let violations = ws.check_imports_all();
        let report = ws.format_violations(&violations, None, in_github_actions);
        print!("{}", report.stdout);
        eprint!("{}", report.stderr);
        return Ok(if report.ok {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        });
    }

    if cli.tree_json {
        let report = ws.trust_tree()?;
        if !report.violations.is_empty() {
            for v in &report.violations {
                let message = format!("[{}]: {}", v.rule, v.text);
                if in_github_actions {
                    println!("::error file={},line={}::{}", v.path, v.line, message);
                }
                eprintln!("{}:{}: {}", v.path, v.line, message);
            }
            return Ok(ExitCode::FAILURE);
        }
        println!("{}", report.to_json_pretty());
        return Ok(ExitCode::SUCCESS);
    }

    let report = ws.format_report(cli.tree, in_github_actions, true)?;
    print!("{}", report.stdout);
    eprint!("{}", report.stderr);
    if !report.ok {
        let _ = tree::RULE;
        return Ok(ExitCode::FAILURE);
    }
    Ok(ExitCode::SUCCESS)
}
