// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Static (`svc #0` + `x8` constant/wrapper dataflow) and dynamic (`qemu-aarch64 -strace`)
//! Linux AArch64 syscall inventory generator and drift/audit checker (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted host audit infrastructure under
//!   `tools/run-trusted-tests`).
//! - **Purpose:** Given a declarative JSON manifest of static AArch64 ELF executables and dynamic
//!   execution scenarios, statically decode every `svc #0` instruction across `.text` / executable
//!   sections, run every scenario under `qemu-aarch64 -strace` inside an isolated working
//!   directory, enforce the three-way [`classify::SyscallClass`] fail-closed audit, and write or
//!   verify host-independent JSON and Markdown inventory artifacts.
//!
//! # Submodules
//! - [`classify`]: `Modeled` / `NeedsModel` / `ProvablyUnreachable` table and fail-closed checks.
//! - [`static_scan`]: ELF64 `.symtab` + intra-procedural CFG `x8` / `arg0` `svc #0` decoder.
//! - [`strace`]: Isolated `qemu-aarch64` runner and strict `-strace` log parser.

pub mod classify;
pub mod static_scan;
pub mod strace;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, anyhow, bail};
use serde::{Deserialize, Serialize};

use crate::process_e2e::qemu::resolve_qemu_aarch64_with_override;

use self::classify::{
    SyscallClass, audit_dynamic_syscall, audit_static_syscall, classify_syscall,
};
use self::static_scan::{StaticBinaryScan, StaticX8Value, scan_elf_bytes};
use self::strace::{
    DataKind, DynamicScenarioRun, ScenarioRunParams, SetupFileSpec, SyscallRun,
    normalize_closed_fds, run_scenario_in_qemu,
};

fn default_schema_version() -> u32 {
    1
}

/// Declarative input manifest (`--manifest <PATH>`) specifying binaries and QEMU scenarios.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InventoryManifest {
    #[serde(default = "default_schema_version")]
    pub schema_version: u32,
    pub binaries: Vec<BinarySpec>,
    #[serde(default)]
    pub scenarios: Vec<ScenarioSpec>,
}

/// Single static AArch64 ELF binary entry in [`InventoryManifest`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySpec {
    pub id: String,
    /// Path to the ELF binary (resolved relative to the directory containing `--manifest` if relative).
    pub elf: String,
    #[serde(default)]
    pub description: String,
}

/// Single dynamic `qemu-aarch64 -strace` execution scenario in [`InventoryManifest`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScenarioSpec {
    pub id: String,
    pub bin_id: String,
    #[serde(default)]
    pub description: String,
    /// Optional explicit `argv[0]` passed to `qemu-aarch64 -0`; defaults to `bin_id`.
    #[serde(default)]
    pub argv0: Option<String>,
    /// Command-line arguments `argv[1..]` passed after the binary path.
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default)]
    pub envp: Vec<String>,
    #[serde(default)]
    pub stdin_kind: DataKind,
    #[serde(default)]
    pub setup_files: Vec<SetupFileSpec>,
    /// Subset of standard file descriptors `[0, 1, 2]` closed prior to guest startup.
    #[serde(default)]
    pub closed_fds: Vec<i32>,
    #[serde(default)]
    pub expect_exit: i32,
    /// Syscall numbers (`__NR_*`) asserted to appear dynamically in this scenario's trace.
    #[serde(default)]
    pub require_dynamic_syscalls: Vec<u64>,
    /// Optional per-scenario allowlist of `provably_unreachable` syscalls permitted only when a
    /// host-environment probe deliberately violates standard-descriptor preconditions.
    #[serde(default)]
    pub allow_unreachable_syscalls: Vec<u64>,
}

/// Deterministic top-level JSON inventory written to `--json-out` and checked by `check`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InventoryReport {
    pub schema_version: u32,
    pub binaries: Vec<BinaryInventory>,
    pub scenarios: Vec<ScenarioInventory>,
    pub classification_summary: Vec<AggregatedSyscallEntry>,
}

/// Per-ELF static `svc #0` inventory serialized into [`InventoryReport`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryInventory {
    pub id: String,
    pub elf: String,
    pub description: String,
    pub size_bytes: u64,
    pub sha256: String,
    pub entry_va: String,
    pub total_svc_sites: usize,
    pub resolved_direct_sites: usize,
    pub indirect_wrapper_sites: usize,
    pub dynamic_unknown_sites: usize,
    pub distinct_syscalls: Vec<StaticSyscallEntry>,
    pub svc_sites: Vec<SerializedSvcSite>,
}

/// Deduplicated static syscall summary within a single ELF binary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StaticSyscallEntry {
    pub nr: u64,
    pub name: String,
    pub class: SyscallClass,
    pub direct_sites: usize,
    pub indirect_wrapper_sites: usize,
    pub functions: Vec<String>,
}

/// Individual static `svc #0` instruction site serialized into [`BinaryInventory`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializedSvcSite {
    pub pc: String,
    pub function: String,
    pub offset_in_fn: String,
    pub resolution: SerializedX8Resolution,
}

/// Serialized `x8` resolution for a static `svc #0` site.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SerializedX8Resolution {
    Resolved {
        nr: u64,
        name: String,
        class: SyscallClass,
    },
    IndirectArg0 {
        caller_syscalls: Vec<ClassifiedSyscallRef>,
        unresolved_callers: usize,
    },
    DynamicUnknown,
}

/// Compact `(nr, name, class)` reference inside indirect wrapper call summaries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassifiedSyscallRef {
    pub nr: u64,
    pub name: String,
    pub class: SyscallClass,
}

/// Host-independent dynamic scenario execution record serialized into [`InventoryReport`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScenarioInventory {
    pub id: String,
    pub bin_id: String,
    pub description: String,
    pub args: Vec<String>,
    pub closed_fds: Vec<i32>,
    pub expect_exit: i32,
    pub exit_code: i32,
    pub require_dynamic_syscalls: Vec<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allow_unreachable_syscalls: Vec<u64>,
    pub total_syscall_invocations: usize,
    pub distinct_syscalls: Vec<DynamicSyscallEntry>,
    pub ordered_runs: Vec<SyscallRun>,
}

/// Per-syscall call count and classification within one dynamic scenario.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DynamicSyscallEntry {
    pub nr: u64,
    pub name: String,
    pub class: SyscallClass,
    pub calls: usize,
}

/// Cross-binary and cross-scenario summary row for a single classified syscall.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AggregatedSyscallEntry {
    pub nr: u64,
    pub name: String,
    pub class: SyscallClass,
    pub static_binaries: Vec<String>,
    pub dynamic_scenarios: Vec<String>,
    pub total_dynamic_calls: usize,
    pub rationale: String,
}

/// Build a [`BinaryInventory`] from a [`StaticBinaryScan`], enforcing static fail-closed classification.
pub fn build_binary_inventory(spec: &BinarySpec, scan: &StaticBinaryScan) -> Result<BinaryInventory> {
    let mut resolved_direct_sites = 0usize;
    let mut indirect_wrapper_sites = 0usize;
    let mut dynamic_unknown_sites = 0usize;

    // `nr` -> `(direct_count, indirect_wrapper_count, functions)`
    let mut per_nr: BTreeMap<u64, (usize, usize, BTreeSet<String>)> = BTreeMap::new();
    let mut svc_sites = Vec::with_capacity(scan.sites.len());

    for site in &scan.sites {
        let resolution = match &site.x8 {
            StaticX8Value::Resolved(nr) => {
                resolved_direct_sites += 1;
                let info = audit_static_syscall(&spec.id, *nr)?;
                let entry = per_nr.entry(*nr).or_insert_with(|| (0, 0, BTreeSet::new()));
                entry.0 += 1;
                entry.2.insert(site.function.clone());
                SerializedX8Resolution::Resolved {
                    nr: *nr,
                    name: info.name.to_owned(),
                    class: info.class,
                }
            }
            StaticX8Value::IndirectArg0 {
                caller_nrs,
                unresolved_callers,
            } => {
                indirect_wrapper_sites += 1;
                let mut refs = Vec::with_capacity(caller_nrs.len());
                for &nr in caller_nrs {
                    let info = audit_static_syscall(&spec.id, nr)?;
                    let entry = per_nr.entry(nr).or_insert_with(|| (0, 0, BTreeSet::new()));
                    entry.1 += 1;
                    entry.2.insert(format!("{} (via arg0)", site.function));
                    refs.push(ClassifiedSyscallRef {
                        nr,
                        name: info.name.to_owned(),
                        class: info.class,
                    });
                }
                SerializedX8Resolution::IndirectArg0 {
                    caller_syscalls: refs,
                    unresolved_callers: *unresolved_callers,
                }
            }
            StaticX8Value::DynamicUnknown => {
                dynamic_unknown_sites += 1;
                SerializedX8Resolution::DynamicUnknown
            }
        };

        svc_sites.push(SerializedSvcSite {
            pc: format!("0x{:08x}", site.pc),
            function: site.function.clone(),
            offset_in_fn: format!("0x{:x}", site.offset_in_fn),
            resolution,
        });
    }

    let mut distinct_syscalls = Vec::with_capacity(per_nr.len());
    for (nr, (direct_sites, indirect_sites, functions)) in per_nr {
        let info = audit_static_syscall(&spec.id, nr)?;
        distinct_syscalls.push(StaticSyscallEntry {
            nr,
            name: info.name.to_owned(),
            class: info.class,
            direct_sites,
            indirect_wrapper_sites: indirect_sites,
            functions: functions.into_iter().collect(),
        });
    }

    Ok(BinaryInventory {
        id: spec.id.clone(),
        elf: spec.elf.clone(),
        description: spec.description.clone(),
        size_bytes: scan.size_bytes,
        sha256: scan.sha256.clone(),
        entry_va: format!("0x{:08x}", scan.entry_va),
        total_svc_sites: scan.sites.len(),
        resolved_direct_sites,
        indirect_wrapper_sites,
        dynamic_unknown_sites,
        distinct_syscalls,
        svc_sites,
    })
}

/// Build a [`ScenarioInventory`] from a [`DynamicScenarioRun`], enforcing dynamic fail-closed rules.
pub fn build_scenario_inventory(
    spec: &ScenarioSpec,
    run: DynamicScenarioRun,
) -> Result<ScenarioInventory> {
    let closed_fds = normalize_closed_fds(&spec.closed_fds)?;
    let mut distinct_syscalls = Vec::with_capacity(run.parsed.distinct_counts.len());

    for &(nr, _, calls) in &run.parsed.distinct_counts {
        let info = audit_dynamic_syscall(
            &spec.id,
            &spec.bin_id,
            nr,
            &spec.allow_unreachable_syscalls,
        )?;
        distinct_syscalls.push(DynamicSyscallEntry {
            nr,
            name: info.name.to_owned(),
            class: info.class,
            calls,
        });
    }

    let mut req_sorted = spec.require_dynamic_syscalls.clone();
    req_sorted.sort_unstable();
    req_sorted.dedup();

    let mut allow_sorted = spec.allow_unreachable_syscalls.clone();
    allow_sorted.sort_unstable();
    allow_sorted.dedup();

    Ok(ScenarioInventory {
        id: spec.id.clone(),
        bin_id: spec.bin_id.clone(),
        description: spec.description.clone(),
        args: spec.args.clone(),
        closed_fds,
        expect_exit: spec.expect_exit,
        exit_code: run.exit_code,
        require_dynamic_syscalls: req_sorted,
        allow_unreachable_syscalls: allow_sorted,
        total_syscall_invocations: run.parsed.total_calls,
        distinct_syscalls,
        ordered_runs: run.parsed.ordered_runs,
    })
}

/// Aggregate static and dynamic inventories into a unified sorted classification summary.
pub fn build_classification_summary(
    binaries: &[BinaryInventory],
    scenarios: &[ScenarioInventory],
) -> Result<Vec<AggregatedSyscallEntry>> {
    let mut all_nrs: BTreeSet<u64> = BTreeSet::new();
    for b in binaries {
        for s in &b.distinct_syscalls {
            all_nrs.insert(s.nr);
        }
    }
    for sc in scenarios {
        for s in &sc.distinct_syscalls {
            all_nrs.insert(s.nr);
        }
    }

    let mut out = Vec::with_capacity(all_nrs.len());
    for nr in all_nrs {
        let info = classify_syscall(nr)
            .ok_or_else(|| anyhow!("internal error: unclassified syscall {nr} in summary"))?;
        let static_binaries: Vec<String> = binaries
            .iter()
            .filter(|b| b.distinct_syscalls.iter().any(|s| s.nr == nr))
            .map(|b| b.id.clone())
            .collect();
        let mut dynamic_scenarios = Vec::new();
        let mut total_dynamic_calls = 0usize;
        for sc in scenarios {
            if let Some(entry) = sc.distinct_syscalls.iter().find(|s| s.nr == nr) {
                dynamic_scenarios.push(sc.id.clone());
                total_dynamic_calls += entry.calls;
            }
        }
        out.push(AggregatedSyscallEntry {
            nr,
            name: info.name.to_owned(),
            class: info.class,
            static_binaries,
            dynamic_scenarios,
            total_dynamic_calls,
            rationale: info.rationale.to_owned(),
        });
    }
    Ok(out)
}

fn validate_manifest(manifest: &InventoryManifest) -> Result<()> {
    if manifest.binaries.is_empty() {
        bail!("inventory manifest must declare at least one binary");
    }
    let mut seen_bins = BTreeSet::new();
    for b in &manifest.binaries {
        if b.id.trim().is_empty() {
            bail!("binary `id` must not be empty");
        }
        if !seen_bins.insert(b.id.as_str()) {
            bail!("duplicate binary id `{}` in manifest", b.id);
        }
    }
    let mut seen_scenarios = BTreeSet::new();
    for sc in &manifest.scenarios {
        if sc.id.trim().is_empty() {
            bail!("scenario `id` must not be empty");
        }
        if !seen_scenarios.insert(sc.id.as_str()) {
            bail!("duplicate scenario id `{}` in manifest", sc.id);
        }
        if !seen_bins.contains(sc.bin_id.as_str()) {
            bail!(
                "scenario `{}` references unknown bin_id `{}`",
                sc.id,
                sc.bin_id
            );
        }
    }
    Ok(())
}

fn resolve_elf_path(manifest_dir: &Path, elf_field: &str) -> Result<PathBuf> {
    let p = Path::new(elf_field);
    let joined = if p.is_absolute() {
        p.to_path_buf()
    } else {
        manifest_dir.join(p)
    };
    if joined.is_absolute() {
        Ok(joined)
    } else {
        let cwd = std::env::current_dir().context("failed to read current working directory")?;
        Ok(cwd.join(joined))
    }
}

/// Execute static ELF scans and dynamic QEMU `-strace` scenarios from `manifest_path`.
pub fn generate_inventory_from_manifest(
    repo_root: &Path,
    manifest_path: &Path,
    explicit_qemu: Option<&Path>,
) -> Result<InventoryReport> {
    let raw_manifest = fs::read_to_string(manifest_path)
        .with_context(|| format!("failed to read manifest {}", manifest_path.display()))?;
    let manifest: InventoryManifest = serde_json::from_str(&raw_manifest)
        .with_context(|| format!("failed to parse JSON manifest {}", manifest_path.display()))?;
    validate_manifest(&manifest)?;

    let manifest_dir = manifest_path.parent().unwrap_or_else(|| Path::new("."));

    // 1. Static ELF scans
    let mut elf_abs_by_id: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut binaries = Vec::with_capacity(manifest.binaries.len());
    for bspec in &manifest.binaries {
        let elf_abs = resolve_elf_path(manifest_dir, &bspec.elf)?;
        let elf_bytes = fs::read(&elf_abs).with_context(|| {
            format!(
                "failed to read ELF binary `{}` at {}",
                bspec.id,
                elf_abs.display()
            )
        })?;
        let scan = scan_elf_bytes(&bspec.id, &elf_bytes)?;
        let bin_inv = build_binary_inventory(bspec, &scan)?;
        elf_abs_by_id.insert(bspec.id.clone(), elf_abs);
        binaries.push(bin_inv);
    }

    // 2. Dynamic QEMU `-strace` scenarios
    let mut scenarios = Vec::with_capacity(manifest.scenarios.len());
    if !manifest.scenarios.is_empty() {
        let (qemu_bin, _qemu_ver) = resolve_qemu_aarch64_with_override(repo_root, explicit_qemu)?;
        for sspec in &manifest.scenarios {
            let elf_abs = elf_abs_by_id
                .get(&sspec.bin_id)
                .ok_or_else(|| anyhow!("missing ELF path for `{}`", sspec.bin_id))?;
            let argv0 = sspec.argv0.as_deref().unwrap_or(&sspec.bin_id);
            let run = run_scenario_in_qemu(&ScenarioRunParams {
                scenario_id: &sspec.id,
                bin_id: &sspec.bin_id,
                qemu_bin: &qemu_bin,
                elf_abs_path: elf_abs,
                argv0,
                args: &sspec.args,
                envp: &sspec.envp,
                stdin_kind: &sspec.stdin_kind,
                setup_files: &sspec.setup_files,
                closed_fds: &sspec.closed_fds,
                expect_exit: sspec.expect_exit,
                require_dynamic_syscalls: &sspec.require_dynamic_syscalls,
            })?;
            scenarios.push(build_scenario_inventory(sspec, run)?);
        }
    }

    let classification_summary = build_classification_summary(&binaries, &scenarios)?;

    Ok(InventoryReport {
        schema_version: manifest.schema_version,
        binaries,
        scenarios,
        classification_summary,
    })
}

/// Render a deterministic, host-independent Markdown summary of `report`.
pub fn render_markdown_report(report: &InventoryReport) -> String {
    let total_static_sites: usize = report.binaries.iter().map(|b| b.total_svc_sites).sum();
    let n_modeled = report
        .classification_summary
        .iter()
        .filter(|e| e.class == SyscallClass::Modeled)
        .count();
    let n_needs_model = report
        .classification_summary
        .iter()
        .filter(|e| e.class == SyscallClass::NeedsModel)
        .count();
    let n_unreachable = report
        .classification_summary
        .iter()
        .filter(|e| e.class == SyscallClass::ProvablyUnreachable)
        .count();

    let mut out = String::new();
    let _ = writeln!(
        &mut out,
        "# Linux AArch64 Static & Dynamic Syscall Inventory\n"
    );
    let _ = writeln!(
        &mut out,
        "> **Note (`[OUTSIDE TCB]`):** This inventory and its `provably_unreachable` classifications are informational, argued rather than proven, and outside the TCB.\n"
    );
    let _ = writeln!(&mut out, "- **Inspected ELF Binaries:** {}", report.binaries.len());
    let _ = writeln!(
        &mut out,
        "- **Dynamic QEMU `-strace` Scenarios:** {}",
        report.scenarios.len()
    );
    let _ = writeln!(
        &mut out,
        "- **Total Static `svc #0` Sites:** {total_static_sites}"
    );
    let _ = writeln!(
        &mut out,
        "- **Classified Syscalls Observed:** **{}** (`modeled`: **{n_modeled}**, `needs_model`: **{n_needs_model}**, `provably_unreachable`: **{n_unreachable}**)\n",
        report.classification_summary.len()
    );

    let _ = writeln!(&mut out, "## 1. Static ELF `svc #0` Summary\n");
    let _ = writeln!(
        &mut out,
        "| Binary | ELF Path | Size (B) | SHA-256 (prefix) | Entry VA | `svc #0` Sites | Direct | Indirect (`arg0`) | Unknown | Distinct Syscalls |"
    );
    let _ = writeln!(
        &mut out,
        "|---|---|---:|---|---|---:|---:|---:|---:|---:|"
    );
    for b in &report.binaries {
        let sha_prefix = &b.sha256[..b.sha256.len().min(12)];
        let _ = writeln!(
            &mut out,
            "| `{}` | `{}` | {} | `{}` | `{}` | {} | {} | {} | {} | {} |",
            b.id,
            b.elf,
            b.size_bytes,
            sha_prefix,
            b.entry_va,
            b.total_svc_sites,
            b.resolved_direct_sites,
            b.indirect_wrapper_sites,
            b.dynamic_unknown_sites,
            b.distinct_syscalls.len()
        );
    }

    let _ = writeln!(&mut out, "\n## 2. Dynamic `qemu-aarch64 -strace` Scenarios\n");
    let _ = writeln!(
        &mut out,
        "| Scenario | Binary | Args | Closed FDs | Exit | Required Syscalls | Total Calls | Observed Syscalls |"
    );
    let _ = writeln!(&mut out, "|---|---|---|---|---:|---|---:|---|");
    for sc in &report.scenarios {
        let args_str = if sc.args.is_empty() {
            "—".to_owned()
        } else {
            format!("`{}`", sc.args.join(" "))
        };
        let closed_str = if sc.closed_fds.is_empty() {
            "—".to_owned()
        } else {
            format!(
                "`[{}]`",
                sc.closed_fds
                    .iter()
                    .map(i32::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let req_str = if sc.require_dynamic_syscalls.is_empty() {
            "—".to_owned()
        } else {
            sc.require_dynamic_syscalls
                .iter()
                .map(|nr| format!("`{nr}`"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let obs_str = sc
            .distinct_syscalls
            .iter()
            .map(|s| format!("`{}({})`×{}", s.name, s.nr, s.calls))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            &mut out,
            "| `{}` | `{}` | {} | {} | `{}` | {} | {} | {} |",
            sc.id,
            sc.bin_id,
            args_str,
            closed_str,
            sc.exit_code,
            req_str,
            sc.total_syscall_invocations,
            obs_str
        );
    }

    let _ = writeln!(
        &mut out,
        "\n## 3. Unified Syscall Classification & Audit Table\n"
    );
    let _ = writeln!(
        &mut out,
        "| NR | Syscall | Classification | Static Binaries | Dynamic Scenarios | Dynamic Calls | Rationale |"
    );
    let _ = writeln!(&mut out, "|---:|---|---|---|---|---:|---|");
    for row in &report.classification_summary {
        let static_str = if row.static_binaries.is_empty() {
            "—".to_owned()
        } else {
            row.static_binaries
                .iter()
                .map(|b| format!("`{b}`"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let dyn_str = if row.dynamic_scenarios.is_empty() {
            "—".to_owned()
        } else {
            row.dynamic_scenarios
                .iter()
                .map(|s| format!("`{s}`"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let _ = writeln!(
            &mut out,
            "| `{}` | `{}` | `{}` | {} | {} | {} | {} |",
            row.nr,
            row.name,
            row.class.as_str(),
            static_str,
            dyn_str,
            row.total_dynamic_calls,
            row.rationale
        );
    }

    let _ = writeln!(
        &mut out,
        "\n## 4. Per-Binary Static Syscall Attribution\n"
    );
    for b in &report.binaries {
        let _ = writeln!(&mut out, "### `{}` (`{}`)\n", b.id, b.elf);
        let _ = writeln!(
            &mut out,
            "| NR | Syscall | Class | Direct Sites | Indirect Wrapper Sites | Enclosing Symbols |"
        );
        let _ = writeln!(&mut out, "|---:|---|---|---:|---:|---|");
        for s in &b.distinct_syscalls {
            let fns = s
                .functions
                .iter()
                .map(|f| format!("`{f}`"))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                &mut out,
                "| `{}` | `{}` | `{}` | {} | {} | {} |",
                s.nr,
                s.name,
                s.class.as_str(),
                s.direct_sites,
                s.indirect_wrapper_sites,
                fns
            );
        }
        let _ = writeln!(&mut out);
    }

    out
}

/// Serialize `report` to canonical JSON (`serde_json` pretty format + trailing newline).
pub fn serialize_inventory_json(report: &InventoryReport) -> Result<String> {
    let mut s = serde_json::to_string_pretty(report)?;
    s.push('\n');
    Ok(s)
}

/// Write canonical JSON and optional Markdown inventory artifacts to disk.
pub fn write_inventory_outputs(
    report: &InventoryReport,
    json_out: &Path,
    md_out: Option<&Path>,
) -> Result<()> {
    let json_text = serialize_inventory_json(report)?;
    if let Some(parent) = json_out.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)?;
    }
    fs::write(json_out, json_text)
        .with_context(|| format!("failed to write {}", json_out.display()))?;

    if let Some(md_path) = md_out {
        let md_text = render_markdown_report(report);
        if let Some(parent) = md_path.parent()
            && !parent.as_os_str().is_empty()
        {
            fs::create_dir_all(parent)?;
        }
        fs::write(md_path, md_text)
            .with_context(|| format!("failed to write {}", md_path.display()))?;
    }
    Ok(())
}

fn first_diff_line(expected: &str, actual: &str) -> String {
    let mut exp_lines = expected.lines();
    let mut act_lines = actual.lines();
    let mut line_no = 1usize;
    loop {
        match (exp_lines.next(), act_lines.next()) {
            (None, None) => return "trailing newline mismatch".to_owned(),
            (Some(e), Some(a)) if e == a => line_no += 1,
            (e, a) => {
                return format!(
                    "first difference at line {line_no}:\n  checked-in: {:?}\n  fresh:      {:?}",
                    e.unwrap_or("<EOF>"),
                    a.unwrap_or("<EOF>")
                );
            }
        }
    }
}

/// Verify that fresh `report` matches checked-in `json_out` (and `md_out` when provided) byte-for-byte.
pub fn check_inventory_outputs(
    report: &InventoryReport,
    json_out: &Path,
    md_out: Option<&Path>,
) -> Result<()> {
    let fresh_json = serialize_inventory_json(report)?;
    let disk_json = fs::read_to_string(json_out)
        .with_context(|| format!("failed to read checked-in JSON {}", json_out.display()))?;
    if disk_json != fresh_json {
        bail!(
            "syscall inventory JSON drift in {} ({})",
            json_out.display(),
            first_diff_line(&disk_json, &fresh_json)
        );
    }

    if let Some(md_path) = md_out {
        let fresh_md = render_markdown_report(report);
        let disk_md = fs::read_to_string(md_path).with_context(|| {
            format!(
                "failed to read checked-in Markdown {}",
                md_path.display()
            )
        })?;
        if disk_md != fresh_md {
            bail!(
                "syscall inventory Markdown drift in {} ({})",
                md_path.display(),
                first_diff_line(&disk_md, &fresh_md)
            );
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::std_syscall_inventory::static_scan::StaticSvcSite;
    use crate::std_syscall_inventory::strace::parse_qemu_strace_strict;

    #[test]
    fn build_scenario_inventory_fails_closed_on_provably_unreachable_syscall() {
        let trace_with_futex = "\
771 set_tid_address(0x230000) = 771
771 futex(0x230100,129,1,NULL,NULL,0) = 0
771 exit_group(0)
";
        let parsed = parse_qemu_strace_strict(trace_with_futex).unwrap();
        let spec = ScenarioSpec {
            id: "alpha_default".into(),
            bin_id: "alpha".into(),
            description: String::new(),
            argv0: None,
            args: Vec::new(),
            envp: Vec::new(),
            stdin_kind: DataKind::Empty,
            setup_files: Vec::new(),
            closed_fds: Vec::new(),
            expect_exit: 0,
            require_dynamic_syscalls: Vec::new(),
            allow_unreachable_syscalls: Vec::new(),
        };
        let err = build_scenario_inventory(
            &spec,
            DynamicScenarioRun {
                exit_code: 0,
                parsed,
            },
        )
        .unwrap_err();
        assert!(err.to_string().contains("provably_unreachable"));
        assert!(err.to_string().contains("futex"));
    }

    #[test]
    fn build_binary_inventory_fails_closed_on_unclassified_static_syscall() {
        let spec = BinarySpec {
            id: "widget".into(),
            elf: "bin/widget".into(),
            description: "Synthetic fixture".into(),
        };
        let scan = StaticBinaryScan {
            size_bytes: 4096,
            sha256: "00".repeat(32),
            entry_va: 0x20_0000,
            sites: vec![StaticSvcSite {
                pc: 0x20_0100,
                function: "do_fork".into(),
                offset_in_fn: 8,
                x8: StaticX8Value::Resolved(220), // `clone` = 220 (unclassified)
            }],
            distinct_resolved_nrs: vec![220],
        };
        let err = build_binary_inventory(&spec, &scan).unwrap_err();
        assert!(err.to_string().contains("unclassified static `svc #0` syscall 220"));
    }
}
