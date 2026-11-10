// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI Argument Definitions and `translation.toml` Configuration Loader
//! (`untrusted_driver::config`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (parses CLI flags and `translation.toml` files to configure
//!   which Rust crates or C translation units the build driver compiles and where generated files
//!   are written; does not parse ELF bytes, link sections, or emit trusted Lean definitions).
//! - **Purpose:** Defines the [`Cli`] / [`CommandName`] command-line interface, the
//!   [`TranslationConfig`] / [`ExportConfig`] / [`ExportTarget`] schema and loader
//!   ([`load_config`], [`load_configs`], [`select_configs`], [`apply_overrides`]), and the
//!   deterministic compiler flag sets ([`DETERMINISTIC_CODEGEN_FLAGS`], [`NATIVE_CFLAGS`]).
//!
//! # Key Types & Functions
//! - [`Cli`], [`CommandName`]: `clap` CLI definition for `rust-obj2lean`.
//! - [`TranslationConfig`], [`ExportConfig`], [`ExportTarget`]: `translation.toml` schema and
//!   resolved configuration.
//! - [`load_config`], [`load_configs`], [`select_configs`], [`apply_overrides`],
//!   [`default_config_paths`]: Configuration loading, filtering, and CLI flag overrides.
//! - [`DEFAULT_TARGET`], [`DETERMINISTIC_CODEGEN_FLAGS`], [`NATIVE_CFLAGS`],
//!   [`native_cflags_string`]: Deterministic Rust and C compilation flags.
//!
//! # When to Read This File
//! - Read this file when adding fields to `translation.toml`, adding CLI options, or changing path
//!   resolution for `--out-dir` / `--output`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use itertools::Itertools;
use serde::Deserialize;

use crate::trusted_common::{
    ConfiguredExtern, ExternKind, ObjModuleMeta, sha256_hex, upper_camel,
};

pub const DEFAULT_TARGET: &str = "aarch64-unknown-linux-gnu";
pub const DEFAULT_CONFIG_REL_PATHS: &[&str] = &[
    "CaseStudies/Hpack/Implementation/translation.toml",
    "CaseStudies/U128/Implementation/translation.toml",
    "CaseStudies/Protobuf/Implementation/translation.toml",
    "CaseStudies/Postcard/Implementation/translation.toml",
    "CaseStudies/Zerocopy/Implementation/translation.toml",
];
pub const DETERMINISTIC_CODEGEN_FLAGS: &[&str] = &[
    "-C",
    "target-cpu=generic",
    "-C",
    "no-vectorize-slp",
    "-C",
    "no-vectorize-loops",
];

/// Environment variable fallback for `--perturb-layout <BYTES>` when not passed on the CLI.
pub const PERTURB_LAYOUT_ENV: &str = "RUST_OBJ2LEAN_PERTURB_BYTES";

/// Validate that a layout-perturbation byte count is a multiple of 4.
pub fn validate_perturb_layout_bytes(bytes: u64, source: &str) -> Result<u64> {
    if bytes % 4 != 0 {
        bail!("{source}: layout perturbation byte count ({bytes}) must be a multiple of 4");
    }
    Ok(bytes)
}

fn parse_perturb_layout_arg(raw: &str) -> std::result::Result<u64, String> {
    let bytes: u64 = raw.trim().parse().map_err(|_| {
        format!("invalid `--perturb-layout` value `{raw}`: expected a non-negative integer multiple of 4")
    })?;
    validate_perturb_layout_bytes(bytes, "`--perturb-layout`").map_err(|e| e.to_string())
}

/// Resolve the active layout-perturbation byte count with precedence:
/// `--perturb-layout <BYTES>` CLI flag > `$RUST_OBJ2LEAN_PERTURB_BYTES` env var > `0`.
pub fn resolve_perturb_layout_bytes(
    cli_flag: Option<u64>,
    env_val: Option<&str>,
) -> Result<u64> {
    if let Some(b) = cli_flag {
        return validate_perturb_layout_bytes(b, "`--perturb-layout`");
    }
    if let Some(raw) = env_val.map(str::trim).filter(|s| !s.is_empty()) {
        let b: u64 = raw.parse().with_context(|| {
            format!(
                "invalid `{PERTURB_LAYOUT_ENV}` value `{raw}` (expected a non-negative integer multiple of 4)"
            )
        })?;
        return validate_perturb_layout_bytes(b, &format!("`{PERTURB_LAYOUT_ENV}`"));
    }
    Ok(0)
}

// ---------------------------------------------------------------------------
// CLI definitions
// ---------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(
    about = "Link the relocatable AArch64 objects (`.o`) of Rust crates and C sources and export the result to Lean 4 as an `Arm64.Obj.LinkedImage`, or generate fetch-decode lemmas.",
    after_help = "Additional subcommands (dispatched directly):\n  symexec         Fast untrusted ARM64 symbolic execution advisor (`rust-obj2lean symexec --help`)\n  layout          Print DWARF struct/union layouts (`rust-obj2lean layout --help`)\n\nEnvironment variables:\n  RUST_OBJ2LEAN_PERTURB_BYTES=<BYTES>  Fallback for `--perturb-layout <BYTES>` when not set on the CLI.\n\nExamples:\n  tools/target/release/rust-obj2lean --config CaseStudies/<Campaign>/Implementation/translation.toml\n  tools/target/release/rust-obj2lean --config CaseStudies/<Campaign>/Implementation/translation.toml --perturb-layout 64\n  RUST_OBJ2LEAN_PERTURB_BYTES=4096 tools/target/release/rust-obj2lean --config CaseStudies/<Campaign>/Implementation/translation.toml\n  tools/target/release/rust-obj2lean --check --only MyTarget\n  tools/target/release/rust-obj2lean fetch-decode-lemmas --prog myProg --base 0x1000 0x91000400 0xd65f03c0\n  tools/target/release/rust-obj2lean symexec MyLib my_func --to 0x40"
)]
pub struct Cli {
    /// Path(s) to per-crate TOML translation configuration file(s).
    /// May be specified multiple times; defaults to all crate `translation.toml` files under `VerifiedLibraries/*/Implementation/` and `CaseStudies/*/Implementation/`.
    #[arg(short, long = "config", value_name = "FILE", global = true)]
    pub config: Vec<PathBuf>,

    /// Output base directory for generated `.lean` files (resolves each target's relative `lean_file` under `<DIR>`).
    #[arg(long = "out-dir", visible_alias = "out-root", value_name = "DIR", global = true)]
    pub out_dir: Option<PathBuf>,

    /// Explicit output `.lean` file path when exporting a single target (the `Obj`/`Code`
    /// modules are written next to it).
    #[arg(short = 'o', long = "output", value_name = "FILE", global = true)]
    pub output: Option<PathBuf>,

    /// Override the Lean module prefix for generated `Obj`/`Code`/target modules
    /// (e.g. `CaseStudies.<Lib>.Generated`).
    #[arg(long = "module-prefix", value_name = "PREFIX", global = true)]
    pub module_prefix: Option<String>,

    /// Override the top-level Lean namespace prefix (defaults to `Examples`).
    #[arg(long = "namespace-prefix", value_name = "PREFIX", global = true)]
    pub namespace_prefix: Option<String>,

    /// Override the target's sub-namespace inside the namespace prefix (pass `""` to clear).
    #[arg(long = "sub-namespace", value_name = "NAMESPACE", global = true)]
    pub sub_namespace: Option<String>,

    /// Deterministically shift `.text` and `.rodata`/`.data` symbol offsets by `<BYTES>`
    /// (must be a multiple of 4; falls back to `$RUST_OBJ2LEAN_PERTURB_BYTES`).
    #[arg(
        long = "perturb-layout",
        value_name = "BYTES",
        global = true,
        value_parser = parse_perturb_layout_arg
    )]
    pub perturb_layout: Option<u64>,

    /// Emit pre-encoded `<c>_symEnc` / `<c>_stubEnc` tables, correspondence lemmas, and
    /// `<c>_lookup_0x<off>` / `<c>_unique_0x<off>` lemmas in `<ObjName>Code.lean`.
    #[arg(long = "emit-symbol-unique-lemmas", global = true)]
    pub emit_symbol_unique_lemmas: bool,

    /// Emit multi-block placed libraries (`Obj.MultiPlacedLib`) with one `CodeBlock` per
    /// `.text.<fn>` section and per-symbol `SymDataInfo` entries.
    #[arg(long = "multi-placed", global = true)]
    pub multi_placed: bool,

    /// Emit only `[placed]` outputs (and `<ObjName>ExtractedObj.*` when enabled) without invoking
    /// `untrusted_legacy_linker::link` or emitting `<ObjName>Obj.lean`.
    #[arg(long = "placed-only", global = true)]
    pub placed_only: bool,

    /// Emit pre-link `<ObjName>ExtractedObj.lean` (`List Obj.ExtractedObj`) and its `.bin`
    /// sidecar directly from `trusted_extractor` without invoking a static linker.
    #[arg(long = "extracted-obj", global = true)]
    pub extracted_obj: bool,

    /// Emit an ELF-free interned placement witness (`<ObjName>PlacedWitness.lean`) proving
    /// `<obj>Lib_placeable : ∃ pl, <obj>Lib.Placeable pl ∧ (<obj>Lib.text.externs.map pl.ρ).Nodup`
    /// when `[placed]` has no stock-linked `elf`.
    #[arg(
        long = "placed-witness",
        visible_alias = "placeable-witness",
        global = true
    )]
    pub placed_witness: bool,

    /// Explicit output `.lean` file path for the placed witness (`<ObjName>PlacedWitness.lean`).
    /// Also enables ELF-free witness emission when `[placed]` has no `elf`.
    #[arg(
        long = "placed-witness-out",
        visible_alias = "placeable-witness-out",
        value_name = "FILE",
        global = true
    )]
    pub placed_witness_out: Option<PathBuf>,

    /// Opt in to deprecated legacy `Arm64.Obj.LinkedImage` (`<ObjName>Obj.lean`) emission when
    /// `[placed] placed_only = true` is not set.
    #[arg(long = "legacy-linked-image", global = true)]
    pub legacy_linked_image: bool,

    /// Do not write: fail if a generated file differs from what the compiler produces now.
    #[arg(long)]
    pub check: bool,

    /// Print the verification-friendly C compiler flags (`NATIVE_CFLAGS`) and exit.
    #[arg(long = "print-cflags")]
    pub print_cflags: bool,

    /// Only export the named target(s) from the translation config(s).
    #[arg(long = "only", value_name = "NAME")]
    pub only: Vec<String>,

    #[command(subcommand)]
    pub command: Option<CommandName>,
}

#[derive(Subcommand, Debug)]
pub enum CommandName {
    /// Export crate objects (`Obj` modules), the laid-out `Code` modules and lemma files to Lean 4 (default).
    #[command(
        after_help = "Examples:\n  tools/target/release/rust-obj2lean export --config CaseStudies/<Campaign>/Implementation/translation.toml\n  tools/target/release/rust-obj2lean export --check --only MyTarget"
    )]
    Export {
        /// Do not write: fail if a generated file differs from what the compiler produces now.
        #[arg(long)]
        check: bool,

        /// Only export the named target(s) from the translation config(s).
        #[arg(long = "only", value_name = "NAME")]
        only: Vec<String>,
    },
    /// Print the verification-friendly C compiler flags (`NATIVE_CFLAGS`), space-separated.
    #[command(
        name = "print-cflags",
        visible_alias = "cflags",
        after_help = "Examples:\n  tools/target/release/rust-obj2lean print-cflags"
    )]
    PrintCflags,
    /// Generate or check `@[simp, arm64_norm]` fetch-decode lemmas for `Program.ofWords` / `Program.ofBytes` definitions in Lean files (or CLI hex words).
    #[command(
        visible_alias = "gen-fetch-decode-lemmas",
        after_help = "Examples:\n  tools/target/release/rust-obj2lean fetch-decode-lemmas --prog myProg --base 0x1000 0x91000400 0xd65f03c0\n  tools/target/release/rust-obj2lean fetch-decode-lemmas --check CaseStudies/<Campaign>/Spec/Top.lean"
    )]
    FetchDecodeLemmas {
        /// Verify that auto-generated fetch-decode lemma blocks in Lean files are up to date without modifying them.
        #[arg(long)]
        check: bool,

        /// Program name for standalone CLI hex-word mode.
        #[arg(long)]
        prog: Option<String>,

        /// Base address (e.g. `0x1000`) for standalone CLI hex-word mode.
        #[arg(long, default_value = "0x1000")]
        base: String,

        /// Lean files (`Examples/*.lean`) to update/check, or 32-bit hex words when `--prog` is set.
        #[arg(value_name = "FILES_OR_WORDS", required = true)]
        inputs: Vec<String>,
    },
}

// ---------------------------------------------------------------------------
// Translation Configuration (`translation.toml`)
// ---------------------------------------------------------------------------

/// A `translation.toml`: either a pure-Rust configuration (`crates` and optional
/// `[[sysroot_objects]]`) or a pure-C configuration (`[native_compiler]`,
/// `[[native_objects]]`, `c_sources`, `c_objects`, `c_archives`, `build_script`,
/// `build_command`), extracted into one trusted `Obj` module and its lemma files.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TranslationConfig {
    pub crate_dir: Option<PathBuf>,
    /// Rust target triple for `cargo rustc` and sysroot `.rlib` lookup
    /// (defaults to [`DEFAULT_TARGET`], `"aarch64-unknown-linux-gnu"`).
    pub target: Option<String>,
    /// Rust crates whose `.o` files are extracted (default: the package in `crate_dir`;
    /// must be omitted for pure-C configurations).
    pub crates: Option<Vec<String>>,
    /// Stem of the generated Lean names: `<obj_name>Obj`, `<obj_name>Image`, `<obj_name>Code`.
    pub obj_name: String,
    /// Trusted `Obj` module path (default: `<dir of first lean_file>/<ObjName>Obj.lean`, or
    /// `Examples/Generated/<ObjName>Obj.lean` when `targets` is empty).
    pub obj_file: Option<PathBuf>,
    /// Untrusted `Code` module path (default: `<dir of first lean_file>/<ObjName>Code.lean`).
    pub code_file: Option<PathBuf>,
    /// Whether to emit `<ObjName>RegistryFacts.lean` containing `.rodata` / `.data.rel.ro`
    /// `R_AARCH64_ABS64` relocation pointer equations (`rodataPtr img (sym + off) = img.fnAddr target`).
    #[serde(default)]
    pub registry_facts: bool,
    /// Optional explicit output path for `<ObjName>RegistryFacts.lean`.
    pub registry_facts_file: Option<PathBuf>,
    /// Whether to emit `relocFns` and `dataSyms` on `ObjectInfo` in `<ObjName>Obj.lean`.
    #[serde(default)]
    pub layout_generic_relocs: bool,
    /// Whether to emit `<c>_lookup_0x<off>` and `<c>_unique_0x<off>` lemmas for all symbols in `<ObjName>Code.lean`.
    #[serde(default)]
    pub emit_symbol_unique_lemmas: bool,
    /// Whether `<code>` in `<ObjName>Code.lean` slices `.code` to `<imgName>.code.take <code>TextEnd`
    /// so external stub slots after `.text` are excluded from `CodeLoaded`.
    #[serde(default)]
    pub slice_stubs_in_code: bool,
    /// Whether to place non-empty `.rodata`, writable `.data`/`.bss`/extern-data, and the GOT on
    /// separate 4 KiB pages (`DataLayout::PageSeparated`; default `false` = `DataLayout::Interleaved`).
    #[serde(default)]
    pub page_separate_data: bool,
    /// Opt in to deprecated legacy `Arm64.Obj.LinkedImage` (`<ObjName>Obj.lean`) emission when
    /// `[placed] placed_only = true` is not set.
    #[serde(default)]
    pub legacy_linked_image: bool,
    pub namespace_prefix: Option<String>,
    pub title: Option<String>,
    #[serde(default)]
    pub license_header: Vec<String>,
    pub upstream: Option<UpstreamConfig>,
    #[serde(default)]
    pub hashed_inputs: Vec<String>,
    /// Extra `rustc` flags appended to `RUSTFLAGS` for the whole build (every crate, including
    /// dependencies), one argument per entry, e.g. `["--cfg", "aes_backend=\"soft\""]`.
    #[serde(default)]
    pub rustflags: Vec<String>,
    /// Functions to extract from the precompiled objects of sysroot crates (loaded after
    /// the crates' or native objects, in this order).
    #[serde(default)]
    pub sysroot_objects: Vec<SysrootObjectConfig>,
    /// The pinned C compiler for `[[native_objects]]` / `c_sources` / `build_script`.
    pub native_compiler: Option<NativeCompilerConfig>,
    /// C translation units compiled to AArch64 and extracted in full (pure-C configurations
    /// only, in this order).
    #[serde(default)]
    pub native_objects: Vec<NativeObjectConfig>,
    /// C source files (`.c`, relative to the config directory) compiled with `zig cc` using
    /// `NATIVE_CFLAGS` + `c_flags` and extracted in full.
    #[serde(default)]
    pub c_sources: Vec<PathBuf>,
    /// Pre-compiled relocatable AArch64 ELF `.o` object files (or `.a` archives), relative
    /// to the config directory, loaded directly without recompiling.
    #[serde(default)]
    pub c_objects: Vec<PathBuf>,
    /// Pre-compiled static library archives (`.a`), relative to the config directory, whose
    /// `.o` members are extracted in archive order.
    #[serde(default)]
    pub c_archives: Vec<PathBuf>,
    /// Extra compiler flags appended to `NATIVE_CFLAGS` when compiling `c_sources` /
    /// `[[native_objects]]` and passed in `CFLAGS` to `build_script` / `build_command`.
    #[serde(default)]
    pub c_flags: Vec<String>,
    /// Optional build script (relative to the config directory) executed via `sh` before
    /// loading `c_archives`, `c_objects`, `c_sources`, and `[[native_objects]]`.
    pub build_script: Option<PathBuf>,
    /// Optional build command + arguments (executed in the config directory) before loading
    /// `c_archives`, `c_objects`, `c_sources`, and `[[native_objects]]`.
    pub build_command: Option<Vec<String>>,
    /// Explicit external symbol declarations (`[[externs]]`) overriding or specifying the
    /// kind, size, and alignment of undefined symbols.
    #[serde(default)]
    pub externs: Vec<ExternConfig>,
    #[serde(default)]
    pub targets: Vec<TargetConfig>,
    /// `[placed]`: also emit the layout-generic placed library (`<ObjName>PlacedObj.lean`) and,
    /// with `elf`, the pinned ELF bytes (`<ObjName>ElfObj.lean`) and the library's placement in
    /// that stock-linked ELF (`<ObjName>PlacedWitness.lean`).
    pub placed: Option<PlacedTomlConfig>,
}

/// `[placed]`: the placed-library outputs (`untrusted_placed`).
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PlacedTomlConfig {
    /// Raw `.symtab` names of the exported functions.
    pub exports: Vec<String>,
    /// Stock-linked ELF (relative to the config directory) to read the placement witness from.
    pub elf: Option<PathBuf>,
    /// Expected lowercase hex SHA-256 of `elf` (required with `elf`). The generator fails closed
    /// when it is missing or does not match the file, and pins the emitted `file_bytes%` to it.
    pub elf_sha256: Option<String>,
    /// With `elf`: an existing Lean constant holding the ELF's bytes (pinned there by
    /// `file_bytes%`) and the module that defines it, used instead of emitting
    /// `<ObjName>ElfObj.lean`, so that several configs can name the same bytes constant. Set both
    /// or neither.
    pub elf_bytes: Option<String>,
    pub elf_bytes_module: Option<String>,
    /// With `elf` and `linked`: module stem of an existing per-ELF facts module (`<…>ElfFacts`,
    /// emitted by another config in the same generated directory) to import instead of emitting
    /// one. The generator fails closed unless that module exists and records the same ELF bytes
    /// constant, defining module and SHA-256.
    pub elf_facts_module: Option<String>,
    /// With `elf`: also put the kernel-checked `Obj.PlacedLib.LinkedIn` proof for the witness
    /// (via `ProofLib.Placed.Check`) in `<ObjName>PlacedWitness.lean`.
    #[serde(default)]
    pub linked: bool,
    /// Emit a multi-block placed library (`Obj.MultiPlacedLib`, one `CodeBlock` per `.text.<fn>`
    /// section and per-symbol `SymDataInfo` entries) instead of a single concatenated `CodeBlock`.
    #[serde(default, alias = "multi_placed")]
    pub multi: bool,
    /// Emit `noncomputable def` for the code bytes, the text block and the library of a
    /// single-block `<ObjName>PlacedObj.lean`, so that Lean skips compiling them. Compiling the
    /// `include_bytes%` literal of a large code image takes time superlinear in its size; proofs
    /// only need the kernel to reduce these constants. With it, `#guard`/`#eval` over the library
    /// and computable definitions built on it are unavailable. Not supported with `multi` or a
    /// placement witness (default `false`).
    #[serde(default)]
    pub noncomputable_code: bool,
    /// With `multi`: split the code blocks of `<ObjName>PlacedObj.lean` over this many sibling
    /// shard modules `<ObjName>PlacedObjShard<k>.lean` (balanced by code size), each defining
    /// its blocks' code constants and a `List Obj.CodeBlock`; `<ObjName>PlacedObj.lean` imports
    /// them and joins the lists. The resulting `Obj.MultiPlacedLib` is the same value. Omitted
    /// or `1` emits the single module unchanged.
    pub placed_shards: Option<usize>,
    /// With `multi`: functions defined in this library (raw `.symtab` or demangled block names)
    /// at which the reachability search from `exports` stops. Their blocks, and code reachable
    /// only through them, are left out, and direct calls to them become ordinary externs (hooks)
    /// resolved from the stock-linked ELF. Each must be a non-exported function with exactly one
    /// global `.symtab` entry in every witness ELF; a proof composing this library still needs
    /// a contract for each boundary function, typically another config's export.
    #[serde(default)]
    pub extern_boundary: Vec<String>,
    /// Emit only the placed-library artifacts (`<ObjName>PlacedObj.lean`, `<ObjName>ElfObj.lean`,
    /// `<ObjName>PlacedWitness.lean`), skipping `untrusted_legacy_linker::link` and `<ObjName>Obj.lean`.
    #[serde(default)]
    pub placed_only: bool,
    /// Emit `<ObjName>ExtractedObj.lean` and `<ObjName>ExtractedObj.bin` directly from the
    /// extracted `.o` files (`trusted_extractor`) without invoking a static linker.
    #[serde(default, alias = "extracted_obj")]
    pub emit_extracted_obj: bool,
    /// Without `elf`: synthesize a canonical valid `Placement` and emit `<ObjName>PlacedWitness.lean`
    /// proving `<obj>Lib_placeable : ∃ pl, <obj>Lib.Placeable pl ∧ (<obj>Lib.text.externs.map pl.ρ).Nodup`
    /// via `Obj.Interned.checkPlaceableExt` (`by decide +kernel`).
    #[serde(default, alias = "placeable_witness")]
    pub witness: bool,
    /// Optional explicit output `.lean` path for `<ObjName>PlacedWitness.lean` (relative to the
    /// output base directory). Setting this without `elf` also enables ELF-free witness emission.
    #[serde(default, alias = "witness_out", alias = "placeable_witness_out")]
    pub placed_witness_out: Option<PathBuf>,
    /// `[[placed.extra_witnesses]]`: further placement witnesses of the same library, each in
    /// another ELF whose bytes are already defined by an existing (SHA-pinned) Lean module.
    #[serde(default)]
    pub extra_witnesses: Vec<ExtraWitnessTomlConfig>,
    /// With `multi` and `linked`: full name of a Lean module (e.g. `ProofLib.Placed.Split`, or a
    /// module re-exporting it) whose namespace of the same name provides `seg_lens%`, `rLen`,
    /// the chunked walks (`lTextChunk`, `lTextTail`, `lDataChunk`, ...), the per-check `Bool`s
    /// (`textPlaceableAllB`, ...) and `checkMultiDisjoint_spec_chunks`. Every linked multi-block
    /// witness then proves its `<p>_ok` theorem from separate top-level kernel facts (segment
    /// lengths, one per text or data walk chunk, and one per segment-free check, each in its own
    /// shard module) instead of one `decide +kernel` over
    /// `Obj.Interned.checkMultiDisjoint`, so the kernel's peak memory is that of the largest fact
    /// rather than of the whole check (needed for multi-megabyte ELFs).
    pub split_check_module: Option<String>,
    /// Single-block (`multi = false`) linked witnesses only (`linked = true` or
    /// `[[placed.extra_witnesses]]`): prove each witness's placement theorem from separate
    /// top-level kernel facts (`ProofLib.Placed.SplitSingleFast`: a literal symbol tree checked
    /// in index chunks, the text walk in word chunks, the data walk in object chunks, and one fact
    /// per segment-free check, each in its own shard module) instead of one `decide +kernel` over
    /// `Obj.Interned.check`, so the kernel's peak memory is that of the largest fact.
    #[serde(default)]
    pub chunked_check: bool,
    /// With `elf` and `linked`: full name of a Lean module whose namespace of the same name
    /// provides `suffix_of%`, `TailsOk`, `drop_of_rDrop`, `drop_chain`, `length_of_drop`,
    /// `hdrOk`, `phdrsOf`, `symtabOf` and `parse_of_parts`. Every emitted facts module then proves
    /// its parse theorem from separate top-level kernel facts (file length, ELF header, program
    /// headers, symbol table, well-formedness) over suffix constants of the bytes at the far
    /// offsets the symbol-table parse seeks to, instead of one `rfl_kernel` over
    /// `ElfImage.fastParse`, so the kernel's peak memory is that of the largest fact.
    pub split_parse_module: Option<String>,
}

/// `[[placed.extra_witnesses]]`: a placement witness of the library in a further ELF.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExtraWitnessTomlConfig {
    /// Module stem of the generated witness (`<module>.lean` next to `<ObjName>PlacedWitness.lean`).
    pub module: String,
    /// Name prefix of the definitions it emits (`<prefix>Placement`, `<prefix>Elf`,
    /// `<prefix>_parse`, `<prefix>_linkedIn`, …).
    pub prefix: String,
    /// Lean namespace of the generated module (default: the generated-code namespace).
    pub namespace: Option<String>,
    /// The ELF (relative to the config directory).
    pub elf: PathBuf,
    /// Expected lowercase hex SHA-256 of `elf` (fail closed).
    pub elf_sha256: String,
    /// The existing Lean constant holding the ELF's bytes (pinned there by `file_bytes%`), and
    /// the module that defines it.
    pub elf_bytes: String,
    pub elf_bytes_module: String,
    /// Module stem of an existing per-ELF facts module to import instead of emitting one (see
    /// [`PlacedTomlConfig::elf_facts_module`]).
    pub elf_facts_module: Option<String>,
}

/// Resolved `[[placed.extra_witnesses]]` entry.
#[derive(Clone, Debug)]
pub struct ExtraWitnessConfig {
    pub prefix: String,
    pub namespace: Option<String>,
    /// Absolute path of the ELF.
    pub elf: PathBuf,
    pub elf_sha256: String,
    pub elf_bytes: String,
    pub elf_bytes_module: String,
    /// Module stem of an existing per-ELF facts module to import instead of emitting one.
    pub elf_facts_module: Option<String>,
    /// Output path and Lean module name of the witness.
    pub witness_file: PathBuf,
    pub witness_module: String,
}

/// Resolved `[placed]` outputs.
#[derive(Clone, Debug)]
pub struct PlacedConfig {
    pub exports: Vec<String>,
    /// Absolute path of the stock-linked ELF.
    pub elf: Option<PathBuf>,
    /// Pinned SHA-256 of `elf` (`[placed] elf_sha256`).
    pub elf_sha256: Option<String>,
    /// Output path and Lean module name of `<ObjName>PlacedObj.lean` (the `PlacedLib`).
    pub lib_file: PathBuf,
    pub lib_module: String,
    /// Output path and Lean module name of `<ObjName>ElfObj.lean` (the pinned ELF bytes).
    pub elf_file: PathBuf,
    pub elf_module: String,
    /// `[placed] elf_bytes` / `elf_bytes_module`: an existing bytes constant and its module, used
    /// instead of emitting `<ObjName>ElfObj.lean`.
    pub elf_bytes_override: Option<(String, String)>,
    /// `[placed] elf_facts_module`: module stem of an existing per-ELF facts module to import.
    pub elf_facts_module: Option<String>,
    /// Output path and Lean module name of `<ObjName>PlacedWitness.lean`.
    pub witness_file: PathBuf,
    pub witness_module: String,
    /// Put the `LinkedIn` proof in `<ObjName>PlacedWitness.lean` (requires `elf`).
    pub linked: bool,
    /// Emit a synthesized ELF-free interned placement witness when `elf` is `None`.
    pub emit_placeable_witness: bool,
    /// Emit a multi-block `Obj.MultiPlacedLib` instead of a single-block `Obj.PlacedLib`.
    pub multi: bool,
    /// `[placed] noncomputable_code`: emit the single-block code, text and library as
    /// `noncomputable def`.
    pub noncomputable_code: bool,
    /// Number of shard modules for the multi-block library's code blocks (`1`: no shards).
    pub placed_shards: usize,
    /// `[placed] extern_boundary`: functions at which the reachability cone stops (`multi` only).
    pub extern_boundary: Vec<String>,
    /// Emit only the placed-library artifacts without invoking `untrusted_legacy_linker::link` or emitting `<ObjName>Obj.lean`.
    pub placed_only: bool,
    /// Emit `<ObjName>ExtractedObj.lean` and `<ObjName>ExtractedObj.bin` from `trusted_extractor`.
    pub emit_extracted_obj: bool,
    /// Further linked placement witnesses (`[[placed.extra_witnesses]]`).
    pub extra_witnesses: Vec<ExtraWitnessConfig>,
    /// `[placed] split_check_module`: module (and namespace) of the split multi-block check.
    pub split_check_module: Option<String>,
    /// `[placed] chunked_check`: chunked kernel check of the single-block linked witnesses.
    pub chunked_check: bool,
    /// `[placed] split_parse_module`: module (and namespace) of the split ELF parse.
    pub split_parse_module: Option<String>,
}

impl PlacedConfig {
    /// Output path of shard module `k` of `<ObjName>PlacedObj.lean` (`<ObjName>PlacedObjShard<k>.lean`).
    pub fn shard_file(&self, k: usize) -> PathBuf {
        let stem = self
            .lib_file
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy();
        self.lib_file.with_file_name(format!("{stem}Shard{k}.lean"))
    }

    /// Lean module name of shard module `k` (`<lib_module>Shard<k>`).
    pub fn shard_module(&self, k: usize) -> String {
        format!("{}Shard{k}", self.lib_module)
    }

    /// The shard module paths (empty when `placed_shards <= 1`).
    pub fn shard_files(&self) -> Vec<PathBuf> {
        if self.placed_shards <= 1 {
            return vec![];
        }
        (0..self.placed_shards).map(|k| self.shard_file(k)).collect()
    }

    /// Output path of the generated module with stem `stem` next to `<ObjName>PlacedObj.lean`
    /// (e.g. a per-ELF facts module).
    pub fn sibling_file(&self, stem: &str) -> PathBuf {
        self.lib_file.with_file_name(format!("{stem}.lean"))
    }

    /// Lean module name of the generated module with stem `stem` next to `<ObjName>PlacedObj`.
    pub fn sibling_module(&self, stem: &str) -> String {
        match self.lib_module.rsplit_once('.') {
            Some((prefix, _)) => format!("{prefix}.{stem}"),
            None => stem.to_string(),
        }
    }
}

/// `[[sysroot_objects]]`: extract the named global functions or objects of a sysroot crate
/// (e.g. `alloc` or `compiler_builtins`), with every section they reach through relocations
/// against local symbols, from the single precompiled `.o` member defining them in the target's
/// sysroot rlib. Relocations against other global symbols are left undefined (resolved like any
/// other extern).
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SysrootObjectConfig {
    /// Crate name of the sysroot rlib (`lib<crate>-<hash>.rlib`).
    #[serde(rename = "crate")]
    pub krate: String,
    /// Optional distinct object name (a C identifier; defaults to `crate`), used when
    /// extracting multiple members from a multi-object sysroot rlib.
    #[serde(default)]
    pub name: Option<String>,
    /// Demangled (`{:#}`) or raw names of the global functions or objects to extract.
    pub roots: Vec<String>,
}

impl SysrootObjectConfig {
    /// Object name used in the linked image and local-symbol disambiguation suffix.
    pub fn obj_name(&self) -> &str {
        self.name.as_deref().unwrap_or(&self.krate)
    }
}

/// `[native_compiler]`: the C compiler used for `[[native_objects]]`. Only `zig cc` is
/// supported; the binary is `$ZIG`, `zig` on `PATH`, or `~/.local/bin/zig`, and must
/// report `zig_version`.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCompilerConfig {
    pub zig_version: String,
}

/// `[[native_objects]]`: compile one C translation unit (`source`, relative to the config
/// directory) to a relocatable AArch64 object with `zig cc` (`NATIVE_CFLAGS`, plus the given
/// include directories, defines, and `c_flags`) and extract the entire `.o` file.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeObjectConfig {
    /// The object's name (a C identifier; distinct from every other object).
    pub name: String,
    pub source: PathBuf,
    #[serde(default)]
    pub include_dirs: Vec<PathBuf>,
    /// `NAME` or `NAME=VALUE`, passed as `-D`.
    #[serde(default)]
    pub defines: Vec<String>,
    /// Additional per-object compiler flags appended after `NATIVE_CFLAGS`.
    #[serde(default)]
    pub c_flags: Vec<String>,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum ExternKindSimple {
    Func,
    Object,
    Tls,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum ExternKindConfig {
    Simple(ExternKindSimple),
    DataMap {
        data: u64,
    },
    TlsMap {
        tls: u64,
    },
    FuncMap {
        func: u64,
    },
}

/// `[[externs]]`: explicit declaration of an external symbol's kind, size, and alignment.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ExternConfig {
    pub name: String,
    pub kind: ExternKindConfig,
    pub size: Option<u64>,
    pub align: Option<u64>,
}

/// Fixed `zig cc` flags for `[[native_objects]]` / `c_sources`: freestanding-friendly, static
/// relocation model, no unwind tables / debug info / stack protector / auto-vectorization /
/// jump tables / common symbols, one section per function/datum.
pub const NATIVE_CFLAGS: &[&str] = &[
    "-target",
    "aarch64-linux-musl",
    "-mcpu=generic",
    "-O2",
    "-g0",
    "-fno-pic",
    "-fno-pie",
    "-fno-stack-protector",
    "-fno-asynchronous-unwind-tables",
    "-fno-unwind-tables",
    "-fno-vectorize",
    "-fno-slp-vectorize",
    "-fno-jump-tables",
    "-fno-common",
    "-ffunction-sections",
    "-fdata-sections",
    "-fno-ident",
];

/// Format `NATIVE_CFLAGS` (plus optional `extra` flags) as a single space-separated string.
pub fn native_cflags_string(extra: &[String]) -> String {
    NATIVE_CFLAGS
        .iter()
        .copied()
        .chain(extra.iter().map(String::as_str))
        .join(" ")
}

/// Return `Some(tok)` if `flag` contains an optimization flag that overrides the verified
/// `-O2` optimization level (anything starting with `-O` or `--optimize` other than `-O2`,
/// `-O3`, `--optimize=2`, or `--optimize=3`).
pub fn disallowed_opt_flag(flag: &str) -> Option<&str> {
    flag.split_whitespace().find(|&tok| {
        (tok.starts_with("-O") && tok != "-O2" && tok != "-O3")
            || tok == "--optimize"
            || (tok.starts_with("--optimize=") && tok != "--optimize=2" && tok != "--optimize=3")
    })
}

/// Derive a valid C identifier from a file path's stem (stripping a trailing `.c` before `.o`
/// if present, and replacing non-alphanumeric characters with `_`).
pub fn c_stem_ident(path: &Path) -> Result<String> {
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    let stem = stem.strip_suffix(".c").unwrap_or(stem);
    let mut s: String = stem
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() || s.chars().all(|c| c == '_') {
        bail!("cannot derive a C identifier from `{}`", path.display());
    }
    if s.starts_with(|c: char| c.is_ascii_digit()) {
        s.insert(0, '_');
    }
    Ok(s)
}

/// A lemma file (`[[targets]]`): fetch lemmas for the functions matching `lemma_allowlist`.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TargetConfig {
    pub name: String,
    pub lean_file: PathBuf,
    pub sub_namespace: Option<String>,
    pub prog_name: String,
    pub title: String,
    #[serde(default)]
    pub hashed_inputs: Vec<String>,
    /// Regexes matched (anchored) against demangled names or their last `::` component.
    pub lemma_allowlist: Vec<String>,
    /// Split the per-instruction lemmas into this many shard modules (`<lean_file>Shard<i>.lean`,
    /// imported by `lean_file`), so Lake checks them in parallel. Lemma names do not change.
    #[serde(default)]
    pub lemma_shards: Option<usize>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamConfig {
    pub name: String,
    pub repo_url: String,
    pub tag: String,
    pub commit: Option<String>,
    pub vendor_symlink: Option<PathBuf>,
    pub probe_path: Option<PathBuf>,
    pub env_var: Option<String>,
    pub no_clone_env_var: Option<String>,
    pub home_subdir: Option<PathBuf>,
}

/// A resolved `translation.toml`.
#[derive(Clone, Debug)]
pub struct ExportConfig {
    pub config_rel: String,
    pub config_hash: String,
    pub crate_dir: PathBuf,
    pub target: String,
    pub crates: Vec<String>,
    pub obj_name: String,
    /// Output path and Lean module name of the trusted `Obj` module.
    pub obj_file: PathBuf,
    pub obj_module: String,
    /// Output path and Lean module name of the untrusted `Code` module.
    pub code_file: PathBuf,
    pub code_module: String,
    /// Optional output path and Lean module name of `<ObjName>RegistryFacts.lean`.
    pub registry_facts_file: Option<PathBuf>,
    pub registry_facts_module: Option<String>,
    /// Whether to emit `relocFns` and `dataSyms` on `ObjectInfo` in `<ObjName>Obj.lean`.
    pub layout_generic_relocs: bool,
    /// Whether to emit `<c>_lookup_0x<off>` and `<c>_unique_0x<off>` lemmas for all symbols in `<ObjName>Code.lean`.
    pub emit_symbol_unique_lemmas: bool,
    /// Whether `<code>` in `<ObjName>Code.lean` slices `.code` to `<imgName>.code.take <code>TextEnd`.
    pub slice_stubs_in_code: bool,
    /// Whether to place non-empty `.rodata`, writable `.data`/`.bss`/extern-data, and the GOT on
    /// separate 4 KiB pages (`DataLayout::PageSeparated`; default `false` = `DataLayout::Interleaved`).
    pub page_separate_data: bool,
    /// Opt in to deprecated legacy `Arm64.Obj.LinkedImage` (`<ObjName>Obj.lean`) emission when
    /// `[placed] placed_only = true` is not set.
    pub legacy_linked_image: bool,
    /// Deterministic layout perturbation shift in bytes (`0` for normal layout, else multiple of 4).
    pub perturb_layout_bytes: u64,
    pub namespace_prefix: String,
    pub title: String,
    pub license_header: Vec<String>,
    pub upstream: Option<UpstreamConfig>,
    pub hashed_inputs: Vec<String>,
    pub rustflags: Vec<String>,
    pub sysroot_objects: Vec<SysrootObjectConfig>,
    pub native_compiler: Option<NativeCompilerConfig>,
    pub native_objects: Vec<NativeObjectConfig>,
    pub c_sources: Vec<PathBuf>,
    pub c_objects: Vec<PathBuf>,
    pub c_archives: Vec<PathBuf>,
    pub c_flags: Vec<String>,
    pub build_script: Option<PathBuf>,
    pub build_command: Option<Vec<String>>,
    pub externs: Vec<ConfiguredExtern>,
    pub targets: Vec<ExportTarget>,
    pub placed: Option<PlacedConfig>,
}

/// A resolved lemma file.
#[derive(Clone, Debug)]
pub struct ExportTarget {
    pub name: String,
    pub lean_file: PathBuf,
    pub lean_module: String,
    pub sub_namespace: Option<String>,
    pub prog_name: String,
    pub title: String,
    pub hashed_inputs: Vec<String>,
    pub lemma_allowlist: Vec<String>,
    /// Number of shard modules for the per-instruction lemmas (1 = everything in `lean_file`).
    pub lemma_shards: usize,
    /// Explicit `lemma_shards` setting from the `.toml` config (`None` when omitted).
    pub explicit_lemma_shards: Option<usize>,
}

impl ExportConfig {
    /// `Obj` module metadata passed to `untrusted_legacy_linker` / `untrusted_placed`.
    pub fn obj_meta(&self) -> ObjModuleMeta {
        ObjModuleMeta {
            obj_name: self.obj_name.clone(),
            obj_file: self.obj_file.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            title: self.title.clone(),
            license_header: self.license_header.clone(),
        }
    }

    /// Names of all statically known single-file objects, in load order: the crates, the
    /// native objects, `c_sources`, non-archive `c_objects`, and the sysroot objects.
    pub fn object_names(&self) -> Vec<String> {
        self.crates
            .iter()
            .cloned()
            .chain(self.native_objects.iter().map(|n| n.name.clone()))
            .chain(
                self.c_sources
                    .iter()
                    .filter_map(|p| c_stem_ident(p).ok()),
            )
            .chain(
                self.c_objects
                    .iter()
                    .filter(|p| p.extension().is_none_or(|e| e != "a"))
                    .filter_map(|p| c_stem_ident(p).ok()),
            )
            .chain(self.sysroot_objects.iter().map(|s| s.obj_name().to_string()))
            .collect()
    }

    /// `<obj_name>Obj` (single object) or `<obj_name><Crate>Obj` (several objects).
    pub fn obj_def_name(&self, crate_name: &str) -> String {
        self.obj_def_name_for(
            crate_name,
            if self.c_archives.is_empty()
                && self
                    .c_objects
                    .iter()
                    .all(|p| p.extension().is_none_or(|e| e != "a"))
            {
                self.object_names().len()
            } else {
                2
            },
        )
    }

    /// `<obj_name>Obj` when `num_objects == 1`, or `<obj_name><Crate>Obj` when `num_objects > 1`.
    pub fn obj_def_name_for(&self, crate_name: &str, num_objects: usize) -> String {
        self.obj_meta().obj_def_name_for(crate_name, num_objects)
    }

    /// `<obj_name>Image : Obj.LinkedImage`, the linked image of all objects.
    pub fn image_def_name(&self) -> String {
        self.obj_meta().image_def_name()
    }

    /// File next to `obj_file` holding the linked code bytes: `<ObjStem>.code.bin`.
    pub fn code_bin_file(&self) -> PathBuf {
        self.obj_meta().code_bin_file()
    }

    /// File next to `obj_file` holding the linked data bytes: `<ObjStem>.data.bin`.
    pub fn data_bin_file(&self) -> PathBuf {
        self.obj_meta().data_bin_file()
    }
}

/// Lean module name of a file given relative to its library's source directory.
pub fn lean_module_of(rel: &Path) -> String {
    rel.with_extension("")
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .join(".")
}

#[derive(Deserialize)]
struct CargoManifestPackageOnly {
    package: CargoPackageName,
}

#[derive(Deserialize)]
struct CargoPackageName {
    name: String,
}

pub fn infer_target_crate_name(crate_dir: &Path) -> Result<String> {
    let manifest_path = crate_dir.join("Cargo.toml");
    let raw = fs::read_to_string(&manifest_path).with_context(|| {
        format!(
            "failed to read `{}` to infer crate name",
            manifest_path.display()
        )
    })?;
    let parsed: CargoManifestPackageOnly = toml::from_str(&raw).with_context(|| {
        format!(
            "failed to parse `[package].name` from `{}`",
            manifest_path.display()
        )
    })?;
    Ok(parsed.package.name.replace('-', "_"))
}

pub fn normalize_path(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for comp in path.components() {
        match comp {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                if !out.pop() {
                    out.push(comp);
                }
            }
            c => out.push(c),
        }
    }
    if out.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        out
    }
}

pub fn resolve_path_from(base: &Path, path: &Path) -> PathBuf {
    if path.is_relative() {
        normalize_path(&base.join(path))
    } else {
        normalize_path(path)
    }
}

pub fn resolve_target_lean_file(out_base: &Path, lean_file: &Path) -> PathBuf {
    if lean_file.is_relative()
        && out_base
            .file_name()
            .is_some_and(|n| n == "Generated" || n == "GeneratedLean" || lean_file.starts_with(n))
        && let Some(fname) = lean_file.file_name()
    {
        return normalize_path(&out_base.join(fname));
    }
    resolve_path_from(out_base, lean_file)
}

pub fn infer_namespace_prefix_from_out_dir(out_dir: Option<&Path>) -> Option<String> {
    let out = out_dir?;
    if out.file_name().is_some_and(|n| n == "Generated") {
        let parent_name = out.parent()?.file_name()?.to_str()?;
        if !parent_name.is_empty()
            && parent_name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            return Some(parent_name.to_string());
        }
    } else if out
        .file_name()
        .is_some_and(|n| n == "GeneratedLean" || n == ".GeneratedLean")
    {
        return Some("GeneratedLean".to_string());
    }
    None
}

pub fn resolve_cli_existing_or_repo_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        return normalize_path(path);
    }
    if let Ok(cwd) = env::current_dir() {
        let from_cwd = normalize_path(&cwd.join(path));
        if from_cwd.exists() {
            return from_cwd;
        }
    }
    let from_repo = normalize_path(&repo_root.join(path));
    if from_repo.exists() {
        return from_repo;
    }
    if let Ok(cwd) = env::current_dir() {
        normalize_path(&cwd.join(path))
    } else {
        from_repo
    }
}

pub fn resolve_cli_output_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        return normalize_path(path);
    }
    if let Ok(cwd) = env::current_dir() {
        normalize_path(&cwd.join(path))
    } else {
        normalize_path(&repo_root.join(path))
    }
}

pub fn resolve_crate_dir(
    config_path: &Path,
    repo_root: &Path,
    configured: Option<&Path>,
) -> PathBuf {
    let config_dir = config_path.parent().unwrap_or_else(|| Path::new("."));
    match configured {
        None => normalize_path(config_dir),
        Some(dir) if dir.is_absolute() => normalize_path(dir),
        Some(dir) => {
            let from_config = normalize_path(&config_dir.join(dir));
            if dir == Path::new(".") || from_config.join("Cargo.toml").exists() {
                from_config
            } else {
                let from_repo = normalize_path(&repo_root.join(dir));
                if from_repo.join("Cargo.toml").exists()
                    || (!from_config.exists() && from_repo.exists())
                {
                    from_repo
                } else {
                    from_config
                }
            }
        }
    }
}

pub fn merge_hashed_inputs(crate_inputs: &[String], target_inputs: &[String]) -> Vec<String> {
    let mut combined = Vec::new();
    let mut seen = BTreeSet::new();
    for item in crate_inputs.iter().chain(target_inputs.iter()) {
        if seen.insert(item.clone()) {
            combined.push(item.clone());
        }
    }
    combined
}

/// `path` relative to `base` (climbing with `..` if needed), so that provenance does not
/// depend on where the repository is checked out.
pub fn relative_display(path: &Path, base: &Path) -> String {
    let mut up = PathBuf::new();
    let mut anc = Some(base);
    while let Some(a) = anc {
        if let Ok(rest) = path.strip_prefix(a) {
            return up.join(rest).to_string_lossy().into_owned();
        }
        up.push("..");
        anc = a
            .parent()
            .filter(|p| !p.as_os_str().is_empty() && *p != Path::new("/"));
    }
    path.to_string_lossy().into_owned()
}

/// Default path of a generated module next to the first target's lemma file.
fn default_generated_file(first_lean_file: &Path, stem: &str) -> PathBuf {
    first_lean_file
        .parent()
        .unwrap_or_else(|| Path::new(""))
        .join(format!("{stem}.lean"))
}

/// Is `s` a bare Lean module stem (one non-empty component of ASCII letters, digits and `_`)?
fn is_module_stem(s: &str) -> bool {
    !s.is_empty()
        && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !s.as_bytes()[0].is_ascii_digit()
}

/// Consistency of the `[placed]` ELF keys: `elf_bytes` / `elf_bytes_module` come together and
/// need `elf`; `elf_facts_module` needs a linked witness and is a bare module stem;
/// `split_check_module` needs a linked multi-block witness and is a dotted module name;
/// `chunked_check` needs a linked single-block witness;
/// `split_parse_module` needs a linked witness and is a dotted module name;
/// `noncomputable_code` needs a single-block library without a placement witness.
pub(crate) fn validate_placed_elf_keys(p: &PlacedTomlConfig) -> Result<()> {
    if p.noncomputable_code
        && (p.multi
            || p.elf.is_some()
            || p.linked
            || p.witness
            || p.placed_witness_out.is_some()
            || !p.extra_witnesses.is_empty())
    {
        bail!(
            "`noncomputable_code` is only supported for a single-block library without a \
             placement witness (no `multi`, `elf`, `linked`, `witness`, `placed_witness_out` or \
             `extra_witnesses`)"
        );
    }
    match (&p.elf_bytes, &p.elf_bytes_module) {
        (Some(_), None) | (None, Some(_)) => {
            bail!("`elf_bytes` and `elf_bytes_module` must be set together")
        }
        (Some(_), Some(_)) if p.elf.is_none() => {
            bail!("`elf_bytes` / `elf_bytes_module` require `elf`")
        }
        _ => {}
    }
    if let Some(m) = &p.elf_facts_module {
        if p.elf.is_none() || !p.linked {
            bail!("`elf_facts_module` requires `elf` and `linked = true`");
        }
        if !is_module_stem(m) {
            bail!("`elf_facts_module = {m:?}` must be a bare module stem (no `.` or `/`)");
        }
    }
    for x in &p.extra_witnesses {
        if let Some(m) = &x.elf_facts_module
            && !is_module_stem(m)
        {
            bail!(
                "`[[placed.extra_witnesses]] elf_facts_module = {m:?}` (module `{}`) must be a \
                 bare module stem (no `.` or `/`)",
                x.module
            );
        }
    }
    if let Some(m) = &p.split_check_module {
        if !p.multi || !p.linked {
            bail!("`split_check_module` requires `multi = true` and `linked = true`");
        }
        if !m.split('.').all(is_module_stem) {
            bail!("`split_check_module = {m:?}` must be a dotted Lean module name");
        }
    }
    if p.chunked_check
        && (p.multi || !((p.elf.is_some() && p.linked) || !p.extra_witnesses.is_empty()))
    {
        bail!(
            "`chunked_check` requires `multi = false` and a linked witness (`elf` with \
             `linked = true`, or `[[extra_witnesses]]`)"
        );
    }
    if let Some(m) = &p.split_parse_module {
        if p.elf.is_none() || !p.linked {
            bail!("`split_parse_module` requires `elf` and `linked = true`");
        }
        if !m.split('.').all(is_module_stem) {
            bail!("`split_parse_module = {m:?}` must be a dotted Lean module name");
        }
    }
    Ok(())
}

pub fn load_config(
    config_path: &Path,
    repo_root: &Path,
    out_dir: Option<&Path>,
) -> Result<ExportConfig> {
    let raw = fs::read_to_string(config_path).with_context(|| {
        format!(
            "failed to read translation config `{}`",
            config_path.display()
        )
    })?;
    let cfg: TranslationConfig = toml::from_str(&raw).with_context(|| {
        format!(
            "failed to parse translation config `{}`",
            config_path.display()
        )
    })?;

    let config_rel = relative_display(config_path, repo_root);
    let config_hash = sha256_hex(raw.as_bytes());
    let crate_dir = resolve_crate_dir(config_path, repo_root, cfg.crate_dir.as_deref());
    let target = cfg
        .target
        .clone()
        .unwrap_or_else(|| DEFAULT_TARGET.to_string());
    if !matches!(
        target.as_str(),
        "aarch64-unknown-linux-gnu" | "aarch64-unknown-linux-musl"
    ) {
        bail!(
            "`target` {target:?} in `{}` must be `\"aarch64-unknown-linux-gnu\"` or `\"aarch64-unknown-linux-musl\"`",
            config_path.display()
        );
    }
    let has_c_inputs = !cfg.native_objects.is_empty()
        || !cfg.c_sources.is_empty()
        || !cfg.c_objects.is_empty()
        || !cfg.c_archives.is_empty();
    let is_c_config = has_c_inputs
        || cfg.native_compiler.is_some()
        || cfg.build_script.is_some()
        || cfg.build_command.is_some()
        || !cfg.c_flags.is_empty();
    if !cfg.native_objects.is_empty() && cfg.native_compiler.is_none() {
        bail!(
            "`[native_compiler]` must be given exactly when there are `[[native_objects]]` (in `{}`)",
            config_path.display()
        );
    }
    if is_c_config && !has_c_inputs {
        bail!(
            "`[native_compiler]` / C configuration must specify at least one of `[[native_objects]]`, `c_sources`, `c_objects`, or `c_archives` (in `{}`)",
            config_path.display()
        );
    }
    let crates: Vec<String> = if is_c_config && cfg.crates.is_none() {
        if !cfg.rustflags.is_empty() || crate_dir.join("Cargo.toml").is_file() {
            bail!(
                "translation config `{}` cannot combine Rust crates (`Cargo.toml` / `rustflags`) with C `[[native_objects]]` / `c_sources` / `c_objects` / `c_archives` unless `crates = [...]` is explicitly listed",
                config_path.display()
            );
        }
        Vec::new()
    } else {
        let cs: Vec<String> = match &cfg.crates {
            Some(cs) => cs.iter().map(|c| c.replace('-', "_")).collect(),
            None => vec![infer_target_crate_name(&crate_dir)?],
        };
        if cs.is_empty() {
            bail!(
                "translation config `{}` defines no crates",
                config_path.display()
            );
        }
        cs
    };
    if let Some(dup) = crates.iter().duplicates().next() {
        bail!("duplicate crate `{dup}` in `{}`", config_path.display());
    }
    if let Some(f) = cfg.rustflags.iter().find(|f| {
        f.is_empty()
            || f
                .chars()
                .any(|c| c.is_ascii_whitespace() || c.is_ascii_control())
    }) {
        bail!(
            "`rustflags` entry {f:?} in `{}` must be one non-empty argument without whitespace",
            config_path.display()
        );
    }
    for s in &cfg.sysroot_objects {
        if s.krate.is_empty()
            || !s
                .krate
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            bail!(
                "sysroot object crate `{}` in `{}` is not a crate name",
                s.krate,
                config_path.display()
            );
        }
        if let Some(name) = &s.name
            && (name.is_empty()
                || name.starts_with(|c: char| c.is_ascii_digit())
                || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
        {
            bail!(
                "sysroot object name `{name}` in `{}` is not a C identifier",
                config_path.display()
            );
        }
        if s.roots.is_empty() {
            bail!(
                "sysroot object `{}` in `{}` has no roots",
                s.obj_name(),
                config_path.display()
            );
        }
        if let Some(dup) = s.roots.iter().duplicates().next() {
            bail!(
                "duplicate root `{dup}` of sysroot object `{}`",
                s.obj_name()
            );
        }
    }
    for n in &cfg.native_objects {
        if n.name.is_empty()
            || n.name.starts_with(|c: char| c.is_ascii_digit())
            || !n
                .name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            bail!(
                "native object name `{}` in `{}` is not a C identifier",
                n.name,
                config_path.display()
            );
        }
        if n.source.as_os_str().is_empty()
            || n.source.is_absolute()
            || n.include_dirs
                .iter()
                .any(|d| d.as_os_str().is_empty() || d.is_absolute())
        {
            bail!(
                "native object `{}`: `source` and `include_dirs` must be non-empty and relative to the crate directory",
                n.name
            );
        }
        if let Some(d) = n.defines.iter().find(|d| {
            let (name, val) = match d.split_once('=') {
                Some((name, val)) => (name, Some(val)),
                None => (d.as_str(), None),
            };
            name.is_empty()
                || name.starts_with(|c: char| c.is_ascii_digit())
                || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                || val.is_some_and(|v| {
                    v.chars()
                        .any(|c| c.is_ascii_whitespace() || c.is_ascii_control())
                })
        }) {
            bail!("native object `{}`: bad define `{d}`", n.name);
        }
        if n.c_flags.iter().any(|f| f.trim().is_empty()) {
            bail!("native object `{}`: empty flag in `c_flags`", n.name);
        }
        if let Some(bad) = n.c_flags.iter().find_map(|f| disallowed_opt_flag(f)) {
            bail!(
                "native object `{}`: flag `{bad}` in `c_flags` overrides `-O2` optimization level (only `-O2` or `-O3` allowed)",
                n.name
            );
        }
    }
    if cfg.c_flags.iter().any(|f| f.trim().is_empty()) {
        bail!("empty flag in `c_flags` in `{}`", config_path.display());
    }
    if let Some(bad) = cfg.c_flags.iter().find_map(|f| disallowed_opt_flag(f)) {
        bail!(
            "flag `{bad}` in `c_flags` in `{}` overrides `-O2` optimization level (only `-O2` or `-O3` allowed)",
            config_path.display()
        );
    }
    if cfg.build_script.is_some() && cfg.build_command.is_some() {
        bail!(
            "cannot specify both `build_script` and `build_command` in `{}`",
            config_path.display()
        );
    }
    if let Some(script) = &cfg.build_script
        && (script.as_os_str().is_empty() || script.is_absolute())
    {
        bail!(
            "`build_script` in `{}` must be non-empty and relative to the config directory",
            config_path.display()
        );
    }
    if let Some(cmd) = &cfg.build_command
        && (cmd.is_empty() || cmd.iter().any(|a| a.trim().is_empty()))
    {
        bail!(
            "`build_command` in `{}` must be a non-empty list of non-empty strings",
            config_path.display()
        );
    }
    let mut c_source_names = Vec::with_capacity(cfg.c_sources.len());
    for src in &cfg.c_sources {
        if src.as_os_str().is_empty() || src.is_absolute() {
            bail!(
                "`c_sources` entry `{}` in `{}` must be non-empty and relative to the config directory",
                src.display(),
                config_path.display()
            );
        }
        c_source_names.push(c_stem_ident(src)?);
    }
    let mut c_object_names = Vec::new();
    for obj in &cfg.c_objects {
        if obj.as_os_str().is_empty() || obj.is_absolute() {
            bail!(
                "`c_objects` entry `{}` in `{}` must be non-empty and relative to the config directory",
                obj.display(),
                config_path.display()
            );
        }
        if obj.extension().is_none_or(|e| e != "a") {
            c_object_names.push(c_stem_ident(obj)?);
        }
    }
    for arch in &cfg.c_archives {
        if arch.as_os_str().is_empty() || arch.is_absolute() {
            bail!(
                "`c_archives` entry `{}` in `{}` must be non-empty and relative to the config directory",
                arch.display(),
                config_path.display()
            );
        }
    }
    if let Some(dup) = crates
        .iter()
        .map(String::as_str)
        .chain(cfg.sysroot_objects.iter().map(|s| s.obj_name()))
        .chain(cfg.native_objects.iter().map(|n| n.name.as_str()))
        .chain(c_source_names.iter().map(String::as_str))
        .chain(c_object_names.iter().map(String::as_str))
        .duplicates()
        .next()
    {
        bail!(
            "duplicate object name `{dup}` in `{}`",
            config_path.display()
        );
    }
    let mut configured_externs = Vec::with_capacity(cfg.externs.len());
    let mut seen_externs = BTreeSet::new();
    for ext in cfg.externs {
        if ext.name.trim().is_empty() {
            bail!("empty `name` in `[[externs]]` in `{}`", config_path.display());
        }
        if !seen_externs.insert(ext.name.clone()) {
            bail!(
                "duplicate `[[externs]]` entry `{}` in `{}`",
                ext.name,
                config_path.display()
            );
        }
        let (kind, size, default_align) = match ext.kind {
            ExternKindConfig::Simple(ExternKindSimple::Func)
            | ExternKindConfig::FuncMap { .. } => (ExternKind::Func, Some(0), 1),
            ExternKindConfig::Simple(ExternKindSimple::Object) => {
                (ExternKind::Object, ext.size, 8)
            }
            ExternKindConfig::Simple(ExternKindSimple::Tls) => (ExternKind::Tls, ext.size, 8),
            ExternKindConfig::DataMap { data } => {
                (ExternKind::Object, Some(ext.size.unwrap_or(data)), 8)
            }
            ExternKindConfig::TlsMap { tls } => {
                (ExternKind::Tls, Some(ext.size.unwrap_or(tls)), 8)
            }
        };
        if matches!(kind, ExternKind::Object | ExternKind::Tls) && size == Some(0) {
            bail!(
                "`[[externs]]` entry `{}` in `{}`: data/tls externs cannot have size 0",
                ext.name,
                config_path.display()
            );
        }
        let align = ext.align.unwrap_or(default_align);
        if !align.is_power_of_two() || align > 4096 {
            bail!(
                "`[[externs]]` entry `{}` in `{}` has unsupported alignment {align}",
                ext.name,
                config_path.display()
            );
        }
        configured_externs.push(ConfiguredExtern {
            name: ext.name,
            kind,
            size,
            align,
        });
    }
    if cfg.obj_name.is_empty()
        || !cfg
            .obj_name
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic())
        || !cfg
            .obj_name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        bail!(
            "`obj_name` `{}` in `{}` is not a simple Lean identifier",
            cfg.obj_name,
            config_path.display()
        );
    }
    let default_out_base;
    let mut default_mod_prefix: Option<String> = None;
    let out_base = match out_dir {
        Some(d) => d,
        None => {
            let parts: Vec<&str> = config_rel.split('/').collect();
            if let [top @ ("CaseStudies" | "VerifiedLibraries"), lib, ..] = parts.as_slice()
                && !lib.starts_with('_')
            {
                default_out_base = repo_root.join(top).join(lib);
                default_mod_prefix = Some(format!("{top}.{lib}"));
                default_out_base.as_path()
            } else {
                repo_root
            }
        }
    };
    let resolve_mod = |rel: &Path| -> String {
        let m = lean_module_of(rel);
        if let Some(pfx) = &default_mod_prefix
            && !m.starts_with(&format!("{pfx}."))
        {
            format!("{pfx}.{m}")
        } else {
            m
        }
    };
    let namespace_prefix = cfg
        .namespace_prefix
        .clone()
        .or_else(|| infer_namespace_prefix_from_out_dir(out_dir))
        .unwrap_or_else(|| "Examples".to_string());

    let placed_only = cfg.placed.as_ref().is_some_and(|p| p.placed_only);
    let stem = upper_camel(&cfg.obj_name);
    let anchor_lean_file = match cfg.targets.first() {
        Some(first) => first.lean_file.clone(),
        None if placed_only || cfg.obj_file.is_some() => cfg
            .obj_file
            .clone()
            .unwrap_or_else(|| PathBuf::from(format!("Examples/Generated/{stem}Obj.lean"))),
        None => {
            bail!(
                "translation config `{}` defines no targets",
                config_path.display()
            );
        }
    };
    let obj_rel = cfg
        .obj_file
        .clone()
        .unwrap_or_else(|| default_generated_file(&anchor_lean_file, &format!("{stem}Obj")));
    let code_rel = cfg
        .code_file
        .clone()
        .unwrap_or_else(|| default_generated_file(&anchor_lean_file, &format!("{stem}Code")));
    let (registry_facts_file, registry_facts_module) =
        if cfg.registry_facts || cfg.registry_facts_file.is_some() {
            let reg_rel = cfg.registry_facts_file.clone().unwrap_or_else(|| {
                default_generated_file(&anchor_lean_file, &format!("{stem}RegistryFacts"))
            });
            (
                Some(resolve_target_lean_file(out_base, &reg_rel)),
                Some(resolve_mod(&reg_rel)),
            )
        } else {
            (None, None)
        };

    if let Some(p) = &cfg.placed
        && p.placed_shards.is_some_and(|n| n > 1)
        && !p.multi
    {
        bail!(
            "`[placed] placed_shards` requires `multi = true` in `{}`",
            config_path.display()
        );
    }
    if let Some(p) = &cfg.placed
        && !p.extern_boundary.is_empty()
        && !p.multi
    {
        bail!(
            "`[placed] extern_boundary` requires `multi = true` in `{}`",
            config_path.display()
        );
    }
    if let Some(p) = &cfg.placed {
        validate_placed_elf_keys(p)
            .with_context(|| format!("invalid `[placed]` in `{}`", config_path.display()))?;
    }
    let placed = cfg.placed.as_ref().map(|p| {
        let config_dir = config_path.parent().unwrap_or_else(|| Path::new("."));
        let lib_rel = default_generated_file(&anchor_lean_file, &format!("{stem}PlacedObj"));
        let elf_rel = default_generated_file(&anchor_lean_file, &format!("{stem}ElfObj"));
        let wit_rel = p
            .placed_witness_out
            .clone()
            .unwrap_or_else(|| default_generated_file(&anchor_lean_file, &format!("{stem}PlacedWitness")));
        let emit_placeable_witness =
            p.witness || p.placed_witness_out.is_some() || (p.elf.is_none() && p.linked);
        PlacedConfig {
            exports: p.exports.clone(),
            elf: p.elf.as_ref().map(|e| normalize_path(&config_dir.join(e))),
            elf_sha256: p.elf_sha256.clone(),
            lib_file: resolve_target_lean_file(out_base, &lib_rel),
            lib_module: resolve_mod(&lib_rel),
            elf_file: resolve_target_lean_file(out_base, &elf_rel),
            elf_module: resolve_mod(&elf_rel),
            elf_bytes_override: p.elf_bytes.clone().zip(p.elf_bytes_module.clone()),
            elf_facts_module: p.elf_facts_module.clone(),
            witness_file: resolve_target_lean_file(out_base, &wit_rel),
            witness_module: resolve_mod(&wit_rel),
            linked: p.linked,
            emit_placeable_witness,
            multi: p.multi,
            noncomputable_code: p.noncomputable_code,
            placed_shards: p.placed_shards.unwrap_or(1).max(1),
            extern_boundary: p.extern_boundary.clone(),
            placed_only: p.placed_only,
            emit_extracted_obj: p.emit_extracted_obj,
            extra_witnesses: p
                .extra_witnesses
                .iter()
                .map(|x| {
                    let rel = default_generated_file(&anchor_lean_file, &x.module);
                    ExtraWitnessConfig {
                        prefix: x.prefix.clone(),
                        namespace: x.namespace.clone(),
                        elf: normalize_path(&config_dir.join(&x.elf)),
                        elf_sha256: x.elf_sha256.clone(),
                        elf_bytes: x.elf_bytes.clone(),
                        elf_bytes_module: x.elf_bytes_module.clone(),
                        elf_facts_module: x.elf_facts_module.clone(),
                        witness_file: resolve_target_lean_file(out_base, &rel),
                        witness_module: resolve_mod(&rel),
                    }
                })
                .collect(),
            split_check_module: p.split_check_module.clone(),
            chunked_check: p.chunked_check,
            split_parse_module: p.split_parse_module.clone(),
        }
    });

    let mut targets = Vec::new();
    let mut seen_names = BTreeSet::new();
    for tgt in cfg.targets {
        if !seen_names.insert(tgt.name.clone()) {
            bail!(
                "duplicate target name `{}` in `{}`",
                tgt.name,
                config_path.display()
            );
        }
        targets.push(ExportTarget {
            name: tgt.name,
            lean_file: resolve_target_lean_file(out_base, &tgt.lean_file),
            lean_module: resolve_mod(&tgt.lean_file),
            sub_namespace: tgt.sub_namespace,
            prog_name: tgt.prog_name,
            title: tgt.title,
            hashed_inputs: merge_hashed_inputs(&cfg.hashed_inputs, &tgt.hashed_inputs),
            lemma_allowlist: tgt.lemma_allowlist,
            lemma_shards: tgt.lemma_shards.unwrap_or(1).max(1),
            explicit_lemma_shards: tgt.lemma_shards.map(|n| n.max(1)),
        });
    }

    let hashed_inputs = targets.iter().fold(cfg.hashed_inputs.clone(), |acc, t| {
        merge_hashed_inputs(&acc, &t.hashed_inputs)
    });
    let env_perturb = env::var(PERTURB_LAYOUT_ENV).ok();
    let perturb_layout_bytes = resolve_perturb_layout_bytes(None, env_perturb.as_deref())?;
    Ok(ExportConfig {
        config_rel,
        config_hash,
        crate_dir,
        target,
        crates,
        obj_file: resolve_target_lean_file(out_base, &obj_rel),
        obj_module: resolve_mod(&obj_rel),
        code_file: resolve_target_lean_file(out_base, &code_rel),
        code_module: resolve_mod(&code_rel),
        registry_facts_file,
        registry_facts_module,
        layout_generic_relocs: cfg.layout_generic_relocs,
        emit_symbol_unique_lemmas: cfg.emit_symbol_unique_lemmas,
        slice_stubs_in_code: cfg.slice_stubs_in_code,
        page_separate_data: cfg.page_separate_data,
        legacy_linked_image: cfg.legacy_linked_image,
        perturb_layout_bytes,
        title: cfg.title.unwrap_or_else(|| {
            targets
                .first()
                .map(|t| t.title.clone())
                .unwrap_or_else(|| cfg.obj_name.clone())
        }),
        obj_name: cfg.obj_name,
        namespace_prefix,
        license_header: cfg.license_header,
        upstream: cfg.upstream,
        hashed_inputs,
        rustflags: cfg.rustflags,
        sysroot_objects: cfg.sysroot_objects,
        native_compiler: cfg.native_compiler,
        native_objects: cfg.native_objects,
        c_sources: cfg.c_sources,
        c_objects: cfg.c_objects,
        c_archives: cfg.c_archives,
        c_flags: cfg.c_flags,
        build_script: cfg.build_script,
        build_command: cfg.build_command,
        externs: configured_externs,
        targets,
        placed,
    })
}

pub fn load_configs(
    config_paths: &[PathBuf],
    repo_root: &Path,
    out_dir: Option<&Path>,
) -> Result<Vec<ExportConfig>> {
    let mut configs: Vec<ExportConfig> = Vec::new();
    let mut seen_names: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut seen_files: BTreeMap<PathBuf, PathBuf> = BTreeMap::new();
    let mut seen_objs: BTreeMap<String, PathBuf> = BTreeMap::new();
    for config_path in config_paths {
        let loaded = load_config(config_path, repo_root, out_dir)?;
        if let Some(prev) = seen_objs.insert(loaded.obj_name.clone(), config_path.clone()) {
            bail!(
                "duplicate `obj_name` `{}` across `{}` and `{}`",
                loaded.obj_name,
                prev.display(),
                config_path.display()
            );
        }
        for tgt in &loaded.targets {
            if let Some(prev) = seen_names.insert(tgt.name.clone(), config_path.clone()) {
                bail!(
                    "duplicate target name `{}` across `{}` and `{}`",
                    tgt.name,
                    prev.display(),
                    config_path.display()
                );
            }
        }
        let mut files = Vec::new();
        if !loaded.placed.as_ref().is_some_and(|p| p.placed_only) {
            files.push(loaded.obj_file.clone());
            files.push(loaded.code_file.clone());
            files.push(loaded.code_bin_file());
            files.push(loaded.data_bin_file());
        }
        if let Some(p) = &loaded.placed {
            files.push(p.lib_file.clone());
            files.extend(p.shard_files());
            if p.emit_extracted_obj {
                let (lean_path, bin_path) =
                    crate::trusted_extractor::extracted_obj_files(&loaded.obj_meta());
                files.push(lean_path);
                files.push(bin_path);
            }
        }
        files.extend(loaded.targets.iter().map(|t| t.lean_file.clone()));
        for file in files {
            if let Some(prev) = seen_files.insert(file.clone(), config_path.clone()) {
                bail!(
                    "output file `{}` is generated by both `{}` and `{}`",
                    file.display(),
                    prev.display(),
                    config_path.display()
                );
            }
        }
        configs.push(loaded);
    }
    Ok(configs)
}

/// Keep only the configurations with a target named in `only` (all if `only` is empty).
pub fn select_configs(configs: Vec<ExportConfig>, only: &[String]) -> Result<Vec<ExportConfig>> {
    if only.is_empty() {
        return Ok(configs);
    }
    let known: BTreeSet<&str> = configs
        .iter()
        .flat_map(|c| c.targets.iter().map(|t| t.name.as_str()))
        .collect();
    if let Some(missing) = only.iter().find(|n| !known.contains(n.as_str())) {
        bail!(
            "unknown target `{missing}` (known: {})",
            known.iter().join(", ")
        );
    }
    Ok(configs
        .into_iter()
        .filter(|c| c.targets.iter().any(|t| only.contains(&t.name)))
        .collect())
}

pub fn apply_overrides(
    configs: &mut [ExportConfig],
    output: Option<&Path>,
    namespace_prefix: Option<&str>,
    sub_namespace: Option<&str>,
) -> Result<()> {
    if let Some(out_file) = output {
        let n_targets: usize = configs.iter().map(|c| c.targets.len()).sum();
        if n_targets != 1 {
            bail!(
                "`--output` can only be used with a single target (selected {n_targets}); \
                 use `--out-dir <DIR>` for multiple targets"
            );
        }
        let cfg = &mut configs[0];
        let dir = out_file.parent().unwrap_or_else(|| Path::new(""));
        let stem = upper_camel(&cfg.obj_name);
        cfg.obj_file = dir.join(format!("{stem}Obj.lean"));
        cfg.code_file = dir.join(format!("{stem}Code.lean"));
        if cfg.registry_facts_file.is_some() {
            cfg.registry_facts_file = Some(dir.join(format!("{stem}RegistryFacts.lean")));
        }
        if let Some(p) = &mut cfg.placed {
            p.lib_file = dir.join(format!("{stem}PlacedObj.lean"));
            p.elf_file = dir.join(format!("{stem}ElfObj.lean"));
            p.witness_file = dir.join(format!("{stem}PlacedWitness.lean"));
            for x in &mut p.extra_witnesses {
                let name = x.witness_module.rsplit('.').next().unwrap_or_default();
                x.witness_file = dir.join(format!("{name}.lean"));
            }
        }
        cfg.targets[0].lean_file = out_file.to_path_buf();
    }
    if let Some(prefix) = namespace_prefix {
        for cfg in configs.iter_mut() {
            cfg.namespace_prefix = prefix.to_string();
        }
    }
    if let Some(sub) = sub_namespace {
        let sub_opt = (!sub.trim().is_empty()).then(|| sub.trim().to_string());
        for tgt in configs.iter_mut().flat_map(|c| c.targets.iter_mut()) {
            tgt.sub_namespace = sub_opt.clone();
        }
    }
    Ok(())
}

pub fn apply_module_prefix_override(configs: &mut [ExportConfig], module_prefix: Option<&str>) {
    let Some(mp) = module_prefix.map(str::trim).filter(|s| !s.is_empty()) else {
        return;
    };
    let mp = mp.trim_end_matches('.');
    for cfg in configs.iter_mut() {
        let stem = upper_camel(&cfg.obj_name);
        cfg.obj_module = format!("{mp}.{stem}Obj");
        cfg.code_module = format!("{mp}.{stem}Code");
        if cfg.registry_facts_module.is_some() {
            cfg.registry_facts_module = Some(format!("{mp}.{stem}RegistryFacts"));
        }
        if let Some(p) = &mut cfg.placed {
            p.lib_module = format!("{mp}.{stem}PlacedObj");
            p.elf_module = format!("{mp}.{stem}ElfObj");
            p.witness_module = format!("{mp}.{stem}PlacedWitness");
            for x in &mut p.extra_witnesses {
                let name = x
                    .witness_module
                    .rsplit('.')
                    .next()
                    .unwrap_or_default()
                    .to_string();
                x.witness_module = format!("{mp}.{name}");
            }
        }
        for tgt in &mut cfg.targets {
            let leaf = tgt
                .lean_module
                .rsplit('.')
                .next()
                .unwrap_or(&tgt.lean_module);
            tgt.lean_module = format!("{mp}.{leaf}");
        }
    }
}

pub fn apply_perturb_layout_override(
    configs: &mut [ExportConfig],
    perturb_layout: Option<u64>,
) -> Result<()> {
    let Some(bytes) = perturb_layout else {
        return Ok(());
    };
    validate_perturb_layout_bytes(bytes, "`--perturb-layout`")?;
    for cfg in configs.iter_mut() {
        cfg.perturb_layout_bytes = bytes;
    }
    Ok(())
}

pub fn default_config_paths(repo_root: &Path) -> Vec<PathBuf> {
    if let Ok(cwd) = env::current_dir() {
        let local = normalize_path(&cwd.join("translation.toml"));
        if local.is_file() {
            return vec![local];
        }
    }
    DEFAULT_CONFIG_REL_PATHS
        .iter()
        .map(|rel| normalize_path(&repo_root.join(rel)))
        .collect()
}
