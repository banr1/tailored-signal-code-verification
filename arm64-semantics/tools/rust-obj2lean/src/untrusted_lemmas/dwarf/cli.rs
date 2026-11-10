// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `layout` Subcommand (`untrusted_lemmas::dwarf::cli`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (prints hints for spec authors and auditors; nothing here
//!   reaches a Lean definition).
//! - **`rust-obj2lean layout <INPUT> [FILTER] [--lean]`**: struct/union layouts from DWARF, where
//!   `INPUT` is a relocatable `.o` with DWARF, a `*Index.json` (its `dwarf_types`), or a
//!   `translation.toml` (built like `export`, plus the `-g` companion compile). Prints a table
//!   (byte offset, size, bit range, type) and ready-to-paste `abbrev off<Field> : Nat := 0x..`
//!   definitions (nested aggregates flattened as `offIn_B`).
//!
//! # Key Types & Functions
//! - [`run_layout_cli`] (dispatched from `cli_main`).
//! - [`render_layout_table`], [`render_layout_lean`].
//!
//! # When to Read This File
//! - Read this file when changing the output of `layout`.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result, bail};
use clap::Parser;

use super::companion::{ImageDwarf, image_dwarf};
use super::{DwarfTypeLayout, read_elf_dwarf};
use crate::untrusted_driver::{
    Toolchain, extract, load_configs, resolve_cli_existing_or_repo_path,
};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("CARGO_MANIFEST_DIR must be at <repo>/tools/rust-obj2lean")
        .to_path_buf()
}

/// Load one `translation.toml`, build its objects and compute their DWARF.
fn config_dwarf(config: &Path) -> Result<ImageDwarf> {
    let root = repo_root();
    let path = resolve_cli_existing_or_repo_path(&root, config);
    let cfg = load_configs(&[path], &root, None)?
        .into_iter()
        .next()
        .context("no config loaded")?;
    let mut tc = Toolchain::new(root)?;
    let ex =
        extract(&cfg, &mut tc).with_context(|| format!("cannot build `{}`", cfg.config_rel))?;
    let dw = image_dwarf(&cfg, &ex.objects);
    for w in &dw.warnings {
        eprintln!("warning: DWARF: {w}");
    }
    Ok(dw)
}

#[derive(Parser, Debug)]
#[command(
    name = "rust-obj2lean layout",
    about = "Print DWARF struct/union layouts",
    after_help = "Examples:\n  tools/target/release/rust-obj2lean layout Implementation/my_lib/translation.toml\n  tools/target/release/rust-obj2lean layout Examples/Generated/MyLibIndex.json Widget --lean"
)]
struct LayoutArgs {
    /// A relocatable `.o` with DWARF, a `*Index.json`, or a `translation.toml`.
    input: PathBuf,
    /// Only types whose name, tag or typedef contains this (exact matches win).
    filter: Option<String>,
    /// Print only the Lean `abbrev` definitions.
    #[arg(long)]
    lean: bool,
}

fn load_layouts(input: &Path) -> Result<BTreeMap<String, DwarfTypeLayout>> {
    let ext = input.extension().and_then(|e| e.to_str()).unwrap_or("");
    match ext {
        "json" => {
            let text = std::fs::read_to_string(input)?;
            let idx: crate::untrusted_lemmas::index::TargetSymbolIndex = serde_json::from_str(&text)
                .with_context(|| format!("{} is not a *Index.json", input.display()))?;
            Ok(idx
                .dwarf_types
                .into_iter()
                .map(|l| (l.name.clone(), l))
                .collect())
        }
        "toml" => Ok(config_dwarf(input)?.layouts),
        _ => Ok(read_elf_dwarf(&std::fs::read(input)?)?.layouts),
    }
}

/// Layouts selected by `filter` (all if `None`; exact name/tag/typedef matches beat substrings).
pub fn select_layouts<'a>(
    layouts: &'a BTreeMap<String, DwarfTypeLayout>,
    filter: Option<&str>,
) -> Vec<&'a DwarfTypeLayout> {
    let Some(f) = filter else {
        return layouts.values().collect();
    };
    let names = |l: &'a DwarfTypeLayout| {
        let tag = l.name.split_once(' ').map_or(l.name.as_str(), |(_, t)| t);
        std::iter::once(l.name.as_str())
            .chain([tag])
            .chain(l.typedefs.iter().map(String::as_str))
    };
    let exact: Vec<_> = layouts
        .values()
        .filter(|l| names(l).any(|n| n == f))
        .collect();
    if !exact.is_empty() {
        return exact;
    }
    layouts
        .values()
        .filter(|l| names(l).any(|n| n.contains(f)))
        .collect()
}

/// Human-readable layout table of `l`.
pub fn render_layout_table(l: &DwarfTypeLayout) -> String {
    let mut s = String::new();
    let td = if l.typedefs.is_empty() {
        String::new()
    } else {
        format!(" (typedef {})", l.typedefs.join(", "))
    };
    let _ = writeln!(
        s,
        "{}{td}: size {:#x} ({}), align {}  [{}:{}]",
        l.name, l.byte_size, l.byte_size, l.alignment, l.decl_file, l.decl_line
    );
    for m in &l.members {
        let bits = match (m.bit_offset, m.bit_size) {
            (Some(o), Some(n)) => format!(" bits {o}..{}", o + n),
            _ => String::new(),
        };
        let name = if m.name.is_empty() { "<anon>" } else { &m.name };
        let _ = writeln!(
            s,
            "  +{:#06x} {:>4}  {name}{bits} : {}",
            m.byte_offset, m.byte_size, m.c_type
        );
    }
    s
}

fn lean_ident(s: &str) -> String {
    let mut out: String = s
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if let Some(c) = out.get(0..1) {
        let up = c.to_ascii_uppercase();
        out.replace_range(0..1, &up);
    }
    out
}

fn lean_members(
    layouts: &BTreeMap<String, DwarfTypeLayout>,
    l: &DwarfTypeLayout,
    base: u64,
    prefix: &str,
    depth: usize,
    out: &mut String,
) {
    for m in &l.members {
        let off = base + m.byte_offset;
        // Anonymous members are accessed through the parent: flatten without a name component.
        let name = if m.name.is_empty() {
            prefix.to_string()
        } else if prefix.is_empty() {
            lean_ident(&m.name)
        } else {
            format!("{prefix}_{}", lean_ident(&m.name))
        };
        if !m.name.is_empty() {
            let bits = match (m.bit_offset, m.bit_size) {
                (Some(o), Some(n)) => format!(", bits {o}..{} of the containing bytes", o + n),
                _ => String::new(),
            };
            let _ = writeln!(
                out,
                "abbrev off{name} : Nat := {off:#x}  -- {} ({} B{bits})",
                m.c_type, m.byte_size
            );
        }
        if let Some(agg) = m.aggregate.as_ref().and_then(|a| layouts.get(a))
            && depth < 4
        {
            lean_members(layouts, agg, off, &name, depth + 1, out);
        }
    }
}

/// Lean offset definitions of `l` in `namespace <Type>Layout`.
pub fn render_layout_lean(
    layouts: &BTreeMap<String, DwarfTypeLayout>,
    l: &DwarfTypeLayout,
) -> String {
    let tag = l.typedefs.first().cloned().unwrap_or_else(|| {
        l.name
            .split_once(' ')
            .map_or(l.name.clone(), |(_, t)| t.to_string())
    });
    let ns = format!("{}Layout", lean_ident(&tag));
    let mut s = format!(
        "-- DWARF layout of `{}` ({}:{})\nnamespace {ns}\n",
        l.name, l.decl_file, l.decl_line
    );
    let _ = writeln!(s, "abbrev size : Nat := {:#x}", l.byte_size);
    lean_members(layouts, l, 0, "", 0, &mut s);
    let _ = writeln!(s, "end {ns}");
    s
}

/// `rust-obj2lean layout ...`.
pub fn run_layout_cli(args: &[String]) -> ExitCode {
    let a = match LayoutArgs::try_parse_from(
        std::iter::once("layout".to_string()).chain(args.iter().cloned()),
    ) {
        Ok(a) => a,
        Err(e) => {
            let _ = e.print();
            return if e.use_stderr() {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            };
        }
    };
    let res = (|| -> Result<()> {
        let layouts = load_layouts(&a.input)?;
        let sel = select_layouts(&layouts, a.filter.as_deref());
        if sel.is_empty() {
            bail!(
                "no DWARF layout matches (input has {} layouts)",
                layouts.len()
            );
        }
        for l in sel {
            if !a.lean {
                println!("{}", render_layout_table(l));
            }
            println!("{}", render_layout_lean(&layouts, l));
        }
        Ok(())
    })();
    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
    }
}
