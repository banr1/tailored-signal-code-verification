// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Per-ELF facts modules (`[OUTSIDE TCB]`).
//!
//! Every linked placement witness needs the parsed ELF (`elf_image%`), its parse theorem against
//! the pinned bytes constant (`ElfImage.parse <bytes> = .ok <img>`, an O(ELF) `rfl_kernel`) and
//! the ELF's symbol table in interned form. These depend only on the ELF, so they are emitted once
//! per bytes constant in a `Proof`-role module `<Base>ElfFacts.lean` next to
//! `<ObjName>PlacedObj.lean`, and each witness imports it:
//!
//! - [`plan`] groups the linked witnesses of one config by bytes constant; each group emits one
//!   facts module, named after the constant ([`facts_stem`]).
//! - A witness may instead import a facts module emitted by another config
//!   (`elf_facts_module`). [`plan`] fails closed unless that module exists and its
//!   [`MARKER`] line records the same bytes constant, defining module and SHA-256. The witness
//!   also restates every fact it re-exports against its own bytes constant, checked at reducible
//!   transparency, so a facts module about another constant fails to elaborate without
//!   unfolding any ELF bytes.
//!
//! A facts module imports the module defining the bytes constant and never defines or re-exports
//! the constant itself; `Spec`-role modules never import it.
//!
//! With `[placed] split_parse_module`, the parse theorem is instead composed (by that module's
//! `parse_of_parts`) from separate top-level kernel facts: suffix constants of the bytes at the
//! far offsets the symbol-table parse seeks to ([`parse_layout`]), each proved equal to a
//! `List.drop` of the bytes, the file length, the ELF header, the program headers, the symbol
//! table and well-formedness. The kernel's peak memory is then that of the largest fact rather
//! than of the whole parse, which multi-megabyte ELFs need.

use std::path::{Path, PathBuf};

use anyhow::{Result, bail};

use crate::trusted_common::lean_string_lit;
use crate::untrusted_driver::config::PlacedConfig;

use super::emit::{doc_safe, header, relative_path};

/// Prefix of the line recording what a facts module is about (parsed by [`read_marker`]).
pub const MARKER: &str = "-- rust-obj2lean elf-facts:";

/// The fully qualified names of the declarations of one facts module, and the module itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElfFacts {
    /// Lean module name of the facts module.
    pub module: String,
    /// `<ns>.<base>Image`, `<ns>.<base>Image_parse`, `<ns>.<base>ImageSyms`,
    /// `<ns>.<base>ImageSymChars` and `<ns>.<base>ImageSyms_eq`.
    pub image: String,
    pub parse: String,
    pub syms: String,
    pub sym_chars: String,
    pub syms_eq: String,
}

impl ElfFacts {
    /// The names of the facts module `module` about bytes constant `elf_bytes`, in namespace `ns`.
    pub fn new(module: &str, ns: &str, elf_bytes: &str) -> Self {
        let base = bytes_base(elf_bytes);
        let q = |s: &str| format!("{ns}.{base}{s}");
        ElfFacts {
            module: module.to_string(),
            image: q("Image"),
            parse: q("Image_parse"),
            syms: q("ImageSyms"),
            sym_chars: q("ImageSymChars"),
            syms_eq: q("ImageSyms_eq"),
        }
    }
}

/// One linked witness's ELF: which bytes constant it is about and where its facts come from.
#[derive(Clone, Debug)]
pub struct ElfUse {
    pub elf: PathBuf,
    pub elf_sha256: String,
    pub elf_bytes: String,
    pub elf_bytes_module: String,
    /// Namespace of the witness (the facts module emitted for its group uses the first one).
    pub namespace: String,
    /// `elf_facts_module`: import this existing facts module instead of emitting one.
    pub facts_module: Option<String>,
}

/// A facts module to emit.
#[derive(Clone, Debug)]
pub struct FactsModule {
    pub file: PathBuf,
    pub facts: ElfFacts,
    pub namespace: String,
    pub elf: PathBuf,
    pub elf_sha256: String,
    pub elf_bytes: String,
    pub elf_bytes_module: String,
    /// `[placed] split_parse_module` and the ELF's [`ParseLayout`]: prove the parse theorem
    /// from separate kernel facts; `None` keeps the single `rfl_kernel`.
    pub split_parse: Option<(String, ParseLayout)>,
}

/// Where the split parse of an ELF seeks: its length and the ascending, distinct far offsets
/// (section headers, first global symbol, string table) the symbol-table parse drops to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseLayout {
    pub len: usize,
    /// Ascending, distinct, each in `1..len`; nonempty (the last one anchors the length).
    pub tails: Vec<usize>,
}

fn rd(b: &[u8], off: usize, n: usize) -> Result<u64> {
    let Some(s) = off.checked_add(n).and_then(|e| b.get(off..e)) else {
        bail!("ELF read of {n} bytes at offset {off} is out of bounds");
    };
    Ok(s.iter().rev().fold(0u64, |a, &x| (a << 8) | u64::from(x)))
}

fn rd_usize(b: &[u8], off: usize, n: usize) -> Result<usize> {
    Ok(usize::try_from(rd(b, off, n)?)?)
}

/// The [`ParseLayout`] of the ELF64 little-endian file `b`, following the section-header and
/// symbol-table offsets the way `ElfImage.parse` does (the first `SHT_SYMTAB` section and its
/// `sh_link` string table). Fails on files without section headers or with out-of-range offsets.
pub fn parse_layout(b: &[u8]) -> Result<ParseLayout> {
    if b.len() < 64 || b[..4] != *b"\x7fELF" || b[4] != 2 || b[5] != 1 {
        bail!("split parse: not an ELF64 little-endian file");
    }
    let (sh_off, sh_entsize, sh_num) = (
        rd_usize(b, 40, 8)?,
        rd_usize(b, 58, 2)?,
        rd_usize(b, 60, 2)?,
    );
    if sh_num == 0 || sh_entsize != 64 {
        bail!(
            "split parse: needs section headers of 64 bytes (e_shnum={sh_num}, e_shentsize={sh_entsize})"
        );
    }
    let sh = |i: usize| sh_off + 64 * i;
    let mut tails = vec![sh_off];
    if let Some(i) = (0..sh_num).find(|&i| rd(b, sh(i) + 4, 4).ok() == Some(2)) {
        let (off, info, link) = (
            rd_usize(b, sh(i) + 24, 8)?,
            rd_usize(b, sh(i) + 44, 4)?,
            rd_usize(b, sh(i) + 40, 4)?,
        );
        if link >= sh_num {
            bail!("split parse: SHT_SYMTAB sh_link {link} out of bounds");
        }
        tails.push(off + 24 * info);
        tails.push(rd_usize(b, sh(link) + 24, 8)?);
    }
    tails.sort_unstable();
    tails.dedup();
    if let Some(&k) = tails.iter().find(|&&k| k == 0 || k >= b.len()) {
        bail!(
            "split parse: far offset {k} is not inside the {}-byte file",
            b.len()
        );
    }
    Ok(ParseLayout {
        len: b.len(),
        tails,
    })
}

/// The facts of each use (in order) and the facts modules to emit.
#[derive(Clone, Debug)]
pub struct FactsPlan {
    pub per_use: Vec<ElfFacts>,
    pub emit: Vec<FactsModule>,
}

/// Last component of `elf_bytes` without a trailing `Bytes` (`myLibElfBytes` -> `myLibElf`).
pub fn bytes_base(elf_bytes: &str) -> String {
    let last = elf_bytes.rsplit('.').next().unwrap_or(elf_bytes);
    match last.strip_suffix("Bytes") {
        Some(b) if !b.is_empty() => b.to_string(),
        _ => last.to_string(),
    }
}

/// Module stem of the facts module about `elf_bytes`: `<Base>ElfFacts` (`<Base>Facts` when the
/// base already ends in `Elf`), e.g. `myLibElfBytes` -> `MyLibElfFacts`, `altBytes` ->
/// `AltElfFacts`.
pub fn facts_stem(elf_bytes: &str) -> String {
    let base = bytes_base(elf_bytes);
    let mut cs = base.chars();
    let upper: String = match cs.next() {
        Some(c) => c.to_uppercase().chain(cs).collect(),
        None => String::new(),
    };
    if upper.ends_with("Elf") {
        format!("{upper}Facts")
    } else {
        format!("{upper}ElfFacts")
    }
}

/// The marker line of a facts module.
pub fn marker_line(elf_bytes: &str, elf_bytes_module: &str, sha: &str, ns: &str) -> String {
    format!("{MARKER} bytes={elf_bytes} module={elf_bytes_module} sha256={sha} namespace={ns}")
}

/// The `(bytes, module, sha256, namespace)` recorded by the marker line of facts module text.
pub fn read_marker(text: &str) -> Option<(String, String, String, String)> {
    let line = text.lines().find_map(|l| l.strip_prefix(MARKER))?;
    let get = |key: &str| {
        line.split_whitespace()
            .find_map(|kv| kv.strip_prefix(key)?.strip_prefix('='))
            .map(str::to_string)
    };
    Some((
        get("bytes")?,
        get("module")?,
        get("sha256")?,
        get("namespace")?,
    ))
}

/// The facts of `u` from the existing facts module with stem `stem` (file `file`, module
/// `module`): fails closed unless the file exists and records `u`'s bytes constant, defining
/// module and SHA-256.
fn resolve_existing(u: &ElfUse, stem: &str, file: &Path, module: &str) -> Result<ElfFacts> {
    let Ok(text) = std::fs::read_to_string(file) else {
        bail!(
            "`elf_facts_module = {stem:?}`: {} does not exist; generate the config that emits it \
             first (it must be in the same generated directory)",
            file.display()
        );
    };
    let Some((bytes, bytes_module, sha, ns)) = read_marker(&text) else {
        bail!(
            "`elf_facts_module = {stem:?}`: {} is not a facts module (no `{MARKER}` line)",
            file.display()
        );
    };
    if bytes != u.elf_bytes || bytes_module != u.elf_bytes_module {
        bail!(
            "`elf_facts_module = {stem:?}` is about `{bytes}` (module `{bytes_module}`), not \
             `{}` (module `{}`)",
            u.elf_bytes,
            u.elf_bytes_module
        );
    }
    if !sha.eq_ignore_ascii_case(&u.elf_sha256) {
        bail!(
            "`elf_facts_module = {stem:?}` records SHA-256 {sha}, but the witness pins {}",
            u.elf_sha256
        );
    }
    Ok(ElfFacts::new(module, &ns, &u.elf_bytes))
}

/// Group `uses` (the linked witnesses of `p`, in emission order) by bytes constant: each use
/// without `facts_module` shares the facts module emitted for its constant; each use with one
/// imports that existing module ([`resolve_existing`]).
pub fn plan(p: &PlacedConfig, uses: &[ElfUse]) -> Result<FactsPlan> {
    let mut emit: Vec<FactsModule> = Vec::new();
    for u in uses.iter().filter(|u| u.facts_module.is_none()) {
        if let Some(g) = emit.iter().find(|g| g.elf_bytes == u.elf_bytes) {
            if g.elf_bytes_module != u.elf_bytes_module
                || !g.elf_sha256.eq_ignore_ascii_case(&u.elf_sha256)
            {
                bail!(
                    "two witnesses name ELF bytes `{}` with different modules or SHA-256 pins \
                     (`{}` / {} and `{}` / {})",
                    u.elf_bytes,
                    g.elf_bytes_module,
                    g.elf_sha256,
                    u.elf_bytes_module,
                    u.elf_sha256
                );
            }
            continue;
        }
        let stem = facts_stem(&u.elf_bytes);
        if let Some(g) = emit.iter().find(|g| g.file == p.sibling_file(&stem)) {
            bail!(
                "ELF bytes `{}` and `{}` both map to facts module `{stem}`; rename one constant",
                g.elf_bytes,
                u.elf_bytes
            );
        }
        let module = p.sibling_module(&stem);
        let split_parse = match &p.split_parse_module {
            None => None,
            Some(m) => {
                let bytes = std::fs::read(&u.elf)
                    .map_err(|e| anyhow::anyhow!("reading {}: {e}", u.elf.display()))?;
                let layout = parse_layout(&bytes)
                    .map_err(|e| anyhow::anyhow!("{}: {e}", u.elf.display()))?;
                Some((m.clone(), layout))
            }
        };
        emit.push(FactsModule {
            file: p.sibling_file(&stem),
            facts: ElfFacts::new(&module, &u.namespace, &u.elf_bytes),
            namespace: u.namespace.clone(),
            elf: u.elf.clone(),
            elf_sha256: u.elf_sha256.to_ascii_lowercase(),
            elf_bytes: u.elf_bytes.clone(),
            elf_bytes_module: u.elf_bytes_module.clone(),
            split_parse,
        });
    }
    let mut per_use = Vec::with_capacity(uses.len());
    for u in uses {
        match &u.facts_module {
            None => {
                let g = emit
                    .iter()
                    .find(|g| g.elf_bytes == u.elf_bytes)
                    .expect("every use without `elf_facts_module` has a group");
                per_use.push(g.facts.clone());
            }
            Some(stem) => {
                if let Some(g) = emit.iter().find(|g| g.elf_bytes == u.elf_bytes) {
                    bail!(
                        "`elf_facts_module = {stem:?}` is redundant: this config already emits \
                         `{}` for `{}`",
                        g.facts.module,
                        u.elf_bytes
                    );
                }
                per_use.push(resolve_existing(
                    u,
                    stem,
                    &p.sibling_file(stem),
                    &p.sibling_module(stem),
                )?);
            }
        }
    }
    Ok(FactsPlan { per_use, emit })
}

/// `<Base>ElfFacts.lean` for `m`, reading the ELF at `elf_rel` (relative to the module).
pub fn render_facts(m: &FactsModule, elf_rel: &str, license: &[String]) -> String {
    let f = &m.facts;
    let ns = &m.namespace;
    let local = |q: &str| q.rsplit('.').next().unwrap_or(q).to_string();
    let (image, parse, syms, sym_chars) = (
        local(&f.image),
        local(&f.parse),
        local(&f.syms),
        local(&f.sym_chars),
    );
    let bytes = &m.elf_bytes;
    let mut l = header(license);
    l.extend([
        "module".to_string(),
        String::new(),
        format!("public import {}", m.elf_bytes_module),
        "public import ProofLib.Process.FastParse".into(),
        "public import ProofLib.ProgramReflection".into(),
    ]);
    if let Some((sm, _)) = &m.split_parse {
        l.push(format!("public import {sm}"));
    }
    l.extend([
        "public meta import ProofLib.Process".into(),
        "public meta import ProofLib.ProgramReflection".into(),
    ]);
    if let Some((sm, _)) = &m.split_parse {
        l.push(format!("public meta import {sm}"));
    }
    l.extend([
        String::new(),
        format!(
            "/-! # Parsed stock-linked ELF `{}` (untrusted generator output)",
            doc_safe(elf_rel)
        ),
        String::new(),
        "Generated by `rust-obj2lean` (`untrusted_placed`), which `lake build` runs before compiling"
            .into(),
        "this library. DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "The parsed ELF `{image}`, its parse theorem `{parse}` against `{bytes}`, and its symbol"
        ),
        "table in interned form, shared by every placement witness about these bytes. The kernel"
            .into(),
        "checks each fact; this module defines no bytes and has the Proof role.".into(),
        "-/".into(),
        marker_line(bytes, &m.elf_bytes_module, &m.elf_sha256, ns),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64 Arm64.Process ProofLib.ProgramReflection".into(),
        String::new(),
        "set_option maxHeartbeats 0".into(),
        "set_option maxRecDepth 2000000".into(),
        String::new(),
        format!(
            "/-- The parsed ELF `{}` (checked against `{bytes}` by `{parse}`). -/",
            doc_safe(elf_rel)
        ),
        format!(
            "noncomputable def {image} : ElfImage := elf_image% {}",
            lean_string_lit(elf_rel)
        ),
        String::new(),
    ]);
    match &m.split_parse {
        None => l.extend([
            format!("theorem {parse} : ElfImage.parse {bytes} = .ok {image} := by"),
            "  apply ElfImage.parse_of_fastParse".into(),
            "  rfl_kernel".into(),
        ]),
        Some((sm, lay)) => l.extend(render_split_parse(sm, lay, bytes, &image, &parse)),
    }
    l.extend([
        String::new(),
        format!("noncomputable def {syms} : List (String × BitVec 64) := {image}.symbols"),
        String::new(),
        format!(
            "noncomputable def {sym_chars} : List (List Char × BitVec 64) := assoc_chars_of% {syms}"
        ),
        String::new(),
        format!("theorem {syms}_eq : {image}.symbols = toStringAssoc {sym_chars} := by rfl_kernel"),
        String::new(),
        format!("end {ns}"),
        String::new(),
    ]);
    l.join("\n")
}

/// The split proof of `<parse> : ElfImage.parse <bytes> = .ok <image>` over layout `lay`, using
/// the declarations of module (and namespace) `sm`: one suffix constant per far offset (the first
/// proved by `rDrop` from the bytes, each later one from its predecessor), the file length from
/// the last suffix, and one top-level kernel fact per parse component.
fn render_split_parse(
    sm: &str,
    lay: &ParseLayout,
    bytes: &str,
    image: &str,
    parse: &str,
) -> Vec<String> {
    let n = lay.len;
    let t = |i: usize| format!("{image}_tail{i}");
    let mut l = vec![
        format!(
            "/-! The parse theorem, from separate kernel facts composed by `{sm}.parse_of_parts`. -/"
        ),
        String::new(),
    ];
    for (i, &k) in lay.tails.iter().enumerate() {
        l.push(format!("/-- `{bytes}.drop {k}`. -/"));
        l.push(format!(
            "noncomputable def {} : List (BitVec 8) := suffix_of% {bytes} {k}",
            t(i)
        ));
        l.push(if i == 0 {
            format!(
                "theorem {}_eq : {bytes}.drop {k} = {} := {sm}.drop_of_rDrop (by rfl_kernel)",
                t(i),
                t(i)
            )
        } else {
            format!(
                "theorem {}_eq : {bytes}.drop {k} = {} :=\n  {sm}.drop_chain {}_eq (b := {}) (by rfl_kernel) rfl",
                t(i),
                t(i),
                t(i - 1),
                k - lay.tails[i - 1]
            )
        });
        l.push(String::new());
    }
    let ts: Vec<String> = lay
        .tails
        .iter()
        .enumerate()
        .map(|(i, k)| format!("({k}, {})", t(i)))
        .collect();
    let ok = lay
        .tails
        .iter()
        .enumerate()
        .rev()
        .fold(".nil".to_string(), |acc, (i, _)| {
            format!(".cons {}_eq ({acc})", t(i))
        });
    let last = lay.tails.len() - 1;
    let k_last = lay.tails[last];
    l.extend([
        format!("noncomputable def {image}_tails : List (Nat × List (BitVec 8)) :="),
        format!("  [{}]", ts.join(", ")),
        String::new(),
        format!("theorem {image}_tails_ok : {sm}.TailsOk {bytes} {image}_tails :="),
        format!("  {ok}"),
        String::new(),
        format!("theorem {image}_length : {bytes}.length = {n} :="),
        format!(
            "  {sm}.length_of_drop {} {}_eq (by rfl_kernel) (by decide) rfl",
            n - k_last,
            t(last)
        ),
        String::new(),
        format!("theorem {image}_hdr : {sm}.hdrOk {bytes} {n} {image} = true := by rfl_kernel"),
        String::new(),
        format!("theorem {image}_phdrs : {sm}.phdrsOf {bytes} {n} ="),
        format!("    .ok ({image}.segments, {image}.phdrVaddr, {image}.brkStart.toNat) := by rfl_kernel"),
        String::new(),
        format!(
            "theorem {image}_symtab : {sm}.symtabOf {bytes} {image}_tails {n} = .ok {image}.symbols := by"
        ),
        "  rfl_kernel".into(),
        String::new(),
        format!("theorem {image}_wf : fastWellFormed {image} = true := by rfl_kernel"),
        String::new(),
        format!("theorem {parse} : ElfImage.parse {bytes} = .ok {image} :="),
        format!(
            "  {sm}.parse_of_parts {image}_length {image}_tails_ok {image}_hdr {image}_phdrs {image}_symtab"
        ),
        format!("    {image}_wf"),
    ]);
    l
}

/// The facts module of `m`, as `(path, contents)`, with the ELF path relative to its file.
pub fn facts_output(m: &FactsModule, license: &[String]) -> (PathBuf, String) {
    let dir = m.file.parent().unwrap_or_else(|| Path::new(""));
    (
        m.file.clone(),
        render_facts(m, &relative_path(dir, &m.elf), license),
    )
}
