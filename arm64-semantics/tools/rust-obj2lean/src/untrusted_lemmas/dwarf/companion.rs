// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `-g` Companion Build: DWARF for the Trusted `-g0` Image (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. The trusted extractor keeps compiling C with
//!   `NATIVE_CFLAGS` (`-g0`): measured on this repository's targets, adding `-g` changes the
//!   machine code of about a third of the functions (LLVM emits CFI for `.debug_frame` when
//!   debug info is on, and CFI pseudo-instructions are scheduling barriers in prologues; Rust's
//!   `-C debuginfo=2` changes MIR/LLVM output too), so it cannot be turned on without changing
//!   the verified images. Instead this module recompiles every `[[native_objects]]` /
//!   `c_sources` translation unit a second time, identically plus `-g` and
//!   `-fdebug-prefix-map=<dir>=/src|/zig|/build` (host-independent DWARF paths), reads its
//!   DWARF, and attaches it to the *trusted* objects' functions by `(section name, offset)`.
//! - Every function is marked [`DwarfFunctionInfo::exact`] iff its bytes in the companion
//!   object equal its bytes in the trusted object: then line rows and variable locations are
//!   exact for the image; otherwise only they are approximate (signatures and type layouts do not
//!   depend on scheduling). Objects that already carry DWARF (e.g. prebuilt `c_objects` compiled
//!   with `-g`) are read directly and are exact.
//! - Failures (no `zig`, compile errors) only drop the DWARF hints; they never fail an export.
//!   Set `RUST_OBJ2LEAN_NO_DWARF=1` to skip the companion build.
//!
//! # Key Types & Functions
//! - [`ImageDwarf`], [`image_dwarf`]: DWARF keyed by trusted (disambiguated) symbol name.
//! - [`debug_prefix_map_flags`], [`zig_lib_dir`], [`companion_cc_args`].
//!
//! # When to Read This File
//! - Read this file when DWARF is missing for a C function in `*Index.json`, or when changing how
//!   the companion objects are compiled.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};
use object::{Object, ObjectSection};

use super::{DwarfFunctionInfo, DwarfObject, DwarfTypeLayout, read_elf_dwarf};
use crate::trusted_common::{ObjObject, SymKind, SymSection};
use crate::untrusted_driver::{
    ExportConfig, NativeObjectConfig, c_stem_ident, find_zig_binary, native_cc_args_with_flags,
};

/// DWARF attached to an exported image.
#[derive(Clone, Debug, Default)]
pub struct ImageDwarf {
    /// Function DWARF keyed by the trusted symbol name (as in `FuncRange::name`).
    pub functions: BTreeMap<String, DwarfFunctionInfo>,
    /// All struct/union layouts of all objects.
    pub layouts: BTreeMap<String, DwarfTypeLayout>,
    /// Every source file named by a line table.
    pub files: BTreeSet<String>,
    /// Companion objects `(trusted object name, ELF bytes)`.
    pub objects: Vec<(String, Vec<u8>)>,
    /// Headers included by each companion-compiled object (keyed by trusted object name).
    pub headers: BTreeMap<String, Vec<PathBuf>>,
    /// Non-fatal problems (missing compiler, compile errors), for diagnostics.
    pub warnings: Vec<String>,
}

/// `-fdebug-prefix-map` flags making DWARF paths host-independent.
///
/// Each entry is `(host_dir, replacement)`. Every directory is mapped as given and canonicalized
/// (if different); directories containing `=` or whitespace are skipped. Flags are sorted by
/// increasing directory length because clang (like gcc) applies the last matching map, so a
/// nested directory wins. Only `-fdebug-prefix-map` is used (never `-ffile-prefix-map`), so
/// `__FILE__` strings in `.rodata` are untouched.
pub fn debug_prefix_map_flags(entries: &[(&Path, &str)]) -> Vec<String> {
    let mut real: Vec<(String, String)> = Vec::new();
    for (dir, to) in entries {
        let mut variants = vec![dir.to_path_buf()];
        if let Ok(c) = dir.canonicalize()
            && c != *dir
        {
            variants.push(c);
        }
        for v in variants {
            let s = v.to_string_lossy().into_owned();
            if s.is_empty() || s.contains('=') || s.chars().any(char::is_whitespace) {
                continue;
            }
            let flag = format!("-fdebug-prefix-map={s}={to}");
            if !real.iter().any(|(_, f)| *f == flag) {
                real.push((s, flag));
            }
        }
    }
    real.sort_by_key(|(d, _)| d.len());
    real.into_iter().map(|(_, f)| f).collect()
}

/// The library directory of `zig` (`lib_dir` in `zig env`, whose libc headers appear in line
/// tables), or `None`.
pub fn zig_lib_dir(zig: &Path) -> Option<PathBuf> {
    let out = Command::new(zig).arg("env").output().ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    // ZON (`.lib_dir = "..."`, zig 0.14+) or JSON (`"lib_dir": "..."`).
    let line = text.lines().find(|l| l.contains("lib_dir"))?;
    let after = line.split_once("lib_dir")?.1;
    let start = after.find('"')? + 1;
    let end = start + after[start..].find('"')?;
    let dir = PathBuf::from(&after[start..end]);
    dir.is_absolute().then_some(dir)
}

/// `zig cc` arguments of the companion compile: exactly the trusted compile's arguments
/// (`native_cc_args_with_flags` with the config's `c_flags`) plus `-g2` and `prefix_maps`.
pub fn companion_cc_args(
    obj: &NativeObjectConfig,
    top_c_flags: &[String],
    prefix_maps: &[String],
    out: &str,
) -> Vec<String> {
    let extra: Vec<String> = top_c_flags
        .iter()
        .cloned()
        // zig cc ignores a plain `-g` after `-g0`; `-g2` overrides it.
        .chain(["-g2".to_string()])
        .chain(prefix_maps.iter().cloned())
        .collect();
    native_cc_args_with_flags(obj, &extra, out)
}

/// The `[[native_objects]]` and `c_sources` of `cfg` with the object names the trusted
/// extractor gives them (same order and `c_stem_ident` deduplication as `extract`).
pub fn native_sources(cfg: &ExportConfig) -> Vec<NativeObjectConfig> {
    let mut out: Vec<NativeObjectConfig> = cfg.native_objects.clone();
    let mut used: BTreeSet<String> = out.iter().map(|n| n.name.clone()).collect();
    for src in &cfg.c_sources {
        let Ok(base) = c_stem_ident(src) else {
            continue;
        };
        let mut name = base.clone();
        let mut idx = 2usize;
        while !used.insert(name.clone()) {
            name = format!("{base}_{idx}");
            idx += 1;
        }
        out.push(NativeObjectConfig {
            name,
            source: src.clone(),
            include_dirs: Vec::new(),
            defines: Vec::new(),
            c_flags: Vec::new(),
        });
    }
    out
}

/// Compile one companion object; returns its ELF bytes.
pub(crate) fn compile_companion(
    zig: &Path,
    crate_dir: &Path,
    obj: &NativeObjectConfig,
    top_c_flags: &[String],
    maps: &[String],
) -> Result<(Vec<u8>, Vec<PathBuf>)> {
    let tmp = tempfile::Builder::new()
        .prefix("rust_obj2lean_dwarf_")
        .tempdir()?;
    let out = tmp.path().join(format!("{}.o", obj.name));
    let dep = tmp.path().join(format!("{}.d", obj.name));
    let mut all_maps = maps.to_vec();
    all_maps.extend(debug_prefix_map_flags(&[(tmp.path(), "/build")]));
    // Header dependencies from `-MD`; `-MD` does not affect code generation.
    all_maps.extend([
        "-MD".to_string(),
        "-MF".to_string(),
        dep.to_string_lossy().into_owned(),
    ]);
    let args = companion_cc_args(obj, top_c_flags, &all_maps, &out.to_string_lossy());
    let res = Command::new(zig)
        .args(&args)
        .current_dir(crate_dir)
        .output()
        .with_context(|| format!("failed to spawn `{}`", zig.display()))?;
    if !res.status.success() {
        bail!(
            "companion compile of `{}` failed: {}",
            obj.name,
            String::from_utf8_lossy(&res.stderr)
        );
    }
    let headers = fs::read_to_string(&dep)
        .map(|d| parse_depfile(&d, crate_dir))
        .unwrap_or_default();
    Ok((fs::read(&out)?, headers))
}

/// Header paths (`.h`) of a Make depfile, resolved against `base`.
pub fn parse_depfile(text: &str, base: &Path) -> Vec<PathBuf> {
    let joined = text.replace("\\\n", " ").replace("\\\r\n", " ");
    let deps = joined.split_once(": ").map_or("", |(_, d)| d);
    let mut out: Vec<PathBuf> = deps
        .split_whitespace()
        .filter(|t| t.ends_with(".h"))
        .map(|t| base.join(t))
        .collect();
    out.dedup();
    out
}

/// Map DWARF functions of an object onto the trusted object `o` by `(section, offset)`.
/// `elf` is the object the DWARF came from (to compare code bytes for `exact`).
fn attach(dw: DwarfObject, elf: &[u8], o: &ObjObject, out: &mut ImageDwarf) {
    let companion = object::File::parse(elf).ok();
    for f in dw.functions {
        let Some((si, sec)) = o
            .sections
            .iter()
            .enumerate()
            .find(|(_, s)| s.name == f.section)
        else {
            continue;
        };
        let Some(sym) = o.symbols.iter().find(|s| {
            s.kind == SymKind::Func && s.sec == SymSection::Sec(si) && s.value == f.section_offset
        }) else {
            continue;
        };
        let (start, end) = (
            f.section_offset as usize,
            (f.section_offset + f.size) as usize,
        );
        let image_bytes = sec.bytes.get(start..end);
        let dwarf_bytes = companion.as_ref().and_then(|c| {
            let s = c.section_by_name(&f.section)?;
            s.data().ok()?.get(start..end)
        });
        let mut info = f.info;
        info.exact = f.size > 0
            && (sym.size == 0 || sym.size == f.size)
            && image_bytes.is_some()
            && image_bytes == dwarf_bytes;
        out.functions.entry(sym.name.clone()).or_insert(info);
    }
    for (k, v) in dw.layouts {
        out.layouts.entry(k).or_insert(v);
    }
    out.files.extend(dw.files);
}

/// DWARF for the image built from `objects` (the trusted objects of `cfg`): read from objects
/// that carry DWARF, else from `-g` companion compiles of `cfg`'s C sources.
pub fn image_dwarf(cfg: &ExportConfig, objects: &[ObjObject]) -> ImageDwarf {
    let mut out = ImageDwarf::default();
    if std::env::var_os("RUST_OBJ2LEAN_NO_DWARF").is_some_and(|v| !v.is_empty() && v != "0") {
        return out;
    }
    // Objects compiled with DWARF already (exact by construction).
    let mut have: BTreeSet<&str> = BTreeSet::new();
    for o in objects {
        match read_elf_dwarf(&o.elf_bytes) {
            Ok(dw) if !dw.functions.is_empty() || !dw.layouts.is_empty() => {
                have.insert(o.name.as_str());
                attach(dw, &o.elf_bytes, o, &mut out);
            }
            Ok(_) => {}
            Err(e) => out.warnings.push(format!("{}: {e:#}", o.name)),
        }
    }
    let sources: Vec<NativeObjectConfig> = native_sources(cfg)
        .into_iter()
        .filter(|n| !have.contains(n.name.as_str()))
        .collect();
    if sources.is_empty() {
        return out;
    }
    let zig = match find_zig_binary("DWARF companion build") {
        Ok(z) => z,
        Err(e) => {
            out.warnings.push(format!("no DWARF for C objects: {e:#}"));
            return out;
        }
    };
    let mut entries: Vec<(&Path, &str)> = vec![(cfg.crate_dir.as_path(), "/src")];
    let lib = zig_lib_dir(&zig);
    if let Some(l) = lib.as_deref() {
        entries.push((l, "/zig"));
    }
    let maps = debug_prefix_map_flags(&entries);
    for n in &sources {
        let Some(o) = objects.iter().find(|o| o.name == n.name) else {
            continue;
        };
        match compile_companion(&zig, &cfg.crate_dir, n, &cfg.c_flags, &maps)
            .and_then(|(elf, hdrs)| read_elf_dwarf(&elf).map(|dw| (dw, elf, hdrs)))
        {
            Ok((dw, elf, hdrs)) => {
                attach(dw, &elf, o, &mut out);
                out.headers.insert(o.name.clone(), hdrs);
                out.objects.push((o.name.clone(), elf));
            }
            Err(e) => out.warnings.push(format!("{}: {e:#}", n.name)),
        }
    }
    out
}

/// Fill `FunctionIndexEntry::dwarf` (by function name) and `dwarf_types` (layouts reachable from
/// the indexed functions, following member pointers one hop) of `idx` from `dw`.
pub fn attach_to_index(dw: &ImageDwarf, idx: &mut crate::untrusted_lemmas::index::TargetSymbolIndex) {
    for f in &mut idx.functions {
        f.dwarf = dw.functions.get(&f.name).cloned();
    }
    idx.dwarf_types = super::reachable_layouts(
        idx.functions.iter().filter_map(|f| f.dwarf.as_ref()),
        &dw.layouts,
        1,
    );
}
