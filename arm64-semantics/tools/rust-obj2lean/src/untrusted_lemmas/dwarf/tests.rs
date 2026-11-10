// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Tests for the DWARF reader and `-g` companion build (`Role::Test`, `[OUTSIDE TCB]`).
//!
//! Compiles a small C translation unit (structs, a bitfield, a nested struct, an anonymous
//! union, an inlined helper, an unused parameter) with `zig cc` and checks the extracted
//! signatures, layouts, line rows with inline chains, variable locations and the `exact` flag.
//! Tests that need `zig` are skipped (with a message) when it is not installed.

use std::path::Path;

use super::companion::{compile_companion, debug_prefix_map_flags};
use super::*;
use crate::untrusted_driver::{NativeObjectConfig, find_zig_binary};

pub(crate) const SAMPLE_C: &str = r#"#include <stdint.h>
struct inner { uint16_t a; uint16_t b; };
struct flags { unsigned x : 3; unsigned y : 5; unsigned z : 1; };
typedef struct node {
  struct node *next;
  struct inner in;
  struct flags f;
  uint32_t buf[3];
  union { int i; float fl; } u;
} node_t;
static inline int helper(const node_t *n) { return n->in.b + n->buf[1]; }
int sum_list(node_t *p, int unused, uint32_t k) {
  int s = 0;
  while (p) { s += helper(p) * (int)k; p = p->next; }
  return s;
}
int set_flags(struct flags *f, unsigned v) { f->y = v; return f->x; }
"#;

/// Compile [`SAMPLE_C`] with `extra` flags into ELF bytes (`None` if `zig` is missing).
pub(crate) fn compile_sample(extra: &[&str]) -> Option<(tempfile::TempDir, Vec<u8>)> {
    let Ok(zig) = find_zig_binary("dwarf tests") else {
        eprintln!("skipping DWARF test: zig not found");
        return None;
    };
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("sample.c"), SAMPLE_C).unwrap();
    let obj = NativeObjectConfig {
        name: "sample".into(),
        source: "sample.c".into(),
        include_dirs: Vec::new(),
        defines: Vec::new(),
        c_flags: extra.iter().map(|s| s.to_string()).collect(),
    };
    let maps = debug_prefix_map_flags(&[(dir.path(), "/src")]);
    let (elf, _headers) = compile_companion(&zig, dir.path(), &obj, &[], &maps).unwrap();
    Some((dir, elf))
}

fn func<'a>(dw: &'a DwarfObject, name: &str) -> &'a FoundFunction {
    dw.functions
        .iter()
        .find(|f| f.info.name == name)
        .unwrap_or_else(|| panic!("no DWARF function {name}"))
}

#[test]
fn signature_and_params() {
    let Some((_d, elf)) = compile_sample(&[]) else {
        return;
    };
    let dw = read_elf_dwarf(&elf).unwrap();
    let f = func(&dw, "sum_list");
    assert_eq!(f.section, ".text.sum_list");
    assert_eq!(f.section_offset, 0);
    assert_eq!(f.symbol.as_deref(), Some("sum_list"));
    assert_eq!(
        f.info.signature(),
        "int sum_list(node_t * p, int unused, uint32_t k)"
    );
    assert_eq!(f.info.decl_file, "/src/sample.c");
    assert_eq!(f.info.decl_line, 12);
    assert!(f.info.external);
    assert_eq!(f.info.params[0].byte_size, Some(8));
    assert_eq!(f.info.params[0].pointee.as_deref(), Some("struct node"));
    assert_eq!(f.info.params[0].entry_location.as_deref(), Some("x0"));
    // Unused but never clobbered: still described as live in its ABI register at entry.
    assert_eq!(f.info.params[1].entry_location.as_deref(), Some("x1"));
    assert!(!f.info.params[1].optimized_out);
    assert_eq!(f.info.params[2].entry_location.as_deref(), Some("x2"));
}

#[test]
fn struct_union_bitfield_layouts() {
    let Some((_d, elf)) = compile_sample(&[]) else {
        return;
    };
    let dw = read_elf_dwarf(&elf).unwrap();
    let node = &dw.layouts["struct node"];
    assert_eq!(node.byte_size, 32);
    assert!(
        node.typedefs.contains(&"node_t".to_string()),
        "{:?}",
        node.typedefs
    );
    let m = |n: &str| node.members.iter().find(|m| m.name == n).unwrap();
    assert_eq!(
        (m("next").byte_offset, m("next").pointee.as_deref()),
        (0, Some("struct node"))
    );
    assert_eq!(
        (m("in").byte_offset, m("in").aggregate.as_deref()),
        (8, Some("struct inner"))
    );
    assert_eq!(
        (m("buf").byte_offset, m("buf").array_elem_size),
        (16, Some(4))
    );
    assert_eq!(m("u").byte_offset, 28);
    let u = &dw.layouts[m("u").aggregate.as_deref().unwrap()];
    assert_eq!((u.kind.as_str(), u.byte_size), ("union", 4));
    let flags = &dw.layouts["struct flags"];
    let y = flags.members.iter().find(|m| m.name == "y").unwrap();
    assert_eq!((y.bit_offset, y.bit_size), (Some(3), Some(5)));
    // Reachable from `sum_list`: node, its nested inner/flags/union.
    let reach = reachable_layouts([&func(&dw, "sum_list").info], &dw.layouts, 1);
    let names: Vec<&str> = reach.iter().map(|l| l.name.as_str()).collect();
    for n in ["struct node", "struct inner", "struct flags"] {
        assert!(names.contains(&n), "{names:?}");
    }
}

#[test]
fn lines_inlines_and_variables() {
    let Some((_d, elf)) = compile_sample(&[]) else {
        return;
    };
    let dw = read_elf_dwarf(&elf).unwrap();
    let f = &func(&dw, "sum_list").info;
    assert!(
        f.lines.iter().all(|l| l.file == "/src/sample.c"),
        "{:?}",
        f.lines
    );
    assert!(f.lines.iter().any(|l| l.line == 14), "{:?}", f.lines);
    assert!(
        f.lines
            .iter()
            .any(|l| l.line == 11 && l.inlined.iter().any(|s| s.contains("helper"))),
        "{:#?}",
        f.lines
    );
    let p = f.variables.iter().find(|v| v.name == "p").unwrap();
    assert_eq!(p.kind, "param");
    assert!(
        p.locations
            .iter()
            .any(|l| l.start == 0 && l.location == "x0"),
        "{p:?}"
    );
    assert!(
        f.variables
            .iter()
            .any(|v| v.name == "s" && v.kind == "local"),
        "{:?}",
        f.variables
    );
}

#[test]
fn debug_prefix_map_hides_host_paths() {
    let Some((d, elf)) = compile_sample(&[]) else {
        return;
    };
    let host = d.path().to_string_lossy().into_owned();
    let hay = String::from_utf8_lossy(&elf);
    assert!(!hay.contains(&host), "host path {host} leaked into DWARF");
    let flags = debug_prefix_map_flags(&[(Path::new("/a/b"), "/x"), (Path::new("/a"), "/y")]);
    assert_eq!(
        flags,
        ["-fdebug-prefix-map=/a=/y", "-fdebug-prefix-map=/a/b=/x"]
    );
}

#[test]
fn non_alloc_debug_sections_only() {
    // `-g` adds only non-`SHF_ALLOC` sections (+ their relocations) for this TU, and no DWARF is
    // present without it: the companion object is the trusted one plus debug sections.
    let Some((_d, g0)) = compile_sample(&["-g0"]) else {
        return;
    };
    assert!(read_elf_dwarf(&g0).unwrap().functions.is_empty());
}

#[test]
fn layout_table_and_lean_offsets() {
    use super::cli::{render_layout_lean, render_layout_table, select_layouts};
    let Some((_d, elf)) = compile_sample(&[]) else {
        return;
    };
    let dw = read_elf_dwarf(&elf).unwrap();
    // Exact typedef match wins over substring matches (`struct node` vs nothing else here).
    let sel = select_layouts(&dw.layouts, Some("node_t"));
    assert_eq!(sel.len(), 1);
    let table = render_layout_table(sel[0]);
    assert!(
        table.contains("struct node (typedef node_t): size 0x20"),
        "{table}"
    );
    assert!(
        table.contains("+0x0010    4  buf : uint32_t[3]") || table.contains("buf : uint32_t"),
        "{table}"
    );
    let lean = render_layout_lean(&dw.layouts, sel[0]);
    assert!(lean.contains("namespace Node_tLayout"), "{lean}");
    assert!(lean.contains("abbrev size : Nat := 0x20"), "{lean}");
    assert!(lean.contains("abbrev offNext : Nat := 0x0"), "{lean}");
    assert!(lean.contains("abbrev offIn_B : Nat := 0xa"), "{lean}");
    assert!(lean.contains("abbrev offF_Y : Nat := 0xc"), "{lean}");
    assert!(lean.contains("bits 3..8"), "{lean}");
    assert!(lean.contains("abbrev offBuf : Nat := 0x10"), "{lean}");
    assert!(lean.contains("abbrev offU_Fl : Nat := 0x1c"), "{lean}");
    let flags = select_layouts(&dw.layouts, Some("flag"));
    assert_eq!(flags.len(), 1);
}

#[test]
fn depfile_headers() {
    let d = "x.o: x.c /a/b.h \\\n  inc/c.h x.c\n";
    let hs = super::companion::parse_depfile(d, Path::new("/base"));
    assert_eq!(
        hs,
        [
            Path::new("/a/b.h").to_path_buf(),
            Path::new("/base/inc/c.h").to_path_buf()
        ]
    );
}
