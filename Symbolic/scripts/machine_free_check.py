#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Transitive constant-cone "machine-free" checker and proof-dependency criterion tool.

Usage (from any directory):
    # 1. Audit the symbolic CLI statement modules against Symbolic/scripts/machine_free_allow.txt:
    Symbolic/scripts/machine_free_check.py --root <WORKTREE> --all-module-consts --summary-only \\
      Symbolic.Specifications.Refinement.Statement \\
      --import Symbolic.Specifications.Refinement.CliSetup \\
      --import Symbolic.Specifications.Security.AsmSecure \\
      --import Symbolic.Specifications.Refinement.RefinementPreservation

    # 2. Compute per-module machine-level criterion over the default Lake target closure:
    Symbolic/scripts/machine_free_check.py --root <WORKTREE> --criterion \\
      --criterion-tsv /tmp/proofdeps_criterion.tsv \\
      --deny-file Symbolic/scripts/machine_free_deny.txt \\
      --deny-file Symbolic/scripts/machine_free_deny_d2.txt \\
      --exclude-deny-group 5 \\
      --allow-file Symbolic/scripts/machine_free_allow.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps_q1.txt \\
      --exempt-specs-file Symbolic/scripts/machine_free_exempt_specs.txt

    # 3. Emit Symbolic/scripts/machine_free_deny_proofdeps.txt:
    Symbolic/scripts/machine_free_check.py --root <WORKTREE> \\
      --emit-proofdeps Symbolic/scripts/machine_free_deny_proofdeps.txt \\
      --deny-file Symbolic/scripts/machine_free_deny.txt \\
      --deny-file Symbolic/scripts/machine_free_deny_d2.txt \\
      --exclude-deny-group 5 \\
      --allow-file Symbolic/scripts/machine_free_allow.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps_q1.txt \\
      --exempt-specs-file Symbolic/scripts/machine_free_exempt_specs.txt

    # 4. CI drift check on Symbolic/scripts/machine_free_deny_proofdeps.txt:
    Symbolic/scripts/machine_free_check.py --root <WORKTREE> --gate \\
      --check-proofdeps Symbolic/scripts/machine_free_deny_proofdeps.txt \\
      --deny-file Symbolic/scripts/machine_free_deny.txt \\
      --deny-file Symbolic/scripts/machine_free_deny_d2.txt \\
      --exclude-deny-group 5 \\
      --allow-file Symbolic/scripts/machine_free_allow.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps_q1.txt \\
      --exempt-specs-file Symbolic/scripts/machine_free_exempt_specs.txt

    # 5. Proof-root dependency gate run:
    Symbolic/scripts/machine_free_check.py --root <WORKTREE> --gate --root-report \\
      --expected-root-type-file Symbolic/scripts/machine_free_expected_root_types.txt \\
      --bridges-file Symbolic/scripts/machine_free_bridges.txt \\
      --deny-file Symbolic/scripts/machine_free_deny.txt \\
      --deny-file Symbolic/scripts/machine_free_deny_d2.txt \\
      --exclude-deny-group 5 \\
      --deny-file Symbolic/scripts/machine_free_deny_proofdeps.txt \\
      --allow-file Symbolic/scripts/machine_free_allow.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps.txt \\
      --allow-file Symbolic/scripts/machine_free_allow_proofdeps_q1.txt \\
      --exempt-specs-file Symbolic/scripts/machine_free_exempt_specs.txt \\
      <RootModule> <RootConst1> [<RootConst2> ...]

    # 6. Run self-tests:
    Symbolic/scripts/machine_free_check.py --root <WORKTREE> --self-test

Exit codes:
  0  Clean (`MACHINE_FREE=yes` / `CRITERION` / `CHECK_PROOFDEPS=PASS`, pins `PASS`, `UNREACHED_ALLOW=0`).
  1  Violation (`MACHINE_FREE=no`, uncovered machine-level module, `D2` finding, root outside default
     Lake targets, `--root-report` check failure, stale allow-list entry, or engine/blob pin mismatch).
  2  Usage, I/O, missing header pin, missing required tag, wildcard/module/prefix allow entry,
     invalid `[group ...]` or `--exclude-deny-group`, missing `.olean`, or missing constant error.
"""
import argparse
import contextlib
import fcntl
import hashlib
import io
import os
import pathlib
import posixpath
import re
import resource
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
SCRIPT_REPO = SCRIPT_DIR.parents[1]

PRODUCTION_PIN_ALLOW_FILENAMES: tuple[str, ...] = (
    "machine_free_allow.txt",
    "machine_free_allow_proofdeps.txt",
    "machine_free_allow_proofdeps_q1.txt",
)

GK_CONTROL_CHOICES = [
    "neg1",
    "neg1-standin",
    "neg2",
    "neg3",
    "neg3-bug-demo",
    "neg4",
    "neg5",
    "neg5b",
    "arch1",
    "arch2",
    "arch3",
]

ENGINE_PIN_PATTERNS = (
    re.compile(r"(?i)\bengine[\s_-]*pin\s*[:=@]\s*([0-9a-f]{7,40})\b"),
    re.compile(
        r"(?i)\bpinned\s+engine(?:\s+submodule|\s+commit)?\s*"
        r"(?:[:=@]|arm64-semantics\s*@\s*)?\s*([0-9a-f]{7,40})\b"
    ),
    re.compile(
        r"(?i)\bengine\s+submodule(?:\s+commit|\s+pin)?\s*(?:[:=@]\s*|\s+)([0-9a-f]{7,40})\b"
    ),
    re.compile(
        r"(?i)\barm64-semantics\s*(?:@|==|=|:|\s+at\s+|\s+commit\s+)\s*([0-9a-f]{7,40})\b"
    ),
)

BLOB_PIN_RE = re.compile(
    r"^#\s*blob-pin\s*:\s*([^\s=#]+)\s*=\s*([0-9a-fA-F]{7,40})\s*$"
)
REQUIRE_TAG_RE = re.compile(
    r"^#\s*require-tag\s*:\s*(\S+)\s*$"
)

GITLINK_RE = re.compile(r"^160000\s+commit\s+([0-9a-f]{40})\tarm64-semantics$")

SKIP_TOP_DIRS = {
    ".agents",
    ".git",
    ".github",
    ".lake",
    ".skills",
    ".sym-logs",
    "arm64-semantics",
    "docs",
    "scripts",
    "third_party",
}
# Placeholder `@[default_target]` libraries that explicitly declare `roots := #[]` and no `globs`
# (their modules are built via `Symbolic`).
ALLOWED_LITERAL_EMPTY_DEFAULT_LIBS: frozenset[str] = frozenset({"SymbolicTheorems"})

DEFAULT_TARGET_ATTR_RE = re.compile(r"@\[[^\]]*\bdefault_target\b[^\]]*\]")
LEAN_LIB_DECL_RE = re.compile(
    r"(?:(@\[[^\]]*\])\s*)?lean_lib\s+(?:«([^»]+)»|([\w.-]+))(.*?)"
    r"(?=\n\s*(?:@\[|lean_lib\b|lean_exe\b|extern_lib\b|/--|require\b|target\b|script\b|input_file\b|input_dir\b|package\b|def\b|abbrev\b|unsafe\b|opaque\b)|\Z)",
    re.S,
)
KNOWN_NON_MODULE_LIB_FIELDS: frozenset[str] = frozenset(
    {
        "leanOptions",
        "moreLeanArgs",
        "weakLeanArgs",
        "moreServerArgs",
        "moreGlobalServerArgs",
        "nativeFacets",
        "defaultFacets",
        "extraDepTargets",
        "needs",
        "precompileModules",
        "platformIndependent",
        "backend",
        "srcDir",
        "roots",
        "globs",
    }
)
SINGLE_ROOT_ITEM_RE = re.compile(r"^`(?:«([^»]+)»|([\w.]+))$")
SINGLE_GLOB_ITEM_RE = re.compile(r"^\.(one|submodules|andSubmodules)\s+`(?:«([^»]+)»|([\w.]+))$")

def resolve_default_asset(repo_root: pathlib.Path, filename: str) -> pathlib.Path:
    """Prefer `<repo_root>/Symbolic/scripts/<filename>` when present, else `<SCRIPT_DIR>/<filename>`."""
    cand = repo_root / "Symbolic" / "scripts" / filename
    if cand.is_file():
        return cand
    return SCRIPT_DIR / filename

_LEX_OUTER_RE = re.compile(
    r"""'\\"'|'\"'|(r(#+)")|"(?:\\.|[^"\\])*"|"|--[^\n]*|/-""",
    re.S,
)
_BLOCK_COMMENT_DELIM_RE = re.compile(r"/-|-/")

def strip_lean_comments(text: str) -> str:
    """Strip `--` line comments and nested `/- ... -/` block comments outside string literals.

    Handles `"..."` string literals, raw `r#+"..."#+` string literals, and `'"'` / `'\\"'`
    character literals without treating identifier primes (`foo'`) as quotes. Raises `RuntimeError`
    on unterminated string literals or block comments.
    """
    out: list[str] = []
    pos = 0
    n = len(text)
    while pos < n:
        m = _LEX_OUTER_RE.search(text, pos)
        if m is None:
            out.append(text[pos:])
            break
        start = m.start()
        if start > pos:
            out.append(text[pos:start])
        tok = m.group(0)
        if m.group(1) is not None:
            if start > 0 and (text[start - 1].isalnum() or text[start - 1] == "_"):
                # Identifier ending in `r` followed by `#+"`: advance past `r#...` up to `"`,
                # so the `"` itself is re-lexed as a normal string opening on the next iteration.
                out.append(tok[:-1])
                pos = m.end() - 1
                continue
            close_tok = '"' + m.group(2)
            end_idx = text.find(close_tok, m.end())
            if end_idx < 0:
                raise RuntimeError("unterminated raw string literal in Lean source")
            out.append(text[start : end_idx + len(close_tok)])
            pos = end_idx + len(close_tok)
        elif tok == "/-":
            depth = 1
            cpos = m.end()
            nl_count = 0
            while depth > 0:
                cm = _BLOCK_COMMENT_DELIM_RE.search(text, cpos)
                if cm is None:
                    raise RuntimeError("unterminated block comment '/-' in Lean source")
                nl_count += text.count("\n", cpos, cm.start())
                if cm.group(0) == "/-":
                    depth += 1
                else:
                    depth -= 1
                cpos = cm.end()
            if nl_count:
                out.append("\n" * nl_count)
            pos = cpos
        elif tok.startswith("--"):
            pos = m.end()
        elif tok == '"':
            raise RuntimeError("unterminated string literal in Lean source")
        else:
            out.append(tok)
            pos = m.end()
    return "".join(out)

_MASK_OUTER_RE = re.compile(
    r"""'\\"'|'\"'|(r(#+)")|"(?:\\.|[^"\\])*\x22""",
    re.S,
)

def mask_lean_strings(text: str) -> str:
    """Replace interior characters of Lean string/char-quote literals with spaces (preserving `\\n` and offsets)."""
    out: list[str] = []
    pos = 0
    n = len(text)
    while pos < n:
        m = _MASK_OUTER_RE.search(text, pos)
        if m is None:
            out.append(text[pos:])
            break
        start = m.start()
        if start > pos:
            out.append(text[pos:start])
        tok = m.group(0)
        if m.group(1) is not None:
            if start > 0 and (text[start - 1].isalnum() or text[start - 1] == "_"):
                out.append(tok[:-1])
                pos = m.end() - 1
                continue
            close_tok = '"' + m.group(2)
            end_idx = text.find(close_tok, m.end())
            if end_idx < 0:
                raise RuntimeError("unterminated raw string literal in Lean source")
            out.append(tok)
            interior = text[m.end() : end_idx]
            out.append(re.sub(r"[^\n]", " ", interior))
            out.append(close_tok)
            pos = end_idx + len(close_tok)
        elif tok == "'\"'":
            out.append("' '")
            pos = m.end()
        elif tok == "'\\\"'":
            out.append("'  '")
            pos = m.end()
        else:
            interior = tok[1:-1]
            out.append('"' + re.sub(r"[^\n]", " ", interior) + '"')
            pos = m.end()
    return "".join(out)

def scan_repo_lean_modules(repo_root: pathlib.Path) -> set[str]:
    """Scan working-tree `.lean` module names (including `.GeneratedLean`) for Lake glob expansion."""
    all_mods: set[str] = set()
    for top in sorted(repo_root.iterdir()):
        if top.name in SKIP_TOP_DIRS:
            continue
        if top.name == ".GeneratedLean" and top.is_dir():
            for p in top.rglob("*.lean"):
                rel = p.relative_to(top)
                if any(part.startswith(".") for part in rel.parts):
                    continue
                mod = ".".join((*rel.parts[:-1], rel.stem))
                all_mods.add(mod)
            continue
        if top.name.startswith("."):
            continue
        if top.is_file() and top.suffix == ".lean":
            if top.name == "lakefile.lean":
                continue
            all_mods.add(top.stem)
        elif top.is_dir():
            for p in top.rglob("*.lean"):
                rel = p.relative_to(repo_root)
                if any(
                    part.startswith(".")
                    or part == "RELEASE_EXCLUDE"
                    or part == "test_fixtures"
                    for part in rel.parts
                ):
                    continue
                mod = ".".join((*rel.parts[:-1], rel.stem))
                all_mods.add(mod)
    return all_mods

def parse_generated_lean_modules_from_lakefile(cleaned: str, lakefile: pathlib.Path) -> list[str]:
    """Parse static `generatedLeanModules` derived from `def exportOutputs` in `lakefile.lean`."""
    if not re.search(r"\bdef\s+generatedLeanModules\s*:\s*Array\s+Lean\.Name\s*:=", cleaned):
        raise RuntimeError(
            f"@[default_target] lean_lib GeneratedLean references `generatedLeanModules`, "
            f"but `def generatedLeanModules : Array Lean.Name :=` was not found in {lakefile}"
        )
    om = re.search(
        r"\bdef\s+exportOutputs\s*:\s*Array\s+FilePath\s*:=\s*\(#\[(.*?)\]\s*:\s*Array\s+String\)\.map\s+FilePath\.mk",
        cleaned,
        re.S,
    )
    if om is None:
        raise RuntimeError(
            f"could not parse literal `def exportOutputs` array in {lakefile} for `generatedLeanModules`"
        )
    pfx = ".GeneratedLean/GeneratedLean/"
    sfx = ".lean"
    mods: list[str] = []
    for raw_item in [x.strip() for x in om.group(1).split(",") if x.strip()]:
        sm = re.fullmatch(r'"([^"\\\n]+)"', raw_item)
        if sm is None:
            raise RuntimeError(
                f"unparseable `exportOutputs` item {raw_item!r} in {lakefile}"
            )
        rel_path = sm.group(1)
        if rel_path.startswith(pfx) and rel_path.endswith(sfx):
            stem = rel_path[len(pfx) : -len(sfx)].replace("/", ".")
            mods.append(f"GeneratedLean.{stem}")
    if not mods:
        raise RuntimeError(
            f"`exportOutputs` in {lakefile} yielded 0 `.GeneratedLean/GeneratedLean/*.lean` modules"
        )
    return mods

def compute_default_target_lib_batches(repo_root: pathlib.Path) -> list[list[str]]:
    """Parse `<repo_root>/lakefile.lean` for per-`@[default_target] lean_lib` seed module batches.

    Keeping one batch per `@[default_target] lean_lib` avoids importing unrelated umbrella
    libraries (such as `LibsignalBinary.Cli` and `Computational`) into a single `Lean.Environment`
    when they declare identically named local tactic macros.
    """
    bug_inj = os.environ.get("CV_BUG_INJECTION", "").strip()
    if bug_inj:
        raise RuntimeError(
            f"CV_BUG_INJECTION={bug_inj!r} is set; refusing default-target audit on bug-injected image"
        )
    lakefile = repo_root / "lakefile.lean"
    if not lakefile.is_file():
        raise RuntimeError(f"lakefile.lean not found in {repo_root}")
    cleaned = strip_lean_comments(lakefile.read_text(encoding="utf-8"))
    masked = mask_lean_strings(cleaned)
    assert len(masked) == len(cleaned), "internal error: mask_lean_strings changed string length"

    raw_dt_count = len(DEFAULT_TARGET_ATTR_RE.findall(masked))
    if raw_dt_count == 0:
        raise RuntimeError(f"found 0 @[default_target] attributes in {lakefile}")

    all_mods = scan_repo_lean_modules(repo_root)
    batches: list[list[str]] = []
    parsed_default_count = 0

    for m in LEAN_LIB_DECL_RE.finditer(masked):
        attr_str = m.group(1) or ""
        if not DEFAULT_TARGET_ATTR_RE.search(attr_str):
            continue
        parsed_default_count += 1
        name = m.group(2) if m.group(2) is not None else m.group(3)
        body = m.group(4)
        unmasked_body = cleaned[m.start(4) : m.end(4)]

        for fm in re.finditer(r"(\w+)\s*:=", body):
            fname = fm.group(1)
            if fname not in KNOWN_NON_MODULE_LIB_FIELDS:
                raise RuntimeError(
                    f"@[default_target] lean_lib {name} has unsupported field '{fname} :=' in {lakefile}"
                )

        if re.search(r"\bsrcDir\s*:=", body):
            if not re.search(
                r'\bsrcDir\s*:=\s*(?:generatedLeanSrcDir|"\.GeneratedLean")(?:\s|$)',
                unmasked_body,
            ):
                raise RuntimeError(
                    f"@[default_target] lean_lib {name} has unsupported srcDir in {lakefile}"
                )

        is_static_generated_lean = (
            name == "GeneratedLean"
            and bool(re.search(r"\broots\s*:=\s*generatedLeanModules(?:\s|$)", body))
            and bool(re.search(r"\bglobs\s*:=\s*generatedLeanModules\.map\s+Glob\.one(?:\s|$)", body))
        )

        has_roots_field = bool(re.search(r"\broots\s*:=", body))
        rm = re.search(r"\broots\s*:=\s*#\[(.*?)\]", body, re.S)
        if has_roots_field and rm is None and not is_static_generated_lean:
            raise RuntimeError(
                f"@[default_target] lean_lib {name} has non-literal `roots :=` in {lakefile}"
            )

        has_globs_field = bool(re.search(r"\bglobs\s*:=", body))
        gm = re.search(r"\bglobs\s*:=\s*#\[(.*?)\]", body, re.S)
        if has_globs_field and gm is None and not is_static_generated_lean:
            raise RuntimeError(
                f"@[default_target] lean_lib {name} has non-literal `globs :=` in {lakefile}"
            )

        roots: list[str] = []
        globs: list[tuple[str, str]] = []
        has_literal_empty_roots = False
        if is_static_generated_lean:
            gen_mods = parse_generated_lean_modules_from_lakefile(cleaned, lakefile)
            for gmod in gen_mods:
                if gmod not in all_mods:
                    raise RuntimeError(
                        f"@[default_target] lean_lib {name} static module `{gmod} not found in scanned repo modules"
                    )
                roots.append(gmod)
                globs.append(("one", gmod))
        if rm is not None:
            raw_items = [item.strip() for item in rm.group(1).split(",") if item.strip()]
            if not raw_items:
                has_literal_empty_roots = True
            for item in raw_items:
                im = SINGLE_ROOT_ITEM_RE.match(item)
                if im is None:
                    raise RuntimeError(
                        f"@[default_target] lean_lib {name} has unparseable root item {item!r} in {lakefile}"
                    )
                rmod = im.group(1) if im.group(1) is not None else im.group(2)
                if rmod not in all_mods:
                    raise RuntimeError(
                        f"@[default_target] lean_lib {name} root `{rmod} not found in scanned repo modules"
                    )
                roots.append(rmod)

        if gm is not None:
            raw_gitems = [item.strip() for item in gm.group(1).split(",") if item.strip()]
            for item in raw_gitems:
                gim = SINGLE_GLOB_ITEM_RE.match(item)
                if gim is None:
                    raise RuntimeError(
                        f"@[default_target] lean_lib {name} has unparseable glob item {item!r} in {lakefile}"
                    )
                gkind = gim.group(1)
                gmod = gim.group(2) if gim.group(2) is not None else gim.group(3)
                globs.append((gkind, gmod))

        if rm is None and gm is None and not is_static_generated_lean:
            if name not in all_mods:
                raise RuntimeError(
                    f"@[default_target] lean_lib {name} implicit root `{name} not found in scanned repo modules"
                )
            roots.append(name)

        lib_seeds: set[str] = set(roots)
        for kind, mod in globs:
            if kind == "one":
                if mod not in all_mods:
                    raise RuntimeError(
                        f"@[default_target] lean_lib {name} glob .one `{mod} not found in scanned repo modules"
                    )
                lib_seeds.add(mod)
            else:
                matched = {x for x in all_mods if x.startswith(mod + ".")}
                if kind == "andSubmodules" and mod in all_mods:
                    matched.add(mod)
                if not matched:
                    raise RuntimeError(
                        f"@[default_target] lean_lib {name} glob .{kind} `{mod} matched 0 modules"
                    )
                lib_seeds |= matched

        if not lib_seeds:
            if name in ALLOWED_LITERAL_EMPTY_DEFAULT_LIBS and has_literal_empty_roots and gm is None:
                print(
                    f"DEFAULT_LIB_EMPTY_ALLOWED {name} (literal roots := #[], 0 globs)",
                    flush=True,
                )
                continue
            raise RuntimeError(
                f"@[default_target] lean_lib {name} resolved to 0 seed modules in {lakefile}"
            )

        batches.append(sorted(lib_seeds))

    if parsed_default_count != raw_dt_count:
        raise RuntimeError(
            f"@[default_target] count mismatch in {lakefile}: "
            f"raw @[default_target] attributes={raw_dt_count}, parsed lean_lib declarations={parsed_default_count}"
        )
    if not batches:
        raise RuntimeError(f"parsed 0 default-target seed modules from {lakefile}")
    return batches

def compute_default_target_seeds(repo_root: pathlib.Path) -> list[str]:
    """Flatten `compute_default_target_lib_batches` into a sorted deduplicated seed list."""
    batches = compute_default_target_lib_batches(repo_root)
    return sorted({mod for batch in batches for mod in batch})

IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:public\s+)?(?:meta\s+)?(?:«([^»]+)»|([\w.]+))",
    re.M,
)

def compute_default_target_closure(repo_root: pathlib.Path, seeds: list[str]) -> list[str]:
    """Compute the transitive `.lean` import closure of `seeds` in `repo_root` for `--root-report`."""
    mod_to_file: dict[str, pathlib.Path] = {}
    for top in sorted(repo_root.iterdir()):
        if top.name in SKIP_TOP_DIRS:
            continue
        if top.name == ".GeneratedLean" and top.is_dir():
            for p in top.rglob("*.lean"):
                rel = p.relative_to(top)
                if any(part.startswith(".") for part in rel.parts):
                    continue
                mod_to_file[".".join((*rel.parts[:-1], rel.stem))] = p
            continue
        if top.name.startswith("."):
            continue
        if top.is_file() and top.suffix == ".lean" and top.name != "lakefile.lean":
            mod_to_file[top.stem] = top
        elif top.is_dir():
            for p in top.rglob("*.lean"):
                rel = p.relative_to(repo_root)
                if any(
                    part.startswith(".")
                    or part == "RELEASE_EXCLUDE"
                    or part == "test_fixtures"
                    for part in rel.parts
                ):
                    continue
                mod_to_file[".".join((*rel.parts[:-1], rel.stem))] = p

    seen: set[str] = set()
    stack = list(seeds)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        fp = mod_to_file.get(m)
        if fp is None or not fp.is_file():
            continue
        # Strip comments before matching top-level imports.
        stripped_txt = strip_lean_comments(fp.read_text(encoding="utf-8", errors="replace"))
        for g1, g2 in IMPORT_RE.findall(stripped_txt):
            imp = g1 or g2
            if imp and imp not in seen:
                stack.append(imp)
    return sorted(seen)

def parse_allow_file_header(
    allow_file: pathlib.Path,
) -> tuple[str | None, list[tuple[int, str, str]], str | None, list[tuple[int, str, str]]]:
    """Parse leading `#` header lines and entries of `allow_file`.

    Returns `(engine_pin_or_none, blob_pins, require_tag_or_none, entries)`.
    Raises `ValueError` on conflicting pins or malformed `# blob-pin:` / `# require-tag:` directives.
    """
    raw = allow_file.read_text(encoding="utf-8")
    in_header = True
    pins: list[tuple[int, str]] = []
    blob_pins: list[tuple[int, str, str]] = []
    require_tags: list[tuple[int, str]] = []
    entries: list[tuple[int, str, str]] = []

    for line_no, raw_line in enumerate(raw.splitlines(), start=1):
        stripped = raw_line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            low = stripped.lower()
            if low.startswith("# blob-pin") or low.startswith("#blob-pin"):
                if not in_header:
                    raise ValueError(
                        f"{allow_file}:{line_no}: `# blob-pin:` must appear in leading header before entries"
                    )
                bm = BLOB_PIN_RE.match(stripped)
                if not bm:
                    raise ValueError(
                        f"{allow_file}:{line_no}: malformed `# blob-pin: <path> = <hex>` line: {stripped!r}"
                    )
                blob_pins.append((line_no, bm.group(1), bm.group(2).lower()))
                continue
            if low.startswith("# require-tag") or low.startswith("#require-tag"):
                if not in_header:
                    raise ValueError(
                        f"{allow_file}:{line_no}: `# require-tag:` must appear in leading header before entries"
                    )
                tm = REQUIRE_TAG_RE.match(stripped)
                if not tm:
                    raise ValueError(
                        f"{allow_file}:{line_no}: malformed `# require-tag: <tag>` line: {stripped!r}"
                    )
                require_tags.append((line_no, tm.group(1)))
                continue
            if in_header:
                for pat in ENGINE_PIN_PATTERNS:
                    for m in pat.finditer(stripped):
                        pins.append((line_no, m.group(1).lower()))
            continue

        in_header = False
        parts = stripped.split(":", 1)
        const_str = parts[0].strip()
        reason_str = parts[1].strip() if len(parts) > 1 else ""
        entries.append((line_no, const_str, reason_str))

    canonical_engine: str | None = None
    if pins:
        canonical_engine = pins[0][1]
        for line_no, cand in pins[1:]:
            if canonical_engine.startswith(cand):
                continue
            if cand.startswith(canonical_engine):
                canonical_engine = cand
                continue
            raise ValueError(
                f"conflicting engine pins in {allow_file} header: '{canonical_engine}' vs '{cand}' (line {line_no})"
            )

    req_tag: str | None = None
    if require_tags:
        req_tag = require_tags[0][1]
        for line_no, rt in require_tags[1:]:
            if rt != req_tag:
                raise ValueError(
                    f"conflicting `# require-tag:` in {allow_file} header: '{req_tag}' vs '{rt}' (line {line_no})"
                )

    seen_blob_by_path: dict[str, tuple[int, str]] = {}
    for line_no, rel_path, bpin_hex in blob_pins:
        norm_rel = posixpath.normpath(rel_path)
        prev = seen_blob_by_path.get(norm_rel)
        if prev is not None:
            prev_line, prev_hex = prev
            if prev_hex.startswith(bpin_hex):
                continue
            if bpin_hex.startswith(prev_hex):
                seen_blob_by_path[norm_rel] = (line_no, bpin_hex)
                continue
            raise ValueError(
                f"conflicting `# blob-pin:` for {norm_rel!r} in {allow_file} header: "
                f"'{prev_hex}' (line {prev_line}) vs '{bpin_hex}' (line {line_no})"
            )
        seen_blob_by_path[norm_rel] = (line_no, bpin_hex)

    return canonical_engine, blob_pins, req_tag, entries

def read_repo_engine_gitlink(repo_root: pathlib.Path) -> tuple[str, str | None]:
    """Read `git ls-tree HEAD arm64-semantics` (and submodule `HEAD` if checked out) in `repo_root`."""
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "ls-tree", "HEAD", "arm64-semantics"],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`git -C {repo_root} ls-tree HEAD arm64-semantics` failed (rc={proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    out = proc.stdout.strip()
    m = GITLINK_RE.match(out)
    if not m:
        raise RuntimeError(
            f"unexpected `git ls-tree HEAD arm64-semantics` output in {repo_root}: {out!r}"
        )
    gitlink_sha = m.group(1).lower()

    submod_dir = repo_root / "arm64-semantics"
    submod_sha: str | None = None
    if (submod_dir / ".git").exists():
        sub_proc = subprocess.run(
            ["git", "-C", str(submod_dir), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=False,
        )
        if sub_proc.returncode != 0:
            raise RuntimeError(
                f"`git -C {submod_dir} rev-parse HEAD` failed (rc={sub_proc.returncode}): "
                f"{sub_proc.stderr.strip()}"
            )
        cand = sub_proc.stdout.strip().lower()
        if re.fullmatch(r"[0-9a-f]{40}", cand):
            submod_sha = cand
        else:
            raise RuntimeError(f"unexpected submodule HEAD SHA in {submod_dir}: {cand!r}")

    return gitlink_sha, submod_sha

def read_repo_file_blobs(repo_root: pathlib.Path, rel_path: str) -> tuple[str, str]:
    """Return `(head_blob_sha, worktree_blob_sha)` for `rel_path` in `repo_root`."""
    p_head = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", f"HEAD:{rel_path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if p_head.returncode != 0:
        raise RuntimeError(
            f"`git -C {repo_root} rev-parse HEAD:{rel_path}` failed (rc={p_head.returncode}): "
            f"{p_head.stderr.strip()}"
        )
    head_sha = p_head.stdout.strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", head_sha):
        raise RuntimeError(f"unexpected HEAD blob SHA for {rel_path}: {head_sha!r}")

    wt_file = (repo_root / rel_path).resolve()
    try:
        wt_file.relative_to(repo_root.resolve())
    except ValueError as exc:
        raise RuntimeError(f"blob-pin path escapes repo root: {rel_path}") from exc
    if not wt_file.is_file():
        raise RuntimeError(f"pinned working-tree file does not exist: {wt_file}")

    p_wt = subprocess.run(
        ["git", "-C", str(repo_root), "hash-object", str(wt_file)],
        capture_output=True,
        text=True,
        check=False,
    )
    if p_wt.returncode != 0:
        raise RuntimeError(
            f"`git -C {repo_root} hash-object {wt_file}` failed (rc={p_wt.returncode}): "
            f"{p_wt.stderr.strip()}"
        )
    wt_sha = p_wt.stdout.strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", wt_sha):
        raise RuntimeError(f"unexpected working-tree blob SHA for {rel_path}: {wt_sha!r}")
    return head_sha, wt_sha

def git_hash_object_file(repo_root: pathlib.Path, file_path: pathlib.Path) -> str:
    """Return 40-hex Git blob SHA (`git hash-object`) for `file_path`."""
    resolved = file_path.resolve()
    p_obj = subprocess.run(
        ["git", "-C", str(repo_root), "hash-object", "--", str(resolved)],
        capture_output=True,
        text=True,
        check=False,
    )
    if p_obj.returncode != 0:
        raise RuntimeError(
            f"`git -C {repo_root} hash-object -- {resolved}` failed (rc={p_obj.returncode}): "
            f"{p_obj.stderr.strip()}"
        )
    blob_sha = p_obj.stdout.strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", blob_sha):
        raise RuntimeError(f"unexpected git hash-object output for {resolved}: {blob_sha!r}")
    return blob_sha

def display_list_path(repo_root: pathlib.Path, file_path: pathlib.Path) -> tuple[str, str | None]:
    """Return `(display_path, repo_rel_posix_or_none)` for `file_path` relative to `repo_root`."""
    resolved = file_path.resolve()
    try:
        rel_posix = resolved.relative_to(repo_root.resolve()).as_posix()
        return rel_posix, rel_posix
    except ValueError:
        return str(resolved), None

def verify_deny_files_have_group_markers(
    repo_root: pathlib.Path,
    deny_files: list[pathlib.Path],
    excluded_groups: list[str],
) -> int:
    """When `--exclude-deny-group` is used, fail closed if any `--deny-file` lacks `[group <id>]` markers."""
    if not excluded_groups:
        return 0
    for df in deny_files:
        disp, _ = display_list_path(repo_root, df)
        try:
            raw_lines = df.read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            sys.stderr.write(f"[machine-free-check] error reading deny file {disp}: {exc}\n")
            return 2
        group_count = 0
        for line_no, raw_line in enumerate(raw_lines, 1):
            code = raw_line.split("#", 1)[0].strip()
            if not code:
                continue
            if code.startswith("["):
                if not re.fullmatch(r"\[group\s+[^\s\[\]]+\]", code):
                    sys.stderr.write(
                        f"[machine-free-check] error: {disp}:{line_no}: malformed [group <id>] header '{code}'\n"
                    )
                    return 2
                group_count += 1
            elif group_count == 0:
                sys.stderr.write(
                    f"[machine-free-check] error: --exclude-deny-group cannot be used with unmarked deny file "
                    f"{disp} ({disp}:{line_no}: pattern '{code}' is not inside a '[group <id>]' section; fail-closed)\n"
                )
                return 2
        if group_count == 0:
            sys.stderr.write(
                f"[machine-free-check] error: --exclude-deny-group cannot be used with unmarked deny file "
                f"{disp} (0 '[group <id>]' markers found; fail-closed)\n"
            )
            return 2
    return 0

def emit_and_verify_loaded_lists(
    repo_root: pathlib.Path,
    deny_files: list[pathlib.Path],
    allow_files: list[pathlib.Path],
    exempt_file: pathlib.Path | None,
    cp_path: pathlib.Path | None,
    gate: bool,
    bridges_path: pathlib.Path | None = None,
    expected_type_path: pathlib.Path | None = None,
) -> int:
    """Print list (`git hash-object`) lines; if `gate`, enforce `HEAD:<path>` match across all input files."""
    seen_deny: set[pathlib.Path] = set()
    for df in deny_files:
        r = df.resolve()
        if r in seen_deny:
            sys.stderr.write(f"[machine-free-check] error: duplicate --deny-file path: {df}\n")
            return 2
        seen_deny.add(r)

    seen_allow: set[pathlib.Path] = set()
    for af in allow_files:
        r = af.resolve()
        if r in seen_allow:
            sys.stderr.write(f"[machine-free-check] error: duplicate --allow-file path: {af}\n")
            return 2
        seen_allow.add(r)

    loaded: list[tuple[str, pathlib.Path]] = []
    for df in deny_files:
        loaded.append(("DENY_FILE", df))
    for af in allow_files:
        loaded.append(("ALLOW_FILE", af))
    if exempt_file is not None:
        loaded.append(("EXEMPT_SPECS_FILE", exempt_file))
    if cp_path is not None:
        loaded.append(("PROOFDEPS_FILE", cp_path))
    if bridges_path is not None:
        loaded.append(("BRIDGES_FILE", bridges_path))
    if expected_type_path is not None:
        loaded.append(("EXPECTED_ROOT_TYPE_FILE", expected_type_path))

    entries_info: list[tuple[str, pathlib.Path, str, str | None, str]] = []
    for tag, fpath in loaded:
        try:
            blob_sha = git_hash_object_file(repo_root, fpath)
        except RuntimeError as exc:
            sys.stderr.write(f"[machine-free-check] error hashing {tag} {fpath}: {exc}\n")
            return 2
        disp, rel_posix = display_list_path(repo_root, fpath)
        print(f"{tag} {disp} {blob_sha}", flush=True)
        entries_info.append((tag, fpath, disp, rel_posix, blob_sha))

    if not gate:
        return 0

    p_head = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    if p_head.returncode != 0:
        sys.stderr.write(
            f"[machine-free-check] error resolving HEAD in {repo_root}: {p_head.stderr.strip()}\n"
        )
        return 2
    head_commit = p_head.stdout.strip().lower()

    mismatches: list[str] = []
    for tag, _fpath, disp, rel_posix, blob_sha in entries_info:
        if rel_posix is None:
            mismatches.append(f"{tag} {disp} is outside repository root {repo_root}")
            continue
        p_hb = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--verify", f"HEAD:{rel_posix}"],
            capture_output=True,
            text=True,
            check=False,
        )
        if p_hb.returncode != 0:
            mismatches.append(f"{tag} {rel_posix} (blob={blob_sha}) is not committed at HEAD={head_commit}")
            continue
        head_blob = p_hb.stdout.strip().lower()
        if blob_sha != head_blob:
            mismatches.append(
                f"{tag} {rel_posix} worktree blob={blob_sha} differs from HEAD:{rel_posix} blob={head_blob}"
            )

    if mismatches:
        reason = "; ".join(mismatches)
        print(f"# gate-check: GATE_STATUS=FAIL head={head_commit} ({reason})")
        print("=== SUMMARY ===")
        print("SUMMARY_STATUS=FAIL")
        print("SUMMARY_MACHINE_FREE=no")
        print(f"SUMMARY_GATE_STATUS=FAIL ({reason})")
        sys.stdout.flush()
        return 1

    print(
        f"# gate-check: GATE_STATUS=PASS head={head_commit} verified_lists={len(entries_info)}",
        flush=True,
    )
    return 0

def check_allow_files_pins_and_tags(
    repo_root: pathlib.Path,
    allow_files: list[pathlib.Path],
    gate: bool = False,
    require_blob_pins: bool = False,
) -> int:
    """Verify engine pins, `# blob-pin:` headers, and `# require-tag:` directives across `allow_files`.

    When `require_blob_pins=True` (`--check-pins-only`), requires at least one `# blob-pin:` across
    `allow_files` and prints a `SUMMARY_PINS_ONLY=PASS` summary line when all pins match.
    Returns 0 on pass, 1 on pin mismatch, and 2 on missing/conflicting pins, malformed tags, or git errors.
    """
    seen_engine_pin: tuple[pathlib.Path, str] | None = None
    seen_blob_pins: dict[str, tuple[pathlib.Path, int, str]] = {}
    engine_pins_checked = 0
    total_blob_pins = 0
    pass_blob_pins = 0

    for idx, allow_file in enumerate(allow_files):
        try:
            pin_hex, blob_pins, req_tag, entries = parse_allow_file_header(allow_file)
        except (OSError, ValueError) as exc:
            sys.stderr.write(f"[machine-free-check] error parsing allow-file header: {exc}\n")
            return 2

        entry_count = len(entries)
        if req_tag is not None:
            for line_no, const_str, reason_str in entries:
                if not reason_str.startswith(req_tag):
                    sys.stderr.write(
                        f"[machine-free-check] error: {allow_file}:{line_no}: allow entry '{const_str}' "
                        f"must start reason with required tag {req_tag!r}\n"
                    )
                    return 2
                rest_reason = reason_str[len(req_tag) :].strip()
                if not rest_reason:
                    sys.stderr.write(
                        f"[machine-free-check] error: {allow_file}:{line_no}: allow entry '{const_str}' "
                        f"has tag {req_tag!r} but empty explanation\n"
                    )
                    return 2

        if pin_hex is None and not blob_pins:
            if entry_count == 0 and not gate and not require_blob_pins:
                if idx == 0:
                    print(
                        "# engine-pin-check: ENGINE_PIN_STATUS=SKIP (0 allow entries, no header pin)",
                        flush=True,
                    )
                continue
            sys.stderr.write(
                f"[machine-free-check] error: allow file {allow_file} has {entry_count} entries "
                "but is missing engine submodule commit pin or `# blob-pin:` in leading `#` header (fail-closed)\n"
            )
            return 2

        if pin_hex is not None:
            if seen_engine_pin is not None:
                prev_af, prev_ehex = seen_engine_pin
                if not (prev_ehex.startswith(pin_hex) or pin_hex.startswith(prev_ehex)):
                    sys.stderr.write(
                        f"[machine-free-check] error: conflicting engine pins across allow-files: "
                        f"{prev_af} ('{prev_ehex}') vs {allow_file} ('{pin_hex}')\n"
                    )
                    return 2
                if len(pin_hex) > len(prev_ehex):
                    seen_engine_pin = (allow_file, pin_hex)
            else:
                seen_engine_pin = (allow_file, pin_hex)

            try:
                gitlink_sha, submod_sha = read_repo_engine_gitlink(repo_root)
            except RuntimeError as exc:
                sys.stderr.write(
                    f"[machine-free-check] error checking arm64-semantics gitlink: {exc}\n"
                )
                return 2

            gitlink_ok = gitlink_sha.startswith(pin_hex)
            submod_ok = (submod_sha is None) or (submod_sha == gitlink_sha)
            sub_disp = submod_sha if submod_sha is not None else "n/a"

            if gitlink_ok and submod_ok:
                engine_pins_checked += 1
                print(
                    f"# engine-pin-check: ENGINE_PIN_STATUS=PASS allow_pin={pin_hex} "
                    f"gitlink_head={gitlink_sha} submodule_head={sub_disp}",
                    flush=True,
                )
            else:
                reason_parts: list[str] = []
                if not gitlink_ok:
                    reason_parts.append(
                        f"allow_pin={pin_hex} does not match git ls-tree HEAD arm64-semantics={gitlink_sha}"
                    )
                if not submod_ok:
                    reason_parts.append(
                        f"submodule HEAD={sub_disp} does not match gitlink HEAD={gitlink_sha}"
                    )
                reason_str = "; ".join(reason_parts)
                print(
                    f"# engine-pin-check: ENGINE_PIN_STATUS=FAIL allow_pin={pin_hex} "
                    f"gitlink_head={gitlink_sha} submodule_head={sub_disp}"
                )
                print("=== SUMMARY ===")
                print("SUMMARY_STATUS=FAIL")
                print("SUMMARY_MACHINE_FREE=no")
                print(f"SUMMARY_ENGINE_PIN_STATUS=FAIL ({reason_str})")
                sys.stdout.flush()
                return 1

        for line_no, rel_path, bpin_hex in blob_pins:
            total_blob_pins += 1
            norm_rel = posixpath.normpath(rel_path)
            prev_b = seen_blob_pins.get(norm_rel)
            if prev_b is not None:
                prev_af, prev_ln, prev_bhex = prev_b
                if not (prev_bhex.startswith(bpin_hex) or bpin_hex.startswith(prev_bhex)):
                    sys.stderr.write(
                        f"[machine-free-check] error: conflicting `# blob-pin:` for {norm_rel!r} across allow-files: "
                        f"{prev_af}:{prev_ln} ('{prev_bhex}') vs {allow_file}:{line_no} ('{bpin_hex}')\n"
                    )
                    return 2
                if len(bpin_hex) > len(prev_bhex):
                    seen_blob_pins[norm_rel] = (allow_file, line_no, bpin_hex)
            else:
                seen_blob_pins[norm_rel] = (allow_file, line_no, bpin_hex)

            try:
                head_sha, wt_sha = read_repo_file_blobs(repo_root, rel_path)
            except RuntimeError as exc:
                sys.stderr.write(
                    f"[machine-free-check] error checking blob-pin ({allow_file}:{line_no}): {exc}\n"
                )
                return 2

            head_ok = head_sha.startswith(bpin_hex)
            wt_ok = wt_sha == head_sha and wt_sha.startswith(bpin_hex)
            if head_ok and wt_ok:
                pass_blob_pins += 1
                print(
                    f"# blob-pin-check: BLOB_PIN_STATUS=PASS path={rel_path} "
                    f"allow_pin={bpin_hex} head_blob={head_sha} worktree_blob={wt_sha}",
                    flush=True,
                )
            else:
                reasons: list[str] = []
                if not head_ok:
                    reasons.append(
                        f"path={rel_path} allow_pin={bpin_hex} does not match HEAD blob={head_sha}"
                    )
                if wt_sha != head_sha:
                    reasons.append(
                        f"path={rel_path} working-tree blob={wt_sha} differs from HEAD blob={head_sha}"
                    )
                r_str = "; ".join(reasons)
                print(
                    f"# blob-pin-check: BLOB_PIN_STATUS=FAIL path={rel_path} "
                    f"allow_pin={bpin_hex} head_blob={head_sha} worktree_blob={wt_sha}"
                )
                print("=== SUMMARY ===")
                print("SUMMARY_STATUS=FAIL")
                print("SUMMARY_MACHINE_FREE=no")
                print(f"SUMMARY_BLOB_PIN_STATUS=FAIL ({r_str})")
                sys.stdout.flush()
                return 1

    if require_blob_pins:
        if total_blob_pins == 0 or pass_blob_pins != total_blob_pins:
            sys.stderr.write(
                f"[machine-free-check] error: --check-pins-only non-vacuity check failed "
                f"(total_blob_pins={total_blob_pins}, pass_blob_pins={pass_blob_pins}; expected >= 1 and equal)\n"
            )
            return 2
        print(
            f"# pins-only-check: SUMMARY_PINS_ONLY=PASS allow_files={len(allow_files)} "
            f"engine_pins={engine_pins_checked} blob_pins={pass_blob_pins}",
            flush=True,
        )

    return 0

def build_emit_header_metadata() -> str:
    """Build the `#` header written above the generated `--emit-proofdeps` deny list.

    `--check-proofdeps` ignores this header and recomputes the body directly from the loaded
    deny, allow, and exempt lists.
    """
    lines = [
        "# Generated Part-C proof-dependency deny list (`Symbolic/scripts/machine_free_deny_proofdeps.txt`).",
        "# Covers every machine-level module outside A ∪ B ∪ E under the transitive constant-cone",
        "# fixed-point criterion (`Symbolic/scripts/machine_free_check.py --emit-proofdeps`).",
        "# Do not edit the body by hand: regenerate it with `--emit-proofdeps`. CI's `--check-proofdeps`",
        "# recomputes the body from the deny/allow/exempt lists on every run; this header is not compared.",
    ]
    return "\n".join(lines) + "\n"

def build_merged_arm64_dir(repo_root: pathlib.Path, tmp_root: pathlib.Path) -> pathlib.Path | None:
    """Merge split `Arm64` `.olean` roots (`Arm64.Trusted.*` and `Arm64.Testing.*`) if both exist."""
    nested = repo_root / "arm64-semantics" / "Arm64" / ".lake" / "build" / "lib" / "lean"
    engine = repo_root / "arm64-semantics" / "Arm64" / "Testing" / ".lake" / "build" / "lib" / "lean"
    nested_arm = nested / "Arm64"
    engine_arm = engine / "Arm64"
    if not (nested_arm.is_dir() and engine_arm.is_dir()):
        return None

    merged = tmp_root / "merged_arm64"
    merged_arm = merged / "Arm64"
    merged_arm.mkdir(parents=True, exist_ok=True)

    for top_entry in sorted(nested.glob("Arm64.*")):
        os.symlink(top_entry.resolve(), merged / top_entry.name)

    for src_dir, is_nested in ((nested_arm, True), (engine_arm, False)):
        for entry in sorted(src_dir.iterdir()):
            if is_nested and entry.is_symlink():
                eng_peer = engine_arm / entry.name
                if eng_peer.exists() and entry.resolve() == eng_peer.resolve():
                    continue
            dst = merged_arm / entry.name
            if dst.exists() or dst.is_symlink():
                raise RuntimeError(
                    f"both halves of Arm64 contain '{entry.name}': {nested_arm} vs {engine_arm}"
                )
            os.symlink(entry.resolve(), dst)

    return merged

def query_lake_env(repo_root: pathlib.Path) -> tuple[str, str]:
    """Return `(lean_bin, lean_path)` from `lake env` in `repo_root`."""
    cmd = [
        "lake",
        "env",
        "python3",
        "-c",
        "import os, shutil; print(shutil.which('lean') or ''); print(os.environ.get('LEAN_PATH', ''))",
    ]
    proc = subprocess.run(
        cmd,
        cwd=str(repo_root),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(
            f"[machine-free-check] error: `lake env` failed in {repo_root} (rc={proc.returncode}):\n"
            f"{proc.stderr}"
        )
        sys.exit(2)
    lines = proc.stdout.splitlines()
    lean_bin = lines[0].strip() if len(lines) >= 1 else ""
    lean_path = lines[1].strip() if len(lines) >= 2 else ""
    if not lean_bin or not lean_path:
        sys.stderr.write(
            f"[machine-free-check] error: empty lean binary or LEAN_PATH from `lake env` in {repo_root}\n"
        )
        sys.exit(2)
    return lean_bin, lean_path

def ensure_compiled_mfc_binary(lean_bin: str, lean_script: pathlib.Path) -> pathlib.Path | None:
    """Compile `MachineFreeCheck.lean` with `lean -c` and `leanc -O2 -rdynamic` into a UID-owned `0700` cache.

    Native compilation avoids Lean VM interpreter overhead during full-environment `Expr` traversals.
    Returns `None` if `leanc` is not present alongside `lean_bin`, in which case callers use `lean --run`.
    """
    lean_bin_path = pathlib.Path(lean_bin).resolve()
    leanc_bin = lean_bin_path.parent / "leanc"
    if not leanc_bin.is_file():
        return None

    uid = os.getuid()
    lb_stat = lean_bin_path.stat()
    lc_stat = leanc_bin.stat()
    key_h = hashlib.sha256()
    key_h.update(f"{lean_bin_path}:{lb_stat.st_size}:{lb_stat.st_mtime_ns}".encode("utf-8"))
    key_h.update(b"\0")
    key_h.update(f"{leanc_bin}:{lc_stat.st_size}:{lc_stat.st_mtime_ns}".encode("utf-8"))
    key_h.update(b"\0")
    key_h.update(lean_script.read_bytes())
    cache_key = key_h.hexdigest()[:24]

    tmp_base = os.environ.get("TMPDIR")
    if tmp_base and pathlib.Path(tmp_base).is_dir():
        cache_root = pathlib.Path(tmp_base) / f"mfc_native_cache_{uid}"
    else:
        cache_root = pathlib.Path(tempfile.gettempdir()) / f"mfc_native_cache_{uid}"
    cache_root.mkdir(mode=0o700, parents=True, exist_ok=True)
    c_stat = cache_root.lstat()
    if stat.S_ISLNK(c_stat.st_mode) or not stat.S_ISDIR(c_stat.st_mode) or c_stat.st_uid != uid:
        raise RuntimeError(
            f"unsafe native cache directory {cache_root} (uid={c_stat.st_uid}, expected uid={uid})"
        )
    if (c_stat.st_mode & 0o777) != 0o700:
        cache_root.chmod(0o700)

    def _valid_cached_bin(p: pathlib.Path) -> bool:
        try:
            st = p.lstat()
        except FileNotFoundError:
            return False
        if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode) or st.st_uid != uid:
            raise RuntimeError(f"unsafe cached binary {p} (uid={st.st_uid}, expected uid={uid})")
        return os.access(p, os.X_OK)

    out_bin = cache_root / f"mfc_{cache_key}"
    if _valid_cached_bin(out_bin):
        return out_bin

    cc_env = os.environ.copy()
    cc_env["LEAN_ABORT_ON_PANIC"] = "1"

    lock_path = cache_root / f"mfc_{cache_key}.lock"
    with lock_path.open("w", encoding="utf-8") as lock_fh:
        fcntl.flock(lock_fh.fileno(), fcntl.LOCK_EX)
        if _valid_cached_bin(out_bin):
            return out_bin

        build_dir = pathlib.Path(tempfile.mkdtemp(prefix=f"mfc_build_{cache_key}_", dir=str(cache_root)))
        try:
            c_path = build_dir / "mfc.c"
            tmp_bin = build_dir / "mfc_bin"
            p_c = subprocess.run(
                [
                    str(lean_bin_path),
                    "-R",
                    str(lean_script.parent.resolve()),
                    "-c",
                    str(c_path),
                    str(lean_script.resolve()),
                ],
                env=cc_env,
                capture_output=True,
                text=True,
                check=False,
            )
            if p_c.returncode != 0:
                sys.stderr.write(
                    f"[machine-free-check] error compiling {lean_script} to C (rc={p_c.returncode}):\n"
                    f"{p_c.stderr or p_c.stdout}\n"
                )
                sys.exit(2)

            p_cc = subprocess.run(
                [str(leanc_bin), "-O2", "-rdynamic", str(c_path), "-o", str(tmp_bin)],
                env=cc_env,
                capture_output=True,
                text=True,
                check=False,
            )
            if p_cc.returncode != 0:
                sys.stderr.write(
                    f"[machine-free-check] error linking {c_path} with leanc (rc={p_cc.returncode}):\n"
                    f"{p_cc.stderr or p_cc.stdout}\n"
                )
                sys.exit(2)

            tmp_bin.chmod(0o700)
            os.replace(tmp_bin, out_bin)
            return out_bin
        finally:
            shutil.rmtree(build_dir, ignore_errors=True)

def _set_child_stack_limit() -> None:
    """Ensure 512 MiB stack soft limit for deep `Expr` / `.olean` deserialization."""
    target = 524288 * 1024
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        if hard == resource.RLIM_INFINITY or hard >= target:
            new_soft = target
        else:
            new_soft = hard
        if soft != resource.RLIM_INFINITY and soft < new_soft:
            resource.setrlimit(resource.RLIMIT_STACK, (new_soft, hard))
    except (ValueError, OSError):
        pass

def run_self_test(repo_root: pathlib.Path, lean_script: pathlib.Path, deny_file: pathlib.Path) -> int:
    """Verify fail-closed rejection of malformed/wildcard/module/prefix/group/pin inputs."""
    lean_bin, lean_path = query_lake_env(repo_root)
    native_bin = ensure_compiled_mfc_binary(lean_bin, lean_script)
    gitlink_sha, _ = read_repo_engine_gitlink(repo_root)
    tr_head_sha, _ = read_repo_file_blobs(
        repo_root, "LibsignalBinary/Specifications/LibsignalTripleRatchet.lean"
    )
    env = os.environ.copy()
    env["LEAN_PATH"] = lean_path
    env["LEAN_ABORT_ON_PANIC"] = "1"
    env.setdefault("LEAN_NUM_THREADS", "2")

    tmp_dir = pathlib.Path(tempfile.mkdtemp(prefix="mfc_selftest_"))
    try:
        empty_deny = tmp_dir / "empty_deny.txt"
        empty_deny.write_text("# comment only\n", encoding="utf-8")

        ungrouped_deny = tmp_dir / "ungrouped_deny.txt"
        ungrouped_deny.write_text("Arm64.*\n[group 1]\nProofLib.*\n", encoding="utf-8")

        cur_grp = None
        total_df_pats = 0
        g5_df_pats = 0
        for raw_ln in deny_file.read_text(encoding="utf-8").splitlines():
            s_ln = raw_ln.strip()
            if not s_ln or s_ln.startswith("#"):
                continue
            if s_ln.startswith("[group ") and s_ln.endswith("]"):
                cur_grp = s_ln[len("[group ") : -1].strip()
                continue
            total_df_pats += 1
            if cur_grp == "5":
                g5_df_pats += 1
        assert g5_df_pats > 0, f"expected [group 5] patterns in {deny_file}"
        exp_excl_g5 = f"deny_patterns={total_df_pats - g5_df_pats}"

        cases: list[tuple[str, pathlib.Path, str, list[str], int, str]] = [
            ("empty_deny", empty_deny, "", [], 2, "deny list is empty"),
            ("missing_reason", deny_file, "Arm64.FsPath\n", [], 2, "allow entry must be"),
            ("wildcard_allow", deny_file, "Arm64.* : wildcard\n", [], 2, "invalid allow entry"),
            ("trailing_dot_prefix", deny_file, "Arm64.Process. : prefix\n", [], 2, "invalid allow entry"),
            ("top_pkg_prefix", deny_file, "Arm64 : top package\n", [], 2, "top-level package/prefix"),
            ("denied_prefix_exact", deny_file, "ProofLib : denied prefix\n", [], 2, "top-level package/prefix"),
            ("module_name_in_env", deny_file, "Init.Core : module name\n", [], 2, "module or module prefix"),
            ("namespace_prefix_in_env", deny_file, "Lean.Internal : namespace prefix\n", [], 2, "namespace/prefix"),
            ("stale_unreached_allow", deny_file, "Nat.succ_ne_zero : unreached\n", [], 1, "SUMMARY_UNREACHED_ALLOW=1"),
            ("clean_no_allow", deny_file, "", [], 0, "MACHINE_FREE=yes"),
            ("ungrouped_before_group", ungrouped_deny, "", [], 2, "precedes first [group"),
            ("exclude_missing_group", deny_file, "", ["--exclude-deny-group", "99"], 2, "not found in any --deny-file"),
            ("exclude_group_5_ok", deny_file, "", ["--exclude-deny-group", "5"], 0, exp_excl_g5),
        ]

        for name, df, allow_txt, extra_args, exp_rc, needle in cases:
            af = tmp_dir / f"{name}_allow.txt"
            af.write_text(allow_txt, encoding="utf-8")
            if native_bin is not None:
                cmd = [str(native_bin)]
            else:
                cmd = [lean_bin, "-s", "524288", "-M", "4096", "--run", str(lean_script)]
            cmd.extend([
                "--deny-file",
                str(df),
                *extra_args,
                "--allow-file",
                str(af),
                "Init.Core",
                "Bool.true",
            ])
            proc = subprocess.run(
                cmd,
                cwd=str(repo_root),
                env=env,
                capture_output=True,
                text=True,
                check=False,
                preexec_fn=_set_child_stack_limit,
            )
            combined = (proc.stdout or "") + "\n" + (proc.stderr or "")
            if proc.returncode != exp_rc or needle not in combined:
                sys.stderr.write(
                    f"[self-test] FAIL case={name}: expected rc={exp_rc} needle={needle!r}, "
                    f"got rc={proc.returncode}\n{combined}\n"
                )
                return 1
            print(f"[self-test] PASS {name}: rc={proc.returncode} matched {needle!r}")

        pin_cases: list[tuple[str, str, list[str], int, str]] = [
            (
                "engine_pin_match",
                f"# read at engine submodule {gitlink_sha[:9]}\n",
                [],
                0,
                "ENGINE_PIN_STATUS=PASS",
            ),
            (
                "engine_pin_mismatch",
                "# read at engine submodule 000000000\n",
                [],
                1,
                "SUMMARY_ENGINE_PIN_STATUS=FAIL",
            ),
            (
                "engine_pin_missing_header",
                "# header without pin\nNat.succ_ne_zero : entry\n",
                [],
                2,
                "missing engine submodule commit pin",
            ),
            (
                "blob_pin_match",
                f"# blob-pin: LibsignalBinary/Specifications/LibsignalTripleRatchet.lean = {tr_head_sha[:12]}\n",
                [],
                0,
                "BLOB_PIN_STATUS=PASS",
            ),
            (
                "blob_pin_mismatch",
                "# blob-pin: LibsignalBinary/Specifications/LibsignalTripleRatchet.lean = 000000000\n",
                [],
                1,
                "SUMMARY_BLOB_PIN_STATUS=FAIL",
            ),
            (
                "require_tag_missing",
                f"# blob-pin: LibsignalBinary/Specifications/LibsignalTripleRatchet.lean = {tr_head_sha}\n"
                "# require-tag: [MODEL]\n"
                "Nat.succ_ne_zero : missing tag reason\n",
                ["--subset-allow"],
                2,
                "must start reason with required tag '[MODEL]'",
            ),
            (
                "list_blobs_printed",
                f"# read at engine submodule {gitlink_sha[:9]}\n",
                [],
                0,
                "ALLOW_FILE ",
            ),
            (
                "gate_fail_uncommitted_allow",
                f"# read at engine submodule {gitlink_sha[:9]}\n",
                ["--gate"],
                1,
                "SUMMARY_GATE_STATUS=FAIL",
            ),
            (
                "gate_rejects_no_allow",
                f"# read at engine submodule {gitlink_sha[:9]}\n",
                ["--gate", "--no-allow"],
                2,
                "--gate cannot be combined with",
            ),
        ]
        self_script = pathlib.Path(__file__).resolve()
        for name, allow_txt, extra_wargs, exp_rc, needle in pin_cases:
            af = tmp_dir / f"{name}_allow.txt"
            af.write_text(allow_txt, encoding="utf-8")
            wcmd = [
                sys.executable,
                str(self_script),
                "--root",
                str(repo_root),
                "--deny-file",
                str(deny_file),
                "--allow-file",
                str(af),
                *extra_wargs,
                "--max-memory-mib",
                "4096",
                "Init.Core",
                "Bool.true",
            ]
            proc = subprocess.run(
                wcmd, cwd=str(repo_root), env=env, capture_output=True, text=True, check=False
            )
            combined = (proc.stdout or "") + "\n" + (proc.stderr or "")
            if proc.returncode != exp_rc or needle not in combined:
                sys.stderr.write(
                    f"[self-test] FAIL case={name}: expected rc={exp_rc} needle={needle!r}, "
                    f"got rc={proc.returncode}\n{combined}\n"
                )
                return 1
            if name == "list_blobs_printed":
                exp_df_sha = git_hash_object_file(repo_root, deny_file)
                exp_af_sha = git_hash_object_file(repo_root, af)
                if exp_df_sha not in (proc.stdout or "") or exp_af_sha not in (proc.stdout or ""):
                    sys.stderr.write(
                        f"[self-test] FAIL case={name}: missing DENY_FILE/ALLOW_FILE git hash-object SHAs\n{combined}\n"
                    )
                    return 1
            print(f"[self-test] PASS {name}: rc={proc.returncode} matched {needle!r}")

        # Gate check rejects an uncommitted --deny-file paired with a committed --allow-file.
        committed_allow = repo_root / "Symbolic" / "scripts" / "machine_free_allow.txt"
        uncommitted_deny = tmp_dir / "gate_uncommitted_deny.txt"
        uncommitted_deny.write_text(deny_file.read_text(encoding="utf-8"), encoding="utf-8")
        gcmd = [
            sys.executable,
            str(self_script),
            "--root",
            str(repo_root),
            "--gate",
            "--deny-file",
            str(uncommitted_deny),
            "--allow-file",
            str(committed_allow),
            "--subset-allow",
            "--max-memory-mib",
            "4096",
            "Init.Core",
            "Bool.true",
        ]
        gproc = subprocess.run(
            gcmd, cwd=str(repo_root), env=env, capture_output=True, text=True, check=False
        )
        gcomb = (gproc.stdout or "") + "\n" + (gproc.stderr or "")
        if gproc.returncode != 1 or "SUMMARY_GATE_STATUS=FAIL" not in gcomb:
            sys.stderr.write(
                f"[self-test] FAIL case=gate_fail_uncommitted_deny: expected rc=1 SUMMARY_GATE_STATUS=FAIL, "
                f"got rc={gproc.returncode}\n{gcomb}\n"
            )
            return 1
        print("[self-test] PASS gate_fail_uncommitted_deny: rc=1 matched 'SUMMARY_GATE_STATUS=FAIL'")

        # --exclude-deny-group fails closed on an unmarked deny file.
        unmarked_deny = tmp_dir / "unmarked_deny.txt"
        unmarked_deny.write_text("# unmarked deny list\nArm64.*\n", encoding="utf-8")
        ugcmd = [
            sys.executable,
            str(self_script),
            "--root",
            str(repo_root),
            "--gate",
            "--deny-file",
            str(unmarked_deny),
            "--exclude-deny-group",
            "5",
            "--allow-file",
            str(committed_allow),
            "--subset-allow",
            "--max-memory-mib",
            "4096",
            "Init.Core",
            "Bool.true",
        ]
        ugproc = subprocess.run(
            ugcmd, cwd=str(repo_root), env=env, capture_output=True, text=True, check=False
        )
        ugcomb = (ugproc.stdout or "") + "\n" + (ugproc.stderr or "")
        if ugproc.returncode != 2 or "cannot be used with unmarked deny file" not in ugcomb:
            sys.stderr.write(
                f"[self-test] FAIL case=gate_rejects_exclude_group_on_unmarked_deny: expected rc=2 "
                f"'cannot be used with unmarked deny file', got rc={ugproc.returncode}\n{ugcomb}\n"
            )
            return 1
        print(
            "[self-test] PASS gate_rejects_exclude_group_on_unmarked_deny: "
            "rc=2 matched 'cannot be used with unmarked deny file'"
        )

        # Direct Lean binary rejects --one-step with --emit-proofdeps or --check-proofdeps.
        dummy_exempt = tmp_dir / "selftest_exempt.txt"
        dummy_exempt.write_text("# empty\n", encoding="utf-8")
        dummy_seeds = tmp_dir / "selftest_seeds.txt"
        dummy_seeds.write_text("Init.Core\n", encoding="utf-8")
        dummy_cp = tmp_dir / "selftest_cp.txt"
        dummy_cp.write_text("[group proofdeps]\nArm64.*\n", encoding="utf-8")
        for sub_name, mode_args in (
            ("lean_rejects_onestep_emit", ["--emit-proofdeps", str(tmp_dir / "out_c.txt")]),
            ("lean_rejects_onestep_check", ["--check-proofdeps", str(dummy_cp)]),
        ):
            if native_bin is not None:
                lcmd = [str(native_bin)]
            else:
                lcmd = [lean_bin, "-s", "524288", "-M", "4096", "--run", str(lean_script)]
            lcmd.extend([
                "--deny-file",
                str(deny_file),
                "--no-allow",
                "--exempt-specs-file",
                str(dummy_exempt),
                "--default-target-seeds-file",
                str(dummy_seeds),
                "--one-step",
                *mode_args,
            ])
            lproc = subprocess.run(
                lcmd,
                cwd=str(repo_root),
                env=env,
                capture_output=True,
                text=True,
                check=False,
                preexec_fn=_set_child_stack_limit,
            )
            lcomb = (lproc.stdout or "") + "\n" + (lproc.stderr or "")
            exp_lean_msg = "--one-step cannot be combined with --emit-proofdeps or --check-proofdeps"
            if lproc.returncode != 2 or exp_lean_msg not in lcomb:
                sys.stderr.write(
                    f"[self-test] FAIL case={sub_name}: expected rc=2 {exp_lean_msg!r}, "
                    f"got rc={lproc.returncode}\n{lcomb}\n"
                )
                return 1
            print(f"[self-test] PASS {sub_name}: rc=2 matched {exp_lean_msg!r}")

        if run_pin_self_test() != 0:
            return 1

        total = len(cases) + len(pin_cases) + 4
        print(f"[self-test] ALL {total} CASES PASSED")
        return 0
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def run_pin_self_test() -> int:
    """Run git-only positive and negative self-tests for `--check-pins-only`."""
    git_env = os.environ.copy()
    git_env["GIT_OPTIONAL_LOCKS"] = "0"
    git_env["GIT_AUTHOR_NAME"] = "Test"
    git_env["GIT_AUTHOR_EMAIL"] = "test@example.com"
    git_env["GIT_COMMITTER_NAME"] = "Test"
    git_env["GIT_COMMITTER_EMAIL"] = "test@example.com"

    with tempfile.TemporaryDirectory(prefix="mfc_pin_selftest_") as td:
        root = pathlib.Path(td)

        def _git(*gargs: str) -> str:
            proc = subprocess.run(
                ["git", "-c", "maintenance.auto=false", "-c", "gc.auto=0", "-C", str(root), *gargs],
                env=git_env,
                capture_output=True,
                text=True,
                check=True,
            )
            return proc.stdout.strip()

        _git("init", "-q")
        (root / "Symbolic" / "scripts").mkdir(parents=True)
        (root / "Spec").mkdir(parents=True)
        spec_a = root / "Spec" / "A.lean"
        spec_b = root / "Spec" / "B.lean"
        spec_a.write_text("def a : Nat := 1\n", encoding="utf-8")
        spec_b.write_text("def b : Nat := 2\n", encoding="utf-8")
        (root / "Symbolic" / "scripts" / "MachineFreeCheck.lean").write_text("-- stub\n", encoding="utf-8")
        (root / "Symbolic" / "scripts" / "machine_free_deny.txt").write_text("[group 1]\nArm64.*\n", encoding="utf-8")

        engine_sha = "da33279f59111111111111111111111111111111"
        other_engine_sha = "deadbeef00222222222222222222222222222222"
        _git("add", "Spec/A.lean", "Spec/B.lean", "Symbolic/scripts/MachineFreeCheck.lean", "Symbolic/scripts/machine_free_deny.txt")
        _git("update-index", "--add", "--cacheinfo", f"160000,{engine_sha},arm64-semantics")
        _git("commit", "-q", "-m", "seed")

        sha_a = _git("rev-parse", "HEAD:Spec/A.lean")
        sha_b = _git("rev-parse", "HEAD:Spec/B.lean")

        allow_main = root / "Symbolic" / "scripts" / "machine_free_allow.txt"
        allow_pd = root / "Symbolic" / "scripts" / "machine_free_allow_proofdeps.txt"
        allow_q1 = root / "Symbolic" / "scripts" / "machine_free_allow_proofdeps_q1.txt"
        allow_main.write_text(f"# read at engine submodule {engine_sha[:10]}\nFoo.bar : reason\n", encoding="utf-8")
        allow_pd.write_text(
            f"# blob-pin: Spec/A.lean = {sha_a[:12]}\n"
            f"# blob-pin: Spec/B.lean = {sha_b}\n"
            "# require-tag: [MODEL]\n"
            "Foo.baz : [MODEL] pure model helper\n",
            encoding="utf-8",
        )
        allow_q1.write_text(
            f"# Pinned engine submodule: arm64-semantics @ {engine_sha}\n"
            f"# blob-pin: Spec/A.lean = {sha_a}\n"
            "# require-tag: [MODEL]\n"
            "Foo.qux : [MODEL] pure q1 helper\n",
            encoding="utf-8",
        )
        _git(
            "add",
            "Symbolic/scripts/machine_free_allow.txt",
            "Symbolic/scripts/machine_free_allow_proofdeps.txt",
            "Symbolic/scripts/machine_free_allow_proofdeps_q1.txt",
        )
        _git("commit", "-q", "-m", "add allowlists")

        def _invoke(cli_args: list[str]) -> tuple[int, str, str]:
            out_buf = io.StringIO()
            err_buf = io.StringIO()
            with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                rc = main(["--root", str(root), *cli_args])
            return rc, out_buf.getvalue(), err_buf.getvalue()

        def _expect(case_name: str, cli_args: list[str], exp_rc: int, needle: str) -> bool:
            rc, out_s, err_s = _invoke(cli_args)
            comb = out_s + "\n" + err_s
            if rc != exp_rc or needle not in comb:
                sys.stderr.write(
                    f"[pin-self-test] FAIL case={case_name}: expected rc={exp_rc} needle={needle!r}, "
                    f"got rc={rc}\n{comb}\n"
                )
                return False
            print(f"[pin-self-test] PASS {case_name}: rc={rc} matched {needle!r}")
            return True

        # Default 3-file `--gate --check-pins-only` positive case (3 blob pins, 2 engine pins).
        rc0, out0, err0 = _invoke(["--gate", "--check-pins-only"])
        if (
            rc0 != 0
            or out0.count("BLOB_PIN_STATUS=PASS") != 3
            or out0.count("ENGINE_PIN_STATUS=PASS") != 2
            or "SUMMARY_PINS_ONLY=PASS allow_files=3 engine_pins=2 blob_pins=3" not in out0
        ):
            sys.stderr.write(
                f"[pin-self-test] FAIL case=blob_pin_match_gate_defaults: rc={rc0}\n{out0}\n{err0}\n"
            )
            return 1
        print("[pin-self-test] PASS blob_pin_match_gate_defaults: rc=0 (3 blob_pins, 2 engine_pins)")

        # Dirty and missing working-tree pinned files.
        orig_a = spec_a.read_text(encoding="utf-8")
        try:
            spec_a.write_text("def a : Nat := 999\n", encoding="utf-8")
            if not _expect(
                "blob_pin_mismatch_dirty_worktree",
                ["--gate", "--check-pins-only"],
                1,
                "SUMMARY_BLOB_PIN_STATUS=FAIL",
            ):
                return 1
            spec_a.unlink()
            if not _expect(
                "missing_pinned_file_in_worktree",
                ["--gate", "--check-pins-only"],
                2,
                "pinned working-tree file does not exist",
            ):
                return 1
        finally:
            spec_a.write_text(orig_a, encoding="utf-8")

        # Uncommitted allow-file under --gate, plus malformed and mismatch cases.
        scratch_dir = pathlib.Path(tempfile.mkdtemp(prefix="mfc_pin_cases_"))
        try:
            uncommitted_af = scratch_dir / "uncommitted_allow.txt"
            uncommitted_af.write_text(
                f"# blob-pin: Spec/A.lean = {sha_a}\n", encoding="utf-8"
            )
            if not _expect(
                "gate_fail_uncommitted_allow",
                ["--gate", "--check-pins-only", "--allow-file", str(uncommitted_af)],
                1,
                "SUMMARY_GATE_STATUS=FAIL",
            ):
                return 1

            neg_cases: list[tuple[str, list[str], int, str]] = []

            def _mk_af(fname: str, content: str) -> str:
                p = scratch_dir / fname
                p.write_text(content, encoding="utf-8")
                return str(p)

            neg_cases.extend([
                (
                    "blob_pin_mismatch",
                    ["--check-pins-only", "--allow-file", _mk_af("bad_blob.txt", "# blob-pin: Spec/A.lean = 000000000000\n")],
                    1,
                    "SUMMARY_BLOB_PIN_STATUS=FAIL",
                ),
                (
                    "engine_pin_mismatch",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af(
                            "bad_eng.txt",
                            f"# arm64-semantics @ {other_engine_sha[:10]}\n# blob-pin: Spec/A.lean = {sha_a}\n",
                        ),
                    ],
                    1,
                    "SUMMARY_ENGINE_PIN_STATUS=FAIL",
                ),
                (
                    "missing_pinned_file_in_head",
                    ["--check-pins-only", "--allow-file", _mk_af("missing_head.txt", "# blob-pin: Spec/Missing.lean = deadbeef\n")],
                    2,
                    "rev-parse HEAD:Spec/Missing.lean",
                ),
                (
                    "malformed_blob_pin",
                    ["--check-pins-only", "--allow-file", _mk_af("mal_blob.txt", "# blob-pin: Spec/A.lean\n")],
                    2,
                    "malformed `# blob-pin:",
                ),
                (
                    "malformed_require_tag",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af("mal_tag.txt", f"# blob-pin: Spec/A.lean = {sha_a}\n# require-tag:\n"),
                    ],
                    2,
                    "malformed `# require-tag:",
                ),
                (
                    "require_tag_missing_on_entry",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af(
                            "no_tag.txt",
                            f"# blob-pin: Spec/A.lean = {sha_a}\n# require-tag: [MODEL]\nFoo.bar : untagged\n",
                        ),
                    ],
                    2,
                    "must start reason with required tag '[MODEL]'",
                ),
                (
                    "require_tag_empty_explanation",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af(
                            "empty_exp.txt",
                            f"# blob-pin: Spec/A.lean = {sha_a}\n# require-tag: [MODEL]\nFoo.bar : [MODEL]   \n",
                        ),
                    ],
                    2,
                    "empty explanation",
                ),
                (
                    "conflicting_blob_pin_intra_file",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af(
                            "intra_conflict.txt",
                            f"# blob-pin: Spec/A.lean = {sha_a[:12]}\n# blob-pin: ./Spec/A.lean = 000000000000\n",
                        ),
                    ],
                    2,
                    "conflicting `# blob-pin:`",
                ),
                (
                    "conflicting_blob_pin_cross_file",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af("cross_b1.txt", f"# blob-pin: Spec/A.lean = {sha_a}\n"),
                        "--allow-file",
                        _mk_af("cross_b2.txt", "# blob-pin: Spec/A.lean = 000000000000\n"),
                    ],
                    2,
                    "conflicting `# blob-pin:`",
                ),
                (
                    "conflicting_engine_pin_cross_file",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af("cross_e1.txt", f"# arm64-semantics @ {engine_sha[:10]}\n# blob-pin: Spec/A.lean = {sha_a}\n"),
                        "--allow-file",
                        _mk_af("cross_e2.txt", f"# arm64-semantics @ {other_engine_sha[:10]}\n# blob-pin: Spec/B.lean = {sha_b}\n"),
                    ],
                    2,
                    "conflicting engine pins across allow-files",
                ),
                (
                    "vacuous_zero_blob_pins",
                    [
                        "--check-pins-only",
                        "--allow-file",
                        _mk_af("zero_blobs.txt", f"# arm64-semantics @ {engine_sha[:10]}\n"),
                    ],
                    2,
                    "non-vacuity check failed (total_blob_pins=0",
                ),
                (
                    "rejects_no_allow",
                    ["--check-pins-only", "--no-allow"],
                    2,
                    "--check-pins-only cannot be combined with --no-allow",
                ),
            ])

            for cname, cargs, exprc, cneedle in neg_cases:
                if not _expect(cname, cargs, exprc, cneedle):
                    return 1
        finally:
            shutil.rmtree(scratch_dir, ignore_errors=True)

    total_pin_cases = 16
    print(f"[pin-self-test] ALL {total_pin_cases} CASES PASSED")
    return 0

def parse_args(argv: list[str]) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Check whether named Lean constants are transitively machine-free by defining module.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument(
        "--root",
        default=str(SCRIPT_REPO),
        help="Repository/worktree root containing compiled .lake build (default: repo containing this script).",
    )
    ap.add_argument(
        "--deny-file",
        dest="deny_files",
        action="append",
        default=None,
        help="Path to defining-module deny list (repeatable; default: Symbolic/scripts/machine_free_deny.txt).",
    )
    ap.add_argument(
        "--exclude-deny-group",
        dest="excluded_groups",
        action="append",
        default=[],
        metavar="GROUP_ID",
        help="Exclude `[group <GROUP_ID>]` patterns from `--deny-file` (repeatable; fail-closed if absent).",
    )
    ap.add_argument(
        "--allow-file",
        dest="allow_files",
        action="append",
        default=None,
        help="Path to exact per-constant allow-list (repeatable; default: Symbolic/scripts/machine_free_allow.txt).",
    )
    ap.add_argument(
        "--exempt-specs-file",
        default=None,
        help="Closed exemption list E of mixed Specifications modules (default: Symbolic/scripts/machine_free_exempt_specs.txt).",
    )
    ap.add_argument(
        "--gate",
        action="store_true",
        help="Enforce gate mode: fail closed unless every loaded allow/deny/exempt/proofdeps list matches HEAD:<path>.",
    )
    ap.add_argument(
        "--no-allow",
        action="store_true",
        help="Ignore allow-list (require 0 allowed constants in transitive cone).",
    )
    ap.add_argument(
        "--subset-allow",
        action="store_true",
        help="Permit unreached entries in allow-list (when checking an individual helper lemma).",
    )
    ap.add_argument(
        "--criterion",
        action="store_true",
        help="Compute per-module machine-level taint fixed point over default Lake target closure.",
    )
    ap.add_argument(
        "--criterion-tsv",
        default=None,
        metavar="PATH",
        help="Write `--criterion` TSV rows to PATH (and print tree/D2/fixed-point summary to stdout).",
    )
    ap.add_argument(
        "--one-step",
        action="store_true",
        help="Debug mode for control P5 (plain --criterion only): compute 1-step direct A∪B taint instead of transitive fixed point.",
    )
    ap.add_argument(
        "--emit-proofdeps",
        default=None,
        metavar="OUT_PATH",
        help="Compute `--criterion` and write Part-C `machine_free_deny_proofdeps.txt` (fails if D2 > 0).",
    )
    ap.add_argument(
        "--check-proofdeps",
        default=None,
        metavar="PROOFDEPS_PATH",
        help="CI drift check: verify every non-E machine-level module is covered by PROOFDEPS_PATH and D2 == 0.",
    )
    ap.add_argument(
        "--root-report",
        action="store_true",
        help="Emit proof-run R-a root types, R-b bridge coverage, E1 widened residual report, and std3/ofReduce checks.",
    )
    ap.add_argument(
        "--bridges-file",
        default=None,
        metavar="PATH",
        help="Bridge constant names file for R-b table under `--root-report`.",
    )
    ap.add_argument(
        "--expected-root-type-file",
        default=None,
        metavar="PATH",
        help="Expected `<FullRootConst> : <ppExpr type>` file for R-a comparison under `--root-report`.",
    )
    ap.add_argument(
        "--allow-scratch-fixture-roots",
        action="store_true",
        help="Control-runner mode only: permit scratch fixture modules outside `lakefile.lean` default targets.",
    )
    ap.add_argument(
        "--scratch-fixture-seeds-file",
        default=None,
        metavar="PATH",
        help="Control-runner mode only (requires --allow-scratch-fixture-roots): override seed batches for fast fixture controls.",
    )
    ap.add_argument(
        "--extra-lean-path",
        dest="extra_lean_paths",
        action="append",
        default=[],
        metavar="DIR",
        help="Prepend DIR to LEAN_PATH (for scratch fixture/overlay `.olean`s without mutating worktree).",
    )
    ap.add_argument(
        "--import",
        dest="extra_imports",
        action="append",
        default=[],
        metavar="MODULE",
        help="Additional Lean module to import (repeatable).",
    )
    ap.add_argument(
        "--all-module-consts",
        action="store_true",
        help="Audit ALL constants declared in <module> (and --import modules), including internals.",
    )
    ap.add_argument(
        "--non-internal-module-consts",
        action="store_true",
        help="Audit !Name.isInternal constants declared in <module> (and --import modules).",
    )
    ap.add_argument(
        "--summary-only",
        action="store_true",
        help="Print concise per-root one-liners + aggregate summary.",
    )
    ap.add_argument(
        "--synth-induct-aux",
        action="store_true",
        help="Also traverse unused projections/recursors on .inductInfo (comparison mode).",
    )
    ap.add_argument(
        "--in-process-batches",
        action="store_true",
        help="Run all criterion batches inside a single process (comparison mode).",
    )
    ap.add_argument(
        "--legacy-slow-edges",
        action="store_true",
        help="Use legacy sorted ConstEdges cache in criterion batches (comparison mode).",
    )
    ap.add_argument(
        "--gk-control",
        choices=GK_CONTROL_CHOICES,
        default=None,
        help="Inject negative control in-memory via addDeclCore: " + " | ".join(GK_CONTROL_CHOICES),
    )
    ap.add_argument(
        "--max-chain-hops",
        type=int,
        default=10,
        help="Truncate shortest BFS chains longer than N hops (default: 10; 0 = unlimited).",
    )
    ap.add_argument(
        "--max-hits",
        type=int,
        default=0,
        help="Cap printed chains per section to N (default: 0 = print all).",
    )
    ap.add_argument(
        "--max-memory-mib",
        type=int,
        default=34816,
        help="Pass `-M <MiB>` to Lean to cap heap usage (default: 34816 = 34 GiB; 0 = unlimited).",
    )
    ap.add_argument(
        "--timeout-sec",
        type=float,
        default=1200.0,
        help="Wall-clock timeout in seconds for the Lean child process (default: 1200.0).",
    )
    ap.add_argument(
        "--check-pins-only",
        action="store_true",
        help=(
            "Fast git-only pin/tag gate: verify engine submodule pins, `# blob-pin:` headers "
            "(requiring >= 1 PASS blob-pin), and `# require-tag:` directives across the production "
            "allow-lists without invoking Lean."
        ),
    )
    ap.add_argument(
        "--pin-self-test",
        action="store_true",
        help="Run fast pure-git/Python positive and negative controls for `--check-pins-only` and exit.",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="Run fail-closed allow/deny parser, group, prefix-rejection, and engine/blob-pin self-tests and exit.",
    )
    ap.add_argument("module", nargs="?", default=None, help="Primary Lean module to import.")
    ap.add_argument("constants", nargs="*", help="Fully-qualified constant names to check.")
    return ap.parse_args(argv)

def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.pin_self_test:
        return run_pin_self_test()

    repo_root = pathlib.Path(args.root).resolve()
    if not repo_root.is_dir():
        sys.stderr.write(f"[machine-free-check] error: --root directory does not exist: {repo_root}\n")
        return 2

    if args.check_pins_only:
        if args.no_allow:
            sys.stderr.write(
                "[machine-free-check] error: --check-pins-only cannot be combined with --no-allow\n"
            )
            return 2
        if (
            args.module is not None
            or args.constants
            or args.criterion
            or args.emit_proofdeps is not None
            or args.check_proofdeps is not None
            or args.root_report
            or args.gk_control is not None
        ):
            sys.stderr.write(
                "[machine-free-check] error: --check-pins-only cannot be combined with Lean audit modes or <module>/<constants>\n"
            )
            return 2
        pin_allow_files = (
            [pathlib.Path(p).resolve() for p in args.allow_files]
            if args.allow_files
            else [resolve_default_asset(repo_root, fn) for fn in PRODUCTION_PIN_ALLOW_FILENAMES]
        )
        for af in pin_allow_files:
            if not af.is_file():
                sys.stderr.write(f"[machine-free-check] error: allow list not found: {af}\n")
                return 2
        t0_pin = time.monotonic()
        list_rc = emit_and_verify_loaded_lists(
            repo_root,
            [],
            pin_allow_files,
            None,
            None,
            args.gate,
        )
        if list_rc != 0:
            elapsed_s = time.monotonic() - t0_pin
            sys.stderr.write(
                f"[machine-free-check] elapsed_s={elapsed_s:.2f} peak_rss_mib=0.0 exit_code={list_rc}\n"
            )
            return list_rc
        pin_rc = check_allow_files_pins_and_tags(
            repo_root, pin_allow_files, gate=args.gate, require_blob_pins=True
        )
        elapsed_s = time.monotonic() - t0_pin
        sys.stderr.write(
            f"[machine-free-check] elapsed_s={elapsed_s:.2f} peak_rss_mib=0.0 exit_code={pin_rc}\n"
        )
        return pin_rc

    lean_script = SCRIPT_DIR / "MachineFreeCheck.lean"
    if not lean_script.is_file():
        sys.stderr.write(f"[machine-free-check] error: Lean script not found: {lean_script}\n")
        return 2

    deny_files = (
        [pathlib.Path(p).resolve() for p in args.deny_files]
        if args.deny_files
        else [resolve_default_asset(repo_root, "machine_free_deny.txt")]
    )
    for df in deny_files:
        if not df.is_file():
            sys.stderr.write(f"[machine-free-check] error: deny list not found: {df}\n")
            return 2

    if args.self_test:
        return run_self_test(repo_root, lean_script, deny_files[0])

    allow_files: list[pathlib.Path] = []
    if not args.no_allow:
        allow_files = (
            [pathlib.Path(p).resolve() for p in args.allow_files]
            if args.allow_files
            else [resolve_default_asset(repo_root, "machine_free_allow.txt")]
        )
        for af in allow_files:
            if not af.is_file():
                sys.stderr.write(f"[machine-free-check] error: allow list not found: {af}\n")
                return 2

    criterion_family = bool(
        args.criterion or (args.emit_proofdeps is not None) or (args.check_proofdeps is not None)
    )
    needs_exempt_and_lakefile = criterion_family or args.root_report

    mode_count = sum(
        1
        for flag in (
            args.criterion,
            args.emit_proofdeps is not None,
            args.check_proofdeps is not None,
        )
        if flag
    )
    if mode_count > 1:
        sys.stderr.write(
            "[machine-free-check] error: --criterion, --emit-proofdeps, and --check-proofdeps are mutually exclusive\n"
        )
        return 2
    if criterion_family and args.root_report:
        sys.stderr.write(
            "[machine-free-check] error: --root-report cannot be combined with --criterion/--emit-proofdeps/--check-proofdeps\n"
        )
        return 2
    if args.one_step and not (
        args.criterion and args.emit_proofdeps is None and args.check_proofdeps is None
    ):
        sys.stderr.write(
            "[machine-free-check] error: --one-step is only permitted with plain --criterion "
            "(never with --emit-proofdeps, --check-proofdeps, or --gate)\n"
        )
        return 2

    exempt_file: pathlib.Path | None = None
    if needs_exempt_and_lakefile:
        exempt_file = (
            pathlib.Path(args.exempt_specs_file).resolve()
            if args.exempt_specs_file
            else resolve_default_asset(repo_root, "machine_free_exempt_specs.txt")
        )
        if not exempt_file.is_file():
            sys.stderr.write(
                f"[machine-free-check] error: exempt-specs file not found: {exempt_file}\n"
            )
            return 2

    if args.check_proofdeps is not None:
        cp_path = pathlib.Path(args.check_proofdeps).resolve()
        if not cp_path.is_file():
            sys.stderr.write(
                f"[machine-free-check] error: --check-proofdeps file not found: {cp_path}\n"
            )
            return 2
    else:
        cp_path = None

    bridges_path: pathlib.Path | None = None
    if args.bridges_file is not None:
        bridges_path = pathlib.Path(args.bridges_file).resolve()
        if not bridges_path.is_file():
            sys.stderr.write(
                f"[machine-free-check] error: --bridges-file not found: {bridges_path}\n"
            )
            return 2

    expected_type_path: pathlib.Path | None = None
    if args.expected_root_type_file is not None:
        expected_type_path = pathlib.Path(args.expected_root_type_file).resolve()
        if not expected_type_path.is_file():
            sys.stderr.write(
                f"[machine-free-check] error: --expected-root-type-file not found: {expected_type_path}\n"
            )
            return 2

    if not criterion_family:
        if not args.module:
            sys.stderr.write("[machine-free-check] error: missing <module> argument\n")
            return 2
        if (
            not args.constants
            and not args.all_module_consts
            and not args.non_internal_module_consts
            and not args.gk_control
        ):
            sys.stderr.write(
                "[machine-free-check] error: specify constant names or --all-module-consts / --non-internal-module-consts\n"
            )
            return 2
    else:
        if args.module is not None or args.constants:
            sys.stderr.write(
                "[machine-free-check] error: positional <module>/<constants> are not accepted in --criterion/--emit-proofdeps/--check-proofdeps\n"
            )
            return 2

    if args.max_chain_hops < 0 or args.max_hits < 0 or args.max_memory_mib < 0:
        sys.stderr.write("[machine-free-check] error: numeric limits must be >= 0\n")
        return 2
    if args.timeout_sec <= 0:
        sys.stderr.write("[machine-free-check] error: --timeout-sec must be > 0\n")
        return 2

    if args.gate:
        forbidden_gate_flags: list[str] = []
        if args.no_allow:
            forbidden_gate_flags.append("--no-allow")
        if args.one_step:
            forbidden_gate_flags.append("--one-step")
        if args.allow_scratch_fixture_roots:
            forbidden_gate_flags.append("--allow-scratch-fixture-roots")
        if args.scratch_fixture_seeds_file is not None:
            forbidden_gate_flags.append("--scratch-fixture-seeds-file")
        if args.extra_lean_paths:
            forbidden_gate_flags.append("--extra-lean-path")
        if args.gk_control is not None:
            forbidden_gate_flags.append("--gk-control")
        if forbidden_gate_flags:
            sys.stderr.write(
                f"[machine-free-check] error: --gate cannot be combined with {', '.join(forbidden_gate_flags)}\n"
            )
            return 2
        if args.root_report and expected_type_path is None:
            sys.stderr.write(
                "[machine-free-check] error: --gate --root-report requires --expected-root-type-file <PATH>\n"
            )
            return 2

    t0 = time.monotonic()

    grp_rc = verify_deny_files_have_group_markers(repo_root, deny_files, args.excluded_groups)
    if grp_rc != 0:
        elapsed_s = time.monotonic() - t0
        sys.stderr.write(
            f"[machine-free-check] elapsed_s={elapsed_s:.2f} peak_rss_mib=0.0 exit_code={grp_rc}\n"
        )
        return grp_rc

    list_rc = emit_and_verify_loaded_lists(
        repo_root,
        deny_files,
        allow_files,
        exempt_file,
        cp_path,
        args.gate,
        bridges_path=bridges_path,
        expected_type_path=expected_type_path,
    )
    if list_rc != 0:
        elapsed_s = time.monotonic() - t0
        sys.stderr.write(
            f"[machine-free-check] elapsed_s={elapsed_s:.2f} peak_rss_mib=0.0 exit_code={list_rc}\n"
        )
        return list_rc

    if not args.no_allow:
        pin_rc = check_allow_files_pins_and_tags(repo_root, allow_files, gate=args.gate)
        if pin_rc != 0:
            elapsed_s = time.monotonic() - t0
            sys.stderr.write(
                f"[machine-free-check] elapsed_s={elapsed_s:.2f} peak_rss_mib=0.0 exit_code={pin_rc}\n"
            )
            return pin_rc

    tmp_base = os.environ.get("TMPDIR")
    if tmp_base and not pathlib.Path(tmp_base).is_dir():
        tmp_base = None
    tmp_dir_str = tempfile.mkdtemp(prefix="machine_free_check_", dir=tmp_base)
    tmp_dir = pathlib.Path(tmp_dir_str)
    try:
        if args.scratch_fixture_seeds_file is not None and not args.allow_scratch_fixture_roots:
            sys.stderr.write(
                "[machine-free-check] error: --scratch-fixture-seeds-file requires --allow-scratch-fixture-roots\n"
            )
            return 2

        default_seeds_file: pathlib.Path | None = None
        default_closure_file: pathlib.Path | None = None
        emit_meta_file: pathlib.Path | None = None
        if needs_exempt_and_lakefile:
            if args.scratch_fixture_seeds_file is not None:
                sf_path = pathlib.Path(args.scratch_fixture_seeds_file).resolve()
                if not sf_path.is_file():
                    sys.stderr.write(
                        f"[machine-free-check] error: --scratch-fixture-seeds-file not found: {sf_path}\n"
                    )
                    return 2
                default_seeds_file = sf_path
                default_seeds = [
                    part.strip()
                    for line in sf_path.read_text(encoding="utf-8").splitlines()
                    if line.strip() and not line.strip().startswith("#")
                    for part in line.split(",")
                    if part.strip()
                ]
            else:
                try:
                    lib_batches = compute_default_target_lib_batches(repo_root)
                    default_seeds = sorted({mod for batch in lib_batches for mod in batch})
                except RuntimeError as exc:
                    sys.stderr.write(f"[machine-free-check] error parsing lakefile.lean: {exc}\n")
                    return 2
                default_seeds_file = tmp_dir / "default_target_seeds.txt"
                batch_lines = [",".join(batch) for batch in lib_batches]
                default_seeds_file.write_text("\n".join(batch_lines) + "\n", encoding="utf-8")
            if args.root_report:
                try:
                    default_closure = compute_default_target_closure(repo_root, default_seeds)
                except RuntimeError as exc:
                    sys.stderr.write(
                        f"[machine-free-check] error computing default-target closure: {exc}\n"
                    )
                    return 2
                default_closure_file = tmp_dir / "default_target_closure.txt"
                default_closure_file.write_text("\n".join(default_closure) + "\n", encoding="utf-8")

        lean_bin, lean_path = query_lake_env(repo_root)

        try:
            merged_arm64 = build_merged_arm64_dir(repo_root, tmp_dir)
        except RuntimeError as exc:
            sys.stderr.write(f"[machine-free-check] error: {exc}\n")
            return 2

        if args.emit_proofdeps is not None:
            emit_meta_file = tmp_dir / "emit_header_meta.txt"
            emit_meta_file.write_text(build_emit_header_metadata(), encoding="utf-8")

        env = os.environ.copy()
        lp_parts = [str(pathlib.Path(p).resolve()) for p in args.extra_lean_paths]
        if merged_arm64 is not None:
            lp_parts.append(str(merged_arm64))
        lp_parts.append(lean_path)
        env["LEAN_PATH"] = ":".join(lp_parts)
        env["LEAN_ABORT_ON_PANIC"] = "1"
        env["MFC_TMP_DIR"] = str(tmp_dir)
        env.setdefault("LEAN_NUM_THREADS", "8")

        try:
            native_bin = ensure_compiled_mfc_binary(lean_bin, lean_script)
        except RuntimeError as exc:
            sys.stderr.write(f"[machine-free-check] error: {exc}\n")
            return 2
        if native_bin is not None:
            lean_cmd = [str(native_bin)]
        else:
            lean_cmd = [lean_bin, "-s", "524288"]
            if args.max_memory_mib > 0:
                lean_cmd.extend(["-M", str(args.max_memory_mib)])
            lean_cmd.extend(["--run", str(lean_script)])

        for df in deny_files:
            lean_cmd.extend(["--deny-file", str(df)])
        for gid in args.excluded_groups:
            lean_cmd.extend(["--exclude-deny-group", gid])
        for af in allow_files:
            lean_cmd.extend(["--allow-file", str(af)])
        if exempt_file is not None:
            lean_cmd.extend(["--exempt-specs-file", str(exempt_file)])
        if default_seeds_file is not None:
            lean_cmd.extend(["--default-target-seeds-file", str(default_seeds_file)])
        if default_closure_file is not None:
            lean_cmd.extend(["--default-target-closure-file", str(default_closure_file)])
        if emit_meta_file is not None:
            lean_cmd.extend(["--emit-header-meta-file", str(emit_meta_file)])

        lean_cmd.extend([
            "--max-chain-hops",
            str(args.max_chain_hops),
            "--max-hits",
            str(args.max_hits),
        ])
        if args.no_allow:
            lean_cmd.append("--no-allow")
        if args.subset_allow:
            lean_cmd.append("--subset-allow")
        if args.criterion:
            lean_cmd.append("--criterion")
        if args.criterion_tsv is not None:
            lean_cmd.extend(["--criterion-tsv", str(pathlib.Path(args.criterion_tsv).resolve())])
        if args.one_step:
            lean_cmd.append("--one-step")
        if args.emit_proofdeps is not None:
            lean_cmd.extend(["--emit-proofdeps", str(pathlib.Path(args.emit_proofdeps).resolve())])
        if cp_path is not None:
            lean_cmd.extend(["--check-proofdeps", str(cp_path)])
        if args.root_report:
            lean_cmd.append("--root-report")
        if bridges_path is not None:
            lean_cmd.extend(["--bridges-file", str(bridges_path)])
        if expected_type_path is not None:
            lean_cmd.extend(["--expected-root-type-file", str(expected_type_path)])
        if args.allow_scratch_fixture_roots:
            lean_cmd.append("--allow-scratch-fixture-roots")
        if args.all_module_consts:
            lean_cmd.append("--all-module-consts")
        if args.non_internal_module_consts:
            lean_cmd.append("--non-internal-module-consts")
        if args.summary_only:
            lean_cmd.append("--summary-only")
        if args.synth_induct_aux:
            lean_cmd.append("--synth-induct-aux")
        if args.in_process_batches:
            lean_cmd.append("--in-process-batches")
        if args.legacy_slow_edges:
            lean_cmd.append("--legacy-slow-edges")
        if args.gk_control:
            lean_cmd.extend(["--gk-control", args.gk_control])
        for extra_mod in args.extra_imports:
            lean_cmd.extend(["--import", extra_mod])
        if args.module is not None:
            lean_cmd.append(args.module)
        lean_cmd.extend(args.constants)

        def _child_session_and_stack() -> None:
            try:
                os.setsid()
            except OSError:
                pass
            _set_child_stack_limit()

        proc = subprocess.Popen(
            lean_cmd, cwd=str(repo_root), env=env, preexec_fn=_child_session_and_stack
        )
        timed_out = False

        def _kill_child() -> None:
            nonlocal timed_out
            timed_out = True
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except OSError:
                try:
                    os.kill(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

        timer = threading.Timer(args.timeout_sec, _kill_child)
        timer.daemon = True
        timer.start()
        received_sig: int | None = None

        def _on_term_signal(signum: int, _frame: object) -> None:
            nonlocal received_sig
            received_sig = signum
            _kill_child()

        prev_sigterm = signal.signal(signal.SIGTERM, _on_term_signal)
        prev_sigint = signal.signal(signal.SIGINT, _on_term_signal)
        prev_sighup = signal.signal(signal.SIGHUP, _on_term_signal)
        reaped = False
        try:
            _, wait_status, rusage = os.wait4(proc.pid, 0)
            reaped = True
        finally:
            timer.cancel()
            signal.signal(signal.SIGTERM, prev_sigterm)
            signal.signal(signal.SIGINT, prev_sigint)
            signal.signal(signal.SIGHUP, prev_sighup)
            if not reaped:
                _kill_child()
                try:
                    os.waitpid(proc.pid, 0)
                except ChildProcessError:
                    pass
        elapsed_s = time.monotonic() - t0
        peak_rss_mib = rusage.ru_maxrss / 1024.0
        if received_sig is not None:
            sys.stderr.write(
                f"[machine-free-check] error: wrapper terminated by signal {received_sig}; killed child process group\n"
            )
            rc = 128 + received_sig
        elif timed_out:
            sys.stderr.write(
                f"[machine-free-check] error: lean child timed out after {args.timeout_sec:.3f}s\n"
            )
            rc = 2
        elif os.WIFEXITED(wait_status):
            rc = os.WEXITSTATUS(wait_status)
        elif os.WIFSIGNALED(wait_status):
            sig = os.WTERMSIG(wait_status)
            sys.stderr.write(f"[machine-free-check] error: lean killed by signal {sig}\n")
            rc = 2
        else:
            rc = 2

        sys.stderr.write(
            f"[machine-free-check] elapsed_s={elapsed_s:.2f} peak_rss_mib={peak_rss_mib:.1f} exit_code={rc}\n"
        )
        return rc
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)

if __name__ == "__main__":
    sys.exit(main())
