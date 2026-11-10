#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Checks the import rules of the `Computational/` tree: the trusted base, the proofs and the tests.

Usage (from any directory): Computational/scripts/check_computational_deps.py [--root REPO]

The rules apply to the git-tracked `.lean` files (and the untracked ones git does not ignore)
outside `arm64-semantics/`, `.GeneratedLean/` and the `RELEASE_EXCLUDE` archives, except
`lakefile.lean`. A module is local if its first component is a top-level directory or file of the
repository; any other module (Mathlib, VCVio, the engine, Lean core, `GeneratedLean`, ...) belongs
to an external package. "The umbrella" is `Computational.lean` (module `Computational`).

1. No module outside `Computational/` imports `Computational.*`, except the umbrella (files under
   `scripts/`, standalone CI tools run with `lean` and built by no library, are exempt). The
   comparator challenge (`comparator/ComparatorChallenge/`) may import `Computational.Specifications.*`
   and the comparator solution (`comparator/ComparatorSolution/`) `Computational.Theorems.*`, and
   nothing else of `Computational` (`comparator/README.md`).
2. A `Computational.Specifications.*` module imports only `Computational.Specifications.*`,
   `LibsignalBinary.Specifications.*`, `GeneratedLean.*Obj` (a `*Guards` module may also import
   `GeneratedLean.*Code`) and external packages. So the statements never import a proof, a
   theorem or a test.
3. Only the umbrella, `Computational.Tests.*` and the comparator solution import
   `Computational.Theorems.*`. A Theorems
   module imports neither a test nor the umbrella, and declares only theorems: each top-level
   command is a `theorem`, `namespace`, `section`, `end`, `open`, `export`, `variable`,
   `universe` or `set_option`, and the body of each `theorem NAME` is `NAME_proof`, possibly
   applied to identifiers (the proof lives in `Computational/Proofs/`).
4. A `Computational.Proofs.*` module never imports `Computational.Theorems.*` or
   `Computational.Tests.*`, and only `Computational.Tests.*` modules import `Computational.Tests.*`
   (files under `scripts/`, standalone CI tools run with `lean` and built by no library, are
   exempt).
5. (Checked by `scripts/TrustedClosure.lean`, not here: every theorem of `Computational/Theorems/`
   is a headline, and its trusted closure contains no declaration from a proof file.)
6. Every module under `Computational/` is built: it is reachable by local imports from the roots of
   the default libraries `Computational` (`Computational.lean`) and `ComputationalTests`
   (`Computational/Tests.lean`), unless `UNBUILT` lists it with the reason. An `UNBUILT` entry
   that is reachable or has no source file is reported as stale. The known-answer tests in
   `Computational/Tests/Kat/` (library `ComputationalKat`) are imported by no module outside that
   directory, since Copybara does not export it. For the same reason its `UNBUILT_PREFIXES` entry,
   and only that one (`EXPORT_EXCLUDED`), may have no source file under it: the exported tree has
   none. Any other `UNBUILT_PREFIXES` entry with no source file under it is stale. `lakefile.lean`
   declares `Computational` and
   `ComputationalTests` as default targets with exactly these roots (`LIB_ROOTS`), and
   `ComputationalKat` as a library that is not one.
7. No module imports `scripts.*`, so the scripts are in no import closure.
8. No declaration outside the canonical CLI security definitions (`CliPqxdhSecurityFor` in
   `Computational/Specifications/LibsignalCli/StatementPqElf.lean` and `SignalSessionSecureFor` in
   `Symbolic/Specifications/Security/Binary.lean`) restates their body (detected via their
   signature identifiers `(CliAdapterCostBounded, bhPrefixFullBoundMixV1With)` and
   `AllSecurityQueriesHoldOnHwTrace` paired with `CollisionAfterExplainedPrefix` or
   `NextEventCollides`).

Every rule also reports imports of `Computational.*` modules that have no source file. Prints every
violation and a summary, and exits with 1 if there is a violation. Needs only Python 3 (and `git`
when run inside a git worktree), not a Lean build.
"""
import argparse
import collections
import os
import re
import subprocess
import sys

EXCLUDE = ("arm64-semantics/", ".GeneratedLean/")
# The comparator challenge and solution (`comparator/README.md`, rules 1 and 3).
COMPARATOR_CHALLENGE_DIR = "comparator/ComparatorChallenge/"
COMPARATOR_SOLUTION_DIR = "comparator/ComparatorSolution/"
IGNORE_DIRS = frozenset({".git", ".lake", "build", "target", "vendor", ".GeneratedLean"})
UMBRELLA = "Computational"
SPECS = "Computational.Specifications"
PROOFS = "Computational.Proofs"
THEOREMS = "Computational.Theorems"
TESTS = "Computational.Tests"
KAT = "Computational.Tests.Kat"
GENERATED = "GeneratedLean"
# Roots of the default libraries `Computational` and `ComputationalTests` (rule 6).
LIB_ROOTS = {
    "Computational": [UMBRELLA],
    "ComputationalTests": [TESTS],
}
BUILD_ROOTS = tuple(r for roots in LIB_ROOTS.values() for r in roots)
# Modules under `Computational/` that no default library builds (rule 6), with the reason.
UNBUILT = {
    "Computational.Proofs.LibsignalCli.ElfHeadlinePq":
        "built by non-default library `CliElfLib` (depends on `.GeneratedLean/cli-elf/libsignal-cli.elf`)",
    "Computational.Theorems.Main":
        "built by non-default library `CliElfLib` (depends on `.GeneratedLean/cli-elf/libsignal-cli.elf`)",
}
# Module prefixes that no default library builds (rule 6), with the reason.
UNBUILT_PREFIXES = {
    KAT: "the known-answer tests: library `ComputationalKat`, built by its own CI step and not "
         "exported",
}
# The `UNBUILT_PREFIXES` entries whose directory Copybara does not export (`ORIGIN_EXCLUDES` in
# `copy.bara.sky` lists `Computational/Tests/Kat/**`). Only these may have no source file under
# them, so the check also passes on the exported tree; every other entry with no source file is
# stale (rule 6).
EXPORT_EXCLUDED = frozenset({KAT})
THEOREM_COMMANDS = ("theorem", "namespace", "section", "end", "open", "export", "variable",
                    "universe", "set_option")

_COMMENT_TOKEN = re.compile(r"/-|-/|--")
# The file-level `@[expose] public section` of a Lean `module` (inserted by Modulize.lean); it
# declares nothing, so a Theorems file may contain it.
_FILE_PUBLIC_SECTION = re.compile(r"(?:@\[expose\]\s+)?public\s+section")
_IMPORT = re.compile(r"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)")
_IDENT = r"[^\W\d][\w.'!?]*"
_THEOREM = re.compile(rf"theorem\s+({_IDENT})")
_BODY = re.compile(rf"({_IDENT})((?:\s+{_IDENT})*)")


def strip_line(line, depth):
    """Returns the code of `line` outside comments and the block-comment depth after it.

    `depth` is the depth of nested `/- ... -/` comments at the start of the line.
    """
    out = []
    pos = 0
    for m in _COMMENT_TOKEN.finditer(line):
        tok = m.group()
        if depth == 0:
            if tok == "--":
                out.append(line[pos:m.start()])
                return "".join(out), 0
            if tok == "/-":
                out.append(line[pos:m.start()])
                depth = 1
        elif tok == "/-":
            depth += 1
        elif tok == "-/":
            depth -= 1
            if depth == 0:
                pos = m.end()
    if depth == 0:
        out.append(line[pos:])
    return "".join(out), depth


def read_module(path):
    """Returns the modules imported by the header of a Lean file and the code lines after it."""
    imports = []
    code_lines = []
    depth = 0
    in_header = True
    with open(path, encoding="utf-8") as fp:
        for line in fp:
            code, depth = strip_line(line.rstrip("\n"), depth)
            if in_header:
                stripped = code.strip()
                if not stripped or stripped in ("module", "prelude"):
                    continue
                m = _IMPORT.fullmatch(stripped)
                if m is not None:
                    imports.extend(m.group(1).split())
                    continue
                in_header = False
            code_lines.append(code)
    return imports, code_lines


def _is_git_worktree(root):
    if not os.path.exists(os.path.join(root, ".git")):
        return False
    try:
        res = subprocess.run(
            ["git", "-C", root, "rev-parse", "--is-inside-work-tree"],
            capture_output=True, text=True, check=False,
        )
        return res.returncode == 0 and res.stdout.strip() == "true"
    except OSError:
        return False


def lean_files(root):
    """The `.lean` files the rules apply to, relative to `root`."""
    if _is_git_worktree(root):
        out = subprocess.run(
            ["git", "-C", root, "ls-files", "--cached", "--others", "--exclude-standard", "--",
             "*.lean"], capture_output=True, text=True, check=True).stdout
        raw_files = out.splitlines()
    else:
        raw_files = []
        for dirpath, dirs, filenames in os.walk(root):
            dirs[:] = sorted(d for d in dirs if d not in IGNORE_DIRS)
            for fn in filenames:
                if fn.endswith(".lean"):
                    raw_files.append(
                        os.path.relpath(os.path.join(dirpath, fn), root).replace(os.sep, "/")
                    )
    return sorted({f for f in raw_files
                   if f.endswith(".lean") and not f.startswith(EXCLUDE) and f != "lakefile.lean"
                   and "/RELEASE_EXCLUDE/" not in f and os.path.isfile(os.path.join(root, f))})


def top(module):
    return module.split(".", 1)[0]


def under(module, prefix):
    return module == prefix or module.startswith(prefix + ".")


def top_level_assign(text):
    """The index of the first `:=` outside brackets in `text`, or -1."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return i
    return -1


def theorem_file_violations(f, code_lines):
    """Rule 3: a Theorems file declares only theorems, each proved by `<name>_proof`."""
    out = []
    commands = []  # (line number, text)
    for n, line in enumerate(code_lines, 1):
        if not line.strip():
            continue
        if line[0].isspace():
            if commands:
                commands[-1][1].append(line)
            continue
        commands.append((n, [line]))
    for n, lines in commands:
        text = "\n".join(lines)
        if _FILE_PUBLIC_SECTION.fullmatch(text.strip()):
            continue
        head = text.split(None, 1)[0]
        if head not in THEOREM_COMMANDS:
            out.append(f"{f}: top-level command `{head}` (a Theorems file declares only theorems)")
            continue
        if head != "theorem":
            continue
        m = _THEOREM.match(text)
        if m is None:
            out.append(f"{f}: cannot parse the theorem `{text.splitlines()[0]}`")
            continue
        name = m.group(1)
        i = top_level_assign(text[m.end():])
        body = text[m.end() + i + 2:].strip() if i >= 0 else ""
        bm = _BODY.fullmatch(body)
        short = name.rsplit(".", 1)[-1]
        if bm is None or bm.group(1).rsplit(".", 1)[-1] != short + "_proof":
            out.append(f"{f}: theorem {name} is not proved by `{short}_proof` (body: "
                       f"`{' '.join(body.split()) or '<none>'}`)")
    return out


_ATTR_OR_MOD = (
    r"(?:@\[(?:[^\[\]]|\[[^\[\]]*\])*\]"
    r"|(?:private|protected|public|local|noncomputable|unsafe|partial)\b"
    r"|scoped(?:\s*\[[^\]]*\])?(?=\s|@\[))"
)
_DECL_KWS = (
    "def", "abbrev", "theorem", "lemma", "structure", "class",
    "inductive", "opaque", "axiom", "instance", "example",
)
_DIR_KWS = (
    "namespace", "section", "end", "mutual", "open", "export", "variable",
    "universe", "set_option", "notation", "macro", "elab", "syntax",
    "infix", "infixl", "infixr", "prefix", "postfix",
)
_TOP_CMD = re.compile(
    rf"(?:^|\n|[ \t]+in(?=\s))[ \t]*(?:{_ATTR_OR_MOD}\s*)*"
    rf"(?P<kind>{'|'.join(_DECL_KWS + _DIR_KWS)})\b"
    rf"(?:\s+(?P<name>{_IDENT}))?"
)
_LET_OR_HAVE = re.compile(r"(?:let|have)\b")
_WHERE_KW = re.compile(r"where\b")
_HEADLINE_SIGS = (
    (
        "Computational/Specifications/LibsignalCli/StatementPqElf.lean",
        "CliPqxdhSecurityFor",
        re.compile(r"\bCliAdapterCostBounded\b"),
        re.compile(r"\bbhPrefixFullBoundMixV1With\b"),
    ),
    (
        "Symbolic/Specifications/Security/Binary.lean",
        "SignalSessionSecureFor",
        re.compile(r"\bAllSecurityQueriesHoldOnHwTrace\b"),
        re.compile(r"\b(?:CollisionAfterExplainedPrefix|NextEventCollides)\b"),
    ),
)


def _is_ident_char(ch):
    return ch.isalnum() or ch in "_'!?."


def theorem_type_prefix(text):
    """Returns the statement prefix of a `theorem`/`lemma`/`example` before its proof body.

    Tracks bracket depth across `([{⦃⟨` .. `)]}⦄⟩` and depth-0 `let`/`have` bindings so that
    `let x := ...` bindings inside a theorem's proposition do not prematurely truncate the scan.
    """
    n = len(text)
    i = 0
    depth = 0
    let_pending = 0
    seen_colon = False
    while i < n:
        ch = text[i]
        if ch == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if ch == "'" and (i == 0 or not _is_ident_char(text[i - 1])):
            j = i + 1
            if j < n and text[j] == "\\":
                j += 2
            else:
                j += 1
            if j < n and text[j] == "'":
                i = j + 1
                continue
        if ch in "([{⦃⟨":
            depth += 1
            i += 1
            continue
        if ch in ")]}⦄⟩":
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            if text.startswith(":=", i):
                if let_pending > 0:
                    let_pending -= 1
                    i += 2
                    continue
                return text[:i]
            if ch == ":" and not text.startswith("::", i) and let_pending == 0:
                seen_colon = True
                i += 1
                continue
            if (seen_colon and let_pending == 0 and ch == "|"
                    and not text.startswith("||", i) and not text.startswith("|>", i)
                    and (i == 0 or text[i - 1] != "|")):
                return text[:i]
            if i == 0 or not _is_ident_char(text[i - 1]):
                m_let = _LET_OR_HAVE.match(text, i)
                if m_let is not None and (m_let.end() == n or not _is_ident_char(text[m_let.end()])):
                    let_pending += 1
                    i = m_let.end()
                    continue
                if let_pending == 0:
                    m_where = _WHERE_KW.match(text, i)
                    if m_where is not None and (m_where.end() == n
                                                or not _is_ident_char(text[m_where.end()])):
                        return text[:i]
        i += 1
    return text


def _line_indent(text, pos):
    line_start = text.rfind("\n", 0, pos) + 1
    i = line_start
    n = len(text)
    while i < n and text[i] in " \t":
        i += 1
    return i - line_start


def headline_restatement_violations(f, code_lines):
    """Rule 8: no declaration outside the canonical definitions restates a CLI security body."""
    if f.startswith("scripts/"):
        return []
    code_text = "\n".join(code_lines)
    if not code_text.strip():
        return []
    raw_matches = list(_TOP_CMD.finditer(code_text))
    matches = []
    thm_body_start = None
    thm_indent = 0
    for m in raw_matches:
        cmd_pos = m.start() + 1 if code_text[m.start()] == "\n" else m.start()
        ind = _line_indent(code_text, cmd_pos)
        if thm_body_start is not None:
            if cmd_pos >= thm_body_start and ind > thm_indent:
                continue
            if ind <= thm_indent:
                thm_body_start = None
        matches.append(m)
        if m.group("kind") in ("theorem", "lemma", "example"):
            thm_indent = ind
            thm_body_start = cmd_pos + len(theorem_type_prefix(code_text[cmd_pos:]))
    chunks = []  # (kind, name, segment_text)
    if not matches:
        chunks.append(("", "", code_text))
    else:
        if code_text[:matches[0].start()].strip():
            chunks.append(("", "", code_text[:matches[0].start()]))
        for idx, m in enumerate(matches):
            end = matches[idx + 1].start() if idx + 1 < len(matches) else len(code_text)
            chunks.append((m.group("kind"), m.group("name") or "", code_text[m.start():end]))
    out = []
    for kind, name, text in chunks:
        # Pure `open`/`export` import lists have neither `:=` nor `where`; any unrecognized
        # declaration trailing after a directive has `:=` or `where` and is still scanned.
        if kind in ("open", "export") and ":=" not in text and not re.search(r"\bwhere\b", text):
            continue
        if kind in ("theorem", "lemma", "example"):
            text = theorem_type_prefix(text)
        short = name.rsplit(".", 1)[-1]
        for canon_file, canon_name, sig_a, sig_b in _HEADLINE_SIGS:
            if f == canon_file and short == canon_name and kind in ("def", "abbrev"):
                continue
            m_a = sig_a.search(text)
            m_b = sig_b.search(text)
            if m_a and m_b:
                out.append(
                    f"{f}: `{name or kind or '<top-level>'}` restates `{canon_name}` (mentions both "
                    f"`{m_a.group(0)}` and `{m_b.group(0)}`); specialize "
                    f"`{canon_name}` ({canon_file}) instead"
                )
    return out


def lakefile_violations(root):
    """Rule 6: the default libraries and `ComputationalKat` in `lakefile.lean`."""
    path = os.path.join(root, "lakefile.lean")
    depth = 0
    lines = []
    with open(path, encoding="utf-8") as fp:
        for line in fp:  # strip `--` and (nested, multi-line) `/- ... -/` comments
            code, depth = strip_line(line.rstrip("\n"), depth)
            lines.append(code)
    text = "\n".join(lines)
    libs = {}
    # A library's body ends at the next line that starts in column 0 or, after spaces, with `@[`
    # or `lean_lib`.
    for m in re.finditer(r"(@\[default_target\]\s*)?lean_lib\s+(\w+)\s+where"
                         r"(.*?)(?=\n\S|\n[ \t]*(?:@\[|lean_lib\b)|\Z)", text, re.S):
        roots = re.search(r"roots\s*:=\s*#\[(.*?)\]", m.group(3), re.S)
        globs = re.search(r"globs\s*:=\s*#\[(.*?)\]", m.group(3), re.S)
        libs[m.group(2)] = (bool(m.group(1)),
                            re.findall(r"`([\w.]+)", roots.group(1)) if roots else [m.group(2)],
                            globs.group(1) if globs else "")
    out = []
    for lib, roots in LIB_ROOTS.items():
        if lib not in libs or not libs[lib][0] or libs[lib][1] != roots:
            out.append(f"lakefile.lean: `{lib}` must be a default target with roots "
                       f"#[{', '.join('`' + r for r in roots)}]")
    kat = libs.get("ComputationalKat")
    if kat is None or kat[0] or not re.search(rf"\.submodules\s+`{re.escape(KAT)}\b", kat[2]):
        out.append(f"lakefile.lean: `ComputationalKat` must be a library that is not a default "
                   f"target, with globs .submodules `{KAT}")
    return out


def main(argv=None):
    default_root = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                 "..", ".."))
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=default_root, help="repository root (default: %(default)s)")
    args = ap.parse_args(argv)

    path_of = {}  # module -> file
    imports_of = {}  # module -> imported modules
    code_of = {}  # Theorems module -> code lines after the header
    restatement_violations = []
    for f in lean_files(args.root):
        mod = f[:-len(".lean")].replace("/", ".")
        imports, code = read_module(os.path.join(args.root, f))
        path_of[mod] = f
        imports_of[mod] = imports
        if under(mod, THEOREMS):
            code_of[mod] = code
        restatement_violations.extend(headline_restatement_violations(f, code))
    local_tops = {top(m) for m in path_of}

    def is_comp(m):
        return under(m, UMBRELLA)

    violations = collections.defaultdict(list)
    for mod in sorted(imports_of):
        f = path_of[mod]
        for imp in imports_of[mod]:
            if is_comp(imp) and imp not in path_of:
                violations[0].append(f"{f}: imports {imp}, which has no source file")
            # Rule 1
            comparator_ok = ((f.startswith(COMPARATOR_CHALLENGE_DIR) and under(imp, SPECS))
                             or (f.startswith(COMPARATOR_SOLUTION_DIR) and under(imp, THEOREMS)))
            if (is_comp(imp) and not is_comp(mod) and not f.startswith("scripts/")
                    and not comparator_ok):
                violations[1].append(f"{f}: imports {imp}")
            # Rule 2
            if under(mod, SPECS):
                t = top(imp)
                ok = (under(imp, SPECS) or under(imp, "LibsignalBinary.Specifications")
                      or (t == GENERATED and (imp.endswith("Obj")
                                              or (imp.endswith("Code")
                                                  and mod.endswith("Guards"))))
                      or (t != GENERATED and t not in local_tops))
                if not ok:
                    violations[2].append(f"{f}: imports {imp}")
            # Rule 3
            if (under(imp, THEOREMS) and mod != UMBRELLA and not under(mod, TESTS)
                    and not f.startswith(COMPARATOR_SOLUTION_DIR)):
                violations[3].append(f"{f}: imports {imp}")
            if under(mod, THEOREMS) and (under(imp, TESTS) or imp == UMBRELLA):
                violations[3].append(f"{f}: imports {imp}")
            # Rule 4
            if under(mod, PROOFS) and under(imp, THEOREMS):
                violations[4].append(f"{f}: imports {imp}")
            if under(imp, TESTS) and not under(mod, TESTS) and not f.startswith("scripts/"):
                violations[4].append(f"{f}: imports {imp}")
            # Rule 6 (Kat isolation)
            if under(imp, KAT) and not under(mod, KAT):
                violations[6].append(f"{f}: imports {imp} (Computational/Tests/Kat/ is not "
                                     "exported)")
            # Rule 7
            if under(imp, "scripts"):
                violations[7].append(f"{f}: imports {imp}")
    for mod in sorted(code_of):
        violations[3].extend(theorem_file_violations(path_of[mod], code_of[mod]))

    # Rule 6: breadth-first over local imports from the roots of the default libraries.
    reached = set()
    queue = collections.deque()
    for r in BUILD_ROOTS:
        if r in path_of:
            reached.add(r)
            queue.append(r)
        else:
            violations[6].append(f"build root {r} has no source file")
    while queue:
        m = queue.popleft()
        for imp in imports_of[m]:
            if imp in path_of and imp not in reached:
                reached.add(imp)
                queue.append(imp)
    comp = sorted(m for m in path_of if is_comp(m))
    for m in comp:
        if m in reached or m in UNBUILT or any(under(m, p) for p in UNBUILT_PREFIXES):
            continue
        violations[6].append(f"{path_of[m]} is not built (not imported, directly or not, by "
                             f"{' or '.join(BUILD_ROOTS)}, and not in UNBUILT)")
    for m in sorted(UNBUILT):
        if m not in path_of:
            violations[6].append(f"stale UNBUILT entry {m}: no source file")
        elif m in reached:
            violations[6].append(f"stale UNBUILT entry {m}: it is built now")
    for p in sorted(UNBUILT_PREFIXES):
        under_p = [m for m in comp if under(m, p)]
        if not under_p and p not in EXPORT_EXCLUDED:
            violations[6].append(f"stale UNBUILT_PREFIXES entry {p}: no source file under it")
        for m in under_p:
            if m in reached:
                violations[6].append(f"{path_of[m]} is under UNBUILT_PREFIXES entry {p} but is "
                                     "built by a default library")
    violations[6].extend(lakefile_violations(args.root))
    violations[8].extend(restatement_violations)

    for rule in sorted(violations):
        for v in violations[rule]:
            print(f"RULE{rule} {v}" if rule else f"MISSING {v}")
    n = collections.Counter(m.split(".")[1] if "." in m else "(umbrella)" for m in comp)
    unbuilt = sum(1 for m in comp if m not in reached)
    print(f"check_computational_deps: {len(comp)} Computational modules ({n['Specifications']} "
          f"Specifications, {n['Proofs']} Proofs, {n['Theorems']} Theorems, {n['Tests']} Tests)")
    print(f"  missing source files: {len(violations[0])} violations")
    print(f"  rule 1 (Computational imported from outside Computational/): "
          f"{len(violations[1])} violations")
    print(f"  rule 2 (Specifications imports): {len(violations[2])} violations")
    print(f"  rule 3 (Theorems imports and declarations, {len(code_of)} files): "
          f"{len(violations[3])} violations")
    print(f"  rule 4 (Proofs and Tests imports): {len(violations[4])} violations")
    print(f"  rule 6 (built from {' and '.join(BUILD_ROOTS)}: {len(comp) - unbuilt} modules, "
          f"{unbuilt} unbuilt as listed): {len(violations[6])} violations")
    print(f"  rule 7 (scripts.* not imported): {len(violations[7])} violations")
    print(f"  rule 8 (canonical CLI security statements not restated): "
          f"{len(violations[8])} violations")
    return 1 if any(violations.values()) else 0


if __name__ == "__main__":
    sys.exit(main())
