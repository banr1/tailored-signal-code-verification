#!/usr/bin/env python3
# Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
# See `third_party/libsignal/README.md`.

"""Replace hand-copied instruction decode lemmas with `gen_decodes` commands.

Usage (from the repository root):
  gen_decodes.py [--apply] [--keep FILE] [ROOT ...]

Scans the `.lean` files under ROOTs (default `DEFAULT_ROOTS`: `Computational/Proofs`,
`Computational/Tests`, `LibsignalBinary/Proofs`, `Symbolic/Proofs`, without `DEFAULT_SKIP`) for
hand-copied decode lemmas of the libsignal session image,

    [@[attrs]] [private] theorem <prefix>_decode_0x<off> :
        <libsignalSessionCode_tree>.fetchDecodeAt 0x<off> = some … := by rfl_kernel

(also `WordTree.fetchDecodeAt libsignalSessionCode_tree 0x<off>`, `:= by decide`, a preceding
`set_option … in`, and a preceding trivial offset comment `-- +0x1a8 (0x3a650)` or
`/-- +0x1a8 (0x3a650) -/`), and replaces each maximal run of such lemmas with the same prefix,
attributes and visibility by one command

    [@[attrs]] [private] gen_decodes libsignalSessionCode_tree <prefix> [0xa → 0xb, 0xc]

(`LibsignalBinary/Proofs/CodeLayout.lean`), which generates the same theorem names with the
statements read off the current code, so they cannot go stale when the image is re-exported. Any
other line between two lemmas (a section comment, a non-trivial docstring, other declarations) ends
the run and is kept. `import LibsignalBinary.Proofs.CodeLayout` is added where needed (unless the
file already imports it).

The generated statements are in the engine's canonical form (what `reduceDecode` writes in
`wp_steps`), where a 64-bit immediate `2^64 - k` (`0 < k ≤ 2^32`) reads `-(k#64)`. A lemma that
spells such an immediate as the plain numeral instead (`18446744073709551600`, `{ toFin := … }`,
`0xffff…`) becomes a `raw 0x<off>` item, which keeps that form, since its consumers were proved
against it.

`--keep FILE` lists fully qualified theorem names (one per line) to leave hand-written. A comment
line `-- gen_decodes: keep (<reason>)` right above a lemma does the same in place, so it also holds
on every re-run.
Without `--apply` nothing is written (dry run); a summary is printed either way.
Keyed only on the lemma shape and names, so it can be re-run after any rename or move; a converted
file has no hand-copied decode lemmas left, so a second run is a no-op.
"""
import os
import re
import sys

TREE = 'libsignalSessionCode_tree'
IMPORT = 'import LibsignalBinary.Proofs.CodeLayout'
# `IMPORT` (makes `gen_decodes` available)
HAS_IMPORT = re.compile(r'^import LibsignalBinary\.Proofs\.CodeLayout\s*$', re.M)
# default ROOTs: the proof and test trees (`Computational/`, `LibsignalBinary/`, `Symbolic/`)
DEFAULT_ROOTS = ['Computational/Proofs', 'Computational/Tests', 'LibsignalBinary/Proofs',
                 'Symbolic/Proofs']
# skipped under the default ROOTs: the `CryptoGames/` modules (formerly the unscanned top-level
# `CryptoGames/`), the AGPL-derived KATs (`Computational/Tests/Kat/`, formerly under it) and the
# compile-time guards of the E2E statement (`Computational/Tests/Guards/`, formerly under
# `Specifications/`)
DEFAULT_SKIP = ('Computational/Proofs/CryptoGames/', 'Computational/Tests/Kat/',
                'Computational/Tests/Guards/')
HEADER = re.compile(
    r'^(?P<attrs>@\[[^\]]*\]\s*)?(?P<priv>private\s+)?theorem\s+'
    r'(?P<pfx>[A-Za-z_][A-Za-z0-9_\']*)_decode_0x(?P<off>[0-9a-f]+)\b')
TRIVIAL_COMMENT = re.compile(
    r'^\s*(--\s*\+0x[0-9a-f]+(\s*\(0x[0-9a-f]+\))?\s*|/--\s*\+0x[0-9a-f]+(\s*\(0x[0-9a-f]+\))?\s*-/\s*)$')
SET_OPTION_IN = re.compile(r'^set_option\s+\S+\s+\S+\s+in\s*$')
KEEP_MARKER = re.compile(r'^\s*--\s*gen_decodes:\s*keep\b')
STMT = re.compile(
    r'^\s*:\s*(?:\(\s*)?(?:(?:WordTree\.fetchDecodeAt\s+' + TREE + r')|(?:' + TREE +
    r'\.fetchDecodeAt))\s+(?P<off>0x[0-9a-fA-F]+|\d+)\s*=\s*(?:\(\s*)?(?:Option\.)?some\b', re.S)
PROOF = re.compile(r':=\s*by\s+(rfl_kernel|decide)\s*$', re.S)
NUMERAL = re.compile(r'(?<![0-9A-Za-z_.])(0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_])')


def raw_imm(text):
    """Whether a statement spells a 64-bit immediate `2^64 - k` (`0 < k ≤ 2^32`) as the plain
    numeral, where the canonical form (`ProofLib.cleanReducedExpr`) reads `-(k#64)`."""
    for m in NUMERAL.finditer(text):
        v = int(m.group(1), 0)
        if 1 << 63 <= v < 1 << 64 and (1 << 64) - v <= 1 << 32:
            return True
    return False


def namespaces_at(lines, i):
    """The namespace (`namespace` / `end` stack) in effect at line `i` (sections ignored)."""
    stack = []
    for l in lines[:i]:
        m = re.match(r'^namespace\s+(\S+)', l)
        if m:
            stack.append(('ns', m.group(1)))
            continue
        m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?', l)
        if m:
            stack.append(('sec', m.group(1) or ''))
            continue
        m = re.match(r'^end(?:\s+(\S+))?\s*$', l)
        if m and stack:
            stack.pop()
    return '.'.join(n for k, n in stack if k == 'ns')


def parse_blocks(lines):
    """Decode lemma blocks: dicts with start/end line indices (end exclusive), key, off, name."""
    blocks = []
    i = 0
    n = len(lines)
    while i < n:
        m = HEADER.match(lines[i])
        if not m:
            i += 1
            continue
        j = i + 1
        while j < n and lines[j].strip() and (lines[j][0].isspace()):
            j += 1
        text = lines[i][m.end():] + '\n' + '\n'.join(lines[i + 1:j])
        sm = STMT.match(text)
        pm = PROOF.search(text)
        off = int(m.group('off'), 16)
        ok = sm is not None and pm is not None and int(sm.group('off'), 0) == off
        start = i
        if i > 0 and SET_OPTION_IN.match(lines[i - 1]):
            start = i - 1
        # a `-- gen_decodes: keep …` marker right above keeps the lemma hand-written
        marked = start > 0 and KEEP_MARKER.match(lines[start - 1]) is not None
        # a trivial offset comment right above belongs to the block
        if start > 0 and TRIVIAL_COMMENT.match(lines[start - 1]):
            start -= 1
        attrs = re.sub(r'\s+', ' ', (m.group('attrs') or '').strip())
        blocks.append(dict(start=start, end=j, ok=ok and not marked, off=off, pfx=m.group('pfx'),
                           key=(attrs, bool(m.group('priv')), m.group('pfx')),
                           attrs=attrs, priv=bool(m.group('priv')), line=i,
                           marked=ok and marked, raw=ok and raw_imm(text[sm.end():pm.start()])))
        i = j
    return blocks


def ranges(items):
    """`gen_decodes` range items for `(offset, raw)` pairs: maximal runs of consecutive non-raw
    offsets become `0xa → 0xb`, and each raw offset is its own `raw 0xa` item."""
    out = []
    for o, raw in items:
        if out and not raw and not out[-1][2] and o == out[-1][1] + 4:
            out[-1][1] = o
        else:
            out.append([o, o, raw])
    return [f'raw {a:#x}' if raw else f'{a:#x}' if a == b else f'{a:#x} → {b:#x}'
            for a, b, raw in out]


def emit(group):
    b0 = group[0]
    head = ''
    if b0['attrs']:
        head += b0['attrs'] + ' '
    if b0['priv']:
        head += 'private '
    head += f'gen_decodes {TREE} {b0["pfx"]} ['
    items = ranges([(b['off'], b['raw']) for b in group])
    out, cur = [], head
    for k, it in enumerate(items):
        piece = it + (', ' if k + 1 < len(items) else ']')
        if len(cur) + len(piece.rstrip()) > 100 and cur.strip():
            out.append(cur.rstrip())
            cur = '    '
        cur += piece
    out.append(cur.rstrip())
    return out


def convert(path, keep, stats):
    src = open(path).read()
    lines = src.split('\n')
    blocks = parse_blocks(lines)
    if not blocks:
        return None
    for b in blocks:
        ns = namespaces_at(lines, b['line'])
        b['name'] = (ns + '.' if ns else '') + f'{b["pfx"]}_decode_0x{b["off"]:x}'
        if b['marked']:
            stats['kept'] += 1
        elif not b['ok']:
            stats['unparsed'].append(f'{path}:{b["line"] + 1}')
        elif b['name'] in keep:
            b['ok'] = False
            stats['kept'] += 1
    # group consecutive convertible blocks separated only by blank / trivial-comment lines
    groups, cur = [], []
    for b in blocks:
        if not b['ok']:
            if cur:
                groups.append(cur)
            cur = []
            continue
        if cur:
            prev = cur[-1]
            between = lines[prev['end']:b['start']]
            if b['key'] == prev['key'] and all(not l.strip() or TRIVIAL_COMMENT.match(l)
                                               for l in between):
                cur.append(b)
                continue
            groups.append(cur)
        cur = [b]
    if cur:
        groups.append(cur)
    if not groups:
        return None
    out = []
    pos = 0
    for g in groups:
        out.extend(lines[pos:g[0]['start']])
        out.extend(emit(g))
        pos = g[-1]['end']
        stats['lemmas'] += len(g)
        stats['commands'] += 1
    out.extend(lines[pos:])
    text = '\n'.join(out)
    if not HAS_IMPORT.search(text):
        imports = [m.end() for m in re.finditer(r'^import\s+\S+[^\n]*$', text, re.M)]
        if imports:
            text = text[:imports[-1]] + '\n' + IMPORT + text[imports[-1]:]
        else:
            text = IMPORT + '\n' + text
    stats['files'] += 1
    return text


def main():
    args = sys.argv[1:]
    apply = '--apply' in args
    keep = set()
    if '--keep' in args:
        k = args.index('--keep')
        keep = {l.strip() for l in open(args[k + 1]) if l.strip() and not l.startswith('#')}
        del args[k:k + 2]
    roots = [a for a in args if not a.startswith('--')]
    skip = () if roots else DEFAULT_SKIP
    files = []
    for r in roots or DEFAULT_ROOTS:
        if os.path.isfile(r):
            files.append(r)
        for d, _, fs in os.walk(r):
            files += [os.path.join(d, f) for f in fs
                      if f.endswith('.lean') and not os.path.join(d, f).startswith(skip)]
    stats = dict(files=0, lemmas=0, commands=0, kept=0, unparsed=[])
    for f in sorted(set(files)):
        src = open(f).read()
        if '_decode_0x' not in src or TREE not in src:
            continue
        new = convert(f, keep, stats)
        if new is not None and new != src:
            print(f'{f}: converted')
            if apply:
                open(f, 'w').write(new)
    print(f'{stats["lemmas"]} decode lemmas -> {stats["commands"]} gen_decodes commands in '
          f'{stats["files"]} files; {stats["kept"]} kept (--keep or marker); '
          f'{len(stats["unparsed"])} not recognised (kept):')
    for u in stats['unparsed']:
        print('  ' + u)
    if not apply:
        print('(dry run; pass --apply to write)')


if __name__ == '__main__':
    main()
