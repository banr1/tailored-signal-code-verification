#!/usr/bin/env python3
# Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
# See `third_party/libsignal/README.md`.

"""Replace layout-dependent numerals in the libsignal-session proofs with symbolic lookups.

Usage (from the repository root):
  symbolize.py [--gen DIR] [--apply] [--report OUT] [--lean-check OUT.lean] [ROOT ...]

`DIR` is the `rust-obj2lean` output directory of the current image (default
`.GeneratedLean/GeneratedLean`). ROOTs (default `DEFAULT_ROOTS`: `Computational/Proofs`,
`Computational/Specifications`, `Computational/Tests`, `Proofs Specifications` under
`LibsignalBinary/` and under `Symbolic/`, without `DEFAULT_SKIP`) are scanned for `.lean` files; the files
rewritten are those that import (transitively) a `GeneratedLean.LibsignalSession*` or
`GeneratedLean.LibsignalTripleRatchet*` module. Files under a specification tree (`SPEC_DIRS`:
`Computational/Specifications/`, `Computational/Tests/Guards/`, `LibsignalBinary/Specifications/`,
`Symbolic/Specifications/`; trusted) are never written: their sites are only reported.
Without `--apply` nothing is written (dry run). The tool is idempotent: the arguments of existing
`num%` / `bv%` / `ls_*%` / `code_*%` / `img_*%` / `nat_lit%` forms are never touched, so it can be
re-run after new proofs land.

Why: when more crates are appended to the image, every function keeps its offset, but the extern
stubs, the `.rodata` pieces, the GOT (global offset table) and the extern data objects move. A proof
that spells such an address (`b + 0x4dab0#64`), a distance from code to it (`entry + 17640#64`,
`(k := 17640)`, a `bl`/`adrp` immediate) or a generated hook-lemma name
(`libsignalSessionCode_hookAtOff?_0x47f20`) breaks. This tool rewrites each such site into a form
that `LibsignalBinary/Proofs/CodeLayout.lean` evaluates, at elaboration time, to the very same
numeral (so the elaborated term is unchanged) but that follows the image:

  absolute stub / data address A   ->  `bv% (KEY + d)` / `num% (KEY + d)`
  distance A - F from function F   ->  `bv% (KEY + d - 0xF)`        (F does not move)
  `adrp` page displacement          ->  `bv% (page% (KEY + d) - 0xP)` (P = page of the `adrp`)
  low-12 offset                     ->  `bv% ((KEY + d) % 4096)`
  hook / stub lemma names           ->  `(ls_hook% "sym")`, `(ls_stub% "sym")`

where KEY is, by preference: a stub (`ls_off% "memcpy"`), a field (`ls_field% dataOff|gotOff|
codeLen|textEnd`), an extern data object or named data symbol (`ls_sym% "…"`), a unique string or
byte window of the `.rodata` piece (`ls_str% "…"`, `ls_bytes% "…"`), or a data relocation slot
whose target is unique (`ls_reloc% (0x2f4c)`). Keys are chosen against the current image only;
the build (and `--lean-check`) is the oracle, and a later re-export that makes a key ambiguous
fails loudly at the use site.

Which numerals are layout-dependent is decided from their syntactic context (see `classify`):
  * `b + N#64` (`b`, `base`, `img.base`, …): N absolute, rewritten if in the stub / data range;
  * `entry + N#64`, `fnAddr X + N#64`, `(k := N)`, `X N` after a name abbreviation: N a
    distance from a function F (resolved from `X`, or from `fnAddr X = entry` nearby, or from the
    functions the file mentions), rewritten if F + N is a stub / data target that F references;
  * `Int64.ofBitVec N#64` (a `bl`/`b`/`adr` immediate) inside a `fetchDecodeAt PC` block;
  * `(X &&& PAGE_MASK) + P#64) + L#64`: an `adrp` page displacement P and low-12 offset L;
  * other hex / >= 5-digit decimal literals in the stub / data range: absolute.
Sizes, stack offsets (`sp + N`) and in-function offsets are left alone. Everything not rewritten
but suspicious is listed in the report (`# review` sections).
"""
import argparse
import bisect
import glob
import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image import Image, PAGE, page_of, decode_ref  # noqa: E402

SEED_PREFIX = ('GeneratedLean.LibsignalSession', 'GeneratedLean.LibsignalTripleRatchet')
# default ROOTs: the proof, specification and test trees (`Computational/`, `LibsignalBinary/`,
# `Symbolic/`)
DEFAULT_ROOTS = ['Computational/Proofs', 'Computational/Specifications', 'Computational/Tests',
                 'LibsignalBinary/Proofs', 'LibsignalBinary/Specifications', 'Symbolic/Proofs',
                 'Symbolic/Specifications']
# skipped under the default ROOTs: the `CryptoGames/` modules (formerly the unscanned top-level
# `CryptoGames/`) and the AGPL-derived KATs (`Computational/Tests/Kat/`, formerly under it)
DEFAULT_SKIP = ('Computational/Specifications/CryptoGames/',
                'Computational/Specifications/Reductions/Primitives/',
                'Computational/Specifications/Session/ACD19/', 'Computational/Proofs/CryptoGames/',
                'Computational/Tests/Kat/', 'LibsignalBinary/Specifications/CryptoGames/',
                'LibsignalBinary/Proofs/CryptoGames/')
# read only for the import graph (and the name abbreviations of imported files)
SCAN_ALL_ROOTS = ['Computational', 'LibsignalBinary',
                  'Symbolic/Proofs', 'Symbolic/Specifications', 'Symbolic/Theorems']
# specification trees (trusted): their sites are reported, never written. The compile-time guards
# of the E2E statement (`Computational/Tests/Guards/`) were under `Specifications/`.
SPEC_DIRS = ('Computational/Specifications/', 'Computational/Tests/Guards/',
             'LibsignalBinary/Specifications/', 'Symbolic/Specifications/')
# the module evaluating the forms
CODE_LAYOUT = 'LibsignalBinary.Proofs.CodeLayout'
CODE_LAYOUT_IMPORT = re.compile(r'^import LibsignalBinary\.Proofs\.CodeLayout\s*$', re.M)
PAGE_MASK_RE = r'(?:18446744073709547520|0x(?:[fF]_?){13}000|0x(?:[fF]{4}_){3}[fF]000)#64'
NUM = re.compile(r'(?<![\w.?#\'])(0x[0-9a-fA-F_]+|\d[\d_]*)(?![\w.\'])')
FORM_HEADS = ('num%', 'bv%', 'nat_lit%', 'page%', 'ls_off%', 'ls_rel%', 'ls_hook%', 'ls_stub%',
              'ls_lemma%', 'ls_sym%', 'ls_str%', 'ls_bytes%', 'ls_reloc%', 'ls_field%', 'ls_xref%',
              'code_off%', 'code_rel%', 'code_lemma%', 'code_xref%', 'img_sym%', 'img_str%',
              'img_bytes%', 'img_reloc%', 'img_field%')
SKIP_LINE = re.compile(r'^\s*(?:set_option|gen_decodes|gen_decode_range|register_fn_entry|import|'
                       r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?gen_decodes)\b')


def val(tok):
    t = tok.replace('_', '')
    return int(t, 16) if t.lower().startswith('0x') else int(t, 10)


def hx(v):
    return hex(v) if v >= 4096 else str(v)


def signed(d):
    return '' if d == 0 else (f' + {hx(d)}' if d > 0 else f' - {hx(-d)}')


def lean_str(bs):
    """A Lean string literal for the UTF-8 bytes `bs`, or None if not plain printable text."""
    try:
        s = bs.decode('utf-8')
    except UnicodeDecodeError:
        return None
    out = []
    for c in s:
        if c == '"':
            out.append('\\"')
        elif c == '\\':
            out.append('\\\\')
        elif c == '\n':
            out.append('\\n')
        elif c == '\t':
            out.append('\\t')
        elif 32 <= ord(c) < 127 or ord(c) >= 0xa0:
            out.append(c)
        else:
            return None
    return '"' + ''.join(out) + '"'


# ------------------------------------------------------------------------------------------------
# Keys: symbolic forms of absolute image offsets
# ------------------------------------------------------------------------------------------------
class Keys:
    MIN_WIN = 12

    def __init__(self, img):
        self.img = img
        self.piece_key_cache = {}
        self.data_syms = sorted((v, k) for k, v in img.syms.items() if v >= img.dataOff)
        self.problems = []
        self.refs_by_target = None
        self.fragile_addr = set()  # addresses keyed by a fragile key (see `fragile_at`)

    def absform(self, a, depth=0):
        """A `Nat` term (no outer parentheses needed for `+`/`-` chains) for image offset `a` in
        the stub / data range, or None."""
        img = self.img
        if img.text_end <= a < img.code_len:
            base = a - a % 4
            name = img.stub_at.get(base)
            if name is None:
                return None
            return f'ls_off% {lean_str(name.encode())}{signed(a - base)}'
        if a == img.code_len:
            return 'ls_field% codeLen'
        if img.code_len < a < img.dataOff:
            return f'ls_field% dataOff - {hx(img.dataOff - a)}'
        if a == img.dataOff and img.piece_of(a) is None:
            return 'ls_field% dataOff'
        if img.gotOff <= a <= img.data_end:
            return f'ls_field% gotOff{signed(a - img.gotOff)}'
        for name, (ea, sz) in img.extern.items():
            if ea <= a <= ea + sz:
                return f'ls_sym% {lean_str(name.encode())}{signed(a - ea)}'
        p = img.piece_of(a) or img.piece_of(a, end_ok=True)
        if p is None:
            # a gap between pieces: key on the nearest piece before it
            i = bisect.bisect_right(img.piece_starts, a) - 1
            if i < 0:
                return None
            p = img.roData[i]
        key = self.piece_key(p, depth)
        if key is None or key[2]:
            # no robust key for the piece: the code that refers to `a` itself, if any
            x = self.xref_key(a)
            if x is not None:
                return x
            if key is None:
                return None
            self.fragile_addr.add(a)
            if depth == 0:  # nested keys pass fragility up through `piece_key`'s flag
                self.problems.append(f'fragile key for {a:#x}: {key[0]}')
        kform, koff, _ = key
        return f'{kform}{signed(a - koff)}'

    def piece_key(self, p, depth=0):
        """`(form, offset, fragile)`: a unique key inside (or at) piece `p`, or None. `fragile`:
        a content window in source paths (see `fragile_at`) or a key derived from one."""
        if p in self.piece_key_cache:
            return self.piece_key_cache[p]
        self.piece_key_cache[p] = None  # cycle guard
        r = self._piece_key(p, depth)
        self.piece_key_cache[p] = r
        if r is None:
            self.problems.append(f'no unique key for .rodata piece {p[0]:#x}+{p[1]}')
        return r

    def _piece_key(self, p, depth):
        img = self.img
        s, n = p
        # 1. a named data symbol in the piece (stable global names: vtables, statics)
        for v, k in self.data_syms:
            if s <= v < s + n:
                return (f'ls_sym% {lean_str(k.encode())}', v, False)
        mask = img.reloc_mask(s, n)
        relocs = img.relocs_in(s, n)
        # 2. a data relocation slot whose target is a code offset (functions do not move) and is
        #    the target of no other slot (vtables, panic locations with a fn pointer)
        for off, w, t in relocs:
            if t < img.text_end and len(img.relocs_to(t)) == 1:
                return (f'ls_reloc% {hx(t)}', off, False)
        # 3. a unique content window in a relocation-free run
        runs, i = [], 0
        while i < n:
            if mask[i]:
                i += 1
                continue
            j = i
            while j < n and not mask[j]:
                j += 1
            runs.append((s + i, j - i))
            i = j
        runs.sort(key=lambda r: -r[1])
        for rs, rn in runs:
            w = self.unique_window(rs, rn, strict=True)
            if w is not None:
                return w + (False,)
        # 4. a relocation slot whose target has a unique form (stub / other data)
        fragile_reloc = None
        if depth < 2:
            for off, w, t in relocs:
                if len(img.relocs_to(t)) != 1:
                    continue
                if img.text_end <= t <= img.data_end and not (s <= t < s + n):
                    tf = self.absform(t, depth + 1)
                    if tf is None:
                        continue
                    if t not in self.fragile_addr:
                        return (f'ls_reloc% ({tf})', off, False)
                    fragile_reloc = fragile_reloc or (f'ls_reloc% ({tf})', off, True)
        # 5. a code reference to the piece start (functions do not move): `adrp` + low-12 user,
        #    preferring an adjacent pair, then the lowest PC
        x = self.xref_key(s)
        if x is not None:
            return (x, s, False)
        if fragile_reloc:
            return fragile_reloc
        # 6. a window in source paths (unique today, but appended crates bring more)
        for rs, rn in runs:
            w = self.unique_window(rs, rn)
            if w is not None:
                return w + (True,)
        # 7. a window that runs past the piece end into the following bytes (identical strings
        #    in two pieces; the next piece disambiguates)
        if not any(mask):
            for extra in (8, 16, 32, 64):
                e = min(s + n + extra, img.dataOff + len(img.data))
                m2 = img.reloc_mask(s, e - s)
                k = 0
                while k < len(m2) and not m2[k]:
                    k += 1
                bs = img.bytes_at(s, k)
                if len(img.occurrences(bs)) == 1:
                    return (self.render(bs, prefer_str=False), s, True)
        return None

    def xref_key(self, t):
        """`ls_xref% …` for a code reference whose target is exactly `t`, or None."""
        if self.refs_by_target is None:
            self.refs_by_target = defaultdict(list)
            for pc, f, kind, tt, apc in self.img.code_refs():
                self.refs_by_target[tt].append((kind, pc, apc))
        cands = []
        for kind, pc, apc in self.refs_by_target.get(t, ()):
            if kind in ('add', 'ldst') and pc - apc <= 16:  # near pairs only (see `Ctx`)
                cands.append((pc - apc != 4, pc, f'ls_xref% {hx(apc)} {hx(pc)}', apc, pc))
            elif kind in ('adr', 'b', 'bl'):
                cands.append((False, pc, f'ls_xref% {hx(pc)}', pc, None))
        for _, _, form, a, b in sorted(cands):
            if Evaluator(self.img).xref(a, b) == t:
                return form
        return None

    # source paths of panic locations (`/rustc/<hash>/library/std/src/sync/once.rs`,
    # `~/.cargo/git/checkouts/<crate>/src/…`): a window in them is unique today, but every crate
    # appended brings more paths with the same toolchain / checkout prefixes and file names
    PATH_MARKERS = (b'/rustc/', b'cargo', b'/library/', b'registry/src/', b'.rs', b'/src/')

    def fragile_at(self, st, ln):
        """The window `[st, st + ln)` lies in (or next to) a source path."""
        a = max(self.img.dataOff, st - 32)
        ctx = self.img.bytes_at(a, st + ln + 32 - a)
        return any(t in ctx for t in self.PATH_MARKERS)

    @staticmethod
    def weak(bs):
        """Low-entropy bytes (zero padding, small integers such as the length / line / column
        words of a panic location, short words): unique today, but an appended crate can
        repeat them by chance."""
        return len(set(bs)) < 8 or bs.count(0) * 2 > len(bs)

    def unique_window(self, rs, rn, strict=False):
        """The shortest unique prefix (at least `MIN_WIN` bytes, or the whole run) of the run
        `[rs, rs + rn)`, then of each later start within the run, as `(form, offset)`. `strict`:
        no window that touches a toolchain path or has low entropy (see `weak`)."""
        img = self.img
        starts = [rs] + [rs + k for k in (1, 2, 4, 8, 16, 32, 64) if k < rn]
        for st in starts:
            avail = rs + rn - st
            for ln in sorted(set([min(self.MIN_WIN, avail), 16, 24, 32, 48, 64, avail])):
                if ln > avail or ln <= 0:
                    continue
                bs = img.bytes_at(st, ln)
                if strict and (self.fragile_at(st, ln) or self.weak(bs)):
                    continue
                if len(img.occurrences(bs)) == 1:
                    # prefer a whole short string (more readable, same uniqueness)
                    whole = img.bytes_at(st, avail)
                    if avail <= 48 and lean_str(whole) and st == rs:
                        bs = whole
                    return (self.render(bs), st)
        return None

    @staticmethod
    def render(bs, prefer_str=True):
        s = lean_str(bs) if prefer_str else None
        if s is not None and len(bs) >= 4:
            return f'ls_str% {s}'
        return f'ls_bytes% "{bs.hex()}"'


# ------------------------------------------------------------------------------------------------
# Evaluator of emitted forms (Python mirror of the elaborators, for the self-check)
# ------------------------------------------------------------------------------------------------
class EvalError(Exception):
    pass


class Evaluator:
    TOK = re.compile(r'\s*(?:(0x[0-9a-fA-F_]+|\d[\d_]*)|("(?:[^"\\]|\\.)*")|([A-Za-z_][\w.%]*)|'
                     r'(\(|\)|\+|-|%|\*|/))')

    def __init__(self, img):
        self.img = img

    def sym(self, name):
        img = self.img
        hits = [img.syms[name]] if name in img.syms else []
        if not hits and name in img.stubs:
            hits = [img.stubs[name]]
        if not hits and name in img.extern:
            hits = [img.extern[name][0]]
        if len(hits) != 1:
            raise EvalError(f'symbol {name!r} not found')
        return hits[0]

    def off(self, name):  # code_off%: fnOff (symbols below the data) else stubOff
        img = self.img
        if name in img.syms:
            return img.syms[name]
        if name in img.stubs:
            return img.stubs[name]
        raise EvalError(f'no fnOff/stubOff for {name!r}')

    def occ(self, bs, what):
        o = self.img.occurrences(bs)
        if len(o) != 1:
            raise EvalError(f'{what}: {len(o)} occurrences')
        return o[0]

    def reloc(self, t):
        o = [r[0] for r in self.img.relocs if r[2] == t]
        if len(o) != 1:
            raise EvalError(f'reloc to {t:#x}: {len(o)} slots')
        return o[0]

    def field(self, f):
        img = self.img
        return {'dataOff': img.dataOff, 'gotOff': img.gotOff, 'codeLen': img.code_len,
                'textEnd': img.text_end, 'dataLen': len(img.data)}[f]

    def xref(self, pc, pc2=None):
        """Mirror of `xrefTarget` (CodeLayout.lean)."""
        img = self.img
        if pc % 4 or pc // 4 >= len(img.words):
            raise EvalError(f'ls_xref%: bad pc {pc}')
        w = img.words[pc // 4]
        d = decode_ref(w, pc)
        if not d or d[0] not in ('adrp', 'adr', 'b', 'bl'):
            raise EvalError(f'ls_xref%: no PC-relative instruction at {pc:#x}')
        t = d[2]
        if pc2 is not None:
            if d[0] != 'adrp' or pc2 % 4 or pc2 // 4 >= len(img.words):
                raise EvalError(f'ls_xref%: bad pair {pc:#x} {pc2:#x}')
            w2 = img.words[pc2 // 4]
            d2 = decode_ref(w2, pc2)
            if not d2 or d2[0] not in ('add', 'ldst') or (w2 >> 5) & 31 != w & 31:
                raise EvalError(f'ls_xref%: no low-12 user of the adrp at {pc2:#x}')
            t += d2[1]
        if t < 0:
            raise EvalError('ls_xref%: negative target')
        return t

    def eval(self, s):
        self.toks = []
        pos = 0
        s = s.strip()
        while pos < len(s):
            m = self.TOK.match(s, pos)
            if not m or m.end() == pos:
                raise EvalError(f'cannot tokenize {s[pos:pos + 20]!r}')
            self.toks.append(next(g for g in m.groups() if g is not None))
            pos = m.end()
        self.i = 0
        v = self.expr()
        if self.i != len(self.toks):
            raise EvalError(f'trailing tokens in {s!r}')
        return v

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def take(self):
        t = self.peek()
        self.i += 1
        return t

    def expr(self):
        v = self.term()
        while self.peek() in ('+', '-'):
            op = self.take()
            r = self.term()
            v = v + r if op == '+' else max(0, v - r)
        return v

    def term(self):
        v = self.atom()
        while self.peek() in ('%', '*', '/'):
            op = self.take()
            r = self.atom()
            v = v % r if op == '%' else (v * r if op == '*' else v // r)
        return v

    def string(self):
        t = self.take()
        if not t or not t.startswith('"'):
            raise EvalError('expected a string')
        body = t[1:-1]
        return re.sub(r'\\(.)', lambda m: {'n': '\n', 't': '\t'}.get(m.group(1), m.group(1)), body)

    def atom(self):
        t = self.take()
        if t is None:
            raise EvalError('unexpected end')
        if t == '(':
            v = self.expr()
            if self.take() != ')':
                raise EvalError('expected )')
            return v
        if re.match(r'0x|\d', t):
            return val(t)
        if t in ('ls_off%', 'code_off%'):
            return self.off(self.string())
        if t == 'ls_sym%':
            return self.sym(self.string())
        if t == 'ls_str%':
            return self.occ(self.string().encode('utf-8'), 'ls_str%')
        if t == 'ls_bytes%':
            return self.occ(bytes.fromhex(self.string().replace('_', '')), 'ls_bytes%')
        if t == 'ls_reloc%':
            return self.reloc(self.atom())
        if t == 'ls_field%':
            return self.field(self.take())
        if t == 'page%':
            return page_of(self.atom())
        if t == 'ls_xref%':
            a = self.take()
            b = None
            if self.peek() is not None and re.match(r'0x|\d', self.peek()):
                b = val(self.take())
            return self.xref(val(a), b)
        raise EvalError(f'unknown token {t!r}')


# ------------------------------------------------------------------------------------------------
# Source masking
# ------------------------------------------------------------------------------------------------
def mask_source(txt):
    """`txt` with comments, string contents and the arguments of existing layout forms blanked
    (same length; newlines kept), so numerals there are never matched."""
    out = list(txt)
    n = len(txt)
    i = 0
    depth = 0

    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '
    while i < n:
        if txt.startswith('/-', i):
            j, d = i + 2, 1
            while j < n and d:
                if txt.startswith('/-', j):
                    d += 1
                    j += 2
                elif txt.startswith('-/', j):
                    d -= 1
                    j += 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif txt.startswith('--', i):
            j = txt.find('\n', i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif txt[i] == '"':
            j = i + 1
            while j < n and txt[j] != '"':
                j += 2 if txt[j] == '\\' else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != '\n':
                    out[k] = '_'
            i = j + 1
        else:
            i += 1
    m = ''.join(out)
    # arguments of existing layout forms (idempotency)
    out = list(m)
    for mm in re.finditer(r'(?<![\w.])(' + '|'.join(re.escape(h) for h in FORM_HEADS) + r')', m):
        j = mm.end()
        while j < n and m[j] in ' \t':
            j += 1
        if j < n and m[j] == '(':
            d, k = 0, j
            while k < n:
                if m[k] == '(':
                    d += 1
                elif m[k] == ')':
                    d -= 1
                    if d == 0:
                        break
                k += 1
            end = k + 1
        else:  # `ls_off% "…"`, `ls_field% dataOff`, `ls_reloc% 0x2f4c`: up to the atoms
            end = j
            for _ in range(2):
                q = re.match(r'\s*(?:"_*"|[\w.]+)', m[end:])
                if not q:
                    break
                end += q.end()
        for k in range(mm.start(), min(end, n)):
            if out[k] != '\n':
                out[k] = ' '
    m = ''.join(out)
    # whole lines that take raw numerals
    out = list(m)
    pos = 0
    for line in m.split('\n'):
        if SKIP_LINE.match(line):
            for k in range(pos, pos + len(line)):
                out[k] = ' '
        pos += len(line) + 1
    return ''.join(out)


# ------------------------------------------------------------------------------------------------
# Per-file analysis
# ------------------------------------------------------------------------------------------------
class Ctx:
    """Everything the classifier needs about the image."""

    def __init__(self, img, name_abbrevs):
        self.img = img
        self.keys = Keys(img)
        self.ev = Evaluator(img)
        self.name_abbrevs = name_abbrevs  # identifier -> symbol name (functions only)
        refs = img.code_refs()
        self.refs = refs
        # per function: targets referenced; per adrp pc: `(user pc, full target)` of its low-12
        # users (`code_refs` pairs a user with the nearest preceding `adrp` in program order, so
        # a far user may really take its base from an `adrp` on another path: prefer near ones)
        self.targets_of = defaultdict(set)
        self.adrp_users = defaultdict(set)
        self.ref_at = defaultdict(list)
        for pc, f, kind, t, apc in refs:
            self.ref_at[pc].append((kind, t, apc))
            if kind in ('bl', 'b', 'adr'):
                self.targets_of[f].add(t)
            elif kind in ('add', 'ldst'):
                self.targets_of[f].add(t)
                self.adrp_users[apc].add((pc, t))
        self.fn_set = set(img.fn_starts)
        self.form_cache = {}

    def absform(self, a):
        if a not in self.form_cache:
            self.form_cache[a] = self.img and self.keys.absform(a)
        return self.form_cache[a]

    def fn_of_name(self, name):
        v = self.img.syms.get(name)
        if v is not None and v < self.img.text_end:
            return v
        return None


def emit(expr, suffix, neg):
    """Replacement text for a numeral token whose value is the `Nat` term `expr`."""
    if suffix == '#64':
        core = f'bv% ({expr})'
    elif suffix:
        core = f'BitVec.ofNat {suffix[1:]} (num% ({expr}))'
    else:
        core = f'num% ({expr})'
    return ('-' if neg else '') + core


LEFT_SP = re.compile(r"(?:\bsp(?:[0-9'_]\w*|[A-Z]\w*)?|\bSP|\bstack\w*|\bframe\w*)\s*[+-]\s*\(?\s*$")
LEFT_BASE = re.compile(r'(?:\bb|\bbase|\.base|\bimgBase|\broBase|\bdataBase|\bb\d|\bb\')\s*\+\s*\(?\s*$')
LEFT_FNADDR = re.compile(r'fnAddr\s+(\w+|"_*")\s*\)?\s*\+\s*(?:BitVec\.ofNat\s+64\s+)?\(?\s*$')
LEFT_FNOFF = re.compile(r'fnOff\s+(\w+|"_*")\s*\)?\s*\+\s*\(?\s*$')
LEFT_ENTRY = re.compile(r'\b(entry\w*|encEntry\s+\w+|\w*[eE]ntry\w*)\s*\)?\s*\+\s*(?:BitVec\.ofNat\s+64\s+)?\(?\s*$')
LEFT_K = re.compile(r'\(\s*k\s*:=\s*$')
LEFT_INT64 = re.compile(r'Int64\.ofBitVec\s*\(?\s*(?:BitVec\.ofNat\s+64\s+)?\(?\s*$')
LEFT_NAME_POS = re.compile(r'\b(\w+)\s+$')
LEFT_LIT_PLUS = re.compile(r'(0x[0-9a-fA-F]+|\d{4,})\s*\+\s*$')
LEFT_CMP = re.compile(r'(?:<|≤|<=|ble|blt|Nat\.ble\s+\w+|Nat\.blt\s+\w+)\s*\(?\s*$')


class FileScan:
    def __init__(self, ctx, path, txt):
        self.ctx, self.path, self.txt = ctx, path, txt
        self.m = mask_source(txt)
        self.line_starts = [0] + [mm.end() for mm in re.finditer('\n', txt)]
        self.out = []        # (start, end, new, rule, value)
        self.review = []     # (line, msg)
        self.claimed = set()
        self.mentioned = self.find_mentioned()

    def line_of(self, p):
        return bisect.bisect_right(self.line_starts, p)

    def find_mentioned(self):
        img, m = self.ctx.img, self.m
        fs = set()
        for x in re.findall(r'libsignalSession\w*?_0x([0-9a-f]+)', m):
            v = int(x, 16)
            if v < img.text_end:
                fs.add(img.fn_of(v))
        for x in re.findall(r'fetchDecodeAt\s+(0x[0-9a-fA-F]+|\d+)', m):
            fs.add(img.fn_of(val(x)))
        for line in self.txt.split('\n'):
            if re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?gen_decodes\b', line):
                for x in re.findall(r'\b(\d+)\b', line.split('[', 1)[-1]):
                    if int(x) < img.text_end:
                        fs.add(img.fn_of(int(x)))
        for mm in NUM.finditer(m):
            v = val(mm.group(1))
            if v in self.ctx.fn_set and v >= 0x100 and (mm.group(1).startswith('0x') or v >= 1000):
                fs.add(v)
        for lit in re.findall(r'"((?:[^"\\]|\\.)*)"', self.txt):
            f = self.ctx.fn_of_name(lit)
            if f is not None:
                fs.add(f)
        for ident in set(re.findall(r'(?<![\w.])(\w+)\b', m)):
            sym = self.ctx.name_abbrevs.get(ident)
            if sym is not None:
                f = self.ctx.fn_of_name(sym)
                if f is not None:
                    fs.add(f)
        return fs

    # --- helpers --------------------------------------------------------------------------------
    def resolve_name(self, tok, pos):
        """Function offset named by identifier / quoted string `tok` (as in the masked text; the
        real string is read from the source at the same position)."""
        if tok.startswith('"'):
            q = re.match(r'"((?:[^"\\]|\\.)*)"', self.txt[pos:])
            return self.ctx.fn_of_name(q.group(1)) if q else None
        sym = self.ctx.name_abbrevs.get(tok)
        if sym is not None:
            return self.ctx.fn_of_name(sym)
        return None

    def entry_hint(self, pos):
        """`F` from the nearest preceding `fnAddr X = entry` / `fnOff X = …` binding (within 60
        lines), else None."""
        lo = self.line_starts[max(0, self.line_of(pos) - 60)]
        seg = self.m[lo:pos]
        best = None
        for mm in re.finditer(r'fnAddr\s+(\w+|"_*")\s*=\s*entry', seg):
            f = self.resolve_name(mm.group(1), lo + mm.start(1))
            if f is not None:
                best = f
        return best

    def enclosing_pc(self, pos):
        lo = self.line_starts[max(0, self.line_of(pos) - 12)]
        seg = self.m[lo:pos]
        hits = re.findall(r'fetchDecodeAt\s+(0x[0-9a-fA-F]+|\d+)|fetch\s+\(?\w*\s*\+?\s*(0x[0-9a-fA-F]+)', seg)
        for a, b in reversed(hits):
            return val(a or b)
        return None

    def left(self, pos, width=90):
        """Masked text before `pos` on the logical line (spanning up to 2 previous lines),
        whitespace-collapsed."""
        lo = self.line_starts[max(0, self.line_of(pos) - 3)]
        s = self.m[lo:pos]
        return re.sub(r'\s+', ' ', s)[-width:]

    def add(self, s, e, new, rule, v):
        if any(k in self.claimed for k in range(s, e)):
            return
        self.claimed.update(range(s, e))
        self.out.append((s, e, new, rule, v))

    # --- rules ----------------------------------------------------------------------------------
    def rule_names(self):
        img, ctx = self.ctx.img, self.ctx
        txt, m = self.txt, self.m
        # `attribute [...] n₁ n₂ …` commands (with their indented continuation lines): it takes
        # identifiers only, so a rewritten name there switches the command to `ls_attribute`
        attr_spans = []
        for mm in re.finditer(r'^attribute\s*\[', m, re.M):
            nxt = re.search(r'\n(?=\S|\n)', m[mm.end():])
            attr_spans.append((mm.start(), mm.end() + nxt.start() if nxt else len(m)))
        attr_done = set()
        for mm in re.finditer(r'(?<![\w.])((?:[\w.]*\.)?libsignalSessionCode_(hookAtOff\?|stubOff|fnOff)_0x([0-9a-f]+))(?![\w?])', m):
            kind, a = mm.group(2), int(mm.group(3), 16)
            if kind == 'fnOff' and not (img.text_end <= a <= img.data_end):
                continue
            ln = self.line_of(mm.start())
            name = img.stub_at.get(a) if kind != 'fnOff' else next(
                (k for k, v in img.syms.items() if v == a), None)
            if name is None:
                self.review.append((ln, f'{mm.group(1)}: no symbol at {a:#x}'))
                continue
            before = m[max(0, mm.start() - 1):mm.start()]
            after = m[mm.end():mm.end() + 40]
            span = next((sp for sp in attr_spans if sp[0] <= mm.start() < sp[1]), None)
            if before == '@' or re.match(r'\s*\(\s*\w+\s*:=', after) or (
                    span and m.find(']', span[0]) > mm.start()):
                self.review.append((ln, f'{mm.group(1)} ({name}): `@`, named argument or '
                                        f'attribute; left alone'))
                continue
            macro = {'hookAtOff?': 'ls_hook%', 'stubOff': 'ls_stub%'}.get(kind)
            q = lean_str(name.encode())
            new = f'({macro} {q})' if macro else f'(ls_lemma% fnOff {q})'
            self.add(mm.start(1), mm.end(1), new, 'name', a)
            if span and span not in attr_done:
                attr_done.add(span)
                self.add(span[0], span[0] + len('attribute'), 'ls_attribute', 'attr', 0)

    # --- adrp -----------------------------------------------------------------------------------
    BASE_ID = re.compile(r"(?:\w+\.)?(?:b|base|b\d|b'|imgBase|roBase|dataBase)")
    NUM64 = r'(0x[0-9a-fA-F_]+|\d[\d_]*)#64'
    DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                      r'(?:theorem|lemma|def|abbrev|example|instance)\b', re.M)

    def binding(self, ident, pos):
        """Function offset `F` bound to identifier `ident` before `pos` in the current declaration:
        `ident = B + F#64` / `B + F#64 = ident` / `fnAddr X = ident` (the last one before `pos`),
        else a file-level `def ident : BitVec 64 := F#64`. None unless `F` is in the text."""
        lo = self.line_starts[max(0, self.line_of(pos) - 80)]
        decls = [mm.start() for mm in self.DECL.finditer(self.m, lo, pos)]
        if decls:
            lo = decls[-1]
        seg = self.m[lo:pos]
        idre = re.escape(ident)
        best = None
        for pat in (rf"(?<![\w.']){idre}\s*=\s*[\w.']+\s*\+\s*{self.NUM64}",
                    rf"[\w.']+\s*\+\s*{self.NUM64}\s*=\s*{idre}(?![\w.'])"):
            for mm in re.finditer(pat, seg):
                if best is None or mm.start() > best[0]:
                    best = (mm.start(), val(mm.group(1)))
        for mm in re.finditer(rf"fnAddr\s+(\w+|\"_*\")\s*\)?\s*=\s*{idre}(?![\w.'])", seg):
            f = self.resolve_name(mm.group(1), lo + mm.start(1))
            if f is not None and (best is None or mm.start() > best[0]):
                best = (mm.start(), f)
        if best is None:
            dm = re.search(rf'\bdef\s+{idre}\s*:\s*BitVec\s+64\s*:=\s*{self.NUM64}', self.m)
            if dm:
                best = (0, val(dm.group(1)))
        if best is None or best[1] >= self.ctx.img.text_end:
            return None
        return best[1]

    def operand_before(self, pos):
        """Start of the left operand of the binary operator at `pos`: back to an unmatched `(`, or
        to `=`, `:`, `,`, `<`, `≤`, `∧`, `∨`, `→`, `↦`, `[`, `{` at depth 0 (at most 4 lines)."""
        m = self.m
        lo = self.line_starts[max(0, self.line_of(pos) - 4)]
        d, i = 0, pos - 1
        while i >= lo:
            c = m[i]
            if c == ')':
                d += 1
            elif c == '(':
                if d == 0:
                    return i + 1
                d -= 1
            elif d == 0 and c in '=:,<≤∧∨→↦[{':
                return i + 1
            i -= 1
        return lo

    def adrp_pcs(self, a, b):
        """`(pcs, how)`: candidate PCs of the `adrp` whose result the operand `m[a:b]` is. The
        operand is a sum of `#64` numerals `k` and `fnAddr X` (PC = F + k), a base (`b`,
        `img.base`; PC = k) or an identifier bound to `base + F` (PC = F + k); otherwise every
        function the file mentions is tried."""
        seg = self.m[a:b]
        k = sum(val(x) for x in re.findall(r'(?<![\w.#])' + self.NUM64, seg))
        fm = list(re.finditer(r'fnAddr\s+(\w+|"_*")', seg))
        if fm:
            f = self.resolve_name(fm[-1].group(1), a + fm[-1].start(1))
            return ([f + k], 'fnAddr') if f is not None else ([], 'fnAddr ?')
        ids = re.findall(r"(?<![\w.'#])([A-Za-z_][\w.']*)", seg)
        if any(self.BASE_ID.fullmatch(x) for x in ids):
            return [k], 'base'
        for x in ids:
            f = self.binding(x, a)
            if f is not None:
                return [f + k], f'{x} = base + {f:#x}'
        return [f + k for f in sorted(self.mentioned)], 'mentioned'

    def adrp_solve(self, apc, P, L1, T):
        """`(P form, L1 form, T form)` (None: not rewritten) if the `adrp` at `apc` explains the
        immediate `P`, else None. `P` is either the page displacement (`page(t) - page(apc)`,
        then `L1` is the low-12 offset of `t` and a page-aligned `T` is the page) or a combined
        displacement `t - page(apc)` with `t` on the `adrp`'s page. `apc` may also be a later
        instruction on the `adrp`'s page (up to 4 instructions on): only its page matters."""
        img = self.ctx.img
        if apc < 0 or apc % 4 or apc >= img.text_end:
            return None
        for back in range(5):
            a = apc - 4 * back
            if a < 0 or page_of(a) != page_of(apc):
                break
            d = decode_ref(img.words[a // 4], a)
            if d and d[0] == 'adrp':
                r = self.adrp_solve1(a, d[2], P, L1, T)
                if r is not None:
                    return r
        return None

    NEAR = 16  # an `adrp` user at most 4 instructions on is its genuine pair

    def adrp_solve1(self, apc, page_t, P, L1, T):
        ctx, img = self.ctx, self.ctx.img
        pp = page_of(apc)
        sub = f' - {hx(pp)}' if pp else ''
        # users on the page, nearest first
        users = sorted((upc - apc, upc, u) for upc, u in ctx.adrp_users.get(apc, ())
                       if page_of(u) == page_t)

        def user_form(d, upc, u):
            """A data key for a near user's target; the code for a far one (its base may come
            from an `adrp` on another path, so its target need not be a fixed data object)."""
            if d <= self.NEAR:
                return ctx.absform(u)
            return f'ls_xref% {hx(apc)} {hx(upc)}'

        if P == page_t - pp:
            if not (img.in_layout_range(page_t) or img.in_layout_range(page_t + PAGE - 1)):
                return None
            if L1 is not None:
                hit, delta = next((x for x in users if x[2] % PAGE == L1), None), 0
                if hit is None:  # `L` = low-12 offset + a field offset
                    below = [x for x in users if 0 < L1 - x[2] % PAGE < 64]
                    if below:
                        hit = min(below, key=lambda x: (L1 - x[2] % PAGE, x[0]))
                        delta = L1 - hit[2] % PAGE
                if hit is not None:
                    tf = user_form(*hit)
                elif not users and img.in_layout_range(page_t + L1):
                    tf = ctx.absform(page_t + L1)
                else:
                    tf = None
                if tf is None:
                    return None
                return (f'page% ({tf}){sub}', f'({tf}) % 4096{signed(delta)}', None)
            tf = ctx.absform(users[0][2]) if users and users[0][0] <= self.NEAR else None
            pf = f'page% ({tf})' if tf else f'ls_xref% {hx(apc)}'
            return (f'{pf}{sub}', None, pf if T == page_t else None)
        t = pp + P
        if 0 <= t - page_t < PAGE and img.in_layout_range(t):
            tf = ctx.absform(t)
            return (f'{tf}{sub}', None, None) if tf else None
        return None

    def rule_adrp(self):
        """`(X &&& PAGE_MASK) + P#64`, optionally `+ L#64 …` and `= B + T#64`."""
        img, m = self.ctx.img, self.m
        nre = self.NUM64
        for mm in re.finditer(r'&&&\s*' + PAGE_MASK_RE, m):
            pm = re.match(r'\s*\)?\s*\+\s*' + nre, m[mm.end():])
            if not pm:
                continue
            ln = self.line_of(mm.start())
            P = val(pm.group(1))
            ptok = (mm.end() + pm.start(1), mm.end() + pm.end(1) + 3)
            pos = mm.end() + pm.end()
            Ls = []
            while True:
                lm = re.match(r'\s*\)?\s*\+\s*' + nre, m[pos:])
                if not lm:
                    break
                Ls.append((val(lm.group(1)), pos + lm.start(1), pos + lm.end(1) + 3))
                pos += lm.end()
            T = None
            tm = re.match(r"\s*\)*\s*=\s*([\w.']+)\s*\+\s*" + nre, m[pos:])
            if tm and self.BASE_ID.fullmatch(tm.group(1)):
                T = (val(tm.group(2)), pos + tm.start(2), pos + tm.end(2) + 3)
            L1 = Ls[0][0] if Ls and Ls[0][0] < PAGE else None
            apcs, how = self.adrp_pcs(self.operand_before(mm.start()), mm.start())
            sols = {}
            for apc in apcs:
                r = self.adrp_solve(apc, P, L1, T[0] if T else None)
                if r is not None:
                    sols.setdefault(r, []).append(apc)
            if len(sols) != 1:
                if sols or img.in_layout_range(P) or (P >= PAGE and how != 'mentioned'):
                    self.review.append((ln, f'adrp immediate {pm.group(1)} ({how}): '
                                            f'{len(sols)} solutions {[s[0] for s in sols][:3]}'))
                continue
            pf, lf, tf = next(iter(sols))
            self.add(*ptok, emit(pf, '#64', False), 'adrp', P)
            if lf is not None:
                self.add(Ls[0][1], Ls[0][2], emit(lf, '#64', False), 'lo12', L1)
            if tf is not None:
                self.add(T[1], T[2], emit(tf, '#64', False), 'adrp-page', T[0])

    def classify_numeral(self, mm):
        """Handle one numeral token (not inside a form). Returns nothing; records edits."""
        ctx, img = self.ctx, self.ctx.img
        tok = mm.group(1)
        s, e = mm.start(1), mm.end(1)
        if any(k in self.claimed for k in range(s, e)):
            return
        v = val(tok)
        suf_m = re.match(r'#(\d+)', self.m[e:e + 4])
        suffix = suf_m.group(0) if suf_m else ''
        end = e + len(suffix)
        neg = False
        # a leading unary minus (`-N`, `(-N`), not a binary one
        pre = self.m[max(0, s - 2):s]
        if pre.endswith('-') and (len(pre) < 2 or pre[0] in ' (,[=:') and not re.search(
                r'[\w)]\s*-$', self.m[max(0, s - 3):s]):
            neg = True
        L = self.left(s)
        ln = self.line_of(s)
        is_big = tok.lower().startswith('0x') or len(tok.replace('_', '')) >= 5

        def put(expr, rule):
            ss = s - 1 if neg else s
            self.add(ss, end, emit(expr, suffix, neg), rule, v)

        # stack / frame offsets: never layout
        if LEFT_SP.search(L):
            return
        # distances from a function
        f, hint_kind = None, None
        mfn = LEFT_FNADDR.search(L) or LEFT_FNOFF.search(L)
        if mfn:
            f = self.resolve_name(mfn.group(1), s - len(L) + mfn.start(1)) if not mfn.group(1).startswith('"') \
                else self.resolve_name_from_txt(s, mfn)
            hint_kind = 'fn'
        elif LEFT_K.search(L):
            seg = self.m[self.line_starts[max(0, ln - 6)]:s]
            nm = re.search(r'\(\s*name\s*:=\s*(\w+)\s*\)', seg)
            if nm:
                f = self.resolve_name(nm.group(1), 0)
            if f is None:
                hks = {int(x, 16) for x in re.findall(r'libsignalSessionCode_fnOff_0x([0-9a-f]+)', seg)}
                hks = {h for h in hks if h < img.text_end}
                hit = {h for h in hks if h + v in ctx.targets_of.get(h, ())}
                if len(hit) == 1:
                    f = next(iter(hit))
                elif len(hks) == 1:
                    f = next(iter(hks))
            hint_kind = 'k'
        elif LEFT_INT64.search(L):
            pc = self.enclosing_pc(s)
            sv = -v if neg else v
            if pc is not None:
                for kind, t, _ in ctx.ref_at.get(pc, []):
                    if kind in ('bl', 'b', 'adr') and t - pc == sv:
                        tf = ctx.absform(t)
                        if tf:
                            put(f'{tf} - {hx(pc)}', 'imm')
                        return
                    if kind == 'adrp' and t - page_of(pc) == sv:
                        r = self.adrp_solve1(pc, t, sv, None, None)
                        if r is not None:
                            put(r[0], 'imm')
                        return
                return
            cands = {(pc2, t) for pc2, f2, kind, t, _ in ctx.refs
                     if kind in ('bl', 'b', 'adr') and t - pc2 == sv and f2 in self.mentioned}
            if len(cands) == 1:
                pc2, t = next(iter(cands))
                tf = ctx.absform(t)
                if tf:
                    put(f'{tf} - {hx(pc2)}', 'imm')
            elif len(cands) > 1 and v >= 256:
                self.review.append((ln, f'branch immediate {tok}: {len(cands)} candidates'))
            return
        elif LEFT_ENTRY.search(L):
            f = self.entry_hint(s)
            hint_kind = 'entry'
        elif LEFT_LIT_PLUS.search(L) and not LEFT_BASE.search(L):
            fl = val(LEFT_LIT_PLUS.search(L).group(1))
            if fl in ctx.fn_set:
                f, hint_kind = fl, 'lit'
        elif not suffix and re.search(r'\b(\w+)\s+(?:"_*"\s+)?$', L):
            pm = re.search(r'\b(\w+)\s+(?:"_*"\s+)?$', L)
            nm = pm.group(1) if pm else None
            if nm in ctx.name_abbrevs:
                f = ctx.fn_of_name(ctx.name_abbrevs[nm])
                hint_kind = 'pos'
        if hint_kind is not None:
            if neg or v < 256:
                return
            cands = [f] if f is not None else sorted(self.mentioned)
            sols = {(f2, f2 + v) for f2 in cands if f2 + v in ctx.targets_of.get(f2, ())}
            if f is not None and not sols and img.in_layout_range(f + v):
                sols = {(f, f + v)}  # a target F does not reference directly (e.g. a tail)
            if len(sols) == 1:
                f2, t = next(iter(sols))
                tf = ctx.absform(t)
                if tf is None:
                    self.review.append((ln, f'distance {tok} from {f2:#x}: target {t:#x} has no key'))
                    return
                put(f'{tf} - {hx(f2)}', 'rel')
                return
            if len(sols) > 1:
                forms = {f'{ctx.absform(t)} - {hx(f2)}' for f2, t in sols}
                self.review.append((ln, f'distance {tok}: {len(sols)} candidate functions'))
                return
            if f is None and is_big and img.in_layout_range(v):
                pass  # fall through to the absolute rule
            else:
                return
        # absolute values
        if neg or not is_big:
            return
        if v == img.text_end - 1:
            put('ls_field% textEnd - 1', 'code-end')
            return
        if v == img.text_end and (LEFT_CMP.search(L) or re.match(r'\s*(?:≤|<|>|≥)', self.m[end:end + 3])):
            put('ls_field% textEnd', 'code-end')
            return
        if v == len(img.data) and re.search(r'(?:length|size|len)\w*\s*(?:==|=)\s*$|data\s+$', L):
            put('ls_field% dataLen', 'data-len')
            return
        if not img.in_layout_range(v):
            return
        tf = ctx.absform(v)
        if tf is None:
            self.review.append((ln, f'absolute {tok}: no key'))
            return
        rule = 'abs' if LEFT_BASE.search(L) else 'abs-other'
        put(tf, rule)

    def resolve_name_from_txt(self, s, mfn):
        # the quoted symbol of `fnAddr "…" + N`: find it in the source just before `s`
        seg = self.txt[max(0, s - 300):s]
        q = list(re.finditer(r'fnAddr\s+"((?:[^"\\]|\\.)*)"', seg))
        return self.ctx.fn_of_name(q[-1].group(1)) if q else None

    def run(self):
        self.rule_names()
        self.rule_adrp()
        for mm in NUM.finditer(self.m):
            self.classify_numeral(mm)
        return self

    def apply(self):
        res, pos = [], 0
        for s, e, new, rule, v in sorted(self.out):
            res.append(self.txt[pos:s])
            # an application argument (after an identifier, numeral or closing bracket): `bv% x`
            # and `num% x` are not arguments, so parenthesise
            k = s - 1
            while k >= 0 and self.m[k].isspace():
                k -= 1
            prev = self.m[k] if k >= 0 else ''
            if not new.startswith('(') and rule not in ('attr',) and re.match(r"[\w)\]'»]", prev):
                new = f'({new})'
            res.append(new)
            pos = e
        res.append(self.txt[pos:])
        return ''.join(res)


# ------------------------------------------------------------------------------------------------
# Driver
# ------------------------------------------------------------------------------------------------
def lean_files(roots):
    files = []
    for r in roots:
        if os.path.isdir(r):
            files += glob.glob(os.path.join(r, '**', '*.lean'), recursive=True)
        elif r.endswith('.lean') and os.path.exists(r):
            files.append(r)
    return sorted(set(os.path.normpath(f) for f in files))


def in_scope(files, all_files):
    mod = {f: f[:-5].replace(os.sep, '.') for f in all_files}
    imports = {mod[f]: re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', open(f).read(), re.M)
               for f in all_files}
    memo = {}

    def dep(m, stack=()):
        if m.startswith(SEED_PREFIX):
            return True
        if m in memo:
            return memo[m]
        if m in stack or m not in imports:
            return False
        memo[m] = any(dep(i, stack + (m,)) for i in imports[m])
        return memo[m]
    return [f for f in files if dep(mod[f])]


def name_abbrevs_by_file(all_files, img):
    """`path -> {identifier: function symbol}` from the `abbrev|def X : String := "…"` in the file
    and its transitive imports (the same identifier names different functions in different
    files, e.g. `encodeChainName`)."""
    mod = {f: f[:-5].replace(os.sep, '.') for f in all_files}
    defs, imports = {}, {}
    for f in all_files:
        txt = open(f).read()
        imports[mod[f]] = re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', txt, re.M)
        defs[mod[f]] = {i: lit for i, lit in re.findall(
            r'(?:abbrev|def)\s+(\w+)\s*:\s*String\s*:=\s*"((?:[^"\\]|\\.)*)"', txt)
            if lit in img.syms and img.syms[lit] < img.text_end}
    memo = {}

    def closure(m):
        if m not in memo:
            memo[m] = frozenset()  # cycle guard
            acc = {m}
            for i in imports.get(m, ()):
                if i in imports:
                    acc |= closure(i)
            memo[m] = frozenset(acc)
        return memo[m]

    def of(path):
        m = mod[os.path.normpath(path)]
        out = {}
        for d in sorted(closure(m) - {m}):
            out.update(defs.get(d, {}))
        out.update(defs.get(m, {}))
        return out
    return of


def add_import(txt):
    if CODE_LAYOUT_IMPORT.search(txt):
        return txt
    lines = txt.split('\n')
    last = max(i for i, l in enumerate(lines) if re.match(r'^\s*(?:public\s+)?import\s', l))
    lines.insert(last + 1, f'import {CODE_LAYOUT}')
    return '\n'.join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--gen', default='.GeneratedLean/GeneratedLean')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--report')
    ap.add_argument('--lean-check', help='write a Lean file of `example`s checking every form')
    ap.add_argument('roots', nargs='*')
    a = ap.parse_args()
    img = Image(a.gen)
    scan_all = lean_files(SCAN_ALL_ROOTS)
    abbrevs_of = name_abbrevs_by_file(scan_all, img)
    ctx = Ctx(img, {})
    candidates = lean_files(a.roots) if a.roots else [
        f for f in lean_files(DEFAULT_ROOTS) if not f.startswith(DEFAULT_SKIP)]
    files = in_scope(candidates, scan_all)
    report, review, spec, bad = [], [], [], []
    counts, per_file = Counter(), {}
    checks = {}
    for path in files:
        txt = open(path).read()
        ctx.name_abbrevs = abbrevs_of(path)
        fs = FileScan(ctx, path, txt).run()
        if not fs.out and not fs.review:
            continue
        for ln, msg in fs.review:
            review.append(f'{path}:{ln}: {msg}')
        good = []
        for s, e, new, rule, v in fs.out:
            ln = fs.line_of(s)
            exprs = re.findall(r'(?:bv%|num%) \((.*)\)\)?$', new)
            ok = True
            if rule not in ('name', 'attr'):
                inner = re.match(r'-?(?:bv% |BitVec\.ofNat \d+ \(num% |num% )\((.*)\)\)?$', new)
                try:
                    got = ctx.ev.eval(inner.group(1))
                    if got != v:
                        ok = False
                        bad.append(f'{path}:{ln}: {txt[s:e]} -> {new}: evaluates to {got}, not {v}')
                    else:
                        checks.setdefault(inner.group(1), v)
                except (EvalError, AttributeError) as ex:
                    ok = False
                    bad.append(f'{path}:{ln}: {txt[s:e]} -> {new}: {ex}')
            if ok:
                good.append((s, e, new, rule, v))
                line = f'{path}:{ln}: {txt[s:e]} -> {new} [{rule}]'
                (spec if path.startswith(SPEC_DIRS) else report).append(line)
                if not path.startswith(SPEC_DIRS):
                    counts[rule] += 1
        fs.out = good
        if good and not path.startswith(SPEC_DIRS):
            per_file[path] = Counter(r[3] for r in good)
            if a.apply:
                open(path, 'w').write(add_import(fs.apply()))
    summary = (f'{sum(counts.values())} replacements in {len(per_file)} files ({dict(counts)}); '
               f'{len(spec)} sites in specification trees (report only); {len(review)} to review; '
               f'{len(bad)} failed the self-check (left alone); '
               f'{len(ctx.keys.problems)} key problems')
    print(summary)
    if a.report:
        lines = [f'image: text end {img.text_end:#x}, code end {img.code_len:#x}, dataOff '
                 f'{img.dataOff:#x}, GOT {img.gotOff:#x}, data end {img.data_end:#x}', '', summary, '',
                 '# per-file counts'] + [f'{p}: {dict(c)}' for p, c in sorted(per_file.items())]
        lines += ['', '# key problems'] + sorted(set(ctx.keys.problems))
        lines += ['', '# failed self-check (left alone)'] + bad
        lines += ['', '# review (left alone)'] + review
        lines += ['', '# specification-tree (`SPEC_DIRS`) sites (trusted; not rewritten)'] + spec
        lines += ['', '# all replacements'] + report
        open(a.report, 'w').write('\n'.join(lines) + '\n')
    if a.lean_check:
        out = ['import GeneratedLean.LibsignalSessionCode', 'import GeneratedLean.LibsignalSessionObj',
               f'import {CODE_LAYOUT}', '', '-- generated by symbolize.py --lean-check', '']
        for expr, v in sorted(checks.items()):
            out.append(f'example : (num% ({expr}) : Nat) = {v} := rfl')
        open(a.lean_check, 'w').write('\n'.join(out) + '\n')
    if not a.apply:
        print('(dry run: pass --apply to write)')


if __name__ == '__main__':
    main()
