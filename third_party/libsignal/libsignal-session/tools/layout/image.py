# Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
# See `third_party/libsignal/README.md`.

"""One `rust-obj2lean` export of the libsignal-session image, for the layout tools.

`Image(gen_dir)` reads `LibsignalSessionObj.{lean,code.bin,data.bin}` from a `rust-obj2lean` output
directory (normally `.GeneratedLean/GeneratedLean`): the symbol table, the extern stubs, the
`.rodata` pieces, the extern data objects, the GOT (global offset table) and the data relocations.
`Image.code_refs()` lists every PC-relative reference from the text into the stubs or the data
(`bl`/`b`/`adr` targets and `adrp` + low-12 `add`/`ldr`/`str` pairs).

Offsets are image offsets (code at 0; `dataOff` is where the data region starts).
"""
import bisect
import re
import struct
from collections import defaultdict

OBJ = 'LibsignalSessionObj'
PAGE = 4096


def section(txt, field):
    """The text of the Lean structure field `field := [...]` (up to the next field)."""
    m = txt.index(f'\n  {field} := [')
    nxt = re.search(r'\n  [A-Za-z]+ :=', txt[m + 1:])
    return txt[m:m + 1 + nxt.start()] if nxt else txt[m:]


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def page_of(a):
    return a // PAGE * PAGE


def decode_ref(w, pc):
    """`(kind, imm, target)` of a PC-relative or low-12 instruction word, else None. `imm` is the
    value the engine's decoder shows (`bl`/`b`/`adr`: byte displacement; `adrp`: page displacement
    in bytes; `add`/`ldr`/`str`: byte offset, `target` None)."""
    if (w & 0x7C000000) == 0x14000000:
        d = 4 * sext(w & 0x3FFFFFF, 26)
        return ('bl' if w >> 31 else 'b', d, pc + d)
    if (w & 0x9F000000) == 0x90000000:
        imm = sext((((w >> 5) & 0x7FFFF) << 2) | ((w >> 29) & 3), 21) << 12
        return ('adrp', imm, page_of(pc) + imm)
    if (w & 0x9F000000) == 0x10000000:
        imm = sext((((w >> 5) & 0x7FFFF) << 2) | ((w >> 29) & 3), 21)
        return ('adr', imm, pc + imm)
    if (w & 0x7F800000) == 0x11000000 and not (w >> 22) & 1:  # add/adds (immediate), sh = 0
        return ('add', (w >> 10) & 0xFFF, None)
    if (w & 0x3B000000) == 0x39000000:  # ldr/str (unsigned offset)
        size, v, opc = w >> 30, (w >> 26) & 1, (w >> 22) & 3
        scale = 16 if (v and size == 0 and opc & 2) else (1 << size)
        return ('ldst', ((w >> 10) & 0xFFF) * scale, None)
    return None


class Image:
    def __init__(self, gen_dir):
        txt = open(f'{gen_dir}/{OBJ}.lean').read()
        self.syms = {}
        for name, off in re.findall(r'\("((?:[^"\\]|\\.)*)", (\d+)\)', section(txt, 'symbols')):
            self.syms.setdefault(unescape(name), int(off))
        self.stubs = {unescape(n): int(o) for n, o in
                      re.findall(r'\("((?:[^"\\]|\\.)*)", (\d+)\)', section(txt, 'stubs'))}
        self.code = open(f'{gen_dir}/{OBJ}.code.bin', 'rb').read()
        self.data = open(f'{gen_dir}/{OBJ}.data.bin', 'rb').read()
        self.words = [struct.unpack_from('<I', self.code, i)[0]
                      for i in range(0, len(self.code) - 3, 4)]
        self.dataOff = int(re.search(r'\n  dataOff := (0x[0-9a-f]+)', txt).group(1), 16)
        self.gotOff = int(re.search(r'\n  gotOff := (0x[0-9a-f]+)', txt).group(1), 16)
        self.got_n = len(re.findall(r'\n    \.', section(txt, 'got')))
        self.roData = sorted((int(a, 16), int(n)) for a, n in
                             re.findall(r'\((0x[0-9a-f]+), (\d+)\)', section(txt, 'roData')))
        self.extern = {unescape(n): (int(a, 16), int(s)) for n, a, s in
                       re.findall(r'\("((?:[^"\\]|\\.)*)", (0x[0-9a-f]+), (\d+)\)',
                                  section(txt, 'externData'))}
        # `relocs.off` is relative to `dataOff`; `target` is an image offset
        self.relocs = sorted((self.dataOff + int(o, 16), int(w), int(t, 16)) for o, w, t in re.findall(
            r'off := (0x[0-9a-f]+), width := (\d+), target := (0x[0-9a-f]+)', section(txt, 'relocs')))
        self.reloc_offs = [r[0] for r in self.relocs]
        self.text_end = min(self.stubs.values())
        self.code_len = max(self.stubs.values()) + 4
        self.stub_at = {v: k for k, v in self.stubs.items()}
        self.data_end = self.gotOff + 8 * self.got_n
        self.fn_starts = sorted(set(v for v in self.syms.values() if v < self.text_end))
        self.sym_at = defaultdict(list)
        for k, v in self.syms.items():
            self.sym_at[v].append(k)
        self.piece_starts = [a for a, _ in self.roData]

    # --- code ---------------------------------------------------------------------------------
    def fn_of(self, pc):
        i = bisect.bisect_right(self.fn_starts, pc) - 1
        return self.fn_starts[i] if i >= 0 else 0

    def in_layout_range(self, t):
        """`t` is in the stub area or the data region (moves when code is appended)."""
        return self.text_end <= t <= self.data_end

    def code_refs(self):
        """`(pc, fn, kind, target, apc)` for every reference from the text into the stubs or the
        data: `bl`/`b`/`adr` (`apc` None), `adrp` (target = the page), and `add`/`ldst` paired with
        the nearest preceding `adrp` of its base register in the same function (`apc` = that
        `adrp`'s PC; target = page + low-12 offset)."""
        out = []
        n = self.text_end // 4
        last_adrp = {}  # reg -> (pc, page) within the current function
        cur_fn = None
        for i in range(n):
            pc = 4 * i
            f = self.fn_of(pc)
            if f != cur_fn:
                cur_fn, last_adrp = f, {}
            w = self.words[i]
            d = decode_ref(w, pc)
            if not d:
                continue
            kind = d[0]
            if kind in ('bl', 'b', 'adr'):
                if self.in_layout_range(d[2]):
                    out.append((pc, f, kind, d[2], None))
            elif kind == 'adrp':
                last_adrp[w & 0x1F] = (pc, d[2])
                if self.in_layout_range(d[2]) or self.in_layout_range(d[2] + PAGE - 1):
                    out.append((pc, f, 'adrp', d[2], pc))
            else:
                rn = (w >> 5) & 0x1F
                if rn in last_adrp:
                    apc, page = last_adrp[rn]
                    t = page + d[1]
                    if self.in_layout_range(t):
                        out.append((pc, f, kind, t, apc))
        return out

    # --- data ---------------------------------------------------------------------------------
    def piece_of(self, a, end_ok=False):
        """`(start, len)` of the `.rodata` piece holding `a` (or ending at `a` if `end_ok`)."""
        i = bisect.bisect_right(self.piece_starts, a) - 1
        if i >= 0:
            s, n = self.roData[i]
            if s <= a < s + n or (end_ok and a == s + n):
                return (s, n)
        return None

    def relocs_in(self, a, n):
        i = bisect.bisect_left(self.reloc_offs, a - 7)
        out = []
        while i < len(self.relocs) and self.relocs[i][0] < a + n:
            if self.relocs[i][0] + self.relocs[i][1] > a:
                out.append(self.relocs[i])
            i += 1
        return out

    def reloc_mask(self, a, n):
        """Per byte of `[a, a + n)`: True if it belongs to a relocation slot."""
        m = [False] * n
        for off, w, _ in self.relocs_in(a, n):
            for k in range(max(off, a), min(off + w, a + n)):
                m[k - a] = True
        return m

    def bytes_at(self, a, n):
        return self.data[a - self.dataOff:a - self.dataOff + n]

    def occurrences(self, needle):
        out, i = [], self.data.find(needle)
        while i >= 0:
            out.append(self.dataOff + i)
            i = self.data.find(needle, i + 1)
        return out

    def relocs_to(self, t):
        return [r[0] for r in self.relocs if r[2] == t]


def unescape(s):
    """Lean string literal body -> str (the escapes `rust-obj2lean` emits)."""
    if '\\' not in s:
        return s
    return re.sub(r'\\(["\\nt]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\})',
                  lambda m: {'"': '"', '\\': '\\', 'n': '\n', 't': '\t'}.get(m.group(1)) or
                  chr(int(m.group(1)[1:].strip('{}'), 16)), s)
