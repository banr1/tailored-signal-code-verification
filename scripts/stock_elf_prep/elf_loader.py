# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Bit-exact ELF64 loader mirroring `Arm64/Trusted/Process/Loader.lean`, raw ELF parsers,
and parsers/interners for `MultiPlacedLib` and `ExtractedObj`."""

from __future__ import annotations

import pathlib
import re
import struct
from dataclasses import dataclass, field

PAGE_SIZE = 4096


@dataclass(frozen=True)
class Perm:
    r: bool
    w: bool
    x: bool

    def lean_expr(self) -> str:
        if (self.r, self.w, self.x) == (True, False, False):
            return "Perm.ro"
        if (self.r, self.w, self.x) == (True, True, False):
            return "Perm.rw"
        if (self.r, self.w, self.x) == (True, False, True):
            return "Perm.rx"
        return f"{{ r := {str(self.r).lower()}, w := {str(self.w).lower()}, x := {str(self.x).lower()} }}"


PERM_RO = Perm(True, False, False)
PERM_RW = Perm(True, True, False)
PERM_RX = Perm(True, False, True)


@dataclass
class ElfRegion:
    start: int
    bytes_data: bytes
    perm: Perm
    nonAnonLen: int
    phdr_idx: int

    @property
    def end(self) -> int:
        return self.start + len(self.bytes_data)


@dataclass
class ElfImage:
    entry: int
    phdrVaddr: int
    phent: int
    phnum: int
    brkStart: int
    regions: list[ElfRegion]
    symbols: list[tuple[str, int]]  # non-local STT_FUNC defined symbols matching Loader.lean

    def region_view(self, addr: int) -> tuple[int, Perm, bytes] | None:
        """Exact mirror of `Check.regionView` (`Check.lean:86-93`)."""
        for reg in self.regions:
            end = reg.start + len(reg.bytes_data)
            if reg.start <= addr <= end:
                return (reg.start, reg.perm, reg.bytes_data)
        return None

    def read_bytes(self, addr: int, length: int) -> tuple[bytes, Perm] | None:
        for reg in self.regions:
            if reg.start <= addr and addr + length <= reg.end:
                off = addr - reg.start
                return reg.bytes_data[off : off + length], reg.perm
        return None

    def read_u32(self, addr: int) -> int | None:
        got = self.read_bytes(addr, 4)
        if got is None:
            return None
        return struct.unpack("<I", got[0])[0]

    def read_u64(self, addr: int) -> int | None:
        got = self.read_bytes(addr, 8)
        if got is None:
            return None
        return struct.unpack("<Q", got[0])[0]


@dataclass(frozen=True)
class RawPhdr:
    idx: int
    p_type: int
    p_flags: int
    p_offset: int
    p_vaddr: int
    p_paddr: int
    p_filesz: int
    p_memsz: int
    p_align: int
    raw_bytes: bytes


@dataclass(frozen=True)
class RawElfSection:
    idx: int
    name: str
    sh_type: int
    sh_flags: int
    sh_addr: int
    sh_offset: int
    sh_size: int
    sh_link: int
    sh_info: int
    sh_addralign: int
    sh_entsize: int


@dataclass(frozen=True)
class RawElfSym:
    idx: int
    name: str
    st_info: int
    st_other: int
    st_shndx: int
    st_value: int
    st_size: int
    bind: int
    stype: int
    is_local: bool


def _read_cstr(buf: bytes, off: int) -> str:
    if off < 0 or off >= len(buf):
        return ""
    end = buf.find(b"\x00", off)
    if end == -1:
        end = len(buf)
    return buf[off:end].decode("utf-8", errors="replace")


def parse_raw_elf(
    elf_bytes: bytes,
    *,
    require_symtab: bool = False,
) -> tuple[ElfImage, list[RawPhdr], list[RawElfSection], list[RawElfSym]]:
    """Parse raw ELF64 + construct exact `Arm64.Loader.ElfImage.parse` result."""
    if len(elf_bytes) < 64:
        raise ValueError("ELF file shorter than 64-byte header")
    if elf_bytes[:4] != b"\x7fELF":
        raise ValueError("Bad ELF magic")
    ei_class, ei_data, _ei_ver = elf_bytes[4], elf_bytes[5], elf_bytes[6]
    if ei_class != 2 or ei_data != 1:
        raise ValueError(f"Expected ELF64 LE, got class={ei_class}, data={ei_data}")

    (
        e_type,
        e_machine,
        _e_version,
        e_entry,
        e_phoff,
        e_shoff,
        _e_flags,
        _e_ehsize,
        e_phentsize,
        e_phnum,
        e_shentsize,
        e_shnum,
        e_shstrndx,
    ) = struct.unpack_from("<HHIQQQIHHHHHH", elf_bytes, 16)

    if e_type != 2:
        raise ValueError(f"Expected ET_EXEC (2), got e_type={e_type}")
    if e_machine != 183:
        raise ValueError(f"Expected EM_AARCH64 (183), got e_machine={e_machine}")
    if e_phentsize != 56 or e_phnum == 0:
        raise ValueError(f"Unexpected PHDR table phentsize={e_phentsize}, phnum={e_phnum}")
    if e_phoff + e_phnum * e_phentsize > len(elf_bytes):
        raise ValueError("PHDR table exceeds file bounds")

    phdrs: list[RawPhdr] = []
    unsorted_regions: list[ElfRegion] = []
    phdr_vaddr_opt: int | None = None

    for i in range(e_phnum):
        off = e_phoff + i * 56
        raw_b = elf_bytes[off : off + 56]
        p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align = struct.unpack(
            "<IIQQQQQQ", raw_b
        )
        phdrs.append(
            RawPhdr(
                idx=i,
                p_type=p_type,
                p_flags=p_flags,
                p_offset=p_offset,
                p_vaddr=p_vaddr,
                p_paddr=p_paddr,
                p_filesz=p_filesz,
                p_memsz=p_memsz,
                p_align=p_align,
                raw_bytes=raw_b,
            )
        )
        if p_type == 6:  # PT_PHDR
            phdr_vaddr_opt = p_vaddr

    for ph in phdrs:
        if ph.p_type != 1 or ph.p_memsz == 0:
            continue
        if ph.p_filesz > ph.p_memsz:
            raise ValueError(f"PT_LOAD[{ph.idx}] filesz > memsz")
        if ph.p_filesz > 0 and (ph.p_vaddr % PAGE_SIZE != ph.p_offset % PAGE_SIZE):
            raise ValueError(f"PT_LOAD[{ph.idx}] vaddr/offset page-congruence violation")
        page_start = (ph.p_vaddr // PAGE_SIZE) * PAGE_SIZE
        lead = ph.p_vaddr - page_start
        page_end = ((ph.p_vaddr + ph.p_memsz + PAGE_SIZE - 1) // PAGE_SIZE) * PAGE_SIZE
        region_size = page_end - page_start

        pf_x = bool(ph.p_flags & 1)
        pf_w = bool(ph.p_flags & 2)
        pf_r = bool(ph.p_flags & 4)
        if pf_w and pf_x:
            raise ValueError(f"PT_LOAD[{ph.idx}] violates W^X")
        perm = Perm(r=pf_r, w=pf_w, x=pf_x)

        if ph.p_filesz == 0:
            reg_bytes = b"\x00" * region_size
            non_anon_len = 0
        else:
            if ph.p_offset < lead or ph.p_offset + ph.p_filesz > len(elf_bytes):
                raise ValueError(f"PT_LOAD[{ph.idx}] file range out of bounds")
            file_start = ph.p_offset - lead
            non_anon_end = ((ph.p_vaddr + ph.p_filesz + PAGE_SIZE - 1) // PAGE_SIZE) * PAGE_SIZE
            non_anon_len = non_anon_end - page_start
            if ph.p_filesz == ph.p_memsz:
                avail = min(region_size, len(elf_bytes) - file_start)
                reg_bytes = elf_bytes[file_start : file_start + avail] + b"\x00" * (
                    region_size - avail
                )
            else:
                file_len = (ph.p_offset + ph.p_filesz) - file_start
                tail_len = page_end - (ph.p_vaddr + ph.p_filesz)
                reg_bytes = elf_bytes[file_start : file_start + file_len] + b"\x00" * tail_len

        assert len(reg_bytes) == region_size
        unsorted_regions.append(
            ElfRegion(
                start=page_start,
                bytes_data=reg_bytes,
                perm=perm,
                nonAnonLen=non_anon_len,
                phdr_idx=ph.idx,
            )
        )

        # Fallback phdrVaddr if no PT_PHDR: PT_LOAD covering e_phoff
        if (
            phdr_vaddr_opt is None
            and ph.p_offset <= e_phoff
            and e_phoff + e_phnum * 56 <= ph.p_offset + ph.p_filesz
        ):
            phdr_vaddr_opt = ph.p_vaddr + (e_phoff - ph.p_offset)

    if not unsorted_regions:
        raise ValueError("ELF has no non-empty PT_LOAD segments")
    if phdr_vaddr_opt is None:
        raise ValueError("Could not determine phdrVaddr from PT_PHDR or PT_LOAD")

    # Python's list.sort is Timsort (stable), matching Lean's mergeSort by `r.start <= q.start`
    regions = sorted(unsorted_regions, key=lambda r: r.start)
    for idx in range(len(regions) - 1):
        if regions[idx].end > regions[idx + 1].start:
            raise ValueError(
                f"Overlapping page-rounded PT_LOAD regions: {regions[idx].start:#x}..{regions[idx].end:#x} "
                f"and {regions[idx + 1].start:#x}..{regions[idx + 1].end:#x}"
            )

    brk_start = max(r.end for r in regions)

    # Parse section headers + `.symtab`
    sections: list[RawElfSection] = []
    raw_syms: list[RawElfSym] = []
    loader_symbols: list[tuple[str, int]] = []

    if require_symtab:
        if e_shoff == 0 or e_shnum == 0 or e_shentsize != 64:
            raise ValueError(
                f"Missing or malformed section header table (shoff={e_shoff:#x}, shnum={e_shnum}, shentsize={e_shentsize})"
            )
        if e_shoff + e_shnum * e_shentsize > len(elf_bytes):
            raise ValueError("Section header table exceeds file bounds")
        if e_shstrndx == 0 or e_shstrndx >= e_shnum:
            raise ValueError(f"Invalid e_shstrndx={e_shstrndx} for shnum={e_shnum}")

    if e_shoff > 0 and e_shnum > 0 and e_shentsize >= 64:
        if e_shoff + e_shnum * e_shentsize > len(elf_bytes):
            raise ValueError("Section header table exceeds file bounds")
        shstr_off = 0
        shstr_size = 0
        if e_shstrndx < e_shnum:
            shdr_str = e_shoff + e_shstrndx * e_shentsize
            _, shstr_type, _, _, shstr_off, shstr_size, _, _, _, _ = struct.unpack_from(
                "<IIQQQQIIQQ", elf_bytes, shdr_str
            )
            if require_symtab and (shstr_type != 3 or shstr_size == 0):
                raise ValueError(f"Missing or empty .shstrtab (type={shstr_type}, size={shstr_size})")
        if shstr_off + shstr_size > len(elf_bytes):
            raise ValueError(".shstrtab exceeds file bounds")
        shstrtab = elf_bytes[shstr_off : shstr_off + shstr_size]

        for si in range(e_shnum):
            soff = e_shoff + si * e_shentsize
            (
                sh_name,
                sh_type,
                sh_flags,
                sh_addr,
                sh_offset,
                sh_size,
                sh_link,
                sh_info,
                sh_addralign,
                sh_entsize,
            ) = struct.unpack_from("<IIQQQQIIQQ", elf_bytes, soff)
            if sh_name >= len(shstrtab) and (require_symtab or len(shstrtab) > 0):
                raise ValueError(f"Section[{si}] sh_name={sh_name} out of .shstrtab bounds ({len(shstrtab)})")
            sections.append(
                RawElfSection(
                    idx=si,
                    name=_read_cstr(shstrtab, sh_name),
                    sh_type=sh_type,
                    sh_flags=sh_flags,
                    sh_addr=sh_addr,
                    sh_offset=sh_offset,
                    sh_size=sh_size,
                    sh_link=sh_link,
                    sh_info=sh_info,
                    sh_addralign=sh_addralign,
                    sh_entsize=sh_entsize,
                )
            )

        symtab_secs = [s for s in sections if s.sh_type == 2]
        if require_symtab and len(symtab_secs) != 1:
            raise ValueError(f"Expected exactly 1 SHT_SYMTAB section, found {len(symtab_secs)}")

        for sec in symtab_secs:
            if sec.sh_entsize != 24 or (sec.sh_size % 24) != 0:
                raise ValueError(f"Malformed SHT_SYMTAB entsize={sec.sh_entsize}, size={sec.sh_size}")
            if sec.sh_offset + sec.sh_size > len(elf_bytes):
                raise ValueError("SHT_SYMTAB exceeds file bounds")
            if sec.sh_link == 0 or sec.sh_link >= len(sections):
                raise ValueError(f"SHT_SYMTAB invalid sh_link={sec.sh_link}")
            str_sec = sections[sec.sh_link]
            if str_sec.sh_type != 3:
                raise ValueError(f"SHT_SYMTAB sh_link={sec.sh_link} is not SHT_STRTAB (type={str_sec.sh_type})")
            if str_sec.sh_offset + str_sec.sh_size > len(elf_bytes):
                raise ValueError("Linked SHT_STRTAB exceeds file bounds")
            strtab = elf_bytes[str_sec.sh_offset : str_sec.sh_offset + str_sec.sh_size]
            nsyms = sec.sh_size // 24
            if require_symtab and (nsyms <= 1 or len(strtab) <= 1):
                raise ValueError(f"Empty SHT_SYMTAB/SHT_STRTAB (nsyms={nsyms}, strtab={len(strtab)})")
            if sec.sh_info > nsyms:
                raise ValueError(f"SHT_SYMTAB sh_info={sec.sh_info} exceeds symbol count={nsyms}")
            for idx in range(nsyms):
                eoff = sec.sh_offset + idx * 24
                st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", elf_bytes, eoff
                )
                if st_name >= len(strtab):
                    raise ValueError(
                        f"Symbol[{idx}] st_name={st_name} exceeds SHT_STRTAB size={len(strtab)}"
                    )
                sname = _read_cstr(strtab, st_name)
                bind = st_info >> 4
                stype = st_info & 0xF
                is_local = idx < sec.sh_info
                raw_syms.append(
                    RawElfSym(
                        idx=idx,
                        name=sname,
                        st_info=st_info,
                        st_other=st_other,
                        st_shndx=st_shndx,
                        st_value=st_value,
                        st_size=st_size,
                        bind=bind,
                        stype=stype,
                        is_local=is_local,
                    )
                )
                # Loader.lean symbols: idx >= sh_info, stype == STT_FUNC (2), st_shndx != 0, st_name != 0
                if not is_local and stype == 2 and st_shndx != 0 and st_name != 0:
                    loader_symbols.append((sname, st_value))

    img = ElfImage(
        entry=e_entry,
        phdrVaddr=phdr_vaddr_opt,
        phent=e_phentsize,
        phnum=e_phnum,
        brkStart=brk_start,
        regions=regions,
        symbols=loader_symbols,
    )
    check_elf_well_formed(img)
    return img, phdrs, sections, raw_syms


def parse_elf_image(elf_bytes: bytes) -> ElfImage:
    img, _, _, _ = parse_raw_elf(elf_bytes)
    return img


def check_elf_well_formed(img: ElfImage) -> None:
    """Mirror `ElfImage.WellFormed` (`Loader.lean:117-148`)."""
    if not img.regions:
        raise ValueError("ElfImage.WellFormed: empty regions")
    entry_exec = False
    for i, reg in enumerate(img.regions):
        if reg.start % PAGE_SIZE != 0 or len(reg.bytes_data) % PAGE_SIZE != 0:
            raise ValueError(f"Region[{i}] not page-aligned")
        if len(reg.bytes_data) == 0:
            raise ValueError(f"Region[{i}] empty")
        if reg.perm.w and reg.perm.x:
            raise ValueError(f"Region[{i}] violates W^X")
        if reg.nonAnonLen > len(reg.bytes_data) or reg.nonAnonLen % PAGE_SIZE != 0:
            raise ValueError(f"Region[{i}] bad nonAnonLen={reg.nonAnonLen}")
        if reg.end > img.brkStart:
            raise ValueError(f"Region[{i}] exceeds brkStart")
        if i + 1 < len(img.regions) and reg.end > img.regions[i + 1].start:
            raise ValueError(f"Region[{i}] overlaps Region[{i+1}]")
        if reg.perm.x and reg.start <= img.entry < reg.end and img.entry % 4 == 0:
            entry_exec = True
    if not entry_exec:
        raise ValueError(f"Entry {img.entry:#x} not inside an executable region on 4B boundary")


# ==============================================================================
# MultiPlacedLib & ExtractedObj Data Structures + Parsers
# ==============================================================================


@dataclass
class RawReloc:
    off: int
    kind: str | None
    symIdx: int
    addend: int = 0


@dataclass
class RawSec:
    name: str
    bytes_slice: bytes
    size: int
    align: int
    isExec: bool
    readOnly: bool
    isNobits: bool
    isTls: bool = False
    relocs: list[RawReloc] = field(default_factory=list)


@dataclass
class RawSym:
    rawName: str
    name: str
    sec: tuple[str, int | None]
    value: int
    size: int
    kind: str
    bind: str


@dataclass
class ExtractedObj:
    name: str
    sections: list[RawSec]
    symbols: list[RawSym]


@dataclass
class RelocEntry:
    off: int
    kind: str
    sym: str
    addend: int = 0


@dataclass
class CodeBlock:
    code: bytes
    align: int
    symbols: list[tuple[str, int]]
    relocs: list[RelocEntry]
    externs: list[str]
    weakRefs: list[str]


@dataclass
class SymDataInfo:
    sym: str
    align: int
    readOnly: bool
    bytes_slice: bytes
    zeroTail: int
    relocs: list[RelocEntry]

    @property
    def total_size(self) -> int:
        return len(self.bytes_slice) + self.zeroTail


@dataclass
class MultiPlacedLib:
    name: str
    blocks: list[CodeBlock]
    data: list[SymDataInfo]
    exports: list[str]
    exportSyms: list[tuple[str, str]]


@dataclass(frozen=True)
class SliceOrigin:
    oi: int
    si: int
    start: int
    len: int


def char_list_lt_key(s: str) -> list[int]:
    """Exact comparison key for Lean's `Obj.Interned.charListLt` (`String.toList` codepoint order)."""
    return [ord(c) for c in s]


def lean_quote(s: str) -> str:
    """Format a Python string as a valid Lean 4 string literal."""
    out = ['"']
    for ch in s:
        code = ord(ch)
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif code < 0x20 or code == 0x7F:
            out.append(f"\\x{code:02x}")
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def parse_lean_str_at(s: str, pos: int) -> tuple[str, int]:
    assert s[pos] == '"', f"expected quote at {pos}: {s[pos:pos+20]!r}"
    i = pos + 1
    out: list[str] = []
    while i < len(s):
        ch = s[i]
        if ch == '"':
            return "".join(out), i + 1
        if ch == "\\":
            nxt = s[i + 1]
            if nxt == "n":
                out.append("\n")
                i += 2
            elif nxt == "r":
                out.append("\r")
                i += 2
            elif nxt == "t":
                out.append("\t")
                i += 2
            elif nxt == "\\":
                out.append("\\")
                i += 2
            elif nxt == '"':
                out.append('"')
                i += 2
            elif nxt == "'":
                out.append("'")
                i += 2
            elif nxt == "x":
                out.append(chr(int(s[i + 2 : i + 4], 16)))
                i += 4
            elif nxt == "u":
                if s[i + 2] == "{":
                    end = s.index("}", i + 3)
                    out.append(chr(int(s[i + 3 : end], 16)))
                    i = end + 1
                else:
                    out.append(chr(int(s[i + 2 : i + 6], 16)))
                    i += 6
            else:
                raise ValueError(f"unknown escape \\{nxt}")
        else:
            out.append(ch)
            i += 1
    raise ValueError("unterminated string")


def _parse_raw_reloc_list(rel_str: str) -> list[RawReloc]:
    out: list[RawReloc] = []
    for m in re.finditer(
        r"\{\s*off\s*:=\s*(0x[0-9a-fA-F]+|\d+),\s*kind\s*:=\s*(none|some\s+\.[A-Za-z0-9_]+),\s*symIdx\s*:=\s*(\d+)(?:,\s*addend\s*:=\s*(-?\d+))?\s*\}",
        rel_str,
    ):
        off = int(m.group(1), 0)
        k_raw = m.group(2)
        kind = None if k_raw == "none" else k_raw.split()[1]
        sym_idx = int(m.group(3))
        addend = int(m.group(4)) if m.group(4) is not None else 0
        out.append(RawReloc(off=off, kind=kind, symIdx=sym_idx, addend=addend))
    return out


def _parse_raw_sec(rec: str, blob: bytes) -> RawSec:
    assert rec.startswith("name := ")
    sec_name, pos = parse_lean_str_at(rec, len("name := "))
    rest = rec[pos:].lstrip(", ")
    relocs: list[RawReloc] = []
    if ", relocs := [" in rest:
        rest, rel_part = rest.split(", relocs := [", 1)
        assert rel_part.endswith("]")
        relocs = _parse_raw_reloc_list(rel_part[:-1])
    fields: dict[str, str] = {}
    for part in rest.split(", "):
        k, v = part.split(" := ", 1)
        fields[k.strip()] = v.strip()
    b_expr = fields["bytes"]
    if b_expr == "[]":
        bs = b""
    else:
        _, q_end = parse_lean_str_at(b_expr, b_expr.index('"'))
        off_s, len_s = b_expr[q_end:].strip().split()
        off_i, len_i = int(off_s), int(len_s)
        bs = blob[off_i : off_i + len_i]
    return RawSec(
        name=sec_name,
        bytes_slice=bs,
        size=int(fields["size"]),
        align=int(fields["align"]),
        isExec=(fields["isExec"] == "true"),
        readOnly=(fields["readOnly"] == "true"),
        isNobits=(fields["isNobits"] == "true"),
        isTls=(fields.get("isTls", "false") == "true"),
        relocs=relocs,
    )


def _parse_raw_sym(rec: str) -> RawSym:
    assert rec.startswith("rawName := ")
    raw_name, pos = parse_lean_str_at(rec, len("rawName := "))
    assert rec[pos:].startswith(", name := ")
    sym_name, pos2 = parse_lean_str_at(rec, pos + len(", name := "))
    tail = rec[pos2:].lstrip(", ")
    fields: dict[str, str] = {}
    for part in tail.split(", "):
        k, v = part.split(" := ", 1)
        fields[k.strip()] = v.strip()
    sec_s = fields["sec"]
    if sec_s == ".undef":
        sec: tuple[str, int | None] = ("undef", None)
    elif sec_s == ".other":
        sec = ("other", None)
    elif sec_s.startswith(".sec "):
        sec = ("sec", int(sec_s.split()[1]))
    else:
        raise ValueError(f"bad sec: {sec_s}")
    return RawSym(
        rawName=raw_name,
        name=sym_name,
        sec=sec,
        value=int(fields["value"], 0),
        size=int(fields["size"]),
        kind=fields["kind"],
        bind=fields["bind"],
    )


def parse_extracted_objs(lean_path: pathlib.Path, bin_path: pathlib.Path) -> list[ExtractedObj]:
    src = lean_path.read_text(encoding="utf-8")
    blob = bin_path.read_bytes()
    lines = src.splitlines()
    objs: list[ExtractedObj] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("def ") and ": Obj.ExtractedObj where" in line:
            i += 1
            assert lines[i].startswith("  name := ")
            obj_name, _ = parse_lean_str_at(lines[i], len("  name := "))
            i += 1
            sections: list[RawSec] = []
            if lines[i].strip() == "sections := []":
                i += 1
            else:
                assert lines[i].strip() == "sections := ["
                i += 1
                while True:
                    sline = lines[i].strip()
                    if sline.endswith("}]"):
                        end_list = True
                        rec = sline[1:-2].strip()
                    elif sline.endswith("},"):
                        end_list = False
                        rec = sline[1:-2].strip()
                    else:
                        raise ValueError(f"unexpected section line: {sline}")
                    sections.append(_parse_raw_sec(rec, blob))
                    i += 1
                    if end_list:
                        break
            symbols: list[RawSym] = []
            if lines[i].strip() == "symbols := []":
                i += 1
            else:
                assert lines[i].strip() == "symbols := ["
                i += 1
                while True:
                    sline = lines[i].strip()
                    if sline.endswith("}]"):
                        end_list = True
                        rec = sline[1:-2].strip()
                    elif sline.endswith("},"):
                        end_list = False
                        rec = sline[1:-2].strip()
                    else:
                        raise ValueError(f"unexpected symbol line: {sline}")
                    symbols.append(_parse_raw_sym(rec))
                    i += 1
                    if end_list:
                        break
            objs.append(ExtractedObj(name=obj_name, sections=sections, symbols=symbols))
        else:
            i += 1
    return objs


def _parse_placed_reloc_line(s: str) -> RelocEntry:
    s = s.strip()
    if s.endswith(","):
        s = s[:-1].strip()
    if s.endswith("]"):
        s = s[:-1].strip()
    if s.endswith("}"):
        s = s[1:-1].strip()
    m = re.match(r"off\s*:=\s*(\d+),\s*kind\s*:=\s*(\.[A-Za-z0-9_]+),\s*sym\s*:=\s*", s)
    assert m, f"bad reloc line: {s!r}"
    off = int(m.group(1))
    kind = m.group(2)
    sym, pos = parse_lean_str_at(s, m.end())
    tail = s[pos:].strip()
    addend = 0
    if tail.startswith(", addend := "):
        addend = int(tail[len(", addend := ") :].strip())
    return RelocEntry(off=off, kind=kind, sym=sym, addend=addend)


def parse_multi_placed_lib(lean_path: pathlib.Path, bin_path: pathlib.Path) -> MultiPlacedLib:
    src = lean_path.read_text(encoding="utf-8")
    blob = bin_path.read_bytes()
    lines = src.splitlines()

    byte_defs: dict[str, bytes] = {}
    for line in lines:
        m = re.match(
            r"^def\s+([A-Za-z0-9_]+)\s*:\s*List\s*\(BitVec\s+8\)\s*:=\s*include_bytes%\s*",
            line,
        )
        if m:
            dname = m.group(1)
            _, q_end = parse_lean_str_at(line, line.index('"', m.end()))
            off_s, len_s = line[q_end:].strip().split()
            off_i, len_i = int(off_s), int(len_s)
            byte_defs[dname] = blob[off_i : off_i + len_i]

    def parse_str_list_block(start_idx: int, field_name: str) -> tuple[list[str], int]:
        l0 = lines[start_idx].strip()
        if l0.startswith(f"{field_name} := []"):
            return [], start_idx + 1
        assert l0 == f"{field_name} := [", f"unexpected {l0!r}"
        idx = start_idx + 1
        items: list[str] = []
        while True:
            cur = lines[idx].strip()
            val, pos = parse_lean_str_at(cur, 0)
            items.append(val)
            rem = cur[pos:].strip()
            idx += 1
            if rem.startswith("]"):
                return items, idx

    blocks: list[CodeBlock] = []
    data: list[SymDataInfo] = []
    exports: list[str] = []
    export_syms: list[tuple[str, str]] = []
    lib_name = ""

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("def ") and ": List Obj.CodeBlock := [" in line:
            i += 1
            while i < len(lines) and lines[i].strip() != "]":
                assert lines[i].strip().startswith("{ code := "), lines[i]
                code_name = lines[i].strip().split(":=")[1].strip()
                i += 1
                align = int(lines[i].strip().split(":=")[1].strip())
                i += 1
                syms: list[tuple[str, int]] = []
                if lines[i].strip() == "symbols := []":
                    i += 1
                else:
                    assert lines[i].strip() == "symbols := ["
                    i += 1
                    while True:
                        cur = lines[i].strip()
                        assert cur.startswith("(")
                        sname, pos = parse_lean_str_at(cur, 1)
                        rest = cur[pos:].lstrip(", ")
                        off_tok = rest.split(")")[0].strip()
                        syms.append((sname, int(off_tok, 0)))
                        after = rest.split(")", 1)[1].strip()
                        i += 1
                        if after.startswith("]"):
                            break
                rels: list[RelocEntry] = []
                if lines[i].strip() == "relocs := []":
                    i += 1
                else:
                    assert lines[i].strip() == "relocs := ["
                    i += 1
                    while True:
                        cur = lines[i].strip()
                        end_rel = cur.endswith("]")
                        rels.append(_parse_placed_reloc_line(cur[:-1] if end_rel else cur))
                        i += 1
                        if end_rel:
                            break
                ext_line = lines[i].strip()
                externs: list[str] = []
                weak_refs: list[str] = []
                block_done = False
                if ext_line.startswith("externs := []"):
                    if ext_line.endswith("}") or ext_line.endswith("},"):
                        block_done = True
                    i += 1
                else:
                    assert ext_line == "externs := ["
                    i += 1
                    while True:
                        cur = lines[i].strip()
                        val, pos = parse_lean_str_at(cur, 0)
                        externs.append(val)
                        rem = cur[pos:].strip()
                        i += 1
                        if rem.startswith("]"):
                            if "}" in rem:
                                block_done = True
                            break
                if not block_done:
                    w_line = lines[i].strip()
                    assert w_line == "weakRefs := [", f"unexpected {w_line!r}"
                    i += 1
                    while True:
                        cur = lines[i].strip()
                        val, pos = parse_lean_str_at(cur, 0)
                        weak_refs.append(val)
                        rem = cur[pos:].strip()
                        i += 1
                        if rem.startswith("]"):
                            break
                blocks.append(
                    CodeBlock(
                        code=byte_defs[code_name],
                        align=align,
                        symbols=syms,
                        relocs=rels,
                        externs=externs,
                        weakRefs=weak_refs,
                    )
                )
            i += 1
        elif line.startswith("def ") and ": List Obj.SymDataInfo := [" in line:
            i += 1
            while i < len(lines) and lines[i].strip() != "]":
                assert lines[i].strip().startswith("{ sym := "), lines[i]
                sym, _ = parse_lean_str_at(lines[i].strip(), len("{ sym := "))
                i += 1
                align = int(lines[i].strip().split(":=")[1].strip())
                i += 1
                ro = lines[i].strip().split(":=")[1].strip() == "true"
                i += 1
                bname = lines[i].strip().split(":=")[1].strip()
                i += 1
                zt = int(lines[i].strip().split(":=")[1].strip())
                i += 1
                rline = lines[i].strip()
                rels = []
                if rline.startswith("relocs := []"):
                    i += 1
                else:
                    assert rline == "relocs := ["
                    i += 1
                    while True:
                        cur = lines[i].strip()
                        is_last = "] }" in cur
                        clean = cur.split("] }")[0] if is_last else cur
                        rels.append(_parse_placed_reloc_line(clean))
                        i += 1
                        if is_last:
                            break
                data.append(
                    SymDataInfo(
                        sym=sym,
                        align=align,
                        readOnly=ro,
                        bytes_slice=byte_defs[bname],
                        zeroTail=zt,
                        relocs=rels,
                    )
                )
            i += 1
        elif line.startswith("def ") and ": Obj.MultiPlacedLib where" in line:
            i += 1
            lib_name, _ = parse_lean_str_at(lines[i].strip(), len("name := "))
            i += 3
            exports, i = parse_str_list_block(i, "exports")
            if i < len(lines) and lines[i].strip().startswith("exportSyms :="):
                if lines[i].strip() == "exportSyms := []":
                    i += 1
                else:
                    assert lines[i].strip() == "exportSyms := ["
                    i += 1
                    while True:
                        cur = lines[i].strip()
                        assert cur.startswith("(")
                        e1, p1 = parse_lean_str_at(cur, 1)
                        p2_start = cur.index('"', p1 + 1)
                        e2, p2 = parse_lean_str_at(cur, p2_start)
                        export_syms.append((e1, e2))
                        rem = cur[p2:].strip()
                        i += 1
                        if rem.endswith("]"):
                            break
        else:
            i += 1
    return MultiPlacedLib(
        name=lib_name, blocks=blocks, data=data, exports=exports, exportSyms=export_syms
    )


# ==============================================================================
# InternedMultiLib (`ProofLib/Placed/Interned.lean`)
# ==============================================================================


@dataclass(frozen=True)
class RelocId:
    off: int
    kind: str
    sym: int
    addend: int = 0


@dataclass
class BlockId:
    code: bytes
    align: int
    symbols: list[tuple[int, int]]
    relocs: list[RelocId]
    externs: list[int]
    weakRefs: list[int]


@dataclass
class DataId:
    sym: int
    align: int
    readOnly: bool
    bytes_slice: bytes
    zeroTail: int
    relocs: list[RelocId]


@dataclass
class InternedMultiLib:
    names: list[str]
    sym_to_id: dict[str, int]
    blocks: list[BlockId]
    data: list[DataId]
    exports: list[int]
    exportSyms: list[tuple[int, int]]
    sharedExterns: list[int] | None
    # Fast lookup structures matching `Interned.lean` / `ConeCert.lean`
    tSym: list[tuple[int, int] | None]  # symId -> first (bi, off) in block symbols


def intern_multi_placed_lib(lib: MultiPlacedLib) -> InternedMultiLib:
    """Bit-exact Python mirror of `internMultiPlacedLib` (`ProofLib/Placed/Interned.lean`)."""
    all_strs: set[str] = set()
    for b in lib.blocks:
        for s, _ in b.symbols:
            all_strs.add(s)
        for r in b.relocs:
            all_strs.add(r.sym)
        for e in b.externs:
            all_strs.add(e)
        for w in b.weakRefs:
            all_strs.add(w)
    for d in lib.data:
        all_strs.add(d.sym)
        for r in d.relocs:
            all_strs.add(r.sym)
    for e in lib.exports:
        all_strs.add(e)
    for e1, e2 in lib.exportSyms:
        all_strs.add(e1)
        all_strs.add(e2)

    names = sorted(all_strs, key=char_list_lt_key)
    sym_to_id = {s: idx for idx, s in enumerate(names)}

    iblocks: list[BlockId] = []
    for b in lib.blocks:
        iblocks.append(
            BlockId(
                code=b.code,
                align=b.align,
                symbols=[(sym_to_id[s], off) for s, off in b.symbols],
                relocs=[
                    RelocId(off=r.off, kind=r.kind, sym=sym_to_id[r.sym], addend=r.addend)
                    for r in b.relocs
                ],
                externs=[sym_to_id[e] for e in b.externs],
                weakRefs=[sym_to_id[w] for w in b.weakRefs],
            )
        )

    idata: list[DataId] = []
    for d in lib.data:
        idata.append(
            DataId(
                sym=sym_to_id[d.sym],
                align=d.align,
                readOnly=d.readOnly,
                bytes_slice=d.bytes_slice,
                zeroTail=d.zeroTail,
                relocs=[
                    RelocId(off=r.off, kind=r.kind, sym=sym_to_id[r.sym], addend=r.addend)
                    for r in d.relocs
                ],
            )
        )

    shared_ext: list[int] | None = None
    if iblocks:
        first_ext = iblocks[0].externs
        if all(b.externs == first_ext for b in iblocks):
            shared_ext = list(first_ext)

    t_sym: list[tuple[int, int] | None] = [None] * len(names)
    for bi, b in enumerate(iblocks):
        for sid, off in b.symbols:
            if t_sym[sid] is None:
                t_sym[sid] = (bi, off)

    return InternedMultiLib(
        names=names,
        sym_to_id=sym_to_id,
        blocks=iblocks,
        data=idata,
        exports=[sym_to_id[e] for e in lib.exports],
        exportSyms=[(sym_to_id[e1], sym_to_id[e2]) for e1, e2 in lib.exportSyms],
        sharedExterns=shared_ext,
        tSym=t_sym,
    )
