# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Fail-closed Option-α, S1/S2 (including GK rows 373 & 374 / A-LINK v0.3.2), and D1 checks.

Implements:
  - B1/α: Exact 3-symbol `displaced_weak` set (`__aarch64_cas8_acq_rel`,
    `__aarch64_ldadd8_rel`, `__aarch64_ldadd8_relax`), input `.symtab` binding verification
    (`STB_GLOBAL` in stub `.o` displacing `STB_WEAK` in runtime archive), final ELF `.symtab`
    RX `udf #0` (`0x00000000`) verification, and `displaced_weak_referrers ⊆ cliLinkObjs`
    computed from `ld.lld -Map` + input `.o`/`.a` `SHT_RELA` relocations.
  - B2/S1 & S2 (GK rows 373 & 374, A-LINK v0.3.2 rule (vii)):
    1. Input-object `.symtab` binding check (`input_binding == "STB_GLOBAL"`, never read from
       shipped ELF `.symtab` where stock links may mark symbols `LOCAL`/`HIDDEN`);
    2. Explicit musl `libc.a(strlen.lo)` extraction & unmasked 88-byte (`0x58`) equality check
       against `ProofLib.StdStartup.muslStrlenWords` (0 relocations);
    3. Full-body unmasked byte equality of `memcpy` and `memset` against pinned `rustc 1.98.1`
       `self-contained/libc.a` members (`memcpy.lo`, `memset.lo`), asserting 0 `.text*`
       relocations on both the pinned `libc.a` members and the linked defining sections;
    4. Relocation-field-masked section byte equality for `memmove`, `memcmp`, and `bcmp`,
       recording `input_binding`, `body_sha256`, and `byte_equal: true` on every `s2_real_body_lock` row.
  - D1: Fail-closed verification that every non-placed `STT_OBJECT` referenced by a surviving
    `cliLinkObjs` relocation equals `.GeneratedLean` `LibsignalSessionObj.lean` `externData`
    minus GC-dead entries (`{MAX_LOG_LEVEL_FILTER, ED25519_BASEPOINT_TABLE}` kept as 8 B zero
    stubs, `{WHITESPACE_MAP, GETRANDOM_FN}` GC-dead), with pinned definer & SHA-256.
"""

from __future__ import annotations

import hashlib
import pathlib
import re
import struct
from typing import Any, Mapping, Sequence

from . import elf_loader

EXPECTED_DISPLACED_WEAK: tuple[str, ...] = (
    "__aarch64_cas8_acq_rel",
    "__aarch64_ldadd8_rel",
    "__aarch64_ldadd8_relax",
)

S2_REQUIRED_NAMES: tuple[str, ...] = (
    "bcmp",
    "memcmp",
    "memcpy",
    "memmove",
    "memset",
    "strlen",
)

# 8-byte external data objects in `LibsignalSessionObj.lean` `externData`
EIGHT_BYTE_EXTERN_DATA_SYMS: frozenset[str] = frozenset(
    {
        "_RNvCs4Dv7yoBiUx4_3log20MAX_LOG_LEVEL_FILTER",
        "_RNvNtNtCs40xgxkZUUew_9getrandom8backends27linux_android_with_fallback12GETRANDOM_FN",
        "_RNvNtNtNtNtCs2wR8L9wiBdT_16curve25519_dalek7backend6serial3u649constants23ED25519_BASEPOINT_TABLE",
    }
)

# Pinned `rustc 1.98.1` `aarch64-unknown-linux-musl/lib/self-contained/libc.a` + member SHA-256s
PINNED_RUSTC_SELF_CONTAINED_LIBC_SHA256: str = (
    "b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f"
)
PINNED_STRLEN_LO_SHA256: str = (
    "485bad76aa759b278a152412850885ad84fab30893998d18337c2d1d1d56ec81"
)
PINNED_MEMCPY_LO_SHA256: str = (
    "1264ddb7eca435a24ef713ef3c201a0118429e91c66b0b0d187ca786534ba7b5"
)
PINNED_MEMSET_LO_SHA256: str = (
    "51971558cc2d0677a192f9a3df86d2ee802b91d6d10ade153ce3a371ad845b95"
)
PINNED_MUSL_MEMBER_SHAS: dict[str, tuple[str, str]] = {
    "strlen": ("strlen.lo", PINNED_STRLEN_LO_SHA256),
    "memcpy": ("memcpy.lo", PINNED_MEMCPY_LO_SHA256),
    "memset": ("memset.lo", PINNED_MEMSET_LO_SHA256),
}

# Canonical 22-instruction (88-byte) musl `strlen` machine code from
# `arm64-semantics/ProofLib/StdStartup/Strlen.lean` (`muslStrlenWords`).
MUSL_STRLEN_WORDS: tuple[int, ...] = (
    0xAA0003E1,
    0xF240083F,
    0x540000A0,
    0x39400022,
    0x34000202,
    0x91000421,
    0x17FFFFFB,
    0xB207DBE4,
    0xF29FDFE4,
    0xF9400022,
    0x8B040043,
    0x8A220062,
    0xF201C05F,
    0x54000061,
    0x91002021,
    0x17FFFFFA,
    0x39400022,
    0x34000062,
    0x91000421,
    0x17FFFFFD,
    0xCB000020,
    0xD65F03C0,
)
MUSL_STRLEN_BYTES: bytes = b"".join(struct.pack("<I", w) for w in MUSL_STRLEN_WORDS)
assert len(MUSL_STRLEN_BYTES) == 88

# Known AArch64 ELF64 relocation types permitted in C-compiled class-N objects (`memmove`, `bcmp`).
# `strlen`, `memcpy`, and `memset` permit 0 relocations (GK row 374).
AARCH64_INSN_RELOC_TYPES: frozenset[int] = frozenset(
    {
        275,  # R_AARCH64_ADR_PREL_PG_HI21
        277,  # R_AARCH64_ADD_ABS_LO12_NC
        278,  # R_AARCH64_LDST8_ABS_LO12_NC
        282,  # R_AARCH64_JUMP26
        283,  # R_AARCH64_CALL26
        284,  # R_AARCH64_LDST16_ABS_LO12_NC
        285,  # R_AARCH64_LDST32_ABS_LO12_NC
        286,  # R_AARCH64_LDST64_ABS_LO12_NC
        299,  # R_AARCH64_LDST128_ABS_LO12_NC
        311,  # R_AARCH64_ADR_GOT_PAGE
        312,  # R_AARCH64_LD64_GOT_LO12_NC
    }
)
R_AARCH64_ABS64: int = 257

ARCHIVE_SPECIAL_NAMES: frozenset[str] = frozenset(
    {"/", "//", "__.SYMDEF", "__.SYMDEF SORTED", "/SYM64/"}
)

HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
MAP_INPUT_SEC_RE = re.compile(
    r"^\s*([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+(\d+)\s+(\S+):\((\S+)\)\s*$"
)
EXTERN_DATA_BLOCK_RE = re.compile(r"externData\s*:=\s*\[(.*?)\]", re.S)
EXTERN_DATA_ITEM_RE = re.compile(r'\(\s*"([^"]+)"\s*,\s*(0x[0-9a-fA-F]+|\d+)\s*,\s*(\d+)\s*\)')


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _bind_label(bind_val: int) -> str:
    if bind_val == 1:
        return "STB_GLOBAL"
    if bind_val == 2:
        return "STB_WEAK"
    if bind_val == 0:
        return "STB_LOCAL"
    return f"STB_{bind_val}"


def _c_str(table: bytes, off: int) -> str:
    if off < 0 or off >= len(table):
        return ""
    end = table.find(b"\x00", off)
    if end < 0:
        end = len(table)
    return table[off:end].decode("utf-8", errors="replace")


def iter_named_ar_elf_members(ar_bytes: bytes) -> list[tuple[str, bytes]]:
    """Parse a Unix `ar` archive into `(member_name, member_bytes)` pairs, supporting GNU `//`
    extended string tables and BSD `#1/<len>` names, and rejecting non-ELF payload members."""
    if not ar_bytes.startswith(b"!<arch>\n"):
        raise ValueError("not a Unix ar archive")
    pos = 8
    n = len(ar_bytes)
    gnu_strtab = b""
    raw_records: list[tuple[str, bytes]] = []
    while pos < n:
        if pos & 1:
            pos += 1
        if pos >= n:
            break
        if pos + 60 > n:
            raise ValueError("truncated Unix ar member header")
        hdr = ar_bytes[pos : pos + 60]
        if hdr[58:60] != b"`\n":
            raise ValueError(f"invalid Unix ar member magic {hdr[58:60]!r}")
        pos += 60
        raw_name = hdr[:16].decode("ascii", errors="replace").strip()
        size_str = hdr[48:58].decode("ascii", errors="replace").strip()
        if not size_str.isdigit():
            raise ValueError(f"non-numeric Unix ar member size {size_str!r} for {raw_name!r}")
        size = int(size_str)
        if pos + size > n:
            raise ValueError(f"truncated Unix ar member body for {raw_name!r}")
        body = ar_bytes[pos : pos + size]
        pos += size
        if raw_name == "//":
            gnu_strtab = body
            continue
        if raw_name in ARCHIVE_SPECIAL_NAMES:
            continue
        if raw_name.startswith("#1/") and raw_name[3:].isdigit():
            nlen = int(raw_name[3:])
            if nlen > len(body):
                raise ValueError(f"BSD ar extended name length {nlen} exceeds member size")
            mname = body[:nlen].rstrip(b"\x00").decode("utf-8", errors="replace")
            body = body[nlen:]
            raw_records.append((mname, body))
        else:
            raw_records.append((raw_name, body))

    members: list[tuple[str, bytes]] = []
    for raw_name, body in raw_records:
        if raw_name.startswith("/") and raw_name[1:].isdigit():
            off = int(raw_name[1:])
            if off >= len(gnu_strtab):
                raise ValueError(f"GNU ar extended name offset {off} out of range")
            end = gnu_strtab.find(b"\n", off)
            raw_slice = gnu_strtab[off:end] if end >= 0 else gnu_strtab[off:]
            mname = raw_slice.rstrip(b"/\r").decode("utf-8", errors="replace")
        else:
            mname = raw_name.rstrip("/")
        if not body.startswith(b"\x7fELF"):
            raise ValueError(
                f"non-ELF archive member {mname!r} (head={body[:8]!r}); bitcode/non-ELF forbidden"
            )
        members.append((mname, body))
    if not members:
        raise ValueError("Unix ar archive contains 0 ELF object members")
    return members


def extract_ar_member_exact(ar_bytes: bytes, member_name: str) -> bytes:
    """Extract a single named ELF member from `ar_bytes`, failing closed on 0 or >1 matches."""
    hits = [body for name, body in iter_named_ar_elf_members(ar_bytes) if name == member_name]
    if len(hits) != 1:
        raise RuntimeError(
            f"expected exactly 1 archive member named {member_name!r}, found {len(hits)}"
        )
    return hits[0]


def parse_reloc_elf_object(obj: bytes) -> dict[str, Any]:
    """Parse an ELF64 `ET_REL` object: section names/bytes, symbol table, and per-section `SHT_RELA`."""
    if len(obj) < 64 or obj[:4] != b"\x7fELF" or obj[4] != 2 or obj[5] != 1:
        raise ValueError("expected 64-bit little-endian ELF object")
    (e_shoff,) = struct.unpack_from("<Q", obj, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", obj, 58)
    if e_shoff == 0 or e_shnum == 0 or e_shentsize < 64 or e_shstrndx >= e_shnum:
        raise ValueError("malformed ELF64 section header table in relocatable object")
    if e_shoff + e_shnum * e_shentsize > len(obj):
        raise ValueError("truncated ELF64 section header table in relocatable object")

    shdrs = [
        struct.unpack_from("<IIQQQQIIQQ", obj, e_shoff + i * e_shentsize)
        for i in range(e_shnum)
    ]
    shstr_sh = shdrs[e_shstrndx]
    if shstr_sh[4] + shstr_sh[5] > len(obj):
        raise ValueError("truncated .shstrtab in relocatable object")
    shstr = obj[shstr_sh[4] : shstr_sh[4] + shstr_sh[5]]

    sec_names: list[str] = [_c_str(shstr, sh[0]) for sh in shdrs]
    sec_bytes: list[bytes] = []
    for sh in shdrs:
        if sh[1] == 8:  # SHT_NOBITS
            sec_bytes.append(b"")
        else:
            if sh[4] + sh[5] > len(obj):
                raise ValueError("truncated section body in relocatable object")
            sec_bytes.append(obj[sh[4] : sh[4] + sh[5]])

    symtab_idxs = [i for i, sh in enumerate(shdrs) if sh[1] == 2]
    if len(symtab_idxs) != 1:
        raise ValueError(
            f"relocatable ELF object must contain 1 SHT_SYMTAB, found {len(symtab_idxs)}"
        )
    sym_sh = shdrs[symtab_idxs[0]]
    entsz = sym_sh[9]
    if entsz < 24 or sym_sh[5] % entsz != 0 or sym_sh[4] + sym_sh[5] > len(obj):
        raise ValueError("malformed SHT_SYMTAB in relocatable object")
    if sym_sh[6] == 0 or sym_sh[6] >= e_shnum:
        raise ValueError("invalid SHT_SYMTAB sh_link in relocatable object")
    str_sh = shdrs[sym_sh[6]]
    if str_sh[4] + str_sh[5] > len(obj):
        raise ValueError("truncated SHT_STRTAB in relocatable object")
    strtab = obj[str_sh[4] : str_sh[4] + str_sh[5]]

    syms: list[dict[str, Any]] = []
    for idx in range(sym_sh[5] // entsz):
        st_name, st_info, _st_other, st_shndx, st_value, st_size = struct.unpack_from(
            "<IBBHQQ", obj, sym_sh[4] + idx * entsz
        )
        syms.append(
            {
                "idx": idx,
                "name": _c_str(strtab, st_name),
                "bind": st_info >> 4,
                "type": st_info & 0xF,
                "shndx": st_shndx,
                "value": st_value,
                "size": st_size,
            }
        )

    relocs_by_sec_name: dict[str, set[str]] = {}
    reloc_records_by_sec_name: dict[str, list[dict[str, Any]]] = {}
    for sh in shdrs:
        if sh[1] != 4:  # SHT_RELA
            continue
        r_entsz = sh[9]
        if r_entsz < 24 or sh[5] % r_entsz != 0 or sh[4] + sh[5] > len(obj):
            raise ValueError("malformed SHT_RELA in relocatable object")
        target_shndx = sh[7]
        if target_shndx >= len(sec_names):
            continue
        from_sec = sec_names[target_shndx]
        if not from_sec or from_sec.startswith(".debug"):
            continue
        targets = relocs_by_sec_name.setdefault(from_sec, set())
        rec_list = reloc_records_by_sec_name.setdefault(from_sec, [])
        for i in range(sh[5] // r_entsz):
            r_off, r_info, r_add = struct.unpack_from("<QQq", obj, sh[4] + i * r_entsz)
            sym_idx = r_info >> 32
            rtype = r_info & 0xFFFFFFFF
            tname = syms[sym_idx]["name"] if 0 < sym_idx < len(syms) else ""
            if tname:
                targets.add(tname)
            rec_list.append(
                {
                    "offset": int(r_off),
                    "rtype": int(rtype),
                    "target": str(tname),
                    "addend": int(r_add),
                }
            )

    return {
        "sec_names": sec_names,
        "sec_bytes": sec_bytes,
        "syms": syms,
        "relocs_by_sec_name": {k: sorted(v) for k, v in relocs_by_sec_name.items()},
        "reloc_records_by_sec_name": {
            k: sorted(v, key=lambda r: (int(r["offset"]), int(r["rtype"])))
            for k, v in reloc_records_by_sec_name.items()
        },
    }


def verify_strlen_lo_bytes(obj_bytes: bytes) -> None:
    """Verify `strlen.lo` defines `STB_GLOBAL` `STT_FUNC` `strlen` (`88 B`) in `.text.strlen`
    with 0 relocations whose 22 instruction words match `ProofLib.StdStartup.muslStrlenWords`."""
    parsed = parse_reloc_elf_object(obj_bytes)
    strlen_defs = [
        s
        for s in parsed["syms"]
        if s["name"] == "strlen" and s["shndx"] != 0 and s["bind"] in (1, 2) and s["type"] == 2
    ]
    if len(strlen_defs) != 1 or int(strlen_defs[0]["bind"]) != 1:
        raise RuntimeError(
            f"strlen.lo expected 1 STB_GLOBAL STT_FUNC `strlen`, found {strlen_defs}"
        )
    srec = strlen_defs[0]
    shndx = int(srec["shndx"])
    sec_name = parsed["sec_names"][shndx]
    sec_bytes = parsed["sec_bytes"][shndx]
    sec_relocs = parsed["reloc_records_by_sec_name"].get(sec_name, [])
    if sec_name != ".text.strlen":
        raise RuntimeError(
            f"strlen.lo `strlen` expected in `.text.strlen`, got section {sec_name!r}"
        )
    if sec_relocs:
        raise RuntimeError(
            f"strlen.lo `.text.strlen` must have 0 relocations, found {sec_relocs}"
        )
    if int(srec["size"]) != 88 or int(srec["value"]) != 0 or len(sec_bytes) != 88:
        raise RuntimeError(
            f"strlen.lo `strlen` expected value=0 size=88 sec_len=88, got "
            f"value={srec['value']} size={srec['size']} sec_len={len(sec_bytes)}"
        )
    if sec_bytes != MUSL_STRLEN_BYTES:
        raise RuntimeError(
            "strlen.lo `.text.strlen` bytes disagree with ProofLib.StdStartup.muslStrlenWords"
        )


def extract_and_verify_pinned_musl_members(
    ar_bytes: bytes,
    *,
    expected_archive_sha256: str = PINNED_RUSTC_SELF_CONTAINED_LIBC_SHA256,
    expected_member_shas: Mapping[str, tuple[str, str]] | None = None,
) -> tuple[dict[str, dict[str, Any]], dict[str, bytes]]:
    """GK rows 373 & 374 (`A-LINK v0.3.2` rule (vii)):
    Verify SHA-pinned `rustc 1.98.1` `self-contained/libc.a` and extract `strlen.lo`, `memcpy.lo`,
    and `memset.lo`. Enforces `STB_GLOBAL` binding, **0 `.text*` relocations** (never masked),
    and `strlen.lo == muslStrlenWords`. Returns `(json_ref_map, raw_member_obj_bytes_by_sym)`."""
    got_ar_sha = sha256_bytes(ar_bytes)
    if not HEX64_RE.match(expected_archive_sha256) or got_ar_sha != expected_archive_sha256:
        raise RuntimeError(
            f"rustc self-contained/libc.a sha256 {got_ar_sha!r} != pinned {expected_archive_sha256!r}"
        )
    target_members = (
        dict(expected_member_shas)
        if expected_member_shas is not None
        else dict(PINNED_MUSL_MEMBER_SHAS)
    )
    ref_map: dict[str, dict[str, Any]] = {}
    raw_objs: dict[str, bytes] = {}

    for sym_name, (mem_name, exp_mem_sha) in sorted(target_members.items()):
        mem_bytes = extract_ar_member_exact(ar_bytes, mem_name)
        got_mem_sha = sha256_bytes(mem_bytes)
        if not HEX64_RE.match(exp_mem_sha) or got_mem_sha != exp_mem_sha:
            raise RuntimeError(
                f"pinned libc.a({mem_name}) sha256 {got_mem_sha!r} != expected {exp_mem_sha!r}"
            )
        if sym_name == "strlen":
            verify_strlen_lo_bytes(mem_bytes)

        parsed = parse_reloc_elf_object(mem_bytes)
        defs = [
            s
            for s in parsed["syms"]
            if s["name"] == sym_name and s["shndx"] != 0 and s["bind"] in (1, 2) and s["type"] == 2
        ]
        if len(defs) != 1:
            raise RuntimeError(
                f"pinned libc.a({mem_name}) expected 1 non-local STT_FUNC `{sym_name}`, found {defs}"
            )
        srec = defs[0]
        if int(srec["bind"]) != 1:
            raise RuntimeError(
                f"GK row 373 (1): pinned libc.a({mem_name}) `{sym_name}` has non-STB_GLOBAL binding {_bind_label(int(srec['bind']))}"
            )
        shndx = int(srec["shndx"])
        if shndx >= len(parsed["sec_names"]):
            raise RuntimeError(f"pinned libc.a({mem_name}) `{sym_name}` invalid shndx={shndx}")
        sec_name = parsed["sec_names"][shndx]
        sec_bytes = parsed["sec_bytes"][shndx]
        sec_relocs = parsed["reloc_records_by_sec_name"].get(sec_name, [])
        # GK row 374: `strlen`, `memcpy`, and `memset` are `.S` / reloc-free bodies; ANY relocation fails closed!
        if sec_relocs:
            raise RuntimeError(
                f"GK row 374: pinned libc.a({mem_name}):({sec_name}) must have 0 relocations, found {sec_relocs}"
            )
        sym_val = int(srec["value"])
        sym_sz = int(srec["size"])
        if sym_sz <= 0 or sym_val < 0 or sym_val + sym_sz > len(sec_bytes):
            raise RuntimeError(
                f"pinned libc.a({mem_name}) `{sym_name}` invalid bounds value={sym_val} size={sym_sz} sec_len={len(sec_bytes)}"
            )
        body = sec_bytes[sym_val : sym_val + sym_sz]
        if sym_name == "strlen" and body != MUSL_STRLEN_BYTES:
            raise RuntimeError(
                "pinned libc.a(strlen.lo) body disagrees with ProofLib.StdStartup.muslStrlenWords"
            )
        ref_map[sym_name] = {
            "archive_sha256": expected_archive_sha256,
            "member": mem_name,
            "member_sha256": got_mem_sha,
            "input_binding": "STB_GLOBAL",
            "section": sec_name,
            "size": sym_sz,
            "reloc_count": 0,
            "body_sha256": sha256_bytes(body),
            "body_hex": body.hex(),
        }
        raw_objs[sym_name] = mem_bytes

    return ref_map, raw_objs


class _RustV0Parser:
    """Minimal RFC-2603 Rust `_R` v0 symbol path demangler (sufficient for crate/module/value/type paths)."""

    def __init__(self, s: str) -> None:
        self.s = s
        self.pos = 2  # after `_R`

    def peek(self) -> str:
        return self.s[self.pos] if self.pos < len(self.s) else ""

    def eat(self, ch: str) -> bool:
        if self.peek() == ch:
            self.pos += 1
            return True
        return False

    def parse_base62(self) -> int:
        if self.eat("_"):
            return 0
        end = self.s.find("_", self.pos)
        if end < 0:
            raise ValueError("unterminated base62 number")
        tok = self.s[self.pos : end]
        self.pos = end + 1
        val = 0
        for c in tok:
            if "0" <= c <= "9":
                d = ord(c) - ord("0")
            elif "a" <= c <= "z":
                d = 10 + ord(c) - ord("a")
            elif "A" <= c <= "Z":
                d = 36 + ord(c) - ord("A")
            else:
                raise ValueError(f"invalid base62 digit {c!r}")
            val = val * 62 + d
        return val + 1

    def skip_disambiguator(self) -> None:
        if self.eat("s"):
            self.parse_base62()

    def parse_ident(self) -> str:
        is_puny = self.eat("u")
        start = self.pos
        while self.pos < len(self.s) and self.s[self.pos].isdigit():
            self.pos += 1
        if self.pos == start:
            raise ValueError(f"expected identifier length at {self.pos} in {self.s!r}")
        length = int(self.s[start : self.pos])
        self.eat("_")
        if self.pos + length > len(self.s):
            raise ValueError("truncated identifier")
        ident = self.s[self.pos : self.pos + length]
        self.pos += length
        if is_puny:
            return ident
        return ident

    def parse_path(self) -> str:
        tag = self.peek()
        if tag == "C":
            self.pos += 1
            self.skip_disambiguator()
            return self.parse_ident()
        if tag == "N":
            self.pos += 1
            if self.pos >= len(self.s):
                raise ValueError("truncated N namespace")
            ns = self.s[self.pos]
            self.pos += 1
            parent = self.parse_path()
            self.skip_disambiguator()
            ident = self.parse_ident()
            if ns in ("t", "v") and ident:
                return f"{parent}::{ident}"
            if ident:
                return f"{parent}::{ident}"
            return parent
        if tag == "B":
            self.pos += 1
            backref = self.parse_base62()
            sub = _RustV0Parser("_R" + self.s[2 + backref :])
            return sub.parse_path()
        if tag == "I":
            self.pos += 1
            base = self.parse_path()
            while self.pos < len(self.s) and not self.eat("E"):
                self.pos += 1
            return base
        raise ValueError(f"unsupported Rust v0 path tag {tag!r} in {self.s!r}")


def demangle_rust_v0(sym: str) -> str:
    """Demangle a Rust `_R` v0 module path to `crate::mod::NAME` (returning `sym` unchanged if non-`_R` or impl-qualified)."""
    base_sym = sym.split(".llvm.", 1)[0]
    if not base_sym.startswith("_R"):
        return sym
    try:
        p = _RustV0Parser(base_sym)
        if p.peek().isdigit():
            while p.peek().isdigit():
                p.pos += 1
        return p.parse_path()
    except ValueError:
        return sym


def parse_generated_lean_extern_data(repo_root: pathlib.Path) -> dict[str, int]:
    """Parse `externData := [ ("...", 0x..., <size>), ... ]` from `.GeneratedLean/**/LibsignalSessionObj.lean`."""
    gen_root = repo_root / ".GeneratedLean"
    if not gen_root.is_dir():
        raise RuntimeError(f"missing `.GeneratedLean` directory at {gen_root}")
    cands = sorted(p for p in gen_root.glob("**/LibsignalSessionObj.lean") if p.is_file())
    if len(cands) != 1:
        raise RuntimeError(
            f"expected exactly 1 LibsignalSessionObj.lean under {gen_root}, found {cands}"
        )
    text = cands[0].read_text(encoding="utf-8")
    m_blk = EXTERN_DATA_BLOCK_RE.search(text)
    if m_blk is None:
        raise RuntimeError(f"missing `externData := [...]` block in {cands[0]}")
    out: dict[str, int] = {}
    for m_it in EXTERN_DATA_ITEM_RE.finditer(m_blk.group(1)):
        name = m_it.group(1)
        size = int(m_it.group(3))
        if name in out:
            raise RuntimeError(f"duplicate externData entry {name!r} in {cands[0]}")
        out[name] = size
    if not out:
        raise RuntimeError(f"parsed empty `externData` in {cands[0]}")
    return out


def canonicalize_map_input_token(raw_input: str) -> tuple[str, str | None, str]:
    """Normalize `/path/to/foo.a(bar.o)` -> `('foo.a', 'bar.o', 'foo.a(bar.o)')` and
    `/path/to/baz.o` -> `('baz.o', None, 'baz.o')`."""
    if "(" in raw_input and raw_input.endswith(")"):
        ar_part, mem_part = raw_input[:-1].rsplit("(", 1)
        src_file = pathlib.Path(ar_part).name
        return src_file, mem_part, f"{src_file}({mem_part})"
    src_file = pathlib.Path(raw_input).name
    return src_file, None, src_file


def parse_lld_map(map_text: str) -> list[dict[str, Any]]:
    """Parse `ld.lld -Map` surviving input-section rows, failing closed if empty or malformed."""
    entries: list[dict[str, Any]] = []
    for ln in map_text.splitlines():
        m = MAP_INPUT_SEC_RE.match(ln)
        if m is None:
            continue
        vma = int(m.group(1), 16)
        lma = int(m.group(2), 16)
        size = int(m.group(3), 16)
        align = int(m.group(4))
        raw_inp = m.group(5)
        in_sec = m.group(6)
        src_file, ar_mem, canon_id = canonicalize_map_input_token(raw_inp)
        entries.append(
            {
                "vma": vma,
                "lma": lma,
                "size": size,
                "align": align,
                "source_file": src_file,
                "archive_member": ar_mem,
                "canonical_input": canon_id,
                "input_section": in_sec,
            }
        )
    if not entries:
        raise RuntimeError("ld.lld -Map parser matched 0 input-section rows (fail-closed)")
    if not any(e["input_section"].startswith(".text") for e in entries):
        raise RuntimeError("ld.lld -Map parser found 0 `.text*` input sections (fail-closed)")
    if not any(e["source_file"].startswith("lib0_") for e in entries):
        raise RuntimeError("ld.lld -Map parser found 0 `lib0_*.o` input sections (fail-closed)")
    return entries


def _record_s2_candidates(
    canon_inp: str,
    parsed: Mapping[str, Any],
    s2_candidate_defs: dict[str, dict[str, dict[str, Any]]],
) -> None:
    """Capture input-object `.symtab` binding, raw section slice, and overlapping `SHT_RELA`
    records for any `S2_REQUIRED_NAMES` symbol defined in `canon_inp` (GK row 373 changes 1 & 3)."""
    s2_set = set(S2_REQUIRED_NAMES)
    sec_names: Sequence[str] = parsed["sec_names"]
    sec_bytes: Sequence[bytes] = parsed["sec_bytes"]
    reloc_recs: Mapping[str, Sequence[Mapping[str, Any]]] = parsed["reloc_records_by_sec_name"]

    for s in parsed["syms"]:
        sname = str(s["name"])
        if sname not in s2_set or int(s["shndx"]) == 0 or int(s["bind"]) not in (1, 2):
            continue
        shndx = int(s["shndx"])
        if shndx >= len(sec_names):
            raise RuntimeError(f"{canon_inp}: `{sname}` has out-of-range shndx={shndx}")
        sec_nm = sec_names[shndx]
        raw_sec = sec_bytes[shndx]
        sval = int(s["value"])
        ssz = int(s["size"])
        if ssz <= 0 or sval < 0 or sval + ssz > len(raw_sec):
            raise RuntimeError(
                f"{canon_inp}: `{sname}` invalid section slice value={sval} size={ssz} sec_len={len(raw_sec)}"
            )
        body_slice = raw_sec[sval : sval + ssz]
        overlapping_relocs: list[dict[str, Any]] = []
        for r in reloc_recs.get(sec_nm, ()):
            roff = int(r["offset"])
            if sval <= roff < sval + ssz:
                overlapping_relocs.append(
                    {
                        "offset": roff - sval,
                        "rel_offset": roff - sval,
                        "r_type": int(r["rtype"]),
                        "rtype": int(r["rtype"]),
                        "target_symbol": str(r["target"]),
                        "target": str(r["target"]),
                        "addend": int(r.get("addend", 0)),
                    }
                )
        per_inp = s2_candidate_defs.setdefault(canon_inp, {})
        if sname in per_inp:
            raise RuntimeError(
                f"{canon_inp}: multiple non-local definitions of S2 symbol `{sname}` in input .symtab"
            )
        per_inp[sname] = {
            "input_binding": _bind_label(int(s["bind"])),
            "stype": int(s["type"]),
            "sec_name": sec_nm,
            "value": sval,
            "size": ssz,
            "body_hex": body_slice.hex(),
            "reloc_records": overlapping_relocs,
        }


def scan_link_inputs_for_alpha(
    *,
    cli_link_objs: Sequence[pathlib.Path],
    other_objs: Sequence[pathlib.Path],
    native_objs: Sequence[pathlib.Path],
    stubs_o: pathlib.Path,
    runtime_archives: Sequence[pathlib.Path],
    strlen_source_override: Mapping[str, str] | None = None,
    pinned_musl_ref_bodies: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Scan staged `.o` and `.a` link inputs into a path-independent, JSON-serializable bundle
    for `compute_and_verify_alpha_b3` (used during `--build`, `--verify`, `--verify-pin`, and `--verify-alpha`)."""
    object_shas: dict[str, str] = {}
    object_classes: dict[str, str] = {}
    archive_shas: dict[str, str] = {}
    archive_member_shas: dict[str, str] = {}
    section_relocs: dict[str, dict[str, list[str]]] = {}
    s2_candidate_defs: dict[str, dict[str, dict[str, Any]]] = {}

    cli_link_obj_names: list[str] = []
    cli_defined_syms: set[str] = set()
    cli_undef_object_syms: set[str] = set()
    stub_global_defs: set[str] = set()
    stub_weak_defs: set[str] = set()
    runtime_strong_defs: set[str] = set()
    runtime_weak_defs: set[str] = set()

    def register_obj(path: pathlib.Path, cls: str) -> tuple[str, dict[str, Any]]:
        raw = path.read_bytes()
        name = path.name
        if name in object_shas and object_shas[name] != sha256_bytes(raw):
            raise RuntimeError(f"colliding link input basename {name!r} with distinct sha256")
        object_shas[name] = sha256_bytes(raw)
        object_classes[name] = cls
        parsed = parse_reloc_elf_object(raw)
        section_relocs[name] = parsed["relocs_by_sec_name"]
        _record_s2_candidates(name, parsed, s2_candidate_defs)
        return name, parsed

    for p in cli_link_objs:
        nm, parsed = register_obj(p, "cli_link_obj")
        cli_link_obj_names.append(nm)
        for s in parsed["syms"]:
            sname = s["name"]
            if not sname or s["bind"] not in (1, 2):
                continue
            if s["shndx"] != 0:
                cli_defined_syms.add(sname)
            elif s["type"] in (0, 1):  # undefined STT_NOTYPE / STT_OBJECT in cliLinkObjs
                cli_undef_object_syms.add(sname)

    for p in other_objs:
        cls = "S" if p.name.startswith("lib") and p.name.endswith(".o") else "harness"
        _, parsed = register_obj(p, cls)
        for s in parsed["syms"]:
            if s["shndx"] != 0 and s["name"]:
                if s["bind"] == 1:
                    runtime_strong_defs.add(s["name"])
                elif s["bind"] == 2:
                    runtime_weak_defs.add(s["name"])

    for p in native_objs:
        _, parsed = register_obj(p, "N")
        for s in parsed["syms"]:
            if s["shndx"] != 0 and s["name"]:
                if s["bind"] == 1:
                    runtime_strong_defs.add(s["name"])
                elif s["bind"] == 2:
                    runtime_weak_defs.add(s["name"])

    stub_name, stub_parsed = register_obj(stubs_o, "Z")
    for s in stub_parsed["syms"]:
        if s["shndx"] != 0 and s["name"]:
            if s["bind"] == 1:
                stub_global_defs.add(s["name"])
            elif s["bind"] == 2:
                stub_weak_defs.add(s["name"])

    for ar_path in runtime_archives:
        ar_bytes = ar_path.read_bytes()
        ar_name = ar_path.name
        archive_shas[ar_name] = sha256_bytes(ar_bytes)
        for mem_name, mem_bytes in iter_named_ar_elf_members(ar_bytes):
            canon = f"{ar_name}({mem_name})"
            archive_member_shas[canon] = sha256_bytes(mem_bytes)
            mparsed = parse_reloc_elf_object(mem_bytes)
            section_relocs[canon] = mparsed["relocs_by_sec_name"]
            _record_s2_candidates(canon, mparsed, s2_candidate_defs)
            for s in mparsed["syms"]:
                if s["shndx"] != 0 and s["name"]:
                    if s["bind"] == 1:
                        runtime_strong_defs.add(s["name"])
                    elif s["bind"] == 2:
                        runtime_weak_defs.add(s["name"])

    return {
        "cli_link_obj_names": sorted(cli_link_obj_names),
        "stubs_obj_name": stub_name,
        "object_shas": dict(sorted(object_shas.items())),
        "object_classes": dict(sorted(object_classes.items())),
        "archive_shas": dict(sorted(archive_shas.items())),
        "archive_member_shas": dict(sorted(archive_member_shas.items())),
        "section_relocs": {k: section_relocs[k] for k in sorted(section_relocs.keys())},
        "s2_candidate_defs": {k: s2_candidate_defs[k] for k in sorted(s2_candidate_defs.keys())},
        "cli_defined_syms": sorted(cli_defined_syms),
        "cli_undef_object_syms": sorted(cli_undef_object_syms),
        "stub_global_defs": sorted(stub_global_defs),
        "stub_weak_defs": sorted(stub_weak_defs),
        "runtime_strong_defs": sorted(runtime_strong_defs),
        "runtime_weak_defs": sorted(runtime_weak_defs),
        "strlen_source_override": dict(strlen_source_override) if strlen_source_override else None,
        "pinned_musl_ref_bodies": (
            {k: dict(v) for k, v in sorted(pinned_musl_ref_bodies.items())}
            if pinned_musl_ref_bodies is not None
            else None
        ),
    }


def _find_defining_map_entry(
    map_entries: Sequence[dict[str, Any]], sym_addr: int, sym_size: int
) -> dict[str, Any]:
    """Locate the unique surviving `-Map` input section covering `[sym_addr, sym_addr + max(1, sym_size))`."""
    eff_sz = max(1, sym_size)
    cands = [
        e
        for e in map_entries
        if e["size"] > 0 and e["vma"] <= sym_addr and sym_addr + eff_sz <= e["vma"] + e["size"]
    ]
    if len(cands) != 1:
        raise RuntimeError(
            f"expected 1 surviving -Map input section covering {sym_addr:#x} (+{sym_size}), "
            f"found {len(cands)}: {cands}"
        )
    return cands[0]


def _verify_masked_body_equal(
    sym_name: str,
    elf_body: bytes,
    src_body: bytes,
    reloc_records: Sequence[Mapping[str, Any]],
) -> None:
    """Compare `elf_body` against `src_body` outside relocation patched fields (`4 B` for AArch64
    instruction relocations, `8 B` for `R_AARCH64_ABS64`), failing closed on unknown reloc types."""
    if len(elf_body) != len(src_body):
        raise RuntimeError(
            f"S2 `{sym_name}` ELF body length {len(elf_body)} != input section body length {len(src_body)}"
        )
    masked_offsets: set[int] = set()
    for r in reloc_records:
        roff = int(r["rel_offset"])
        rtype = int(r["rtype"])
        if rtype in AARCH64_INSN_RELOC_TYPES:
            width = 4
        elif rtype == R_AARCH64_ABS64:
            width = 8
        else:
            raise RuntimeError(
                f"S2 `{sym_name}` unsupported relocation type {rtype} at offset {roff:#x} (fail-closed)"
            )
        if roff < 0 or roff + width > len(src_body):
            raise RuntimeError(
                f"S2 `{sym_name}` relocation span [{roff}, {roff + width}) out of body bounds {len(src_body)}"
            )
        masked_offsets.update(range(roff, roff + width))

    mismatches = [
        idx
        for idx in range(len(elf_body))
        if idx not in masked_offsets and elf_body[idx] != src_body[idx]
    ]
    if mismatches:
        first = mismatches[0]
        raise RuntimeError(
            f"S2 `{sym_name}` ELF body differs from defining input section outside relocations "
            f"({len(mismatches)} byte(s), first at +{first:#x}: elf={elf_body[first]:#04x} != src={src_body[first]:#04x})"
        )


def compute_and_verify_alpha_b3(
    *,
    elf_bytes: bytes,
    map_text: str,
    alpha_scan: Mapping[str, Any],
    generated_extern_data: Mapping[str, int],
    expected_lock: Mapping[str, Any] | None = None,
    verify_addresses: bool = True,
) -> dict[str, Any]:
    """Enforce B3 fail-closed checks:
    - Option α `displaced_weak` + `udf #0` + `displaced_weak_referrers ⊆ cliLinkObjs`;
    - GK rows 373 & 374 (`A-LINK v0.3.2` rule (vii)): input-object `.symtab` binding check,
      `S1` unmasked 88 B `strlen == muslStrlenWords` (0 relocs), unmasked full-body `memcpy`/`memset`
      equality against pinned `rustc` `self-contained/libc.a` members (0 relocs), and `S2` `s2_real_body_lock`;
    - `D1` `d1_extern_data_lock` (`externData \\ gc_dead`)."""
    img, _phdrs, _sections, raw_syms = elf_loader.parse_raw_elf(elf_bytes, require_symtab=True)
    map_entries = parse_lld_map(map_text)

    kept_sec_pairs: set[tuple[str, str]] = {
        (str(e["canonical_input"]), str(e["input_section"]))
        for e in map_entries
        if int(e["size"]) > 0
    }

    nonlocal_defs_by_name: dict[str, list[elf_loader.RawElfSym]] = {}
    all_defs_by_name: dict[str, list[elf_loader.RawElfSym]] = {}
    for s in raw_syms[1:]:
        if s.st_shndx != 0 and s.name:
            all_defs_by_name.setdefault(s.name, []).append(s)
            if not s.is_local:
                nonlocal_defs_by_name.setdefault(s.name, []).append(s)

    # ------------------------------------------------------------------
    # 1. B3.1: Exact `displaced_weak` set (lock schema AND actual shadowed weak runtime set)
    # ------------------------------------------------------------------
    expected_dw = list(EXPECTED_DISPLACED_WEAK)
    if expected_lock is not None and "displaced_weak" in expected_lock:
        lock_dw_raw = expected_lock["displaced_weak"]
        if not isinstance(lock_dw_raw, list):
            raise RuntimeError("lock `displaced_weak` must be a list of symbol names")
        lock_dw = [str(x) for x in lock_dw_raw]
        if len(lock_dw) != len(set(lock_dw)) or sorted(lock_dw) != expected_dw:
            raise RuntimeError(
                f"displaced_weak lock mismatch: got {lock_dw!r}, expected exact {expected_dw!r}"
            )

    stub_weaks = sorted(str(x) for x in alpha_scan.get("stub_weak_defs", ()))
    if stub_weaks:
        raise RuntimeError(f"stub object must define only STB_GLOBAL symbols, found weak: {stub_weaks}")

    rt_strong = set(str(x) for x in alpha_scan["runtime_strong_defs"])
    rt_weak = set(str(x) for x in alpha_scan["runtime_weak_defs"])
    stub_globals = set(str(x) for x in alpha_scan["stub_global_defs"])
    rt_weak_only = rt_weak - rt_strong

    strong_collisions = sorted(set(expected_dw) & rt_strong)
    if strong_collisions:
        raise RuntimeError(
            f"displaced_weak symbol(s) have strong runtime definitions: {strong_collisions}"
        )
    missing_weak_in_rt = sorted(set(expected_dw) - rt_weak_only)
    if missing_weak_in_rt:
        raise RuntimeError(
            f"displaced_weak symbol(s) missing STB_WEAK runtime definitions: {missing_weak_in_rt}"
        )
    shadowed_weak = sorted(stub_globals & rt_weak_only)
    if shadowed_weak != expected_dw:
        raise RuntimeError(
            f"actual shadowed runtime-weak stub set {shadowed_weak!r} != expected {expected_dw!r}"
        )

    # ------------------------------------------------------------------
    # 2. B3.2: Each `displaced_weak` symbol's FINAL ELF `.symtab` address decodes to `udf #0`
    # ------------------------------------------------------------------
    stubs_obj_name = str(alpha_scan["stubs_obj_name"])
    dw_elf_addrs: dict[str, str] = {}
    for sym_name in expected_dw:
        defs = [s for s in nonlocal_defs_by_name.get(sym_name, []) if s.stype == 2]
        if not defs:
            defs = [s for s in all_defs_by_name.get(sym_name, []) if s.stype == 2]
        if len(defs) != 1:
            raise RuntimeError(
                f"displaced_weak `{sym_name}` expected 1 STT_FUNC .symtab def, found {len(defs)}"
            )
        dsym = defs[0]
        if dsym.stype != 2 or dsym.st_size != 4:
            raise RuntimeError(
                f"displaced_weak `{sym_name}` expected STT_FUNC size 4, got stype={dsym.stype} size={dsym.st_size}"
            )
        got = img.read_bytes(dsym.st_value, 4)
        if got is None or got[1] != elf_loader.PERM_RX:
            raise RuntimeError(
                f"displaced_weak `{sym_name}` at {dsym.st_value:#x} not mapped in RX segment"
            )
        if got[0] != b"\x00\x00\x00\x00":
            (word_val,) = struct.unpack("<I", got[0])
            raise RuntimeError(
                f"displaced_weak `{sym_name}` at {dsym.st_value:#x} decodes to {word_val:#010x}, "
                f"expected udf #0 (0x00000000)"
            )
        ment = _find_defining_map_entry(map_entries, dsym.st_value, 4)
        if ment["canonical_input"] != stubs_obj_name:
            raise RuntimeError(
                f"displaced_weak `{sym_name}` at {dsym.st_value:#x} defined by {ment['canonical_input']!r}, "
                f"expected stub object {stubs_obj_name!r}"
            )
        dw_elf_addrs[sym_name] = hex(dsym.st_value)

    # ------------------------------------------------------------------
    # 3. B3.3: `displaced_weak_referrers ⊆ cliLinkObjs` (by surviving `-Map` input section)
    # ------------------------------------------------------------------
    cli_obj_set = set(str(x) for x in alpha_scan["cli_link_obj_names"])
    section_relocs: Mapping[str, Mapping[str, Sequence[str]]] = alpha_scan["section_relocs"]
    dw_set = set(expected_dw)

    surviving_dw_referrers: list[str] = []
    non_cli_dw_referrers: list[str] = []
    for canon_inp, in_sec in sorted(kept_sec_pairs):
        rel_targets = section_relocs.get(canon_inp, {}).get(in_sec, ())
        if any(t in dw_set for t in rel_targets):
            ref_id = f"{canon_inp}:({in_sec})"
            surviving_dw_referrers.append(ref_id)
            if canon_inp not in cli_obj_set:
                non_cli_dw_referrers.append(ref_id)

    if not surviving_dw_referrers:
        raise RuntimeError(
            "displaced_weak_referrers check found 0 surviving referrer sections (fail-closed)"
        )
    if non_cli_dw_referrers:
        raise RuntimeError(
            f"displaced_weak_referrers outside cliLinkObjs forbidden under Option α: {non_cli_dw_referrers}"
        )
    if expected_lock is not None and "displaced_weak_referrers" in expected_lock:
        exp_refs = [str(x) for x in expected_lock["displaced_weak_referrers"]]
        if surviving_dw_referrers != exp_refs:
            raise RuntimeError(
                f"displaced_weak_referrers mismatch vs lock:\n"
                f"  got:      {surviving_dw_referrers!r}\n"
                f"  expected: {exp_refs!r}"
            )

    alpha_dw_lock = {
        "displaced_weak": expected_dw,
        "elf_addrs": dw_elf_addrs,
        "displaced_weak_referrers": surviving_dw_referrers,
    }

    # ------------------------------------------------------------------
    # 4. B3.4: `S1` + `S2` + GK rows 373 & 374 (`A-LINK v0.3.2` rule (vii))
    # ------------------------------------------------------------------
    object_shas: Mapping[str, str] = alpha_scan["object_shas"]
    object_classes: Mapping[str, str] = alpha_scan["object_classes"]
    archive_shas: Mapping[str, str] = alpha_scan["archive_shas"]
    archive_member_shas: Mapping[str, str] = alpha_scan["archive_member_shas"]
    s2_candidate_defs: Mapping[str, Mapping[str, Mapping[str, Any]]] = alpha_scan.get(
        "s2_candidate_defs", {}
    )
    strlen_override = alpha_scan.get("strlen_source_override")
    pinned_musl_refs = alpha_scan.get("pinned_musl_ref_bodies")
    if not isinstance(pinned_musl_refs, Mapping):
        raise RuntimeError(
            "GK row 373 (3): `alpha_scan` missing `pinned_musl_ref_bodies` from pinned rustc self-contained/libc.a"
        )

    s2_real_body_lock: dict[str, dict[str, Any]] = {}
    for s2_name in S2_REQUIRED_NAMES:
        # GK row 373 (1): Stock links can mark `mem*`/`strlen` LOCAL/HIDDEN in the shipped ELF;
        # resolve the unique `STT_FUNC` symbol in shipped ELF `.symtab`, then read the binding
        # strictly from the DEFINING INPUT OBJECT's `.symtab`.
        fn_defs = [s for s in nonlocal_defs_by_name.get(s2_name, []) if s.stype == 2]
        if not fn_defs:
            fn_defs = [s for s in all_defs_by_name.get(s2_name, []) if s.stype == 2]
        if len(fn_defs) != 1:
            raise RuntimeError(
                f"S2 `{s2_name}` expected 1 STT_FUNC .symtab definition in ELF, found {len(fn_defs)}"
            )
        dsym = fn_defs[0]
        if dsym.st_size <= 0:
            raise RuntimeError(
                f"S2 `{s2_name}` expected positive-size STT_FUNC, got size={dsym.st_size}"
            )
        ment = _find_defining_map_entry(map_entries, dsym.st_value, dsym.st_size)
        src_file = str(ment["source_file"])
        ar_mem = ment["archive_member"]
        in_sec = str(ment["input_section"])
        canon_inp = str(ment["canonical_input"])

        cand_def = s2_candidate_defs.get(canon_inp, {}).get(s2_name)
        if cand_def is None:
            raise RuntimeError(
                f"GK row 373 (1): defining input `{canon_inp}` missing `{s2_name}` in its input .symtab"
            )
        input_binding = str(cand_def["input_binding"])
        if input_binding != "STB_GLOBAL":
            raise RuntimeError(
                f"GK row 373 (1) violation: `{s2_name}` defined by `{canon_inp}` with input .symtab binding "
                f"{input_binding!r} (expected 'STB_GLOBAL'; STB_WEAK definer forbidden)"
            )
        if str(cand_def["sec_name"]) != in_sec or int(cand_def["size"]) != dsym.st_size:
            raise RuntimeError(
                f"S2 `{s2_name}` input .symtab ({cand_def['sec_name']}, size={cand_def['size']}) "
                f"disagrees with -Map/.symtab ({in_sec}, size={dsym.st_size})"
            )

        if ar_mem is not None:
            def_class = "R"
            mem_sha = archive_member_shas.get(canon_inp)
            ar_sha = archive_shas.get(src_file)
            if not mem_sha or not ar_sha:
                raise RuntimeError(f"S2 `{s2_name}` missing SHA-256 for archive member {canon_inp!r}")
            entry_sha = mem_sha
            entry_ar_sha: str | None = ar_sha
            n_object_file_sha: str | None = None
            archive_sha_labeled: str | None = ar_sha
            member_file_sha: str | None = mem_sha
            matched_libc_member: str | None = str(ar_mem)
        elif (
            s2_name == "strlen"
            and src_file == "strlen.lo"
            and isinstance(strlen_override, Mapping)
        ):
            obj_sha = object_shas.get(src_file)
            if not obj_sha or obj_sha != str(strlen_override["member_sha256"]):
                raise RuntimeError(
                    f"S1 `strlen.lo` sha256 {obj_sha!r} != pinned {strlen_override['member_sha256']!r}"
                )
            def_class = "R"
            src_file = str(strlen_override["source_file"])
            ar_mem = str(strlen_override["archive_member"])
            entry_sha = obj_sha
            entry_ar_sha = str(strlen_override["archive_sha256"])
            n_object_file_sha = None
            archive_sha_labeled = entry_ar_sha
            member_file_sha = obj_sha
            matched_libc_member = str(ar_mem)
        else:
            def_class = str(object_classes.get(src_file, ""))
            if def_class not in ("N", "S"):
                raise RuntimeError(
                    f"S2 `{s2_name}` resolved to unexpected object {src_file!r} (class={def_class!r})"
                )
            obj_sha = object_shas.get(src_file)
            if not obj_sha:
                raise RuntimeError(f"S2 `{s2_name}` missing SHA-256 for object {src_file!r}")
            entry_sha = obj_sha
            entry_ar_sha = None
            n_object_file_sha = obj_sha if def_class == "N" else None
            archive_sha_labeled = None
            member_file_sha = None
            matched_libc_member = None

        got_rx = img.read_bytes(dsym.st_value, dsym.st_size)
        if got_rx is None or got_rx[1] != elf_loader.PERM_RX:
            raise RuntimeError(f"S2 `{s2_name}` at {dsym.st_value:#x} not mapped in RX segment")
        elf_body = got_rx[0]
        body_sha = sha256_bytes(elf_body)
        src_body = bytes.fromhex(str(cand_def["body_hex"]))
        text_sha = sha256_bytes(src_body)
        cand_relocs: list[dict[str, Any]] = [
            {
                "offset": int(r.get("rel_offset", r.get("offset", 0))),
                "rel_offset": int(r.get("rel_offset", r.get("offset", 0))),
                "r_type": int(r.get("rtype", r.get("r_type", 0))),
                "rtype": int(r.get("rtype", r.get("r_type", 0))),
                "target_symbol": str(r.get("target", r.get("target_symbol", ""))),
                "target": str(r.get("target", r.get("target_symbol", ""))),
                "addend": int(r.get("addend", 0)),
            }
            for r in cand_def.get("reloc_records", ())
        ]
        n_text_relocs: int | None = len(cand_relocs) if def_class == "N" else None
        member_text_relocs: int | None = len(cand_relocs) if def_class == "R" else None

        # S1 & GK row 373 (2) + row 374: `strlen` 88 B unmasked == `muslStrlenWords` (0 relocs)
        if s2_name == "strlen":
            if (
                def_class != "R"
                or src_file != "libc.a"
                or ar_mem != "strlen.lo"
                or in_sec != ".text.strlen"
                or dsym.st_size != 88
                or entry_sha != PINNED_STRLEN_LO_SHA256
            ):
                raise RuntimeError(
                    f"S1 `strlen` pin violated: expected libc.a(strlen.lo):(.text.strlen) 88 B "
                    f"sha256={PINNED_STRLEN_LO_SHA256}, got class={def_class!r} {src_file}({ar_mem}):({in_sec}) "
                    f"size={dsym.st_size} sha256={entry_sha}"
                )
            if cand_relocs:
                raise RuntimeError(
                    f"GK row 374: `strlen` defining section `{canon_inp}:({in_sec})` must have 0 relocations, "
                    f"found {cand_relocs}"
                )
            if elf_body != MUSL_STRLEN_BYTES:
                raise RuntimeError(
                    f"GK row 373 (2): `strlen` ELF bytes at {dsym.st_value:#x} (+88 B) disagree with "
                    f"ProofLib.StdStartup.muslStrlenWords"
                )
            member_text_relocs = 0
            libc_byte_equal: bool | None = True
        # GK row 373 (3) + row 374 + row 375 (i)-(iv):
        # `memcpy` & `memset` FINAL ELF body == pinned `libc.a` member `.text` (0 relocs on BOTH sides)
        elif s2_name in ("memcpy", "memset"):
            ref_info = pinned_musl_refs.get(s2_name)
            if not isinstance(ref_info, Mapping):
                raise RuntimeError(
                    f"GK row 373 (3): missing pinned libc.a reference body for `{s2_name}`"
                )
            if int(ref_info.get("reloc_count", -1)) != 0:
                raise RuntimeError(
                    f"GK row 374: pinned libc.a `{s2_name}` member has non-zero reloc_count={ref_info.get('reloc_count')}"
                )
            if cand_relocs:
                raise RuntimeError(
                    f"GK row 374: `{s2_name}` defining section `{canon_inp}:({in_sec})` must have 0 relocations, "
                    f"found {cand_relocs}"
                )
            ref_body = bytes.fromhex(str(ref_info["body_hex"]))
            if dsym.st_size != len(ref_body) or elf_body != ref_body or src_body != ref_body:
                raise RuntimeError(
                    f"GK row 373 (3) / 375 (iii): `{s2_name}` FINAL ELF body at {dsym.st_value:#x} "
                    f"(size={dsym.st_size}, sha256={body_sha}) is NOT byte-equal to pinned rustc "
                    f"libc.a({ref_info.get('member')}) (size={len(ref_body)}, text_sha={ref_info.get('body_sha256')})"
                )
            # GK row 375 (i) & (iv): record matched `libc.a` archive_sha + member_file_sha even when class N
            archive_sha_labeled = str(ref_info["archive_sha256"])
            member_file_sha = str(ref_info["member_sha256"])
            matched_libc_member = str(ref_info["member"])
            if def_class == "N":
                n_text_relocs = 0
            member_text_relocs = 0
            libc_byte_equal = True
        else:
            # GK row 375: `memmove`, `memcmp`, `bcmp` have NO `libc.a` full-body equality;
            # verify against defining N object section modulo relocations + record `relocs` list.
            _verify_masked_body_equal(s2_name, elf_body, src_body, cand_relocs)
            libc_byte_equal = None

        s2_real_body_lock[s2_name] = {
            "definer_class": def_class,
            "input_binding": input_binding,
            "elf_addr": hex(dsym.st_value),
            "size": int(dsym.st_size),
            "input_section": in_sec,
            "source_file": src_file,
            "archive_member": ar_mem,
            "sha256": entry_sha,
            "archive_sha256": entry_ar_sha,
            "n_object_file_sha": n_object_file_sha,
            "archive_sha": archive_sha_labeled,
            "member_name": matched_libc_member,
            "member_file_sha": member_file_sha,
            "matched_libc_member": matched_libc_member,
            "n_text_relocs": n_text_relocs,
            "member_text_relocs": member_text_relocs,
            "text_sha": text_sha,
            "body_sha256": body_sha,
            "relocs": cand_relocs,
            "byte_equal": libc_byte_equal,
        }

    # GK row 375 (`bcmp` single-word unconditional `B` decode -> `memcmp` ELF address)
    bcmp_row = s2_real_body_lock["bcmp"]
    memcmp_row = s2_real_body_lock["memcmp"]
    bcmp_addr = int(str(bcmp_row["elf_addr"]), 16)
    memcmp_addr = int(str(memcmp_row["elf_addr"]), 16)
    if int(bcmp_row["size"]) != 4:
        raise RuntimeError(f"GK row 375: `bcmp` expected st_size == 4, got {bcmp_row['size']}")
    bcmp_got = img.read_bytes(bcmp_addr, 4)
    if bcmp_got is None or bcmp_got[1] != elf_loader.PERM_RX:
        raise RuntimeError(f"GK row 375: `bcmp` at {bcmp_addr:#x} not readable in RX segment")
    (bcmp_word,) = struct.unpack("<I", bcmp_got[0])
    if (bcmp_word & 0xFC000000) != 0x14000000:
        raise RuntimeError(
            f"GK row 375: `bcmp` word {bcmp_word:#010x} at {bcmp_addr:#x} is not an unconditional AArch64 `B` (`0x14000000`)"
        )
    imm26 = bcmp_word & 0x03FFFFFF
    if imm26 & (1 << 25):
        imm26 -= 1 << 26
    bcmp_target = (bcmp_addr + (imm26 << 2)) & 0xFFFFFFFFFFFFFFFF
    if bcmp_target != memcmp_addr:
        raise RuntimeError(
            f"GK row 375: `bcmp` `B` at {bcmp_addr:#x} targets {bcmp_target:#x} != `memcmp` {memcmp_addr:#x}"
        )

    if expected_lock is not None and "s2_real_body_lock" in expected_lock:
        exp_s2 = expected_lock["s2_real_body_lock"]
        if not isinstance(exp_s2, Mapping) or set(exp_s2.keys()) != set(s2_real_body_lock.keys()):
            raise RuntimeError(
                f"s2_real_body_lock key set mismatch: got {sorted(s2_real_body_lock.keys())}, "
                f"expected {sorted(exp_s2.keys()) if isinstance(exp_s2, Mapping) else exp_s2!r}"
            )
        for k, got_ent in s2_real_body_lock.items():
            exp_ent = dict(exp_s2[k])
            exp_be = exp_ent.get("byte_equal")
            if k in ("strlen", "memcpy", "memset"):
                if exp_be is not True:
                    raise RuntimeError(
                        f"S2 lock entry `{k}` must specify boolean `byte_equal = true`, got {exp_be!r}"
                    )
                norm_be: bool | None = True
            else:
                if exp_be not in (None, False, ""):
                    raise RuntimeError(
                        f"GK row 375: S2 lock entry `{k}` must NOT claim libc.a `byte_equal = true`, got {exp_be!r}"
                    )
                norm_be = None
            raw_relocs = exp_ent.get("relocs", [])
            if not isinstance(raw_relocs, list):
                raise RuntimeError(f"S2 lock entry `{k}` `relocs` must be a list")
            norm_relocs = [
                {
                    "offset": int(r.get("rel_offset", r["offset"])),
                    "rel_offset": int(r.get("rel_offset", r["offset"])),
                    "r_type": int(r.get("rtype", r["r_type"])),
                    "rtype": int(r.get("rtype", r["r_type"])),
                    "target_symbol": str(r.get("target", r["target_symbol"])),
                    "target": str(r.get("target", r["target_symbol"])),
                    "addend": int(r.get("addend", 0)),
                }
                for r in raw_relocs
            ]
            raw_matched_mem = exp_ent.get("matched_libc_member", exp_ent.get("member_name"))
            norm_matched_mem = (
                str(raw_matched_mem) if raw_matched_mem not in (None, "") else None
            )
            norm_exp = {
                "definer_class": str(exp_ent["definer_class"]),
                "input_binding": str(exp_ent["input_binding"]),
                "elf_addr": str(exp_ent["elf_addr"]),
                "size": int(exp_ent["size"]),
                "input_section": str(exp_ent["input_section"]),
                "source_file": str(exp_ent["source_file"]),
                "archive_member": (
                    str(exp_ent["archive_member"])
                    if exp_ent.get("archive_member") not in (None, "")
                    else None
                ),
                "sha256": str(exp_ent["sha256"]),
                "archive_sha256": (
                    str(exp_ent["archive_sha256"])
                    if exp_ent.get("archive_sha256") not in (None, "")
                    else None
                ),
                "n_object_file_sha": (
                    str(exp_ent["n_object_file_sha"])
                    if exp_ent.get("n_object_file_sha") not in (None, "")
                    else None
                ),
                "archive_sha": (
                    str(exp_ent["archive_sha"])
                    if exp_ent.get("archive_sha") not in (None, "")
                    else None
                ),
                "member_name": norm_matched_mem,
                "member_file_sha": (
                    str(exp_ent["member_file_sha"])
                    if exp_ent.get("member_file_sha") not in (None, "")
                    else None
                ),
                "matched_libc_member": norm_matched_mem,
                "n_text_relocs": (
                    int(exp_ent["n_text_relocs"])
                    if exp_ent.get("n_text_relocs") not in (None, "")
                    else None
                ),
                "member_text_relocs": (
                    int(exp_ent["member_text_relocs"])
                    if exp_ent.get("member_text_relocs") not in (None, "")
                    else None
                ),
                "text_sha": str(exp_ent["text_sha"]),
                "body_sha256": str(exp_ent["body_sha256"]),
                "relocs": norm_relocs,
                "byte_equal": norm_be,
            }
            cmp_got = dict(got_ent)
            if not verify_addresses:
                norm_exp.pop("elf_addr", None)
                cmp_got.pop("elf_addr", None)
                if k in ("bcmp", "memmove"):
                    norm_exp.pop("body_sha256", None)
                    cmp_got.pop("body_sha256", None)
            if cmp_got != norm_exp:
                raise RuntimeError(
                    f"S2 lock mismatch for `{k}`:\n  got:      {cmp_got!r}\n  expected: {norm_exp!r}"
                )

    # ------------------------------------------------------------------
    # 5. B3.5: `D1` (`d1_extern_data_lock`: kept proved non-placed `STT_OBJECT`s == `externData \ gc_dead`)
    # ------------------------------------------------------------------
    if not generated_extern_data:
        raise RuntimeError("D1 requires non-empty `generated_extern_data` from LibsignalSessionObj.lean")

    cli_defined = set(str(x) for x in alpha_scan["cli_defined_syms"])
    cli_undef_objs = set(str(x) for x in alpha_scan["cli_undef_object_syms"])

    kept_cli_reloc_targets: set[str] = set()
    for canon_inp, in_sec in kept_sec_pairs:
        if canon_inp in cli_obj_set:
            kept_cli_reloc_targets.update(section_relocs.get(canon_inp, {}).get(in_sec, ()))

    kept_external_objects: dict[str, dict[str, Any]] = {}
    for t_sym in sorted(kept_cli_reloc_targets):
        dem_t = demangle_rust_v0(t_sym)
        cands = [s for s in all_defs_by_name.get(t_sym, []) if s.stype == 1]
        if not cands:
            if dem_t in generated_extern_data and t_sym not in cli_defined:
                raise RuntimeError(
                    f"D1 symbol `{t_sym}` (`{dem_t}`) referenced by kept cliLinkObjs section "
                    "lacks STT_OBJECT definition in ELF .symtab"
                )
            continue  # Not an `STT_OBJECT`
        if t_sym in cli_defined:
            for csym in cands:
                if not csym.is_local and csym.st_size > 0:
                    ment = _find_defining_map_entry(map_entries, csym.st_value, csym.st_size)
                    if ment["canonical_input"] not in cli_obj_set:
                        raise RuntimeError(
                            f"D1 internal cliLinkObjs STT_OBJECT `{t_sym}` resolved outside cliLinkObjs: {ment}"
                        )
            continue

        obj_cands = [s for s in cands if not s.is_local]
        if not obj_cands:
            obj_cands = list(cands)
        if len(obj_cands) != 1:
            raise RuntimeError(
                f"D1 external STT_OBJECT `{t_sym}` expected 1 .symtab def, found {len(obj_cands)}"
            )
        osym = obj_cands[0]
        dem_name = demangle_rust_v0(t_sym)
        if dem_name not in generated_extern_data:
            raise RuntimeError(
                f"D1 violation: kept proved section references unexpected external STT_OBJECT "
                f"`{t_sym}` (demangled `{dem_name}`), not in LibsignalSessionObj.externData "
                f"{sorted(generated_extern_data.keys())}"
            )
        exp_obj_sz = int(generated_extern_data[dem_name])
        if osym.st_size != exp_obj_sz:
            raise RuntimeError(
                f"D1 external STT_OBJECT `{t_sym}` (`{dem_name}`) size {osym.st_size} != "
                f"LibsignalSessionObj.externData size {exp_obj_sz}"
            )
        ment = _find_defining_map_entry(map_entries, osym.st_value, osym.st_size)
        src_file = str(ment["source_file"])
        ar_mem = ment["archive_member"]
        in_sec = str(ment["input_section"])
        canon_inp = str(ment["canonical_input"])

        if ar_mem is not None:
            def_class = "R"
            def_kind = "archive_member"
            obj_sha = archive_member_shas.get(canon_inp, "")
        else:
            raw_cls = str(object_classes.get(src_file, ""))
            if raw_cls == "Z":
                def_class = "Z"
                def_kind = "stub_object"
                got_obj_bytes = img.read_bytes(osym.st_value, osym.st_size)
                if got_obj_bytes is None or got_obj_bytes[1] != elf_loader.PERM_RW:
                    raise RuntimeError(
                        f"D1 zero-stub STT_OBJECT `{t_sym}` at {osym.st_value:#x} not mapped RW"
                    )
                if got_obj_bytes[0] != (b"\x00" * osym.st_size):
                    raise RuntimeError(
                        f"D1 zero-stub STT_OBJECT `{t_sym}` at {osym.st_value:#x} has non-zero bytes"
                    )
            elif raw_cls == "S":
                def_class = "S"
                def_kind = "crate_section"
            elif raw_cls == "N":
                def_class = "N"
                def_kind = "native_object"
            else:
                raise RuntimeError(
                    f"D1 external STT_OBJECT `{t_sym}` has unexpected definer {src_file!r} (class={raw_cls!r})"
                )
            obj_sha = object_shas.get(src_file, "")

        if not HEX64_RE.match(obj_sha):
            raise RuntimeError(f"D1 external STT_OBJECT `{t_sym}` missing valid definer sha256")

        kept_external_objects[t_sym] = {
            "demangled_name": dem_name,
            "definer_class": def_class,
            "definer_kind": def_kind,
            "elf_addr": hex(osym.st_value),
            "size": int(osym.st_size),
            "input_section": in_sec,
            "source_file": src_file,
            "archive_member": ar_mem,
            "sha256": obj_sha,
        }

    gc_dead_mangled: list[str] = []
    gc_dead_demangled: list[str] = []
    for usym in sorted(cli_undef_objs - cli_defined):
        if usym in kept_external_objects:
            continue
        udem = demangle_rust_v0(usym)
        if udem in generated_extern_data:
            if usym in kept_cli_reloc_targets:
                raise RuntimeError(
                    f"D1 symbol `{usym}` (`{udem}`) referenced by kept cliLinkObjs section yet missing STT_OBJECT def"
                )
            gc_dead_mangled.append(usym)
            gc_dead_demangled.append(udem)

    kept_demangled_set = {v["demangled_name"] for v in kept_external_objects.values()}
    if (kept_demangled_set | set(gc_dead_demangled)) != set(generated_extern_data.keys()):
        raise RuntimeError(
            f"D1 externData partition mismatch: kept={sorted(kept_demangled_set)}, "
            f"gc_dead={sorted(gc_dead_demangled)}, expected_total={sorted(generated_extern_data.keys())}"
        )
    if kept_demangled_set & set(gc_dead_demangled):
        raise RuntimeError("D1 kept and gc_dead externData sets overlap")

    d1_extern_data_lock: dict[str, Any] = {
        "total_proved_extern_data": len(generated_extern_data),
        "kept": kept_external_objects,
        "gc_dead": sorted(gc_dead_mangled),
        "gc_dead_demangled": sorted(gc_dead_demangled),
    }

    if expected_lock is not None and "d1_extern_data_lock" in expected_lock:
        exp_d1 = expected_lock["d1_extern_data_lock"]
        if not isinstance(exp_d1, Mapping):
            raise RuntimeError("lock `d1_extern_data_lock` must be a table/dict")
        if int(exp_d1.get("total_proved_extern_data", -1)) != len(generated_extern_data):
            raise RuntimeError(
                f"D1 total_proved_extern_data {len(generated_extern_data)} != lock {exp_d1.get('total_proved_extern_data')}"
            )
        if [str(x) for x in exp_d1.get("gc_dead", [])] != d1_extern_data_lock["gc_dead"]:
            raise RuntimeError(
                f"D1 gc_dead mismatch: got {d1_extern_data_lock['gc_dead']!r} != lock {exp_d1.get('gc_dead')!r}"
            )
        if "gc_dead_demangled" in exp_d1 and [
            str(x) for x in exp_d1["gc_dead_demangled"]
        ] != d1_extern_data_lock["gc_dead_demangled"]:
            raise RuntimeError(
                f"D1 gc_dead_demangled mismatch: got {d1_extern_data_lock['gc_dead_demangled']!r} "
                f"!= lock {exp_d1['gc_dead_demangled']!r}"
            )
        exp_kept = exp_d1.get("kept", {})
        if not isinstance(exp_kept, Mapping) or set(exp_kept.keys()) != set(
            kept_external_objects.keys()
        ):
            raise RuntimeError(
                f"D1 kept symbol set mismatch: got {sorted(kept_external_objects.keys())}, "
                f"expected {sorted(exp_kept.keys()) if isinstance(exp_kept, Mapping) else exp_kept!r}"
            )
        for k, got_ent in kept_external_objects.items():
            raw_exp = dict(exp_kept[k])
            norm_exp = {
                "demangled_name": str(raw_exp["demangled_name"]),
                "definer_class": str(raw_exp["definer_class"]),
                "definer_kind": str(raw_exp["definer_kind"]),
                "elf_addr": str(raw_exp["elf_addr"]),
                "size": int(raw_exp["size"]),
                "input_section": str(raw_exp["input_section"]),
                "source_file": str(raw_exp["source_file"]),
                "archive_member": (
                    str(raw_exp["archive_member"])
                    if raw_exp.get("archive_member") not in (None, "")
                    else None
                ),
                "sha256": str(raw_exp["sha256"]),
            }
            cmp_got = dict(got_ent)
            if not verify_addresses:
                norm_exp.pop("elf_addr", None)
                cmp_got.pop("elf_addr", None)
            if cmp_got != norm_exp:
                raise RuntimeError(
                    f"D1 lock mismatch for `{k}`:\n  got:      {cmp_got!r}\n  expected: {norm_exp!r}"
                )

    return {
        "alpha_displaced_weak_lock": alpha_dw_lock,
        "s2_real_body_lock": s2_real_body_lock,
        "d1_extern_data_lock": d1_extern_data_lock,
    }
