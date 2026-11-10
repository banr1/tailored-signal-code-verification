#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Pure-Python ELF64 (`.o` ET_REL, `.a` archives, `ET_EXEC`), `ld.lld` `-Map` / `--why-extract`
/ `--trace-symbol` parsers, Rust v0 + legacy demangler, relocation-masked byte comparator, and
trusted-spec symbol-table loaders for `alink_check.py` and `m4_lock.py`.

Zero external `readelf` / `nm` / `objdump` subprocesses; fails closed on malformed inputs,
multiple `.symtab` sections, thin archives, or LLVM bitcode members.
"""

from __future__ import annotations

import dataclasses
from dataclasses import dataclass, field
import hashlib
import pathlib
import re
import struct
from typing import Iterable, Sequence

PAGE_SIZE = 4096

# ELF constants
ET_REL = 1
ET_EXEC = 2
EM_AARCH64 = 183

SHT_NULL = 0
SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHT_STRTAB = 3
SHT_RELA = 4
SHT_NOBITS = 8
SHT_INIT_ARRAY = 14
SHT_FINI_ARRAY = 15
SHT_PREINIT_ARRAY = 16
SHT_GROUP = 17
SHT_SYMTAB_SHNDX = 18

SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4

SHN_UNDEF = 0
SHN_LORESERVE = 0xFF00
SHN_ABS = 0xFFF1
SHN_COMMON = 0xFFF2
SHN_XINDEX = 0xFFFF

STB_LOCAL = 0
STB_GLOBAL = 1
STB_WEAK = 2

STT_NOTYPE = 0
STT_OBJECT = 1
STT_FUNC = 2
STT_SECTION = 3
STT_FILE = 4
STT_COMMON = 5
STT_TLS = 6

BIND_NAMES: dict[int, str] = {
    STB_LOCAL: "STB_LOCAL",
    STB_GLOBAL: "STB_GLOBAL",
    STB_WEAK: "STB_WEAK",
}

# AArch64 ELF64 relocation byte widths
R_AARCH64_NONE_SET = frozenset({0, 256})
R_AARCH64_8B_SET = frozenset({
    257,  # R_AARCH64_ABS64
    260,  # R_AARCH64_PREL64
})
R_AARCH64_2B_SET = frozenset({
    259,  # R_AARCH64_ABS16
    262,  # R_AARCH64_PREL16
})
# All standard static AArch64 32-bit data & instruction relocations (branches, calls, ADR/ADRP,
# ADD/LDST, GOT, TLSLE/TLSIE)
R_AARCH64_4B_SET = frozenset({
    258,  # R_AARCH64_ABS32
    261,  # R_AARCH64_PREL32
    273,  # R_AARCH64_ADR_PREL_PG_HI21_NC / LO21 family
    274,  # R_AARCH64_ADR_PREL_LO21
    275,  # R_AARCH64_ADR_PREL_PG_HI21
    276,  # R_AARCH64_ADR_PREL_PG_HI21_NC
    277,  # R_AARCH64_ADD_ABS_LO12_NC
    278,  # R_AARCH64_LDST8_ABS_LO12_NC
    279,  # R_AARCH64_TSTBR14
    280,  # R_AARCH64_CONDBR19
    282,  # R_AARCH64_JUMP26
    283,  # R_AARCH64_CALL26
    284,  # R_AARCH64_LDST16_ABS_LO12_NC
    285,  # R_AARCH64_LDST32_ABS_LO12_NC
    286,  # R_AARCH64_LDST64_ABS_LO12_NC
    287,  # R_AARCH64_MOVW_PREL_G0
    288,  # R_AARCH64_MOVW_PREL_G0_NC
    289,  # R_AARCH64_MOVW_PREL_G1
    290,  # R_AARCH64_MOVW_PREL_G1_NC
    291,  # R_AARCH64_MOVW_PREL_G2
    292,  # R_AARCH64_MOVW_PREL_G2_NC
    293,  # R_AARCH64_MOVW_PREL_G3
    299,  # R_AARCH64_LDST128_ABS_LO12_NC
    309,  # R_AARCH64_GOTREL64
    310,  # R_AARCH64_GOTREL32
    311,  # R_AARCH64_ADR_GOT_PAGE
    312,  # R_AARCH64_LD64_GOT_LO12_NC
    313,  # R_AARCH64_LD64_GOTPAGE_LO15
    314,  # R_AARCH64_PLT32
    540, 541, 542, 543, 544, 545, 546, 547, 548, 549,
    550, 551, 552, 553, 554, 555, 556, 557, 560,
})

LLVM_BITCODE_MAGICS = (b"BC\xc0\xde", b"\xde\xc0\x17\x0b")

MAP_HEADER = "             VMA              LMA     Size Align Out     In      Symbol"
MAP_COLS = 49
WHY_HEADER = "reference\textracted\tsymbol"

# Exact 22 32-bit LE words (88 bytes) of `ProofLib/StdStartup/Strlen.lean` `muslStrlenWords`
DEFAULT_MUSL_STRLEN_WORDS: tuple[int, ...] = (
    0xAA0003E1, 0xF240083F,
    0x540000A0, 0x39400022,
    0x34000202, 0x91000421,
    0x17FFFFFB, 0xB207DBE4,
    0xF29FDFE4, 0xF9400022,
    0x8B040043, 0x8A220062,
    0xF201C05F, 0x54000061,
    0x91002021, 0x17FFFFFA,
    0x39400022, 0x34000062,
    0x91000421, 0x17FFFFFD,
    0xCB000020, 0xD65F03C0,
)
DEFAULT_MUSL_STRLEN_BYTES: bytes = struct.pack(f"<{len(DEFAULT_MUSL_STRLEN_WORDS)}I", *DEFAULT_MUSL_STRLEN_WORDS)
assert len(DEFAULT_MUSL_STRLEN_BYTES) == 88

# `Arm64/Trusted/Spec/RustRuntime.lean` `Rust.isPanicSymbol`
RUST_PANIC_EXACT_NAMES: frozenset[str] = frozenset({
    "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error",
})

# `CliBinaryPq.lean` `cliPanicSymbolsPlaced` (exact 18 mangled keys from `CliBinaryPq.lean:238-256`)
DEFAULT_CLI_PANIC_SYMBOLS_PLACED: frozenset[str] = frozenset({
    "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_",
    "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_",
    "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error",
    "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error",
    "_RNvNtCskxtBwYRO61I_4core6option13expect_failed",
    "_RNvNtCskxtBwYRO61I_4core6option13unwrap_failed",
    "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed",
    "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check",
    "_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_inner",
    "_RNvNtCskxtBwYRO61I_4core9panicking5panic",
    "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt",
    "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail",
    "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow",
    "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul_overflow",
    "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflow",
    "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow",
    "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumed",
    "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed",
})

# `CliBinaryPq.lean` `cliHookTablePlaced` (exact 37 mangled/C keys after WP6c + `libsignal-cli` rename)
DEFAULT_CLI_HOOK_TABLE_PLACED: frozenset[str] = frozenset({
    # 18 PQXDH crypto/session hooks (`cliPqxdhHookTablePlaced`)
    "_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512",
    "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
    "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
    "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
    "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
    "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
    "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
    "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
    "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
    "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
    "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
    "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
    "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
    "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
    "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
    "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
    "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
    "_RNvCs65XVORQObL2_12libcrux_hmac4hmac",
    # 19 CLI / libc / IO / fmt / TR hooks (`cliHookTablePlaced` after F3 + IO.6b + stock `ld.lld` WP6c cutover)
    "memmove",
    "bcmp",
    "strlen",
    "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_file",
    "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io12write_stdout",
    "_RNvNtNtCskxtBwYRO61I_4core5slice6memchr7memrchr",
    "_RNvNtNtCskxtBwYRO61I_4core3str8converts9from_utf8",
    "_RNvNtCskxtBwYRO61I_4core3fmt5write",
    "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner",
    "_RNvMs5_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTime14duration_since",
    "_RNvXs6_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTimeINtNtNtCskxtBwYRO61I_4core3ops5arith3AddNtNtBR_4time8DurationE3add",
    "_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek",
    "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256",
    "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encrypt",
    "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decrypt",
    "_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4from",
    "_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellman",
    "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop",
    "_RNvXse_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12SharedSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop",
})

DISPLACED_WEAK_ATOMICS: frozenset[str] = frozenset({
    "__aarch64_cas8_acq_rel",
    "__aarch64_ldadd8_rel",
    "__aarch64_ldadd8_relax",
})

DEFAULT_FAILSTOP_DROP_STUBS: frozenset[str] = frozenset({
    "_RNvXsd_NtNtCskxtBwYRO61I_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop",
    "<core::io::error::CustomOwner as core::ops::drop::Drop>::drop",
})

# Pinned `rustc 1.98.1` `aarch64-unknown-linux-musl/lib/self-contained/libc.a` & member digests (GK rows 373-375)
PINNED_RUSTC_MUSL_LIBC_SHA256 = "b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f"
PINNED_STRLEN_MEMBER_SHA256 = "485bad76aa759b278a152412850885ad84fab30893998d18337c2d1d1d56ec81"

# Trusted `externData` symbols (`LibsignalTripleRatchet.lean` / GK row 372 D1)
DEFAULT_TRUSTED_EXTERN_DATA: frozenset[str] = frozenset({
    "_RNvCs4Dv7yoBiUx4_3log20MAX_LOG_LEVEL_FILTER",
    "_RNvNtNtNtNtCs2wR8L9wiBdT_16curve25519_dalek7backend6serial3u649constants23ED25519_BASEPOINT_TABLE",
    "_RNvNtNtCs40xgxkZUUew_9getrandom8backends27linux_android_with_fallback12GETRANDOM_FN",
    "_RNvNtNtNtCskxtBwYRO61I_4core7unicode12unicode_data11white_space14WHITESPACE_MAP",
})

R_AARCH64_NAMES: dict[int, str] = {
    0: "R_AARCH64_NONE",
    256: "R_AARCH64_NONE",
    257: "R_AARCH64_ABS64",
    258: "R_AARCH64_ABS32",
    259: "R_AARCH64_ABS16",
    260: "R_AARCH64_PREL64",
    261: "R_AARCH64_PREL32",
    262: "R_AARCH64_PREL16",
    274: "R_AARCH64_ADR_PREL_LO21",
    275: "R_AARCH64_ADR_PREL_PG_HI21",
    276: "R_AARCH64_ADR_PREL_PG_HI21_NC",
    277: "R_AARCH64_ADD_ABS_LO12_NC",
    278: "R_AARCH64_LDST8_ABS_LO12_NC",
    279: "R_AARCH64_TSTBR14",
    280: "R_AARCH64_CONDBR19",
    282: "R_AARCH64_JUMP26",
    283: "R_AARCH64_CALL26",
    284: "R_AARCH64_LDST16_ABS_LO12_NC",
    285: "R_AARCH64_LDST32_ABS_LO12_NC",
    286: "R_AARCH64_LDST64_ABS_LO12_NC",
    299: "R_AARCH64_LDST128_ABS_LO12_NC",
    311: "R_AARCH64_ADR_GOT_PAGE",
    312: "R_AARCH64_LD64_GOT_LO12_NC",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ==============================================================================
# Pure-Python Rust Symbol Demangler (`_R` v0 + `_ZN` legacy, `{:#}` alternate)
# ==============================================================================

_V0_PRIMITIVES: dict[str, str] = {
    "a": "i8",
    "b": "bool",
    "c": "char",
    "d": "f64",
    "e": "str",
    "f": "f32",
    "h": "u8",
    "i": "isize",
    "j": "usize",
    "l": "i32",
    "m": "u32",
    "n": "i128",
    "o": "u128",
    "p": "_",
    "s": "i16",
    "t": "u16",
    "u": "()",
    "v": "...",
    "x": "i64",
    "y": "u64",
    "z": "!",
}


class _V0Demangler:
    """RFC 2603 Rust `_R` v0 symbol demangler producing `{:#}` alternate output
    (omitting crate disambiguator `[hash]`, matching `rustc_demangle` `{:#}`)."""

    def __init__(self, sym: str) -> None:
        self.s = sym
        self.pos = 2  # skip `_R`

    def peek(self) -> str:
        return self.s[self.pos] if self.pos < len(self.s) else ""

    def next_ch(self) -> str:
        if self.pos >= len(self.s):
            raise ValueError("unexpected EOF in v0 symbol")
        ch = self.s[self.pos]
        self.pos += 1
        return ch

    def eat(self, ch: str) -> bool:
        if self.peek() == ch:
            self.pos += 1
            return True
        return False

    def parse_base62(self) -> int:
        if self.eat("_"):
            return 0
        n = 0
        while True:
            ch = self.next_ch()
            if ch == "_":
                return n + 1
            if "0" <= ch <= "9":
                d = ord(ch) - ord("0")
            elif "a" <= ch <= "z":
                d = 10 + ord(ch) - ord("a")
            elif "A" <= ch <= "Z":
                d = 36 + ord(ch) - ord("A")
            else:
                raise ValueError(f"bad base62 char {ch!r}")
            n = n * 62 + d

    def parse_dec_num(self) -> int:
        if self.peek() == "0":
            self.pos += 1
            return 0
        start = self.pos
        while self.pos < len(self.s) and self.s[self.pos].isdigit():
            self.pos += 1
        if start == self.pos:
            raise ValueError(f"expected decimal length at {self.pos}")
        return int(self.s[start : self.pos])

    def parse_opt_disambiguator(self) -> int | None:
        if self.eat("s"):
            return self.parse_base62()
        return None

    def parse_ident(self) -> str:
        is_puny = self.eat("u")
        length = self.parse_dec_num()
        self.eat("_")
        if self.pos + length > len(self.s):
            raise ValueError("ident length exceeds symbol")
        raw = self.s[self.pos : self.pos + length]
        self.pos += length
        if is_puny:
            return _decode_rust_punycode(raw)
        return raw

    def parse_backref(self, parse_fn) -> str:
        offset = self.parse_base62()
        target = 2 + offset
        if target >= self.pos:
            raise ValueError("forward/self backref in v0 symbol")
        saved = self.pos
        self.pos = target
        try:
            return parse_fn()
        finally:
            self.pos = saved

    def parse_lifetime(self) -> str:
        if self.eat("L"):
            idx = self.parse_base62()
            return "" if idx == 0 else "'_"
        return ""

    def parse_binder(self) -> int:
        if self.eat("G"):
            return self.parse_base62() + 1
        return 0

    def parse_path(self, in_value: bool = False) -> str:
        tag = self.next_ch()
        if tag == "C":
            self.parse_opt_disambiguator()
            return self.parse_ident()
        if tag == "M":
            self.parse_opt_disambiguator()
            _impl_path = self.parse_path(in_value=False)
            ty = self.parse_type()
            return f"<{ty}>"
        if tag == "X":
            self.parse_opt_disambiguator()
            _impl_path = self.parse_path(in_value=False)
            ty = self.parse_type()
            tr = self.parse_path(in_value=False)
            return f"<{ty} as {tr}>"
        if tag == "Y":
            ty = self.parse_type()
            tr = self.parse_path(in_value=False)
            return f"<{ty} as {tr}>"
        if tag == "N":
            ns = self.next_ch()
            parent = self.parse_path(in_value=False)
            dis = self.parse_opt_disambiguator()
            name = self.parse_ident()
            if ns in ("C", "v"):
                return f"{parent}::{name}" if parent else name
            if ns.isupper():
                # Special compiler namespace (`C` closure, `S` shim, `K` const/static, etc.)
                idx = 0 if dis is None else dis + 1
                if ns == "C":
                    label = f"{{closure#{idx - 1 if dis is not None else 0}}}"
                    if name:
                        label = f"{{closure:{name}#{idx - 1 if dis is not None else 0}}}"
                elif ns == "S":
                    label = f"{{shim:{name}#{idx - 1 if dis is not None else 0}}}" if name else "{shim}"
                else:
                    num = 0 if dis is None else dis
                    label = f"{{{ns}#{num}}}" if not name else f"{name}"
                return f"{parent}::{label}" if parent else label
            return f"{parent}::{name}" if parent else name
        if tag == "I":
            base = self.parse_path(in_value=in_value)
            args: list[str] = []
            while not self.eat("E"):
                arg = self.parse_generic_arg()
                if arg:
                    args.append(arg)
            if not args:
                return base
            sep = "::" if in_value else ""
            return f"{base}{sep}<{', '.join(args)}>"
        if tag == "B":
            return self.parse_backref(lambda: self.parse_path(in_value=in_value))
        raise ValueError(f"unknown v0 path tag {tag!r} at {self.pos - 1}")

    def parse_generic_arg(self) -> str:
        if self.peek() == "L":
            return self.parse_lifetime()
        if self.eat("K"):
            return self.parse_const()
        if self.eat("p"):
            name = self.parse_ident()
            eq_ty = self.parse_type()
            return f"{name} = {eq_ty}"
        return self.parse_type()

    def parse_type(self) -> str:
        ch = self.peek()
        if ch in _V0_PRIMITIVES:
            self.pos += 1
            return _V0_PRIMITIVES[ch]
        tag = self.next_ch()
        if tag == "B":
            return self.parse_backref(self.parse_type)
        if tag == "A":
            elem = self.parse_type()
            ln = self.parse_const()
            return f"[{elem}; {ln}]"
        if tag == "S":
            elem = self.parse_type()
            return f"[{elem}]"
        if tag == "T":
            items: list[str] = []
            while not self.eat("E"):
                items.append(self.parse_type())
            if len(items) == 1:
                return f"({items[0]},)"
            return f"({', '.join(items)})"
        if tag == "R":
            lt = self.parse_lifetime()
            inner = self.parse_type()
            return f"&{lt} {inner}" if lt else f"&{inner}"
        if tag == "Q":
            lt = self.parse_lifetime()
            inner = self.parse_type()
            return f"&{lt} mut {inner}" if lt else f"&mut {inner}"
        if tag == "P":
            return f"*const {self.parse_type()}"
        if tag == "O":
            return f"*mut {self.parse_type()}"
        if tag == "F":
            self.parse_binder()
            is_unsafe = self.eat("U")
            abi = ""
            if self.eat("K"):
                if self.eat("C"):
                    abi = 'extern "C" '
                else:
                    abi_name = self.parse_ident()
                    abi = f'extern "{abi_name}" '
            params: list[str] = []
            while not self.eat("E"):
                params.append(self.parse_type())
            ret = self.parse_type()
            prefix = ("unsafe " if is_unsafe else "") + abi
            ret_str = "" if ret == "()" else f" -> {ret}"
            return f"{prefix}fn({', '.join(params)}){ret_str}"
        if tag == "D":
            self.parse_binder()
            traits: list[str] = []
            while not self.eat("E"):
                p = self.parse_path(in_value=False)
                assoc: list[str] = []
                while self.eat("p"):
                    aname = self.parse_ident()
                    aty = self.parse_type()
                    assoc.append(f"{aname} = {aty}")
                if assoc:
                    if p.endswith(">"):
                        p = p[:-1] + ", " + ", ".join(assoc) + ">"
                    else:
                        p = f"{p}<{', '.join(assoc)}>"
                traits.append(p)
            lt = self.parse_lifetime()
            body = " + ".join(traits) if traits else "_"
            if lt:
                body = f"{body} + {lt}"
            return f"dyn {body}"
        # Otherwise tag was start of a `<path>`! Rewind 1 char and parse_path(in_value=False)
        self.pos -= 1
        return self.parse_path(in_value=False)

    def parse_const(self) -> str:
        if self.eat("B"):
            return self.parse_backref(self.parse_const)
        if self.eat("p"):
            return "_"
        ty_ch = self.next_ch()
        neg = self.eat("n")
        start = self.pos
        while self.pos < len(self.s) and self.s[self.pos] != "_":
            self.pos += 1
        hex_digits = self.s[start : self.pos]
        self.eat("_")
        val = int(hex_digits, 16) if hex_digits else 0
        if neg:
            val = -val
        if ty_ch == "b":
            return "true" if val else "false"
        if ty_ch == "c":
            return repr(chr(val))
        return str(val)


def _decode_rust_punycode(raw: str) -> str:
    # Rust v0 punycode uses `_` instead of `-` as delimiter between ASCII and bootstring!
    sep = raw.rfind("_")
    if sep == -1:
        ascii_part = ""
        code = raw
    else:
        ascii_part = raw[:sep]
        code = raw[sep + 1 :]
    try:
        reconstructed = (ascii_part + "-" + code) if ascii_part else code
        return reconstructed.encode("ascii").decode("punycode")
    except Exception:  # noqa: BLE001
        return raw


_LEGACY_ESCAPES: tuple[tuple[str, str], ...] = (
    ("$SP$", "@"),
    ("$BP$", "*"),
    ("$RF$", "&"),
    ("$LT$", "<"),
    ("$GT$", ">"),
    ("$LP$", "("),
    ("$RP$", ")"),
    ("$C$", ","),
)
_LEGACY_UNICODE_RE = re.compile(r"\$u([0-9a-fA-F]{2,6})\$")
_LEGACY_HASH_RE = re.compile(r"^h[0-9a-f]{16}$")


def _demangle_legacy_zn(sym: str) -> str:
    # Strip `.llvm.<hex>` suffix if present
    base = sym.split(".llvm.", 1)[0]
    pos = 3 if base.startswith("_ZN") else 4  # `__ZN` on macOS
    parts: list[str] = []
    while pos < len(base):
        if base[pos] == "E":
            pos += 1
            break
        n_start = pos
        while pos < len(base) and base[pos].isdigit():
            pos += 1
        if n_start == pos:
            return sym
        ln = int(base[n_start:pos])
        if pos + ln > len(base):
            return sym
        seg = base[pos : pos + ln]
        pos += ln
        if seg.startswith("_$"):
            seg = seg[1:]
        seg = seg.replace("..", "::")
        for k, v in _LEGACY_ESCAPES:
            seg = seg.replace(k, v)
        seg = _LEGACY_UNICODE_RE.sub(lambda m: chr(int(m.group(1), 16)), seg)
        parts.append(seg)
    if parts and _LEGACY_HASH_RE.match(parts[-1]):
        parts.pop()
    return "::".join(parts) if parts else sym


def demangle_rust(sym: str) -> str:
    """Demangle Rust `_R` (v0) or `_ZN` (legacy) symbol into `{:#}` form (no crate hash).
    Unmangled C symbols pass through unchanged."""
    base = sym.split(".llvm.", 1)[0]
    if base.startswith("_R"):
        try:
            d = _V0Demangler(base)
            out = d.parse_path(in_value=True)
            # Optional vendor suffix (`.0`, `.llvm...`) or instantiating crate path
            return out
        except Exception:  # noqa: BLE001
            return sym
    if base.startswith("_ZN") or base.startswith("__ZN"):
        return _demangle_legacy_zn(sym)
    return sym


# ==============================================================================
# ELF64 Relocatable Object (`ET_REL` `.o`) & `.a` Archive Parsers
# ==============================================================================

@dataclass(frozen=True)
class RelocEntry:
    r_offset: int
    r_type: int
    sym_idx: int
    r_addend: int


@dataclass(frozen=True)
class RelSection:
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
    data: bytes
    relocs: tuple[RelocEntry, ...] = ()


@dataclass(frozen=True)
class RelSymbol:
    idx: int
    name: str
    demangled: str
    st_info: int
    st_other: int
    st_shndx: int
    st_value: int
    st_size: int
    bind: int
    stype: int

    @property
    def is_local(self) -> bool:
        return self.bind == STB_LOCAL

    @property
    def is_undefined(self) -> bool:
        return self.st_shndx == SHN_UNDEF

    @property
    def is_defined(self) -> bool:
        return self.st_shndx != SHN_UNDEF and self.stype != STT_FILE and self.stype != STT_SECTION

    @property
    def bind_name(self) -> str:
        return BIND_NAMES.get(self.bind, f"STB_{self.bind}")


@dataclass(frozen=True)
class RelocObject:
    label: str
    sha256: str
    size: int
    sections: tuple[RelSection, ...]
    symbols: tuple[RelSymbol, ...]
    sec_by_name: dict[str, list[RelSection]] = field(repr=False)
    defs_by_name: dict[str, list[RelSymbol]] = field(repr=False)
    undefs_by_name: dict[str, list[RelSymbol]] = field(repr=False)


def _read_cstr_checked(buf: bytes, off: int, ctx: str) -> str:
    if off < 0 or off >= len(buf):
        raise ValueError(f"{ctx}: string offset {off} out of bounds (len={len(buf)})")
    end = buf.find(b"\x00", off)
    if end == -1:
        raise ValueError(f"{ctx}: unterminated string at offset {off}")
    return buf[off:end].decode("utf-8", errors="replace")


def check_not_llvm_bitcode(data: bytes, label: str) -> None:
    for magic in LLVM_BITCODE_MAGICS:
        if data.startswith(magic):
            raise ValueError(f"Rule (iv) LTO violation: {label} is LLVM bitcode (magic {magic!r})")


def parse_reloc_obj(data: bytes, label: str) -> RelocObject:
    """Fail-closed parser for AArch64 ELF64 LE `ET_REL` `.o` objects (supporting `SHN_XINDEX`)."""
    check_not_llvm_bitcode(data, label)
    if len(data) < 64 or data[:4] != b"\x7fELF":
        raise ValueError(f"{label}: not a valid 64-byte ELF object")
    if data[4] != 2 or data[5] != 1:
        raise ValueError(f"{label}: expected ELF64 LE, got ei_class={data[4]}, ei_data={data[5]}")
    (
        e_type,
        e_machine,
        _e_ver,
        _e_entry,
        _e_phoff,
        e_shoff,
        _e_flags,
        _e_ehsize,
        _e_phentsize,
        _e_phnum,
        e_shentsize,
        e_shnum_raw,
        e_shstrndx_raw,
    ) = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    if e_type != ET_REL:
        raise ValueError(f"{label}: expected ET_REL (1), got e_type={e_type}")
    if e_machine != EM_AARCH64:
        raise ValueError(f"{label}: expected EM_AARCH64 (183), got e_machine={e_machine}")
    if e_shoff == 0 or e_shentsize != 64:
        raise ValueError(f"{label}: missing/malformed section header table (shoff={e_shoff}, shentsize={e_shentsize})")
    if e_shoff + 64 > len(data):
        raise ValueError(f"{label}: section header 0 out of bounds")

    sh0 = struct.unpack_from("<IIQQQQIIQQ", data, e_shoff)
    shnum = int(sh0[5]) if e_shnum_raw == 0 else int(e_shnum_raw)
    shstrndx = int(sh0[6]) if e_shstrndx_raw == SHN_XINDEX else int(e_shstrndx_raw)
    if shnum == 0 or e_shoff + shnum * 64 > len(data):
        raise ValueError(f"{label}: invalid shnum={shnum} for file size {len(data)}")
    if shstrndx == 0 or shstrndx >= shnum:
        raise ValueError(f"{label}: invalid shstrndx={shstrndx} (shnum={shnum})")

    raw_shdrs: list[tuple[int, int, int, int, int, int, int, int, int, int]] = []
    for i in range(shnum):
        raw_shdrs.append(struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * 64))

    shstr_hdr = raw_shdrs[shstrndx]
    if shstr_hdr[1] != SHT_STRTAB or shstr_hdr[4] + shstr_hdr[5] > len(data):
        raise ValueError(f"{label}: malformed .shstrtab at index {shstrndx}")
    shstrtab = data[shstr_hdr[4] : shstr_hdr[4] + shstr_hdr[5]]

    symtab_indices = [i for i, h in enumerate(raw_shdrs) if h[1] == SHT_SYMTAB]
    if len(symtab_indices) != 1:
        raise ValueError(f"{label}: expected exactly 1 SHT_SYMTAB, found {len(symtab_indices)}")
    symtab_idx = symtab_indices[0]
    sym_hdr = raw_shdrs[symtab_idx]
    if sym_hdr[9] != 24 or sym_hdr[5] % 24 != 0 or sym_hdr[4] + sym_hdr[5] > len(data):
        raise ValueError(f"{label}: malformed SHT_SYMTAB")
    strtab_idx = sym_hdr[6]
    if strtab_idx == 0 or strtab_idx >= shnum or raw_shdrs[strtab_idx][1] != SHT_STRTAB:
        raise ValueError(f"{label}: invalid SHT_SYMTAB strtab link {strtab_idx}")
    str_hdr = raw_shdrs[strtab_idx]
    if str_hdr[4] + str_hdr[5] > len(data):
        raise ValueError(f"{label}: strtab out of bounds")
    strtab = data[str_hdr[4] : str_hdr[4] + str_hdr[5]]

    # Optional SHT_SYMTAB_SHNDX table for >65,280 sections
    xindex_table: tuple[int, ...] | None = None
    for i, h in enumerate(raw_shdrs):
        if h[1] == SHT_SYMTAB_SHNDX and h[6] == symtab_idx:
            if h[4] + h[5] > len(data) or h[5] % 4 != 0:
                raise ValueError(f"{label}: malformed SHT_SYMTAB_SHNDX at {i}")
            cnt = h[5] // 4
            xindex_table = struct.unpack_from(f"<{cnt}I", data, h[4])
            break

    nsyms = sym_hdr[5] // 24
    if sym_hdr[7] > nsyms:
        raise ValueError(f"{label}: SHT_SYMTAB sh_info={sym_hdr[7]} > nsyms={nsyms}")
    if xindex_table is not None and len(xindex_table) != nsyms:
        raise ValueError(f"{label}: SHT_SYMTAB_SHNDX count {len(xindex_table)} != nsyms {nsyms}")

    symbols: list[RelSymbol] = []
    defs_by_name: dict[str, list[RelSymbol]] = {}
    undefs_by_name: dict[str, list[RelSymbol]] = {}
    for k in range(nsyms):
        st_name, st_info, st_other, st_shndx_raw, st_value, st_size = struct.unpack_from(
            "<IBBHQQ", data, sym_hdr[4] + k * 24
        )
        name = _read_cstr_checked(strtab, st_name, f"{label}.symtab[{k}]") if st_name != 0 else ""
        if st_shndx_raw == SHN_XINDEX:
            if xindex_table is None:
                raise ValueError(f"{label}: symbol {k} ({name!r}) uses SHN_XINDEX without SHT_SYMTAB_SHNDX")
            eff_shndx = int(xindex_table[k])
        else:
            eff_shndx = int(st_shndx_raw)
        bind = st_info >> 4
        stype = st_info & 0xF
        if k < sym_hdr[7] and bind != STB_LOCAL:
            raise ValueError(f"{label}: non-local symbol {name!r} at index {k} < sh_info={sym_hdr[7]}")
        if k >= sym_hdr[7] and bind == STB_LOCAL:
            raise ValueError(f"{label}: STB_LOCAL symbol {name!r} at index {k} >= sh_info={sym_hdr[7]}")
        sym_obj = RelSymbol(
            idx=k,
            name=name,
            demangled=demangle_rust(name) if name else "",
            st_info=st_info,
            st_other=st_other,
            st_shndx=eff_shndx,
            st_value=st_value,
            st_size=st_size,
            bind=bind,
            stype=stype,
        )
        symbols.append(sym_obj)
        if name and not sym_obj.is_local:
            if sym_obj.is_defined:
                defs_by_name.setdefault(name, []).append(sym_obj)
            elif sym_obj.is_undefined:
                undefs_by_name.setdefault(name, []).append(sym_obj)

    # Parse SHT_RELA per target section
    relocs_by_sec: dict[int, list[RelocEntry]] = {}
    for i, h in enumerate(raw_shdrs):
        if h[1] != SHT_RELA:
            continue
        if h[6] != symtab_idx:
            continue
        target_sec = h[7]
        if target_sec == 0 or target_sec >= shnum:
            raise ValueError(f"{label}: SHT_RELA[{i}] invalid target sh_info={target_sec}")
        if h[9] != 24 or h[5] % 24 != 0 or h[4] + h[5] > len(data):
            raise ValueError(f"{label}: malformed SHT_RELA[{i}]")
        nrel = h[5] // 24
        bucket = relocs_by_sec.setdefault(target_sec, [])
        for r_i in range(nrel):
            r_off, r_info, r_add = struct.unpack_from("<QQq", data, h[4] + r_i * 24)
            s_idx = r_info >> 32
            r_ty = r_info & 0xFFFFFFFF
            if s_idx >= nsyms:
                raise ValueError(f"{label}: SHT_RELA[{i}] sym_idx={s_idx} >= nsyms={nsyms}")
            bucket.append(RelocEntry(r_offset=r_off, r_type=r_ty, sym_idx=s_idx, r_addend=r_add))

    sections: list[RelSection] = []
    sec_by_name: dict[str, list[RelSection]] = {}
    for i, h in enumerate(raw_shdrs):
        sh_name, sh_type, sh_flags, sh_addr, sh_off, sh_sz, sh_link, sh_info, sh_align, sh_ent = h
        sname = _read_cstr_checked(shstrtab, sh_name, f"{label}.shdr[{i}]") if sh_name != 0 else ""
        if sh_type == SHT_NOBITS or sh_type == SHT_NULL or sh_sz == 0:
            sec_data = b""
        else:
            if sh_off + sh_sz > len(data):
                raise ValueError(f"{label}: section {i} ({sname!r}) data out of bounds")
            sec_data = data[sh_off : sh_off + sh_sz]
        sec_obj = RelSection(
            idx=i,
            name=sname,
            sh_type=sh_type,
            sh_flags=sh_flags,
            sh_addr=sh_addr,
            sh_offset=sh_off,
            sh_size=sh_sz,
            sh_link=sh_link,
            sh_info=sh_info,
            sh_addralign=sh_align,
            sh_entsize=sh_ent,
            data=sec_data,
            relocs=tuple(relocs_by_sec.get(i, ())),
        )
        sections.append(sec_obj)
        if sname:
            sec_by_name.setdefault(sname, []).append(sec_obj)

    return RelocObject(
        label=label,
        sha256=sha256_bytes(data),
        size=len(data),
        sections=tuple(sections),
        symbols=tuple(symbols),
        sec_by_name=sec_by_name,
        defs_by_name=defs_by_name,
        undefs_by_name=undefs_by_name,
    )


@dataclass(frozen=True)
class ArchiveMember:
    index: int
    name: str
    data: bytes
    sha256: str
    obj: RelocObject


@dataclass(frozen=True)
class ParsedArchive:
    label: str
    sha256: str
    size: int
    members: tuple[ArchiveMember, ...]
    members_by_name: dict[str, list[ArchiveMember]] = field(repr=False)


def parse_ar_archive(data: bytes, label: str, *, allow_rmeta: bool = False) -> ParsedArchive:
    """Fail-closed SVR4 / BSD `.a` (or `.rlib` when `allow_rmeta=True`) archive parser.
    Every non-index (and, when `allow_rmeta=True`, non-`.rmeta`) member MUST be an ELF64 `ET_REL`."""
    if data.startswith(b"!<thin>\n"):
        raise ValueError(f"{label}: thin archives (`!<thin>`) are forbidden; require standalone `.a`")
    if len(data) < 8 or data[:8] != b"!<arch>\n":
        raise ValueError(f"{label}: invalid archive magic")

    pos = 8
    ext_names: bytes = b""
    members: list[ArchiveMember] = []
    members_by_name: dict[str, list[ArchiveMember]] = {}
    m_idx = 0

    while pos < len(data):
        if pos + 60 > len(data):
            raise ValueError(f"{label}: truncated 60-byte ar member header at {pos}")
        hdr = data[pos : pos + 60]
        if hdr[58:60] != b"`\n":
            raise ValueError(f"{label}: invalid ar_fmag {hdr[58:60]!r} at {pos}")
        raw_name = hdr[0:16].decode("utf-8", errors="replace").rstrip(" ")
        size_str = hdr[48:58].decode("ascii", errors="strict").strip()
        m_size = int(size_str)
        body_start = pos + 60
        body_end = body_start + m_size
        if body_end > len(data):
            raise ValueError(f"{label}: ar member {raw_name!r} size {m_size} exceeds archive")
        payload = data[body_start:body_end]
        pos = body_end + (1 if (m_size & 1) else 0)

        # Skip SVR4/BSD symbol tables
        if raw_name in ("/", "/SYM64/", "__.SYMDEF", "__.SYMDEF SORTED"):
            continue
        if raw_name == "//":
            ext_names = payload
            continue

        if raw_name.startswith("#1/"):
            nlen = int(raw_name[3:])
            if nlen > len(payload):
                raise ValueError(f"{label}: BSD extended name length {nlen} > payload {len(payload)}")
            m_name = payload[:nlen].rstrip(b"\x00").decode("utf-8", errors="replace")
            payload = payload[nlen:]
        elif raw_name.startswith("/") and raw_name[1:].isdigit():
            off = int(raw_name[1:])
            if off >= len(ext_names):
                raise ValueError(f"{label}: GNU extended name offset {off} >= {len(ext_names)}")
            end_nl = ext_names.find(b"\n", off)
            raw_ext = ext_names[off:] if end_nl == -1 else ext_names[off:end_nl]
            m_name = raw_ext.rstrip(b"/\r\x00").decode("utf-8", errors="replace")
        else:
            m_name = raw_name.rstrip("/")

        m_label = f"{label}({m_name})"
        check_not_llvm_bitcode(payload, m_label)
        if allow_rmeta and (m_name == "lib.rmeta" or m_name.endswith(".rmeta")):
            continue
        obj = parse_reloc_obj(payload, m_label)
        mem = ArchiveMember(
            index=m_idx,
            name=m_name,
            data=payload,
            sha256=obj.sha256,
            obj=obj,
        )
        members.append(mem)
        members_by_name.setdefault(m_name, []).append(mem)
        m_idx += 1

    return ParsedArchive(
        label=label,
        sha256=sha256_bytes(data),
        size=len(data),
        members=tuple(members),
        members_by_name=members_by_name,
    )


def parse_rlib_archive(data: bytes, label: str) -> ParsedArchive:
    """Fail-closed parser for Rust `.rlib` archives (skips `.rmeta`, rejects bitcode/non-ELF members)."""
    return parse_ar_archive(data, label, allow_rmeta=True)


def scan_rlib_defined_symbols_fast(
    data: bytes,
    label: str,
    target_names: set[str],
) -> dict[str, list[tuple[str, str]]]:
    """Scan a `.rlib` archive for exact non-local defined symbol names in `target_names`.

    Uses NUL-terminated `.strtab` byte pre-filtering (`sym_utf8 + b"\\x00" in payload`, 0% false
    negatives even under `.strtab` suffix merging) so scanning all ~80 toolchain `.rlib` archives
    takes < 0.1s while remaining 100% sound. Returns `{sym: [(member_name, member_sha256), ...]}`.
    """
    if not target_names:
        return {}
    if data.startswith(b"!<thin>\n"):
        raise ValueError(f"{label}: thin archives (`!<thin>`) are forbidden")
    if len(data) < 8 or data[:8] != b"!<arch>\n":
        raise ValueError(f"{label}: invalid archive magic")

    nul_pats = [name.encode("utf-8") + b"\x00" for name in sorted(target_names)]
    pos = 8
    ext_names: bytes = b""
    hits: dict[str, list[tuple[str, str]]] = {}

    while pos < len(data):
        if pos + 60 > len(data):
            raise ValueError(f"{label}: truncated 60-byte ar member header at {pos}")
        hdr = data[pos : pos + 60]
        if hdr[58:60] != b"`\n":
            raise ValueError(f"{label}: invalid ar_fmag {hdr[58:60]!r} at {pos}")
        raw_name = hdr[0:16].decode("utf-8", errors="replace").rstrip(" ")
        m_size = int(hdr[48:58].decode("ascii", errors="strict").strip())
        body_start = pos + 60
        body_end = body_start + m_size
        if body_end > len(data):
            raise ValueError(f"{label}: ar member {raw_name!r} size {m_size} exceeds archive")
        payload = data[body_start:body_end]
        pos = body_end + (1 if (m_size & 1) else 0)

        if raw_name in ("/", "/SYM64/", "__.SYMDEF", "__.SYMDEF SORTED"):
            continue
        if raw_name == "//":
            ext_names = payload
            continue

        if raw_name.startswith("#1/"):
            nlen = int(raw_name[3:])
            m_name = payload[:nlen].rstrip(b"\x00").decode("utf-8", errors="replace")
            payload = payload[nlen:]
        elif raw_name.startswith("/") and raw_name[1:].isdigit():
            off = int(raw_name[1:])
            end_nl = ext_names.find(b"\n", off)
            raw_ext = ext_names[off:] if end_nl == -1 else ext_names[off:end_nl]
            m_name = raw_ext.rstrip(b"/\r\x00").decode("utf-8", errors="replace")
        else:
            m_name = raw_name.rstrip("/")

        if m_name == "lib.rmeta" or m_name.endswith(".rmeta"):
            continue
        check_not_llvm_bitcode(payload, f"{label}({m_name})")
        if not any(pat in payload for pat in nul_pats):
            continue
        obj = parse_reloc_obj(payload, f"{label}({m_name})")
        for tname in target_names:
            if tname in obj.defs_by_name:
                hits.setdefault(tname, []).append((m_name, obj.sha256))
    return hits


def extract_reloc_section_subset(
    member_bytes: bytes,
    keep_sections: Sequence[str],
    label: str = "<member>",
) -> bytes:
    """Deterministic canonical ELF64 AArch64 `ET_REL` section-subset extractor (`recipe = 'elf_trim'`).

    Mirrors `arm64-semantics/tools/snapshot-link/src/trimmed.rs`:
      - keeps ONLY the sections listed in `keep_sections` (in member section order), rejecting
        `SHF_GROUP` (`0x200`) / `SHF_LINK_ORDER` (`0x80`) or missing/duplicate kept section names;
      - preserves every symbol (local and non-local) in kept sections verbatim (name, bind, type,
        visibility, offset, size) — never renames or adds any symbol;
      - converts non-local symbols defined in dropped sections that are referenced by kept relocations
        into `SHN_UNDEF` symbols, while failing closed if a kept relocation targets a local symbol in
        a dropped section.
    """
    src = parse_reloc_obj(member_bytes, label)
    req_list = [str(s) for s in keep_sections]
    if not req_list or len(set(req_list)) != len(req_list):
        raise ValueError(f"{label}: keep_sections must be a non-empty deduplicated list, got {req_list!r}")

    req_set = set(req_list)
    kept_old_secs: list[RelSection] = []
    for sec in src.sections:
        if sec.idx == 0 or sec.name not in req_set:
            continue
        if (sec.sh_flags & 0x280) != 0:  # SHF_GROUP (0x200) | SHF_LINK_ORDER (0x80)
            raise ValueError(f"{label}: kept section {sec.name!r} has forbidden SHF_GROUP/SHF_LINK_ORDER")
        kept_old_secs.append(sec)

    found_names = [s.name for s in kept_old_secs]
    if set(found_names) != req_set or len(found_names) != len(req_list):
        raise ValueError(
            f"{label}: keep_sections {req_list} not uniquely matched in member (found {found_names})"
        )

    old_to_new_shndx: dict[int, int] = {sec.idx: new_i for new_i, sec in enumerate(kept_old_secs, start=1)}

    def _add_str(buf: bytearray, offsets: dict[str, int], s: str) -> int:
        if not s:
            return 0
        if s in offsets:
            return offsets[s]
        off = len(buf)
        buf.extend(s.encode("utf-8") + b"\x00")
        offsets[s] = off
        return off

    shstr_buf = bytearray(b"\x00")
    shstr_offs: dict[str, int] = {"": 0}
    strtab_buf = bytearray(b"\x00")
    strtab_offs: dict[str, int] = {"": 0}

    referenced_old_sym_idxs: set[int] = set()
    for sec in kept_old_secs:
        for rel in sec.relocs:
            if rel.r_type not in R_AARCH64_NONE_SET:
                referenced_old_sym_idxs.add(rel.sym_idx)

    # Build symbol table: 0 = null, then kept locals (section symbols + local defs), then non-locals
    local_entries: list[tuple[int, int, int, int, int, int]] = [(0, 0, 0, 0, 0, 0)]
    nonlocal_entries: list[tuple[int, int, int, int, int, int]] = []
    old_to_new_sym_local: dict[int, int] = {0: 0}
    pending_nonlocals: list[tuple[int, tuple[int, int, int, int, int, int]]] = []

    # Ensure every kept section has a `STT_SECTION` local symbol for section-relative relocations
    sec_sym_new_idx: dict[int, int] = {}
    for old_sidx, new_sidx in sorted(old_to_new_shndx.items()):
        st_info = (STB_LOCAL << 4) | STT_SECTION
        new_sym_i = len(local_entries)
        local_entries.append((0, st_info, 0, new_sidx, 0, 0))
        sec_sym_new_idx[old_sidx] = new_sym_i

    for sym in src.symbols[1:]:
        if sym.st_shndx in old_to_new_shndx:
            new_shndx = old_to_new_shndx[sym.st_shndx]
            if sym.is_local and sym.stype == STT_SECTION:
                old_to_new_sym_local[sym.idx] = sec_sym_new_idx[sym.st_shndx]
                continue
            noff = _add_str(strtab_buf, strtab_offs, sym.name)
            st_info = (sym.bind << 4) | (sym.stype & 0xF)
            tup = (noff, st_info, sym.st_other, new_shndx, sym.st_value, sym.st_size)
            if sym.is_local:
                old_to_new_sym_local[sym.idx] = len(local_entries)
                local_entries.append(tup)
            else:
                pending_nonlocals.append((sym.idx, tup))
        elif sym.st_shndx in (SHN_ABS, SHN_COMMON) and (not sym.is_local or sym.idx in referenced_old_sym_idxs):
            noff = _add_str(strtab_buf, strtab_offs, sym.name)
            st_info = (sym.bind << 4) | (sym.stype & 0xF)
            tup = (noff, st_info, sym.st_other, sym.st_shndx, sym.st_value, sym.st_size)
            if sym.is_local:
                old_to_new_sym_local[sym.idx] = len(local_entries)
                local_entries.append(tup)
            else:
                pending_nonlocals.append((sym.idx, tup))
        elif sym.idx in referenced_old_sym_idxs:
            if sym.is_local:
                raise ValueError(
                    f"{label}: kept relocation references local symbol {sym.name!r} in dropped section shndx={sym.st_shndx}"
                )
            noff = _add_str(strtab_buf, strtab_offs, sym.name)
            # Dropped-section global/weak definition becomes `SHN_UNDEF` (matching `trimmed.rs`)
            undef_stype = sym.stype if sym.is_undefined else STT_NOTYPE
            st_info = (sym.bind << 4) | (undef_stype & 0xF)
            pending_nonlocals.append((sym.idx, (noff, st_info, 0, SHN_UNDEF, 0, 0)))

    first_nonlocal = len(local_entries)
    old_to_new_sym: dict[int, int] = dict(old_to_new_sym_local)
    for old_i, tup in pending_nonlocals:
        old_to_new_sym[old_i] = first_nonlocal + len(nonlocal_entries)
        nonlocal_entries.append(tup)

    symtab_bytes = b"".join(
        struct.pack("<IBBHQQ", a, b, c, d, e, f) for a, b, c, d, e, f in (local_entries + nonlocal_entries)
    )

    rela_blobs: list[tuple[int, str, bytes]] = []
    for sec in kept_old_secs:
        active_rels = [r for r in sec.relocs if r.r_type not in R_AARCH64_NONE_SET]
        if not active_rels:
            continue
        new_t_sec = old_to_new_shndx[sec.idx]
        entries = []
        for r in active_rels:
            nsym = old_to_new_sym[r.sym_idx]
            r_info = (nsym << 32) | (r.r_type & 0xFFFFFFFF)
            entries.append(struct.pack("<QQq", r.r_offset, r_info, r.r_addend))
        rela_blobs.append((new_t_sec, f".rela{sec.name}", b"".join(entries)))

    symtab_shndx = 1 + len(kept_old_secs) + len(rela_blobs)
    strtab_shndx = symtab_shndx + 1
    shstrtab_shndx = strtab_shndx + 1
    total_shnum = shstrtab_shndx + 1

    sec_noffs = [_add_str(shstr_buf, shstr_offs, s.name) for s in kept_old_secs]
    rela_noffs = [_add_str(shstr_buf, shstr_offs, rn) for _, rn, _ in rela_blobs]
    sym_noff = _add_str(shstr_buf, shstr_offs, ".symtab")
    str_noff = _add_str(shstr_buf, shstr_offs, ".strtab")
    shstr_noff = _add_str(shstr_buf, shstr_offs, ".shstrtab")

    body = bytearray(64)
    shdrs: list[bytes] = [b"\x00" * 64]

    def _append_aligned(blob: bytes, align: int = 8) -> int:
        if align > 1 and (len(body) % align) != 0:
            body.extend(b"\x00" * (align - (len(body) % align)))
        off = len(body)
        body.extend(blob)
        return off

    for sec, noff in zip(kept_old_secs, sec_noffs):
        align = max(1, int(sec.sh_addralign))
        if sec.sh_type == SHT_NOBITS:
            d_off = len(body)
            d_sz = sec.sh_size
        else:
            d_off = _append_aligned(sec.data, align)
            d_sz = len(sec.data)
        shdrs.append(
            struct.pack(
                "<IIQQQQIIQQ",
                noff,
                sec.sh_type,
                sec.sh_flags,
                sec.sh_addr,
                d_off,
                d_sz,
                0,
                0,
                align,
                sec.sh_entsize,
            )
        )

    for (t_sec_idx, _rn, rbytes), rnoff in zip(rela_blobs, rela_noffs):
        r_off = _append_aligned(rbytes, 8)
        shdrs.append(
            struct.pack(
                "<IIQQQQIIQQ",
                rnoff,
                SHT_RELA,
                0,
                0,
                r_off,
                len(rbytes),
                symtab_shndx,
                t_sec_idx,
                8,
                24,
            )
        )

    sym_off = _append_aligned(symtab_bytes, 8)
    shdrs.append(
        struct.pack(
            "<IIQQQQIIQQ",
            sym_noff,
            SHT_SYMTAB,
            0,
            0,
            sym_off,
            len(symtab_bytes),
            strtab_shndx,
            first_nonlocal,
            8,
            24,
        )
    )
    str_off = _append_aligned(bytes(strtab_buf), 1)
    shdrs.append(
        struct.pack("<IIQQQQIIQQ", str_noff, SHT_STRTAB, 0, 0, str_off, len(strtab_buf), 0, 0, 1, 0)
    )
    shstr_off = _append_aligned(bytes(shstr_buf), 1)
    shdrs.append(
        struct.pack("<IIQQQQIIQQ", shstr_noff, SHT_STRTAB, 0, 0, shstr_off, len(shstr_buf), 0, 0, 1, 0)
    )

    e_shoff = _append_aligned(b"".join(shdrs), 8)
    e_ident = b"\x7fELF\x02\x01\x01" + b"\x00" * 9
    body[:64] = struct.pack(
        "<16sHHIQQQIHHHHHH",
        e_ident,
        ET_REL,
        EM_AARCH64,
        1,
        0,
        0,
        e_shoff,
        0,
        64,
        0,
        0,
        64,
        total_shnum,
        shstrtab_shndx,
    )
    return bytes(body)


def _resolve_pinned_llvm_objcopy(
    toolchain_sysroot: pathlib.Path | None = None,
    repo_root: pathlib.Path | None = None,
) -> str:
    import shutil
    import subprocess

    cands: list[pathlib.Path] = []
    sr = toolchain_sysroot
    if sr is None:
        try:
            r = subprocess.run(
                ["rustc", "--print", "sysroot"],
                cwd=str(repo_root) if repo_root and repo_root.is_dir() else None,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            if r.returncode == 0 and r.stdout.strip():
                sr = pathlib.Path(r.stdout.strip())
        except Exception:  # noqa: BLE001
            pass
    if sr is not None and sr.is_dir():
        for bin_dir in sorted((sr / "lib/rustlib").glob("*/bin")):
            for bname in ("llvm-objcopy", "rust-objcopy"):
                if (bin_dir / bname).is_file():
                    cands.append(bin_dir / bname)
    for p in cands:
        return str(p)
    for fallback in ("llvm-objcopy", "rust-objcopy", "objcopy"):
        found = shutil.which(fallback)
        if found:
            return found
    raise FileNotFoundError("cannot locate `llvm-objcopy` / `rust-objcopy` for kind (a) re-derivation")


def rederive_rlib_subset_object(
    member_bytes: bytes,
    keep_sections: Sequence[str],
    recipe: str,
    *,
    label: str = "<member>",
    repo_root: pathlib.Path | None = None,
    toolchain_sysroot: pathlib.Path | None = None,
) -> bytes:
    """Re-derive the WHOLE kind-(a) `rust_extracted` `.o` from `member_bytes` + `keep_sections` + `recipe`
    so the checker compares its SHA-256 directly against `lock.rust_extracted[name].sha256` (GK 466 N-b/N-c)."""
    import subprocess
    import tempfile

    norm_recipe = recipe.strip()
    if not keep_sections:
        raise ValueError(f"{label}: kind (a) `keep_sections` must be non-empty")

    if norm_recipe == "elf_trim":
        return extract_reloc_section_subset(member_bytes, keep_sections, label=label)

    if norm_recipe == "copy":
        parsed_m = parse_reloc_obj(member_bytes, label)
        alloc_secs = {
            s.name for s in parsed_m.sections if (s.sh_flags & SHF_ALLOC) != 0 and s.sh_type != SHT_NULL
        }
        if alloc_secs != set(keep_sections):
            raise ValueError(
                f"{label}: recipe='copy' is invalid when keep_sections {sorted(set(keep_sections))} "
                f"!= member SHF_ALLOC sections {sorted(alloc_secs)}"
            )
        return member_bytes

    if norm_recipe in ("llvm-objcopy", "llvm-objcopy --strip-debug", "rust-objcopy"):
        objcopy_bin = _resolve_pinned_llvm_objcopy(toolchain_sysroot=toolchain_sysroot, repo_root=repo_root)
        cmd = [objcopy_bin]
        if "--strip-debug" in norm_recipe:
            cmd.append("--strip-debug")
        for ks in keep_sections:
            cmd.append(f"--only-section={ks}")
        with tempfile.TemporaryDirectory() as td:
            in_p = pathlib.Path(td) / "member.o"
            out_p = pathlib.Path(td) / "extracted.o"
            in_p.write_bytes(member_bytes)
            proc = subprocess.run([*cmd, str(in_p), str(out_p)], capture_output=True, text=True, timeout=15, check=False)
            if proc.returncode != 0 or not out_p.is_file():
                raise RuntimeError(
                    f"{label}: `{norm_recipe}` failed (rc={proc.returncode}): {proc.stderr.strip()}"
                )
            return out_p.read_bytes()

    raise ValueError(
        f"{label}: unsupported kind (a) extraction recipe {recipe!r}; expected "
        "'elf_trim', 'llvm-objcopy', 'llvm-objcopy --strip-debug', or 'copy'"
    )


_RDLS_RUSTC_SHIM_RE = re.compile(
    r"^_RNvCs[0-9A-Za-z_]+_7___rustc("
    r"12___rust_alloc|"
    r"14___rust_dealloc|"
    r"14___rust_realloc|"
    r"19___rust_alloc_zeroed|"
    r"35___rust_no_alloc_shim_is_unstable_v2"
    r")$"
)


def extract_rustc_comments(obj: RelocObject) -> list[str]:
    """Return any `.comment` producer strings mentioning `rustc` in `obj` (SR-31 A2)."""
    hits: list[str] = []
    for sec in obj.sections:
        if sec.name == ".comment" or sec.name.startswith(".comment."):
            for raw_part in sec.data.split(b"\x00"):
                if b"rustc" in raw_part.lower():
                    hits.append(raw_part.decode("utf-8", errors="replace").strip())
    return hits


_RUST_LEGACY_HASH_RE = re.compile(r"^_?_ZN.+17h[0-9a-f]{16}E$")


def is_rust_mangled_symbol(sym_name: str) -> bool:
    """True iff `sym_name` uses `_R` (v0) or `_ZN`/`__ZN` mangling (strict `.o` check, §0f(iv))."""
    base = sym_name.split(".llvm.", 1)[0]
    return base.startswith("_R") or base.startswith("_ZN") or base.startswith("__ZN")


def is_strict_rust_symbol(sym_name: str) -> bool:
    """True iff `sym_name` uses Rust `_R` (v0) or Rust legacy `_ZN...17h<16hex>E` mangling
    (distinguishing Rust symbols from LLVM C++ Itanium `_ZN9libunwind...` in `libunwind.a`)."""
    base = sym_name.split(".llvm.", 1)[0]
    return base.startswith("_R") or bool(_RUST_LEGACY_HASH_RE.match(base))


def is_rdl_shim_rustc_alloc_symbol(sym_name: str) -> bool:
    """True iff `sym_name` is one of the 5 `___rustc::___rust_*` global-allocator shim entrypoints."""
    return bool(_RDLS_RUSTC_SHIM_RE.match(sym_name))


# ==============================================================================
# ELF64 Executable (`ET_EXEC`) Parser
# ==============================================================================

@dataclass(frozen=True)
class ExecSegment:
    vaddr: int
    memsz: int
    filesz: int
    flags: int
    data: bytes  # length == memsz (file-backed prefix + zero-filled BSS tail)

    @property
    def end(self) -> int:
        return self.vaddr + self.memsz


@dataclass(frozen=True)
class ExecSection:
    idx: int
    name: str
    sh_type: int
    sh_flags: int
    sh_addr: int
    sh_offset: int
    sh_size: int
    sh_link: int
    sh_info: int
    sh_entsize: int


@dataclass(frozen=True)
class ExecSymbol:
    idx: int
    name: str
    demangled: str
    st_info: int
    st_other: int
    st_shndx: int
    st_value: int
    st_size: int
    bind: int
    stype: int

    @property
    def is_local(self) -> bool:
        return self.bind == STB_LOCAL

    @property
    def is_undefined(self) -> bool:
        return self.st_shndx == SHN_UNDEF


@dataclass(frozen=True)
class ExecElf:
    label: str
    sha256: str
    size: int
    entry: int
    segments: tuple[ExecSegment, ...]
    sections: tuple[ExecSection, ...]
    symbols: tuple[ExecSymbol, ...]
    loader_symbols: dict[str, list[ExecSymbol]] = field(repr=False)
    nonlocal_defs: dict[str, list[ExecSymbol]] = field(repr=False)
    all_defs_by_name: dict[str, list[ExecSymbol]] = field(repr=False)
    undef_symbols: tuple[ExecSymbol, ...] = ()

    def read_vma(self, addr: int, length: int) -> bytes:
        if length == 0:
            return b""
        for seg in self.segments:
            if seg.vaddr <= addr and addr + length <= seg.end:
                off = addr - seg.vaddr
                return seg.data[off : off + length]
        raise ValueError(f"{self.label}: VMA range [{addr:#x}, {addr + length:#x}) not covered by any PT_LOAD")


def parse_exec_elf(data: bytes, label: str) -> ExecElf:
    """Fail-closed parser for linked static AArch64 `ET_EXEC` ELF binaries."""
    if len(data) < 64 or data[:4] != b"\x7fELF":
        raise ValueError(f"{label}: invalid ELF magic")
    if data[4] != 2 or data[5] != 1:
        raise ValueError(f"{label}: expected ELF64 LE")
    (
        e_type,
        e_machine,
        _e_ver,
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
    ) = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    if e_type != ET_EXEC:
        raise ValueError(f"{label}: expected ET_EXEC (2), got e_type={e_type} (PIE/shared forbidden)")
    if e_machine != EM_AARCH64:
        raise ValueError(f"{label}: expected EM_AARCH64 (183), got {e_machine}")
    if e_phentsize != 56 or e_phnum == 0 or e_phoff + e_phnum * 56 > len(data):
        raise ValueError(f"{label}: malformed PHDR table")
    if e_shoff == 0 or e_shnum == 0 or e_shentsize != 64 or e_shoff + e_shnum * 64 > len(data):
        raise ValueError(f"{label}: missing or malformed section header table")
    if e_shstrndx == 0 or e_shstrndx >= e_shnum:
        raise ValueError(f"{label}: invalid e_shstrndx={e_shstrndx}")

    segments: list[ExecSegment] = []
    for i in range(e_phnum):
        p_type, p_flags, p_offset, p_vaddr, _p_paddr, p_filesz, p_memsz, _p_align = struct.unpack_from(
            "<IIQQQQQQ", data, e_phoff + i * 56
        )
        if p_type == 3:  # PT_INTERP
            raise ValueError(f"{label}: dynamic PT_INTERP segment forbidden in static stock ELF")
        if p_type != 1 or p_memsz == 0:
            continue
        if (p_flags & 0x1) and (p_flags & 0x2):
            raise ValueError(f"{label}: PT_LOAD[{i}] violates W^X (flags={p_flags:#x})")
        if p_filesz > p_memsz or p_offset + p_filesz > len(data):
            raise ValueError(f"{label}: PT_LOAD[{i}] file bounds invalid")
        seg_bytes = data[p_offset : p_offset + p_filesz] + b"\x00" * (p_memsz - p_filesz)
        segments.append(
            ExecSegment(vaddr=p_vaddr, memsz=p_memsz, filesz=p_filesz, flags=p_flags, data=seg_bytes)
        )
    segments.sort(key=lambda s: s.vaddr)

    raw_shdrs = [struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * 64) for i in range(e_shnum)]
    shstr_hdr = raw_shdrs[e_shstrndx]
    if shstr_hdr[1] != SHT_STRTAB or shstr_hdr[4] + shstr_hdr[5] > len(data):
        raise ValueError(f"{label}: invalid .shstrtab")
    shstrtab = data[shstr_hdr[4] : shstr_hdr[4] + shstr_hdr[5]]

    sections: list[ExecSection] = []
    symtab_idxs: list[int] = []
    for i, h in enumerate(raw_shdrs):
        sname = _read_cstr_checked(shstrtab, h[0], f"{label}.shdr[{i}]") if h[0] != 0 else ""
        sections.append(
            ExecSection(
                idx=i,
                name=sname,
                sh_type=h[1],
                sh_flags=h[2],
                sh_addr=h[3],
                sh_offset=h[4],
                sh_size=h[5],
                sh_link=h[6],
                sh_info=h[7],
                sh_entsize=h[9],
            )
        )
        if h[1] == SHT_SYMTAB:
            symtab_idxs.append(i)
        if h[1] in (4, 9) and (h[2] & SHF_ALLOC):  # SHF_ALLOC SHT_RELA / SHT_REL (dynamic relocs)
            raise ValueError(f"{label}: dynamic relocation section {sname!r} forbidden in static ELF")

    if len(symtab_idxs) != 1:
        raise ValueError(f"{label}: expected exactly 1 SHT_SYMTAB, found {len(symtab_idxs)}")
    sym_sec = sections[symtab_idxs[0]]
    if sym_sec.sh_entsize != 24 or sym_sec.sh_size % 24 != 0 or sym_sec.sh_offset + sym_sec.sh_size > len(data):
        raise ValueError(f"{label}: malformed .symtab")
    if sym_sec.sh_link == 0 or sym_sec.sh_link >= len(sections):
        raise ValueError(f"{label}: invalid .symtab sh_link")
    str_sec = sections[sym_sec.sh_link]
    if str_sec.sh_type != SHT_STRTAB or str_sec.sh_offset + str_sec.sh_size > len(data):
        raise ValueError(f"{label}: malformed .strtab")
    strtab = data[str_sec.sh_offset : str_sec.sh_offset + str_sec.sh_size]

    nsyms = sym_sec.sh_size // 24
    if sym_sec.sh_info > nsyms:
        raise ValueError(f"{label}: .symtab sh_info={sym_sec.sh_info} > nsyms={nsyms}")

    symbols: list[ExecSymbol] = []
    loader_symbols: dict[str, list[ExecSymbol]] = {}
    nonlocal_defs: dict[str, list[ExecSymbol]] = {}
    all_defs_by_name: dict[str, list[ExecSymbol]] = {}
    undef_symbols: list[ExecSymbol] = []

    for k in range(nsyms):
        st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
            "<IBBHQQ", data, sym_sec.sh_offset + k * 24
        )
        name = _read_cstr_checked(strtab, st_name, f"{label}.symtab[{k}]") if st_name != 0 else ""
        bind = st_info >> 4
        stype = st_info & 0xF
        is_local = (k < sym_sec.sh_info) or (bind == STB_LOCAL)
        if k < sym_sec.sh_info and bind != STB_LOCAL:
            raise ValueError(f"{label}: non-local symbol {name!r} at {k} < sh_info={sym_sec.sh_info}")
        if k >= sym_sec.sh_info and bind == STB_LOCAL:
            raise ValueError(f"{label}: STB_LOCAL symbol {name!r} at {k} >= sh_info={sym_sec.sh_info}")
        esym = ExecSymbol(
            idx=k,
            name=name,
            demangled=demangle_rust(name) if name else "",
            st_info=st_info,
            st_other=st_other,
            st_shndx=st_shndx,
            st_value=st_value,
            st_size=st_size,
            bind=bind,
            stype=stype,
        )
        symbols.append(esym)
        if st_shndx == SHN_UNDEF:
            if k > 0 and (name or not is_local):
                undef_symbols.append(esym)
        elif stype not in (STT_FILE, STT_SECTION) and st_name != 0:
            all_defs_by_name.setdefault(name, []).append(esym)
            if not is_local:
                nonlocal_defs.setdefault(name, []).append(esym)
                if stype == STT_FUNC:
                    loader_symbols.setdefault(name, []).append(esym)

    return ExecElf(
        label=label,
        sha256=sha256_bytes(data),
        size=len(data),
        entry=e_entry,
        segments=tuple(segments),
        sections=tuple(sections),
        symbols=tuple(symbols),
        loader_symbols=loader_symbols,
        nonlocal_defs=nonlocal_defs,
        all_defs_by_name=all_defs_by_name,
        undef_symbols=tuple(undef_symbols),
    )


# ==============================================================================
# `ld.lld` `-Map`, `--why-extract`, and `--trace-symbol` Parsers
# ==============================================================================

@dataclass(frozen=True)
class MapSymbol:
    name: str
    demangled: str
    vma: int
    lma: int
    size: int
    align: int


@dataclass
class MapInputSection:
    out_sec: str
    input_raw: str
    archive_path: str | None
    archive_member: str | None
    sec_name: str
    piece_offset: int | None
    vma: int
    lma: int
    size: int
    align: int
    symbols: list[MapSymbol] = field(default_factory=list)


@dataclass(frozen=True)
class ParsedLldMap:
    input_sections: tuple[MapInputSection, ...]
    sections_by_sym: dict[str, list[tuple[MapInputSection, MapSymbol]]]
    retained_by_input: dict[str, set[str]]


def split_lld_input_section(item: str) -> tuple[str, str, int | None] | None:
    if ":(" not in item or not item.endswith(")"):
        return None
    inp, sec_raw = item.split(":(", 1)
    sec_raw = sec_raw[:-1]
    piece_off: int | None = None
    if "+0x" in sec_raw:
        sec_base, off_hex = sec_raw.split("+0x", 1)
        try:
            piece_off = int(off_hex, 16)
            sec_raw = sec_base
        except ValueError:
            pass
    return inp, sec_raw, piece_off


def split_archive_member_spec(input_raw: str) -> tuple[str | None, str | None]:
    """Parse `<path_to_archive.a>(<member>)` -> `(archive_path, member)` or `(None, None)`."""
    if input_raw.endswith(")") and ".a(" in input_raw:
        idx = input_raw.rfind(".a(")
        arch_path = input_raw[: idx + 2]
        mem_name = input_raw[idx + 3 : -1]
        return arch_path, mem_name
    return None, None


def parse_lld_map(map_text: str, label: str = "link.map") -> ParsedLldMap:
    """Fail-closed parser for `ld.lld -Map` matching `stock_std_audit.rs` fixed-width rules."""
    lines = map_text.splitlines()
    if not lines or lines[0] != MAP_HEADER:
        raise ValueError(f"{label}: unrecognized header (expected {MAP_HEADER!r})")

    current_out_sec = ""
    current_in_sec: MapInputSection | None = None
    input_sections: list[MapInputSection] = []
    sections_by_sym: dict[str, list[tuple[MapInputSection, MapSymbol]]] = {}
    retained_by_input: dict[str, set[str]] = {}

    for line_idx, line in enumerate(lines[1:], start=2):
        if len(line) < MAP_COLS or line[MAP_COLS - 1] != " ":
            raise ValueError(f"{label}:{line_idx}: malformed column prefix: {line!r}")
        cols = line[:MAP_COLS].split()
        if len(cols) != 4:
            raise ValueError(f"{label}:{line_idx}: expected 4 numeric columns, got {cols!r}")
        try:
            vma = int(cols[0], 16)
            lma = int(cols[1], 16)
            sz = int(cols[2], 16)
            align = int(cols[3], 10)
        except ValueError as exc:
            raise ValueError(f"{label}:{line_idx}: bad numeric column in {cols!r}") from exc

        rest = line[MAP_COLS:]
        indent = len(rest) - len(rest.lstrip(" "))
        item = rest[indent:]
        if not item:
            raise ValueError(f"{label}:{line_idx}: empty item column")

        if indent == 0:
            # Output section header vs linker-script assignment (`.` / `PROVIDE` / `=`)
            if " = " not in item and not item.startswith(("PROVIDE(", "ASSERT(")):
                current_out_sec = item.strip()
            current_in_sec = None
        elif indent == 8:
            parsed_in = split_lld_input_section(item)
            if parsed_in is not None:
                inp_raw, sec_name, piece_off = parsed_in
                arch_p, arch_m = split_archive_member_spec(inp_raw)
                current_in_sec = MapInputSection(
                    out_sec=current_out_sec,
                    input_raw=inp_raw,
                    archive_path=arch_p,
                    archive_member=arch_m,
                    sec_name=sec_name,
                    piece_offset=piece_off,
                    vma=vma,
                    lma=lma,
                    size=sz,
                    align=align,
                )
                input_sections.append(current_in_sec)
                retained_by_input.setdefault(inp_raw, set()).add(sec_name)
            else:
                # Linker-script synthetic command inside output section (e.g. `. = ALIGN(...)`, `BYTE(...)`)
                current_in_sec = None
        elif indent == 16:
            msym = MapSymbol(
                name=item,
                demangled=demangle_rust(item),
                vma=vma,
                lma=lma,
                size=sz,
                align=align,
            )
            if current_in_sec is not None:
                current_in_sec.symbols.append(msym)
                sections_by_sym.setdefault(item, []).append((current_in_sec, msym))
        else:
            raise ValueError(f"{label}:{line_idx}: unexpected indent {indent} in {line!r}")

    if not input_sections:
        raise ValueError(f"{label}: zero retained input sections parsed")

    return ParsedLldMap(
        input_sections=tuple(input_sections),
        sections_by_sym=sections_by_sym,
        retained_by_input=retained_by_input,
    )


def parse_why_extract(why_text: str, label: str = "why-extract.tsv") -> list[tuple[str, str, str]]:
    """Fail-closed parser for `ld.lld --why-extract` (`reference<TAB>extracted<TAB>symbol`)."""
    lines = why_text.splitlines()
    if not lines or lines[0] != WHY_HEADER:
        raise ValueError(f"{label}: unrecognized header (expected {WHY_HEADER!r})")
    rows: list[tuple[str, str, str]] = []
    for idx, line in enumerate(lines[1:], start=2):
        parts = line.split("\t")
        if len(parts) != 3 or not all(parts) or not parts[1].endswith(")"):
            raise ValueError(f"{label}:{idx}: malformed row {line!r}")
        rows.append((parts[0], parts[1], parts[2]))
    return rows


_TRACE_DEF_RE = re.compile(r"^(?:ld\.lld:\s+)?(.+?):\s+definition of\s+(\S+)\s*$")
_TRACE_REF_RE = re.compile(r"^(?:ld\.lld:\s+)?(.+?):\s+(?:lazy\s+)?reference to\s+(\S+)\s*$")


def parse_trace_symbol_log(trace_text: str) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    """Parse `ld.lld --trace-symbol=<sym>` output into `(defs_by_sym, refs_by_sym)`."""
    defs: dict[str, list[str]] = {}
    refs: dict[str, list[str]] = {}
    for raw_line in trace_text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        m_def = _TRACE_DEF_RE.match(line)
        if m_def:
            defs.setdefault(m_def.group(2), []).append(m_def.group(1))
            continue
        m_ref = _TRACE_REF_RE.match(line)
        if m_ref:
            refs.setdefault(m_ref.group(2), []).append(m_ref.group(1))
    return defs, refs


# ==============================================================================
# Relocation-Masked Byte Comparison (A-LINK R/N/S + Rule vii full-body checks)
# ==============================================================================

def reloc_mask_width(r_type: int, ctx: str) -> int:
    if r_type in R_AARCH64_NONE_SET:
        return 0
    if r_type in R_AARCH64_8B_SET:
        return 8
    if r_type in R_AARCH64_4B_SET:
        return 4
    if r_type in R_AARCH64_2B_SET:
        return 2
    raise ValueError(f"{ctx}: unsupported AArch64 relocation type {r_type} during byte comparison")


@dataclass(frozen=True)
class BodyCompareResult:
    checked_bytes: int
    masked_bytes: int
    reloc_count: int
    byte_equal_unmasked: bool
    elf_body_sha256: str
    input_body_sha256: str


def compare_defined_symbol_bytes(
    *,
    obj: RelocObject,
    sym: RelSymbol,
    elf: ExecElf,
    elf_vma: int,
    map_sec_size: int | None = None,
    require_zero_relocs: bool = False,
    require_unmasked_equal: bool = False,
) -> BodyCompareResult:
    """Compare the defining input `.o` section slice for `sym` against final `elf` VMA bytes,
    masking only declared `SHT_RELA` spans in that section."""
    if sym.st_shndx in (SHN_UNDEF, SHN_ABS, SHN_COMMON) or sym.st_shndx >= len(obj.sections):
        raise ValueError(f"{obj.label}: symbol {sym.name!r} has non-section shndx={sym.st_shndx:#x}")
    sec = obj.sections[sym.st_shndx]
    sym_off = sym.st_value
    if sym_off > sec.sh_size:
        raise ValueError(f"{obj.label}: symbol {sym.name!r} st_value={sym_off} > sec.sh_size={sec.sh_size}")

    eff_size = sym.st_size if sym.st_size > 0 else (sec.sh_size - sym_off)
    if eff_size == 0 and map_sec_size is not None and map_sec_size > 0 and sym_off == 0:
        eff_size = map_sec_size
    if sym_off + eff_size > sec.sh_size:
        raise ValueError(
            f"{obj.label}: symbol {sym.name!r} range [{sym_off}, {sym_off + eff_size}) exceeds section {sec.name!r} ({sec.sh_size})"
        )

    elf_slice = elf.read_vma(elf_vma, eff_size)
    if sec.sh_type == SHT_NOBITS:
        if any(b != 0 for b in elf_slice):
            raise ValueError(f"{obj.label}: SHT_NOBITS symbol {sym.name!r} at {elf_vma:#x} has non-zero bytes in ELF")
        zero_sha = sha256_bytes(b"\x00" * eff_size)
        return BodyCompareResult(
            checked_bytes=eff_size,
            masked_bytes=0,
            reloc_count=0,
            byte_equal_unmasked=True,
            elf_body_sha256=zero_sha,
            input_body_sha256=zero_sha,
        )

    inp_slice = sec.data[sym_off : sym_off + eff_size]
    mask = bytearray(eff_size)
    rel_in_range = 0
    for rel in sec.relocs:
        w = reloc_mask_width(rel.r_type, f"{obj.label}:{sec.name}")
        if w == 0:
            continue
        r_start = rel.r_offset
        r_end = r_start + w
        # Check overlap with `[sym_off, sym_off + eff_size)`
        ov_lo = max(sym_off, r_start)
        ov_hi = min(sym_off + eff_size, r_end)
        if ov_lo < ov_hi:
            rel_in_range += 1
            for idx in range(ov_lo - sym_off, ov_hi - sym_off):
                mask[idx] = 1

    if require_zero_relocs and rel_in_range != 0:
        raise ValueError(
            f"{obj.label}: symbol {sym.name!r} expected 0 relocations in body, found {rel_in_range}"
        )

    for i in range(eff_size):
        if not mask[i] and inp_slice[i] != elf_slice[i]:
            raise ValueError(
                f"Byte mismatch for {sym.name!r} ({obj.label}:{sec.name}+{sym_off + i:#x} vs ELF {elf_vma + i:#x}): "
                f"input={inp_slice[i]:#04x} != elf={elf_slice[i]:#04x}"
            )

    unmasked_eq = inp_slice == elf_slice
    if require_unmasked_equal and not unmasked_eq:
        raise ValueError(
            f"Full-body unmasked equality failed for {sym.name!r} ({obj.label} vs ELF {elf_vma:#x})"
        )

    return BodyCompareResult(
        checked_bytes=eff_size,
        masked_bytes=sum(mask),
        reloc_count=rel_in_range,
        byte_equal_unmasked=unmasked_eq,
        elf_body_sha256=sha256_bytes(elf_slice),
        input_body_sha256=sha256_bytes(inp_slice),
    )


# ==============================================================================
# Trusted Lean Table & Pin Readers
# ==============================================================================

def is_cli_panic_symbol_placed(
    raw_or_demangled: str,
    extra_panic_syms: Iterable[str] = DEFAULT_CLI_PANIC_SYMBOLS_PLACED,
) -> bool:
    """Mirror `CliBinaryPq.isCliPanicSymbolPlaced`: `Rust.isPanicSymbol name || cliPanicSymbolsPlaced.contains name`."""
    dem = demangle_rust(raw_or_demangled)
    extra_set = set(extra_panic_syms)
    for cand in (raw_or_demangled, dem):
        if cand.startswith("core::panicking::") or cand in RUST_PANIC_EXACT_NAMES or cand in extra_set:
            return True
    return False


_STRLEN_WORD_RE = re.compile(r"0x([0-9a-fA-F]{8})#32")


def load_musl_strlen_bytes(repo_root: pathlib.Path | None = None) -> bytes:
    """Load and verify the 22 32-bit `muslStrlenWords` (`88` B) from `ProofLib/StdStartup/Strlen.lean`."""
    if repo_root is None:
        return DEFAULT_MUSL_STRLEN_BYTES
    strlen_lean = repo_root / "arm64-semantics/ProofLib/StdStartup/Strlen.lean"
    if not strlen_lean.is_file():
        return DEFAULT_MUSL_STRLEN_BYTES
    code_only = "\n".join(line for _, line in strip_lean_comments(strlen_lean.read_text(encoding="utf-8")))
    m = re.search(r"def\s+muslStrlenWords\s*:\s*List\s*\(BitVec\s+32\)\s*:=\s*\[(.*?)\]", code_only, re.S)
    if not m:
        raise ValueError(f"cannot locate `muslStrlenWords` in {strlen_lean}")
    words = [int(x, 16) for x in _STRLEN_WORD_RE.findall(m.group(1))]
    if len(words) != 22:
        raise ValueError(f"{strlen_lean}: expected 22 words in `muslStrlenWords`, found {len(words)}")
    raw = struct.pack("<22I", *words)
    if raw != DEFAULT_MUSL_STRLEN_BYTES:
        raise ValueError(f"{strlen_lean}: `muslStrlenWords` drifted from pinned 88-byte sequence")
    return raw


_PIN_LINE_RE = re.compile(r'^\s*sha256\s+"([0-9a-f]{64})"\s*$')
_FILE_BYTES_ELF_RE = re.compile(r'file_bytes%\s+"[^"]*signal-(?:session|cli)(?:-stock)?\.elf"')


def strip_lean_comments(text: str) -> list[tuple[int, str]]:
    """Strip `--` line comments and nested `/- ... -/` block comments from Lean source."""
    out: list[tuple[int, str]] = []
    depth = 0
    in_str = False
    escape = False
    line_no = 1
    buf: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if ch == "\n":
            out.append((line_no, "".join(buf)))
            buf = []
            line_no += 1
            escape = False
            i += 1
            continue
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_str:
            buf.append(ch)
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
            buf.append(ch)
            i += 1
        elif ch == "/" and nxt == "-":
            depth = 1
            i += 2
        elif ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
        else:
            buf.append(ch)
            i += 1
    if depth != 0:
        raise ValueError("unterminated `/- ... -/` block comment in Lean file")
    out.append((line_no, "".join(buf)))
    return out


def parse_cli_elf_pin(lean_mod_path: pathlib.Path) -> str:
    """Fail-closed parser for the single `sha256 "<64-hex>"` pin in `CliElf.lean` (GK-165 W1/W3)."""
    if not lean_mod_path.is_file():
        raise ValueError(f"Lean pin file missing: {lean_mod_path}")
    stripped = strip_lean_comments(lean_mod_path.read_text(encoding="utf-8"))
    code_only = "\n".join(line for _, line in stripped)
    fb = _FILE_BYTES_ELF_RE.findall(code_only)
    if len(fb) != 1:
        raise ValueError(f"{lean_mod_path}: expected 1 `file_bytes%` ELF macro, found {len(fb)}")
    pins: list[str] = []
    for lno, code in stripped:
        if not code.strip():
            continue
        m = _PIN_LINE_RE.match(code)
        if m:
            pins.append(m.group(1))
        elif re.match(r"^\s*sha256\b", code):
            raise ValueError(f"{lean_mod_path}:{lno}: malformed `sha256` line: {code.strip()!r}")
    if len(pins) != 1:
        raise ValueError(f"{lean_mod_path}: expected 1 `sha256` pin, found {len(pins)}")
    return pins[0]


def decode_aarch64_b_target(word: int, pc_vma: int) -> int | None:
    """Decode an unconditional 32-bit AArch64 `B <label>` (`0x14000000 | imm26`) at `pc_vma`."""
    if (word & 0xFC000000) != 0x14000000:
        return None
    imm26 = word & 0x03FFFFFF
    signed_imm = (imm26 - 0x04000000) if (imm26 & 0x02000000) else imm26
    return (pc_vma + signed_imm * 4) & 0xFFFFFFFFFFFFFFFF


def format_section_relocs(obj: RelocObject, sec: RelSection) -> list[dict[str, object]]:
    """Return canonical sorted relocation list for `sec` in `obj` (GK row 375 lock format)."""
    rows: list[dict[str, object]] = []
    for rel in sorted(sec.relocs, key=lambda r: (r.r_offset, r.r_type, r.sym_idx, r.r_addend)):
        if rel.r_type in R_AARCH64_NONE_SET:
            continue
        tsym = obj.symbols[rel.sym_idx]
        tname = tsym.name
        if not tname and tsym.stype == STT_SECTION and tsym.st_shndx < len(obj.sections):
            tname = f"<sec:{obj.sections[tsym.st_shndx].name}>"
        rows.append({
            "offset": int(rel.r_offset),
            "r_type": int(rel.r_type),
            "r_type_name": R_AARCH64_NAMES.get(rel.r_type, f"R_AARCH64_{rel.r_type}"),
            "target_symbol": tname,
            "addend": int(rel.r_addend),
        })
    return rows


def is_failstop_z_symbol(
    raw_or_demangled: str,
    extra_failstop: Iterable[str] = DEFAULT_FAILSTOP_DROP_STUBS,
    extra_panics: Iterable[str] = DEFAULT_CLI_PANIC_SYMBOLS_PLACED,
) -> bool:
    """True iff `raw_or_demangled` is allowed in A-LINK Rule (vi)'s `failstop_z` set."""
    if is_cli_panic_symbol_placed(raw_or_demangled, extra_panics):
        return True
    dem = demangle_rust(raw_or_demangled)
    fset = set(extra_failstop)
    return raw_or_demangled in fset or dem in fset


_LEAN_ABBREV_STR_RE = re.compile(r"(?:abbrev|def)\s+([A-Za-z0-9_']+)\s*:\s*String\s*:=\s*\"([^\"]+)\"")
_LEAN_TUPLE_ENTRY_RE = re.compile(r'\(\s*(?:"([^"]+)"|([A-Za-z0-9_\']+))\s*,')
_LEAN_LIST_STR_RE = re.compile(r'"([^"]+)"')


def load_cli_hook_and_panic_tables(
    repo_root: pathlib.Path | None = None,
) -> tuple[frozenset[str], frozenset[str]]:
    """Load `cliHookTablePlaced` and `cliPanicSymbolsPlaced` from `CliBinaryPq.lean` when present,
    failing closed if they drift from `DEFAULT_CLI_HOOK_TABLE_PLACED` / `DEFAULT_CLI_PANIC_SYMBOLS_PLACED`."""
    if repo_root is None:
        return DEFAULT_CLI_HOOK_TABLE_PLACED, DEFAULT_CLI_PANIC_SYMBOLS_PLACED
    pq_lean = repo_root / "LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean"
    if not pq_lean.is_file():
        return DEFAULT_CLI_HOOK_TABLE_PLACED, DEFAULT_CLI_PANIC_SYMBOLS_PLACED

    code_only = "\n".join(line for _, line in strip_lean_comments(pq_lean.read_text(encoding="utf-8")))
    abbrev_map: dict[str, str] = {
        m.group(1): m.group(2) for m in _LEAN_ABBREV_STR_RE.finditer(code_only)
    }
    m_pq = re.search(
        r"(?:noncomputable\s+)?def\s+cliPqxdhHookTablePlaced\b.*?:=\s*\[\s*(.*?)\s*\]\s*(?:noncomputable\s+)?def\s+cliHookTablePlaced\b",
        code_only,
        re.S,
    )
    m_cli = re.search(
        r"(?:noncomputable\s+)?def\s+cliHookTablePlaced\b.*?:=\s*cliPqxdhHookTablePlaced[^\[]*\+\+\s*\[\s*(.*?)\s*\]\s*(?:noncomputable\s+)?(?:def\s+|abbrev\s+)",
        code_only,
        re.S,
    )
    m_pan = re.search(
        r"(?:noncomputable\s+)?def\s+cliPanicSymbolsPlaced\b.*?:=\s*\[\s*(.*?)\s*\]\s*(?:noncomputable\s+)?(?:def\s+|abbrev\s+)",
        code_only,
        re.S,
    )
    if not (m_pq and m_cli and m_pan):
        raise ValueError(f"{pq_lean}: failed to parse `cliHookTablePlaced` / `cliPanicSymbolsPlaced`")

    hook_list: list[str] = []
    for block_str in (m_pq.group(1), m_cli.group(1)):
        for m_ent in _LEAN_TUPLE_ENTRY_RE.finditer(block_str):
            lit_val, ident_val = m_ent.group(1), m_ent.group(2)
            if lit_val is not None:
                hook_list.append(lit_val)
            else:
                if ident_val not in abbrev_map:
                    raise ValueError(f"{pq_lean}: unknown String abbrev `{ident_val}` in hook table")
                hook_list.append(abbrev_map[ident_val])

    hooks = frozenset(hook_list)
    panics = frozenset(_LEAN_LIST_STR_RE.findall(m_pan.group(1)))
    if hooks != DEFAULT_CLI_HOOK_TABLE_PLACED:
        added = sorted(hooks - DEFAULT_CLI_HOOK_TABLE_PLACED)
        removed = sorted(DEFAULT_CLI_HOOK_TABLE_PLACED - hooks)
        raise ValueError(
            f"{pq_lean}: `cliHookTablePlaced` drifted from `DEFAULT_CLI_HOOK_TABLE_PLACED` "
            f"(added={added}, removed={removed})"
        )
    if panics != DEFAULT_CLI_PANIC_SYMBOLS_PLACED:
        added = sorted(panics - DEFAULT_CLI_PANIC_SYMBOLS_PLACED)
        removed = sorted(DEFAULT_CLI_PANIC_SYMBOLS_PLACED - panics)
        raise ValueError(
            f"{pq_lean}: `cliPanicSymbolsPlaced` drifted from `DEFAULT_CLI_PANIC_SYMBOLS_PLACED` "
            f"(added={added}, removed={removed})"
        )
    return hooks, panics


def load_config_declared_exports(repo_root: pathlib.Path, config_rel_path: str) -> list[str]:
    """Read `[placed].exports` from `<repo_root>/<config_rel_path>`."""
    import tomllib

    cfg_file = (repo_root / config_rel_path).resolve()
    if not cfg_file.is_file():
        raise ValueError(f"translation config missing: {cfg_file}")
    cfg = tomllib.loads(cfg_file.read_text(encoding="utf-8"))
    placed = cfg.get("placed")
    if isinstance(placed, dict) and isinstance(placed.get("exports"), list):
        return [str(x) for x in placed["exports"]]
    exports = cfg.get("exports")
    if isinstance(exports, list):
        return [str(x) for x in exports]
    return []


def find_rustc_musl_libc_archive(
    work_dir: pathlib.Path | None = None,
    repo_root: pathlib.Path | None = None,
    expected_sha256: str = PINNED_RUSTC_MUSL_LIBC_SHA256,
) -> tuple[pathlib.Path, ParsedArchive] | None:
    """Locate `rustc 1.98.1` `aarch64-unknown-linux-musl/lib/self-contained/libc.a` and verify SHA-256."""
    import subprocess

    candidates: list[pathlib.Path] = []
    if work_dir is not None:
        candidates.append(work_dir / "self-contained" / "libc.a")
        candidates.append(work_dir / "libc.a")
    try:
        r = subprocess.run(
            ["rustc", "--print", "sysroot"],
            cwd=str(repo_root) if repo_root and repo_root.is_dir() else None,
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
        if r.returncode == 0 and r.stdout.strip():
            sr = pathlib.Path(r.stdout.strip())
            candidates.append(sr / "lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/libc.a")
    except Exception:  # noqa: BLE001
        pass
    home_tc = (
        pathlib.Path.home()
        / ".rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/libc.a"
    )
    candidates.append(home_tc)

    for cand in candidates:
        if cand.is_file():
            data = cand.read_bytes()
            if sha256_bytes(data) == expected_sha256:
                return cand, parse_ar_archive(data, str(cand))
    return None

