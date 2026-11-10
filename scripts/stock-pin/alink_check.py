#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""A-LINK v0.3.2 (P8) fail-closed stock-linker checker (`scripts/stock-pin/alink_check.py`).

Implements all A-LINK v0.3.2 + Gatekeeper rows 365, 367, 369, 372, 373, 374, 375 checks across
both stock-link recipes (`scripts/cli-elf-stock` builder and engine `snapshot-link --stock`):
  1. Computes `X_i = U_i \\ D_i` directly from as-linked Rust objects (incl. sysroot trims) and
     `X = ⋃_i X_i`; cross-checks engine `hookedExterns ⊆ X` (`scripts/cli-elf-stock --verify`
     checks the 94 `libsignalSessionExterns` in RX); verifies P8-3 `trimmedFrom.keepSet`
     section sets.
  2. Enforces Rule (iv) banned `ld.lld` flags, response/arg-file pins, bitcode/thin-archive bans,
     and weak-undefined allowlist outside `X`.
  3. Resolves every retained `ld.lld -Map` `MapInputSection` to its SHA-verified input `.o`/`.a(member)`,
     identifies `discarded` (`0` surviving relocations), and verifies **exact 1 definer** per
     surviving `x ∈ X` bound on final ELF `.symtab` VMA + `link.map` + defining input `.symtab`,
     classified `R` (archive member), `N` (native object), `S` (sibling image export), or `Z` (zero stub).
  4. Enforces Rule (i) non-local collision ban (G1), Rule (ii) entry harness `main` weak/weakened
     + placed `main` VMA check (W3), R/N/S relocation-masked byte equality, and G4 `n_undef_map`.
  5. Enforces Class `Z` `STB_GLOBAL` + all-zero bytes + whole-archive (`R` + `compiler_builtins.a`
     + `N` + `S`) non-displacement + Option `α` `displaced_weak == {3 outline atomics}` (`udf #0`
     at final VMA) + G5 `displaced_weak_referrers ⊆ cliLinkObjs`.
  6. Enforces Rule (vi) transitive relocation closure from `R`/`N`/`S`-defined `cliHookTablePlaced`
     keys (G3): fails closed if any `Z` stub outside `failstop_z` is reachable (must-fail on
     today's M3 2-config link without IO bridge).
  7. Enforces Rule (iii) per-config `real_hook_reached` / `real_proved` lists, verifying every
     image-reachable surviving referrer of each `real_hook_reached` symbol lies inside a hook closure.
  8. Enforces Rule (vii) + GK rows 373–375 + D1 (GK row 372):
     - `input_binding` read from defining INPUT `.o`/`.lo` `.symtab` (`STB_WEAK` fails);
     - `strlen`: `st_size == 0x58` (`88`), `0` relocs, unmasked `[strlen, +88) == muslStrlenWords`;
     - `memcpy` & `memset`: `0` text relocs on BOTH defining input and `rustc 1.98.1`
       `self-contained/libc.a` member (`memcpy.lo` / `memset.lo`), unmasked final ELF body equality;
     - `memmove`, `memcmp`, `bcmp`: Class `R` `rustc 1.98.1` `self-contained/libc.a` member
       (`memmove.lo`, `memcmp.lo`, `bcmp.lo`) SHA + relocation-masked ELF equality + canonical
       `relocs` list (`0` relocs on `memcmp.lo`), plus `bcmp` 1-word AArch64 `B` decode targeting
       `memcmp`'s final ELF VMA;
     - D1 kept `STT_OBJECT` extern-data == `{MAX_LOG_LEVEL_FILTER, ED25519_BASEPOINT_TABLE}`;
     - `--lock <lock.toml|json>` fail-on-diff verification across all lock rows and exact lists.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass, field
import json
import os
import pathlib
import re
import struct
import sys
import tomllib
from typing import Any, Mapping, Sequence

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
DEFAULT_REL_OUT_DIR = pathlib.Path(".GeneratedLean/cli-elf")
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import elf_inspect  # noqa: E402


BANNED_LLD_EXACT_FLAGS: frozenset[str] = frozenset({
    "--wrap",
    "--defsym",
    "--allow-multiple-definition",
    "-r",
    "--relocatable",
    "-shared",
    "--shared",
    "-Bshareable",
    "-pie",
    "--pie",
    "--pic-executable",
    "--warn-unresolved-symbols",
    "--noinhibit-exec",
    "--allow-shlib-undefined",
})

BANNED_LLD_PREFIXES: tuple[str, ...] = (
    "--wrap=",
    "--defsym=",
    "--unresolved-symbols=ignore",
    "--plugin-opt=",
    "-plugin-opt=",
    "--lto-",
    "-flto",
)

BANNED_Z_ARGS: frozenset[str] = frozenset({"muldefs", "undefs"})

STARTFILE_BASENAMES: frozenset[str] = frozenset({
    "crt1.o",
    "Scrt1.o",
    "rcrt1.o",
    "crti.o",
    "crtn.o",
    "crtbegin.o",
    "crtbeginS.o",
    "crtbeginT.o",
    "crtend.o",
    "crtendS.o",
})

HARNESS_BASENAMES: frozenset[str] = frozenset({
    "main.o",
    "main_cli.o",
    "main_rust.o",
})

KNOWN_COMMITTED_NATIVE_BASENAMES: frozenset[str] = frozenset({
    "memcpy.o",
    "memset.o",
    "strlen.o",
    "strlen.lo",
    "rdl_shim.o",
})

COMPILER_RT_ARCHIVE_BASENAMES: frozenset[str] = frozenset({
    "compiler_builtins.a",
    "libcompiler_rt.a",
})

LINKER_SYNTHESIZED_SYMBOLS: frozenset[str] = frozenset({
    "_DYNAMIC",
    "__init_array_start",
    "__init_array_end",
    "__fini_array_start",
    "__fini_array_end",
    "__preinit_array_start",
    "__preinit_array_end",
    "__bss_start",
    "_edata",
    "_end",
    "_etext",
    "__ehdr_start",
    "__executable_start",
    "__dso_handle",
    "__rela_iplt_start",
    "__rela_iplt_end",
})

ENGINE_CRT_WEAK_UNDEF_PROBES: frozenset[str] = frozenset({
    "_DYNAMIC",
    "__cxa_finalize",
})

S2_REAL_BODY_KEYS: tuple[str, ...] = (
    "bcmp",
    "memcmp",
    "memcpy",
    "memmove",
    "memset",
    "strlen",
)


class ALinkError(RuntimeError):
    """Fail-closed error carrying structured violation messages."""

    def __init__(self, errors: Sequence[str]) -> None:
        self.errors = list(errors)
        joined = "\n  - ".join(self.errors)
        super().__init__(f"A-LINK check FAILED ({len(self.errors)} violation(s)):\n  - {joined}")


@dataclass(frozen=True)
class InputRecord:
    role: str  # "S:<i>", "R", "N", "Z", "startfile", "harness"
    name: str  # canonical display / lock filename (e.g. "libc.a", "memcpy.o", "lib0_0.o")
    rel_path: str
    disk_path: pathlib.Path
    sha256: str
    size: int
    image_idx: int | None = None
    obj: elf_inspect.RelocObject | None = None
    archive: elf_inspect.ParsedArchive | None = None
    trimmed_from: Mapping[str, Any] | None = None


@dataclass(frozen=True)
class RetainedSecNode:
    node_id: str  # "<file_or_archive(member)>:(<sec_name>)[+0x...]"
    role: str
    image_idx: int | None
    source_file: str
    archive_member: str | None
    archive_member_key: str  # disambiguates duplicate member names via `<name>@<index>`
    file_sha256: str  # `.o` sha256 or archive member `.lo` sha256
    archive_sha256: str | None
    obj: elf_inspect.RelocObject
    sec: elf_inspect.RelSection
    map_sec: elf_inspect.MapInputSection


@dataclass
class ALinkReport:
    recipe: str  # "engine" or "builder"
    config_count: int
    configs: list[str]
    elf_path: str
    elf_sha256: str
    elf_size: int
    elf_entry: str
    main_elf_addr: str
    placed_exports: dict[str, dict[str, str]]
    x_per_image: dict[str, list[str]]
    x_all: list[str]
    x_count: int
    x_sha256: str
    hooked_externs_count: int | None
    engine_hooked_externs_sha256: str | None
    x_minus_hooked_externs: list[str]
    data_only_in_x: list[str]
    class_histogram: dict[str, int]
    zero_definer_names: list[str]
    multi_definer_names: list[str]
    discarded: list[str]
    definers: dict[str, dict[str, Any]]
    real_hook_reached: list[str]
    real_proved: list[str]
    harness_startup_referrers: dict[str, list[str]]
    failstop_z: list[str]
    hook_closures: dict[str, dict[str, Any]]
    displaced_weak: list[str]
    displaced_weak_elf_addrs: dict[str, str]
    displaced_weak_referrers: list[str]
    displaced_weak_non_lib0_relocs_pre_gc: int
    n_undef_map: dict[str, dict[str, dict[str, Any]]]
    s2_real_body_lock: dict[str, dict[str, Any]]
    d1_extern_data_lock: dict[str, Any]
    weakened_in_main: list[str]
    exempted_aliases: list[str]
    weak_undefined_allowed: list[str]
    sysroot_trims: list[dict[str, Any]]
    runtime_archives: dict[str, str]
    native_objects: dict[str, str]
    stub_object: dict[str, Any]
    harness_object: dict[str, Any]
    compiler_builtins_archive: dict[str, Any] | None
    lld_argv: list[str]
    lld_version: str
    stock_lld_arg_files: dict[str, str]
    engine_commit: str
    rustc_version: str
    zig_version: str
    rust_extracted: dict[str, dict[str, Any]] = field(default_factory=dict)
    toolchain_sysroot_scan: dict[str, Any] = field(default_factory=dict)
    proved_closures: dict[str, dict[str, Any]] = field(default_factory=dict)
    inputs_lock_pin: dict[str, Any] | None = None
    violations: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return len(self.violations) == 0

    def to_json_dict(self) -> dict[str, Any]:
        out: dict[str, Any] = {
            "ok": len(self.violations) == 0,
            "recipe": self.recipe,
            "config_count": self.config_count,
            "configs": self.configs,
            "elf_path": self.elf_path,
            "elf_sha256": self.elf_sha256,
            "elf_size": self.elf_size,
            "elf_entry": self.elf_entry,
            "main_elf_addr": self.main_elf_addr,
            "placed_exports": self.placed_exports,
            "x_per_image": self.x_per_image,
            "x_count": self.x_count,
            "x_sha256": self.x_sha256,
            "x_all": self.x_all,
            "hooked_externs_count": self.hooked_externs_count,
            "engine_hooked_externs_sha256": self.engine_hooked_externs_sha256,
            "x_minus_hooked_externs": self.x_minus_hooked_externs,
            "data_only_in_x": self.data_only_in_x,
            "class_histogram": self.class_histogram,
            "zero_definer_names": self.zero_definer_names,
            "multi_definer_names": self.multi_definer_names,
            "discarded": self.discarded,
            "definers": self.definers,
            "real_hook_reached": self.real_hook_reached,
            "real_proved": self.real_proved,
            "harness_startup_referrers": self.harness_startup_referrers,
            "failstop_z": self.failstop_z,
            "hook_closures": self.hook_closures,
            "displaced_weak": self.displaced_weak,
            "displaced_weak_elf_addrs": self.displaced_weak_elf_addrs,
            "displaced_weak_referrers": self.displaced_weak_referrers,
            "displaced_weak_non_lib0_relocs_pre_gc": self.displaced_weak_non_lib0_relocs_pre_gc,
            "n_undef_map": self.n_undef_map,
            "s2_real_body_lock": self.s2_real_body_lock,
            "d1_extern_data_lock": self.d1_extern_data_lock,
            "weakened_in_main": self.weakened_in_main,
            "exempted_aliases": self.exempted_aliases,
            "weak_undefined_allowed": self.weak_undefined_allowed,
            "sysroot_trims": self.sysroot_trims,
            "runtime_archives": self.runtime_archives,
            "native_objects": self.native_objects,
            "stub_object": self.stub_object,
            "harness_object": self.harness_object,
            "compiler_builtins_archive": self.compiler_builtins_archive,
            "lld_argv": self.lld_argv,
            "lld_version": self.lld_version,
            "stock_lld_arg_files": self.stock_lld_arg_files,
            "engine_commit": self.engine_commit,
            "rustc_version": self.rustc_version,
            "zig_version": self.zig_version,
            "violations": self.violations,
        }
        if self.rust_extracted:
            out["rust_extracted"] = self.rust_extracted
        if self.toolchain_sysroot_scan:
            out["toolchain_sysroot_scan"] = self.toolchain_sysroot_scan
        if self.proved_closures:
            out["proved_closures"] = self.proved_closures
        if self.inputs_lock_pin is not None:
            out["inputs_lock_pin"] = self.inputs_lock_pin
        return out


def _canonical_list_sha256(items: Sequence[str]) -> str:
    payload = ("\n".join(items) + ("\n" if items else "")).encode("utf-8")
    return elf_inspect.sha256_bytes(payload)


def _canonicalize_reloc_list(relocs: Sequence[Mapping[str, Any]] | None) -> list[dict[str, Any]]:
    """Normalize relocation dicts so alias keys (`rel_offset`/`rtype`/`target`) compare cleanly."""
    if not relocs:
        return []
    out: list[dict[str, Any]] = []
    for r in relocs:
        out.append({
            "offset": int(r.get("offset", r.get("rel_offset", 0))),
            "r_type": int(r.get("r_type", r.get("rtype", 0))),
            "target_symbol": str(r.get("target_symbol", r.get("target", ""))),
            "addend": int(r.get("addend", 0)),
        })
    return out


def _resolve_staged_file(
    rel_or_name: str,
    search_roots: Sequence[pathlib.Path],
    expected_sha256: str | None = None,
) -> pathlib.Path:
    rel_p = pathlib.Path(rel_or_name)
    exact_candidates: list[pathlib.Path] = []
    basename_candidates: list[pathlib.Path] = []
    has_dir_parts = rel_p.is_absolute() or len(rel_p.parts) >= 2

    if rel_p.is_absolute():
        exact_candidates.append(rel_p)
    for root in search_roots:
        if has_dir_parts and not rel_p.is_absolute():
            exact_candidates.append(root / rel_p)
            if rel_p.parts[0] == "work":
                tail = pathlib.Path(*rel_p.parts[1:])
                exact_candidates.append(root / tail)
                exact_candidates.append(root / "stock_stage" / rel_p)
            elif rel_p.parts[0] == "..":
                stripped_parts = [pt for pt in rel_p.parts if pt != ".."]
                if stripped_parts:
                    exact_candidates.append(root / pathlib.Path(*stripped_parts))
        else:
            exact_candidates.append(root / rel_p)

        basename_candidates.append(root / rel_p.name)
        basename_candidates.append(root / "stubs" / rel_p.name)
        basename_candidates.append(root / "musl-native" / "Implementation" / "musl-string" / "out" / rel_p.name)
        basename_candidates.append(root / "musl-self-contained" / rel_p.name)
        basename_candidates.append(root / "stock_stage" / "work" / rel_p.name)
        basename_candidates.append(root / "stock_stage" / "work" / "runtime" / rel_p.name)
        basename_candidates.append(root / "stock_stage" / "work" / "native" / rel_p.name)
        basename_candidates.append(root / "work" / rel_p.name)
        basename_candidates.append(root / "native" / rel_p.name)
        basename_candidates.append(root / "self-contained" / rel_p.name)
        basename_candidates.append(root / "runtime" / rel_p.name)

    seen_exact: set[pathlib.Path] = set()
    existing_exact: list[pathlib.Path] = []
    for c in exact_candidates:
        rc = c.resolve() if c.exists() else c
        if rc in seen_exact:
            continue
        seen_exact.add(rc)
        if c.is_file():
            existing_exact.append(c)
            if expected_sha256 and elf_inspect.sha256_file(c) == expected_sha256:
                return c
    if has_dir_parts and existing_exact:
        # Never jump across directories by basename when an explicit relative/absolute path exists on disk
        return existing_exact[0]

    seen: set[pathlib.Path] = set(seen_exact)
    existing: list[pathlib.Path] = list(existing_exact)
    for c in basename_candidates:
        rc = c.resolve() if c.exists() else c
        if rc in seen:
            continue
        seen.add(rc)
        if c.is_file():
            existing.append(c)
            if expected_sha256 and elf_inspect.sha256_file(c) == expected_sha256:
                return c

    for root in search_roots:
        if not root.is_dir():
            continue
        for c in sorted(root.rglob(rel_p.name)):
            if not c.is_file():
                continue
            rc = c.resolve()
            if rc in seen:
                continue
            seen.add(rc)
            existing.append(c)
            if expected_sha256 and elf_inspect.sha256_file(c) == expected_sha256:
                return c

    if existing:
        if not expected_sha256 and len({p.resolve() for p in existing}) > 1:
            raise FileNotFoundError(
                f"ambiguous staged input {rel_or_name!r}: multiple files share basename {[str(p) for p in existing]}"
            )
        return existing[0]
    raise FileNotFoundError(f"cannot locate staged input {rel_or_name!r} under {[str(r) for r in search_roots]}")


def _scan_lld_argv_for_banned_flags(argv: Sequence[str], ctx: str, errors: list[str]) -> None:
    i = 0
    n = len(argv)
    while i < n:
        tok = str(argv[i])
        if tok in BANNED_LLD_EXACT_FLAGS:
            errors.append(f"Rule (iv): banned lld flag {tok!r} in {ctx}[{i}]")
        elif any(tok.startswith(p) for p in BANNED_LLD_PREFIXES):
            errors.append(f"Rule (iv): banned lld flag {tok!r} in {ctx}[{i}]")
        elif tok == "-z" and i + 1 < n and str(argv[i + 1]) in BANNED_Z_ARGS:
            errors.append(f"Rule (iv): banned `-z {argv[i + 1]}` in {ctx}[{i}]")
        elif any(tok == f"-z{z}" for z in BANNED_Z_ARGS):
            errors.append(f"Rule (iv): banned `{tok}` in {ctx}[{i}]")
        elif tok.startswith("@"):
            errors.append(f"Rule (iv): unpinned response file `{tok}` in {ctx}[{i}]")
        elif tok.endswith(".rlib"):
            errors.append(f"0f(v): forbidden Rust `.rlib` archive `{tok}` in {ctx}[{i}]")
        i += 1


KNOWN_RUNTIME_ARCHIVE_BASENAMES: frozenset[str] = frozenset({
    "libc.a",
    "libcompiler_rt.a",
    "compiler_builtins.a",
    "libunwind.a",
})

ZERO_RETAINED_ARCHIVE_BASENAMES: frozenset[str] = frozenset({
    "libunwind.a",
})


def _load_lock_bytes(raw_bytes: bytes, lock_path: pathlib.Path) -> dict[str, Any]:
    raw = raw_bytes.decode("utf-8")
    if lock_path.suffix.lower() == ".json":
        data = json.loads(raw)
    else:
        data = tomllib.loads(raw)
    if not isinstance(data, dict):
        raise ValueError(f"{lock_path}: expected top-level mapping")
    return data


def _load_lock_file(lock_path: pathlib.Path) -> dict[str, Any]:
    if not lock_path.exists():
        raise FileNotFoundError(f"file does not exist: {lock_path}")
    if not lock_path.is_file():
        raise IsADirectoryError(f"not a regular file: {lock_path}")
    return _load_lock_bytes(lock_path.read_bytes(), lock_path)


_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")


def _is_hex64(val: Any) -> bool:
    return isinstance(val, str) and bool(_HEX64_RE.match(val))


CANONICAL_CI_INPUTS_LOCK_REL = (
    "third_party/libsignal/libsignal-session/cli-elf/stock/inputs_stock_stdbin.lock"
)


def _verify_k2_inputs_lock(
    *,
    ci: bool,
    inputs_lock_path: pathlib.Path | None,
    lock_path: pathlib.Path | None,
    repo_root: pathlib.Path | None,
    eff_repo_root: pathlib.Path | None,
) -> tuple[list[str], dict[str, Any] | None, bytes | None]:
    """Enforce GK row 492 condition K2 + SR-62 (1) `--inputs-lock` / `--ci` pin on `--lock`.

    Returns `(errors, inputs_lock_pin_summary, lock_raw_bytes_if_read)`.
    """
    errs: list[str] = []
    if ci and repo_root is None:
        errs.append("K2 (--ci): `--repo-root <dir>` is mandatory when `--ci` is set")
    if ci and inputs_lock_path is None:
        errs.append("K2 (--ci): `--inputs-lock <path>` is mandatory when `--ci` is set")
    if ci and lock_path is None:
        errs.append("K2 (--ci): `--lock <path>` is mandatory when `--ci` is set")
    if inputs_lock_path is not None and lock_path is None:
        errs.append("K2 (--inputs-lock): `--lock <path>` is required when `--inputs-lock` is given")

    lock_bytes: bytes | None = None
    if lock_path is not None:
        try:
            if not lock_path.exists():
                raise FileNotFoundError(f"file does not exist: {lock_path}")
            if not lock_path.is_file():
                raise IsADirectoryError(f"not a regular file: {lock_path}")
            lock_bytes = lock_path.read_bytes()
        except OSError as exc:
            errs.append(f"K2 (--lock): lock file {str(lock_path)!r} is missing or unreadable: {exc}")

    if inputs_lock_path is None:
        return errs, None, lock_bytes

    if ci:
        if repo_root is None:
            return errs, None, lock_bytes
        if not repo_root.exists() or not repo_root.is_dir():
            errs.append(
                f"K2 (--ci): `--repo-root` is missing or not a directory: {str(repo_root)!r}"
            )
            return errs, None, lock_bytes
        repo_real_ci = os.path.realpath(repo_root)
        canonical_inputs_target = repo_root / CANONICAL_CI_INPUTS_LOCK_REL
        canonical_inputs_real = os.path.realpath(canonical_inputs_target)
        given_inputs_real = os.path.realpath(inputs_lock_path)
        expected_ci_canon_in_repo = os.path.normpath(
            os.path.join(repo_real_ci, CANONICAL_CI_INPUTS_LOCK_REL)
        )
        try:
            canon_in_repo = (
                os.path.commonpath([repo_real_ci, canonical_inputs_real]) == repo_real_ci
                and canonical_inputs_real != repo_real_ci
            )
        except ValueError:
            canon_in_repo = False
        try:
            given_in_repo = (
                os.path.commonpath([repo_real_ci, given_inputs_real]) == repo_real_ci
                and given_inputs_real != repo_real_ci
            )
        except ValueError:
            given_in_repo = False
        if not canon_in_repo:
            errs.append(
                f"K2 (--ci): canonical inputs lock {str(canonical_inputs_target)!r} "
                f"(realpath {canonical_inputs_real!r}) resolves outside `--repo-root` "
                f"(expected {expected_ci_canon_in_repo!r}; `--inputs-lock` realpath {given_inputs_real!r})"
            )
            return errs, None, lock_bytes
        if not os.path.isfile(canonical_inputs_real):
            errs.append(
                f"K2 (--ci): canonical inputs lock does not exist on disk: {str(canonical_inputs_target)!r} "
                f"(realpath {canonical_inputs_real!r}; `--inputs-lock` realpath {given_inputs_real!r})"
            )
            return errs, None, lock_bytes
        if not given_in_repo or given_inputs_real != canonical_inputs_real:
            errs.append(
                f"K2 (--ci): `--inputs-lock` realpath {given_inputs_real!r} != "
                f"canonical `repo_root / {CANONICAL_CI_INPUTS_LOCK_REL}` realpath {canonical_inputs_real!r}"
            )
            return errs, None, lock_bytes

    try:
        inputs_data = _load_lock_file(inputs_lock_path)
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError, json.JSONDecodeError, ValueError) as exc:
        errs.append(
            f"K2 (--inputs-lock): unreadable or invalid inputs lock {str(inputs_lock_path)!r}: {exc}"
        )
        return errs, None, lock_bytes

    stock_sec = inputs_data.get("stock")
    if "stock" in inputs_data and not isinstance(stock_sec, Mapping):
        errs.append(
            f"K2 (--inputs-lock): `[stock]` in {str(inputs_lock_path)!r} must be a table/mapping"
        )
        stock_sec = None

    def _extract_stock_key(key: str) -> tuple[Any, bool]:
        has_top = key in inputs_data
        has_sub = isinstance(stock_sec, Mapping) and (key in stock_sec)
        if has_top and has_sub and inputs_data[key] != stock_sec[key]:
            errs.append(
                f"K2 (--inputs-lock): conflicting `{key}` between top-level ({inputs_data[key]!r}) "
                f"and `[stock]` ({stock_sec[key]!r}) in {str(inputs_lock_path)!r}"
            )
            return None, False
        if has_sub:
            return stock_sec[key], True
        if has_top:
            return inputs_data[key], True
        return None, False

    raw_sha, has_sha = _extract_stock_key("m4_lock_sha256")
    raw_rel_path, has_rel_path = _extract_stock_key("m4_lock_path")

    expected_sha: str | None = None
    if not has_sha or raw_sha is None:
        errs.append(
            f"K2 (--inputs-lock): missing required key `m4_lock_sha256` in {str(inputs_lock_path)!r}"
        )
    elif not _is_hex64(raw_sha):
        errs.append(
            f"K2 (--inputs-lock): invalid `m4_lock_sha256` {raw_sha!r} in {str(inputs_lock_path)!r} "
            "(expected 64 lowercase hex characters)"
        )
    else:
        expected_sha = str(raw_sha)

    expected_rel_path: str | None = None
    if not has_rel_path or raw_rel_path is None:
        errs.append(
            f"K2 / SR-62 (--inputs-lock): missing required key `m4_lock_path` in {str(inputs_lock_path)!r}"
        )
    elif (
        not isinstance(raw_rel_path, str)
        or not raw_rel_path.strip()
        or raw_rel_path != raw_rel_path.strip()
        or "\x00" in raw_rel_path
        or pathlib.Path(raw_rel_path).is_absolute()
    ):
        errs.append(
            f"K2 / SR-62 (--inputs-lock): invalid `m4_lock_path` {raw_rel_path!r} in {str(inputs_lock_path)!r} "
            "(expected non-empty repo-relative path string)"
        )
    else:
        expected_rel_path = raw_rel_path

    k2_repo_root: pathlib.Path | None = None
    if repo_root is not None:
        if not repo_root.exists() or not repo_root.is_dir():
            errs.append(
                f"K2 / SR-62 (--inputs-lock): `--repo-root` is missing or not a directory: {str(repo_root)!r}"
            )
        else:
            k2_repo_root = repo_root
    elif eff_repo_root is not None and eff_repo_root.is_dir():
        k2_repo_root = eff_repo_root
    else:
        errs.append(
            "K2 / SR-62 (--inputs-lock): repository root could not be resolved; pass `--repo-root <dir>`"
        )

    actual_sha: str | None = None
    if lock_bytes is not None:
        actual_sha = elf_inspect.sha256_bytes(lock_bytes)
        if expected_sha is not None and actual_sha != expected_sha:
            errs.append(
                f"K2 (--inputs-lock): `--lock` ({lock_path}) sha256 {actual_sha} != "
                f"inputs.lock `m4_lock_sha256` {expected_sha}"
            )

    lock_real_str: str | None = None
    expected_real_str: str | None = None
    if (
        lock_path is not None
        and lock_bytes is not None
        and expected_rel_path is not None
        and k2_repo_root is not None
    ):
        repo_real_str = os.path.realpath(k2_repo_root)
        expected_target = k2_repo_root / expected_rel_path
        expected_real_str = os.path.realpath(expected_target)
        lock_real_str = os.path.realpath(lock_path)
        try:
            in_repo = os.path.commonpath([repo_real_str, expected_real_str]) == repo_real_str
        except ValueError:
            in_repo = False
        if not in_repo or expected_real_str == repo_real_str:
            errs.append(
                f"K2 / SR-62 (--inputs-lock): `m4_lock_path` {expected_rel_path!r} resolves outside repo_root "
                f"({expected_real_str!r} vs {repo_real_str!r})"
            )
        elif not os.path.isfile(expected_real_str):
            errs.append(
                f"K2 / SR-62 (--inputs-lock): `repo_root / m4_lock_path` does not exist on disk: "
                f"{str(expected_target)!r} (realpath {expected_real_str!r})"
            )
        elif lock_real_str != expected_real_str or not os.path.samefile(lock_real_str, expected_real_str):
            errs.append(
                f"K2 / SR-62 (--inputs-lock): `--lock` realpath {lock_real_str!r} != "
                f"`repo_root / m4_lock_path` realpath {expected_real_str!r} (`m4_lock_path`={expected_rel_path!r})"
            )

    summary = {
        "inputs_lock_path": str(inputs_lock_path),
        "m4_lock_path": expected_rel_path,
        "m4_lock_sha256": expected_sha,
        "actual_lock_sha256": actual_sha,
        "lock_realpath": lock_real_str,
        "expected_lock_realpath": expected_real_str,
        "ci_mode": bool(ci),
        "verified": len(errs) == 0,
    }
    return errs, summary, lock_bytes


def _parse_lock_native_objects(
    lock: Mapping[str, Any] | None,
) -> tuple[bool, dict[str, dict[str, Any]]]:
    """Parse `lock["native_objects"]` positive list (GK 458 / SR-31 A2).
    Returns `(has_valid_mapping, {obj_name: normalized_entry_dict})`."""
    if lock is None:
        return False, {}
    if "native_objects" not in lock or not isinstance(lock["native_objects"], Mapping):
        return False, {}
    out: dict[str, dict[str, Any]] = {}
    for k, v in lock["native_objects"].items():
        name = str(k)
        if isinstance(v, Mapping):
            ent = dict(v)
            ent["sha256"] = str(v.get("sha256") or v.get("n_object_file_sha") or "")
        else:
            ent = {"sha256": str(v)}
        out[name] = ent
    return True, out


def _parse_lock_rust_extracted(
    lock: Mapping[str, Any] | None,
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    """Parse and schema-check `lock["rust_extracted"]` entries (`stockpin_exit_list.md` §0f / GK 458 / GK 466)."""
    if lock is None or "rust_extracted" not in lock:
        return {}, []
    raw_re = lock["rust_extracted"]
    if not isinstance(raw_re, Mapping):
        return {}, ["SR-31 A2 / GK 458: lock `rust_extracted` must be a mapping"]
    out: dict[str, dict[str, Any]] = {}
    errs: list[str] = []
    for k, v in raw_re.items():
        obj_name = str(k)
        if not isinstance(v, Mapping):
            errs.append(f"GK 458 C1: `rust_extracted[{obj_name!r}]` must be a mapping")
            continue
        ent = dict(v)
        raw_kind = str(ent.get("kind") or "").strip()
        if raw_kind in ("a", "rlib_subset", "rlib_member"):
            kind = "rlib_member"
        elif raw_kind in ("b", "alias_stub"):
            kind = "alias_stub"
        elif not raw_kind:
            if any(fk in ent for fk in ("rlib_path", "rlib", "rlib_sha256", "member", "member_sha256")):
                kind = "rlib_member"
            elif any(fk in ent for fk in ("asm_path", "asm_sha256")):
                kind = "alias_stub"
            else:
                kind = ""
        else:
            kind = raw_kind
        if kind not in ("rlib_member", "alias_stub"):
            errs.append(
                f"GK 458 C1: `rust_extracted[{obj_name!r}]` invalid/missing `kind` "
                f"(expected 'a'/'rlib_member' or 'b'/'alias_stub', got {raw_kind!r})"
            )
            continue
        ent["kind"] = kind
        obj_sha = str(ent.get("sha256") or "")
        if not _is_hex64(obj_sha):
            errs.append(f"GK 458 C1: `rust_extracted[{obj_name!r}].sha256` must be 64-hex SHA-256")
        ent["sha256"] = obj_sha

        if kind == "rlib_member":
            rlib_p = str(ent.get("rlib_path") or ent.get("rlib") or "")
            rlib_sha = str(ent.get("rlib_sha256") or "")
            mem_name = str(ent.get("member") or "")
            mem_sha = str(ent.get("member_sha256") or "")
            recipe_s = str(ent.get("recipe") or "").strip()
            raw_secs = ent.get("keep_sections") if "keep_sections" in ent else ent.get("sections")
            if not rlib_p:
                errs.append(f"0f(vi) / GK 458 C1(a): `rust_extracted[{obj_name!r}]` missing `rlib_path`")
            if not _is_hex64(rlib_sha):
                errs.append(f"0f(vi) / GK 458 C1(a): `rust_extracted[{obj_name!r}]` invalid `rlib_sha256`")
            if not mem_name:
                errs.append(f"0f(vi) / GK 458 C1(a): `rust_extracted[{obj_name!r}]` missing `member`")
            if not _is_hex64(mem_sha):
                errs.append(f"0f(vi) / GK 458 C1(a): `rust_extracted[{obj_name!r}]` invalid `member_sha256`")
            if not recipe_s:
                errs.append(f"0f(vi) / GK 466: `rust_extracted[{obj_name!r}]` missing non-empty extraction `recipe`")
            if (
                raw_secs is None
                or not isinstance(raw_secs, Sequence)
                or isinstance(raw_secs, (str, bytes))
                or len(raw_secs) == 0
            ):
                errs.append(
                    f"0f(vi) / GK 466: `rust_extracted[{obj_name!r}]` missing non-empty `keep_sections` list"
                )
                keep_secs_norm: list[str] = []
            else:
                keep_secs_norm = [str(s) for s in raw_secs]
            ent["rlib_path"] = rlib_p
            ent["rlib_sha256"] = rlib_sha
            ent["member"] = mem_name
            ent["member_sha256"] = mem_sha
            ent["recipe"] = recipe_s
            ent["keep_sections"] = keep_secs_norm
        else:
            asm_p = str(ent.get("asm_path") or "")
            asm_sha = str(ent.get("asm_sha256") or "")
            recipe_s = str(ent.get("recipe") or "").strip()
            if not asm_p:
                errs.append(f"GK 458 C1(b): `rust_extracted[{obj_name!r}]` missing `asm_path`")
            if not _is_hex64(asm_sha):
                errs.append(f"GK 458 C1(b): `rust_extracted[{obj_name!r}]` invalid `asm_sha256`")
            if not recipe_s:
                errs.append(f"GK 458 C1(b): `rust_extracted[{obj_name!r}]` missing non-empty `recipe`")
            ent["asm_path"] = asm_p
            ent["asm_sha256"] = asm_sha
            ent["recipe"] = recipe_s
        out[obj_name] = ent
    return out, errs


def _discover_toolchain_sysroot(
    repo_root: pathlib.Path | None,
    explicit_sysroot: pathlib.Path | None = None,
    expected_rustc_version: str | None = None,
) -> pathlib.Path | None:
    import subprocess

    if explicit_sysroot is not None:
        return explicit_sysroot.resolve()
    ver = (expected_rustc_version or "").strip()
    if ver:
        try:
            r_up = subprocess.run(
                ["rustup", "run", ver, "rustc", "--print", "sysroot"],
                cwd=str(repo_root) if repo_root and repo_root.is_dir() else None,
                capture_output=True,
                text=True,
                timeout=10,
                check=False,
            )
            if r_up.returncode == 0 and r_up.stdout.strip():
                sr_up = pathlib.Path(r_up.stdout.strip()).resolve()
                if sr_up.is_dir():
                    return sr_up
        except Exception:  # noqa: BLE001
            pass
        tc_dir = pathlib.Path.home() / ".rustup/toolchains"
        if tc_dir.is_dir():
            for cand in sorted(tc_dir.glob(f"{ver}-*")):
                if cand.is_dir():
                    return cand.resolve()
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
            sr = pathlib.Path(r.stdout.strip()).resolve()
            if sr.is_dir():
                return sr
    except Exception:  # noqa: BLE001
        pass
    if not ver or ver == "1.98.1":
        fallback = pathlib.Path.home() / ".rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu"
        if fallback.is_dir():
            return fallback.resolve()
    return None


def _query_sysroot_rustc_version(sysroot: pathlib.Path) -> tuple[str | None, str | None]:
    """Run `<sysroot>/bin/rustc -V` and return `(parsed_semver, error_if_any)`."""
    import subprocess

    rustc_bin = sysroot / "bin/rustc"
    if not rustc_bin.is_file():
        return None, f"missing `{rustc_bin}`"
    try:
        r = subprocess.run(
            [str(rustc_bin), "-V"],
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        return None, f"failed to execute `{rustc_bin} -V`: {exc}"
    if r.returncode != 0:
        return None, f"`{rustc_bin} -V` exited with rc={r.returncode}: {r.stderr.strip()}"
    out_line = r.stdout.strip()
    m = re.match(r"^rustc\s+(\S+)", out_line)
    if not m:
        return None, f"unrecognized `{rustc_bin} -V` output: {out_line!r}"
    return m.group(1), None


def _resolve_image_target_triples(
    repo_root: pathlib.Path | None,
    lock_data: Mapping[str, Any] | None,
) -> tuple[list[str], list[str]]:
    """Determine the image target triple(s) for the §0f(vi) sysroot `.rlib` scan (`SR-41 F1`).
    Every linked image in `alink_check` is `EM_AARCH64`, so only `aarch64-*` target triples are valid."""
    errs: list[str] = []
    triples: list[str] = []
    if lock_data is not None:
        raw_tt = lock_data.get("target_triples")
        raw_t1 = lock_data.get("target_triple")
        if raw_tt is not None:
            if (
                not isinstance(raw_tt, Sequence)
                or isinstance(raw_tt, (str, bytes))
                or len(raw_tt) == 0
            ):
                errs.append("0f(vi): lock `target_triples` must be a non-empty list of target triple strings")
            else:
                triples = [str(t).strip() for t in raw_tt if str(t).strip()]
        elif raw_t1 is not None:
            t1_s = str(raw_t1).strip()
            if not t1_s:
                errs.append("0f(vi): lock `target_triple` must be a non-empty string")
            else:
                triples = [t1_s]

    if not triples and repo_root is not None and (repo_root / "rust-toolchain.toml").is_file():
        try:
            rt_cfg = tomllib.loads((repo_root / "rust-toolchain.toml").read_text(encoding="utf-8"))
            tc_sec = rt_cfg.get("toolchain")
            if isinstance(tc_sec, Mapping) and isinstance(tc_sec.get("targets"), list):
                parsed_t = [str(x).strip() for x in tc_sec["targets"] if str(x).strip()]
                if parsed_t:
                    triples = parsed_t
        except Exception as exc:  # noqa: BLE001
            errs.append(f"0f(vi): failed to parse `{repo_root / 'rust-toolchain.toml'}`: {exc}")

    if not triples:
        triples = ["aarch64-unknown-linux-gnu"]

    for t in triples:
        if not t.startswith("aarch64-"):
            errs.append(
                f"0f(vi): image target triple {t!r} is incompatible with `EM_AARCH64` ELF (expected `aarch64-*`)"
            )
    return sorted(dict.fromkeys(triples)), errs


def _discover_rlib_search_roots(
    search_roots: Sequence[pathlib.Path],
    repo_root: pathlib.Path | None,
    eff_sysroot: pathlib.Path | None = None,
    target_triples: Sequence[str] | None = None,
) -> list[pathlib.Path]:
    roots: list[pathlib.Path] = list(search_roots)
    if repo_root is not None and repo_root.is_dir():
        roots.append(repo_root)
    if eff_sysroot is not None and (eff_sysroot / "lib/rustlib").is_dir():
        eff_triples = list(target_triples) if target_triples else ["aarch64-unknown-linux-gnu"]
        for t in eff_triples:
            lib_dir = eff_sysroot / "lib/rustlib" / t / "lib"
            if lib_dir.is_dir():
                roots.append(lib_dir)
    return roots


def _compare_trimmed_reloc_sections(
    linked_obj: elf_inspect.RelocObject,
    ref_obj: elf_inspect.RelocObject,
    keep_sections: Sequence[str],
    label: str,
) -> list[str]:
    """Verify section-subset fidelity (`stockpin_exit_list.md` §0f(vi) / GK 466 N-b):
    exact `keep_sections` set, identical section headers/bytes/relocs, and exact symtab fidelity
    (no added, renamed, dropped, or rebound non-local symbols on kept sections)."""
    errs: list[str] = []
    exp_keep = set(str(s) for s in keep_sections)
    got_alloc = {
        s.name
        for s in linked_obj.sections
        if (s.sh_flags & elf_inspect.SHF_ALLOC) != 0 and s.sh_type != elf_inspect.SHT_NULL
    }
    if got_alloc != exp_keep:
        errs.append(
            f"0f(vi) / GK 458 C1(a): {label} SHF_ALLOC sections {sorted(got_alloc)} != keep_sections {sorted(exp_keep)}"
        )
    for sec_name in sorted(got_alloc & exp_keep):
        l_secs = linked_obj.sec_by_name.get(sec_name, [])
        r_secs = ref_obj.sec_by_name.get(sec_name, [])
        if len(l_secs) != 1 or len(r_secs) != 1:
            errs.append(
                f"0f(vi): {label} section {sec_name!r} count linked={len(l_secs)} vs rlib_member={len(r_secs)}"
            )
            continue
        ls, rs = l_secs[0], r_secs[0]
        if (ls.sh_type, ls.sh_flags, ls.sh_size) != (rs.sh_type, rs.sh_flags, rs.sh_size):
            errs.append(
                f"0f(vi): {label} section {sec_name!r} header mismatch linked={(ls.sh_type, ls.sh_flags, ls.sh_size)} "
                f"!= rlib_member={(rs.sh_type, rs.sh_flags, rs.sh_size)}"
            )
        if ls.data != rs.data:
            errs.append(
                f"0f(vi): {label} section {sec_name!r} raw bytes differ from rlib member"
            )
        l_rel = _canonicalize_reloc_list(elf_inspect.format_section_relocs(linked_obj, ls))
        r_rel = _canonicalize_reloc_list(elf_inspect.format_section_relocs(ref_obj, rs))
        if l_rel != r_rel:
            errs.append(
                f"0f(vi): {label} section {sec_name!r} relocs differ from rlib member"
            )

    # GK 466 N-b: exact non-local symbol set & bindings across kept sections (cannot add, drop, or rename symbols)
    expected_kept_defs: dict[str, tuple[int, int, int, int, int, str]] = {}
    for rsym in ref_obj.symbols:
        if rsym.is_local or rsym.is_undefined or rsym.st_shndx >= len(ref_obj.sections):
            continue
        rsec_name = ref_obj.sections[rsym.st_shndx].name
        if rsec_name in exp_keep:
            expected_kept_defs[rsym.name] = (
                rsym.bind,
                rsym.stype,
                rsym.st_other,
                rsym.st_value,
                rsym.st_size,
                rsec_name,
            )

    got_defs: dict[str, tuple[int, int, int, int, int, str]] = {}
    for lsym in linked_obj.symbols:
        if lsym.is_local or lsym.is_undefined:
            continue
        lsec_name = linked_obj.sections[lsym.st_shndx].name if lsym.st_shndx < len(linked_obj.sections) else ""
        got_defs[lsym.name] = (
            lsym.bind,
            lsym.stype,
            lsym.st_other,
            lsym.st_value,
            lsym.st_size,
            lsec_name,
        )

    if set(got_defs.keys()) != set(expected_kept_defs.keys()):
        errs.append(
            f"0f(vi) / GK 466 N-b: {label} defined non-local symbol set mismatch vs kept member sections: "
            f"added/renamed={sorted(set(got_defs.keys()) - set(expected_kept_defs.keys()))}, "
            f"missing={sorted(set(expected_kept_defs.keys()) - set(got_defs.keys()))}"
        )
    for sname in sorted(set(got_defs.keys()) & set(expected_kept_defs.keys())):
        if got_defs[sname] != expected_kept_defs[sname]:
            errs.append(
                f"0f(vi) / GK 466 N-b: {label} symbol {sname!r} metadata/binding mismatch "
                f"linked={got_defs[sname]} != member={expected_kept_defs[sname]}"
            )
    return errs


def _find_matching_rel_section(
    obj: elf_inspect.RelocObject,
    map_sec: elf_inspect.MapInputSection,
) -> elf_inspect.RelSection:
    if map_sec.sec_name == "COMMON":
        common_syms = [s for s in obj.symbols if not s.is_local and s.st_shndx == elf_inspect.SHN_COMMON]
        if not common_syms:
            raise KeyError(f"{obj.label}: retained map section 'COMMON' not found in object")
        map_sym_names = {ms.name for ms in map_sec.symbols if not ms.name.startswith("$")}
        if map_sym_names and not any(
            (s.name in map_sym_names or s.demangled in map_sym_names) for s in common_syms
        ):
            raise KeyError(
                f"{obj.label}: 'COMMON' symbols {[s.name for s in common_syms]} do not match map {sorted(map_sym_names)}"
            )
        return elf_inspect.RelSection(
            idx=elf_inspect.SHN_COMMON,
            name="COMMON",
            sh_type=elf_inspect.SHT_NOBITS,
            sh_flags=elf_inspect.SHF_ALLOC,
            sh_addr=0,
            sh_offset=0,
            sh_size=map_sec.size,
            sh_link=0,
            sh_info=0,
            sh_addralign=1,
            sh_entsize=0,
            data=b"",
            relocs=(),
        )

    cands = obj.sec_by_name.get(map_sec.sec_name, [])
    if len(cands) == 1:
        return cands[0]
    if len(cands) > 1:
        # Disambiguate COMDAT / duplicate-named sections by symbol names or exact size
        map_sym_names = {ms.name for ms in map_sec.symbols if not ms.name.startswith("$")}
        if map_sym_names:
            filtered = [
                sec
                for sec in cands
                if any(
                    (s.name in map_sym_names or s.demangled in map_sym_names)
                    for s in obj.symbols
                    if s.st_shndx == sec.idx
                )
            ]
            if len(filtered) == 1:
                return filtered[0]
        if map_sec.piece_offset is None:
            sz_filtered = [sec for sec in cands if sec.sh_size == map_sec.size]
            if len(sz_filtered) == 1:
                return sz_filtered[0]
        return cands[0]
    raise KeyError(f"{obj.label}: retained map section {map_sec.sec_name!r} not found in object")


def _find_matching_archive_member(
    mem_cands: Sequence[elf_inspect.ArchiveMember],
    map_sec: elf_inspect.MapInputSection,
) -> tuple[elf_inspect.ArchiveMember, elf_inspect.RelSection]:
    matches: list[tuple[elf_inspect.ArchiveMember, elf_inspect.RelSection]] = []
    last_err: Exception | None = None
    for mem in mem_cands:
        try:
            rsec = _find_matching_rel_section(mem.obj, map_sec)
            matches.append((mem, rsec))
        except KeyError as exc:
            last_err = exc
    if len(matches) == 1:
        return matches[0]
    if len(matches) > 1:
        map_sym_names = {ms.name for ms in map_sec.symbols if not ms.name.startswith("$")}
        if map_sym_names:
            sym_matches = [
                (m, s)
                for m, s in matches
                if any(
                    (sym.name in map_sym_names or sym.demangled in map_sym_names)
                    for sym in m.obj.symbols
                    if sym.st_shndx == s.idx
                )
            ]
            if len(sym_matches) == 1:
                return sym_matches[0]
        if map_sec.piece_offset is None:
            sz_matches = [(m, s) for m, s in matches if s.sh_size == map_sec.size]
            if len(sz_matches) == 1:
                return sz_matches[0]
        return matches[0]
    if last_err is not None:
        raise last_err
    raise KeyError(f"no archive member matched {map_sec.sec_name!r}")


def verify_report_against_lock(
    report: ALinkReport,
    lock: Mapping[str, Any],
    *,
    repo_root: pathlib.Path | None = None,
) -> list[str]:
    """Rule (vii) change 5 + GK row 375: fail-on-diff check of `ALinkReport` against lock."""
    errs: list[str] = []

    def chk_eq(field_label: str, got: Any, exp: Any) -> None:
        if got != exp:
            errs.append(f"Lock diff `{field_label}`: got={got!r} != lock={exp!r}")

    if "x_count" in lock:
        chk_eq("x_count", report.x_count, int(lock["x_count"]))
    if "x_sha256" in lock:
        chk_eq("x_sha256", report.x_sha256, str(lock["x_sha256"]))
    if "x_per_image" in lock and isinstance(lock["x_per_image"], Mapping):
        for k, exp_list in lock["x_per_image"].items():
            chk_eq(f"x_per_image[{k}]", report.x_per_image.get(str(k)), list(exp_list))

    exp_he_sha = lock.get("engine_hooked_externs_sha256")
    if exp_he_sha and exp_he_sha != "TODO_TEJ_ENGINE_PR_1548" and report.engine_hooked_externs_sha256 is not None:
        chk_eq("engine_hooked_externs_sha256", report.engine_hooked_externs_sha256, str(exp_he_sha))

    for list_key, got_list in (
        ("real_hook_reached", report.real_hook_reached),
        ("real_proved", report.real_proved),
        ("failstop_z", report.failstop_z),
        ("discarded", report.discarded),
        ("weakened_in_main", report.weakened_in_main),
        ("exempted_aliases", report.exempted_aliases),
        ("weak_undefined_allowed", report.weak_undefined_allowed),
        ("displaced_weak", report.displaced_weak),
        ("displaced_weak_referrers", report.displaced_weak_referrers),
    ):
        if list_key in lock:
            chk_eq(list_key, got_list, [str(x) for x in lock[list_key]])

    if "elf_sha256" in lock:
        chk_eq("elf_sha256", report.elf_sha256, str(lock["elf_sha256"]))
    if "elf_size" in lock:
        chk_eq("elf_size", report.elf_size, int(lock["elf_size"]))
    if "engine_commit" in lock and str(lock["engine_commit"]):
        chk_eq("engine_commit", report.engine_commit, str(lock["engine_commit"]))
    if "rustc_version" in lock and str(lock["rustc_version"]):
        chk_eq("rustc_version", report.rustc_version, str(lock["rustc_version"]))
    if "zig_version" in lock and str(lock["zig_version"]):
        chk_eq("zig_version", report.zig_version, str(lock["zig_version"]))
    if "lld_version_prefix" in lock and str(lock["lld_version_prefix"]):
        pfx = str(lock["lld_version_prefix"])
        if not report.lld_version.startswith(pfx):
            errs.append(f"Lock diff `lld_version`: {report.lld_version!r} does not start with {pfx!r}")
    if "lld_argv" in lock and isinstance(lock["lld_argv"], Sequence):
        chk_eq("lld_argv", report.lld_argv, [str(x) for x in lock["lld_argv"]])
    if "stock_lld_arg_files" in lock and isinstance(lock["stock_lld_arg_files"], Mapping):
        chk_eq(
            "stock_lld_arg_files",
            report.stock_lld_arg_files,
            {str(k): str(v) for k, v in lock["stock_lld_arg_files"].items()},
        )
    if "stub_object" in lock and isinstance(lock["stub_object"], Mapping):
        e_st = lock["stub_object"]
        for fk in ("name", "sha256", "size", "symbol_count"):
            if fk in e_st and e_st[fk] is not None:
                chk_eq(f"stub_object.{fk}", report.stub_object.get(fk), e_st[fk])
    if "g6_rebuild_pins" in lock and isinstance(lock["g6_rebuild_pins"], Mapping):
        e_g6 = lock["g6_rebuild_pins"]
        if "harness_object" in e_g6 and isinstance(e_g6["harness_object"], Mapping):
            eh = e_g6["harness_object"]
            for fk in ("name", "sha256", "size"):
                if fk in eh and eh[fk] is not None:
                    chk_eq(f"g6_rebuild_pins.harness_object.{fk}", report.harness_object.get(fk), eh[fk])
        if "compiler_builtins" in e_g6 and isinstance(e_g6["compiler_builtins"], Mapping):
            ecb = e_g6["compiler_builtins"]
            if report.compiler_builtins_archive is None:
                errs.append("Lock diff `g6_rebuild_pins.compiler_builtins`: missing `compiler_builtins.a` in link")
            else:
                for fk in ("name", "sha256", "size"):
                    if fk in ecb and ecb[fk] is not None:
                        chk_eq(
                            f"g6_rebuild_pins.compiler_builtins.{fk}",
                            report.compiler_builtins_archive.get(fk),
                            ecb[fk],
                        )

    w3_pin = lock.get("w3_pin")
    if isinstance(w3_pin, Mapping):
        if "elf_sha256" in w3_pin:
            chk_eq("w3_pin.elf_sha256", report.elf_sha256, str(w3_pin["elf_sha256"]))
        if "elf_size" in w3_pin:
            chk_eq("w3_pin.elf_size", report.elf_size, int(w3_pin["elf_size"]))
        if "main_elf_addr" in w3_pin:
            chk_eq("w3_pin.main_elf_addr", int(report.main_elf_addr, 16), int(str(w3_pin["main_elf_addr"]), 0))
        lean_pin_rel = w3_pin.get("lean_pin_path")
        if lean_pin_rel and repo_root is not None:
            lp = (repo_root / str(lean_pin_rel)).resolve()
            try:
                lpin = elf_inspect.parse_cli_elf_pin(lp)
                chk_eq("w3_pin.lean_pin_sha256", report.elf_sha256, lpin)
            except Exception as exc:  # noqa: BLE001
                errs.append(f"Lock W3 Lean pin check failed on {lp}: {exc}")

    if "runtime_archives" in lock and isinstance(lock["runtime_archives"], Mapping):
        chk_eq(
            "runtime_archives",
            report.runtime_archives,
            {str(k): str(v) for k, v in lock["runtime_archives"].items()},
        )

    has_nat_tbl, parsed_lock_nat = _parse_lock_native_objects(lock)
    parsed_lock_re, re_parse_errs = _parse_lock_rust_extracted(lock)
    errs.extend(re_parse_errs)
    if not has_nat_tbl:
        errs.append("0f(i) / SR-31 A2 / GK 458: lock is missing required positive-list `native_objects` mapping")
    else:
        overlap_n_re = sorted(set(parsed_lock_nat.keys()) & set(parsed_lock_re.keys()))
        if overlap_n_re:
            errs.append(
                f"0f(ii): Class N object(s) {overlap_n_re} appear in BOTH lock `native_objects` and `rust_extracted`"
            )
        exp_nat = {
            k: str(v.get("sha256") or "")
            for k, v in sorted(parsed_lock_nat.items())
            if k not in parsed_lock_re
        }
        chk_eq("native_objects", report.native_objects, exp_nat)

    if parsed_lock_re or report.rust_extracted or "rust_extracted" in lock:
        exp_re_keys = sorted(parsed_lock_re.keys())
        got_re_keys = sorted(report.rust_extracted.keys())
        chk_eq("rust_extracted.keys", got_re_keys, exp_re_keys)
        for rek in sorted(set(exp_re_keys) & set(got_re_keys)):
            e_re = parsed_lock_re[rek]
            g_re = report.rust_extracted[rek]
            for fk in ("kind", "sha256", "rlib_sha256", "member", "member_sha256", "asm_sha256", "recipe", "keep_sections"):
                if fk in e_re and e_re[fk] is not None and e_re[fk] != "":
                    chk_eq(f"rust_extracted[{rek!r}].{fk}", g_re.get(fk), e_re[fk])

    if "definers" in lock and isinstance(lock["definers"], Mapping):
        exp_defs = lock["definers"]
        got_keys = set(report.definers.keys())
        exp_keys = set(str(k) for k in exp_defs.keys())
        if got_keys != exp_keys:
            errs.append(
                f"Lock diff `definers` key mismatch: extra={sorted(got_keys - exp_keys)}, "
                f"missing={sorted(exp_keys - got_keys)}"
            )
        for sym in sorted(got_keys & exp_keys):
            g_row = report.definers[sym]
            e_row = exp_defs[sym]
            if not isinstance(e_row, Mapping):
                errs.append(f"Lock `definers[{sym!r}]` is not a table")
                continue
            for fk in (
                "class",
                "source_file",
                "archive_member",
                "sha256",
                "archive_sha256",
                "input_binding",
                "body_sha256",
                "byte_equal",
            ):
                if fk in e_row and e_row[fk] is not None:
                    chk_eq(f"definers[{sym!r}].{fk}", g_row.get(fk), e_row[fk])
            if "elf_addr" in e_row and e_row["elf_addr"] is not None and g_row.get("elf_addr") is not None:
                chk_eq(
                    f"definers[{sym!r}].elf_addr",
                    int(str(g_row["elf_addr"]), 0),
                    int(str(e_row["elf_addr"]), 0),
                )

    for addr_map_key in ("displaced_weak_elf_addrs", "alpha_displaced_weak_elf_addrs"):
        if addr_map_key in lock and isinstance(lock[addr_map_key], Mapping):
            e_amap = lock[addr_map_key]
            chk_eq(
                f"{addr_map_key}.keys",
                sorted(report.displaced_weak_elf_addrs.keys()),
                sorted(str(k) for k in e_amap.keys()),
            )
            for ak in sorted(report.displaced_weak_elf_addrs.keys() & set(str(k) for k in e_amap.keys())):
                chk_eq(
                    f"{addr_map_key}[{ak!r}]",
                    int(str(report.displaced_weak_elf_addrs[ak]), 0),
                    int(str(e_amap[ak]), 0),
                )

    if "s2_real_body_lock" in lock and isinstance(lock["s2_real_body_lock"], Mapping):
        exp_s2 = lock["s2_real_body_lock"]
        got_s2_keys = set(report.s2_real_body_lock.keys())
        exp_s2_keys = set(str(k) for k in exp_s2.keys())
        if got_s2_keys != exp_s2_keys:
            errs.append(
                f"Lock diff `s2_real_body_lock` keys: got={sorted(got_s2_keys)} != lock={sorted(exp_s2_keys)}"
            )
        for sym in sorted(got_s2_keys & exp_s2_keys):
            g_s2 = report.s2_real_body_lock[sym]
            e_s2 = exp_s2[sym]
            if not isinstance(e_s2, Mapping):
                errs.append(f"Lock `s2_real_body_lock[{sym!r}]` is not a table")
                continue
            # A-LINK v0.3.2 rule (vii): `strlen.lo` extracted from pinned rustc 1.98.1 `libc.a`
            # may be recorded in builder locks via `strlen_source_override` (`definer_class="R"`,
            # `source_file="libc.a"`, `archive_member="strlen.lo"`) when linked as standalone `strlen.lo`.
            strlen_repinned_equiv = (
                sym == "strlen"
                and g_s2.get("definer_class") == "N"
                and g_s2.get("source_file") == "strlen.lo"
                and g_s2.get("n_object_file_sha") == elf_inspect.PINNED_STRLEN_MEMBER_SHA256
                and e_s2.get("definer_class") == "R"
                and e_s2.get("source_file") == "libc.a"
                and e_s2.get("archive_member") == "strlen.lo"
                and e_s2.get("archive_sha") == elf_inspect.PINNED_RUSTC_MUSL_LIBC_SHA256
                and e_s2.get("member_file_sha") == elf_inspect.PINNED_STRLEN_MEMBER_SHA256
            )
            for fk in (
                "definer_class",
                "size",
                "input_section",
                "source_file",
                "archive_member",
                "input_binding",
                "n_object_file_sha",
                "archive_sha",
                "member_name",
                "member_file_sha",
                "text_sha",
                "body_sha256",
                "byte_equal",
                "n_text_relocs",
                "member_text_relocs",
            ):
                if strlen_repinned_equiv and fk in ("definer_class", "source_file", "archive_member"):
                    continue
                if fk in e_s2 and e_s2[fk] is not None:
                    chk_eq(f"s2_real_body_lock[{sym!r}].{fk}", g_s2.get(fk), e_s2[fk])
            if "relocs" in e_s2 and e_s2["relocs"] is not None:
                chk_eq(
                    f"s2_real_body_lock[{sym!r}].relocs",
                    _canonicalize_reloc_list(g_s2.get("relocs")),
                    _canonicalize_reloc_list(e_s2["relocs"]),
                )
            if "elf_addr" in e_s2 and e_s2["elf_addr"] is not None:
                chk_eq(
                    f"s2_real_body_lock[{sym!r}].elf_addr",
                    int(str(g_s2["elf_addr"]), 0),
                    int(str(e_s2["elf_addr"]), 0),
                )

    if "d1_extern_data_lock" in lock and isinstance(lock["d1_extern_data_lock"], Mapping):
        e_d1 = lock["d1_extern_data_lock"]
        g_d1 = report.d1_extern_data_lock
        if "gc_dead" in e_d1:
            chk_eq("d1_extern_data_lock.gc_dead", g_d1["gc_dead"], list(e_d1["gc_dead"]))
        if "kept" in e_d1 and isinstance(e_d1["kept"], Mapping):
            chk_eq(
                "d1_extern_data_lock.kept.keys",
                sorted(g_d1["kept"].keys()),
                sorted(str(k) for k in e_d1["kept"].keys()),
            )
            for k in sorted(g_d1["kept"].keys() & set(str(x) for x in e_d1["kept"].keys())):
                ek = e_d1["kept"][k]
                gk = g_d1["kept"][k]
                for fk in ("definer_class", "size", "source_file", "sha256"):
                    if fk in ek and ek[fk] is not None:
                        chk_eq(f"d1_extern_data_lock.kept[{k!r}].{fk}", gk.get(fk), ek[fk])

    nonempty_report_undefs = {k: v for k, v in report.n_undef_map.items() if v}
    if "n_undef_map" not in lock or not isinstance(lock["n_undef_map"], Mapping):
        if nonempty_report_undefs:
            errs.append(
                "GK 458 C4: lock is missing required `n_undef_map` for Class N object(s) with undefined references: "
                f"{sorted(nonempty_report_undefs.keys())}"
            )
    else:
        e_num = lock["n_undef_map"]
        e_nonempty_keys = sorted(
            str(k) for k, v in e_num.items() if isinstance(v, Mapping) and len(v) > 0
        )
        g_nonempty_keys = sorted(nonempty_report_undefs.keys())
        # Enforce full key set when lock includes empty tables too, and always enforce all non-empty objects
        e_all_keys = sorted(str(k) for k in e_num.keys())
        g_all_keys = sorted(report.n_undef_map.keys())
        if set(e_all_keys) == set(g_all_keys):
            chk_eq("n_undef_map.objects", g_all_keys, e_all_keys)
        else:
            missing_nonempty = sorted(set(g_nonempty_keys) - set(e_all_keys))
            extra_lock_objs = sorted(set(e_all_keys) - set(g_all_keys))
            if missing_nonempty or extra_lock_objs or g_nonempty_keys != e_nonempty_keys:
                errs.append(
                    f"Lock diff `n_undef_map.objects`: active_undef_objs={g_nonempty_keys} "
                    f"(all_n={g_all_keys}) != lock={e_all_keys}"
                )
        for nobj in sorted(set(report.n_undef_map.keys()) & set(e_all_keys)):
            e_sub = e_num[nobj]
            g_sub = report.n_undef_map[nobj]
            if not isinstance(e_sub, Mapping):
                errs.append(f"Lock `n_undef_map[{nobj!r}]` must be a mapping")
                continue
            chk_eq(f"n_undef_map[{nobj!r}].syms", sorted(g_sub.keys()), sorted(str(k) for k in e_sub.keys()))
            for usym in sorted(g_sub.keys() & set(str(k) for k in e_sub.keys())):
                eu = e_sub[usym]
                gu = g_sub[usym]
                if isinstance(eu, Mapping):
                    for fk in ("class", "source_file", "archive_member", "sha256"):
                        if fk in eu and eu[fk] is not None:
                            chk_eq(f"n_undef_map[{nobj!r}][{usym!r}].{fk}", gu.get(fk), eu[fk])

    return errs


def check_stock_link(
    *,
    out_dir: pathlib.Path | None = None,
    work_dir: pathlib.Path | None = None,
    elf_path: pathlib.Path | None = None,
    map_path: pathlib.Path | None = None,
    stock_link_json: pathlib.Path | None = None,
    cv_stock_link_json: pathlib.Path | None = None,
    repo_root: pathlib.Path | None = None,
    rustc_libc_a_path: pathlib.Path | None = None,
    toolchain_sysroot: pathlib.Path | None = None,
    trace_log_path: pathlib.Path | None = None,
    lock_path: pathlib.Path | None = None,
    inputs_lock_path: pathlib.Path | None = None,
    ci: bool = False,
    atomics_mode: str = "alpha",
    raise_on_error: bool = True,
) -> ALinkReport:
    """Run all P8 / A-LINK v0.3.2 / GK row 365–375 / K2 checks and return `ALinkReport`."""
    errors: list[str] = []
    if atomics_mode not in ("alpha", "beta"):
        raise ValueError(f"unsupported atomics_mode={atomics_mode!r} (expected 'alpha' or 'beta')")

    eff_repo_root = repo_root.resolve() if repo_root is not None and repo_root.exists() else (
        SCRIPT_DIR.parent.parent if repo_root is None else None
    )
    if eff_repo_root is not None and (
        not (eff_repo_root / "third_party/libsignal").exists()
        and not (eff_repo_root / "AGENTS.md").exists()
    ):
        eff_repo_root = None

    # GK row 492 K2 + SR-62 (1): validate `--ci` / `--inputs-lock` / `--lock` up front (single-read, fail-closed)
    k2_errs, inputs_lock_pin_summary, lock_raw_bytes = _verify_k2_inputs_lock(
        ci=ci,
        inputs_lock_path=inputs_lock_path,
        lock_path=lock_path,
        repo_root=repo_root,
        eff_repo_root=eff_repo_root,
    )
    errors.extend(k2_errs)

    lock_data: dict[str, Any] | None = None
    if lock_path is not None and lock_raw_bytes is not None:
        try:
            lock_data = _load_lock_bytes(lock_raw_bytes, lock_path)
        except (UnicodeDecodeError, tomllib.TOMLDecodeError, json.JSONDecodeError, ValueError) as exc:
            errors.append(f"K2 (--lock): invalid lock file {str(lock_path)!r}: {exc}")

    if raise_on_error and errors:
        raise ALinkError(errors)

    defaulted_out_dir = False
    if (
        out_dir is None
        and stock_link_json is None
        and cv_stock_link_json is None
        and elf_path is None
    ):
        default_root = repo_root.resolve() if repo_root is not None else SCRIPT_DIR.parent.parent
        out_dir = default_root / DEFAULT_REL_OUT_DIR
        defaulted_out_dir = True

    if out_dir is not None:
        out_dir = out_dir.resolve()
        if cv_stock_link_json is None and (out_dir / "cv-stock-link.json").is_file():
            cv_stock_link_json = out_dir / "cv-stock-link.json"
        if stock_link_json is None and (out_dir / "stock-link.json").is_file():
            stock_link_json = out_dir / "stock-link.json"
        if work_dir is None and (out_dir / "work").is_dir():
            work_dir = out_dir / "work"
    if stock_link_json is None and work_dir is not None and (work_dir / "stock_stage" / "stock-link.json").is_file():
        stock_link_json = work_dir / "stock_stage" / "stock-link.json"
        if defaulted_out_dir and cv_stock_link_json is None:
            out_dir = None

    cv_meta: dict[str, Any] | None = None
    eng_meta: dict[str, Any] | None = None
    if cv_stock_link_json is not None:
        cv_meta = json.loads(cv_stock_link_json.read_text(encoding="utf-8"))
    if stock_link_json is not None:
        eng_meta = json.loads(stock_link_json.read_text(encoding="utf-8"))
    if cv_meta is None and eng_meta is None:
        if errors:
            raise ALinkError(errors)
        tried = f" in {out_dir}" if out_dir is not None else ""
        raise ValueError(
            f"neither `cv-stock-link.json` nor `stock-link.json` found{tried}; pass `--out-dir` or metadata path"
        )

    recipe = "builder" if cv_meta is not None else "engine"
    base_dir = (
        out_dir
        or (cv_stock_link_json.parent if cv_stock_link_json else None)
        or (stock_link_json.parent if stock_link_json else None)
    )
    assert base_dir is not None
    eff_work = work_dir.resolve() if work_dir is not None else (base_dir / "work")
    search_roots = [r for r in (base_dir, eff_work) if r.exists()]

    # Locate ELF & link.map
    if elf_path is None:
        if recipe == "builder":
            assert cv_meta is not None
            elf_name = str(
                cv_meta.get("elf_name")
                or (cv_meta.get("elf", {}).get("name") if isinstance(cv_meta.get("elf"), Mapping) else None)
                or "signal-session-stock.elf"
            )
        else:
            assert eng_meta is not None
            elf_name = str(eng_meta["elf"]["name"])
        elf_path = base_dir / elf_name
    elf_path = elf_path.resolve()

    if map_path is None:
        for cand_m in (base_dir / "link.map", eff_work / "link.map"):
            if cand_m.is_file():
                map_path = cand_m
                break
    if map_path is None or not map_path.is_file():
        raise FileNotFoundError(f"link.map not found under {base_dir} or {eff_work}; pass `--map`")
    map_path = map_path.resolve()

    # Load trusted hook & panic symbol tables + muslStrlenWords
    hook_table_keys, panic_table_keys = elf_inspect.load_cli_hook_and_panic_tables(eff_repo_root)
    musl_strlen_bytes = elf_inspect.load_musl_strlen_bytes(eff_repo_root)

    # Parse linked ET_EXEC ELF & ld.lld -Map
    elf = elf_inspect.parse_exec_elf(elf_path.read_bytes(), str(elf_path))
    lmap = elf_inspect.parse_lld_map(map_path.read_text(encoding="utf-8"), str(map_path))

    # Verify ELF digest against metadata
    if recipe == "builder":
        assert cv_meta is not None
        meta_elf_sha = str(
            cv_meta.get("elf_sha256")
            or (cv_meta.get("elf", {}).get("sha256") if isinstance(cv_meta.get("elf"), Mapping) else "")
        )
        meta_elf_sz = int(
            cv_meta.get("elf_size")
            or (cv_meta.get("elf", {}).get("size") if isinstance(cv_meta.get("elf"), Mapping) else 0)
        )
    else:
        assert eng_meta is not None
        meta_elf_sha = str(eng_meta["elf"]["sha256"])
        meta_elf_sz = int(eng_meta["elf"]["size"])
    if meta_elf_sha and elf.sha256 != meta_elf_sha:
        errors.append(f"ELF sha256 {elf.sha256} != metadata {meta_elf_sha}")
    if meta_elf_sz and elf.size != meta_elf_sz:
        errors.append(f"ELF size {elf.size} != metadata {meta_elf_sz}")
    if recipe == "builder" and cv_meta is not None:
        exp_eng_sl_sha = str(cv_meta.get("engine_stock_link_json_sha256") or "")
        if exp_eng_sl_sha and stock_link_json is not None and stock_link_json.is_file():
            got_eng_sl_sha = elf_inspect.sha256_file(stock_link_json)
            if got_eng_sl_sha != exp_eng_sl_sha:
                errors.append(
                    f"stock-link.json sha256 {got_eng_sl_sha} != cv-stock-link.json "
                    f"engine_stock_link_json_sha256 {exp_eng_sl_sha}"
                )
        exp_lmap_sha = str(cv_meta.get("link_map_sha256") or "")
        if exp_lmap_sha:
            got_lmap_sha = elf_inspect.sha256_file(map_path)
            if got_lmap_sha != exp_lmap_sha:
                errors.append(f"link.map sha256 {got_lmap_sha} != cv-stock-link.json {exp_lmap_sha}")

    # Extract lld argv, version, and argFiles for Rule (iv)
    if recipe == "builder":
        assert cv_meta is not None
        lld_argv_tmpl = [str(x) for x in cv_meta.get("lld_argv", [])]
        lld_argv_raw = [str(x) for x in cv_meta.get("lld_argv_raw", lld_argv_tmpl)]
        lld_version = str(cv_meta.get("lld_version", ""))
        arg_files = {str(k): str(v) for k, v in cv_meta.get("stock_lld_arg_files", {}).items()}
        rustc_ver = str(cv_meta.get("rustc_version", ""))
        zig_ver = str(cv_meta.get("zig_version", ""))
        engine_commit = str(cv_meta.get("engine_commit", ""))
    else:
        assert eng_meta is not None
        lld_sec = eng_meta.get("lld", {})
        lld_argv_tmpl = [str(x) for x in lld_sec.get("args", [])]
        lld_argv_raw = list(lld_argv_tmpl)
        lld_version = str(lld_sec.get("version", ""))
        arg_files = {}
        for af in lld_sec.get("argFiles", []):
            if isinstance(af, Mapping) and af.get("path") and af.get("sha256"):
                arg_files[str(af["path"])] = str(af["sha256"])
        rustc_ver = str(eng_meta.get("stdBin", {}).get("rustc", ""))
        zig_ver = str(eng_meta.get("zig", ""))
        engine_commit = str(eng_meta.get("trimmedSysrootObjects", {}).get("engineCommit", ""))

    _scan_lld_argv_for_banned_flags(lld_argv_tmpl, "lld_argv", errors)
    _scan_lld_argv_for_banned_flags(lld_argv_raw, "lld_argv_raw", errors)
    for af_rel, af_sha in sorted(arg_files.items()):
        if eff_repo_root is not None:
            af_disk = eff_repo_root / af_rel
            if af_disk.is_file():
                if elf_inspect.sha256_file(af_disk) != af_sha:
                    errors.append(f"Rule (iv): argFile {af_rel} sha256 != {af_sha}")
                af_txt = af_disk.read_text(encoding="utf-8")
                if "EXTERN(" in af_txt:
                    errors.append(f"Rule (iv): forbidden `EXTERN(...)` directive in linker script {af_rel}")

    # Stage & classify all translated Rust image configs (`configs[0..K-1]`)
    raw_configs: list[dict[str, Any]] = []
    if eng_meta is not None and isinstance(eng_meta.get("configs"), list):
        raw_configs = list(eng_meta["configs"])
    elif cv_meta is not None:
        cfg_rel = str(cv_meta.get("config_path", "third_party/libsignal/libsignal-session/translation.toml"))
        lib_entries = [
            {"name": inp["name"], "path": inp["name"], "sha256": inp["sha256"], "size": inp.get("size", 0)}
            for inp in cv_meta.get("inputs", [])
            if re.match(r"^lib0_\d+\.o$", str(inp.get("name", "")))
        ]
        raw_configs = [{"config": cfg_rel, "objects": lib_entries}]

    if not raw_configs:
        raise ValueError("zero translated Rust image configs discovered")

    image_records: list[list[InputRecord]] = []
    config_paths: list[str] = []
    declared_exports_by_img: dict[int, set[str]] = {}
    image_shas_to_role: dict[str, tuple[str, int, str]] = {}
    sysroot_trims_report: list[dict[str, Any]] = []

    for img_idx, cfg_entry in enumerate(raw_configs):
        cfg_rel = str(cfg_entry["config"])
        config_paths.append(cfg_rel)
        if eff_repo_root is not None and (eff_repo_root / cfg_rel).is_file():
            declared_exports_by_img[img_idx] = set(elf_inspect.load_config_declared_exports(eff_repo_root, cfg_rel))
        else:
            declared_exports_by_img[img_idx] = set()

        objs_for_img: list[InputRecord] = []
        for obj_meta in cfg_entry.get("objects", []):
            rel_p = str(obj_meta["path"])
            exp_sha = str(obj_meta["sha256"])
            disk_p = _resolve_staged_file(rel_p, search_roots, expected_sha256=exp_sha)
            raw_bytes = disk_p.read_bytes()
            got_sha = elf_inspect.sha256_bytes(raw_bytes)
            if got_sha != exp_sha:
                errors.append(f"Image {img_idx} object {rel_p} sha256 {got_sha} != {exp_sha}")
            parsed_o = elf_inspect.parse_reloc_obj(raw_bytes, disk_p.name)
            t_from = obj_meta.get("trimmedFrom")
            rec = InputRecord(
                role=f"S:{img_idx}",
                name=disk_p.name,
                rel_path=rel_p,
                disk_path=disk_p,
                sha256=got_sha,
                size=len(raw_bytes),
                image_idx=img_idx,
                obj=parsed_o,
                trimmed_from=t_from if isinstance(t_from, Mapping) else None,
            )
            objs_for_img.append(rec)
            image_shas_to_role[got_sha] = (f"S:{img_idx}", img_idx, disk_p.name)

            # P8-3: Verify trimmed sysroot object section keepSet
            if isinstance(t_from, Mapping):
                keep_rows = [str(x) for x in t_from.get("keepSet", [])]
                expected_kept_secs = {row.split("\t", 1)[-1] for row in keep_rows}
                actual_alloc_secs = {
                    s.name
                    for s in parsed_o.sections
                    if (s.sh_flags & elf_inspect.SHF_ALLOC) != 0 and s.sh_type != elf_inspect.SHT_NULL
                }
                if actual_alloc_secs != expected_kept_secs:
                    errors.append(
                        f"P8-3 trim mismatch in {disk_p.name} ({t_from.get('rlib')}): "
                        f"SHF_ALLOC sections {sorted(actual_alloc_secs)} != keepSet {sorted(expected_kept_secs)}"
                    )
                sysroot_trims_report.append({
                    "image_idx": img_idx,
                    "object": disk_p.name,
                    "object_sha256": got_sha,
                    "rlib": str(t_from.get("rlib", "")),
                    "member": str(t_from.get("member", "")),
                    "member_sha256": str(t_from.get("memberSha256", "")),
                    "keep_set_sha256": str(t_from.get("keepSetSha256", "")),
                    "kept_sections": sorted(expected_kept_secs),
                })
        image_records.append(objs_for_img)

    # Parse all other linked inputs from the authoritative link metadata (`cv_meta` for builder, `eng_meta` for engine)
    raw_link_inputs: list[dict[str, Any]] = (
        list(cv_meta.get("inputs", [])) if recipe == "builder" and cv_meta is not None else list(eng_meta.get("inputs", []))  # type: ignore[union-attr]
    )

    all_inputs: list[InputRecord] = []
    standalone_by_name: dict[str, InputRecord] = {}
    standalone_by_name_all: dict[str, list[InputRecord]] = {}
    standalone_by_path: dict[str, InputRecord] = {}
    archives_by_name: dict[str, InputRecord] = {}
    archives_by_name_all: dict[str, list[InputRecord]] = {}
    archives_by_path: dict[str, InputRecord] = {}
    image_by_resolved_path: dict[pathlib.Path, InputRecord] = {}
    seen_standalone_resolved_paths: set[pathlib.Path] = set()
    seen_archive_resolved_paths: set[pathlib.Path] = set()

    for img_objs in image_records:
        for r in img_objs:
            rp = r.disk_path.resolve()
            if rp in image_by_resolved_path:
                errors.append(
                    f"G-F1: duplicate registered image object path {r.rel_path!r} ({rp})"
                )
            image_by_resolved_path[rp] = r
            seen_standalone_resolved_paths.add(rp)
            all_inputs.append(r)
            standalone_by_name_all.setdefault(r.name, []).append(r)
            if len(standalone_by_name_all[r.name]) == 1:
                standalone_by_name[r.name] = r
            else:
                errors.append(
                    f"G-F1 / SR-42b: duplicate object basename {r.name!r} across distinct link inputs: "
                    f"{[x.rel_path for x in standalone_by_name_all[r.name]]}"
                )
            standalone_by_path[r.rel_path] = r
            standalone_by_path[str(r.disk_path)] = r
            standalone_by_path[str(rp)] = r

    # `--lock` was already single-read & validated up front (`lock_data`); enforce positive-list Class N & §0f(i)–(v)
    has_lock_nat_tbl, lock_native_objs = _parse_lock_native_objects(lock_data)
    lock_rust_extracted, lock_re_schema_errs = _parse_lock_rust_extracted(lock_data)
    errors.extend(lock_re_schema_errs)
    if has_lock_nat_tbl and lock_rust_extracted:
        overlap_early = sorted(set(lock_native_objs.keys()) & set(lock_rust_extracted.keys()))
        if overlap_early:
            errors.append(
                f"0f(ii): Class N object(s) {overlap_early} appear in BOTH lock `native_objects` and `rust_extracted`"
            )

    stub_record: InputRecord | None = None
    harness_record: InputRecord | None = None
    runtime_archives_map: dict[str, str] = {}
    native_objects_map: dict[str, str] = {}

    for inp_entry in raw_link_inputs:
        rel_p = str(inp_entry.get("path") or inp_entry.get("name") or "")
        exp_sha = str(inp_entry.get("sha256") or "")
        bname = pathlib.Path(rel_p).name
        try:
            disk_p = _resolve_staged_file(rel_p, search_roots, expected_sha256=exp_sha)
        except FileNotFoundError as exc:
            errors.append(f"G-F1: missing or ambiguous link input {rel_p!r}: {exc}")
            continue

        raw_bytes = disk_p.read_bytes()
        got_sha = elf_inspect.sha256_bytes(raw_bytes)
        rp = disk_p.resolve()
        if exp_sha and got_sha != exp_sha:
            errors.append(f"Input {rel_p} sha256 {got_sha} != metadata {exp_sha}")
        pinned_sha = inp_entry.get("pinnedSha256")
        if pinned_sha and got_sha != str(pinned_sha):
            errors.append(f"Input {rel_p} sha256 {got_sha} != pinnedSha256 {pinned_sha}")

        # G-F1 (GK row 477): skip `S:<i>` ONLY when BOTH the resolved on-disk path AND computed SHA-256
        # (and claimed metadata `exp_sha` when present) match the registered image object record.
        img_rec = image_by_resolved_path.get(rp)
        if (
            img_rec is not None
            and got_sha == img_rec.sha256
            and (not exp_sha or exp_sha == img_rec.sha256)
        ):
            standalone_by_path[rel_p] = img_rec
            continue

        is_ar_magic = raw_bytes.startswith((b"!<arch>\n", b"!<thin>\n"))
        if bname.endswith(".rlib") or (is_ar_magic and not bname.endswith(".a")):
            errors.append(
                f"0f(v): forbidden Rust `.rlib` or non-`.a` archive {bname!r} ({rel_p}) passed as link input"
            )
            continue

        if bname.endswith(".a"):
            if lock_data is not None:
                lock_ra = lock_data.get("runtime_archives")
                if not isinstance(lock_ra, Mapping) or bname not in lock_ra:
                    errors.append(
                        f"0f(v): archive {bname!r} ({rel_p}) passed as link input is not in lock `runtime_archives`"
                    )
            elif bname not in KNOWN_RUNTIME_ARCHIVE_BASENAMES:
                errors.append(
                    f"0f(v): unlisted archive {bname!r} ({rel_p}) passed as link input"
                )
            parsed_a = elf_inspect.parse_ar_archive(raw_bytes, bname)
            if bname != "compiler_builtins.a":
                for amem in parsed_a.members:
                    rc_comments = elf_inspect.extract_rustc_comments(amem.obj)
                    rm_syms = sorted(
                        {s.name for s in amem.obj.symbols if s.name and elf_inspect.is_strict_rust_symbol(s.name)}
                    )
                    if rc_comments or rm_syms:
                        errors.append(
                            f"SR-31 A2: runtime archive {bname}({amem.name}) contains forbidden Rust producer/symbols "
                            f"(comments={rc_comments}, syms={rm_syms[:4]})"
                        )
            rec = InputRecord(
                role="R",
                name=bname,
                rel_path=rel_p,
                disk_path=disk_p,
                sha256=got_sha,
                size=len(raw_bytes),
                archive=parsed_a,
            )
            if rp in seen_archive_resolved_paths:
                errors.append(f"G-F1: duplicate archive input path {rel_p!r} ({rp})")
            seen_archive_resolved_paths.add(rp)
            archives_by_name_all.setdefault(bname, []).append(rec)
            if len(archives_by_name_all[bname]) == 1:
                archives_by_name[bname] = rec
                runtime_archives_map[bname] = got_sha
            else:
                errors.append(
                    f"G-F1 / SR-42b: duplicate archive basename {bname!r} across distinct link inputs: "
                    f"{[x.rel_path for x in archives_by_name_all[bname]]}"
                )
            archives_by_path[rel_p] = rec
            archives_by_path[str(disk_p)] = rec
            archives_by_path[str(rp)] = rec
        else:
            parsed_o = elf_inspect.parse_reloc_obj(raw_bytes, bname)
            rustc_comments = elf_inspect.extract_rustc_comments(parsed_o)
            rust_mangled_syms = sorted(
                {s.name for s in parsed_o.symbols if s.name and elf_inspect.is_rust_mangled_symbol(s.name)}
            )

            if bname in STARTFILE_BASENAMES:
                role = "startfile"
                runtime_archives_map[bname] = got_sha
                if rustc_comments or rust_mangled_syms:
                    errors.append(
                        f"SR-31 A2: startfile {bname!r} contains forbidden `rustc` .comment or `_R`/`_ZN` symbol(s): "
                        f"comments={rustc_comments}, syms={rust_mangled_syms[:5]}"
                    )
            elif bname in HARNESS_BASENAMES:
                role = "harness"
                if recipe != "engine" or bname != "main_rust.o":
                    if rustc_comments or rust_mangled_syms:
                        errors.append(
                            f"SR-31 A2: harness {bname!r} contains forbidden `rustc` .comment or `_R`/`_ZN` symbol(s): "
                            f"comments={rustc_comments}, syms={rust_mangled_syms[:5]}"
                        )
                elif (rustc_comments or rust_mangled_syms) and lock_data is not None:
                    pinned_h_sha = ""
                    g6_tbl = lock_data.get("g6_rebuild_pins")
                    if isinstance(g6_tbl, Mapping) and isinstance(g6_tbl.get("harness_object"), Mapping):
                        pinned_h_sha = str(g6_tbl["harness_object"].get("sha256") or "")
                    if not pinned_h_sha or pinned_h_sha != got_sha:
                        errors.append(
                            f"SR-31 A2: Rust engine harness {bname!r} requires exact `g6_rebuild_pins.harness_object.sha256` pin in lock"
                        )
            elif "extern_stubs" in bname or bname.endswith("_stubs.o"):
                role = "Z"
                if rustc_comments:
                    errors.append(
                        f"SR-31 A2: Class Z stub object {bname!r} contains forbidden `rustc` .comment: {rustc_comments}"
                    )
                if parsed_o.undefs_by_name:
                    errors.append(
                        f"Rule (v)(Z): Class Z stub object {bname!r} has unexpected undefined symbol(s): "
                        f"{sorted(parsed_o.undefs_by_name.keys())[:5]}"
                    )
                for zsec in parsed_o.sections:
                    if (zsec.sh_flags & elf_inspect.SHF_ALLOC) != 0 and zsec.sh_type != elf_inspect.SHT_NULL:
                        if any(r.r_type not in elf_inspect.R_AARCH64_NONE_SET for r in zsec.relocs):
                            errors.append(
                                f"Rule (v)(Z): Class Z stub object {bname!r} section {zsec.name!r} has forbidden relocations"
                            )
                        if zsec.sh_type != elf_inspect.SHT_NOBITS and any(b != 0 for b in zsec.data):
                            errors.append(
                                f"Rule (v)(Z): Class Z stub object {bname!r} section {zsec.name!r} contains non-zero bytes"
                            )
            else:
                role = "N"
                in_re = bname in lock_rust_extracted
                if lock_data is not None:
                    if not (has_lock_nat_tbl and bname in lock_native_objs) and not in_re:
                        errors.append(
                            f"GK 458 / SR-31 A2: unlisted Class N object {bname!r} ({rel_p}) is in neither "
                            "lock `native_objects` nor `rust_extracted`"
                        )
                elif bname not in KNOWN_COMMITTED_NATIVE_BASENAMES:
                    errors.append(
                        f"GK 458 / SR-31 A2: unlisted standalone Class N object {bname!r} ({rel_p}); "
                        "pass `--lock` with positive-list `native_objects` / `rust_extracted`"
                    )

                if not in_re:
                    native_objects_map[bname] = got_sha
                    if rustc_comments:
                        errors.append(
                            f"SR-31 A2: non-`rust_extracted` object {bname!r} contains forbidden `rustc` .comment: "
                            f"{rustc_comments}"
                        )
                    if bname == "rdl_shim.o" and not rustc_comments:
                        bad_rust_syms = sorted(
                            {
                                *(
                                    s.name
                                    for s in parsed_o.symbols
                                    if s.name
                                    and elf_inspect.is_rust_mangled_symbol(s.name)
                                    and (s.is_undefined or not elf_inspect.is_rdl_shim_rustc_alloc_symbol(s.name))
                                )
                            }
                        )
                    else:
                        bad_rust_syms = rust_mangled_syms
                    if bad_rust_syms:
                        errors.append(
                            f"SR-31 A2: non-`rust_extracted` object {bname!r} defines/references forbidden "
                            f"Rust-mangled symbol(s): {bad_rust_syms[:5]}"
                        )
                else:
                    if lock_rust_extracted[bname].get("kind") == "alias_stub" and rustc_comments:
                        errors.append(
                            f"SR-31 A2 / GK 458 C1(b): `rust_extracted` alias_stub {bname!r} contains forbidden "
                            f"`rustc` .comment {rustc_comments} (must be assembled from `.S`)"
                        )

            rec = InputRecord(
                role=role,
                name=bname,
                rel_path=rel_p,
                disk_path=disk_p,
                sha256=got_sha,
                size=len(raw_bytes),
                obj=parsed_o,
            )
            if role == "Z":
                if stub_record is not None:
                    errors.append(f"Multiple Class Z stub objects linked: {stub_record.name} and {bname}")
                stub_record = rec
            elif role == "harness":
                if harness_record is not None:
                    errors.append(f"Multiple entry harness objects linked: {harness_record.name} and {bname}")
                harness_record = rec
            if rp in seen_standalone_resolved_paths:
                errors.append(f"G-F1: duplicate object input path {rel_p!r} ({rp})")
            seen_standalone_resolved_paths.add(rp)
            standalone_by_name_all.setdefault(bname, []).append(rec)
            if len(standalone_by_name_all[bname]) == 1:
                standalone_by_name[bname] = rec
            else:
                errors.append(
                    f"G-F1 / SR-42b: duplicate object basename {bname!r} across distinct link inputs: "
                    f"{[x.rel_path for x in standalone_by_name_all[bname]]}"
                )
            standalone_by_path[rel_p] = rec
            standalone_by_path[str(disk_p)] = rec
            standalone_by_path[str(rp)] = rec
        all_inputs.append(rec)

    if stub_record is None or stub_record.obj is None:
        raise ValueError("no Class Z zero-stub object (`*extern_stubs*.o`) found among linked inputs")
    if harness_record is None or harness_record.obj is None:
        raise ValueError("no entry harness object (`main.o` / `main_cli.o` / `main_rust.o`) found among linked inputs")

    # ==========================================================================
    # Step 1: Compute X_i = U_i \ D_i per image and X = ⋃_i X_i
    # ==========================================================================
    defs_per_img: list[set[str]] = []
    undefs_per_img: list[set[str]] = []
    x_per_image: dict[str, list[str]] = {}
    x_to_images: dict[str, set[int]] = {}
    sym_has_code_ref_in_img: set[str] = set()

    for img_idx, objs_for_img in enumerate(image_records):
        d_i: set[str] = set()
        u_i: set[str] = set()
        for r in objs_for_img:
            assert r.obj is not None
            d_i.update(r.obj.defs_by_name.keys())
            u_i.update(r.obj.undefs_by_name.keys())
            for sec in r.obj.sections:
                for rel in sec.relocs:
                    if rel.r_type in (282, 283, 279, 280, 314):  # JUMP26, CALL26, TSTBR14, CONDBR19, PLT32
                        tsym = r.obj.symbols[rel.sym_idx]
                        if not tsym.is_local and tsym.name:
                            sym_has_code_ref_in_img.add(tsym.name)
        defs_per_img.append(d_i)
        undefs_per_img.append(u_i)
        x_i = sorted(u_i - d_i)
        x_per_image[str(img_idx)] = x_i
        for sym in x_i:
            x_to_images.setdefault(sym, set()).add(img_idx)

    x_all = sorted(x_to_images.keys())
    x_set = set(x_all)
    x_sha256 = _canonical_list_sha256(x_all)
    all_image_defs = set().union(*defs_per_img) if defs_per_img else set()

    # Cross-check against engine `hookedExterns`
    tso = eng_meta.get("trimmedSysrootObjects", {}) if eng_meta is not None else {}
    hooked_externs_raw = tso.get("hookedExterns") if isinstance(tso, Mapping) else None
    hooked_externs: list[str] | None = (
        sorted(str(s) for s in hooked_externs_raw) if isinstance(hooked_externs_raw, list) else None
    )
    hooked_externs_sha = _canonical_list_sha256(hooked_externs) if hooked_externs is not None else None
    x_minus_hooked: list[str] = []
    if hooked_externs is not None:
        outside_x = sorted(set(hooked_externs) - x_set)
        if outside_x:
            errors.append(
                f"Engine `hookedExterns` contains {len(outside_x)} name(s) outside computed `X`: {outside_x}"
            )
        x_minus_hooked = sorted(x_set - set(hooked_externs))

    # ==========================================================================
    # Step 2: Resolve all retained `MapInputSection`s in `link.map`
    # ==========================================================================
    retained_nodes: list[RetainedSecNode] = []
    nodes_by_obj_sec: dict[tuple[str, str, int], list[RetainedSecNode]] = {}
    extracted_archive_members: dict[tuple[str, str, int], elf_inspect.ArchiveMember] = {}

    disk_sha_cache: dict[pathlib.Path, str] = {}
    map_obj_cache: dict[str, InputRecord | None] = {}
    map_arch_cache: dict[str, InputRecord | None] = {}

    def _sha256_disk_cached(p: pathlib.Path) -> str:
        rp_c = p.resolve()
        if rp_c not in disk_sha_cache:
            disk_sha_cache[rp_c] = elf_inspect.sha256_file(rp_c)
        return disk_sha_cache[rp_c]

    def _resolve_map_input_strict(
        m_raw: str,
        by_path: Mapping[str, InputRecord],
        by_name_all: Mapping[str, Sequence[InputRecord]],
        cache: dict[str, InputRecord | None],
    ) -> InputRecord | None:
        """G-F1 / SR-42b strict `link.map` path resolver:
        1. Resolve `m_raw` against `map_path.parent`, `base_dir`, and `eff_work` exact-path roots;
           if an on-disk file exists at that exact path, require its resolved path to be in `by_path`
           AND its computed SHA-256 to equal `rec.sha256` (never fall back to basename on mismatch!).
        2. Basename fallback is allowed ONLY when `m_raw` is an ephemeral absolute path not present
           on disk, the basename is unique across all link inputs (`len == 1`), AND `rec.disk_path`
           exists with `sha256 == rec.sha256`. A match on basename alone is rejected."""
        if m_raw in cache:
            return cache[m_raw]
        rp_raw = pathlib.Path(m_raw)
        exact_cands: list[pathlib.Path] = []
        if rp_raw.is_absolute():
            exact_cands.append(rp_raw)
        else:
            exact_cands.append(map_path.parent / rp_raw)
            exact_cands.append(base_dir / rp_raw)
            exact_cands.append(eff_work / rp_raw)
            if len(rp_raw.parts) >= 2 and rp_raw.parts[0] == "work":
                tail = pathlib.Path(*rp_raw.parts[1:])
                exact_cands.append(eff_work / tail)
                exact_cands.append(eff_work / "stock_stage" / rp_raw)
            elif len(rp_raw.parts) >= 2 and rp_raw.parts[0] == "..":
                stripped = [pt for pt in rp_raw.parts if pt != ".."]
                if stripped:
                    tail_s = pathlib.Path(*stripped)
                    exact_cands.append(eff_work / tail_s)
                    exact_cands.append(base_dir / tail_s)

        for cp in exact_cands:
            if cp.is_file():
                cp_res = str(cp.resolve())
                rec = by_path.get(cp_res)
                if rec is not None and _sha256_disk_cached(cp) == rec.sha256:
                    cache[m_raw] = rec
                    return rec
                cache[m_raw] = None
                return None

        # Only accept an unresolving path if `m_raw` is literally a registered `by_path` key
        # (e.g. an exact metadata `rel_path` staged under `--work-dir`), its basename is unique,
        # and the staged file's on-disk SHA-256 matches `rec.sha256`. Never match on basename alone.
        rec_reg = by_path.get(m_raw)
        if rec_reg is not None and len(by_name_all.get(rp_raw.name, ())) == 1:
            if rec_reg.disk_path.is_file() and _sha256_disk_cached(rec_reg.disk_path) == rec_reg.sha256:
                cache[m_raw] = rec_reg
                return rec_reg

        cache[m_raw] = None
        return None

    for m_sec in lmap.input_sections:
        if m_sec.input_raw == "<internal>":
            continue
        if m_sec.archive_path is not None and m_sec.archive_member is not None:
            arch_rec = _resolve_map_input_strict(
                m_sec.archive_path, archives_by_path, archives_by_name_all, map_arch_cache
            )
            if arch_rec is None or arch_rec.archive is None:
                errors.append(f"Unpinned archive in link.map: {m_sec.input_raw}")
                continue
            mem_cands = arch_rec.archive.members_by_name.get(m_sec.archive_member, [])
            if not mem_cands:
                errors.append(f"Archive {arch_rec.name} missing member {m_sec.archive_member!r} from link.map")
                continue
            try:
                mem, rsec = _find_matching_archive_member(mem_cands, m_sec)
            except KeyError as exc:
                if (m_sec.out_sec not in (".comment", ".ARM.attributes")) and m_sec.size > 0:
                    errors.append(str(exc))
                continue
            extracted_archive_members[(arch_rec.name, mem.name, mem.index)] = mem
            mem_key = f"{mem.name}@{mem.index}"
            piece_sfx = f"+0x{m_sec.piece_offset:x}" if m_sec.piece_offset is not None else ""
            node = RetainedSecNode(
                node_id=f"{arch_rec.name}({mem.name}):({m_sec.sec_name}{piece_sfx})",
                role="R",
                image_idx=None,
                source_file=arch_rec.name,
                archive_member=mem.name,
                archive_member_key=mem_key,
                file_sha256=mem.sha256,
                archive_sha256=arch_rec.sha256,
                obj=mem.obj,
                sec=rsec,
                map_sec=m_sec,
            )
            retained_nodes.append(node)
            nodes_by_obj_sec.setdefault((arch_rec.name, mem_key, rsec.idx), []).append(node)
        else:
            o_rec = _resolve_map_input_strict(
                m_sec.input_raw, standalone_by_path, standalone_by_name_all, map_obj_cache
            )
            if o_rec is None or o_rec.obj is None:
                errors.append(f"Unpinned object in link.map: {m_sec.input_raw}")
                continue
            try:
                rsec = _find_matching_rel_section(o_rec.obj, m_sec)
            except KeyError as exc:
                if (m_sec.out_sec not in (".comment", ".ARM.attributes")) and m_sec.size > 0:
                    errors.append(str(exc))
                continue
            piece_sfx = f"+0x{m_sec.piece_offset:x}" if m_sec.piece_offset is not None else ""
            node = RetainedSecNode(
                node_id=f"{o_rec.name}:({m_sec.sec_name}{piece_sfx})",
                role=o_rec.role,
                image_idx=o_rec.image_idx,
                source_file=o_rec.name,
                archive_member=None,
                archive_member_key="",
                file_sha256=o_rec.sha256,
                archive_sha256=None,
                obj=o_rec.obj,
                sec=rsec,
                map_sec=m_sec,
            )
            retained_nodes.append(node)
            nodes_by_obj_sec.setdefault((o_rec.name, "", rsec.idx), []).append(node)

    # Enforce 0 retained sections from `libunwind.a` (mirrors engine `stock_std_audit::unwind_audit`).
    # `node.source_file` holds `arch_rec.name` for archive members; `Path(...).name` handles full/rel paths,
    # and the secondary `lmap.input_sections` pass catches any non-alloc/zero-size map section skipped above.
    flagged_unwind_map_secs: set[int] = set()
    for node in retained_nodes:
        if pathlib.Path(node.source_file).name in ZERO_RETAINED_ARCHIVE_BASENAMES:
            flagged_unwind_map_secs.add(id(node.map_sec))
            errors.append(
                f"0f(v) / unwind_audit: archive 'libunwind.a' ({node.source_file}) "
                f"retained unexpected section {node.node_id} (expected 0 retained sections)"
            )
    for m_sec in lmap.input_sections:
        if (
            id(m_sec) not in flagged_unwind_map_secs
            and m_sec.archive_path is not None
            and pathlib.Path(m_sec.archive_path).name in ZERO_RETAINED_ARCHIVE_BASENAMES
        ):
            errors.append(
                f"0f(v) / unwind_audit: archive 'libunwind.a' ({m_sec.input_raw}) "
                f"retained unexpected map section {m_sec.sec_name!r} (expected 0 retained sections)"
            )

    # Verify P8-3 retained sections of trimmed objects are subsets of keepSet
    for trim_info in sysroot_trims_report:
        obj_name = str(trim_info["object"])
        kept_set = set(trim_info["kept_sections"])
        for node in retained_nodes:
            if node.source_file == obj_name and (node.sec.sh_flags & elf_inspect.SHF_ALLOC) != 0:
                if node.sec.name not in kept_set:
                    errors.append(
                        f"P8-3 violation: retained section {node.sec.name!r} of {obj_name} not in keepSet"
                    )

    # ==========================================================================
    # Step 3: Rule (i) Non-Local Collisions & Exempted Aliases, + Rule (ii) `main`
    # ==========================================================================
    exempted_aliases = sorted(
        str(x) for x in (tso.get("exemptedAliases", []) if isinstance(tso, Mapping) else [])
    )
    exempted_set = set(exempted_aliases)

    # Sibling-vs-sibling collision check (excluding class-S declared exports & exemptedAliases)
    for i in range(len(image_records)):
        for j in range(i + 1, len(image_records)):
            overlap = (defs_per_img[i] & defs_per_img[j]) - exempted_set
            if overlap:
                errors.append(f"Rule (i): non-local symbol collision between image {i} and image {j}: {sorted(overlap)}")

    # Non-image inputs vs `⋃_i D_i` collision check (all standalone `.o`s + extracted `.a` members)
    for r in all_inputs:
        if r.role.startswith("S:") or r.obj is None:
            continue
        for sym_name in r.obj.defs_by_name:
            if sym_name in all_image_defs and sym_name not in exempted_set:
                if r.role == "harness" and sym_name == "main":
                    continue  # Allowed by Rule (ii) iff weak
                errors.append(
                    f"Rule (i): non-image input {r.name} ({r.role}) defines image symbol {sym_name!r}"
                )
    for (arch_name, mem_name, _mem_idx), mem in sorted(extracted_archive_members.items()):
        for sym_name in mem.obj.defs_by_name:
            if sym_name in all_image_defs and sym_name not in exempted_set:
                errors.append(
                    f"Rule (i): extracted archive member {arch_name}({mem_name}) defines image symbol {sym_name!r}"
                )

    # Rule (ii): Entry harness `main` weak/weakened + ELF `main` VMA check
    assert harness_record.obj is not None
    weakened_in_main: list[str] = []
    if recipe == "engine":
        assert eng_meta is not None
        weakened_in_main = [str(x) for x in eng_meta.get("stdBin", {}).get("weakenedInMain", [])]
        if weakened_in_main != ["main"]:
            errors.append(f"Rule (ii): engine `weakenedInMain` expected ['main'], got {weakened_in_main!r}")
    else:
        harness_nonlocal = set(harness_record.obj.defs_by_name.keys())
        if harness_nonlocal != {"main"}:
            errors.append(
                f"Rule (ii): builder harness {harness_record.name} non-local defs {sorted(harness_nonlocal)} != ['main']"
            )
        weakened_in_main = ["main"]

    h_main_syms = harness_record.obj.defs_by_name.get("main", [])
    if len(h_main_syms) != 1 or h_main_syms[0].bind != elf_inspect.STB_WEAK:
        errors.append(
            f"Rule (ii): harness {harness_record.name} must define `main` as single STB_WEAK symbol, got {h_main_syms}"
        )

    elf_main_syms = elf.nonlocal_defs.get("main", [])
    main_elf_vma = 0
    if len(elf_main_syms) != 1:
        errors.append(f"Rule (ii): expected 1 non-local `main` in ELF .symtab, found {len(elf_main_syms)}")
    else:
        main_elf_vma = elf_main_syms[0].st_value
        main_nodes = [
            node
            for node in retained_nodes
            if node.map_sec.vma <= main_elf_vma < node.map_sec.vma + max(1, node.map_sec.size)
            and "main" in node.obj.defs_by_name
            and any(
                s.st_shndx == node.sec.idx
                and node.map_sec.vma + s.st_value - (node.map_sec.piece_offset or 0) == main_elf_vma
                for s in node.obj.defs_by_name["main"]
            )
        ]
        if len(main_nodes) != 1 or main_nodes[0].role != "S:0":
            errors.append(
                f"Rule (ii): ELF `main` at {main_elf_vma:#x} must resolve to `S:0` library export, "
                f"got {[n.node_id for n in main_nodes]}"
            )
        if recipe == "builder" and not (main_elf_vma < elf.entry):
            errors.append(f"Rule (ii)/F9: builder `main` {main_elf_vma:#x} not < e_entry {elf.entry:#x}")

    # Collect placed export addresses per image
    placed_exports_report: dict[str, dict[str, str]] = {}
    for img_idx, exp_names in sorted(declared_exports_by_img.items()):
        img_exp_map: dict[str, str] = {}
        # Map demangled declared exports to mangled definitions in image `img_idx`
        mangled_in_img: dict[str, list[str]] = {}
        for d_sym in defs_per_img[img_idx]:
            mangled_in_img.setdefault(d_sym, []).append(d_sym)
            dem = elf_inspect.demangle_rust(d_sym)
            if dem != d_sym:
                mangled_in_img.setdefault(dem, []).append(d_sym)
        for decl_exp in sorted(exp_names):
            m_cands = mangled_in_img.get(decl_exp, [])
            for mc in m_cands:
                es = elf.nonlocal_defs.get(mc, [])
                if len(es) == 1:
                    img_exp_map[mc] = hex(es[0].st_value)
        placed_exports_report[str(img_idx)] = img_exp_map

    # ==========================================================================
    # Step 4: Helper to resolve any non-local symbol's winning definition in ELF + link.map
    # ==========================================================================
    def resolve_symbol_definer(sym_name: str) -> tuple[list[elf_inspect.ExecSymbol], list[tuple[RetainedSecNode, elf_inspect.RelSymbol]]]:
        nonlocal_hits = elf.nonlocal_defs.get(sym_name, [])
        if nonlocal_hits:
            elf_cands = nonlocal_hits
        else:
            # GK row 373 change 1: stock links may localize STV_HIDDEN symbols in `.symtab`
            elf_cands = elf.all_defs_by_name.get(sym_name, [])

        winning_pairs: list[tuple[RetainedSecNode, elf_inspect.RelSymbol]] = []
        for esym in elf_cands:
            vma = esym.st_value
            for node in retained_nodes:
                lo = node.map_sec.vma
                hi = lo + max(1, node.map_sec.size)
                if not (lo <= vma < hi):
                    continue
                for rsym in node.obj.defs_by_name.get(sym_name, []):
                    if rsym.st_shndx != node.sec.idx:
                        continue
                    if node.sec.idx == elf_inspect.SHN_COMMON:
                        if node.map_sec.symbols:
                            if any(
                                (ms.name == sym_name or ms.name == rsym.demangled) and ms.vma == vma
                                for ms in node.map_sec.symbols
                            ):
                                winning_pairs.append((node, rsym))
                        elif rsym.st_size == esym.st_size:
                            winning_pairs.append((node, rsym))
                    else:
                        expected_vma = node.map_sec.vma + rsym.st_value - (node.map_sec.piece_offset or 0)
                        if expected_vma == vma:
                            winning_pairs.append((node, rsym))
        # Deduplicate identical `(node.node_id, rsym.idx)` pairs
        dedup: list[tuple[RetainedSecNode, elf_inspect.RelSymbol]] = []
        seen_keys: set[tuple[str, int]] = set()
        for node, rsym in winning_pairs:
            k = (node.node_id, rsym.idx)
            if k not in seen_keys:
                seen_keys.add(k)
                dedup.append((node, rsym))
        return elf_cands, dedup

    # ==========================================================================
    # Step 5: Build Surviving Referrer Map & Section-Level Relocation Graph
    # ==========================================================================
    surviving_referrers_all: dict[str, set[str]] = {}
    surviving_referrers_by_node: dict[str, list[RetainedSecNode]] = {}
    section_graph: dict[str, set[str]] = {n.node_id: set() for n in retained_nodes}
    section_nonlocal_syms: dict[str, set[str]] = {n.node_id: set() for n in retained_nodes}
    node_by_id: dict[str, RetainedSecNode] = {n.node_id: n for n in retained_nodes}
    unresolved_outside_x: dict[str, list[tuple[str, str]]] = {}

    for node in retained_nodes:
        p_lo = node.map_sec.piece_offset if node.map_sec.piece_offset is not None else 0
        p_hi = (p_lo + node.map_sec.size) if node.map_sec.piece_offset is not None else node.sec.sh_size

        for rel in node.sec.relocs:
            if rel.r_type in elf_inspect.R_AARCH64_NONE_SET:
                continue
            if node.map_sec.piece_offset is not None and not (p_lo <= rel.r_offset < p_hi):
                continue
            tsym = node.obj.symbols[rel.sym_idx]
            if tsym.is_local:
                if tsym.st_shndx not in (
                    elf_inspect.SHN_UNDEF,
                    elf_inspect.SHN_ABS,
                    elf_inspect.SHN_COMMON,
                ):
                    key = (
                        node.source_file,
                        node.archive_member_key,
                        tsym.st_shndx,
                    )
                    for tgt_node in nodes_by_obj_sec.get(key, []):
                        section_graph[node.node_id].add(tgt_node.node_id)
                continue

            sname = tsym.name
            if not sname:
                continue
            section_nonlocal_syms[node.node_id].add(sname)
            surviving_referrers_all.setdefault(sname, set()).add(node.node_id)
            surviving_referrers_by_node.setdefault(sname, []).append(node)

            _ecands, wpairs = resolve_symbol_definer(sname)
            if wpairs:
                for tgt_node, _rsym in wpairs:
                    section_graph[node.node_id].add(tgt_node.node_id)
            elif _ecands and sname not in x_set:
                if sname not in LINKER_SYNTHESIZED_SYMBOLS:
                    errors.append(
                        f"Rule (iv): unexpected linker-synthesized `<internal>` symbol {sname!r} "
                        f"referenced by {node.node_id}"
                    )
            elif sname not in x_set and not node.role.startswith("S:"):
                unresolved_outside_x.setdefault(sname, []).append((node.node_id, tsym.bind_name))

    # Rule (iv) weak-undefined check outside `X`
    if recipe == "engine":
        assert eng_meta is not None
        allowed_uw = sorted(
            {
                *(
                    str(item["symbol"])
                    for item in eng_meta.get("stdBin", {}).get("unwindAudit", {}).get("allowed", [])
                    if isinstance(item, Mapping) and item.get("symbol")
                ),
                *ENGINE_CRT_WEAK_UNDEF_PROBES,
            }
        )
    else:
        allowed_uw = []
        if elf.undef_symbols:
            errors.append(
                f"Builder F8 violation: ELF .symtab has {len(elf.undef_symbols)} SHN_UNDEF symbol(s): "
                f"{[s.name for s in elf.undef_symbols]}"
            )
    allowed_uw_set = set(allowed_uw)
    for usym, ref_sites in sorted(unresolved_outside_x.items()):
        if usym not in allowed_uw_set:
            errors.append(f"Unresolved symbol {usym!r} outside `X` at retained site(s) {ref_sites}")
        elif any(bind != "STB_WEAK" for _, bind in ref_sites):
            errors.append(f"Strong unresolved symbol {usym!r} outside `X` at {ref_sites}")

    # Compute `image_reachable_nodes` (all retained sections reachable from `⋃_i configs[i]`)
    image_reachable_ids: set[str] = set()
    bfs_img: deque[str] = deque(n.node_id for n in retained_nodes if n.role.startswith("S:"))
    while bfs_img:
        cur = bfs_img.popleft()
        if cur in image_reachable_ids:
            continue
        image_reachable_ids.add(cur)
        for nxt in section_graph.get(cur, ()):
            if nxt not in image_reachable_ids:
                bfs_img.append(nxt)

    # ==========================================================================
    # Step 6: Optional `--trace-symbol` Log Parsing
    # ==========================================================================
    trace_defs: dict[str, list[str]] | None = None
    if trace_log_path is not None:
        trace_defs, _ = elf_inspect.parse_trace_symbol_log(trace_log_path.read_text(encoding="utf-8"))

    # ==========================================================================
    # Step 7: Whole-Archive + N + S Symbol Inventory (for Z Non-Displacement & α)
    # ==========================================================================
    whole_rns_defs: dict[str, list[tuple[str, str, str, str]]] = {}
    # tuple: `(kind, container_name, member_or_empty, bind_name)`
    for r in all_inputs:
        if r.role == "R" and r.archive is not None:
            for mem in r.archive.members:
                for sname, syms in mem.obj.defs_by_name.items():
                    for sym in syms:
                        whole_rns_defs.setdefault(sname, []).append(("R", r.name, mem.name, sym.bind_name))
        elif r.role == "N" and r.obj is not None:
            for sname, syms in r.obj.defs_by_name.items():
                for sym in syms:
                    whole_rns_defs.setdefault(sname, []).append(("N", r.name, "", sym.bind_name))
        elif r.role.startswith("S:") and r.obj is not None:
            for sname, syms in r.obj.defs_by_name.items():
                for sym in syms:
                    whole_rns_defs.setdefault(sname, []).append((r.role, r.name, "", sym.bind_name))

    # Verify Class Z stub object internal invariants (all STB_GLOBAL, all zero bytes)
    for sname, zsyms in sorted(stub_record.obj.defs_by_name.items()):
        for zs in zsyms:
            if zs.bind != elf_inspect.STB_GLOBAL:
                errors.append(f"Class Z stub {stub_record.name} symbol {sname!r} has {zs.bind_name} != STB_GLOBAL")
            if zs.st_shndx < len(stub_record.obj.sections):
                zsec = stub_record.obj.sections[zs.st_shndx]
                if zsec.sh_type != elf_inspect.SHT_NOBITS and any(b != 0 for b in zsec.data):
                    errors.append(f"Class Z stub {stub_record.name} section {zsec.name!r} has non-zero bytes")

    # ==========================================================================
    # Step 8: Classify Every `x ∈ X` & Enforce Exact 1 Definer + Byte Equality
    # ==========================================================================
    class_histogram: dict[str, int] = {"R": 0, "N": 0, "S": 0, "Z": 0, "discarded": 0}
    zero_definer_names: list[str] = []
    multi_definer_names: list[str] = []
    discarded_names: list[str] = []
    definers_table: dict[str, dict[str, Any]] = {}
    winning_node_by_x: dict[str, tuple[RetainedSecNode, elf_inspect.RelSymbol, elf_inspect.ExecSymbol]] = {}
    actual_displaced_by_z: set[str] = set()
    data_only_in_x: list[str] = []

    for x in x_all:
        if x not in sym_has_code_ref_in_img:
            data_only_in_x.append(x)

        surv_refs = surviving_referrers_all.get(x, set())
        elf_cands, wpairs = resolve_symbol_definer(x)

        if not surv_refs and not wpairs:
            # Discarded under `--gc-sections` (`0` surviving relocations and `0` retained definitions)
            class_histogram["discarded"] += 1
            discarded_names.append(x)
            definers_table[x] = {
                "class": "discarded",
                "demangled": elf_inspect.demangle_rust(x),
                "images": sorted(x_to_images[x]),
                "source_file": None,
                "archive_member": None,
                "sha256": None,
                "archive_sha256": None,
                "elf_addr": None,
                "size": 0,
                "input_section": None,
                "input_binding": None,
            }
            continue

        # Surviving reference (or retained symbol in X): MUST have EXACTLY ONE definer!
        nonlocal_elf_hits = elf.nonlocal_defs.get(x, [])
        if len(nonlocal_elf_hits) > 1 or len(wpairs) > 1:
            multi_definer_names.append(x)
            errors.append(
                f"Rule (v): symbol {x!r} has multiple definers: elf_nonlocal={len(nonlocal_elf_hits)}, "
                f"map_definers={[p[0].node_id for p in wpairs]}"
            )
            continue

        if len(wpairs) == 0 or len(elf_cands) == 0:
            zero_definer_names.append(x)
            errors.append(
                f"Rule (v): surviving symbol {x!r} (referrers={sorted(surv_refs)}) has 0 definers in ELF/link.map"
            )
            continue

        win_node, win_rsym = wpairs[0]
        # Match the exact ExecSymbol at `win_node.map_sec.vma + win_rsym.st_value - piece_offset`
        win_vma = win_node.map_sec.vma + win_rsym.st_value - (win_node.map_sec.piece_offset or 0)
        matching_esyms = [e for e in elf_cands if e.st_value == win_vma]
        if len(matching_esyms) != 1:
            if len(matching_esyms) == 0:
                zero_definer_names.append(x)
                errors.append(f"Rule (v): symbol {x!r} VMA {win_vma:#x} missing in ELF .symtab")
            else:
                multi_definer_names.append(x)
                errors.append(f"Rule (v): symbol {x!r} has {len(matching_esyms)} duplicate ELF .symtab defs at {win_vma:#x}")
            continue
        win_esym = matching_esyms[0]
        if win_esym.st_value == 0:
            errors.append(f"Rule (v): symbol {x!r} resolved to address 0 (weak undefined)")
            continue

        # Map `win_node.role` -> A-LINK definer class `R`, `N`, `S`, `Z`
        if win_node.role in ("R", "N", "Z"):
            dclass = win_node.role
        elif win_node.role.startswith("S:"):
            dclass = "S"
            def_img = win_node.image_idx
            assert def_img is not None
            for req_img in sorted(x_to_images[x]):
                if req_img == def_img:
                    errors.append(f"Rule (v)(S): symbol {x!r} in X_{req_img} defined by same image {def_img}")
            decl_exps = declared_exports_by_img.get(def_img, set())
            if x not in decl_exps and elf_inspect.demangle_rust(x) not in decl_exps:
                errors.append(
                    f"Rule (v)(S): symbol {x!r} ({elf_inspect.demangle_rust(x)!r}) defined by image {def_img} "
                    f"is NOT in its declared exports {sorted(decl_exps)}"
                )
        else:
            errors.append(
                f"Rule (v): forbidden definer role {win_node.role!r} ({win_node.node_id}) for {x!r}"
            )
            continue

        # Optional `--trace-symbol` cross-check
        if trace_defs is not None:
            t_lines = trace_defs.get(x, [])
            if not t_lines:
                errors.append(f"Rule (v) trace control: 0 `definition of {x}` lines in trace log")
            elif len(t_lines) > 1 and x not in elf_inspect.DISPLACED_WEAK_ATOMICS:
                errors.append(
                    f"Rule (v) trace control: >1 `definition of {x}` lines outside displaced_weak: {t_lines}"
                )

        class_histogram[dclass] += 1
        winning_node_by_x[x] = (win_node, win_rsym, win_esym)

        row_dict: dict[str, Any] = {
            "class": dclass,
            "demangled": elf_inspect.demangle_rust(x),
            "images": sorted(x_to_images[x]),
            "source_file": win_node.source_file,
            "archive_member": win_node.archive_member,
            "sha256": win_node.file_sha256,
            "archive_sha256": win_node.archive_sha256,
            "elf_addr": hex(win_esym.st_value),
            "size": int(win_esym.st_size),
            "input_section": win_node.sec.name,
            "input_binding": win_rsym.bind_name,
        }

        if dclass in ("R", "N", "S"):
            try:
                cmp_res = elf_inspect.compare_defined_symbol_bytes(
                    obj=win_node.obj,
                    sym=win_rsym,
                    elf=elf,
                    elf_vma=win_esym.st_value,
                    map_sec_size=win_node.map_sec.size,
                )
                row_dict["body_sha256"] = cmp_res.elf_body_sha256
                row_dict["reloc_count"] = cmp_res.reloc_count
            except Exception as exc:  # noqa: BLE001
                errors.append(f"Rule (v) R/N/S byte compare failed for {x!r}: {exc}")

            # Rule (vii)(1): No `cliHookTablePlaced` key has an `STB_WEAK` definer in input `.symtab`
            if x in hook_table_keys and win_rsym.bind == elf_inspect.STB_WEAK:
                errors.append(
                    f"Rule (vii): hook key {x!r} has STB_WEAK input binding in {win_node.node_id}"
                )
        else:
            # Class `Z` checks: final ELF bytes must be all zero (`udf #0` for code, `0x00` for data/TLS)
            if win_rsym.bind != elf_inspect.STB_GLOBAL:
                errors.append(f"Rule (v)(Z): {x!r} in {win_node.node_id} has {win_rsym.bind_name} != STB_GLOBAL")
            if win_esym.stype == elf_inspect.STT_TLS:
                if win_esym.st_shndx < len(elf.sections):
                    tsec = elf.sections[win_esym.st_shndx]
                    if tsec.sh_type != elf_inspect.SHT_NOBITS:
                        raw_elf = elf_path.read_bytes()
                        rel_off = win_esym.st_value
                        if any(b != 0 for b in raw_elf[tsec.sh_offset + rel_off : tsec.sh_offset + rel_off + win_esym.st_size]):
                            errors.append(f"Rule (v)(Z): TLS stub {x!r} has non-zero template bytes in ELF")
            else:
                chk_len = max(4 if win_esym.stype == elf_inspect.STT_FUNC else 1, win_esym.st_size)
                z_bytes = elf.read_vma(win_esym.st_value, chk_len)
                if any(b != 0 for b in z_bytes):
                    errors.append(
                        f"Rule (v)(Z): stub {x!r} at {win_esym.st_value:#x} has non-zero ELF bytes {z_bytes.hex()}"
                    )
            # Check whole-archive + N + S displacement
            rns_cands = whole_rns_defs.get(x, [])
            if rns_cands:
                actual_displaced_by_z.add(x)
                for rkind, cname, mname, bname_str in rns_cands:
                    if rkind != "R" or cname not in COMPILER_RT_ARCHIVE_BASENAMES or bname_str != "STB_WEAK":
                        errors.append(
                            f"Rule (v)(Z) illegal displacement: zero stub for {x!r} displaces {bname_str} "
                            f"definition in {rkind} {cname}{f'({mname})' if mname else ''}"
                        )
                if x in hook_table_keys or elf_inspect.is_cli_panic_symbol_placed(x, panic_table_keys):
                    errors.append(f"Rule (v)(Z): displaced_weak symbol {x!r} is in H ∪ panics")

        definers_table[x] = row_dict

    # Also check unreferenced stubs in `Z` that became `discarded` against illegal strong R/N/S displacement
    for x in discarded_names:
        rns_cands = whole_rns_defs.get(x, [])
        for rkind, cname, mname, bname_str in rns_cands:
            if rkind == "R" and cname in COMPILER_RT_ARCHIVE_BASENAMES and bname_str == "STB_WEAK":
                actual_displaced_by_z.add(x)
            elif x in stub_record.obj.defs_by_name:
                errors.append(
                    f"Rule (v)(Z): stubbed discarded symbol {x!r} collides with {bname_str} in "
                    f"{rkind} {cname}{f'({mname})' if mname else ''}"
                )

    # ==========================================================================
    # Step 9: Option `α` (`displaced_weak` & G5 `displaced_weak_referrers`)
    # ==========================================================================
    expected_displaced_weak = set(elf_inspect.DISPLACED_WEAK_ATOMICS) if atomics_mode == "alpha" else set()
    if actual_displaced_by_z != expected_displaced_weak:
        errors.append(
            f"Option {atomics_mode} `displaced_weak` mismatch: got {sorted(actual_displaced_by_z)} != "
            f"expected {sorted(expected_displaced_weak)}"
        )

    displaced_weak_addrs: dict[str, str] = {}
    displaced_weak_ref_set: set[str] = set()
    non_lib0_atomic_relocs_pre_gc = 0

    # Pre-GC scan of all non-`S:0` inputs for any relocation referencing the 3 outline atomics (STOCK-CLASSIFY 2b)
    for r in all_inputs:
        if r.role == "S:0":
            continue
        objs_to_scan: list[elf_inspect.RelocObject] = []
        if r.obj is not None:
            objs_to_scan.append(r.obj)
        elif r.archive is not None:
            objs_to_scan.extend(m.obj for m in r.archive.members)
        for ro in objs_to_scan:
            for sec in ro.sections:
                for rel in sec.relocs:
                    if rel.r_type in elf_inspect.R_AARCH64_NONE_SET:
                        continue
                    ts = ro.symbols[rel.sym_idx]
                    if not ts.is_local and ts.name in elf_inspect.DISPLACED_WEAK_ATOMICS:
                        non_lib0_atomic_relocs_pre_gc += 1

    if atomics_mode == "alpha":
        for asym in sorted(elf_inspect.DISPLACED_WEAK_ATOMICS):
            if asym not in winning_node_by_x:
                errors.append(f"Option α: atomic {asym!r} is missing a winning definer")
                continue
            anode, _arsym, aesym = winning_node_by_x[asym]
            if anode.role != "Z":
                errors.append(
                    f"Option α: atomic {asym!r} resolved to {anode.role} ({anode.node_id}), expected Class Z `udf #0` stub"
                )
            if aesym.st_size != 4 or elf.read_vma(aesym.st_value, 4) != b"\x00\x00\x00\x00":
                errors.append(f"Option α: atomic {asym!r} at {aesym.st_value:#x} does not decode to 4-byte `udf #0`")
            displaced_weak_addrs[asym] = hex(aesym.st_value)

            for ref_node in surviving_referrers_by_node.get(asym, []):
                displaced_weak_ref_set.add(ref_node.node_id)
                if ref_node.role != "S:0":
                    errors.append(
                        f"Option α G5 violation: `displaced_weak` symbol {asym!r} referenced outside `cliLinkObjs` "
                        f"by {ref_node.node_id} (role={ref_node.role})"
                    )

    displaced_weak_referrers = sorted(displaced_weak_ref_set)

    # ==========================================================================
    # Step 10: G4 (`n_undef_map` for all Class `N` Native & `rust_extracted` Objects)
    # ==========================================================================
    extra_failstop = (
        tuple(str(x) for x in lock_data["failstop_z"])
        if lock_data is not None and "failstop_z" in lock_data
        else tuple(elf_inspect.DEFAULT_FAILSTOP_DROP_STUBS)
    )

    n_undef_map: dict[str, dict[str, dict[str, Any]]] = {}
    for node in retained_nodes:
        if node.role != "N":
            continue
        sub = n_undef_map.setdefault(node.source_file, {})
        for usym in sorted(section_nonlocal_syms.get(node.node_id, ())):
            if usym in node.obj.defs_by_name:
                continue
            _ec, wp = resolve_symbol_definer(usym)
            if len(wp) != 1:
                errors.append(
                    f"Rule (v)(N) G4: Class N object {node.source_file} undefined {usym!r} has {len(wp)} definers"
                )
                continue
            unode, ursym = wp[0]
            if unode.role == "Z":
                # GK 458 C3: `rust_extracted` Class N objects may reference `failstop_z` zero stubs;
                # non-`failstop_z` Z targets (and any Z target from non-`rust_extracted` N) FAIL CLOSED.
                if not (
                    node.source_file in lock_rust_extracted
                    and elf_inspect.is_failstop_z_symbol(
                        usym, extra_failstop=extra_failstop, extra_panics=panic_table_keys
                    )
                ):
                    errors.append(
                        f"Rule (v)(N) G4: Class N object {node.source_file} undefined {usym!r} "
                        "resolved to non-failstop Class Z stub"
                    )
            uvma = unode.map_sec.vma + ursym.st_value - (unode.map_sec.piece_offset or 0)
            sub[usym] = {
                "class": unode.role if unode.role in ("R", "N", "Z") else ("S" if unode.role.startswith("S:") else unode.role),
                "source_file": unode.source_file,
                "archive_member": unode.archive_member,
                "sha256": unode.file_sha256,
                "elf_addr": hex(uvma),
            }

    # ==========================================================================
    # Step 11: Rule (vi) Hooked & `real_proved` Definers Reach No Stub (G3 + GK 459)
    # ==========================================================================
    observed_failstop_z: set[str] = set()

    def _run_rule_vi_closure(
        root_syms: Sequence[str],
        *,
        kind_label: str,
    ) -> tuple[dict[str, dict[str, Any]], set[str]]:
        closures_out: dict[str, dict[str, Any]] = {}
        union_visited: set[str] = set()
        for root_sym in sorted(root_syms):
            if root_sym not in winning_node_by_x:
                continue
            r_node, _r_rsym, _r_esym = winning_node_by_x[root_sym]
            if r_node.role == "Z":
                continue  # Rule (vi) applies to R/N/S definers

            visited_nodes: set[str] = set()
            parent_map: dict[str, str | None] = {r_node.node_id: None}
            q: deque[str] = deque([r_node.node_id])
            reached_z_failstop: set[str] = set()
            reached_z_illegal: list[dict[str, str]] = []

            while q:
                cur_id = q.popleft()
                if cur_id in visited_nodes:
                    continue
                visited_nodes.add(cur_id)
                cur_node = node_by_id[cur_id]
                if cur_node.role == "Z":
                    continue

                for sym_ref in sorted(section_nonlocal_syms.get(cur_id, ())):
                    _ec, wp = resolve_symbol_definer(sym_ref)
                    if not wp:
                        continue
                    tgt_node, _trsym = wp[0]
                    if tgt_node.role == "Z":
                        if elf_inspect.is_failstop_z_symbol(
                            sym_ref, extra_failstop=extra_failstop, extra_panics=panic_table_keys
                        ):
                            reached_z_failstop.add(sym_ref)
                            observed_failstop_z.add(sym_ref)
                        else:
                            chain: list[str] = [cur_id]
                            p = parent_map.get(cur_id)
                            while p is not None:
                                chain.append(p)
                                p = parent_map.get(p)
                            chain.reverse()
                            reached_z_illegal.append({
                                "symbol": sym_ref,
                                "demangled": elf_inspect.demangle_rust(sym_ref),
                                "chain": " -> ".join(chain) + f" -> Z:{sym_ref}",
                            })
                            errors.append(
                                f"Rule (vi) violation: {kind_label} {r_node.role} definer {root_sym!r} "
                                f"({elf_inspect.demangle_rust(root_sym)}) reaches Class Z zero stub "
                                f"{sym_ref!r} ({elf_inspect.demangle_rust(sym_ref)}) via {' -> '.join(chain)}"
                            )

                for nxt_id in sorted(section_graph.get(cur_id, ())):
                    nxt_node = node_by_id[nxt_id]
                    if nxt_node.role == "Z":
                        continue
                    if nxt_id not in visited_nodes and nxt_id not in parent_map:
                        parent_map[nxt_id] = cur_id
                        q.append(nxt_id)

            union_visited.update(visited_nodes)
            closures_out[root_sym] = {
                "demangled": elf_inspect.demangle_rust(root_sym),
                "definer_class": "S" if r_node.role.startswith("S:") else r_node.role,
                "root_section": r_node.node_id,
                "closure_section_count": len(visited_nodes),
                "closure_sections": sorted(visited_nodes),
                "failstop_z_reached": sorted(reached_z_failstop),
                "illegal_z_reached": reached_z_illegal,
            }
        return closures_out, union_visited

    hook_closures, union_hook_closure_node_ids = _run_rule_vi_closure(
        sorted(hook_table_keys), kind_label="hooked"
    )

    # Canonical `failstop_z` list recorded for this link
    canonical_failstop_z = sorted(
        {
            s
            for s in x_all
            if s in winning_node_by_x
            and winning_node_by_x[s][0].role == "Z"
            and elf_inspect.is_failstop_z_symbol(s, extra_failstop=extra_failstop, extra_panics=panic_table_keys)
        }
    )

    # ==========================================================================
    # Step 12: Rule (iii) `real_hook_reached` & `real_proved` Lists + GK 459 Closure
    # ==========================================================================
    actual_unhooked_rns: set[str] = set()
    harness_startup_refs: dict[str, list[str]] = {}
    for x, (win_node, _wrsym, _wesym) in sorted(winning_node_by_x.items()):
        if win_node.role == "Z":
            continue
        if x in hook_table_keys or elf_inspect.is_cli_panic_symbol_placed(x, panic_table_keys):
            continue
        actual_unhooked_rns.add(x)

    if lock_data is None or "real_hook_reached" not in lock_data or "real_proved" not in lock_data:
        expected_real_hook_reached = []
        expected_real_proved = []
        errors.append("Rule (iii): rule (iii) needs --lock; no built-in partition")
    else:
        expected_real_hook_reached = sorted(str(x) for x in lock_data["real_hook_reached"])
        expected_real_proved = sorted(str(x) for x in lock_data["real_proved"])
        exp_rhr_set = set(expected_real_hook_reached)
        exp_rp_set = set(expected_real_proved)
        if exp_rhr_set & exp_rp_set:
            errors.append(f"Rule (iii): `real_hook_reached` and `real_proved` overlap: {sorted(exp_rhr_set & exp_rp_set)}")

        for x, (win_node, _wrsym, _wesym) in sorted(winning_node_by_x.items()):
            if win_node.role == "Z":
                continue
            if x in hook_table_keys or elf_inspect.is_cli_panic_symbol_placed(x, panic_table_keys):
                continue
            if x not in exp_rhr_set and x not in exp_rp_set:
                errors.append(
                    f"Rule (iii): unhooked/non-panic {win_node.role} symbol {x!r} in `X` is in neither "
                    f"`real_hook_reached` nor `real_proved`"
                )

        expected_union = exp_rhr_set | exp_rp_set
        if actual_unhooked_rns != expected_union:
            errors.append(
                f"Rule (iii): unhooked R/N/S set {sorted(actual_unhooked_rns)} != "
                f"`real_hook_reached ∪ real_proved` {sorted(expected_union)}"
            )

        for rsym_name in expected_real_hook_reached:
            if rsym_name not in winning_node_by_x or winning_node_by_x[rsym_name][0].role == "Z":
                errors.append(f"Rule (iii): `real_hook_reached` symbol {rsym_name!r} has no R/N/S definer")
                continue
            all_ref_ids = surviving_referrers_all.get(rsym_name, set())
            img_reach_refs = all_ref_ids & image_reachable_ids
            non_img_refs = all_ref_ids - image_reachable_ids

            if not img_reach_refs:
                errors.append(
                    f"Rule (iii): `real_hook_reached` symbol {rsym_name!r} has 0 image-reachable referrers"
                )
            outside_closure = sorted(img_reach_refs - union_hook_closure_node_ids)
            if outside_closure:
                errors.append(
                    f"Rule (iii): `real_hook_reached` symbol {rsym_name!r} has surviving image-reachable referrer(s) "
                    f"OUTSIDE hook closures (belongs in `real_proved`): {outside_closure}"
                )
            if non_img_refs:
                non_harness = [nid for nid in sorted(non_img_refs) if node_by_id[nid].role not in ("harness", "startfile")]
                if non_harness:
                    errors.append(
                        f"Rule (iii): `real_hook_reached` symbol {rsym_name!r} referenced by unexpected non-image "
                        f"section(s): {non_harness}"
                    )
                harness_startup_refs[rsym_name] = sorted(non_img_refs)

    # GK 459: Run Rule (vi) relocation-closure check over every `real_proved` definer as well
    proved_closure_roots = sorted(set(expected_real_proved) | (actual_unhooked_rns - set(expected_real_hook_reached)))
    proved_closures, _ = _run_rule_vi_closure(proved_closure_roots, kind_label="real_proved")

    # ==========================================================================
    # Step 12c: SC-1 (`rust_extracted`, §0f(vi) Recipe Re-Derive & Disjoint Sections, §0f(vii) SR-35 NB1)
    # ==========================================================================
    lock_rustc_ver = str(lock_data.get("rustc_version") or "").strip() if lock_data is not None else ""
    eff_expected_rustc_ver = lock_rustc_ver or rustc_ver
    image_target_triples, triple_cfg_errs = _resolve_image_target_triples(eff_repo_root, lock_data)
    if lock_rust_extracted:
        errors.extend(triple_cfg_errs)
    eff_toolchain_sysroot = _discover_toolchain_sysroot(
        eff_repo_root, toolchain_sysroot, expected_rustc_version=eff_expected_rustc_ver
    )
    rlib_roots = _discover_rlib_search_roots(
        search_roots, eff_repo_root, eff_toolchain_sysroot, image_target_triples
    )
    rust_extracted_report: dict[str, dict[str, Any]] = {}
    toolchain_sysroot_scan_report: dict[str, Any] = {}

    # §0f(vi): Check that NO section is kept by two objects across `sysroot_trims` and `rust_extracted` kind (a)
    kept_section_owners: dict[str, list[str]] = {}
    for st_row in sysroot_trims_report:
        st_owner = f"sysroot_trim:{st_row['object']}"
        for ksec in st_row.get("kept_sections", []):
            kept_section_owners.setdefault(str(ksec), []).append(st_owner)
    for re_name, re_cfg in sorted(lock_rust_extracted.items()):
        if re_cfg.get("kind") == "rlib_member":
            re_owner = f"rust_extracted:{re_name}"
            for ksec in re_cfg.get("keep_sections") or []:
                kept_section_owners.setdefault(str(ksec), []).append(re_owner)
    for ksec, kowners in sorted(kept_section_owners.items()):
        if len(kowners) > 1:
            errors.append(f"0f(vi): section {ksec!r} is kept by multiple objects: {kowners}")

    # Exact-name definitions in all non-`rust_extracted` pinned inputs (`R`, non-`rust_extracted` `N`, `S:<i>`)
    exact_defs_non_re: dict[str, list[str]] = {}
    for r in all_inputs:
        if r.role == "R" and r.archive is not None:
            for mem in r.archive.members:
                for sname in mem.obj.defs_by_name:
                    exact_defs_non_re.setdefault(sname, []).append(f"R:{r.name}({mem.name})")
        elif r.role == "N" and r.obj is not None and r.name not in lock_rust_extracted:
            for sname in r.obj.defs_by_name:
                exact_defs_non_re.setdefault(sname, []).append(f"N:{r.name}")
        elif r.role.startswith("S:") and r.obj is not None:
            for sname in r.obj.defs_by_name:
                if sname not in exempted_set:
                    exact_defs_non_re.setdefault(sname, []).append(f"{r.role}:{r.name}")

    # Collect target symbols defined by `rust_extracted` objects for the toolchain `lib/rustlib/*/lib/*.rlib` scan
    re_target_syms: set[str] = set()
    for re_name in sorted(lock_rust_extracted.keys()):
        o_rec = standalone_by_name.get(re_name)
        if o_rec is not None and o_rec.obj is not None:
            re_target_syms.update(o_rec.obj.defs_by_name.keys())

    # `rlib_exact_hits[sym]` -> list of `(scope_label, rlib_name, rlib_sha256, member_name, member_sha256)`
    rlib_exact_hits: dict[str, list[tuple[str, str, str, str, str]]] = {}
    scanned_sysroot_rlib_shas: set[str] = set()
    seen_hit_keys: dict[str, set[tuple[str, str, str, str]]] = {}

    def _record_rlib_hits(
        raw_rl: bytes,
        rlib_name: str,
        scope_label: str,
        *,
        is_sysroot_scan: bool = False,
    ) -> str:
        rl_sha = elf_inspect.sha256_bytes(raw_rl)
        if is_sysroot_scan:
            scanned_sysroot_rlib_shas.add(rl_sha)
        elif rl_sha in scanned_sysroot_rlib_shas:
            # Byte-identical staged copy of an already-scanned toolchain sysroot `.rlib`
            return rl_sha
        if not re_target_syms:
            return rl_sha
        fast_hits = elf_inspect.scan_rlib_defined_symbols_fast(raw_rl, rlib_name, re_target_syms)
        for sym_k, mem_pairs in fast_hits.items():
            seen_s = seen_hit_keys.setdefault(sym_k, set())
            for m_name, m_sha in mem_pairs:
                dedup_k = (scope_label, rl_sha, m_name, m_sha)
                if dedup_k not in seen_s:
                    seen_s.add(dedup_k)
                    rlib_exact_hits.setdefault(sym_k, []).append(
                        (scope_label, rlib_name, rl_sha, m_name, m_sha)
                    )
        return rl_sha

    if lock_rust_extracted:
        # G-F2 / SR-41 F1 / STOCK-REV F1: fail closed on missing sysroot, `rustc -V` mismatch,
        # or missing `lib/rustlib/<image_target_triple>/lib`, and scan ONLY `image_target_triples`.
        rlib_counts_by_triple: dict[str, int] = {}
        sysroot_rustc_ver: str | None = None
        if not lock_rustc_ver:
            errors.append(
                "0f(vi): lock `rustc_version` is required when `rust_extracted` is non-empty"
            )
        elif rustc_ver and lock_rustc_ver != rustc_ver:
            errors.append(
                f"0f(vi): lock `rustc_version` {lock_rustc_ver!r} != metadata `rustc_version` {rustc_ver!r}"
            )

        if eff_toolchain_sysroot is None or not (eff_toolchain_sysroot / "lib/rustlib").is_dir():
            errors.append("0f(vi): toolchain sysroot not found; route-order scan cannot run")
        else:
            sysroot_rustc_ver, rver_err = _query_sysroot_rustc_version(eff_toolchain_sysroot)
            if rver_err is not None:
                errors.append(
                    f"0f(vi): toolchain sysroot {eff_toolchain_sysroot} `rustc -V` check failed: {rver_err}"
                )
            elif eff_expected_rustc_ver and sysroot_rustc_ver != eff_expected_rustc_ver:
                errors.append(
                    f"0f(vi): toolchain sysroot {eff_toolchain_sysroot} `rustc -V` version "
                    f"{sysroot_rustc_ver!r} != expected lock `rustc_version` {eff_expected_rustc_ver!r}"
                )

            for tgt_triple in image_target_triples:
                tgt_lib_dir = eff_toolchain_sysroot / "lib/rustlib" / tgt_triple / "lib"
                if not tgt_lib_dir.is_dir():
                    rlib_counts_by_triple[tgt_triple] = 0
                    errors.append(
                        f"0f(vi): toolchain sysroot {eff_toolchain_sysroot} missing image target triple "
                        f"directory `lib/rustlib/{tgt_triple}/lib`"
                    )
                    continue
                rl_files = [f for f in sorted(tgt_lib_dir.glob("*.rlib")) if f.is_file()]
                rlib_counts_by_triple[tgt_triple] = len(rl_files)
                if not rl_files:
                    errors.append(
                        f"0f(vi): toolchain sysroot `lib/rustlib/{tgt_triple}/lib` contains 0 `.rlib` archives"
                    )
                    continue
                for rl_file in rl_files:
                    try:
                        _record_rlib_hits(
                            rl_file.read_bytes(),
                            rl_file.name,
                            f"rustlib/{tgt_triple}",
                            is_sysroot_scan=True,
                        )
                    except Exception as exc:  # noqa: BLE001
                        errors.append(f"0f(vi): malformed toolchain `.rlib` {rl_file}: {exc}")

        toolchain_sysroot_scan_report = {
            "sysroot_path": str(eff_toolchain_sysroot) if eff_toolchain_sysroot is not None else None,
            "rustc_version": sysroot_rustc_ver,
            "expected_rustc_version": eff_expected_rustc_ver,
            "target_triples": list(image_target_triples),
            "rlib_counts_by_triple": rlib_counts_by_triple,
        }

        # 2. Scan any additional `pinned_rlibs` or staged `.rlib`s in `search_roots`
        if lock_data is not None and isinstance(lock_data.get("pinned_rlibs"), Mapping):
            for rl_key, rl_sha_exp in sorted(lock_data["pinned_rlibs"].items()):
                try:
                    rl_p = _resolve_staged_file(str(rl_key), rlib_roots, expected_sha256=str(rl_sha_exp))
                    raw_rl = rl_p.read_bytes()
                    got_rl_sha = _record_rlib_hits(raw_rl, rl_p.name, "pinned_rlibs")
                    if str(rl_sha_exp) and got_rl_sha != str(rl_sha_exp):
                        errors.append(
                            f"0f(vi): `pinned_rlibs[{rl_key!r}]` sha256 {got_rl_sha} != {rl_sha_exp}"
                        )
                except Exception as exc:  # noqa: BLE001
                    errors.append(f"0f(vi): failed to load `pinned_rlibs[{rl_key!r}]`: {exc}")

        for sroot in search_roots:
            if sroot.is_dir():
                for cand_rl in sorted(sroot.glob("*.rlib")):
                    if cand_rl.is_file():
                        try:
                            _record_rlib_hits(cand_rl.read_bytes(), cand_rl.name, "staged")
                        except Exception as exc:  # noqa: BLE001
                            errors.append(f"0f(vi): malformed staged `.rlib` {cand_rl}: {exc}")

    # Parse referenced kind-(a) `.rlib` archives and register them in `rlib_exact_hits` as well
    rlib_parsed_by_re: dict[str, elf_inspect.ParsedArchive] = {}
    for re_name, re_cfg in sorted(lock_rust_extracted.items()):
        if re_cfg.get("kind") != "rlib_member":
            continue
        try:
            rl_disk = _resolve_staged_file(
                re_cfg["rlib_path"], rlib_roots, expected_sha256=re_cfg["rlib_sha256"]
            )
        except FileNotFoundError as exc:
            errors.append(f"0f(vi) / GK 458 C1(a): `rust_extracted[{re_name!r}]` missing rlib: {exc}")
            continue
        raw_rl = rl_disk.read_bytes()
        got_rl_sha = _record_rlib_hits(raw_rl, rl_disk.name, f"rust_extracted:{re_name}")
        if got_rl_sha != re_cfg["rlib_sha256"]:
            errors.append(
                f"0f(vi) / GK 458 C1(a): `rust_extracted[{re_name!r}]` rlib {rl_disk.name} sha256 "
                f"{got_rl_sha} != pinned {re_cfg['rlib_sha256']}"
            )
            continue
        rlib_parsed_by_re[re_name] = elf_inspect.parse_rlib_archive(raw_rl, rl_disk.name)

    for re_name, re_cfg in sorted(lock_rust_extracted.items()):
        o_rec = standalone_by_name.get(re_name)
        if o_rec is None or o_rec.role != "N" or o_rec.obj is None:
            errors.append(f"GK 458 C1: `rust_extracted` entry {re_name!r} is missing from linked Class N inputs")
            continue
        if re_cfg.get("sha256") and o_rec.sha256 != re_cfg["sha256"]:
            errors.append(
                f"GK 458 C1: `rust_extracted[{re_name!r}]` linked `.o` sha256 {o_rec.sha256} != lock {re_cfg['sha256']}"
            )

        re_kind = str(re_cfg["kind"])
        # §0f(vi) & §0f(vii) Route-order + SR-35 NB1 ambiguity checks on every symbol defined by `o_rec`
        for dsym in sorted(o_rec.obj.defs_by_name.keys()):
            if dsym in exempted_set:
                continue
            if dsym in exact_defs_non_re:
                errors.append(
                    f"0f(vi) / SR-31 A1 route-order violation: `rust_extracted` {re_kind} {re_name!r} defines {dsym!r}, "
                    f"displacing exact-name definer in {exact_defs_non_re[dsym][0]}"
                )
            hits = rlib_exact_hits.get(dsym, [])
            if len(hits) > 1:
                fmt_hits = [f"{sc}:{rn}({mn})" for sc, rn, _rs, mn, _ms in hits]
                errors.append(
                    f"0f(vii) / SR-35 NB1: route-order scan ambiguous for {dsym!r} (defined by >1 rlib member): {fmt_hits}"
                )
            elif len(hits) == 1:
                h_scope, h_rname, h_rsha, h_mname, h_msha = hits[0]
                if re_kind == "alias_stub":
                    errors.append(
                        f"0f(vi) / SR-31 A1 route-order violation: alias_stub {re_name!r} defines {dsym!r}, "
                        f"displacing exact-name rlib definer {h_scope}:{h_rname}({h_mname})"
                    )
                elif (re_cfg["rlib_sha256"], re_cfg["member_sha256"]) != (h_rsha, h_msha):
                    errors.append(
                        f"0f(vi) / SR-31 A1 route-order violation: kind (a) {re_name!r} extracts {dsym!r} from "
                        f"({re_cfg['rlib_sha256'][:12]}, {re_cfg['member_sha256'][:12]}) instead of mandatory "
                        f"exact-name rlib definer {h_scope}:{h_rname}({h_mname}) ({h_rsha[:12]}, {h_msha[:12]})"
                    )

        if re_kind == "rlib_member":
            pr = rlib_parsed_by_re.get(re_name)
            rederived_ok = False
            keep_secs = list(re_cfg.get("keep_sections") or [])
            recipe_s = str(re_cfg.get("recipe") or "")
            if pr is not None:
                mem_name = str(re_cfg["member"])
                mcands = pr.members_by_name.get(mem_name, [])
                if len(mcands) > 1:
                    sha_filtered = [m for m in mcands if m.sha256 == re_cfg["member_sha256"]]
                    if len(sha_filtered) == 1:
                        mcands = sha_filtered
                if len(mcands) != 1:
                    errors.append(
                        f"0f(vi) / GK 458 C1(a): rlib {pr.label} has {len(mcands)} members named {mem_name!r} (expected 1)"
                    )
                else:
                    rmem = mcands[0]
                    if rmem.sha256 != re_cfg["member_sha256"]:
                        errors.append(
                            f"0f(vi) / GK 458 C1(a): `rust_extracted[{re_name!r}]` re-extracted member {mem_name!r} "
                            f"sha256 {rmem.sha256} != lock {re_cfg['member_sha256']}"
                        )
                    # §0f(vi) / GK 466 N-b & N-c: Re-derive the WHOLE extracted `.o` by its recipe and compare SHA-256!
                    if keep_secs and recipe_s:
                        try:
                            rederived_bytes = elf_inspect.rederive_rlib_subset_object(
                                rmem.data,
                                keep_secs,
                                recipe_s,
                                label=f"{pr.label}({mem_name})",
                                repo_root=eff_repo_root,
                                toolchain_sysroot=eff_toolchain_sysroot,
                            )
                            rederived_sha = elf_inspect.sha256_bytes(rederived_bytes)
                            if rederived_sha != re_cfg["sha256"] or o_rec.sha256 != rederived_sha:
                                errors.append(
                                    f"0f(vi) / GK 466 N-b: `rust_extracted[{re_name!r}]` re-derived whole-object "
                                    f"sha256 {rederived_sha} != lock {re_cfg['sha256']} (linked={o_rec.sha256})"
                                )
                            else:
                                rederived_ok = rmem.sha256 == re_cfg["member_sha256"]
                        except Exception as exc:  # noqa: BLE001
                            errors.append(
                                f"0f(vi) / GK 466 N-b: `rust_extracted[{re_name!r}]` recipe re-derivation failed: {exc}"
                            )

                    if keep_secs:
                        trim_errs = _compare_trimmed_reloc_sections(
                            o_rec.obj, rmem.obj, keep_secs, f"rust_extracted[{re_name!r}]"
                        )
                        errors.extend(trim_errs)
                        if trim_errs:
                            rederived_ok = False

                    # End-to-end check: compare every retained symbol of `o_rec` in final ELF directly against `rmem.obj`
                    for rnode in retained_nodes:
                        if rnode.source_file != re_name:
                            continue
                        for dsym_name, dsym_list in sorted(o_rec.obj.defs_by_name.items()):
                            for dsym_obj in dsym_list:
                                if dsym_obj.st_shndx != rnode.sec.idx:
                                    continue
                                ref_syms = rmem.obj.defs_by_name.get(dsym_name, [])
                                if len(ref_syms) == 1:
                                    sym_vma = rnode.map_sec.vma + dsym_obj.st_value - (rnode.map_sec.piece_offset or 0)
                                    try:
                                        elf_inspect.compare_defined_symbol_bytes(
                                            obj=rmem.obj,
                                            sym=ref_syms[0],
                                            elf=elf,
                                            elf_vma=sym_vma,
                                            map_sec_size=rnode.map_sec.size,
                                        )
                                    except Exception as exc:  # noqa: BLE001
                                        errors.append(
                                            f"0f(vi): final ELF vs rlib member {pr.label}({mem_name}) mismatch "
                                            f"for {dsym_name!r}: {exc}"
                                        )
                                        rederived_ok = False

            rust_extracted_report[re_name] = {
                "kind": "rlib_member",
                "sha256": o_rec.sha256,
                "rlib_path": re_cfg["rlib_path"],
                "rlib_sha256": re_cfg["rlib_sha256"],
                "member": re_cfg["member"],
                "member_sha256": re_cfg["member_sha256"],
                "recipe": recipe_s,
                "keep_sections": keep_secs,
                "rederived_sha_equal": rederived_ok,
            }

        else:
            # `kind == "alias_stub"` (GK 458 C1(b) + SR-31 A1 & N4)
            try:
                asm_disk = _resolve_staged_file(
                    re_cfg["asm_path"], rlib_roots, expected_sha256=re_cfg["asm_sha256"]
                )
                got_asm_sha = elf_inspect.sha256_file(asm_disk)
                if got_asm_sha != re_cfg["asm_sha256"]:
                    errors.append(
                        f"GK 458 C1(b): `rust_extracted[{re_name!r}]` asm {asm_disk} sha256 {got_asm_sha} != "
                        f"lock {re_cfg['asm_sha256']}"
                    )
            except FileNotFoundError as exc:
                errors.append(f"GK 458 C1(b): `rust_extracted[{re_name!r}]` missing `.S` source: {exc}")

            alloc_secs = [
                s
                for s in o_rec.obj.sections
                if (s.sh_flags & elf_inspect.SHF_ALLOC) != 0 and s.sh_type != elf_inspect.SHT_NULL
            ]
            if not alloc_secs or not o_rec.obj.defs_by_name:
                errors.append(f"GK 458 C1(b): alias_stub {re_name!r} has empty SHF_ALLOC sections or 0 defined symbols")

            for asec in alloc_secs:
                if (
                    asec.sh_type != elf_inspect.SHT_PROGBITS
                    or (asec.sh_flags & elf_inspect.SHF_EXECINSTR) == 0
                    or (asec.sh_flags & elf_inspect.SHF_WRITE) != 0
                    or asec.sh_size < 4
                    or asec.sh_size % 4 != 0
                ):
                    errors.append(
                        f"GK 458 C1(b): alias_stub {re_name!r} section {asec.name!r} must be executable, "
                        f"read-only SHT_PROGBITS of 4B-aligned non-zero size (got type={asec.sh_type}, "
                        f"flags={asec.sh_flags:#x}, size={asec.sh_size})"
                    )
                    continue
                active_rels = [r for r in asec.relocs if r.r_type not in elf_inspect.R_AARCH64_NONE_SET]
                rel_by_off: dict[int, elf_inspect.RelocEntry] = {}
                for rel in active_rels:
                    if rel.r_type != 282 or rel.r_offset % 4 != 0 or rel.r_offset >= asec.sh_size or rel.r_addend != 0:
                        errors.append(
                            f"GK 458 C1(b) / SR-31 N4: alias_stub {re_name!r} section {asec.name!r} has forbidden "
                            f"relocation r_type={rel.r_type}, offset={rel.r_offset:#x}, addend={rel.r_addend} "
                            "(only R_AARCH64_JUMP26 `b <target>` with addend 0 is permitted)"
                        )
                    tsym_o = o_rec.obj.symbols[rel.sym_idx]
                    if tsym_o.is_local or not tsym_o.name:
                        errors.append(
                            f"GK 458 C1(b): alias_stub {re_name!r} section {asec.name!r} jumps to local/unnamed symbol"
                        )
                    rel_by_off[rel.r_offset] = rel

                for off in range(0, asec.sh_size, 4):
                    (insn_w,) = struct.unpack_from("<I", asec.data, off)
                    if (insn_w & 0xFC000000) != 0x14000000 or off not in rel_by_off:
                        errors.append(
                            f"GK 458 C1(b) / SR-31 N4: alias_stub {re_name!r} {asec.name}+0x{off:x} "
                            f"word {insn_w:#010x} is not a relocated unconditional `B` instruction"
                        )

            for dname, dlist in sorted(o_rec.obj.defs_by_name.items()):
                for ds in dlist:
                    if ds.st_size not in (0, 4) or ds.st_value % 4 != 0:
                        errors.append(
                            f"GK 458 C1(b): alias_stub {re_name!r} symbol {dname!r} invalid st_size={ds.st_size} / "
                            f"st_value={ds.st_value:#x} (expected single 4-byte `B` stub)"
                        )

            # Verify every retained alias_stub `B` instruction in the final ELF decodes to a retained R or N VMA
            branch_targets: dict[str, str] = {}
            for rnode in retained_nodes:
                if rnode.source_file != re_name:
                    continue
                p_lo = rnode.map_sec.piece_offset if rnode.map_sec.piece_offset is not None else 0
                p_hi = (p_lo + rnode.map_sec.size) if rnode.map_sec.piece_offset is not None else rnode.sec.sh_size
                for rel in rnode.sec.relocs:
                    if rel.r_type in elf_inspect.R_AARCH64_NONE_SET:
                        continue
                    if rnode.map_sec.piece_offset is not None and not (p_lo <= rel.r_offset < p_hi):
                        continue
                    tsym_name = rnode.obj.symbols[rel.sym_idx].name
                    _ec, wp = resolve_symbol_definer(tsym_name)
                    if len(wp) != 1 or wp[0][0].role not in ("R", "N"):
                        errors.append(
                            f"GK 458 C1(b) / SR-31 N4: alias_stub {re_name!r} target {tsym_name!r} must resolve to "
                            f"a single retained Class R or N definer, got {[p[0].node_id for p in wp]}"
                        )
                        continue
                    tgt_node, tgt_rsym = wp[0]
                    tgt_vma = tgt_node.map_sec.vma + tgt_rsym.st_value - (tgt_node.map_sec.piece_offset or 0)
                    word_vma = rnode.map_sec.vma + rel.r_offset - p_lo
                    (elf_w,) = struct.unpack("<I", elf.read_vma(word_vma, 4))
                    decoded_vma = elf_inspect.decode_aarch64_b_target(elf_w, word_vma)
                    if decoded_vma is None or decoded_vma != tgt_vma:
                        errors.append(
                            f"GK 458 C1(b) / SR-31 N4: alias_stub {re_name!r} ELF word {elf_w:#010x} at {word_vma:#x} "
                            f"decodes to {hex(decoded_vma) if decoded_vma is not None else None} != {tsym_name!r} VMA {tgt_vma:#x}"
                        )
                    else:
                        branch_targets[f"{rnode.node_id}+0x{rel.r_offset - p_lo:x}"] = f"{tsym_name}@{tgt_vma:#x}"

            rust_extracted_report[re_name] = {
                "kind": "alias_stub",
                "sha256": o_rec.sha256,
                "asm_path": re_cfg["asm_path"],
                "asm_sha256": re_cfg["asm_sha256"],
                "recipe": re_cfg["recipe"],
                "branch_targets": branch_targets,
            }

    # ==========================================================================
    # Step 13: Rule (vii) + GK Rows 373, 374, 375 Real-Body Checks (`s2_real_body_lock`)
    # ==========================================================================
    rustc_libc_pair: tuple[pathlib.Path, elf_inspect.ParsedArchive] | None = None
    if rustc_libc_a_path is not None:
        raw_libc = rustc_libc_a_path.read_bytes()
        if elf_inspect.sha256_bytes(raw_libc) != elf_inspect.PINNED_RUSTC_MUSL_LIBC_SHA256:
            errors.append(
                f"Rule (vii): `--rustc-libc-a` {rustc_libc_a_path} sha256 != {elf_inspect.PINNED_RUSTC_MUSL_LIBC_SHA256}"
            )
        rustc_libc_pair = (rustc_libc_a_path, elf_inspect.parse_ar_archive(raw_libc, str(rustc_libc_a_path)))
    else:
        rustc_libc_pair = elf_inspect.find_rustc_musl_libc_archive(eff_work, eff_repo_root)

    if rustc_libc_pair is None:
        errors.append(
            f"Rule (vii): cannot locate pinned rustc 1.98.1 `self-contained/libc.a` "
            f"(sha256={elf_inspect.PINNED_RUSTC_MUSL_LIBC_SHA256})"
        )

    s2_real_body_lock: dict[str, dict[str, Any]] = {}
    for s2_key in S2_REAL_BODY_KEYS:
        if s2_key not in winning_node_by_x:
            errors.append(f"Rule (vii)/S2: required symbol {s2_key!r} missing from active definers")
            continue
        snode, srsym, sesym = winning_node_by_x[s2_key]
        dcls = "S" if snode.role.startswith("S:") else snode.role
        if srsym.bind == elf_inspect.STB_WEAK:
            errors.append(f"Rule (vii): `{s2_key}` input binding in {snode.node_id} is STB_WEAK")

        eff_sz = sesym.st_size if sesym.st_size > 0 else (snode.sec.sh_size - srsym.st_value)
        elf_body = elf.read_vma(sesym.st_value, eff_sz)
        body_sha = elf_inspect.sha256_bytes(elf_body)
        input_sym_bytes = snode.sec.data[srsym.st_value : srsym.st_value + eff_sz]
        input_text_sha = elf_inspect.sha256_bytes(input_sym_bytes)
        sec_relocs = elf_inspect.format_section_relocs(snode.obj, snode.sec)

        s2_row: dict[str, Any] = {
            "definer_class": dcls,
            "elf_addr": hex(sesym.st_value),
            "size": int(eff_sz),
            "input_section": snode.sec.name,
            "source_file": snode.source_file,
            "archive_member": snode.archive_member,
            "sha256": snode.file_sha256,
            "archive_sha256": snode.archive_sha256,
            "input_binding": srsym.bind_name,
            "text_sha": input_text_sha,
            "body_sha256": body_sha,
            "relocs": sec_relocs,
        }

        if s2_key == "strlen":
            # GK row 373 change 2 + SR-31 A2: st_size == 0x58 (88), 0 relocs, ELF [strlen, +88) == muslStrlenWords,
            # AND re-extract `strlen.lo` from pinned rustc `libc.a` and byte-compare full `.o`/`.lo`!
            if sesym.st_size != 0x58:
                errors.append(f"Rule (vii): `strlen` ELF st_size={sesym.st_size:#x} != 0x58 (88)")
            if len(sec_relocs) != 0:
                errors.append(f"Rule (vii): `strlen` defining section has {len(sec_relocs)} relocs (expected 0)")
            if elf_body != musl_strlen_bytes:
                errors.append("Rule (vii): `strlen` final ELF 88-byte body != `muslStrlenWords`")
            if snode.file_sha256 != elf_inspect.PINNED_STRLEN_MEMBER_SHA256:
                errors.append(
                    f"Rule (vii)/S1: `strlen` defining object sha256 {snode.file_sha256} != "
                    f"pinned `strlen.lo` {elf_inspect.PINNED_STRLEN_MEMBER_SHA256}"
                )
            reextracted_strlen_ok = True
            if rustc_libc_pair is not None:
                _lp, rustc_arch = rustc_libc_pair
                sl_list = rustc_arch.members_by_name.get("strlen.lo", [])
                if len(sl_list) != 1:
                    errors.append("SR-31 A2: rustc `libc.a` missing unique `strlen.lo` member")
                    reextracted_strlen_ok = False
                else:
                    sl_mem = sl_list[0]
                    if sl_mem.sha256 != elf_inspect.PINNED_STRLEN_MEMBER_SHA256:
                        errors.append(
                            f"SR-31 A2: re-extracted `libc.a(strlen.lo)` sha256 {sl_mem.sha256} != "
                            f"pinned {elf_inspect.PINNED_STRLEN_MEMBER_SHA256}"
                        )
                        reextracted_strlen_ok = False
            s2_row.update({
                "n_object_file_sha": snode.file_sha256 if dcls == "N" else None,
                "archive_sha": elf_inspect.PINNED_RUSTC_MUSL_LIBC_SHA256,
                "member_name": "strlen.lo",
                "member_file_sha": elf_inspect.PINNED_STRLEN_MEMBER_SHA256,
                "byte_equal": (
                    elf_body == musl_strlen_bytes
                    and sesym.st_size == 0x58
                    and len(sec_relocs) == 0
                    and reextracted_strlen_ok
                ),
                "n_text_relocs": len(sec_relocs) if dcls == "N" else None,
                "member_text_relocs": len(sec_relocs),
            })
            definers_table[s2_key]["byte_equal"] = s2_row["byte_equal"]

        elif s2_key in ("memcpy", "memset"):
            # GK rows 374 & 375 + SR-31 A2: 0 relocs on BOTH sides + input `.text` & final ELF == rustc libc.a member `.text`
            mem_name = f"{s2_key}.lo"
            if len(sec_relocs) != 0:
                errors.append(f"GK row 374/375: `{s2_key}` defining input has {len(sec_relocs)} relocs (expected 0)")
            if rustc_libc_pair is not None:
                _lp, rustc_arch = rustc_libc_pair
                mem_list = rustc_arch.members_by_name.get(mem_name, [])
                if len(mem_list) != 1:
                    errors.append(f"GK row 375: rustc `libc.a` missing unique member `{mem_name}`")
                else:
                    rmem = mem_list[0]
                    rsyms = rmem.obj.defs_by_name.get(s2_key, [])
                    if len(rsyms) != 1:
                        errors.append(f"GK row 375: `{mem_name}` missing unique `{s2_key}` symbol")
                    else:
                        ref_sym = rsyms[0]
                        ref_sec = rmem.obj.sections[ref_sym.st_shndx]
                        ref_relocs = elf_inspect.format_section_relocs(rmem.obj, ref_sec)
                        if len(ref_relocs) != 0:
                            errors.append(
                                f"GK row 374/375: rustc `libc.a({mem_name})` `.text` has {len(ref_relocs)} relocs (expected 0)"
                            )
                        ref_sz = ref_sym.st_size if ref_sym.st_size > 0 else (ref_sec.sh_size - ref_sym.st_value)
                        ref_bytes = ref_sec.data[ref_sym.st_value : ref_sym.st_value + ref_sz]
                        if input_sym_bytes != ref_bytes:
                            errors.append(
                                f"SR-31 A2: `{s2_key}` Class N input `.text` != re-extracted `libc.a({mem_name})` `.text`"
                            )
                        if sesym.st_size != ref_sz or elf_body != ref_bytes:
                            errors.append(
                                f"GK row 375: `{s2_key}` final ELF body ({sesym.st_size} B, sha={body_sha[:16]}) "
                                f"!= rustc `libc.a({mem_name})` `.text` ({ref_sz} B, sha={elf_inspect.sha256_bytes(ref_bytes)[:16]})"
                            )
                        eq_ok = (
                            sesym.st_size == ref_sz
                            and input_sym_bytes == ref_bytes
                            and elf_body == ref_bytes
                            and len(sec_relocs) == 0
                            and len(ref_relocs) == 0
                        )
                        s2_row.update({
                            "n_object_file_sha": snode.file_sha256 if dcls == "N" else None,
                            "archive_sha": rustc_arch.sha256,
                            "member_name": mem_name,
                            "member_file_sha": rmem.sha256,
                            "byte_equal": eq_ok,
                            "n_text_relocs": len(sec_relocs),
                            "member_text_relocs": len(ref_relocs),
                        })
                        definers_table[s2_key]["byte_equal"] = eq_ok

        else:
            # `memmove`, `memcmp`, `bcmp`: WP7 Class R `libc.a` (`memmove.lo`, `memcmp.lo`, `bcmp.lo`)
            mem_name = f"{s2_key}.lo"
            if dcls != "R" or snode.source_file != "libc.a" or snode.archive_member != mem_name:
                errors.append(
                    f"GK row 375: expected `{s2_key}` to have Class R definer `libc.a({mem_name})`, "
                    f"got class={dcls!r}, source={snode.source_file!r}, member={snode.archive_member!r}"
                )
            if rustc_libc_pair is not None:
                _lp, rustc_arch = rustc_libc_pair
                mem_list = rustc_arch.members_by_name.get(mem_name, [])
                if len(mem_list) != 1:
                    errors.append(f"GK row 375: rustc `libc.a` missing unique member `{mem_name}`")
                else:
                    rmem = mem_list[0]
                    if snode.file_sha256 != rmem.sha256:
                        errors.append(
                            f"GK row 375: `{s2_key}` defining member sha256 {snode.file_sha256} != "
                            f"re-extracted `libc.a({mem_name})` {rmem.sha256}"
                        )
                    rsyms = rmem.obj.defs_by_name.get(s2_key, [])
                    if len(rsyms) != 1:
                        errors.append(f"GK row 375: `{mem_name}` missing unique `{s2_key}` symbol")
                    else:
                        ref_sym = rsyms[0]
                        ref_sec = rmem.obj.sections[ref_sym.st_shndx]
                        ref_relocs = elf_inspect.format_section_relocs(rmem.obj, ref_sec)
                        ref_sz = ref_sym.st_size if ref_sym.st_size > 0 else (ref_sec.sh_size - ref_sym.st_value)
                        ref_bytes = ref_sec.data[ref_sym.st_value : ref_sym.st_value + ref_sz]
                        if input_sym_bytes != ref_bytes or _canonicalize_reloc_list(sec_relocs) != _canonicalize_reloc_list(
                            ref_relocs
                        ):
                            errors.append(
                                f"GK row 375: `{s2_key}` defining input `.text`/relocs != re-extracted `libc.a({mem_name})`"
                            )
                        if s2_key == "memcmp" and (
                            len(sec_relocs) != 0 or sesym.st_size != ref_sz or elf_body != ref_bytes
                        ):
                            errors.append(
                                f"GK row 375: `memcmp` final ELF body ({sesym.st_size} B, relocs={len(sec_relocs)}) "
                                f"!= rustc `libc.a(memcmp.lo)` `.text` ({ref_sz} B)"
                            )
                        try:
                            elf_inspect.compare_defined_symbol_bytes(
                                obj=rmem.obj,
                                sym=ref_sym,
                                elf=elf,
                                elf_vma=sesym.st_value,
                                map_sec_size=snode.map_sec.size,
                            )
                            masked_ok = True
                        except Exception as exc:  # noqa: BLE001
                            masked_ok = False
                            errors.append(f"GK row 375: `{s2_key}` relocation-masked compare failed: {exc}")
                        eq_ok = (
                            dcls == "R"
                            and snode.source_file == "libc.a"
                            and snode.archive_member == mem_name
                            and snode.file_sha256 == rmem.sha256
                            and sesym.st_size == ref_sz
                            and input_sym_bytes == ref_bytes
                            and _canonicalize_reloc_list(sec_relocs) == _canonicalize_reloc_list(ref_relocs)
                            and masked_ok
                            and (s2_key != "memcmp" or (len(sec_relocs) == 0 and elf_body == ref_bytes))
                        )
                        s2_row.update({
                            "n_object_file_sha": None,
                            "archive_sha": rustc_arch.sha256,
                            "member_name": mem_name,
                            "member_file_sha": rmem.sha256,
                            "byte_equal": eq_ok,
                            "n_text_relocs": None,
                            "member_text_relocs": len(ref_relocs),
                        })
                        definers_table[s2_key]["byte_equal"] = eq_ok
            if s2_key == "bcmp":
                # GK row 375: single word decodes as unconditional `B` targeting `memcmp`'s final ELF VMA
                if sesym.st_size != 4 or len(elf_body) != 4:
                    errors.append(f"GK row 375: `bcmp` expected 4-byte single instruction, got size={sesym.st_size}")
                elif "memcmp" not in winning_node_by_x:
                    errors.append("GK row 375: `memcmp` missing when verifying `bcmp` branch target")
                else:
                    (b_word,) = struct.unpack("<I", elf_body)
                    b_tgt = elf_inspect.decode_aarch64_b_target(b_word, sesym.st_value)
                    memcmp_vma = winning_node_by_x["memcmp"][2].st_value
                    if b_tgt is None or b_tgt != memcmp_vma:
                        errors.append(
                            f"GK row 375: `bcmp` word {b_word:#010x} at {sesym.st_value:#x} decodes to "
                            f"{hex(b_tgt) if b_tgt is not None else None} != `memcmp` VMA {memcmp_vma:#x}"
                        )
                    s2_row["bcmp_branch_target"] = hex(b_tgt) if b_tgt is not None else None

        s2_real_body_lock[s2_key] = s2_row

    # ==========================================================================
    # Step 14: D1 Kept `STT_OBJECT` Extern-Data Audit (GK row 372)
    # ==========================================================================
    # Every non-placed `STT_OBJECT` referenced by a kept `cliLinkObjs` (`S:0`) relocation must be in
    # `DEFAULT_TRUSTED_EXTERN_DATA` (`{MAX_LOG_LEVEL_FILTER, ED25519_BASEPOINT_TABLE, GETRANDOM_FN, WHITESPACE_MAP}`).
    kept_extern_data: dict[str, dict[str, Any]] = {}
    for x in x_per_image.get("0", []):
        if x not in winning_node_by_x:
            continue
        wnode, wrsym, wesym = winning_node_by_x[x]
        s0_refs = [n for n in surviving_referrers_by_node.get(x, []) if n.role == "S:0"]
        if not s0_refs:
            continue
        if wesym.stype == elf_inspect.STT_OBJECT or wrsym.stype == elf_inspect.STT_OBJECT or x in elf_inspect.DEFAULT_TRUSTED_EXTERN_DATA:
            if x not in elf_inspect.DEFAULT_TRUSTED_EXTERN_DATA:
                errors.append(
                    f"D1 violation (GK row 372): unexpected kept `STT_OBJECT` {x!r} "
                    f"({elf_inspect.demangle_rust(x)}) referenced by `cliLinkObjs`"
                )
            if wnode.role != "Z":
                errors.append(
                    f"D1 violation: kept externData {x!r} resolved to {wnode.role} ({wnode.node_id}), expected Class Z zero stub"
                )
            kept_extern_data[x] = {
                "demangled_name": elf_inspect.demangle_rust(x),
                "definer_class": wnode.role,
                "definer_kind": "stub_object",
                "elf_addr": hex(wesym.st_value),
                "size": int(wesym.st_size),
                "input_section": wnode.sec.name,
                "source_file": wnode.source_file,
                "archive_member": wnode.archive_member,
                "sha256": wnode.file_sha256,
            }

    gc_dead_extern_data = sorted(elf_inspect.DEFAULT_TRUSTED_EXTERN_DATA - set(kept_extern_data.keys()))
    d1_extern_data_lock: dict[str, Any] = {
        "total_proved_extern_data": len(elf_inspect.DEFAULT_TRUSTED_EXTERN_DATA),
        "kept": kept_extern_data,
        "gc_dead": gc_dead_extern_data,
        "gc_dead_demangled": [elf_inspect.demangle_rust(s) for s in gc_dead_extern_data],
    }

    # Assemble stub, harness, and compiler_builtins summary metadata
    stub_summary: dict[str, Any] = {
        "name": stub_record.name,
        "sha256": stub_record.sha256,
        "size": stub_record.size,
        "symbol_count": len(stub_record.obj.defs_by_name),
        "stub_manifest_sha256": (
            str(cv_meta.get("stub_manifest_sha256", "")) if cv_meta is not None else None
        ),
    }
    harness_summary: dict[str, Any] = {
        "name": harness_record.name,
        "sha256": harness_record.sha256,
        "size": harness_record.size,
        "weakened_in_main": weakened_in_main,
    }
    cb_rec = archives_by_name.get("compiler_builtins.a")
    cb_summary: dict[str, Any] | None = (
        {"name": cb_rec.name, "sha256": cb_rec.sha256, "size": cb_rec.size} if cb_rec is not None else None
    )

    report = ALinkReport(
        recipe=recipe,
        config_count=len(image_records),
        configs=config_paths,
        elf_path=str(elf_path),
        elf_sha256=elf.sha256,
        elf_size=elf.size,
        elf_entry=hex(elf.entry),
        main_elf_addr=hex(main_elf_vma),
        placed_exports=placed_exports_report,
        x_per_image=x_per_image,
        x_all=x_all,
        x_count=len(x_all),
        x_sha256=x_sha256,
        hooked_externs_count=len(hooked_externs) if hooked_externs is not None else None,
        engine_hooked_externs_sha256=hooked_externs_sha,
        x_minus_hooked_externs=x_minus_hooked,
        data_only_in_x=data_only_in_x,
        class_histogram=class_histogram,
        zero_definer_names=zero_definer_names,
        multi_definer_names=multi_definer_names,
        discarded=discarded_names,
        definers=definers_table,
        real_hook_reached=expected_real_hook_reached,
        real_proved=expected_real_proved,
        harness_startup_referrers=harness_startup_refs,
        failstop_z=canonical_failstop_z,
        hook_closures=hook_closures,
        displaced_weak=sorted(actual_displaced_by_z),
        displaced_weak_elf_addrs=displaced_weak_addrs,
        displaced_weak_referrers=displaced_weak_referrers,
        displaced_weak_non_lib0_relocs_pre_gc=non_lib0_atomic_relocs_pre_gc,
        n_undef_map=n_undef_map,
        s2_real_body_lock=s2_real_body_lock,
        d1_extern_data_lock=d1_extern_data_lock,
        weakened_in_main=weakened_in_main,
        exempted_aliases=exempted_aliases,
        weak_undefined_allowed=allowed_uw,
        sysroot_trims=sysroot_trims_report,
        runtime_archives=dict(sorted(runtime_archives_map.items())),
        native_objects=dict(sorted(native_objects_map.items())),
        stub_object=stub_summary,
        harness_object=harness_summary,
        compiler_builtins_archive=cb_summary,
        lld_argv=lld_argv_tmpl,
        lld_version=lld_version,
        stock_lld_arg_files=dict(sorted(arg_files.items())),
        engine_commit=engine_commit,
        rustc_version=rustc_ver,
        zig_version=zig_ver,
        rust_extracted=dict(sorted(rust_extracted_report.items())),
        toolchain_sysroot_scan=toolchain_sysroot_scan_report,
        proved_closures=proved_closures,
        inputs_lock_pin=inputs_lock_pin_summary,
        violations=errors,
    )

    if lock_data is not None:
        lock_errs = verify_report_against_lock(report, lock_data, repo_root=eff_repo_root)
        existing_v = set(report.violations)
        for le in lock_errs:
            if le not in existing_v:
                report.violations.append(le)
                existing_v.add(le)

    if raise_on_error and report.violations:
        raise ALinkError(report.violations)
    return report


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="A-LINK v0.3.2 (P8) stock-linker checker")
    ap.add_argument(
        "--out-dir",
        type=pathlib.Path,
        default=None,
        help="Directory with ELF + stock-link.json / cv-stock-link.json (default: <repo-root>/.GeneratedLean/cli-elf)",
    )
    ap.add_argument("--work-dir", type=pathlib.Path, default=None, help="Staged `.o`/`.a` directory (default: <out-dir>/work)")
    ap.add_argument("--elf", type=pathlib.Path, default=None, help="Explicit linked ELF path")
    ap.add_argument("--map", type=pathlib.Path, default=None, help="Explicit ld.lld -Map file path")
    ap.add_argument("--stock-link-json", type=pathlib.Path, default=None, help="Explicit engine stock-link.json")
    ap.add_argument("--cv-stock-link-json", type=pathlib.Path, default=None, help="Explicit builder cv-stock-link.json")
    ap.add_argument("--repo-root", type=pathlib.Path, default=None, help="Repository root for spec/config cross-checks")
    ap.add_argument("--rustc-libc-a", type=pathlib.Path, default=None, help="Explicit rustc 1.98.1 musl self-contained/libc.a")
    ap.add_argument("--toolchain-sysroot", type=pathlib.Path, default=None, help="Explicit rustc toolchain sysroot for 0f(vi) rlib scan")
    ap.add_argument("--trace-log", type=pathlib.Path, default=None, help="Optional ld.lld --trace-symbol log")
    ap.add_argument("--lock", type=pathlib.Path, default=None, help="M4 lock file (.toml or .json) for fail-on-diff check")
    ap.add_argument(
        "--inputs-lock",
        type=pathlib.Path,
        default=None,
        help="Pinned inputs.lock (.toml/.json); verifies `m4_lock_sha256` and `repo_root/m4_lock_path` realpath (GK 492 K2 + SR-62)",
    )
    ap.add_argument(
        "--ci",
        action="store_true",
        help="CI mode: requires `--inputs-lock` and `--lock` and fails closed on any unpinned lock (GK 492 K2)",
    )
    ap.add_argument("--atomics-mode", choices=("alpha", "beta"), default="alpha", help="Outline atomics policy (default: alpha)")
    ap.add_argument("--json-out", type=pathlib.Path, default=None, help="Write full JSON report to this path")
    args = ap.parse_args(argv)

    try:
        rep = check_stock_link(
            out_dir=args.out_dir,
            work_dir=args.work_dir,
            elf_path=args.elf,
            map_path=args.map,
            stock_link_json=args.stock_link_json,
            cv_stock_link_json=args.cv_stock_link_json,
            repo_root=args.repo_root,
            rustc_libc_a_path=args.rustc_libc_a,
            toolchain_sysroot=args.toolchain_sysroot,
            trace_log_path=args.trace_log,
            lock_path=args.lock,
            inputs_lock_path=args.inputs_lock,
            ci=args.ci,
            atomics_mode=args.atomics_mode,
            raise_on_error=False,
        )
        if args.json_out is not None:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(rep.to_json_dict(), indent=2) + "\n", encoding="utf-8")
        if rep.violations:
            raise ALinkError(rep.violations)
    except Exception as exc:  # noqa: BLE001
        print(f"alink_check: FAIL: {exc}", file=sys.stderr)
        return 1

    hist_str = ", ".join(f"{k}={v}" for k, v in rep.class_histogram.items())
    print(
        f"alink_check: PASS ({rep.recipe} {rep.config_count}-cfg, ELF={pathlib.Path(rep.elf_path).name} "
        f"{rep.elf_sha256[:16]}..., |X|={rep.x_count}, [{hist_str}], "
        f"real_hook_reached={rep.real_hook_reached}, real_proved={rep.real_proved}, "
        f"displaced_weak={len(rep.displaced_weak)})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
