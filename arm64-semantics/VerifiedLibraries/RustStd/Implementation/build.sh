#!/bin/sh
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Extract unmodified Rust 1.98.1 aarch64-unknown-linux-musl `core` / `alloc` / `std`
# object code from the pinned rustup sysroot `.rlib`s (`libcore-89491010f55f6617.rlib`,
# `liballoc-33b97f6bdb98e862.rlib`, `libstd-32d384fccf68bbb7.rlib`) via partial
# relocatable linking (`rust-lld -r --unique --gc-sections`) into placed-library objects:
#   1. `build/rust_core_os_fn.o` (`rustCoreOsFnMultiLib`): `core::io::error::os_functions::get_os_functions`,
#      `core::io::error::os_functions::set_functions::set_functions_inner`, and `.data` `OS_FUNCTIONS`
#      (isolated because `std` accesses `OS_FUNCTIONS` via non-adjacent GOT pairs while `core`
#      accesses `OS_FUNCTIONS` via an adjacent relaxable GOT pair).
#   2. `build/rust_std_io.o` (`rustStdIoMultiLib`): the 7 `std` I/O entry routines
#      (`std::fs::read::inner`, `std::fs::write::inner`, `std::io::stdio::stdin`,
#      `<Stdin as Read>::read_to_end`, `std::io::stdio::stdout`, `<Stdout as Write>::write_all`,
#      `<Stdout as Write>::flush`) and all reachable `std` / `alloc` / `core` helpers and data,
#      leaving `OS_FUNCTIONS` and `Arm64.Rust.isPanicSymbol` / unwind abort slow paths external.
#   3. `build/rust_core.o` (`coreMultiLib`): `core::str::converts::from_utf8` (+ `UTF8_CHAR_WIDTH`
#      256-byte `.rodata`), `core::slice::memchr::memrchr`, and `core::fmt::write`.
#   4. `build/rust_alloc.o` (`allocMultiLib`): `alloc::fmt::format::format_inner` (+ `<String as
#      core::fmt::Write>` vtable and `RawVecInner::{do_reserve_and_handle, finish_grow}`) and
#      `<alloc::string::String as core::clone::Clone>::clone`, leaving `core::fmt::write`,
#      allocator entry points, `memcpy`, `_Unwind_Resume`, and `isPanicSymbol` slow paths external.
#   5. `build/rust_time.o` (`timeMultiLib`): `<std::time::SystemTime>::duration_since` (+ internal
#      `Timespec::sub_timespec` and GC'd `.rodata.cst16+0x0`) and
#      `<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add`, leaving
#      `core::option::expect_failed` external.
#   6. `build/rust_core_fmt.o` (`coreFmtMultiLib`): `<core::fmt::Formatter>::{write_str, pad,
#      pad_integral}`, `<str as core::fmt::Display>::fmt`, `<&str as core::fmt::Display>::fmt`,
#      and `<{u8, u32, u64, usize} as core::fmt::Display>::fmt` (+ `<u64>::_fmt_inner`,
#      `pad_integral::write_prefix`, `core::str::count::do_count_chars`, and `200`-byte `.rodata`
#      `DEC_DIGITS_LUT`), leaving unreachable `core::panicking::panic_bounds_check` external.
set -eu

PINNED_RUSTC_PREFIX="rustc 1.98.1"
PINNED_LIBCORE_NAME="libcore-89491010f55f6617.rlib"
PINNED_LIBCORE_SHA256="3397f27434f891334ee2e29352a2fbab8de590e93b496379ee8bc1ab4b17cca9"
PINNED_LIBALLOC_NAME="liballoc-33b97f6bdb98e862.rlib"
PINNED_LIBALLOC_SHA256="963b439cd8b6e922258cab604c3b8f0dfc0757fa8552911ddcb3127369422451"
PINNED_LIBSTD_NAME="libstd-32d384fccf68bbb7.rlib"
PINNED_LIBSTD_SHA256="0ab6dccc7d4304f3a0848dadb8820964d86747b75af12f3921f1d48a1d185579"

RUSTC_BIN="${RUSTC:-rustc}"
RUSTC_VER="$("$RUSTC_BIN" --version 2>/dev/null || true)"
case "$RUSTC_VER" in
  "$PINNED_RUSTC_PREFIX"*)
    SYSROOT="$("$RUSTC_BIN" --print sysroot)"
    HOST_TRIPLE="$("$RUSTC_BIN" -vV | sed -n 's/^host: //p')"
    ;;
  *)
    if command -v rustup >/dev/null 2>&1; then
      RUSTC_BIN="$(rustup which --toolchain 1.98.1 rustc)"
      RUSTC_VER="$("$RUSTC_BIN" --version)"
      case "$RUSTC_VER" in
        "$PINNED_RUSTC_PREFIX"*) ;;
        *)
          echo "error: expected $PINNED_RUSTC_PREFIX, got $RUSTC_VER" >&2
          exit 1
          ;;
      esac
      SYSROOT="$("$RUSTC_BIN" --print sysroot)"
      HOST_TRIPLE="$("$RUSTC_BIN" -vV | sed -n 's/^host: //p')"
    else
      echo "error: expected $PINNED_RUSTC_PREFIX on PATH (got '$RUSTC_VER') and rustup is unavailable" >&2
      exit 1
    fi
    ;;
esac

MUSL_LIB_DIR="$SYSROOT/lib/rustlib/aarch64-unknown-linux-musl/lib"
LIBCORE_RLIB="$MUSL_LIB_DIR/$PINNED_LIBCORE_NAME"
LIBALLOC_RLIB="$MUSL_LIB_DIR/$PINNED_LIBALLOC_NAME"
LIBSTD_RLIB="$MUSL_LIB_DIR/$PINNED_LIBSTD_NAME"

check_rlib() {
  rlib_path="$1"
  expected_sha="$2"
  if [ ! -f "$rlib_path" ]; then
    echo "error: missing $rlib_path (install target aarch64-unknown-linux-musl for rustc 1.98.1)" >&2
    exit 1
  fi
  actual_sha="$(sha256sum "$rlib_path" | awk '{print $1}')"
  if [ "$actual_sha" != "$expected_sha" ]; then
    echo "error: SHA-256 mismatch on $rlib_path: expected $expected_sha, got $actual_sha" >&2
    exit 1
  fi
}

check_rlib "$LIBCORE_RLIB" "$PINNED_LIBCORE_SHA256"
check_rlib "$LIBALLOC_RLIB" "$PINNED_LIBALLOC_SHA256"
check_rlib "$LIBSTD_RLIB" "$PINNED_LIBSTD_SHA256"

BIN_DIR="$SYSROOT/lib/rustlib/$HOST_TRIPLE/bin"
LLD_BIN="$BIN_DIR/gcc-ld/ld.lld"
AR_BIN="$BIN_DIR/llvm-ar"
OBJCOPY_BIN="$BIN_DIR/llvm-objcopy"

for tool in "$LLD_BIN" "$AR_BIN" "$OBJCOPY_BIN"; do
  if [ ! -x "$tool" ]; then
    echo "error: missing bundled LLVM/LLD tool at $tool (install rustup component llvm-tools for 1.98.1)" >&2
    exit 1
  fi
done

mkdir -p build
WORK_DIR="build/work.$$"
rm -rf "$WORK_DIR"
trap 'rm -rf "$WORK_DIR"' EXIT
mkdir -p "$WORK_DIR/core" "$WORK_DIR/alloc" "$WORK_DIR/std"

extract_and_strip_unwind() {
  rlib_path="$1"
  dest_dir="$2"
  (cd "$dest_dir" && "$AR_BIN" x "$rlib_path")
  rcgu_obj="$(ls "$dest_dir"/*.rcgu.o)"
  # Strip DWARF unwind tables (.eh_frame* / .gcc_except_table*) so `ld.lld --gc-sections`
  # does not retain unreachable landing-pad references; `.text*` / `.rodata*` / `.data*` / `.tbss*`
  # bytes and relocations remain 100% byte-identical to upstream `.rlib`.
  "$OBJCOPY_BIN" --wildcard \
    --remove-section='.eh_frame*' \
    --remove-section='.rela.eh_frame*' \
    --remove-section='.gcc_except_table*' \
    --remove-section='.rela.gcc_except_table*' \
    "$rcgu_obj"
  printf '%s\n' "$rcgu_obj"
}

CORE_OBJ="$(extract_and_strip_unwind "$LIBCORE_RLIB" "$WORK_DIR/core")"
ALLOC_OBJ="$(extract_and_strip_unwind "$LIBALLOC_RLIB" "$WORK_DIR/alloc")"
STD_OBJ="$(extract_and_strip_unwind "$LIBSTD_RLIB" "$WORK_DIR/std")"

# 1. Link `build/rust_core_os_fn.o` (`rustCoreOsFnMultiLib`) from untouched `core` `.rcgu.o`.
cp "$CORE_OBJ" "$WORK_DIR/core_osfn.o"
"$LLD_BIN" -r --unique --gc-sections \
  -u _RNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions16get_os_functions \
  -u _RNvNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions13set_functions19set_functions_inner \
  "$WORK_DIR/core_osfn.o" \
  -o "$WORK_DIR/rust_core_os_fn.o"
mv -f "$WORK_DIR/rust_core_os_fn.o" build/rust_core_os_fn.o

# 2. Convert boundary symbols (`OS_FUNCTIONS` + `os_functions` helpers placed in `rustCoreOsFnMultiLib`,
#    `Arm64.Rust.isPanicSymbol` panic/alloc-abort entry points, non-returning panic/abort slow paths,
#    and unused `StringError` formatting vtable methods) to `SHN_UNDEF` in staged `.symtab` without
#    touching any section bytes or relocations, then link placed-library objects.
python3 - "$CORE_OBJ" "$ALLOC_OBJ" "$STD_OBJ" <<'PY'
import struct
import sys

BOUNDARY_UNDEF = {
    # Placed in `rustCoreOsFnMultiLib`:
    "_RNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions12OS_FUNCTIONS",
    "_RNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions16get_os_functions",
    "_RNvNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions13set_functions19set_functions_inner",
    # `Arm64.Rust.isPanicSymbol` panic / alloc-abort boundaries:
    "_RNvNtCshlmZ2E5RoO1_5alloc5alloc18handle_alloc_error",
    "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error",
    "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec17capacity_overflow",
    "_RNvNtCs2kXltWtc1W_4core6result13unwrap_failed",
    "_RNvNtCs2kXltWtc1W_4core6option13unwrap_failed",
    "_RNvNtCs2kXltWtc1W_4core6option13expect_failed",
    "_RNvNtNtCs2kXltWtc1W_4core5slice5index24slice_start_index_len_fail",
    "_RNvNtNtCs2kXltWtc1W_4core5slice5index22slice_end_index_len_fail",
    "_RNvNtNtCs2kXltWtc1W_4core5slice5index22slice_index_order_fail",
    "_RNvNtNtCs2kXltWtc1W_4core5slice5index16slice_index_fail",
    "_RNvNtCs2kXltWtc1W_4core9panicking18panic_bounds_check",
    "_RNvNtCs2kXltWtc1W_4core9panicking9panic_fmt",
    "_RNvNtCs2kXltWtc1W_4core9panicking16panic_in_cleanup",
    "_RNvNtCs2kXltWtc1W_4core9panicking14panic_nounwind",
    "_RNvNtCs2kXltWtc1W_4core9panicking5panic",
    # Non-`isPanicSymbol` panic / abort / unwind slow paths (audited in `G-SITES`):
    "_RNvNtCs2kXltWtc1W_4core4cell22panic_already_borrowed",
    "_RNvNvMNtNtCsiKaSbYLw9fL_3std6thread2idNtB4_8ThreadId3new9exhausted",
    "_RNvNtNtCsiKaSbYLw9fL_3std9panicking11panic_count17is_zero_slow_path",
    # Unused `fmt::Debug` / `fmt::Display` vtable methods on `StringError`:
    "_RNvXs0_NvXsf_NtNtCshlmZ2E5RoO1_5alloc5boxed7convertINtBd_3BoxDNtNtCs2kXltWtc1W_4core5error5ErrorNtNtB12_6marker4SendNtB1y_4SyncEL_EINtNtB12_7convert4FromNtNtBf_6string6StringE4fromNtB5_11StringErrorNtNtB12_3fmt5Debug3fmt",
    "_RNvXs_NvXsf_NtNtCshlmZ2E5RoO1_5alloc5boxed7convertINtBc_3BoxDNtNtCs2kXltWtc1W_4core5error5ErrorNtNtB11_6marker4SendNtB1x_4SyncEL_EINtNtB11_7convert4FromNtNtBe_6string6StringE4fromNtB4_11StringErrorNtNtB11_3fmt7Display3fmt",
}

for obj_path in sys.argv[1:]:
    buf = bytearray(open(obj_path, "rb").read())
    e_shoff, = struct.unpack_from("<Q", buf, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", buf, 58)
    if e_shnum == 0 and e_shoff != 0:
        _, _, _, _, _, sh_size0, sh_link0, _, _, _ = struct.unpack_from("<IIQQQQIIQQ", buf, e_shoff)
        e_shnum = sh_size0
        if e_shstrndx == 0xffff:
            e_shstrndx = sh_link0
    elif e_shstrndx == 0xffff:
        _, _, _, _, _, _, sh_link0, _, _, _ = struct.unpack_from("<IIQQQQIIQQ", buf, e_shoff)
        e_shstrndx = sh_link0
    shdrs = [struct.unpack_from("<IIQQQQIIQQ", buf, e_shoff + i * e_shentsize) for i in range(e_shnum)]
    symtab_i = next(i for i, sh in enumerate(shdrs) if sh[1] == 2)
    symtab_shndx_i = next((i for i, sh in enumerate(shdrs) if sh[1] == 18), None)
    st = shdrs[symtab_i]
    str_sh = shdrs[st[6]]
    strtab = bytes(buf[str_sh[4]:str_sh[4] + str_sh[5]])
    nsyms = st[5] // 24
    for si in range(nsyms):
        off = st[4] + si * 24
        st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", buf, off)
        end = strtab.find(b"\x00", st_name)
        name = strtab[st_name:end].decode("utf-8", errors="replace")
        if (st_info >> 4) != 0 and name in BOUNDARY_UNDEF:
            struct.pack_into("<IBBHQQ", buf, off, st_name, 0x10, 0, 0, 0, 0)
            if symtab_shndx_i is not None:
                sx_off = shdrs[symtab_shndx_i][4] + si * 4
                struct.pack_into("<I", buf, sx_off, 0)
    with open(obj_path, "wb") as fh:
        fh.write(buf)
PY

# 2a. Link `build/rust_std_io.o` (`rustStdIoMultiLib`).
"$LLD_BIN" -r --unique --gc-sections \
  -u _RNvNvNtCsiKaSbYLw9fL_3std2fs4read5inner \
  -u _RNvNvNtCsiKaSbYLw9fL_3std2fs5write5inner \
  -u _RNvNtNtCsiKaSbYLw9fL_3std2io5stdio5stdin \
  -u _RNvXs3_NtNtCsiKaSbYLw9fL_3std2io5stdioNtB5_5StdinNtB7_4Read11read_to_end \
  -u _RNvNtNtCsiKaSbYLw9fL_3std2io5stdio6stdout \
  -u _RNvXse_NtNtCsiKaSbYLw9fL_3std2io5stdioNtB5_6StdoutNtB7_5Write9write_all \
  -u _RNvXse_NtNtCsiKaSbYLw9fL_3std2io5stdioNtB5_6StdoutNtB7_5Write5flush \
  "$STD_OBJ" \
  "$ALLOC_OBJ" \
  "$CORE_OBJ" \
  -o "$WORK_DIR/rust_std_io.o"
mv -f "$WORK_DIR/rust_std_io.o" build/rust_std_io.o

# 2b. Link `build/rust_core.o` (`coreMultiLib`: `from_utf8` + `UTF8_CHAR_WIDTH`, `memrchr`, `fmt::write`).
"$LLD_BIN" -r --unique --gc-sections \
  -u _RNvNtNtCs2kXltWtc1W_4core3str8converts9from_utf8 \
  -u _RNvNtNtCs2kXltWtc1W_4core5slice6memchr7memrchr \
  -u _RNvNtCs2kXltWtc1W_4core3fmt5write \
  "$CORE_OBJ" \
  -o "$WORK_DIR/rust_core.o"
mv -f "$WORK_DIR/rust_core.o" build/rust_core.o

# 2c. Link `build/rust_alloc.o` (`allocMultiLib`: `format_inner` + `<String as fmt::Write>` vtable +
#     `RawVecInner::{do_reserve_and_handle, finish_grow}`, and `<String as Clone>::clone`).
"$LLD_BIN" -r --unique --gc-sections \
  -u _RNvNvNtCshlmZ2E5RoO1_5alloc3fmt6format12format_inner \
  -u _RNvXs4_NtCshlmZ2E5RoO1_5alloc6stringNtB5_6StringNtNtCs2kXltWtc1W_4core5clone5Clone5clone \
  "$ALLOC_OBJ" \
  -o "$WORK_DIR/rust_alloc.o"
mv -f "$WORK_DIR/rust_alloc.o" build/rust_alloc.o

# 2d. Link `build/rust_time.o` (`timeMultiLib`: `SystemTime::duration_since` + `Timespec::sub_timespec`
#     + GC'd `.rodata.cst16+0x0`, and `<SystemTime as Add<Duration>>::add`).
"$LLD_BIN" -r --unique --gc-sections \
  -u _RNvMs5_NtCsiKaSbYLw9fL_3std4timeNtB5_10SystemTime14duration_since \
  -u _RNvXs6_NtCsiKaSbYLw9fL_3std4timeNtB5_10SystemTimeINtNtNtCs2kXltWtc1W_4core3ops5arith3AddNtNtBS_4time8DurationE3add \
  "$STD_OBJ" \
  -o "$WORK_DIR/rust_time.o"
mv -f "$WORK_DIR/rust_time.o" build/rust_time.o

# 2e. Link `build/rust_core_fmt.o` (`coreFmtMultiLib`: `Formatter::{write_str, pad, pad_integral}`,
#     `<str as Display>::fmt`, `<&str as Display>::fmt`, and `<{u8, u32, u64, usize} as Display>::fmt`).
#     Promote `libcore`'s local `<&str as Display>::fmt` symbol binding to global in a staged copy
#     so `--gc-sections` retains and exports it without modifying any section bytes or relocations.
cp "$CORE_OBJ" "$WORK_DIR/core_fmt_in.o"
"$OBJCOPY_BIN" \
  --globalize-symbol=_RNvXs1i_NtCs2kXltWtc1W_4core3fmtReNtB6_7Display3fmtB8_ \
  "$WORK_DIR/core_fmt_in.o"
"$LLD_BIN" -r --unique --gc-sections \
  -u _RNvMsa_NtCs2kXltWtc1W_4core3fmtNtB5_9Formatter9write_str \
  -u _RNvMsa_NtCs2kXltWtc1W_4core3fmtNtB5_9Formatter3pad \
  -u _RNvMsa_NtCs2kXltWtc1W_4core3fmtNtB5_9Formatter12pad_integral \
  -u _RNvXsi_NtCs2kXltWtc1W_4core3fmteNtB5_7Display3fmt \
  -u _RNvXs1i_NtCs2kXltWtc1W_4core3fmtReNtB6_7Display3fmtB8_ \
  -u _RNvXNtNtNtCs2kXltWtc1W_4core3fmt3num3imphNtB6_7Display3fmt \
  -u _RNvXs8_NtNtNtCs2kXltWtc1W_4core3fmt3num3impmNtB9_7Display3fmt \
  -u _RNvXsd_NtNtNtCs2kXltWtc1W_4core3fmt3num3impyNtB9_7Display3fmt \
  -u _RNvXsi_NtNtNtCs2kXltWtc1W_4core3fmt3num3impjNtB9_7Display3fmt \
  "$WORK_DIR/core_fmt_in.o" \
  -o "$WORK_DIR/rust_core_fmt.o"
mv -f "$WORK_DIR/rust_core_fmt.o" build/rust_core_fmt.o
