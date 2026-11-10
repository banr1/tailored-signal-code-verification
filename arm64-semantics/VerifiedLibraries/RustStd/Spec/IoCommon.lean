/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.Alloc
public import VerifiedLibraries.RustStd.Generated.RustStdIoPlacedObj

/-!
# Shared Vocabulary for `std` I/O Specifications

Defines the frame predicates (`IoFrame`, `IoCallFrame`), C-path conversion and `openat` flag
constants (`cPathOf`, `stdReadOpenFlags`, `stdCreateTruncOpenFlags`), bit-packed `io::Error`
representations (`IoErr`, `IoErr.repr`), static/read-only image cells (`RustStdIoAddrs`,
`StdErrCells`, `IoImageRoCells`), and `io::Result<Vec<u8>>` layouts (`ioVecBuf`, `ioResultVecOk`,
`ioResultVecErr`). File-open specifications reuse `Arm64.openatPure` directly.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Frames and Paths -/

/-- The trace and the signal dispositions are unchanged from `s0` to `s`. Every allocation of the
    `std` I/O routines comes before the routine's first trace event, so each out-of-memory prefix
    is `IoFrame s0 sm ∧ <file-system clause>`. -/
abbrev IoFrame (s0 s : State) : Prop :=
  s.trace = s0.trace ∧ s.sigActions = s0.sigActions

/-- The path string `openat` reads from the bytes `bs` (each byte `b` becomes `Char.ofNat b.toNat`,
    as in `readCStringAux`). -/
def cPathOf (bs : List (BitVec 8)) : String :=
  String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- `openat` flags of `File::open(path)` in the compiled `std`: `O_RDONLY | O_CLOEXEC` from
    `OpenOptions::read(true)`, plus `O_LARGEFILE`, which musl `open` always adds. -/
def stdReadOpenFlags : BitVec 32 := O_CLOEXEC_W32 ||| O_LARGEFILE_W32

/-- `openat` flags of `File::create(path)` (`fs::write`) in the compiled `std`:
    `O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC`, plus musl's `O_LARGEFILE`. -/
def stdCreateTruncOpenFlags : BitVec 32 :=
  1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32 ||| O_LARGEFILE_W32

/-! ## Process Fields, `io::Error`, Statics, and `Vec<u8>` Results -/

/-- Process state that a compiled `std` I/O routine leaves unchanged on every return: signal
    dispositions, thread pointer, heap start, oracle and symbol table. The file system and the
    trace are stated separately by each spec; `brk` may move (allocator); memory changes only
    inside the spec's footprint (the separation-logic frame). -/
abbrev IoCallFrame (s0 sf : State) : Prop :=
  sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.brkStart = s0.brkStart ∧
    sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab

/-- `core::io::ErrorKind::OutOfMemory as usize` in Rust 1.98.1: its index (counting from 0) in
    `enum ErrorKind` (`core/src/io/error.rs`). -/
def ioErrorKindOutOfMemory : BitVec 64 := 38#64

/-- Addresses of the `std` statics the I/O routines use, wherever the library is placed:
    - `osFunctions`: `core::io::error::OS_FUNCTIONS`, an 8-byte pointer cell that the routines
      may overwrite (with the address of `std`'s `OsFunctions` table) when they build an OS
      error;
    - `errorFunctions`: `std`'s `OsFunctions` table; its word at `+16` is the address
      `isInterrupted` of `std::sys::io::error::unix::is_interrupted`, which the `EINTR` retry
      loops call (read only);
    - `nulErr`: the static `SimpleMessage` of `io::const_error!(InvalidInput, "file name
      contained an unexpected NUL byte")` (`NUL_ERR`, `std/src/sys/helpers/small_c_string.rs`);
    - `rodataCst8`: the placed address `mpl.ρ ioRodataCst8Sym` of the read-only 8-byte
      `OpenOptions` constant (`IoImageRoCells`); an image fact of the placed library, never a
      caller-supplied value;
    - `osFunctionsGot`: the placed address of `rust_std_io`'s GOT slot for `OS_FUNCTIONS` (symbol
      `_RNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions12OS_FUNCTIONS`, never relaxed), a
      read-only cell holding `osFunctions` (`IoImageRoCells`);
    - `emptyCStr`: the address of musl's empty C string `""` in musl's `.rodata` (one NUL byte),
      which musl `fstat` passes to `fstatat(fd, "", st, AT_EMPTY_PATH)` (read only; `fsReadSpec`).
      In a linked binary it is the startup layout's `emptyCStrAddr`. -/
structure RustStdIoAddrs where
  osFunctions : BitVec 64
  errorFunctions : BitVec 64
  isInterrupted : BitVec 64
  nulErr : BitVec 64
  rodataCst8 : BitVec 64
  osFunctionsGot : BitVec 64
  emptyCStr : BitVec 64

/-- The `io::Error`s the file routines return:
    - `os e`: `Error::from_raw_os_error(e)` for the positive errno `e` of a failed system call;
    - `outOfMemory`: `Error::from(TryReserveError)` = `ErrorKind::OutOfMemory` (a `Simple` error);
    - `nulInPath`: `NUL_ERR`, a path with a NUL byte. -/
inductive IoErr where
  | os (e : BitVec 64)
  | outOfMemory
  | nulInPath
  deriving Inhabited

/-- The 8-byte bit-packed representation of an `IoErr` (`core/src/io/error/repr_bitpacked.rs`):
    `Os` = `code << 32 | 0b10`, `Simple` = `kind << 32 | 0b11`, `SimpleMessage` = the address of
    the static message (tag `0b00`, the static is 4-aligned). -/
def IoErr.repr (addrs : RustStdIoAddrs) : IoErr → BitVec 64
  | .os e => (e <<< 32) ||| 2#64
  | .outOfMemory => (ioErrorKindOutOfMemory <<< 32) ||| 3#64
  | .nulInPath => addrs.nulErr

/-- The error-path cells the I/O routines touch, for thread pointer `tp`: musl's `errno`, the
    `OS_FUNCTIONS` pointer cell (both writable, contents unspecified) and the read-only
    `is_interrupted` slot of `std`'s `OsFunctions` table. The specs own it in the pre and give it
    back in every outcome, with new contents.

    `errno` and the allocator: the first conjunct is exactly `StdErrnoCell tp` (`Spec/Alloc.lean`,
    where `stdErrnoAddr` is defined), the cell every allocator contract frames explicitly because
    musl's allocator writes `ENOMEM` there. A caller that owns `StdErrCells` splits that conjunct
    off around an allocator call and rejoins it after; no `RustStdAlloc` pool owns it. -/
def StdErrCells (addrs : RustStdIoAddrs) (tp : BitVec 64) : SepProp :=
  (∃∗ e : BitVec 32, stdErrnoAddr tp ↦₃₂ e) ∗
    (∃∗ f : BitVec 64, addrs.osFunctions ↦₆₄ f) ∗
    ((addrs.errorFunctions + 16#64) ↦₆₄ᵣ addrs.isInterrupted)

/-- Harness name of the read-only 8-byte `.rodata.cst8` piece of `rustStdIoMultiLib`
    (`rustStdIoData`, bytes `rustStdIoPlacedData1` = `00 00 00 00 b6 01 00 00`, i.e. the
    little-endian word `0x000001b6_00000000` = `OpenOptions { custom_flags: 0, mode: 0o666 }`). -/
abbrev ioRodataCst8Sym : String :=
  "rust_std_io:.rodata.cst8+0x0"

/-- The read-only image cells that the compiled `fs::read` / `fs::write` code loads, each
    unconditionally on its path:
    - `addrs.rodataCst8 ↦ᵣ rustStdIoPlacedData1`: the `OpenOptions { custom_flags: 0, mode: 0o666 }`
      constant (`ldr d0, [x8]` at `std::fs::write::inner+0x02c` and `std::fs::read::inner+0x020`);
    - `addrs.osFunctionsGot ↦₆₄ᵣ addrs.osFunctions`: the GOT slot of `OS_FUNCTIONS`
      (`std::fs::write::inner+0x114`, `<File>::open_c+0x0f8`).
    The specs own them read-only in the pre and give them back unchanged in the post. Read-only
    points-to facts duplicate (`pointsToBytesRO_dup`, `pointsTo64RO_dup`), so a caller keeps its
    own copy across the call. In linked binaries:
    - the `.rodata.cst8` half holds in any binary that loads the placed library
      (`MultiPlacedLib.satisfies_dataRO_of_inElf`);
    - the GOT half is an obligation of the consumer's bridge. The loader maps the GOT read-only
      (`Arm64/Trusted/Object/Loader.lean`) but says nothing about what a slot holds, so the bridge
      must show that the linked image's slot for `OS_FUNCTIONS` holds `addrs.osFunctions`, for
      example from the generated image's data bytes and its relocation of that slot. -/
def IoImageRoCells (addrs : RustStdIoAddrs) : SepProp :=
  (addrs.rodataCst8 ↦ᵣ rustStdIoPlacedData1) ∗ (addrs.osFunctionsGot ↦₆₄ᵣ addrs.osFunctions)

variable {oom : State → State → Prop}

/-- The heap buffer of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs`
    (`len = bs.length`), allocated from `A`: the live block of `cap` bytes (alignment 1), the
    bytes and the spare capacity. With `cap = 0` there is no block and `ptr` is dangling and
    non-null. -/
def ioVecBuf (A : RustStdAlloc oom) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- `Ok(v)` of an `io::Result<Vec<u8>>` at `ret`: the 24-byte `Vec` header `{cap, ptr, len}` and
    its buffer. -/
def ioResultVecOk (A : RustStdAlloc oom) (ret cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SepProp :=
  vecHeader ret cap ptr (BitVec.ofNat 64 bs.length) ∗ ioVecBuf A cap ptr bs

/-- `Err(err)` of an `io::Result<Vec<u8>>` at `ret`: the niche value `2 ^ 64 - 1` (`usize::MAX`)
    in the capacity word (a `Vec` capacity is at most `isize::MAX`; rustc 1.98.1 stores
    `usize::MAX` for `Err`: `std::fs::read::inner` +0x09c..0x0a4, +0x10c..0x118, +0x168..0x170,
    each `mov x9, #-1; stp x9, _, [x19]` with `x19` = `ret`), the representation of `err` at `+8`,
    and 8 bytes at `+16` with unspecified contents (no `Err` path writes them). -/
def ioResultVecErr (addrs : RustStdIoAddrs) (ret : BitVec 64) (err : IoErr) : SepProp :=
  (ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((ret + 8#64) ↦₆₄ err.repr addrs) ∗
    memRegion (ret + 16#64) 8

end VerifiedLibraries.RustStd
