/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.Musl.Generated.MuslStringPlacedObj

/-!
# Stock `musl` v1.2.5 AArch64 Memory Primitives Specification

Public specification surface of stock `musl` v1.2.5 AArch64 `src/string/` memory primitives
(`memcpy`, `memset`, `memmove`, `memcmp`, `bcmp`, `memchr`, `memrchr`, `__memrchr`, `memccpy`,
`mempcpy`, and `memmem`) from the Rust `1.98.1` `aarch64-unknown-linux-musl` sysroot (`libc.a`,
SHA-256 `b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f`). Defines pure
byte-level reference models, `c_type_spec` contracts (with both mutable/shared and read-only slice
variants), and top-level placement correctness `MuslStringImageOkStmt`.
-/

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 Arm64.CType

/-! ## Program and Semantic Types -/

/-- A placed program of `VerifiedLibraries.muslStringLib` at placement `pl` with external hooks `hooks`. -/
abbrev muslStringProg (pl : Obj.Placement)
    (hooks : String → Option (State → State) := fun _ => none) : Program :=
  VerifiedLibraries.muslStringLib.program pl hooks

/-- Read-only byte slice `p ↦ᵣ bs` (e.g. `.rodata` constants; pair with `SliceLen bs` for length). -/
@[reducible] def RoSlice8 : SemType (List (BitVec 8)) :=
  { tyName := "const uint8_t[] (read-only)",
    interp := fun p bs => p ↦ᵣ bs,
    pureWf := fun _ _ => True }

/-- Length register coupled to a pair of equal-length byte-slice models `bs1`, `bs2`:
    `n.toNat = bs1.length ∧ n.toNat = bs2.length`. -/
@[reducible] def SliceLenPair (bs1 bs2 : List (BitVec 8)) : SemType (BitVec 64) :=
  { tyName := "size_t (paired slice length)",
    interp := fun _ _ => emp,
    pureWf := fun _ n => n.toNat = bs1.length ∧ n.toNat = bs2.length }

/-- Partially initialized buffer of total capacity `cap` bytes whose prefix holds `bs`
    (`bs.length ≤ cap`) and whose suffix `[p + bs.length, p + cap)` remains uninitialized `memRegion`. -/
@[reducible] def PrefixBuf (cap : Nat) : SemType (List (BitVec 8)) :=
  { tyName := "void * (prefix-initialized buffer)",
    interp := fun p bs =>
      (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (cap - bs.length),
    pureWf := fun _ bs => bs.length ≤ cap }

/-! ## Pure Byte-Level Reference Models -/

/-- Result of copying `len` bytes from offset `src` to offset `dst` within a single buffer `buf`. -/
def moveBytes (buf : List (BitVec 8)) (dst src len : Nat) : List (BitVec 8) :=
  buf.take dst ++ (buf.drop src).take len ++ buf.drop (dst + len)

/-- Exact return value of musl's `memcmp(s1, s2, n)` / `bcmp(s1, s2, n)` on two byte slices
    `bs1` and `bs2`: returns `(b1.zeroExtend 32 - b2.zeroExtend 32)` at the first differing
    byte pair `(b1, b2)`, or `0#32` if all compared bytes match. -/
def memcmpBytes : List (BitVec 8) → List (BitVec 8) → BitVec 32
  | b1 :: rest1, b2 :: rest2 =>
    if b1 = b2 then memcmpBytes rest1 rest2
    else b1.zeroExtend 32 - b2.zeroExtend 32
  | _, _ => 0#32

/-- Return value of `memchr(s, c, n)` where `s` holds `bs` (`n = bs.length`):
    `s + i` at the first index `i` where `bs[i] = c`, or `0` (`NULL`) if `c ∉ bs`. -/
def memchrRet (s : BitVec 64) (bs : List (BitVec 8)) (c : BitVec 8) : BitVec 64 :=
  match bs.idxOf? c with
  | some i => s + BitVec.ofNat 64 i
  | none => 0#64

/-- Return value of `memrchr(s, c, n)` / `__memrchr(s, c, n)` where `s` holds `bs` (`n = bs.length`):
    `s + i` at the last index `i` where `bs[i] = c`, or `0` (`NULL`) if `c ∉ bs`. -/
def memrchrRet (s : BitVec 64) (bs : List (BitVec 8)) (c : BitVec 8) : BitVec 64 :=
  match bs.reverse.idxOf? c with
  | some j => s + BitVec.ofNat 64 (bs.length - 1 - j)
  | none => 0#64

/-- Number of bytes copied by `memccpy(dst, src, c, n)` where `src` holds `bs` (`n = bs.length`):
    `k + 1` if `c` first occurs at index `k`, or `bs.length` if `c ∉ bs`. -/
def memccpyCount (bs : List (BitVec 8)) (c : BitVec 8) : Nat :=
  match bs.idxOf? c with
  | some k => k + 1
  | none => bs.length

/-- Return value of `memccpy(dst, src, c, n)` where `src` holds `bs` (`n = bs.length`):
    `dst + (k + 1)` if `c` first occurs at index `k`, or `0` (`NULL`) if `c ∉ bs`. -/
def memccpyRet (dst : BitVec 64) (bs : List (BitVec 8)) (c : BitVec 8) : BitVec 64 :=
  match bs.idxOf? c with
  | some k => dst + BitVec.ofNat 64 (k + 1)
  | none => 0#64

/-- First starting index `i ≤ hs.length - ne.length` where `(hs.drop i).take ne.length = ne`,
    or `none` if `ne` does not occur as a contiguous subslice of `hs`. -/
def memmemIdx? (hs ne : List (BitVec 8)) : Option Nat :=
  if hs.length < ne.length then none
  else (List.range (hs.length - ne.length + 1)).find? fun i =>
    decide ((hs.drop i).take ne.length = ne)

/-- Return value of `memmem(hs, k, ne, l)`: `hs + i` at the first index `i` where `ne` occurs
    in `hs`, or `0` (`NULL`) if `ne` does not occur in `hs`. When `ne = []`, returns `hs`. -/
def memmemRet (hs : BitVec 64) (bsHay bsNee : List (BitVec 8)) : BitVec 64 :=
  match memmemIdx? bsHay bsNee with
  | some i => hs + BitVec.ofNat 64 i
  | none => 0#64

/-! ## Public `c_type_spec` Contracts -/

/-- `memcpy(dst, src, n)` from a mutable/shared byte slice `src ↦ₛ bs`: copies `n = bs.length`
    bytes to disjoint uninitialized buffer `dst` and returns `dst`. -/
c_type_spec memcpySpec (dst src : ptr) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ MutSlice8 bs
  c_arg src : ShrRef ShrSlice8 bs
  c_arg n : Val (SliceLen bs)
  returns dst

/-- `memcpy(dst, src, n)` from a read-only byte slice `src ↦ᵣ bs` (e.g., `.rodata`):
    copies `n = bs.length` bytes to disjoint uninitialized buffer `dst` and returns `dst`. -/
c_type_spec memcpyROSpec (dst src : ptr) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ MutSlice8 bs
  c_arg src : ShrRef RoSlice8 bs
  c_arg n : Val (SliceLen bs)
  returns dst

/-- `memmove(dst, src, n)`: copies `n` bytes from `src = base + o` to `dst = base + d` within
    a single mutable buffer `base ↦ₛ buf` (`d + n ≤ buf.length ∧ o + n ≤ buf.length`), handling
    arbitrary overlap, and returns `dst`. -/
c_type_spec memmoveSpec (dst src : ptr) (n : u64)
    (ghost base : BitVec 64) (ghost buf : List (BitVec 8)) (ghost d o : Nat) : ptr where
  c_arg dst : ShrRef (InteriorPtr "void *") (base + BitVec.ofNat 64 d)
  c_arg src : ShrRef (InteriorPtr "const void *") (base + BitVec.ofNat 64 o)
  c_arg n : Val SizeT
  c_env (base ↦ₛ buf) ⇝ (base ↦ₛ moveBytes buf d o n.toNat)
  caveat [API_RESTRICTION]
    "destination [d, d + n) and source [o, o + n) ranges lie within buf" :
    d + n.toNat ≤ buf.length ∧ o + n.toNat ≤ buf.length
  caveat [C_ARITH_BOUND]
    "buffer [base, base + buf.length) does not wrap the 64-bit address space and fits in signed ptrdiff_t" :
    base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63
  returns dst

/-- `memset(dst, c, n)`: fills `n` bytes at `dst` with the low 8 bits of `c` and returns `dst`. -/
c_type_spec memsetSpec (dst : ptr) (c : u32) (n : u64) : ptr where
  c_arg dst : UninitSlot n.toNat ⇝ MutSlice8 (List.replicate n.toNat (c.setWidth 8))
  c_arg c : Val U32
  c_arg n : Val SizeT
  returns dst

/-- `memcmp(s1, s2, n)` on disjoint mutable/shared byte slices `s1 ↦ₛ bs1`, `s2 ↦ₛ bs2`:
    returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
c_type_spec memcmpSpec (s1 s2 : ptr) (n : u64) (ghost bs1 bs2 : List (BitVec 8)) : i32 where
  c_arg s1 : ShrRef ShrSlice8 bs1
  c_arg s2 : ShrRef ShrSlice8 bs2
  c_arg n : Val (SliceLenPair bs1 bs2)
  returns memcmpBytes bs1 bs2

/-- `memcmp(s1, s2, n)` on read-only byte slices `s1 ↦ᵣ bs1`, `s2 ↦ᵣ bs2`:
    returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
c_type_spec memcmpROSpec (s1 s2 : ptr) (n : u64) (ghost bs1 bs2 : List (BitVec 8)) : i32 where
  c_arg s1 : ShrRef RoSlice8 bs1
  c_arg s2 : ShrRef RoSlice8 bs2
  c_arg n : Val (SliceLenPair bs1 bs2)
  returns memcmpBytes bs1 bs2

/-- `bcmp(s1, s2, n)` on disjoint mutable/shared byte slices `s1 ↦ₛ bs1`, `s2 ↦ₛ bs2`:
    tail-calls `memcmp` and returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
c_type_spec bcmpSpec (s1 s2 : ptr) (n : u64) (ghost bs1 bs2 : List (BitVec 8)) : i32 where
  c_arg s1 : ShrRef ShrSlice8 bs1
  c_arg s2 : ShrRef ShrSlice8 bs2
  c_arg n : Val (SliceLenPair bs1 bs2)
  returns memcmpBytes bs1 bs2

/-- `bcmp(s1, s2, n)` on read-only byte slices `s1 ↦ᵣ bs1`, `s2 ↦ᵣ bs2`:
    tail-calls `memcmp` and returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
c_type_spec bcmpROSpec (s1 s2 : ptr) (n : u64) (ghost bs1 bs2 : List (BitVec 8)) : i32 where
  c_arg s1 : ShrRef RoSlice8 bs1
  c_arg s2 : ShrRef RoSlice8 bs2
  c_arg n : Val (SliceLenPair bs1 bs2)
  returns memcmpBytes bs1 bs2

/-- `memchr(s, c, n)` on a mutable/shared byte slice `s ↦ₛ bs`: returns a pointer to the first
    occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
c_type_spec memchrSpec (s : ptr) (c : u32) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg s : ShrRef ShrSlice8 bs
  c_arg c : Val U32
  c_arg n : Val (SliceLen bs)
  returns memchrRet s bs (c.setWidth 8)

/-- `memchr(s, c, n)` on a read-only byte slice `s ↦ᵣ bs`: returns a pointer to the first
    occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
c_type_spec memchrROSpec (s : ptr) (c : u32) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg s : ShrRef RoSlice8 bs
  c_arg c : Val U32
  c_arg n : Val (SliceLen bs)
  returns memchrRet s bs (c.setWidth 8)

/-- `memrchr(s, c, n)` / `__memrchr(s, c, n)` on a mutable/shared byte slice `s ↦ₛ bs`:
    returns a pointer to the last occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
c_type_spec memrchrSpec (s : ptr) (c : u32) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg s : ShrRef ShrSlice8 bs
  c_arg c : Val U32
  c_arg n : Val (SliceLen bs)
  returns memrchrRet s bs (c.setWidth 8)

/-- `memrchr(s, c, n)` / `__memrchr(s, c, n)` on a read-only byte slice `s ↦ᵣ bs`:
    returns a pointer to the last occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
c_type_spec memrchrROSpec (s : ptr) (c : u32) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg s : ShrRef RoSlice8 bs
  c_arg c : Val U32
  c_arg n : Val (SliceLen bs)
  returns memrchrRet s bs (c.setWidth 8)

/-- `memccpy(dst, src, c, n)` from a mutable/shared byte slice `src ↦ₛ bs`: copies bytes from
    `src` to `dst` up to and including the first occurrence of `c.setWidth 8` (or all `n` bytes
    if `c.setWidth 8 ∉ bs`), returning `dst + (k + 1)` on match or `0` (`NULL`) if not found. -/
c_type_spec memccpySpec (dst src : ptr) (c : u32) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ (PrefixBuf bs.length) (bs.take (memccpyCount bs (c.setWidth 8)))
  c_arg src : ShrRef ShrSlice8 bs
  c_arg c : Val U32
  c_arg n : Val (SliceLen bs)
  returns memccpyRet dst bs (c.setWidth 8)

/-- `memccpy(dst, src, c, n)` from a read-only byte slice `src ↦ᵣ bs`: copies bytes from
    `src` to `dst` up to and including the first occurrence of `c.setWidth 8` (or all `n` bytes
    if `c.setWidth 8 ∉ bs`), returning `dst + (k + 1)` on match or `0` (`NULL`) if not found. -/
c_type_spec memccpyROSpec (dst src : ptr) (c : u32) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ (PrefixBuf bs.length) (bs.take (memccpyCount bs (c.setWidth 8)))
  c_arg src : ShrRef RoSlice8 bs
  c_arg c : Val U32
  c_arg n : Val (SliceLen bs)
  returns memccpyRet dst bs (c.setWidth 8)

/-- `mempcpy(dst, src, n)` from a mutable/shared byte slice `src ↦ₛ bs`: copies `n = bs.length`
    bytes to disjoint uninitialized buffer `dst` and returns `dst + n`. -/
c_type_spec mempcpySpec (dst src : ptr) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ MutSlice8 bs
  c_arg src : ShrRef ShrSlice8 bs
  c_arg n : Val (SliceLen bs)
  c_stack 32
  returns dst + n

/-- `mempcpy(dst, src, n)` from a read-only byte slice `src ↦ᵣ bs`: copies `n = bs.length`
    bytes to disjoint uninitialized buffer `dst` and returns `dst + n`. -/
c_type_spec mempcpyROSpec (dst src : ptr) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ MutSlice8 bs
  c_arg src : ShrRef RoSlice8 bs
  c_arg n : Val (SliceLen bs)
  c_stack 32
  returns dst + n

/-- `memmem(hs, k, ne, l)` on disjoint mutable/shared byte slices `hs ↦ₛ bsHay`, `ne ↦ₛ bsNee`:
    returns a pointer to the first occurrence of needle `bsNee` in haystack `bsHay`, or `0` (`NULL`)
    if not found (`hs` if `bsNee = []`). -/
c_type_spec memmemSpec (hs : ptr) (k : u64) (ne : ptr) (l : u64)
    (ghost bsHay bsNee : List (BitVec 8)) : ptr where
  c_arg hs : ShrRef ShrSlice8 bsHay
  c_arg k : Val (SliceLen bsHay)
  c_arg ne : ShrRef ShrSlice8 bsNee
  c_arg l : Val (SliceLen bsNee)
  c_stack 48
  caveat [C_ARITH_BOUND]
    "non-null haystack [hs, hs + k) does not wrap the 64-bit address space" :
    0 < hs.toNat ∧ hs.toNat + bsHay.length ≤ 2 ^ 64
  caveat [PARTIAL_SPEC]
    "short needle (l <= 4) or haystack shorter than needle (k < l); needles of length > 4 enter twoway_memmem" :
    bsNee.length ≤ 4 ∨ bsHay.length < bsNee.length
  returns memmemRet hs bsHay bsNee

/-- `memmem(hs, k, ne, l)` on read-only byte slices `hs ↦ᵣ bsHay`, `ne ↦ᵣ bsNee`:
    returns a pointer to the first occurrence of needle `bsNee` in haystack `bsHay`, or `0` (`NULL`)
    if not found (`hs` if `bsNee = []`). -/
c_type_spec memmemROSpec (hs : ptr) (k : u64) (ne : ptr) (l : u64)
    (ghost bsHay bsNee : List (BitVec 8)) : ptr where
  c_arg hs : ShrRef RoSlice8 bsHay
  c_arg k : Val (SliceLen bsHay)
  c_arg ne : ShrRef RoSlice8 bsNee
  c_arg l : Val (SliceLen bsNee)
  c_stack 48
  caveat [C_ARITH_BOUND]
    "non-null haystack [hs, hs + k) does not wrap the 64-bit address space" :
    0 < hs.toNat ∧ hs.toNat + bsHay.length ≤ 2 ^ 64
  caveat [PARTIAL_SPEC]
    "short needle (l <= 4) or haystack shorter than needle (k < l); needles of length > 4 enter twoway_memmem" :
    bsNee.length ≤ 4 ∨ bsHay.length < bsNee.length
  returns memmemRet hs bsHay bsNee

/-! ## Top-Level Placement Correctness -/

/-- Top-level placement correctness statement for all 11 exported symbols in `VerifiedLibraries.muslStringLib`. -/
def MuslStringImageOkStmt : Prop :=
  ∀ (pl : Obj.Placement) (hooks : String → Option (State → State)),
    VerifiedLibraries.muslStringLib.Placeable pl →
    let prog := muslStringProg pl hooks
    prog.subroutineOk "memcpy" memcpySpec ∧
    prog.subroutineOk "memcpy" memcpyROSpec ∧
    prog.subroutineOk "memmove" memmoveSpec ∧
    prog.subroutineOk "memset" memsetSpec ∧
    prog.subroutineOk "memcmp" memcmpSpec ∧
    prog.subroutineOk "memcmp" memcmpROSpec ∧
    prog.subroutineOk "bcmp" bcmpSpec ∧
    prog.subroutineOk "bcmp" bcmpROSpec ∧
    prog.subroutineOk "memchr" memchrSpec ∧
    prog.subroutineOk "memchr" memchrROSpec ∧
    prog.subroutineOk "memrchr" memrchrSpec ∧
    prog.subroutineOk "memrchr" memrchrROSpec ∧
    prog.subroutineOk "__memrchr" memrchrSpec ∧
    prog.subroutineOk "__memrchr" memrchrROSpec ∧
    prog.subroutineOk "memccpy" memccpySpec ∧
    prog.subroutineOk "memccpy" memccpyROSpec ∧
    prog.subroutineOk "mempcpy" mempcpySpec ∧
    prog.subroutineOk "mempcpy" mempcpyROSpec ∧
    prog.subroutineOk "memmem" memmemSpec ∧
    prog.subroutineOk "memmem" memmemROSpec

end VerifiedLibraries.Musl
