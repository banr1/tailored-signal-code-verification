/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.Placed.Bridge
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `bytes::Bytes` Representation and Function Specifications

Defines the 32-byte `bytes::Bytes` memory layout and separation-logic contracts for
`<Bytes as From<Vec<u8>>>::from` (`0x423cc`), `promotable_even_drop` (`0x41098`),
`promotable_odd_drop` (`0x40fac`), `static_drop` (`0x40950`), `static_clone`, and unified `.rodata`
vtable `drop` dispatch (`[vtable + 0x20]`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

noncomputable section

/-! ## 1. Symbol Names, Vtable Addresses, and Kernel-Checked Guards -/

/-- `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from` at `.text` offset `0x423cc` (`271308`). -/
abbrev bytesFromVecName : String :=
  "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from"

/-- `bytes::bytes::promotable_even_drop` at `.text` offset `0x41098` (`266392`). -/
abbrev promotableEvenDropName : String :=
  "bytes::bytes::promotable_even_drop"

/-- `bytes::bytes::promotable_odd_drop` at `.text` offset `0x40fac` (`266156`). -/
abbrev promotableOddDropName : String :=
  "bytes::bytes::promotable_odd_drop"

/-- `bytes::bytes::static_drop` at `.text` offset `0x40950` (`264528`). -/
abbrev bytesStaticDropName : String :=
  "bytes::bytes::static_drop"

/-- `bytes::bytes::PROMOTABLE_EVEN_VTABLE` at `.rodata` offset `0x50820` (`329760`, 40 bytes). -/
abbrev promotableEvenVtableName : String :=
  "bytes::bytes::PROMOTABLE_EVEN_VTABLE"

/-- `bytes::bytes::PROMOTABLE_ODD_VTABLE` at `.rodata` offset `0x507f8` (`329720`, 40 bytes). -/
abbrev promotableOddVtableName : String :=
  "bytes::bytes::PROMOTABLE_ODD_VTABLE"

/-- Image offset of `STATIC_VTABLE` (anonymous `.rodata..Lanon.e98b55b8c1d80e32ead2e0c78305bd8c.42`
    in `bytes.o`, 40 bytes at `0x503c8 = 328648`; slot `+0x20` relocates to `0x40950` = `static_drop`). -/
abbrev staticVtableOff : Nat := num% (ls_reloc% (ls_off% "bytes::bytes::static_clone"))

/-- Address of `STATIC_VTABLE` at image base `b` (anonymous section, pinned by `staticVtable_in_roData`
    and `staticVtable_drop_reloc` below). -/
def staticVtableAddr (b : BitVec 64) : BitVec 64 :=
  b + BitVec.ofNat 64 staticVtableOff

/-- Address of `bytes::bytes::PROMOTABLE_ODD_VTABLE` at image base `b`, looked up by symbol name. -/
def promotableOddVtableAddr (b : BitVec 64) : BitVec 64 :=
  (libsignalSessionCode.rebase b).fnAddr promotableOddVtableName

/-- Address of `bytes::bytes::PROMOTABLE_EVEN_VTABLE` at image base `b`, looked up by symbol name. -/
def promotableEvenVtableAddr (b : BitVec 64) : BitVec 64 :=
  (libsignalSessionCode.rebase b).fnAddr promotableEvenVtableName

@[simp, arm64_norm] theorem bytesFromVec_fnOff :
    libsignalSessionCode.fnOff bytesFromVecName = num% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from") :=
  (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")

@[simp, arm64_norm] theorem promotableEvenDrop_fnOff :
    libsignalSessionCode.fnOff promotableEvenDropName = num% (ls_off% "bytes::bytes::promotable_even_drop") :=
  (ls_lemma% fnOff "bytes::bytes::promotable_even_drop")

@[simp, arm64_norm] theorem promotableOddDrop_fnOff :
    libsignalSessionCode.fnOff promotableOddDropName = num% (ls_off% "bytes::bytes::promotable_odd_drop") :=
  (ls_lemma% fnOff "bytes::bytes::promotable_odd_drop")

@[simp, arm64_norm] theorem bytesStaticDrop_fnOff :
    libsignalSessionCode.fnOff bytesStaticDropName = num% (ls_off% "bytes::bytes::static_drop") :=
  (ls_lemma% fnOff "bytes::bytes::static_drop")

@[simp, arm64_norm] theorem promotableOddVtable_fnOff :
    libsignalSessionCode.fnOff promotableOddVtableName = num% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
  exact (ls_lemma% fnOff "bytes::bytes::PROMOTABLE_ODD_VTABLE")

@[simp, arm64_norm] theorem promotableEvenVtable_fnOff :
    libsignalSessionCode.fnOff promotableEvenVtableName = num% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") := by
  exact (ls_lemma% fnOff "bytes::bytes::PROMOTABLE_EVEN_VTABLE")

theorem promotableOddVtableAddr_eq_off (b : BitVec 64) :
    promotableOddVtableAddr b = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
  unfold promotableOddVtableAddr
  rw [Program.fnAddr_rebase, promotableOddVtable_fnOff]

theorem promotableEvenVtableAddr_eq_off (b : BitVec 64) :
    promotableEvenVtableAddr b = b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") := by
  unfold promotableEvenVtableAddr
  rw [Program.fnAddr_rebase, promotableEvenVtable_fnOff]

theorem promotableOddVtableAddr_eq_entryOf {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    promotableOddVtableAddr img.base = entryOf img promotableOddVtableName := by
  unfold promotableOddVtableAddr entryOf
  rw [libsignalSessionCode_ofImage himg]

theorem promotableEvenVtableAddr_eq_entryOf {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    promotableEvenVtableAddr img.base = entryOf img promotableEvenVtableName := by
  unfold promotableEvenVtableAddr entryOf
  rw [libsignalSessionCode_ofImage himg]

set_option maxRecDepth 2000000 in
/-- Kernel-checked guard: `STATIC_VTABLE` (`0x503c8`, 40 bytes) is a `.rodata` section of
    `libsignalSessionImage`. -/
theorem staticVtable_in_roData :
    (staticVtableOff, 40) ∈ libsignalSessionImage.roData :=
  List.mem_of_elem_eq_true (by rfl_kernel)

set_option maxRecDepth 2000000 in
/-- Kernel-checked guard: the `drop` slot (`+0x20`) of `STATIC_VTABLE` (`0x503c8`) has an 8-byte
    relocation in `libsignalSessionImage.relocs` targeting `bytesStaticDropName` (`0x40950`). -/
theorem staticVtable_drop_reloc :
    ({ off := staticVtableOff - libsignalSessionImage.dataOff + 0x20
       width := 8
       target := libsignalSessionCode.fnOff bytesStaticDropName } : Obj.DataReloc) ∈
      libsignalSessionImage.relocs :=
  bytesStaticDrop_fnOff.symm ▸ List.mem_of_elem_eq_true (by rfl_kernel)

/-! ## 2. Stack Budgets -/

/-- Stack frame of `<Bytes as From<Vec<u8>>>::from` (`0x423cc`):
    `stp x29, x30, [sp, #-0x30]!` allocates 48 bytes; leaf on the `cap = len` path. -/
abbrev bytesFromVecStack : Nat := 48

/-- Stack budget of `bytes::bytes::promotable_even_drop` (`0x41098`):
    48-byte frame (`stp x29, x30, [sp, #-0x30]!`), popped at `+0x84` before tail-calling
    `__rust_dealloc` (`allocHookStack`). -/
abbrev promotableEvenDropStack : Nat := allocHookStack + 48

/-- Stack budget of `bytes::bytes::promotable_odd_drop` (`0x40fac`):
    48-byte frame (`stp x29, x30, [sp, #-0x30]!`), popped at `+0x80` before tail-calling
    `__rust_dealloc` (`allocHookStack`). -/
abbrev promotableOddDropStack : Nat := allocHookStack + 48

/-- Stack budget of `bytes::bytes::static_drop` (`0x40950`):
    single `ret` instruction, 0 bytes. -/
abbrev bytesStaticDropStack : Nat := 0

/-- Stack budget of the unified `bytesVtableDropSpec`: `allocHookStack + 48`. -/
abbrev bytesVtableDropStack : Nat := allocHookStack + 48

/-! ## 3. `bytes::Bytes` Layout and Representation Predicates

In `bytes 1.x` on 64-bit targets, `Bytes` is 32 bytes (`repr(C)`):
- `+0x00`: `vtable : &'static Vtable` (`0x42418`, `0x42484`, `0x424a8`: `str x8, [x19]`)
- `+0x08`: `ptr : *const u8` (`0x4240c`, `0x42470`, `0x424a0`: `str/stp` to `[x19, #8]`)
- `+0x10`: `len : usize` (`0x4240c`, `0x42474`, `0x424a0`: `stp` to `[x19, #16]`)
- `+0x18`: `data : AtomicPtr<()>` (`0x42410`, `0x42474`, `0x424a4`: `str/stp` to `[x19, #24]`)

When `<Bytes as From<Vec<u8>>>::from` (`0x423cc`) is called on a `Vec<u8>` with `cap = len`
(`0x423ec: subs xzr, x21, x22; 0x423f0: b.ne +0x38` not taken):
- **Case `len = 0`** (`0x423f4: cbz x21, +0x7c` → `0x42470..0x42494`):
  writes `vtable = staticVtableAddr b`, `ptr = 1`, `len = 0`, `data = 0`.
- **Case `len > 0` and `ptr &&& 1 = 0`** (`0x423fc: tbnz w9, #0, +0x9c` not taken → `0x42400..0x42424`):
  writes `vtable = promotableEvenVtableAddr b`, `ptr = ptr`, `len = len`, `data = ptr ||| 1`
  (`KIND_VEC = 0x1` tag in bit 0).
- **Case `len > 0` and `ptr &&& 1 ≠ 0`** (`0x423fc: tbnz w9, #0, +0x9c` taken → `0x42498..0x424b8`):
  writes `vtable = promotableOddVtableAddr b`, `ptr = ptr`, `len = len`, `data = ptr`
  (bit 0 of `ptr` is already `1`).
-/

/-- The `vtable` pointer stored at `Bytes + 0x00` by `Bytes::from(Vec<u8>)` when `cap = len`. -/
def bytesVtable (b ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then staticVtableAddr b
  else if ptr &&& 1#64 = 0#64 then promotableEvenVtableAddr b
  else promotableOddVtableAddr b

theorem bytesVtable_eq_off (b ptr : BitVec 64) (len : Nat) :
    bytesVtable b ptr len =
      if len = 0 then b + bv% (ls_reloc% (ls_off% "bytes::bytes::static_clone"))
      else if ptr &&& 1#64 = 0#64 then b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE")
      else b + bv% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") := by
  unfold bytesVtable staticVtableAddr staticVtableOff
  rw [promotableEvenVtableAddr_eq_off, promotableOddVtableAddr_eq_off]

/-- The `ptr` field stored at `Bytes + 0x08` by `Bytes::from(Vec<u8>)` when `cap = len`. -/
def bytesPtr (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then 1#64 else ptr

/-- The `data` field stored at `Bytes + 0x18` by `Bytes::from(Vec<u8>)` when `cap = len`. -/
def bytesData (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then 0#64
  else if ptr &&& 1#64 = 0#64 then ptr ||| 1#64
  else ptr

/-- The target `drop` function address stored at `[bytesVtable b ptr len + 0x20#64]` in `.rodata`,
    defined via `fnAddr` of the three drop symbol names:
    - `len = 0`: `fnAddr bytesStaticDropName`
    - `len > 0` and `ptr &&& 1#64 = 0#64`: `fnAddr promotableEvenDropName`
    - `len > 0` and `ptr &&& 1#64 ≠ 0#64`: `fnAddr promotableOddDropName` -/
def bytesDropFnAddr (b ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then (libsignalSessionCode.rebase b).fnAddr bytesStaticDropName
  else if ptr &&& 1#64 = 0#64 then (libsignalSessionCode.rebase b).fnAddr promotableEvenDropName
  else (libsignalSessionCode.rebase b).fnAddr promotableOddDropName

theorem bytesDropFnAddr_eq_off (b ptr : BitVec 64) (len : Nat) :
    bytesDropFnAddr b ptr len =
      if len = 0 then b + bv% (ls_off% "bytes::bytes::static_drop")
      else if ptr &&& 1#64 = 0#64 then b + bv% (ls_off% "bytes::bytes::promotable_even_drop")
      else b + bv% (ls_off% "bytes::bytes::promotable_odd_drop") := by
  unfold bytesDropFnAddr
  simp only [Program.fnAddr_rebase, bytesStaticDrop_fnOff, promotableEvenDrop_fnOff,
    promotableOddDrop_fnOff]

/-- Boxed byte-slice buffer predicate (`ptr ↦ₛ bs` with live heap ownership when non-empty,
matching `boxU8Buf` and `vecU8At` when `cap.toNat = bs.length`). -/
def bytesBoxU8Buf (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

/-- The 32-byte `Bytes` header in memory at `p`: `{vtable @ +0, ptr @ +8, len @ +16, data @ +24}`. -/
def bytesHeader (p vtable ptr len data : BitVec 64) : SepProp :=
  (p ↦₆₄ vtable) ∗ ((p + 8#64) ↦₆₄ ptr) ∗
    ((p + 16#64) ↦₆₄ len) ∗ ((p + 24#64) ↦₆₄ data)

/-- Full ownership of a `Bytes` at `p` constructed from a `Vec<u8>` with `cap.toNat = bs.length` and
    buffer pointer `ptr` at image base `b`: the 32-byte `Bytes` header at `p` together with the
    backing `bytesBoxU8Buf` heap ownership (`A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)` when `bs ≠ []`). -/
def bytesAt (A : RustAlloc) (b p ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  bytesHeader p (bytesVtable b ptr bs.length) (bytesPtr ptr bs.length)
    (BitVec.ofNat 64 bs.length) (bytesData ptr bs.length) ∗
  bytesBoxU8Buf A ptr bs

/-! ## 4. Function Specifications -/

/-- Ghost state for `<Bytes as From<Vec<u8>>>::from`:
    `(v, out, cap, ptr, bs)` where `v` is the input `&Vec<u8>` header address (`x0`),
    `out` is the 32-byte `Bytes` sret address (`x8`), `cap` is the capacity word (`cap.toNat = bs.length`),
    `ptr` is the `Vec`'s buffer pointer, and `bs` is the byte list. -/
abbrev BytesFromVecGhost := BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

/-- Specification of `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from`
    (`0x423cc`) when `cap.toNat = bs.length`:
    - `x0 = v`: pointer to the consumed 24-byte `Vec<u8>` header `{cap, ptr, len}` with `cap.toNat = bs.length`.
    - `x8 = out`: pointer to the 32-byte sret slot for `Bytes`.
    Consumes the `Vec<u8>` ownership at `v` (leaving the 24-byte `vecHeader` in place at `v`) and
    initializes `bytesAt A b out ptr bs` at `out`. -/
def bytesFromVecSpec (A : RustAlloc) (b : BitVec 64) : Spec BytesFromVecGhost where
  pre := fun (v, out, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x8 = out ∧ cap.toNat = bs.length⌝ ∗
    vecU8At A v cap ptr bs ∗
    memRegion out 32 ∗
    stackAt s.sp bytesFromVecStack
  post := fun (v, out, cap, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    bytesAt A b out ptr bs ∗
    stackAt s0.sp bytesFromVecStack

/-- Ghost state for `promotable_even_drop` and `promotable_odd_drop`:
    `(ptr, bs, off)` where `ptr` is the backing buffer base pointer, `bs` is the buffer byte list
    (`cap = bs.length`), and `off ≤ bs.length` is the current cursor offset within the buffer. -/
abbrev BytesDropGhost := BitVec 64 × List (BitVec 8) × Nat

/-- Specification of `bytes::bytes::promotable_even_drop` (`0x41098`) on an unpromoted even-pointer
    `Bytes` buffer (`(ptr &&& 1#64) = 0#64`, `data = ptr ||| 1#64`, `bs ≠ []`):
    - `x0 = ptr ||| 1#64` (`data` value with `KIND_VEC = 1` tag in bit 0)
    - `x1 = ptr + BitVec.ofNat 64 off` (current slice cursor within `[ptr, ptr + bs.length]`)
    - `x2 = BitVec.ofNat 64 (bs.length - off)` (remaining slice length, for any `off ≤ bs.length`)
    Reconstructs `buf_ptr = data &&& ~1 = ptr` and `cap = (x1 - ptr) + x2 = bs.length`, pops its
    48B frame, and tail-calls `__rust_dealloc(ptr, bs.length, 1)` (`0x47f30`), freeing the heap allocation. -/
def promotableEvenDropSpec (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableEvenDropStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableEvenDropStack

/-- Specification of `bytes::bytes::promotable_odd_drop` (`0x40fac`) on an unpromoted odd-pointer
    `Bytes` buffer (`(ptr &&& 1#64) ≠ 0#64`, `data = ptr`, `bs ≠ []`):
    - `x0 = ptr` (`data` value, which already has bit 0 set)
    - `x1 = ptr + BitVec.ofNat 64 off` (current slice cursor within `[ptr, ptr + bs.length]`)
    - `x2 = BitVec.ofNat 64 (bs.length - off)` (remaining slice length, for any `off ≤ bs.length`)
    Reconstructs `cap = (x1 - ptr) + x2 = bs.length`, pops its 48B frame, and tail-calls
    `__rust_dealloc(ptr, bs.length, 1)` (`0x47f30`), freeing the heap allocation. -/
def promotableOddDropSpec (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableOddDropStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableOddDropStack

/-- Specification of `bytes::bytes::static_drop` (`0x40950`):
    single `ret` instruction (`0xd65f03c0`), no-op. -/
def bytesStaticDropSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-- Unified specification for dropping a `Bytes` via its vtable `drop` slot
    (`entry_pc = bytesDropFnAddr b ptr bs.length`, loaded from `[bytesVtable b ptr bs.length + 0x20#64]`):
    Whether `bs = []` (`STATIC_VTABLE` → `static_drop`), `bs ≠ []` with even `ptr`
    (`PROMOTABLE_EVEN_VTABLE` → `promotable_even_drop`), or `bs ≠ []` with odd `ptr`
    (`PROMOTABLE_ODD_VTABLE` → `promotable_odd_drop`), calling `bytesDropFnAddr b ptr bs.length` with:
    - `x0 = bytesData ptr bs.length`
    - `x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off`
    - `x2 = BitVec.ofNat 64 (bs.length - off)` (for any `off ≤ bs.length`, e.g. `off = bs.length`
      in `prost::encoding::bytes::merge` after `copy_to_slice` or `off = 0` for direct drop)
    consumes `bytesBoxU8Buf A ptr bs` and returns to `X30`. -/
def bytesVtableDropSpec (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStack

/-! ## 5. Subroutine Contract Targets on `tripleRatchetProgAt` -/

/-- `<Bytes as From<Vec<u8>>>::from` meets `bytesFromVecSpec` on `tripleRatchetProgAt b C ctl abs`. -/
def BytesFromVecOk (img : Obj.Image) (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr bytesFromVecName)
    ((bytesFromVecSpec A b).inImage img)

/-- `bytes::bytes::promotable_even_drop` meets `promotableEvenDropSpec` on `tripleRatchetProgAt b C ctl abs`. -/
def PromotableEvenDropOk (img : Obj.Image) (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr promotableEvenDropName)
    ((promotableEvenDropSpec A).inImage img)

/-- `bytes::bytes::promotable_odd_drop` meets `promotableOddDropSpec` on `tripleRatchetProgAt b C ctl abs`. -/
def PromotableOddDropOk (img : Obj.Image) (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr promotableOddDropName)
    ((promotableOddDropSpec A).inImage img)

/-- `bytes::bytes::static_drop` meets `bytesStaticDropSpec` on `tripleRatchetProgAt b C ctl abs`. -/
def BytesStaticDropOk (img : Obj.Image) (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr bytesStaticDropName)
    (bytesStaticDropSpec.inImage img)

/-- Unified vtable `drop` dispatch (`entry_pc = bytesDropFnAddr b ptr bs.length`) meets
    `bytesVtableDropSpec` on `tripleRatchetProgAt b C ctl abs`. -/
def BytesVtableDropOk (img : Obj.Image) (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State))
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) : Prop :=
  TripleRatchetHooks C A S abs →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (bytesDropFnAddr b ptr bs.length)
    ((bytesVtableDropSpec A ptr bs off).inImage img)

def BytesFromVecOkExt (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr bytesFromVecName)
    ((bytesFromVecSpec A b).inImage img)

def PromotableEvenDropOkExt (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  AllocContracts b A ext →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName)
    ((promotableEvenDropSpec A).inImage img)

def PromotableOddDropOkExt (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  AllocContracts b A ext →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName)
    ((promotableOddDropSpec A).inImage img)

def BytesStaticDropOkExt (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr bytesStaticDropName)
    (bytesStaticDropSpec.inImage img)

def BytesVtableDropOkExt (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) : Prop :=
  AllocContracts b A ext →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    (bytesDropFnAddr b ptr bs.length)
    ((bytesVtableDropSpec A ptr bs off).inImage img)

/-! ## 5b. Refinement-Compatible (`AllocContractsX` / `extHookStack`) Stack Budgets, Specs, and Targets -/

/-- Stack budget of `bytes::bytes::promotable_even_drop` under `AllocContractsX`: `extHookStack + 48`. -/
abbrev promotableEvenDropStackX : Nat := extHookStack + 48

/-- Stack budget of `bytes::bytes::promotable_odd_drop` under `AllocContractsX`: `extHookStack + 48`. -/
abbrev promotableOddDropStackX : Nat := extHookStack + 48

/-- Stack budget of the unified `bytesVtableDropSpecX` under `AllocContractsX`: `extHookStack + 48`. -/
abbrev bytesVtableDropStackX : Nat := extHookStack + 48

/-- `promotableEvenDropSpec A` at `promotableEvenDropStackX` (`= extHookStack + 48`). -/
def promotableEvenDropSpecX (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableEvenDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableEvenDropStackX

/-- `promotableOddDropSpec A` at `promotableOddDropStackX` (`= extHookStack + 48`). -/
def promotableOddDropSpecX (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableOddDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableOddDropStackX

/-- `bytesVtableDropSpec A ptr bs off` at `bytesVtableDropStackX` (`= extHookStack + 48`). -/
def bytesVtableDropSpecX (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStackX

def PromotableEvenDropOkExtX (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  AllocContractsX img A ext →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName)
    ((promotableEvenDropSpecX A).inImage img)

def PromotableOddDropOkExtX (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  AllocContractsX img A ext →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName)
    ((promotableOddDropSpecX A).inImage img)

def BytesVtableDropOkExtX (img : Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) : Prop :=
  AllocContractsX img A ext →
  Obj.Loads libsignalSessionImage img →
  b = img.base →
  subroutine_ok (tripleRatchetProgAtExt b ext)
    (bytesDropFnAddr b ptr bs.length)
    ((bytesVtableDropSpecX A ptr bs off).inImage img)

/-! ## 6. Exported Rodata Vtable Dispatch Lemma for `prost::encoding::bytes::merge`

The `drop` function pointer slot `[vtable + 0x20]` of each of the three vtables
(`STATIC_VTABLE` at `0x503c8`, `PROMOTABLE_ODD_VTABLE` at `0x507f8`, `PROMOTABLE_EVEN_VTABLE` at `0x50820`)
is an 8-byte relocated pointer in `.rodata` (`libsignalSessionImage.relocs` at data offsets
`0x7220`, `0x7320`, `0x7348`). Under `Obj.Loads libsignalSessionImage img` and `img.FrozenLoaded s`,
reading 8 bytes at `bytesVtable img.base ptr len + 0x20#64` is permitted (`canRead = true` / `↦₆₄ᵣ`)
and yields `bytesDropFnAddr img.base ptr len`. -/

/-- Exported `.rodata` vtable dispatch statement: for a loaded image `img` and state `s` satisfying
`img.FrozenLoaded s`, the 8-byte word at `bytesVtable img.base ptr len + 0x20#64` is mapped
read-only (`canRead = true`), equals `bytesDropFnAddr img.base ptr len`, and can be adjoined as a
read-only points-to `↦₆₄ᵣ` to any separation-logic assertion `s.mem ⊨ P`. -/
def BytesVtableSlotLoadedStmt : Prop :=
  ∀ {img : Obj.Image} {s : State} (ptr : BitVec 64) (len : Nat),
    Obj.Loads libsignalSessionImage img →
    img.FrozenLoaded s →
    s.mem.canRead (bytesVtable img.base ptr len + 0x20#64) 8 = true ∧
    s.mem.read64 (bytesVtable img.base ptr len + 0x20#64) =
      bytesDropFnAddr img.base ptr len ∧
    ∀ {P : SepProp}, (s.mem ⊨ P) →
      s.mem ⊨ ((bytesVtable img.base ptr len + 0x20#64) ↦₆₄ᵣ bytesDropFnAddr img.base ptr len) ∗ P

/-! ## 7. Relocatable `[LibsignalPlacement]` Vtable Addresses, Representation, and Specs -/

/-- Symbol name of `STATIC_VTABLE` in `libsignalSessionData` (`bytes:.rodata..Lanon.3`). -/
abbrev staticVtableSym : String := "bytes:.rodata..Lanon.3"

/-- Symbol name of `bytes::bytes::static_clone` (Block `226`). -/
abbrev bytesStaticCloneName : String := "bytes::bytes::static_clone"

/-- Relocatable address of `STATIC_VTABLE` under `[LibsignalPlacement]`. -/
abbrev staticVtablePlacedAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ staticVtableSym

/-- Relocatable address of `bytes::bytes::PROMOTABLE_ODD_VTABLE` under `[LibsignalPlacement]`. -/
abbrev promotableOddVtablePlacedAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ promotableOddVtableName

/-- Relocatable address of `bytes::bytes::PROMOTABLE_EVEN_VTABLE` under `[LibsignalPlacement]`. -/
abbrev promotableEvenVtablePlacedAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ promotableEvenVtableName

/-- The `vtable` pointer stored at `Bytes + 0x00` by `Bytes::from(Vec<u8>)` under `[LibsignalPlacement]`. -/
def bytesPlacedVtable [LibsignalPlacement] (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then staticVtablePlacedAddr
  else if ptr &&& 1#64 = 0#64 then promotableEvenVtablePlacedAddr
  else promotableOddVtablePlacedAddr

/-- The target `drop` function address stored at `[bytesPlacedVtable ptr len + 0x20#64]` in `.rodata`
    under `[LibsignalPlacement]`:
    - `len = 0`: `lsmpl.base 224` (`bytes::bytes::static_drop`)
    - `len > 0` and `ptr &&& 1#64 = 0#64`: `lsmpl.base 237` (`bytes::bytes::promotable_even_drop`)
    - `len > 0` and `ptr &&& 1#64 ≠ 0#64`: `lsmpl.base 236` (`bytes::bytes::promotable_odd_drop`) -/
def bytesPlacedDropFnAddr [LibsignalPlacement] (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then lsmpl.base 224
  else if ptr &&& 1#64 = 0#64 then lsmpl.base 237
  else lsmpl.base 236

/-- Full ownership of a `Bytes` at `p` constructed from a `Vec<u8>` with `cap.toNat = bs.length` and
    buffer pointer `ptr` under `[LibsignalPlacement]`. -/
def bytesPlacedAt [LibsignalPlacement] (A : RustAlloc) (p ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  bytesHeader p (bytesPlacedVtable ptr bs.length) (bytesPtr ptr bs.length)
    (BitVec.ofNat 64 bs.length) (bytesData ptr bs.length) ∗
  bytesBoxU8Buf A ptr bs

/-- Relocatable specification of `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from`
    (Block `250`) when `cap.toNat = bs.length`. -/
def bytesFromVecPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec BytesFromVecGhost where
  pre := fun (v, out, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x8 = out ∧ cap.toNat = bs.length⌝ ∗
    vecU8At A v cap ptr bs ∗
    memRegion out 32 ∗
    stackAt s.sp bytesFromVecStack
  post := fun (v, out, cap, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    bytesPlacedAt A out ptr bs ∗
    stackAt s0.sp bytesFromVecStack

/-- Relocatable specification of `bytes::bytes::static_clone` (Block `226`):
    writes `{vtable = staticVtablePlacedAddr, ptr = x1, len = x2, data = 0}` to `sret` (`x8`). -/
def bytesStaticClonePlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (out, ptr, len) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x1 = ptr ∧ s.readReg64 .x2 = len⌝ ∗
    memRegion out 32
  post := fun (out, ptr, len) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bytesHeader out staticVtablePlacedAddr ptr len 0#64

end

end CryptoVerification.LibsignalTripleRatchet
