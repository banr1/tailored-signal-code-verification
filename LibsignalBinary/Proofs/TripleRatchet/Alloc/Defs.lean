/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.TripleRatchet.Hooks

set_option warningAsError false

/-!
# Specifications of Allocation Helpers and Small Serializers

Separation-logic contracts for seven allocation helpers and small serializers in
`libsignalSessionCode`:
1. `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (`0x15de4`, 45 instructions)
2. `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
   (`0x4cac`, 35 instructions)
3. `<alloc::vec::Vec<u8>>::into_boxed_slice` (`0x1afd4`, 31 instructions)
4. `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`, 28 instructions)
5. `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (`0xcf68`, 25 instructions)
6. `<libsignal_core::curve::PublicKey>::serialize` (`0x3e1e0`, 21 instructions)
7. `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes` (`0x3db4c`, 1 instruction)
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.HookTrace

/-! ## Symbol names -/

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (image offset `0x15de4`). -/
abbrev finishGrowName : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(image offset `0x4cac`). -/
abbrev doReserveName : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"

/-- `<alloc::vec::Vec<u8>>::into_boxed_slice` (image offset `0x1afd4`). -/
abbrev intoBoxedSliceName : String :=
  "<alloc::vec::Vec<u8>>::into_boxed_slice"

/-- `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (image offset `0xd0a0`). -/
abbrev tryCloneFromRefName : String :=
  "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in"

/-- `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (image offset `0xcf68`). -/
abbrev chainKeyToPbName : String :=
  "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb"

/-- `<libsignal_core::curve::PublicKey>::serialize` (image offset `0x3e1e0`). -/
abbrev publicKeySerializeName : String :=
  "<libsignal_core::curve::PublicKey>::serialize"

/-- `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes`
(image offset `0x3db4c`). -/
abbrev derivePublicKeyBytesName : String :=
  "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"

/-! ## Stack budgets (own frame + callee budget) -/

/-- `finish_grow` frame (`0x15de4`: `stp x29, x30, [sp, #-0x30]!` = 48 B) + `allocHookStack` (4096 B). -/
abbrev finishGrowStack : Nat := allocHookStack + 48

/-- `do_reserve_and_handle` frame (`0x4cac`: `sub sp, sp, #0x40` = 64 B) + `finishGrowStack` (4144 B). -/
abbrev doReserveStack : Nat := finishGrowStack + 64

/-- `into_boxed_slice` frame (`0x1afd4`: `stp x29, x30, [sp, #-0x20]!` = 32 B) + `allocHookStack` (4096 B). -/
abbrev intoBoxedSliceStack : Nat := allocHookStack + 32

/-- `try_clone_from_ref_in` frame (`0xd0a0`: `stp x29, x30, [sp, #-0x30]!` = 48 B) + `allocHookStack` (4096 B). -/
abbrev tryCloneFromRefStack : Nat := allocHookStack + 48

/-- `ChainKey::to_pb` frame (`0xcf68`: `stp x29, x30, [sp, #-0x30]!` = 48 B) + `allocHookStack` (4096 B). -/
abbrev chainKeyToPbStack : Nat := allocHookStack + 48

/-- `PublicKey::serialize` frame (`0x3e1e0`: `stp x29, x30, [sp, #-0x20]!` = 32 B) + `allocHookStack` (4096 B). -/
abbrev publicKeySerializeStack : Nat := allocHookStack + 32

/-! ## 1. `RawVecInner::finish_grow` (`0x15de4`, 45 instructions) -/

/-- Ghost of a `finish_grow` call. -/
structure FinishGrowCall where
  /-- Result pointer `x0` (`0x15df8: mov x19, x0`; 24-byte `Result<NonNull<[u8]>, TryReserveError>`). -/
  out : BitVec 64
  /-- Old capacity `x1` in elements (`0x15e28: cbz x1, 0x15e48`; `0` = `current_memory` is `None`). -/
  cap : BitVec 64
  /-- Old buffer pointer `x2` (`0x15e30: mov x0, x2`). -/
  ptr : BitVec 64
  /-- New capacity `x3` in elements (`0x15df4: umulh x8, x5, x3`; `0x15e10: mul x20, x5, x3`). -/
  new : BitVec 64
  /-- Element alignment `x4` in bytes (`0x15e18: mov x21, x4`; covers 1 and 8). -/
  align : BitVec 64
  /-- Element stride `x5` in bytes (`0x15df4`, `0x15e10`, `0x15e2c: mul x1, x5, x1`). -/
  stride : BitVec 64
  /-- Initialized prefix bytes of the existing allocation (`bs = []` when `cap = 0`). -/
  bs : List (BitVec 8)

/-- The heap buffer of a `RawVecInner` before `finish_grow`: empty if `cap = 0`, else a live block
of `cap * stride` bytes with alignment `align`, holding `bs` followed by spare capacity. -/
def FinishGrowCall.oldBuf (A : RustAlloc) (x : FinishGrowCall) : SepProp :=
  if x.cap = 0#64 then emp
  else
    A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
        (x.cap.toNat * x.stride.toNat - x.bs.length)

/-- **Contract of `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]`** (`0x15de4`).
* `pre`: registers `x0..x5` hold `(out, cap, ptr, new, align, stride)`; the new byte size
  `new * stride` is positive and `LayoutOk (new * stride) align` holds (`new * stride + align ≤ 2^63`,
  so `0x15df4: umulh` is 0 and `0x15e20: cmp x20, x11; b.hi` is not taken); `bs.length ≤ cap * stride`
  and `cap ≤ new`; `out` is 24 bytes of writable memory; `stackAt s.sp finishGrowStack`.
* `post`: writes `tag` at `out + 0` (`0x15e84`), `p'` at `out + 8` (`0x15e64` / `0x15e74`), and
  `new * stride` at `out + 16` (`0x15e80`).
  - On `Ok` (`tag = 0`, `0x15e70`): `p' ≠ 0`, `p' % align = 0`, trace unchanged, and `p'` is a live
    `align`-aligned block of `new * stride` bytes starting with `bs`.
  - On `Err` (`tag = 1`, `0x15e60`): `p' = align`, `allocFailedEvent` appended to trace, and the
    old buffer is preserved.
* `onPanic`: `False` (`finish_grow` returns `Err` on allocation failure and never panics). -/
def finishGrowSpec (A : RustAlloc) : Spec FinishGrowCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp finishGrowStack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      (if tag = 1#64 then
        ⌜p' = x.align ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (x.new.toNat * x.stride.toNat - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp finishGrowStack

/-! ## 2. `RawVecInner::reserve::do_reserve_and_handle` (`0x4cac`, 35 instructions) -/

/-- The amortized new capacity computed by `do_reserve_and_handle` for 1-byte elements
(`0x4cdc..0x4cf8`: `max(max(len + additional, 2 * cap), 8)` when `stride = 1` at `0x4ce8`). -/
abbrev reserveCap (cap len additional : Nat) : Nat :=
  max (max (len + additional) (2 * cap)) 8

/-- Ghost of a `do_reserve_and_handle` call on a `Vec<u8>`'s `RawVecInner`. -/
structure DoReserveCall where
  /-- Address of the `RawVecInner` / `Vec<u8>` header (`x0`, `0x4cc4: ldp x1, x2, [x0]`). -/
  v : BitVec 64
  /-- Current capacity (`[v + 0]`). -/
  cap : BitVec 64
  /-- Current buffer pointer (`[v + 8]`). -/
  ptr : BitVec 64
  /-- Initialized bytes (`x1 = bs.length`, `0x4cbc: adds x8, x2, x1`). -/
  bs : List (BitVec 8)
  /-- Additional bytes requested (`x2 = additional`, `0x4cbc`). -/
  additional : Nat

/-- **Contract of `do_reserve_and_handle` on a `RawVecInner` (16 bytes)** (`0x4cac`).
* `pre`: `x0 = v`, `x1 = bs.length`, `x2 = additional`, `x3 = 1` (align, `0x4cd0`), `x4 = 1`
  (stride, `0x4cc8`); `(v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr)` plus the old buffer of `cap` bytes
  starting with `bs` (`bs.length ≤ cap`, `ptr ≠ 0`); `reserveCap cap bs.length additional + 1 ≤ 2^63`
  (excludes `adds` carry at `0x4cbc` and capacity overflow in `finish_grow`). Does not touch
  `[v + 16]`.
* `post`: `[v + 0]` is updated to `newCap = reserveCap cap bs.length additional` and `[v + 8]` to the
  new non-null pointer `p'` (`0x4d14: stp x20, x8, [x19]`), with a live block of `newCap` bytes
  holding `bs` followed by `newCap - bs.length` uninitialized bytes.
* `onPanic`: panics via `alloc::raw_vec::handle_error` (`0x4d34`) only on allocator failure. -/
def doReserveRawSpec (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStack
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- **Contract of `do_reserve_and_handle` on a `Vec<u8>` (`vecU8At`)** (`0x4cac`).
Same as `doReserveRawSpec`, with `(v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length` bundled into
`vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs`. -/
def doReserveSpec (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp doReserveStack
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool ∗ stackAt s0.sp doReserveStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 3. `<alloc::vec::Vec<u8>>::into_boxed_slice` (`0x1afd4`, 31 instructions) -/

/-- The heap ownership of a `Box<[u8]>` with pointer `ptr` and bytes `bs` (the heap part of
`boxU8At A a ptr bs` without the 16-byte header at `a`). -/
def boxU8Buf (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0#64 ∧ bs.length < 2 ^ 63⌝ ∗
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

/-- `boxU8At` is the 16-byte `(ptr, len)` header at `a` plus `boxU8Buf`. -/
theorem boxU8At_eq_boxU8Buf (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs =
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ boxU8Buf A ptr bs :=
  rfl

/-- **Contract of `<alloc::vec::Vec<u8>>::into_boxed_slice`** (`0x1afd4`).
* `pre`: `x0 = v` pointing to a `Vec<u8>` (`vecU8At A v cap ptr bs`); `stackAt s.sp intoBoxedSliceStack`.
* `post`:
  - `cap = bs.length` (`0x1afe8: cmp x1, x19; b.ls 0x1b018`): returns `(ptr, bs.length)` in `(x0, x1)`
    with no allocator call;
  - `cap > bs.length` and `bs = []` (`0x1aff8: cbz x19, 0x1b02c`): calls `__rust_dealloc(ptr, cap, 1)`
    (`0x1b02c`) and returns `(1, 0)` in `(x0, x1)` (`0x1b030: mov w0, #1`);
  - `cap > bs.length` and `bs ≠ []`: calls `__rust_realloc(ptr, cap, 1, bs.length)` (`0x1b000`) and
    returns `(p', bs.length)` in `(x0, x1)`.
  In all cases `(sf.readReg64 .x0, sf.readReg64 .x1)` holds a valid `Box<[u8]>` (`boxU8Buf`) and the
  24-byte header at `v` is preserved.
* `onPanic`: panics via `alloc::raw_vec::handle_error` (`0x1b04c`) only on `realloc` failure. -/
def intoBoxedSliceSpec (A : RustAlloc) : Spec VecArg where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗ x.at A ∗ A.pool ∗ stackAt s.sp intoBoxedSliceStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧ sf.trace = s0.trace⌝ ∗
    vecHeader x.v x.cap x.ptr (BitVec.ofNat 64 x.bytes.length) ∗
    boxU8Buf A (sf.readReg64 .x0) x.bytes ∗ A.pool ∗ stackAt s0.sp intoBoxedSliceStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 4. `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`, 28 instructions) -/

/-- Ghost of a `try_clone_from_ref_in` call: slice pointer `src` (`x0`) and bytes `bs` (`x1 = bs.length`). -/
structure TryCloneSliceCall where
  src : BitVec 64
  bs : List (BitVec 8)

/-- **Contract of `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in`** (`0xd0a0`).
* `pre`: `x0 = src`, `x1 = bs.length`, `bs.length + 1 ≤ 2^63` (so `LayoutOk bs.length 1` holds when
  `bs ≠ []`), `(src ↦ₛ bs)`, `A.pool`, `stackAt s.sp tryCloneFromRefStack`.
* `post`: returns `Result<Box<[u8]>, AllocError>` in `(x0, x1)` with `x1 = bs.length` (`0xd0e4`, `0xd0fc`):
  - If `bs = []` (`0xd0b4: cbz x1, 0xd0f8`): returns `x0 = 1`, `x1 = 0` with no allocation (`boxU8Buf`).
  - If `bs ≠ []`: calls shim (`0xd0bc`), `__rust_alloc(bs.length, 1)` (`0xd0c8`), and on non-null
    `x0` copies `bs` with `memcpy` (`0xd0dc`), returning `x0 = p' ≠ 0` (`boxU8Buf`); on null `x0`
    (`0xd0cc: cbz x0, 0xd0e4`) returns `x0 = 0` with `allocFailedEvent` appended to trace.
* `onPanic`: `False` (allocation failure is returned as `x0 = 0`, not a panic). -/
def tryCloneFromRefSpec (A : RustAlloc) : Spec TryCloneSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.src ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      x.bs.length + 1 ≤ 2 ^ 63⌝ ∗
    (x.src ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bs.length⌝ ∗ (x.src ↦ₛ x.bs) ∗
    (if sf.readReg64 .x0 = 0#64 then
      ⌜x.bs ≠ [] ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ boxU8Buf A (sf.readReg64 .x0) x.bs) ∗
    A.pool ∗ stackAt s0.sp tryCloneFromRefStack

/-! ## 5. `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (`0xcf68`, 25 instructions) -/

/-- Ghost of a `ChainKey::to_pb` call: `&self` (`x0`), the `ChainKey` model value, and sret `ret` (`x8`). -/
structure ChainKeyToPbCall where
  self : BitVec 64
  ck : ChainKey
  ret : BitVec 64

/-- **Contract of `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb`** (`0xcf68`).
* `pre`: `x0 = self` holding the 36-byte `ChainKey` (`chainKeyBytes ck`: 32 key bytes @0, `u32`
  `index` @0x20, `0xcf78: ldr w21, [x0, #0x20]`), `x8 = ret` (32-byte `chain::ChainKey` sret,
  `0xcf80: mov x19, x8`), `A.pool`, `stackAt s.sp chainKeyToPbStack`.
* `post`: calls shim (`0xcf84`) and `__rust_alloc(32, 1)` (`0xcf90`), copies the 32 key bytes
  (`0xcf98: ldp q0, q1, [x20]`; `0xcfa8: stp q0, q1, [x0]`), and writes the `Vec<u8>` header
  `{cap = 32, ptr = p', len = 32}` at `ret + 0..24` (`0xcfa4`, `0xcfac`) and `ck.index` at
  `ret + 24` (`0xcfa0: str w21, [x19, #0x18]`), matching `optChainKeyAt A ⟨32#64, p'⟩ (some ck) ret`.
* `onPanic`: panics via `alloc::raw_vec::handle_error` (`0xcfc8`) only on allocator failure. -/
def chainKeyToPbSpec (A : RustAlloc) : Spec ChainKeyToPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.ret⌝ ∗
    (x.self ↦ₛ chainKeyBytes x.ck) ∗ memRegion x.ret 32 ∗ A.pool ∗
    stackAt s.sp chainKeyToPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.self ↦ₛ chainKeyBytes x.ck) ∗
    (∃∗ p' : BitVec 64, optChainKeyAt A ⟨32#64, p'⟩ (some x.ck) x.ret) ∗
    A.pool ∗ stackAt s0.sp chainKeyToPbStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 6. `<libsignal_core::curve::PublicKey>::serialize` (`0x3e1e0`, 21 instructions) -/

/-- Ghost of a `PublicKey::serialize` call: `&self` (`x0`) and the `PublicKey` model value. -/
structure PublicKeySerializeCall where
  self : BitVec 64
  pk : PublicKey

/-- **Contract of `<libsignal_core::curve::PublicKey>::serialize`** (`0x3e1e0`).
* `pre`: `x0 = self` holding the 32-byte `PublicKey` (`pk.bytes.toList`), `A.pool`,
  `stackAt s.sp publicKeySerializeStack`.
* `post`: calls shim (`0x3e1f0`) and `__rust_alloc(33, 1)` (`0x3e1fc`), writes the DJB type byte
  `0x05` at `p' + 0` (`0x3e208: mov w8, #5; 0x3e20c: strb w8, [x0]`) and the 32 key bytes at
  `p' + 1..33` (`0x3e204: ldp q0, q1, [x19]`; `0x3e214: stur q0, [x0, #1]`;
  `0x3e218: stur q1, [x0, #0x11]`), and returns `x0 = p'`, `x1 = 33` (`0x3e210: mov w1, #0x21`)
  owning `pk.serialize = 0x05#8 :: pk.bytes.toList` (`boxU8Buf`).
* `onPanic`: panics via `alloc::raw_vec::handle_error` (`0x3e230`) only on allocator failure. -/
def publicKeySerializeSpec (A : RustAlloc) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗
    stackAt s.sp publicKeySerializeStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
    A.pool ∗ stackAt s0.sp publicKeySerializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 7. `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes` (`0x3db4c`, 1 instruction) -/

/-- Ghost of a `derive_public_key_bytes` call: `&secret` (`x0`, 32 bytes), the secret bytes `sec`,
and the 32-byte output buffer `out` (`x8`). -/
structure DerivePublicKeyBytesCall where
  secret : BitVec 64
  sec : List.Vector (BitVec 8) 32
  out : BitVec 64

/-- **Contract of `PrivateKey::derive_public_key_bytes`** (`0x3db4c`).
* Single instruction `0x3db4c: b 0x51d04` tail-calling `pubFromSecretName`
  (`<x25519_dalek::x25519::PublicKey as From<&StaticSecret>>::from`), which is hooked by
  `pubFromSecretHook C.pubKey`: reads the 32 secret bytes at `x0` and writes `(pubKey sec).toList`
  to the 32-byte buffer at `x8`, leaving `sp` and `trace` unchanged and never panicking. -/
def derivePublicKeyBytesSpec (pubKey : PubKeyFn) : Spec DerivePublicKeyBytesCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.secret ∧ s.readReg64 .x8 = x.out⌝ ∗
    (x.secret ↦ₛ x.sec.toList) ∗ memRegion x.out 32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (pubKey x.sec).toList)

/-- Stack-parameterized contract of `PrivateKey::derive_public_key_bytes` (`0x3db4c`) /
`pubFromSecretName` (`0x48148`), threading `stackAt s.sp hookStack` (e.g. `externStack = 16384`). -/
def derivePublicKeyBytesStackSpec (pubKey : PubKeyFn) (hookStack : Nat := 0) :
    Spec DerivePublicKeyBytesCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.secret ∧ s.readReg64 .x8 = x.out⌝ ∗
    (x.secret ↦ₛ x.sec.toList) ∗ memRegion x.out 32 ∗ stackAt s.sp hookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (pubKey x.sec).toList) ∗
    stackAt s0.sp hookStack

/-! ## Local hook lemmas and shared stack/memory helpers -/

/-- No-op shim spec that records trace preservation. -/
def noAllocShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem noAllocShim_hookOk : HookOk hookNoop noAllocShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [noAllocShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

/-- Trace-preserving `memcpy` spec without a stack frame. -/
def framelessMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

theorem framelessMemcpy_hookOk : HookOk hookMemcpy framelessMemcpySpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

/-- `pubFromSecretHook pubKey` meets `derivePublicKeyBytesSpec pubKey`. -/
theorem pubFromSecret_hookOk (pubKey : PubKeyFn) :
    HookOk (pubFromSecretHook pubKey) (derivePublicKeyBytesSpec pubKey) := by
  refine retHook_ok fun x R s0 _ hpre _ => ?_
  simp only [derivePublicKeyBytesSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes x.secret x.sec.toList).read hmem
  have hsec_len : x.sec.toList.length = 32 := List.Vector.toList_length x.sec
  rw [hsec_len] at hread
  have hread_vec : readVec32 s0.mem x.secret = x.sec := Subtype.ext hread
  have hout_len32 : (pubKey x.sec).toList.length = 32 := List.Vector.toList_length (pubKey x.sec)
  have hdst_front : s0.mem ⊨ memRegion x.out (pubKey x.sec).toList.length ∗
      ((x.secret ↦ₛ x.sec.toList) ∗ R) := by
    rw [hout_len32]
    rwa [← sepConj_assoc, sepConj_comm (x.secret ↦ₛ x.sec.toList), sepConj_assoc] at hmem
  have hout_len : (pubKey x.sec).toList.length ≤ 2 ^ 64 := by
    rw [hout_len32]; decide
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only [pubFromSecretHook]
    rw [hx0, hx8, hread_vec]
    exact keepsFrozen_writeBytes_of_memRegion (pubKey x.sec).toList hout_len hdst_front
  · dsimp only [pubFromSecretHook]
    simp only [derivePublicKeyBytesSpec, retHook,
      State.trace_setPC, State.trace_setMem, hx0, hx8, hread_vec,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    have hw := satisfies_writeBytes (pubKey x.sec).toList hout_len hdst_front
    rwa [← sepConj_assoc, sepConj_comm (x.out ↦ₛ (pubKey x.sec).toList), sepConj_assoc] at hw

/-- `allocHooks` lifts through `Rust.withPanics (trTrapExterns C abs)`. -/
theorem allocHooks_tripleRatchetExterns_trap (C : Crypto)
    (A : RustAlloc) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    AllocHooks A (Rust.withPanics (trTrapExterns C abs)) := by
  have h8 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_alloc" =
      abs "__rustc::__rust_alloc" := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact Option.some.inj (congrArg (·[4]?) (tripleRatchetExterns_abs C 0#64 abs))
  have h9 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_dealloc" =
      abs "__rustc::__rust_dealloc" := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact Option.some.inj (congrArg (·[5]?) (tripleRatchetExterns_abs C 0#64 abs))
  have h10 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_realloc" =
      abs "__rustc::__rust_realloc" := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact Option.some.inj (congrArg (·[6]?) (tripleRatchetExterns_abs C 0#64 abs))
  exact ⟨by simpa [HookSat, h8] using hA.alloc,
    by simpa [HookSat, h9] using hA.dealloc,
    by simpa [HookSat, h10] using hA.realloc⟩

/-- `allocHooks` lifts through `Rust.withPanics (tripleRatchetExterns C ctl abs)`. -/
theorem allocHooks_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    AllocHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs)) := by
  have habs := tripleRatchetExterns_abs C ctl abs
  have h8 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_alloc" =
      abs "__rustc::__rust_alloc" := Option.some.inj (congrArg (·[4]?) habs)
  have h9 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_dealloc" =
      abs "__rustc::__rust_dealloc" := Option.some.inj (congrArg (·[5]?) habs)
  have h10 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_realloc" =
      abs "__rustc::__rust_realloc" := Option.some.inj (congrArg (·[6]?) habs)
  exact ⟨by simpa [HookSat, h8] using hA.alloc,
    by simpa [HookSat, h9] using hA.dealloc,
    by simpa [HookSat, h10] using hA.realloc⟩

theorem panic_at_handle_error_norm_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by simp only [arm64_norm]) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext name k hk

theorem panic_at_handle_error_norm_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by simp only [arm64_norm]) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_error_trap b C abs name k hk

/-- The `alloc::raw_vec::handle_error` stub panics on `tripleRatchetProgAt`. -/
theorem panic_at_handle_error_norm {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by simp only [arm64_norm]) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_error b C ctl abs name k hk

theorem shim_ok_at2_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) noAllocShimSpec :=
  hA.shim_ok_at name k hk

theorem noAllocShim_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) noAllocShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, noAllocShim_hookOk⟩

/-- No-alloc shim at call distance `k` from `name` on `tripleRatchetProgAt`. -/
theorem noAllocShim_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) noAllocShimSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (noAllocShim_ok_at_trap (b := b) (C := C) (abs := abs) hk)

theorem memcpy_ok_at2_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) framelessMemcpySpec :=
  hA.session_memcpy_region_ok_at name k hk

theorem framelessMemcpy_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) framelessMemcpySpec :=
  hook_ok_at (hname := "memcpy") rfl hk
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

/-- `memcpy` at call distance `k` from `name` on `tripleRatchetProgAt`. -/
theorem framelessMemcpy_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) framelessMemcpySpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (framelessMemcpy_ok_at_trap (b := b) (C := C) (abs := abs) hk)

theorem alloc_ok_at_norm_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hA.alloc_ok_at name k hk

theorem alloc_ok_at_norm_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  alloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) hk

/-- `__rust_alloc` at call distance `k` from `name` on `tripleRatchetProgAt`. -/
theorem alloc_ok_at_norm {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (alloc_ok_at_norm_trap (b := b) (C := C) hA hk)

theorem dealloc_ok_at_norm_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hA.dealloc_ok_at name k hk

theorem dealloc_ok_at_norm_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) hk

/-- `__rust_dealloc` at call distance `k` from `name` on `tripleRatchetProgAt`. -/
theorem dealloc_ok_at_norm {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (dealloc_ok_at_norm_trap (b := b) (C := C) hA hk)

theorem realloc_ok_at_norm_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  hA.realloc_ok_at name k hk

theorem realloc_ok_at_norm_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  realloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) hk

/-- `__rust_realloc` at call distance `k` from `name` on `tripleRatchetProgAt`. -/
theorem realloc_ok_at_norm {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (realloc_ok_at_norm_trap (b := b) (C := C) hA hk)

theorem pubFromSecret_ok_at_of_contract {α : Type} {b : BitVec 64}
    {H : String → Option (State → State)} {spec : Spec α}
    (hpub : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr pubFromSecretName) spec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pubFromSecretName := by simp only [arm64_norm]) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel :
      (libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k =
        (libsignalSessionCode.rebase b H).fnAddr pubFromSecretName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]
  rwa [hrel]

theorem pubFromSecret_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pubFromSecretName := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (derivePublicKeyBytesSpec C.pubKey) :=
  hook_ok_at (hname := pubFromSecretName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by dsimp [pubFromSecretName]; simp [Rust.isPanicSymbol])
    ⟨pubFromSecretHook C.pubKey, rfl, pubFromSecret_hookOk C.pubKey⟩

/-- `pubFromSecretName` at call distance `k` from `name` on `tripleRatchetProgAt`. -/
theorem pubFromSecret_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pubFromSecretName := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (derivePublicKeyBytesSpec C.pubKey) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (pubFromSecret_ok_at_trap (b := b) (C := C) (abs := abs) hk)

/-- Frame `stackAt s.sp hookStack` onto any `derivePublicKeyBytesSpec pubKey` subroutine contract. -/
theorem derivePublicKeyBytesStack_of_spec {P : Program} {addr : BitVec 64}
    {pubKey : PubKeyFn} (hookStack : Nat)
    (h : subroutine_ok P addr (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok P addr (derivePublicKeyBytesStackSpec pubKey hookStack) := by
  refine subroutine_ok_refine_frame h fun x R s0 hpre =>
    ⟨x, stackAt s0.sp hookStack, ?_, fun sf hpost => ?_⟩
  · simp only [derivePublicKeyBytesStackSpec, derivePublicKeyBytesSpec, sepConj_assoc] at hpre ⊢
    exact hpre
  · simp only [derivePublicKeyBytesStackSpec, derivePublicKeyBytesSpec, sepConj_assoc] at hpost ⊢
    exact hpost

/-! ## Shared memory/stack helpers -/

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]

theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem SepWP.instantiate_post_exists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (∃∗ a, Q sf a) ∗ R) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro w)) (h1 hm), h2⟩

/-! ## Refinement-compatible (`AllocContractsX` / `extHookStack`) stack budgets, specs, and helpers -/

/-- `finish_grow` frame (48 B) + `extHookStack` (16384 B). -/
abbrev finishGrowStackX : Nat := extHookStack + 48

/-- `do_reserve_and_handle` frame (64 B) + `finishGrowStackX` (16432 B). -/
abbrev doReserveStackX : Nat := finishGrowStackX + 64

/-- `into_boxed_slice` frame (32 B) + `extHookStack` (16384 B). -/
abbrev intoBoxedSliceStackX : Nat := extHookStack + 32

/-- `try_clone_from_ref_in` frame (48 B) + `extHookStack` (16384 B). -/
abbrev tryCloneFromRefStackX : Nat := extHookStack + 48

/-- `ChainKey::to_pb` frame (48 B) + `extHookStack` (16384 B). -/
abbrev chainKeyToPbStackX : Nat := extHookStack + 48

/-- `PublicKey::serialize` frame (32 B) + `extHookStack` (16384 B). -/
abbrev publicKeySerializeStackX : Nat := extHookStack + 32

/-- `finishGrowSpec A` at `finishGrowStackX` (`= extHookStack + 48`). -/
def finishGrowSpecX (A : RustAlloc) : Spec FinishGrowCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp finishGrowStackX
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      (if tag = 1#64 then
        ⌜p' = x.align ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (x.new.toNat * x.stride.toNat - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp finishGrowStackX

/-- `doReserveRawSpec A` at `doReserveStackX` (`= finishGrowStackX + 64`). -/
def doReserveRawSpecX (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStackX
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `doReserveSpec A` at `doReserveStackX` (`= finishGrowStackX + 64`). -/
def doReserveSpecX (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp doReserveStackX
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool ∗ stackAt s0.sp doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `intoBoxedSliceSpec A` at `intoBoxedSliceStackX` (`= extHookStack + 32`). -/
def intoBoxedSliceSpecX (A : RustAlloc) : Spec VecArg where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗ x.at A ∗ A.pool ∗ stackAt s.sp intoBoxedSliceStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧ sf.trace = s0.trace⌝ ∗
    vecHeader x.v x.cap x.ptr (BitVec.ofNat 64 x.bytes.length) ∗
    boxU8Buf A (sf.readReg64 .x0) x.bytes ∗ A.pool ∗ stackAt s0.sp intoBoxedSliceStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `tryCloneFromRefSpec A` at `tryCloneFromRefStackX` (`= extHookStack + 48`). -/
def tryCloneFromRefSpecX (A : RustAlloc) : Spec TryCloneSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.src ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      x.bs.length + 1 ≤ 2 ^ 63⌝ ∗
    (x.src ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bs.length⌝ ∗ (x.src ↦ₛ x.bs) ∗
    (if sf.readReg64 .x0 = 0#64 then
      ⌜x.bs ≠ [] ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ boxU8Buf A (sf.readReg64 .x0) x.bs) ∗
    A.pool ∗ stackAt s0.sp tryCloneFromRefStackX

/-- `chainKeyToPbSpec A` at `chainKeyToPbStackX` (`= extHookStack + 48`). -/
def chainKeyToPbSpecX (A : RustAlloc) : Spec ChainKeyToPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.ret⌝ ∗
    (x.self ↦ₛ chainKeyBytes x.ck) ∗ memRegion x.ret 32 ∗ A.pool ∗
    stackAt s.sp chainKeyToPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.self ↦ₛ chainKeyBytes x.ck) ∗
    (∃∗ p' : BitVec 64, optChainKeyAt A ⟨32#64, p'⟩ (some x.ck) x.ret) ∗
    A.pool ∗ stackAt s0.sp chainKeyToPbStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `publicKeySerializeSpec A` at `publicKeySerializeStackX` (`= extHookStack + 32`). -/
def publicKeySerializeSpecX (A : RustAlloc) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗
    stackAt s.sp publicKeySerializeStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
    A.pool ∗ stackAt s0.sp publicKeySerializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack-equipped no-op shim spec at `extHookStack`. -/
def session2ShimSpecX : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack

/-- Stack-equipped `memcpy` spec at `extHookStack`. -/
def session2MemcpySpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp extHookStack

theorem shim_ok_at2_ext_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2ShimSpecX.inImage img) := by
  have h := hA.shim_ok_at name k extHookStack (by decide) (by decide) hk
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [Spec.inImage, withStack, sessionShimSpec, session2ShimSpecX] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

theorem memcpy_ok_at2_ext_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2MemcpySpecX.inImage img) := by
  have h := hA.session_memcpy_region_ok_at name k extHookStack (by decide) (by decide) hk
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem alloc_ok_at_norm_ext_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hA.alloc_ok_at name k hk

theorem dealloc_ok_at_norm_ext_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hA.dealloc_ok_at name k hk

theorem realloc_ok_at_norm_ext_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustReallocExternSpecWithStack A extHookStack).inImage img) :=
  hA.realloc_ok_at name k hk

/-- Image call-site invariant (`img.FrozenLoaded s ∧ s.symtab = img.symtab`) preserved by `Steps`. -/
abbrev ImgCallInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

theorem ImgCallInv.of_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : ImgCallInv img s) (hs : Steps prog s s') : ImgCallInv img s' :=
  ⟨h.1.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq.trans h.2⟩

theorem SepWP.seq_inImage {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · rcases (hnext (hinv.of_steps hsteps)).elim hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hf⟩⟩

theorem SepWPp.of_sepWP_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

end CryptoVerification.LibsignalTripleRatchet

