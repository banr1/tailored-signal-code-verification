/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Budget-Threaded Prost Decoding Leaf Specifications

Deterministic allocator event envelopes and `RustCliAllocBudget`-threaded specifications for
`drop_glue::<prost::error::DecodeError>`, `decode_varint_slice`, `int32::merge`, and `skip_field`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   rustAllocEvents rustDeallocEvents)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded
   blkPC_1 blkPl_1 blkPC_4 blkPl_4 blkPC_8 blkPl_8 blkPC_76 blkPl_76)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeUint32 skipField)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack decodeErrorHookStack decodeErrorAt decodeErrorAtStackLen tripleRatchetProgAt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (decodeVarintSliceName int32MergeName skipFieldName dropDecodeErrorName
   decodeErrorHookStackX
   sliceCursorAt sliceCursorAfter VarintSlicePre
   DecodeVarintSliceGhost varintSliceResultAt Int32MergeGhost SkipFieldGhost)

/-! ## `core::ptr::drop_glue::<prost::error::DecodeError>` -/

/-- Callee-fixed allocator event envelope of `drop_glue::<prost::error::DecodeError>`:
frees optional stack buffer `(c * 32, 8)` when `c > 0`, followed by the 72-byte `Box<Inner>`. -/
def DropDecodeErrorEnv (evs : List AllocEvent) : Prop :=
  evs = rustDeallocEvents 72 8 ∨
  ∃ c : Nat, 0 < c ∧ c * 32 < 2 ^ 63 ∧
    evs = rustDeallocEvents (c * 32) 8 ++ rustDeallocEvents 72 8

/-- Stack-parameterized budget-threaded contract of `drop_glue::<prost::error::DecodeError>`
(`0x20 + dStack`; `dealloc` never allocates or panics). -/
def dropDecodeErrorSpecGen [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (dStack : Nat) : Spec (BitVec 64 × M.σ) where
  pre := fun (e, st) s =>
    ⌜s.readReg64 .x0 = e ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ decodeErrorAt A.repAlloc e ∗
      A.pool lim st s ∗ stackAt s.sp (0x20 + dStack)
  post := fun (_, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜DropDecodeErrorEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x20 + dStack)

/-- Budget-threaded contract of `drop_glue::<prost::error::DecodeError>` at `dropDecodeErrorStack`. -/
def dropDecodeErrorSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) :=
  dropDecodeErrorSpecGen A lim allocHookStack

/-- Budget-threaded contract of `drop_glue::<prost::error::DecodeError>` at `dropDecodeErrorStackX`. -/
def dropDecodeErrorSpecX [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) :=
  dropDecodeErrorSpecGen A lim extHookStack

/-! ## `prost::encoding::varint::decode_varint_slice` -/

/-- Deterministic allocator events of `decode_varint_slice` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
def decodeVarintSliceEvents (bs : List (BitVec 8)) : List AllocEvent :=
  match decodeVarint bs with
  | some _ => []
  | none => rustAllocEvents 72 8

/-- Callee-fixed allocator event envelope of `decode_varint_slice`. -/
def DecodeVarintSliceEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = decodeVarintSliceEvents bs

/-- Stack-parameterized budget-threaded contract of `decode_varint_slice`
(`0x50 + errStack`: `= decodeVarintSliceSpec` at `decodeErrorHookStack`,
`= decodeVarintSliceSpecX` at `decodeErrorHookStackX`). -/
def decodeVarintSliceSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) : Spec (DecodeVarintSliceGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧ VarintSlicePre x.bs ∧
      FitsEnv M lim st (DecodeVarintSliceEnv x.bs)⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s ∗ stackAt s.sp (0x50 + errStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      varintSliceResultAt A.repAlloc x.ret x.bs (decodeVarint x.bs) ∗
      (x.ptr ↦ₛ x.bs) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarintSliceEnv x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x50 + errStack)

/-- Budget-threaded contract of `decode_varint_slice` at `decodeVarintSliceStack`. -/
def decodeVarintSliceSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSliceGhost × M.σ) :=
  decodeVarintSliceSpecGen A lim decodeErrorHookStack

/-- Budget-threaded contract of `decode_varint_slice` at `decodeVarintSliceStackX`. -/
def decodeVarintSliceSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSliceGhost × M.σ) :=
  decodeVarintSliceSpecGen A lim decodeErrorHookStackX

/-! ## `prost::encoding::int32::merge::<&mut &[u8]>` -/

/-- Deterministic allocator events of `int32::merge::<&mut &[u8]>` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
def int32MergeEvents (wt : WireType) (bs : List (BitVec 8)) : List AllocEvent :=
  match mergeUint32 wt bs with
  | some _ => []
  | none => rustAllocEvents 72 8

/-- Callee-fixed allocator event envelope of `int32::merge::<&mut &[u8]>`. -/
def Int32MergeEnv (x : Int32MergeGhost) (evs : List AllocEvent) : Prop :=
  evs = int32MergeEvents x.wt x.bs

/-- Stack-parameterized budget-threaded contract of `int32::merge::<&mut &[u8]>`
(`0x50 + (0x50 + errStack)`). -/
def int32MergeSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) : Spec (Int32MergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (Int32MergeEnv x)⌝ ∗
      memRegion x.valPtr 4 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (0x50 + (0x50 + errStack))
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜Int32MergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x50 + (0x50 + errStack)) ∗
      match mergeUint32 x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ (x.valPtr ↦₃₂ v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.valPtr 4 ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `int32::merge::<&mut &[u8]>` at `int32MergeStack`. -/
def int32MergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Int32MergeGhost × M.σ) :=
  int32MergeSpecGen A lim decodeErrorHookStack

/-- Budget-threaded contract of `int32::merge::<&mut &[u8]>` at `int32MergeStackX`. -/
def int32MergeSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Int32MergeGhost × M.σ) :=
  int32MergeSpecGen A lim decodeErrorHookStackX

/-! ## `prost::encoding::skip_field::<&mut &[u8]> [local#1]` -/

/-- Deterministic allocator events of `skip_field::<&mut &[u8]>` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
def skipFieldEventsCore (depth tag : Nat) (wt : WireType) (bs : List (BitVec 8)) :
    List AllocEvent :=
  match skipField (2 * bs.length + 2) depth tag wt bs with
  | some _ => []
  | none => rustAllocEvents 72 8

/-- Callee-fixed allocator event envelope of `skip_field::<&mut &[u8]>`. -/
def SkipFieldEnv (x : SkipFieldGhost) (evs : List AllocEvent) : Prop :=
  evs = skipFieldEventsCore x.depth x.tag x.wt x.bs

/-- Stack-parameterized budget-threaded contract of `skip_field::<&mut &[u8]> [local#1]`
(`(x.depth + 1) * 0x60 + (0x50 + errStack)`). -/
def skipFieldSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) : Spec (SkipFieldGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipFieldEnv x)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp ((x.depth + 1) * 0x60 + (0x50 + errStack))
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipFieldEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp ((x.depth + 1) * 0x60 + (0x50 + errStack)) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `skip_field::<&mut &[u8]> [local#1]` at `skipFieldStack`. -/
def skipFieldSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SkipFieldGhost × M.σ) :=
  skipFieldSpecGen A lim decodeErrorHookStack

/-- Budget-threaded contract of `skip_field::<&mut &[u8]> [local#1]` at `skipFieldStackX`. -/
def skipFieldSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SkipFieldGhost × M.σ) :=
  skipFieldSpecGen A lim decodeErrorHookStackX

/-! ## Target `subroutine_ok` propositions -/

def DropDecodeErrorOk [LibsignalPlacement] {M : AllocCostModel} (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr dropDecodeErrorName)
    (dropDecodeErrorSpec A lim)

def DecodeVarintSliceOk {M : AllocCostModel} (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr decodeVarintSliceName)
    (decodeVarintSliceSpec A lim)

def Int32MergeOk {M : AllocCostModel} (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr int32MergeName)
    (int32MergeSpec A lim)

def SkipFieldOk {M : AllocCostModel} (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr skipFieldName)
    (skipFieldSpec A lim)

abbrev DropDecodeErrorPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_4).rebase (blkPl_4).base H)
    (blkPl_4).base (withLsCodeLoaded lsmpl (dropDecodeErrorSpec A lim))

abbrev DropDecodeErrorPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_4).rebase (blkPl_4).base H)
    (blkPl_4).base (withLsCodeLoaded lsmpl (dropDecodeErrorSpecX A lim))

abbrev DecodeVarintSlicePlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
    (blkPl_76).base (withLsCodeLoaded lsmpl (decodeVarintSliceSpec A lim))

abbrev DecodeVarintSlicePlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
    (blkPl_76).base (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim))

abbrev Int32MergePlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
    (blkPl_8).base (withLsCodeLoaded lsmpl (int32MergeSpec A lim))

abbrev Int32MergePlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
    (blkPl_8).base (withLsCodeLoaded lsmpl (int32MergeSpecX A lim))

abbrev SkipFieldPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
    (blkPl_1).base (withLsCodeLoaded lsmpl (skipFieldSpec A lim))

abbrev SkipFieldPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
    (blkPl_1).base (withLsCodeLoaded lsmpl (skipFieldSpecX A lim))

end LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
