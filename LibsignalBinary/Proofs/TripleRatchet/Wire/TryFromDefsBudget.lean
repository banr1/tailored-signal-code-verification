/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefs

/-!
# Budget-Threaded Definitions & Callee Contracts for `<SignalMessage>::try_from`

Re-exports `RustAlloc`-independent placed helpers from `Wire.TryFromDefs` and defines bounded
`<DecodeError>::push` and exact-capacity `bytes::merge` contracts, `[LibsignalPlacement]` hook
bundles, and callee `subroutine_ok` propositions for Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl lsRustDeallocSym)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 extHookStack withLsCodeRoLoaded lsAllocHandleErrorSym
   decodeErrorFromName decodeErrorPushName varintSlowName
   decodeErrorAtStackLen reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeName)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost BytesMergeCapOk decodeErrorHookStackX sliceCursorAfter
   decodeVarintSliceName int32MergeName skipFieldName dropDecodeErrorName bytesMergeName)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg tryFromPlacedImg logFilterAddr_tryFromPlacedImg
   logOff_tryFromPlacedImg panic_at_handle_alloc_error2_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents rustReallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (intoBoxedSliceName tryCloneFromRefName intoBoxedSliceSpecX tryCloneFromRefSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack decodeErrorFromSpecWithStack
   decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (decodeVarintSliceSpecX int32MergeSpecX skipFieldSpecX dropDecodeErrorSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeRawSpecX)

/-! ## Re-exports of placed helpers from `Wire.TryFromDefs` -/

export CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg tryFromPlacedImg logFilterAddr_tryFromPlacedImg
   logOff_tryFromPlacedImg panic_at_handle_alloc_error2_placed)

/-! ## Bounded `<DecodeError>::push` & Exact-Capacity `bytes::merge` Contracts -/

/-- Bounded `<DecodeError>::push` envelope matching `SpqrV1.Alloc.newCap32` (`max (2 * n) 4`). -/
def DecodeErrorPushBoundedEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ evs = rustAllocEvents 128 8) ∨
  (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)

/-- Stack-parameterized `<DecodeError>::push` specification guarded by `DecodeErrorPushBoundedEnv`. -/
def decodeErrorPushBoundedSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hStack : Nat) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (slot, err, n, st) s =>
    ⌜s.readReg64 .x0 = slot ∧ err ≠ 0#64 ∧ n < 2 ^ 32 ∧
      FitsEnv M lim st (DecodeErrorPushBoundedEnv n)⌝ ∗
      (slot ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
      A.pool lim st s ∗ stackAt s.sp hStack
  post := fun (slot, _err, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ∃∗ err' : BitVec 64, ⌜err' ≠ 0#64⌝ ∗
        ⌜DecodeErrorPushBoundedEnv n evs⌝ ∗
        (slot ↦₆₄ err') ∗ decodeErrorAtStackLen A.repAlloc err' (n + 1) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp hStack)

/-- Deterministic `Vec<u8>` post-capacity after `prost::encoding::bytes::merge::<Vec<u8>, _>`
succeeds with slice `v` (`v.length ≤ cap` overwrites in place; `cap < v.length` reserves
`reserveCap cap 0 v.length`). -/
def bmNextCap (cap vLen : Nat) : Nat :=
  if vLen ≤ cap then cap else reserveCap cap 0 vLen

/-- Exact-capacity output `Vec<u8>` spatial postcondition of `bytesMergeExactRawSpecX`:
records both `BytesMergeCapOk cap' rest.length` and `cap'.toNat = bmNextCap valCap.toNat v.length`. -/
abbrev bmExactPostVec (A : RustAlloc) (valPtr valCap : BitVec 64)
    (v rest : List (BitVec 8)) : SepProp :=
  ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
    ⌜BytesMergeCapOk cap' rest.length ∧ cap'.toNat = bmNextCap valCap.toNat v.length⌝ ∗
      vecU8At A valPtr cap' ptr' v

/-- Budget-threaded raw contract of `bytes::merge` at `bytesMergeStackX` exposing the
deterministic post-capacity equation `cap'.toNat = bmNextCap x.valCap.toNat v.length`
on `some (v, rest)`. -/
def bytesMergeExactRawSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := (bytesMergeRawSpecX A lim).pre
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0xe0 + (0x50 + decodeErrorHookStackX)) ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          bmExactPostVec A.repAlloc x.valPtr x.valCap v rest ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-! ## Relocatable `[LibsignalPlacement]` Hook Bundles & Callee Contracts (Block `85`) -/

structure AllocHooksWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  dealloc : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ lsRustDeallocSym)
    (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack))
  panic_alloc : H lsAllocHandleErrorSym = some Rust.panicked

structure TripleRatchetHooksWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : AllocHooksWPlaced A lim H
  decodeErrorFrom : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeErrorFromName)
    (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack M A lim (2 * extHookStack)))
  decodeErrorPush : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeErrorPushName)
    (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack)))
  decodeVarintSlow : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ varintSlowName)
    (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack)))

def IntoBoxedSliceOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ intoBoxedSliceName)
    (withLsCodeRoLoaded lsmpl (intoBoxedSliceSpecX M A lim))

def TryCloneFromRefOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ tryCloneFromRefName)
    (withLsCodeRoLoaded lsmpl (tryCloneFromRefSpecX M A lim))

def DecodeVarintSliceOkWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeVarintSliceName)
    (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim))

def Int32MergeOkWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ int32MergeName)
    (withLsCodeRoLoaded lsmpl (int32MergeSpecX A lim))

def SkipFieldOkWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ skipFieldName)
    (withLsCodeRoLoaded lsmpl (skipFieldSpecX A lim))

def DropDecodeErrorOkWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ dropDecodeErrorName)
    (withLsCodeRoLoaded lsmpl (dropDecodeErrorSpecX A lim))

def BytesMergeOkWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ bytesMergeName)
    (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim))

def DropSpeOkWPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ dropSpeName)
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
