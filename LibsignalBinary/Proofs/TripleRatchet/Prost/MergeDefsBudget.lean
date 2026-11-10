/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Budget-Threaded `prost::encoding::bytes::merge::<Vec<u8>>` Specifications

Deterministic allocator event sequence (`bytesMergeEventsCore`), envelope (`BytesMergeEnv`), and
`RustCliAllocBudget`-threaded specifications for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl blkPC_7 blkPl_7)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack decodeErrorAtStackLen reserveCap withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost BytesMergeCapOk sliceCursorAt sliceCursorAfter decodeErrorHookStackX)

/-! ## Deterministic allocator events and envelope -/

/-- Deterministic allocator events of `Vec::clear` + `RawVecInner::reserve(0, vLen)` on a `Vec<u8>`
with initial capacity `cap`: `[]` when `vLen ≤ cap`; otherwise `alloc(newCap, 1)` when `cap = 0` or
`realloc(cap, newCap, 1)` when `0 < cap`, where `newCap = reserveCap cap 0 vLen`. -/
def doReserveClearEvents (cap vLen : Nat) : List AllocEvent :=
  if vLen ≤ cap then
    []
  else
    let newCap := reserveCap cap 0 vLen
    if cap = 0 then rustAllocEvents newCap 1 else rustReallocEvents cap newCap 1

/-- Deterministic allocator events of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]`:
72-byte `Box<Inner>` allocation via `DecodeError::from` on `Err`; `[]` on `Ok ([], _)`; and temporary
`Bytes` buffer allocation `(v.length, 1)`, optional `Vec` reserve (`doReserveClearEvents`), and
temporary buffer deallocation `(v.length, 1)` on `Ok (v, _)` with `0 < v.length`. -/
def bytesMergeEventsCore (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) :
    List AllocEvent :=
  match mergeBytes wt bs with
  | none => rustAllocEvents 72 8
  | some (v, _) =>
    if v.length = 0 then
      []
    else
      rustAllocEvents v.length 1 ++
        doReserveClearEvents valCap.toNat v.length ++
        rustDeallocEvents v.length 1

/-- Callee-fixed allocator event envelope of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`. -/
def BytesMergeEnv (x : BytesMergeGhost) (evs : List AllocEvent) : Prop :=
  evs = bytesMergeEventsCore x.wt x.valCap x.bs

/-! ## Parameterized budget-threaded specifications -/

/-- Pure register, slice-bound, capacity, and `FitsEnv` precondition of `bytesMergeRawSpecGen`
(`reqCap = true` for `< 2 ^ 63` + `BytesMergeCapOk`, `reqCap = false` for `< 2 ^ 62`). -/
abbrev bmPreBoundBudget {M : AllocCostModel} (reqCap : Bool) (lim : BudgetLimits)
    (st : M.σ) (s : State) (x : BytesMergeGhost) : Prop :=
  match reqCap with
  | true =>
    (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (BytesMergeEnv x)
  | false =>
    (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62 ∧
      FitsEnv M lim st (BytesMergeEnv x)

/-- Output `Vec<u8>` spatial postcondition of `bytesMergeRawSpecGen` (`reqCap = true` retains
`BytesMergeCapOk cap' rest.length`; `reqCap = false` omits it). -/
abbrev bmPostVec (reqCap : Bool) (A : RustAlloc) (valPtr : BitVec 64)
    (v rest : List (BitVec 8)) : SepProp :=
  match reqCap with
  | true =>
    ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A valPtr cap' ptr' v
  | false =>
    ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A valPtr cap' ptr' v

/-- Stack- and capacity-mode-parameterized budget-threaded raw contract of
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(`0xe0 + (0x50 + errStack)`). -/
def bytesMergeRawSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) (reqCap : Bool) :
    Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜bmPreBoundBudget reqCap lim st s x⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (0xe0 + (0x50 + errStack))
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0xe0 + (0x50 + errStack)) ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          bmPostVec reqCap A.repAlloc x.valPtr v rest ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded raw contract of `bytes::merge` at `bytesMergeStack`. -/
def bytesMergeRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  bytesMergeRawSpecGen A lim decodeErrorHookStack true

/-- Budget-threaded raw contract of `bytes::merge` at `bytesMergeStackX`. -/
def bytesMergeRawSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  bytesMergeRawSpecGen A lim decodeErrorHookStackX true

/-! ## Relocatable specifications and `subroutine_ok` propositions -/

/-- Relocatable budget-threaded contract of `bytes::merge` (Block `7`) at `bytesMergeStack`. -/
def bytesMergePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A lim)

/-- Relocatable budget-threaded contract of `bytes::merge` (Block `7`) at `bytesMergeStackX`. -/
def bytesMergePlacedSpecX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A lim)

/-- `bytes::merge` (Block `7`) meets `bytesMergePlacedSpec` under `[LibsignalPlacement]`. -/
abbrev BytesMergePlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
    (blkPl_7).base (bytesMergePlacedSpec A lim)

/-- `bytes::merge` (Block `7`) meets `bytesMergePlacedSpecX` under `[LibsignalPlacement]`. -/
abbrev BytesMergePlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
    (blkPl_7).base (bytesMergePlacedSpecX A lim)

end LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
