/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget

/-!
# Budget-Threaded Callee Specifications for `SignalMessage::try_from`

`RustCliAllocBudget`-threaded specifications (`*SpecX` at `WireX.*StackX`) and relocatable
`[LibsignalPlacement]` `subroutine_ok` predicates (`*PlacedOkW`, blocks `261`, `257`, `293`, `4`,
`56`, `23`) for the callees of `SignalMessage::try_from`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesWBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded
   blkPC_23 blkPl_23 blkPC_56 blkPl_56 blkPC_261 blkPl_261 blkPC_293 blkPl_293)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (VecArg extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost)
open CryptoVerification.LibsignalTripleRatchet.WireX
  (varintSlowStackX dropSpeStackX intoBoxedSliceStackX tryCloneFromRefStackX)
open LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget
  (decodeErrorFromSpecX decodeErrorPushSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (TryCloneSliceCall intoBoxedSliceSpecWithStack tryCloneFromRefSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (decodeVarintSlowBudgetSpecWithStack)

set_option maxRecDepth 2000000

/-! ## Stack Budget Definitional Alignment with `Alloc.DefsBudget` -/

theorem intoBoxedSliceStackX_eq_gen :
    (allocHookStack + extHookStack) + 32 = intoBoxedSliceStackX := rfl

theorem tryCloneFromRefStackX_eq_gen :
    (allocHookStack + extHookStack) + 48 = tryCloneFromRefStackX := rfl

/-! ## 1–4. Budget-Threaded Callee Specifications at `WireX.*StackX` -/

/-- Budget-threaded `decode_varint_slow::<&mut &[u8]>` contract at `WireX.varintSlowStackX`. -/
def decodeVarintSlowSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) :=
  decodeVarintSlowBudgetSpecWithStack M A lim varintSlowStackX

/-- Budget-threaded `drop_glue::<SignalProtocolError>` contract at `WireX.dropSpeStackX`
(`dropSpeStack + extHookStack`). -/
def dropSpeSpecX [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSpeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speAt A.repAlloc x.fnName x.a x.e ∗ A.pool lim st s ∗ stackAt s.sp dropSpeStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 48 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropSpeStackX

/-- Budget-threaded `Vec<u8>::into_boxed_slice` contract at `WireX.intoBoxedSliceStackX`
(`intoBoxedSliceStack + extHookStack`). -/
def intoBoxedSliceSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecArg × M.σ) :=
  intoBoxedSliceSpecWithStack M A lim (allocHookStack + extHookStack)

/-- Budget-threaded `Box<[u8]>::try_clone_from_ref_in` contract at `WireX.tryCloneFromRefStackX`
(`tryCloneFromRefStack + extHookStack`). -/
def tryCloneFromRefSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryCloneSliceCall × M.σ) :=
  tryCloneFromRefSpecWithStack M A lim (allocHookStack + extHookStack)

/-! ## Relocatable `[LibsignalPlacement]` `subroutine_ok` Propositions -/

/-- `DecodeError::from` (Block `261`) meets `decodeErrorFromSpecX` under `[LibsignalPlacement]`. -/
def DecodeErrorFromPlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
    (blkPl_261).base (withLsCodeLoaded lsmpl (decodeErrorFromSpecX A lim))

/-- `DecodeError::push` (Block `257`) meets `decodeErrorPushSpecX` under `[LibsignalPlacement]`. -/
def DecodeErrorPushPlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok
    ((CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase
      (CryptoVerification.RecordCodecs.Placed.blkPl_257).base H)
    (CryptoVerification.RecordCodecs.Placed.blkPl_257).base
    (withLsCodeLoaded lsmpl (decodeErrorPushSpecX A lim))

/-- `decode_varint_slow` (Block `293`) meets `decodeVarintSlowSpecX` under `[LibsignalPlacement]`. -/
def DecodeVarintSlowPlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
    (blkPl_293).base (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim))

/-- `drop_glue::<SignalProtocolError>` (Block `4`) meets `dropSpeSpecX` under `[LibsignalPlacement]`. -/
def DropSpePlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok
    ((CryptoVerification.LibsignalTripleRatchet.Getters.blkPC_5).rebase
      (CryptoVerification.LibsignalTripleRatchet.Getters.blkPl_5).base H)
    (CryptoVerification.LibsignalTripleRatchet.Getters.blkPl_5).base
    (withLsCodeLoaded lsmpl (dropSpeSpecX A lim))

/-- `Vec<u8>::into_boxed_slice` (Block `56`) meets `intoBoxedSliceSpecX` under `[LibsignalPlacement]`. -/
def IntoBoxedSlicePlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_56).rebase (blkPl_56).base H)
    (blkPl_56).base (withLsCodeLoaded lsmpl (intoBoxedSliceSpecX A lim))

/-- `Box<[u8]>::try_clone_from_ref_in` (Block `23`) meets `tryCloneFromRefSpecX` under `[LibsignalPlacement]`. -/
def TryCloneFromRefPlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
    (blkPl_23).base (withLsCodeLoaded lsmpl (tryCloneFromRefSpecX A lim))

end LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesWBudget
