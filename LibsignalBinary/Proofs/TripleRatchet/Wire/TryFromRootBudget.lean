/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRoot
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Root Assembly for `<SignalMessage as TryFrom<&[u8]>>::try_from`

Instantiates `TryFromEnvGen` and `tryFromPlacedSpecGen` with `TryFromPostEnv` and discharges
`TryFromPostOkGen_placed` via `tryFrom_post_wp_placed`, establishing the relocatable
`[LibsignalPlacement]` panic-free budget theorems `tryFrom_placed_ok` and `tryFrom_placed_ok_of_deps`
on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.LibsignalTripleRatchet
  (TryFromGhost blkPl_85 withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp tryFromPlacedProg loopPostMem entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DecodeVarintSliceOkWPlaced Int32MergeOkWPlaced
   SkipFieldOkWPlaced BytesMergeOkWPlaced DropDecodeErrorOkWPlaced DropSpeOkWPlaced
   IntoBoxedSliceOkPlaced TryCloneFromRefOkPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (TryFromDepsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
  (TryFromEnvGen tryFromPlacedSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudget
  (TryFromPostOkGen_placed tryFrom_subroutine_ok_of_post_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
  (TryFromPostPreEnv TryFromPostEnv tryFrom_post_wp_placed)

/-! ## Concrete Top-Level Envelope & Relocatable `[LibsignalPlacement]` Spec -/

/-- Concrete top-level allocator event envelope for `<SignalMessage as TryFrom<&[u8]>>::try_from`
(instantiating `TryFromEnvGen` with `TryFromPostEnv`). -/
abbrev TryFromEnv (x : TryFromGhost) : List AllocEvent → Prop :=
  TryFromEnvGen (fun g => TryFromPostEnv g.bytes) x

/-- Concrete relocatable `[LibsignalPlacement]` panic-free budget specification of
`<SignalMessage as TryFrom<&[u8]>>::try_from` (Block `85`). -/
abbrev tryFromPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (TryFromGhost × M.σ) :=
  tryFromPlacedSpecGen (fun g => TryFromPostEnv g.bytes) A lim

/-! ## Relocatable `[LibsignalPlacement]` Root Assembly (Block `85`) -/

/-- Discharges `TryFromPostOkGen_placed` via `tryFrom_post_wp_placed`. -/
theorem tryFromPost_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H) :
    TryFromPostOkGen_placed (fun g => TryFromPostEnv g.bytes) A lim H := by
  intro st x s0 s hFit hgt9 hlt hge3 hle4 hpc hrun hst
  have hFitPre : FitsEnv M lim st (TryFromPostPreEnv x.bytes) :=
    fun evs hevs => hFit evs (Or.inl hevs)
  refine SepWPp.mono_pre ?_
    (tryFrom_post_wp_placed hS hDropErr hDropSpe hIntoBox hTryClone st
      hgt9 hlt hge3 hle4 hFitPre hpc hrun hst)
  have hw : ∀ m',
      CryptoVerification.LibsignalTripleRatchet.Prost.wireSignalMessageOf (A.atState lim st s)
        (s0.sp - 448#64 + 176#64) m' =
      CryptoVerification.LibsignalTripleRatchet.Prost.wireSignalMessageOf A.repAlloc
        (s0.sp - 448#64 + 176#64) m' := fun _ => rfl
  have hd :
      CryptoVerification.LibsignalTripleRatchet.decodeErrorAt (A.atState lim st s)
        (s.readReg64 .x24) =
      CryptoVerification.LibsignalTripleRatchet.decodeErrorAt A.repAlloc
        (s.readReg64 .x24) := rfl
  dsimp only [loopPostMem]
  cases CryptoVerification.LibsignalProtoCodec.decode
      ((x.bytes.take (x.bytes.length - 8)).drop 1) with
  | none =>
    simp only [RustCliAllocBudget.atState_pool, hw, hd]
    apply entails_of_eq
    sep_ac_rfl
  | some m' =>
    simp only [RustCliAllocBudget.atState_pool, hw]
    apply entails_of_eq
    sep_ac_rfl

/-- Full relocatable budget-threaded subroutine correctness theorem for
`<SignalMessage as TryFrom<&[u8]>>::try_from` (block `85`) on `tryFromPlacedProg H`. -/
theorem tryFrom_subroutine_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)) :=
  tryFrom_subroutine_ok_of_post_placed hS hvarint hint32 hskip hbytes
    (tryFromPost_ok_placed hS hDropErr hDropSpe hIntoBox hTryClone)

theorem tryFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)) :=
  tryFrom_subroutine_ok_placed hS hvarint hint32 hskip hbytes hDropErr hDropSpe hIntoBox hTryClone

theorem tryFrom_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (d : TryFromDepsPlaced A lim H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)) :=
  tryFrom_subroutine_ok_placed hS
    d.varintSlice d.int32Merge d.skipField d.bytesMerge
    d.dropDecodeError d.dropSpe d.intoBoxed d.tryClone

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
