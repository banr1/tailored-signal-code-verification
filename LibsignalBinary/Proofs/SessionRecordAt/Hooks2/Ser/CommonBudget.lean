/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Serialization Callee Contracts and Call Helpers

Defines `[LibsignalPlacement]` callee-contract abbreviations parameterized by `RustCliAllocBudget M`
and `BudgetLimits` for `SessionRecord::serialize` and its callees, along with OOM-aware and
total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) call combinators in `SepWPpLsCl`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl
  withLsCodeLoaded withLsCl
  blkPC_6 blkPl_6 blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.E2E.Record.Placed (
  lsProg_12 blkPl_12 lsProg_14 blkPl_14 lsProg_52 blkPl_52 lsProg_80 blkPl_80
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (doReserveSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeChainSpecX encodeRawSpecX sessionCloneSpecX
  dropSessionStructureLocal1SpecX serializeSpecX serializeCanonSpecX
)

/-! ## Budget-threaded `[LibsignalPlacement]` callee contracts -/

/-- Block `10` (`encode_varint`) at `encodeVarintStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeVarintPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
    (withLsCodeLoaded lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget.encodeVarintSpecX (M := M) A lim))

/-- Block `13` (`do_reserve_and_handle`) at `doReserveStackX` under `[LibsignalPlacement]`. -/
abbrev DoReservePlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
    (withLsCodeLoaded lsmpl (doReserveSpecX M A lim))

/-- Block `12` (`encode::<Chain, Vec<u8>>`) at `encodeChainStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeChainPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_12 H) (blkPl_12).base
    (withLsCodeLoaded lsmpl (encodeChainSpecX M A lim))

/-- Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeRawPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_14 H) (blkPl_14).base
    (withLsCodeLoaded lsmpl (encodeRawSpecX M A lim))

/-- Block `80` (`SessionStructure::clone`) at `sessionCloneStackX` under `[LibsignalPlacement]`. -/
abbrev SessionClonePlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_80 H) (blkPl_80).base
    (withLsCodeLoaded lsmpl (sessionCloneSpecX M A lim))

/-- Block `6` (`drop_glue<SessionStructure> [local#1]`) at `dropSessionStructureLocal1StackX`
under `[LibsignalPlacement]`. -/
abbrev DropSessionStructureLocal1PlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal1SpecX M A lim))

/-- Block `52` (`SessionRecord::serialize`) at `serializeStackX` under `[LibsignalPlacement]`. -/
abbrev SerializePlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_52 H) (blkPl_52).base
    (withLsCodeLoaded lsmpl (serializeSpecX M A lim))

/-- Canonical Block `52` (`SessionRecord::serialize`) at `serializeStackX` under
`[LibsignalPlacement]`. -/
abbrev SerializeCanonPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_52 H) (blkPl_52).base
    (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim))

/-! ## Stack and `SepWPpLsCl` call helpers -/

abbrev stackAt_sub_split_ser := @Proofs.libsignal.Hooks2.stackAt_sub_split_ser
abbrev SepWPpLsCl := @Proofs.libsignal.Hooks2.SepWPpLsCl
abbrev subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl :=
  @Proofs.libsignal.Hooks2.subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
abbrev sepWPpLsCl_extract_vecU8Buf_bounds :=
  @Proofs.libsignal.Hooks2.sepWPpLsCl_extract_vecU8Buf_bounds

namespace SepWPpLsCl

variable {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

abbrev of_sepWP := @Proofs.libsignal.Hooks2.SepWPpLsCl.of_sepWP
abbrev of_sepWP_ret := @Proofs.libsignal.Hooks2.SepWPpLsCl.of_sepWP_ret
abbrev done := @Proofs.libsignal.Hooks2.SepWPpLsCl.done
abbrev weaken_pre := @Proofs.libsignal.Hooks2.SepWPpLsCl.weaken_pre
abbrev pure_elim := @Proofs.libsignal.Hooks2.SepWPpLsCl.pure_elim
abbrev exists_elim := @Proofs.libsignal.Hooks2.SepWPpLsCl.exists_elim
abbrev congr_pre := @Proofs.libsignal.Hooks2.SepWPpLsCl.congr_pre
abbrev panic := @Proofs.libsignal.Hooks2.SepWPpLsCl.panic
abbrev call := @Proofs.libsignal.Hooks2.SepWPpLsCl.call
abbrev call_withLsCodeLoaded := @Proofs.libsignal.Hooks2.SepWPpLsCl.call_withLsCodeLoaded
abbrev call_withLsCl := @Proofs.libsignal.Hooks2.SepWPpLsCl.call_withLsCl
abbrev call_frame_withLsCodeLoaded :=
  @Proofs.libsignal.Hooks2.SepWPpLsCl.call_frame_withLsCodeLoaded
abbrev call_frame_withLsCl := @Proofs.libsignal.Hooks2.SepWPpLsCl.call_frame_withLsCl

/-- OOM-generalized framed `call_withLsCl` supporting specs whose `onOom` is non-`False`
(discharged at the call site via `hoom`, e.g. from `FitsEvents`). -/
theorem call_frame_withLsCl_oom {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α}
    {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      Proofs.libsignal.Hooks2.SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    Proofs.libsignal.Hooks2.SepWPpLsCl pl prog ret s P Q Qp := by
  have hcall_cl : subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
    refine subroutine_ok_outcome_intro fun y R s0 hpc0 hrun0 hpre0 hsp0 => ?_
    refine hcall.mono_outcome y R s0 hpc0 hrun0 hpre0 hsp0 fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | hpan | hex | hoom_out
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom_out))
  exact Proofs.libsignal.Hooks2.SepWPpLsCl.call_frame_withLsCodeLoaded
    hcall_cl hpc hrun hsp hlr hspec hφ hP hexit hpanic hnext hoom

/-- Total-correctness (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`) specialization
of `call_frame_withLsCodeLoaded`, discharging `hexit`/`hpanic`/`hoom` automatically when `Qp` is
of implication form `fun sf P_f => (sf.mem ⊨ P_f ∗ R₀) → _`. -/
theorem call_noPanic_withLsCodeLoaded {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α}
    {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      Proofs.libsignal.Hooks2.SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hqp_false : ∀ sf, sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F)) :
    Proofs.libsignal.Hooks2.SepWPpLsCl pl prog ret s P Q Qp :=
  Proofs.libsignal.Hooks2.SepWPpLsCl.call_frame_withLsCodeLoaded
    hcall hpc hrun hsp hlr hspec hφ hP
    (fun sf code _ _ hex => by rw [hexit_false code sf] at hex; exact not_satisfies_false_sepConj hex)
    (fun sf hpan => by rw [hpan_false sf]; exact hqp_false sf hpan)
    hnext
    (fun sf _ _ ho => by rw [hoom_false sf] at ho; exact not_satisfies_false_sepConj ho)

/-- Total-correctness (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`) specialization
of `call_frame_withLsCl_oom`. -/
theorem call_noPanic_withLsCl {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α}
    {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      Proofs.libsignal.Hooks2.SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hqp_false : ∀ sf, sf.status = .Panicked → Qp sf (⌜False⌝ ∗ F)) :
    Proofs.libsignal.Hooks2.SepWPpLsCl pl prog ret s P Q Qp :=
  call_frame_withLsCl_oom
    hcall hpc hrun hsp hlr hspec hφ hP
    (fun sf code _ _ hex => by rw [hexit_false code sf] at hex; exact not_satisfies_false_sepConj hex)
    (fun sf hpan => by rw [hpan_false sf]; exact hqp_false sf hpan)
    hnext
    (fun sf _ _ ho => by rw [hoom_false sf] at ho; exact not_satisfies_false_sepConj ho)

end SepWPpLsCl

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
