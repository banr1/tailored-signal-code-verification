/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields

/-!
# Budget-Threaded Relocatable `Q`-Scope `SessionRecord::deserialize` Definitions

Defines the input-bounded allocation envelopes `MergeFieldQEnv` and `DeserPrefixQEnv` and the
budget-threaded `[LibsignalPlacement]` contracts and loop invariants (`mergeFieldQPlacedSpecW`,
`MergeFieldQPlacedOkW`, `deserializeQPlacedSpecW`, `deserializeQExactPlacedSpecW`, `DeserLoopQPlacedW`)
for `SessionStructure::merge_field` (Block `15`) and `SessionRecord::deserialize` (Block `46`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl
)
open CryptoVerification.LibsignalPublicApiRepr (sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  sliceCursorAt sliceCursorAfter
)
open CryptoVerification.E2E.Record (
  RecordGhost encodeRecord recDeserializeStack
)
open CryptoVerification.E2E.Record.Placed (
  blkPl_15 blkPl_46 lsProg_15 lsProg_46
)
open CryptoVerification.E2E.Record.DeserializeSeed (
  deserPlacedPC deserSpL deserCalleeStack deserSaved
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  DeserializeGenGhost SegStepG
)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open Proofs.libsignal.Hooks2 (mergeFieldStackX)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (
  GenFieldQ SSGQ MergeFieldQGhost prostSSGQAt
  recFieldsQ ssgqAfter deserLocalsQA deserOutRecordQA
  encodeRecord_eq_recFieldsQ
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  DeserializeGenEnv
)

/-! ## Input-bounded allocation envelopes -/

/-- Total allocation envelope of `SessionStructure::merge_field` on a `Q`-scope field `x`. -/
def MergeFieldQEnv (x : MergeFieldQGhost) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * x.fld.enc.length) (256 * (x.fld.enc.length + 16)) evs

/-- Prefix allocation envelope after `k` outer fields of `Q`-scope `SessionRecord::deserialize` on `r`. -/
def DeserPrefixQEnv (r : SessionRecord (List (BitVec 8))) (k : Nat)
    (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * (((recFieldsQ r).take k).flatMap GenFieldQ.enc).length + 32)
    (256 * ((encodeRecord r).length + 16)) evs

/-- On `DeserializeScopeP_Q Q r`, `((recFieldsQ r).flatMap GenFieldQ.enc).length ≤ (encodeRecord r).length`. -/
theorem recFieldsQ_flatMap_length_le_encodeRecord {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r) :
    ((recFieldsQ r).flatMap GenFieldQ.enc).length ≤ (encodeRecord r).length := by
  have heq := congrArg List.length (encodeRecord_eq_recFieldsQ r hr)
  rw [List.length_append, List.length_append] at heq
  omega

/-- At `k = 0`, any `BoundedRustEvs 32 0 evs` satisfies `DeserPrefixQEnv r 0 evs`. -/
theorem deserPrefixQEnv_zero (r : SessionRecord (List (BitVec 8))) {evs : List AllocEvent}
    (h : BoundedRustEvs 32 0 evs) : DeserPrefixQEnv r 0 evs := by
  unfold DeserPrefixQEnv
  simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.zero_add]
  exact BoundedRustEvs.mono (Nat.le_refl _) (Nat.zero_le _) h

/-- At `k = (recFieldsQ x.r).length` plus `BoundedRustEvs 32 r₂ evs₂`, `evs₁ ++ evs₂` satisfies
`DeserializeGenEnv x` (`= RecordDeserializeEnv (encodeRecord x.r)`). -/
theorem deserPrefixQEnv_at_length {Q : List (BitVec 8) → Prop}
    {x : DeserializeGenGhost} (hr : DeserializeScopeP_Q Q x.r)
    {evs₁ evs₂ : List AllocEvent} {r₂ : Nat}
    (h1 : DeserPrefixQEnv x.r (recFieldsQ x.r).length evs₁)
    (h2 : BoundedRustEvs 32 r₂ evs₂)
    (hr2 : r₂ ≤ 256 * ((encodeRecord x.r).length + 16)) :
    DeserializeGenEnv x (evs₁ ++ evs₂) := by
  unfold DeserPrefixQEnv at h1
  rw [List.take_length] at h1
  have hle := recFieldsQ_flatMap_length_le_encodeRecord x.r hr
  exact BoundedRustEvs.mono (by omega)
    (Nat.max_le.mpr ⟨Nat.le_refl _, hr2⟩) (BoundedRustEvs.append h1 h2)

/-! ## Relocatable `[LibsignalPlacement]` budget-threaded contracts and loop invariants -/

/-- Image-free budget-threaded contract of `SessionStructure::merge_field` (block `15`) on one
`GenFieldQ` restricted by `P`, at `mergeFieldStackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def mergeFieldQRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : GenFieldQ → Prop) : Spec (MergeFieldQGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEnv M lim st (MergeFieldQEnv x)⌝ ∗
      prostSSGQAt A.repAlloc x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp mergeFieldStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64 ∧ MergeFieldQEnv x evs⌝ ∗
        prostSSGQAt A.repAlloc x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp mergeFieldStackX

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract of `SessionStructure::merge_field`
(block `15`) on `GenFieldQ` restricted by `P`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev mergeFieldQPlacedSpecW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (P : GenFieldQ → Prop) :
    Spec (MergeFieldQGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (mergeFieldQRawSpecW M A lim P)

/-- Relocatable budget-threaded `SessionStructure::merge_field` (block `15`) contract on `lsProg_15 H`. -/
def MergeFieldQPlacedOkW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (P : GenFieldQ → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQPlacedSpecW M A lim P)

theorem mergeFieldQPlacedSpecW_pre_iff [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : GenFieldQ → Prop}
    {x : MergeFieldQGhost} {st : M.σ} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldQPlacedSpecW M A lim P).pre (x, st) s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldQPlacedSpecW M A lim (fun _ => True)).pre (x, st) s0 ∗ R) := by
  dsimp only [mergeFieldQPlacedSpecW, withLsCodeRoLoaded]
  simp only [mergeFieldQRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldQPlacedOkW_of_imp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (H : LibsignalHooks)
    {P Q : GenFieldQ → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldQPlacedOkW M A lim H Q) :
    MergeFieldQPlacedOkW M A lim H P := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQPlacedSpecW_pre_iff] at hpre
  exact hQ.mono_outcome (x, st) R s0 hpc hrun
    (mergeFieldQPlacedSpecW_pre_iff.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal fun _ hout => hout

theorem mergeFieldQPlacedOkW_or [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (H : LibsignalHooks)
    {P Q : GenFieldQ → Prop}
    (hP : MergeFieldQPlacedOkW M A lim H P)
    (hQ : MergeFieldQPlacedOkW M A lim H Q) :
    MergeFieldQPlacedOkW M A lim H (fun fl => P fl ∨ Q fl) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hal => ?_
  rw [mergeFieldQPlacedSpecW_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome (x, st) R s0 hpc hrun
      (mergeFieldQPlacedSpecW_pre_iff.mpr ⟨hp, hpre.2⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome (x, st) R s0 hpc hrun
      (mergeFieldQPlacedSpecW_pre_iff.mpr ⟨hq, hpre.2⟩) hal fun _ hout => hout

/-- Raw loop-exit postcondition of `Q`-scope `SessionRecord::deserialize` before lifting
`deserOutRecordQA` to `sessionRecordAt`. -/
def deserOutRawQBudget (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (st : M.σ) (s0 sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜sf.trace = s0.trace ∧ DeserializeGenEnv x evs⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗
      deserOutRecordQA A.repAlloc x.out x.r ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp recDeserializeStack

/-- Image-free budget-threaded contract of `SessionRecord::deserialize` (block `46`) on
`DeserializeScopeP_Q NonEmptyV1Q` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
noncomputable def deserializeQRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeserializeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScopeP_Q NonEmptyV1Q x.r ∧
      FitsEnv M lim st (DeserializeGenEnv x)⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗
      memRegion x.out 368 ∗ A.pool lim st s ∗ stackAt s.sp recDeserializeStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ DeserializeGenEnv x evs⌝ ∗
        (x.p ↦ₛ encodeRecord x.r) ∗
        (∃∗ g : RecordGhost, ⌜CanonRecord g x.r⌝ ∗ sessionRecordAt A.repAlloc x.out g x.r) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp recDeserializeStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract of `SessionRecord::deserialize`
(block `46`) on `DeserializeScopeP_Q NonEmptyV1Q`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeQPlacedSpecW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DeserializeGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (deserializeQRawSpecW M A lim)

/-- Image-free exact budget-threaded contract of `SessionRecord::deserialize` (block `46`) on
`DeserializeScopeP_Q NonEmptyV1Q` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
noncomputable def deserializeQExactRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeserializeGenGhost × M.σ) where
  pre := (deserializeQRawSpecW M A lim).pre
  post := fun (x, st) s0 sf => deserOutRawQBudget M A lim x st s0 sf

/-- Relocatable `[LibsignalPlacement]` exact budget-threaded contract of `SessionRecord::deserialize`
(block `46`) on `DeserializeScopeP_Q NonEmptyV1Q`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeQExactPlacedSpecW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DeserializeGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (deserializeQExactRawSpecW M A lim)

/-- One segment step of relocatable budget-threaded `Q`-scope deserialize on `lsProg_46 H`. -/
abbrev DeserStepQPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (x : DeserializeGenGhost) (st : M.σ) (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_46 H) (deserializeQPlacedSpecW M A lim) (x, st) R s0 s Q

/-- Raw return state of relocatable budget-threaded `Q`-scope deserialize on `lsProg_46 H`. -/
def DeserRetQPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (st : M.σ) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ deserOutRawQBudget M A lim x st s0 sf ∗ R)

/-- Loop invariant at `(blkPl_46).base + 0x254` after `k` fields of `recFieldsQ x.r` under
`[LibsignalPlacement]`, threading `FitsEnv M lim st (DeserializeGenEnv x)` and
`DeserPrefixQEnv x.r k evs`. -/
def DeserLoopQPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (st : M.σ) (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPlacedPC 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    FitsEnv M lim st (DeserializeGenEnv x) ∧
    ∃ evs : List AllocEvent,
      DeserPrefixQEnv x.r k evs ∧
      (s.mem ⊨ deserLocalsQA A.repAlloc (deserSpL s0.sp) x.p (encodeRecord x.r)
          (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) (ssgqAfter x.r k) ∗
        memRegion x.out 368 ∗ A.pool lim (M.stepEvents evs st) s ∗
        stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

end LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.DefsBudget
