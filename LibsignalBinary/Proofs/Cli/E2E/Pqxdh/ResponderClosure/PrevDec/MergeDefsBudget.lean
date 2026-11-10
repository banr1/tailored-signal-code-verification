/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Handshake `bytes::merge` Specifications and Codec Bridges

Total-correctness (`RustCliAllocBudget M`) contracts `bytesMerge3RawSpecGen`, `bytesMerge3RawSpec`,
and `bytesMerge3ProtoRawSpec` at `bytesMerge3Stack` (`33120` B), together with stack-lifting and
`LibsignalSpqrV1.Proto.mergeBytes` equivalence combinators.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost decodeErrorHookStackX sliceCursorAfter sliceCursorAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  BytesMergeProtoGhost bytesMerge3Stack bytesMerge6Name protoWireTypeToCodec
  protoWireTypeToCodec_toNat proto_mergeBytes_toOption stackAt_bytesMerge3_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bmPostVec bmPreBoundBudget bytesMergeEventsCore bytesMergeRawSpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget (
  MergePanicGen MergePostGen
)

/-! ## `bytesMerge3RawSpecGen` and `bytesMerge3RawSpec` (`33120` B) -/

/-- Capacity-mode-parameterized budget-threaded raw contract of
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]` at `bytesMerge3Stack`
(`reqCap = true` for `< 2 ^ 63` + `BytesMergeCapOk`, `reqCap = false` for `< 2 ^ 62` W-mode). -/
abbrev bytesMerge3RawSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (reqCap : Bool) : Spec (BytesMergeGhost × M.σ) :=
  bytesMergeRawSpecGen A lim (48 + decodeErrorHookStackX) reqCap

/-- Budget-threaded raw contract of
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]` at `bytesMerge3Stack`. -/
def bytesMerge3RawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (BytesMergeEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem bytesMerge3RawSpec_eq_gen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    bytesMerge3RawSpec A lim = bytesMerge3RawSpecGen A lim true :=
  rfl

/-! ## `MergePost3` / `MergePanic3` and `SepWPp` Stack-Lifting Lemmas -/

abbrev MergePost3Gen {M : AllocCostModel} (reqCap : Bool)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  MergePostGen (48 + decodeErrorHookStackX) reqCap A lim x st s0 R sf P_f

abbrev MergePanic3Gen {M : AllocCostModel} (reqCap : Bool)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  MergePanicGen (48 + decodeErrorHookStackX) reqCap A lim x st s0 R sf P_f

abbrev MergePost3 {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpec A lim).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanic3 {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpec A lim).onPanic (x, st) s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3 {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePost3 A lim x st s0 R) (MergePanic3 A lim x st s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMerge3RawSpec A lim) (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.to_subroutineOutcome3_cro {M : AllocCostModel} {pl : Obj.MultiPlacement}
    {prog : Program} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePost3 A lim x st s0 R) (MergePanic3 A lim x st s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded pl (bytesMerge3RawSpec A lim)) (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3Gen {M : AllocCostModel} {reqCap : Bool} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostGen decodeErrorHookStackX reqCap A lim x st s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))
      (MergePanicGen decodeErrorHookStackX reqCap A lim x st s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 33120#64) 48 ∗ P)
      (MergePost3Gen reqCap A lim x st s0 R) (MergePanic3Gen reqCap A lim x st s0 R) := by
  intro F hm hL
  have hm' : s.mem ⊨ P ∗ (memRegion (s0.sp - 33120#64) 48 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h (memRegion (s0.sp - 33120#64) 48 ∗ F) hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmr
    have hp := hpost hmr'
    dsimp only [bytesMerge3RawSpecGen, bytesMergeRawSpecGen] at hp ⊢
    change sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
        (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp bytesMerge3Stack ∗ _) ∗ R
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmr
    exact False.elim (not_satisfies_false_sepConj (hpanic hmr'))
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3 {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostGen decodeErrorHookStackX true A lim x st s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))
      (MergePanicGen decodeErrorHookStackX true A lim x st s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 33120#64) 48 ∗ P)
      (MergePost3 A lim x st s0 R) (MergePanic3 A lim x st s0 R) :=
  SepWPp.lift_merge3Gen (reqCap := true) h

/-! ## `LibsignalSpqrV1.Proto.mergeBytes` Specification and Bridge -/

/-- Callee-fixed allocator event envelope of `bytes::merge` parameterized by
`BytesMergeProtoGhost`. -/
abbrev BytesMergeProtoEnv (x : BytesMergeProtoGhost) : List AllocEvent → Prop :=
  BytesMergeEnv x.toCodec

/-- Budget-threaded raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
stated directly in terms of `LibsignalSpqrV1.Proto.mergeBytes`. -/
def bytesMerge3ProtoRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeProtoGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.wt.toU32.setWidth 8 ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (BytesMergeProtoEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeProtoEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes x.wt x.bs).toOption with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem bytesMerge3ProtoRawSpec_pre_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : BytesMergeProtoGhost) (st : M.σ) (s : State) :
    (bytesMerge3ProtoRawSpec A lim).pre (x, st) s =
      (bytesMerge3RawSpec A lim).pre (x.toCodec, st) s := by
  dsimp only [bytesMerge3ProtoRawSpec, bytesMerge3RawSpec, BytesMergeProtoGhost.toCodec,
    BytesMergeProtoEnv]
  rw [protoWireTypeToCodec_toNat x.wt]

theorem bytesMerge3ProtoRawSpec_post_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : BytesMergeProtoGhost) (st : M.σ) (s0 sf : State) :
    (bytesMerge3ProtoRawSpec A lim).post (x, st) s0 sf =
      (bytesMerge3RawSpec A lim).post (x.toCodec, st) s0 sf := by
  dsimp only [bytesMerge3ProtoRawSpec, bytesMerge3RawSpec, BytesMergeProtoGhost.toCodec,
    BytesMergeProtoEnv]
  rw [proto_mergeBytes_toOption x.wt x.bs]
  rfl

theorem subroutine_ok_bytesMerge3Proto_of_codec {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (bytesMerge3RawSpec A lim)) :
    subroutine_ok prog entry (bytesMerge3ProtoRawSpec A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  rw [bytesMerge3ProtoRawSpec_pre_eq] at hpre
  refine h.mono_outcome (x.toCodec, st) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · rw [← bytesMerge3ProtoRawSpec_post_eq] at hpost
    exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

theorem subroutine_ok_bytesMerge3Proto_of_codec_cro {M : AllocCostModel}
    {pl : Obj.MultiPlacement} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (bytesMerge3RawSpec A lim))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (bytesMerge3ProtoRawSpec A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [bytesMerge3ProtoRawSpec_pre_eq] at hpre
  refine h.mono_outcome (x.toCodec, st) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · dsimp only [withLsCodeRoLoaded] at hpost ⊢
    rw [← bytesMerge3ProtoRawSpec_post_eq] at hpost
    exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

theorem subroutine_ok_bytesMerge3Proto_of_codec_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (withLsCl lsmpl (bytesMerge3RawSpec A lim))) :
    subroutine_ok prog entry (withLsCl lsmpl (bytesMerge3ProtoRawSpec A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCl] at hpre
  rw [bytesMerge3ProtoRawSpec_pre_eq] at hpre
  refine h.mono_outcome (x.toCodec, st) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · dsimp only [withLsCl] at hpost ⊢
    rw [← bytesMerge3ProtoRawSpec_post_eq] at hpost
    exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
