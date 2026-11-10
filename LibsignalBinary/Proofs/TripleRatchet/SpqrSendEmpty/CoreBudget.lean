/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `spqr::send::<HookRng>` on an Empty State

Relocatable `RustCliAllocBudget`-threaded verification of `spqr::decode_state` (block 325) and
`spqr::send::<HookRng>` (block 124) on an empty state (`evs = []`, eliminating `allocFailedIn` from
`onPanic` while preserving `S.sendPanics`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded libsignalSessionExterns
  lsLogFilterAddr ls_hook_ok ls_subroutine_ok_of_block lsmpl
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (tapeAfter tapeAt)
open CryptoVerification.LibsignalTripleRatchet (
  SendCall SpqrModel decodeStateEmptyAt decodeStateEmptySpec
  pqChainNone pqInnerNone sessionMemcpyRegionSpec spqrSendResultAt spqrSendStack
)
open CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty (
  blkPC_124 blkPC_325 blkPl_124 blkPl_325
  bytes_of_pcs decodeEmpty_split decode_fold dst_fold memcpyPcsSpec
  pcs_dst pcs_of_bytes pcs_src result_fold ret_split stackAt_spqr tape_fold
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_with_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post :=
  SepWP.mono (sepWP_rebase_vmPreserved h) fun _ _ _ _ ⟨hvm, hp⟩ => hp hvm

private theorem sepWP_cut_here {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun _ _ _ _ h => h

local syntax "by_vm_open " tacticSeq : tactic
local elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

/-! ## `VmPreserved` `spqr::decode_state` (block 325) and `memcpyPcsBudgetSpec` -/

/-- `decodeStateEmptySpec A` strengthened with `VmPreserved s0 sf`. -/
def decodeStateEmptyBudgetSpec (A : RustAlloc) :=
  withVmPreserved (decodeStateEmptySpec A)

section DecodeStateEmptyVm
attribute [local irreducible] VmPreserved

theorem decodeStateEmpty_vm_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base H) (blkPl_325).base
      (decodeStateEmptyBudgetSpec A) := by
  simp only [decodeStateEmptyBudgetSpec, withVmPreserved, decodeStateEmptySpec,
    decodeStateEmptyAt, pqChainNone, pqInnerNone, sepConj_assoc]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, ret⟩
  dsimp only at *
  have hbs : bs = [] := by assumption
  subst hbs
  rw [CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty.vecArg_at_nil A v cap ptr,
      CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty.ret_352_split ret,
      CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty.stackAt_decodeState_split s0.sp]
  wp_pull_exists
  apply sepWP_cut_here (mid := s0.readReg64 (Reg.gpr 30#5))
  by_vm_open
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by wp_norm_lhs, fun hvm => ?_⟩
    wp_done

end DecodeStateEmptyVm

/-- `memcpyPcsSpec` strengthened with `VmPreserved s0 sf`. -/
def memcpyPcsBudgetSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) :=
  withVmPreserved memcpyPcsSpec

theorem memcpyPcsBudget_of_sessionMemcpyRegion {prog : Program} {entry : BitVec 64}
    (hmc : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok prog entry memcpyPcsBudgetSpec := by
  refine subroutine_ok_outcome_intro fun ⟨t, c, i⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [memcpyPcsBudgetSpec, withVmPreserved, memcpyPcsSpec] at hpre
  rw [← pcs_src, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc : s0.mem ⊨ (withVmPreserved sessionMemcpyRegionSpec).pre
      (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  refine hmc.mono_outcome
    (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
    R s0 hpc hrun hpre_mc hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost⟩ := hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost
    dsimp only [memcpyPcsBudgetSpec, withVmPreserved, memcpyPcsSpec]
    rw [← pcs_src, ← pcs_dst, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5)
      (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5))) hpost_mem
  · right; left
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

/-! ## Budget-threaded `spqr::send::<HookRng>` contracts (block 124) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` contract for `spqr::send::<HookRng>`
(Block `124`), parameterized by allocation envelope `E` (`allocFailedIn` dropped from `onPanic`;
genuine model panic `S.sendPanics` preserved). -/
def spqrSendPlacedSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (E : SendCall → List AllocEvent → Prop := fun _ evs => evs = []) :
    Spec (SendCall × M.σ) where
  pre := fun (x, stB) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v ∧ FitsEnv M lim stB (E x)⌝ ∗
      x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗
      tapeAt ctl x.cur x.rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim stB s ∗ stackAt s.sp spqrSendStack
  post := fun (x, stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜E x evs ∧ S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
        ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A.repAlloc ∗
      spqrSendResultAt A.repAlloc x.ret (S.send x.st.bytes x.rest) ∗
      tapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs stB) sf ∗
      stackAt s0.sp spqrSendStack
  onPanic := fun (x, _) s0 sf =>
    ⌜S.sendPanics x.st.bytes x.rest ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Empty-state specialization (`x.st.bytes = []`, `evs = []`, `0` `FitsEnv` needed). -/
def spqrSendEmptyPlacedSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel) :
    Spec (SendCall × M.σ) where
  pre := fun (x, stB) s =>
    ⌜x.st.bytes = [] ∧ s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v⌝ ∗
      x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗
      tapeAt ctl x.cur x.rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim stB s ∗ stackAt s.sp spqrSendStack
  post := fun (x, stB) s0 sf =>
    ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
      ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A.repAlloc ∗
      spqrSendResultAt A.repAlloc x.ret (S.send x.st.bytes x.rest) ∗
      tapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim stB sf ∗ stackAt s0.sp spqrSendStack
  onPanic := fun (x, _) s0 sf =>
    ⌜S.sendPanics x.st.bytes x.rest ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

set_option maxHeartbeats 1600000 in
/-- Block `124` (`spqr::send::<HookRng>`) on an empty state meets `spqrSendEmptyPlacedSpec`
under `[LibsignalPlacement]`, given `hmc` at `lsmpl.ρ "memcpy"`. -/
theorem spqrSendEmpty_placed_ok_of_memcpy [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State)) (hE : S.SendEmptyOk)
    (hmc : subroutine_ok ((blkPC_124).rebase (blkPl_124).base H)
      (lsmpl.ρ "memcpy") (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (blkPl_124).base
      (withLsCodeLoaded lsmpl (spqrSendEmptyPlacedSpec M A lim ctl S)) := by
  have hdec0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base H) (lsmpl.base 325)
      (decodeStateEmptyBudgetSpec A.repAlloc) := decodeStateEmpty_vm_placed_ok A.repAlloc H
  have hdec := ls_subroutine_ok_of_block (callerProg := (blkPC_124).rebase (blkPl_124).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hdec0)
  simp only [withLsCodeLoaded, decodeStateEmptyBudgetSpec, withVmPreserved,
    decodeStateEmptySpec, sepConj_assoc] at hdec
  have hmc' := memcpyPcsBudget_of_sessionMemcpyRegion hmc
  simp only [memcpyPcsBudgetSpec, withVmPreserved, memcpyPcsSpec, sepConj_assoc] at hmc'
  simp only [withLsCodeLoaded, spqrSendEmptyPlacedSpec, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xB s0
  rcases xB with ⟨⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩, stB⟩
  dsimp only at *
  have hbs : bs = [] := by assumption
  have hcl_0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst hbs
  apply sepWP_seq_lscl hcl_0 (mid := lsmpl.base 325)
  by_vm_open
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by wp_norm_lhs, fun hvm1 hcl_call => ?_⟩
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    wp_apply
    try (refine SepWP.focus_pure (by sep_focus) fun _hvm_dec => ?_)
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    apply SepWP.exists_elim; intro d3
    apply SepWP.exists_elim; intro d2
    apply SepWP.exists_elim; intro d1
    apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
    by_vm_open
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by wp_norm_lhs, fun hvm2 => ?_⟩
      refine SepWP.transport_budgetPool hvm2 (hnext := ?_)
      wp_apply
      try (refine SepWP.focus_pure (by sep_focus) fun _hvm_mc => ?_)
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro r6
      apply SepWP.exists_elim; intro r5
      apply SepWP.exists_elim; intro r4
      apply SepWP.exists_elim; intro r3
      apply SepWP.exists_elim; intro r2
      apply SepWP.exists_elim; intro r1
      apply SepWP.exists_elim; intro r0
      apply sepWP_cut_here (mid := s0.readReg64 (Reg.gpr 30#5))
      by_vm_open
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by wp_norm_lhs, fun hvm3 => ?_⟩
        refine SepWP.transport_budgetPool hvm3 (hnext := ?_)
        try rw [hsp_sf_1]
        try rw [hsp_sf]
        refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
        refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
          (by sep_focus) ?_
        refine SepWP.fold (result_fold A.repAlloc ret) (by sep_focus) ?_
        refine SepWP.fold (tape_fold ctl cur rest) (by sep_focus) ?_
        simp only [hE.send, hE.draws, hE.noPanic]
        wp_done

/-- Block `124` (`spqr::send::<HookRng>`) on an empty state meets `spqrSendEmptyPlacedSpec`
under `[LibsignalPlacement]`, assuming `HookSat H "memcpy" (withVmPreserved sessionMemcpyRegionSpec)`. -/
theorem spqrSendEmpty_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) {H : String → Option (State → State)} (hE : S.SendEmptyOk)
    (hmc : HookSat H "memcpy" (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (blkPl_124).base
      (withLsCodeLoaded lsmpl (spqrSendEmptyPlacedSpec M A lim ctl S)) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (by decide : "memcpy" ∈ libsignalSessionExterns)
  exact spqrSendEmpty_placed_ok_of_memcpy A lim ctl S H hE
    (ls_hook_ok (k := k) (by simp [hk, hget]) hmc)

/-- Lift `spqrSendEmpty_placed_ok` to any allocation envelope `E` admitting `[]` on empty state. -/
theorem spqrSendEmpty_placed_ok_env [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) {E : SendCall → List AllocEvent → Prop}
    {H : String → Option (State → State)} (hE : S.SendEmptyOk)
    (hEnv : ∀ x, x.st.bytes = [] → E x [])
    (hmc : HookSat H "memcpy" (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok ((blkPC_124).rebase (blkPl_124).base H) (blkPl_124).base
      (withLsCodeLoaded lsmpl
        { spqrSendPlacedSpec M A lim ctl S E with
          pre := fun (x, stB) s =>
            ⌜x.st.bytes = []⌝ ∗ (spqrSendPlacedSpec M A lim ctl S E).pre (x, stB) s }) := by
  refine subroutine_ok_outcome_intro fun ⟨x, stB⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcl, hpre1⟩ := extract_withLsCodeLoaded hpre
  dsimp only [spqrSendPlacedSpec] at hpre1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨hbs, hpre2⟩ := hpre1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre2
  obtain ⟨⟨hx0, hx1, _⟩, hmem⟩ := hpre2
  have hpre_e : s0.mem ⊨
      (withLsCodeLoaded lsmpl (spqrSendEmptyPlacedSpec M A lim ctl S)).pre (x, stB) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, spqrSendEmptyPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hbs, hx0, hx1⟩, hmem⟩
  refine (spqrSendEmpty_placed_ok A lim ctl S hE hmc).mono_outcome
    (x, stB) R s0 hpc hrun hpre_e hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [spqrSendEmptyPlacedSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hdr, htr, hnp⟩, hpost_mem⟩ := hpost
    dsimp only [withLsCodeLoaded, spqrSendPlacedSpec, AllocCostModel.stepEvents]
    have hbody : sf.mem ⊨
        (⌜E x [] ∧ S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
          ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A.repAlloc ∗
        spqrSendResultAt A.repAlloc x.ret (S.send x.st.bytes x.rest) ∗
        tapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents [] stB) sf ∗
        stackAt s0.sp spqrSendStack) ∗ R := by
      dsimp only [AllocCostModel.stepEvents]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hEnv x hbs, hdr, htr, hnp⟩, hpost_mem⟩
    exact Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro [])) hbody
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

end LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget
