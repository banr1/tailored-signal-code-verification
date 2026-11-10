/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply

/-!
# `VmPreserved` Relocatable Proofs for `ServiceId::parse_from_service_id_string`

Proves `[LibsignalPlacement]` `VmPreserved`-strengthened contracts (`parseSidCodeBudgetSpec` and
`parseSidCodeStackBudgetSpec`) for `ServiceId::parse_from_service_id_string`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkLib_eq_206 blkPC_206 blkPl_206
  blkPC_252 blkPl_252 ls_subroutine_ok_of_block lsmpl sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (
  parseSidCodeSpec parseSidCodeStackSpec parseSidResultAt parseSidSpec
  uuidTryParseCodeSpec uuidTryParseSpec uuidTryParseStack uuidTryParseStackSpec
)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet.ParseServiceId (
  exists_cons4_of_le le_of_not_ult length_eq_36_of_eq_36 length_eq_36_of_eq_40
  length_ne_36_of_ne_36 length_ne_36_of_ne_40 memRegion_17_none_split memRegion_out1_16_split
  memRegion_sp64_none_split memRegion_sp64_some_split parseSidResultAt_some_eq
  pointsToBytes_cons4 serviceIdParse_cons4_aci serviceIdParse_cons4_pni serviceIdParse_of_lt_4
  stackAt_parseSid_eq_frame stackAt_parseSidFrame_split toNat_lt_of_ult
  uuidResultAt_sp64_none uuidResultAt_sp64_some
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (vmPreserved_right_congr)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  parseSidCodeBudgetSpec parseSidCodeStackBudgetSpec
  uuidTryParseBudgetSpec uuidTryParseCodeBudgetSpec uuidTryParseStackBudgetSpec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

private theorem sepWP_trans_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {target : BitVec 64}
    {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hvm0 : VmPreserved s0 s)
    (hwp : SepWP (P.rebase b Hk) target s Pre (fun sf P_f => VmPreserved s sf ∧ post sf P_f)) :
    SepWP (P.rebase b Hk) target s Pre (fun sf P_f => VmPreserved s0 sf ∧ post sf P_f) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hp⟩ => ⟨hvm0.trans hvm, hp⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem vmPreserved_setPC_setMem (s s' : State) (pc : BitVec 64) (m : Memory) :
    VmPreserved s ((s'.setPC pc).setMem m) ↔ VmPreserved s (s'.setMem m) :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl,
    fun _ _ _ => by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem vmPreserved_setPState_setMem (s s' : State) (ps : PState) (m : Memory) :
    VmPreserved s ((s'.setPState ps).setMem m) ↔ VmPreserved s (s'.setMem m) :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl,
    fun _ _ _ => by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem vmPreserved_writeReg64_setMem (s s' : State) (r : Reg) (v : BitVec 64) (m : Memory) :
    VmPreserved s ((s'.writeReg64 r v).setMem m) ↔ VmPreserved s (s'.setMem m) :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; cases r <;> rfl, fun _ => by cases s'; cases r <;> rfl,
     fun _ _ _ => by cases s'; cases r <;> rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem vmPreserved_writeReg32_setMem (s s' : State) (r : Reg) (v : BitVec 32) (m : Memory) :
    VmPreserved s ((s'.writeReg32 r v).setMem m) ↔ VmPreserved s (s'.setMem m) :=
  vmPreserved_writeReg64_setMem s s' r _ m

theorem uuidTryParseStackBudget_of_spec {P : Program} {addr : BitVec 64}
    (hookStack : Nat)
    (h : subroutine_ok P addr (uuidTryParseBudgetSpec uuidTryParse)) :
    subroutine_ok P addr (uuidTryParseStackBudgetSpec hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (uuidTryParseBudgetSpec uuidTryParse).pre x s0 ∗ (stackAt s0.sp hookStack ∗ R) := by
    simp only [uuidTryParseStackBudgetSpec, uuidTryParseBudgetSpec, withVmPreserved,
      uuidTryParseStackSpec, uuidTryParseSpec, sepConj_assoc] at hpre ⊢
    exact hpre
  refine h.mono_outcome x (stackAt s0.sp hookStack ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [uuidTryParseStackBudgetSpec, uuidTryParseBudgetSpec, withVmPreserved,
      uuidTryParseStackSpec, uuidTryParseSpec, sepConj_assoc] at hpost ⊢
    exact hpost
  · simp only [uuidTryParseBudgetSpec, withVmPreserved, uuidTryParseSpec, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · simp only [uuidTryParseBudgetSpec, withVmPreserved, uuidTryParseSpec, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · simp only [uuidTryParseBudgetSpec, withVmPreserved, uuidTryParseSpec, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`withLsCodeLoaded lsmpl (uuidTryParseStackBudgetSpec hookStack)` on Block `252`. -/
theorem parseSid_placed_ok_of_contract_stack [LibsignalPlacement]
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseStackBudgetSpec hookStack))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec hookStack)) := by
  have huuid := ls_subroutine_ok_of_block (callerProg := (blkPC_206).rebase (blkPl_206).base H) huuid_entry
  change subroutine_ok _ (lsmpl.base 252) _ at huuid
  change subroutine_ok _ _ (withVmPreserved (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack)))
  apply subroutine_ok_withVmPreserved_intro
  intro x R s0 hpc hrun hpre hsp_align
  obtain ⟨p, bs, out⟩ := x
  unfold withLsCodeLoaded at huuid hpre ⊢
  simp only [uuidTryParseStackBudgetSpec, withVmPreserved,
    parseSidCodeStackSpec, parseSidSpec, uuidTryParseStackSpec, uuidTryParseSpec] at huuid hpre ⊢
  clear huuid_entry
  wp_pull_exists
  refine SepWP.pure_elim fun ⟨hx0, hlen_eq, hx8⟩ => ?_
  rw [show (p ↦ₛ bs) ∗ memRegion out 17 ∗ stackAt (s0.sp - 80#64) hookStack ∗
      stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.parseSidFrameStack ∗
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ =
    ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗ ((p ↦ₛ bs) ∗ memRegion out 17 ∗
      stackAt (s0.sp - 80#64) hookStack ∗
      stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.parseSidFrameStack) by sep_ac_rfl]
  refine SepWP.pure_elim fun hcl0 => ?_
  dsimp only [Reg.x0, Reg.x1, Reg.x8] at hx0 hlen_eq hx8
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_206).base + bv% (16))
  apply sepWP_seg_ls_vm
    (Q := (blkPC_206).rebase (blkPl_206).base (hooksException H)) blkLib_eq_206
    (mid := (blkPl_206).base + bv% (16))
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem, wp_norm, arm64_norm] at hvm1 ⊢
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult hlen_eq hlt4), parseSidResultAt]
    apply sepWP_trans_vm
    · simp only [wp_norm, arm64_norm, hvm1]
    · by_vm_steps (wp_steps; wp_done)
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult hlen_eq hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 hlen_eq hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        apply sepWP_trans_vm
        · simp only [wp_norm, arm64_norm, hvm1]
        · by_vm_steps (wp_steps; wp_done)
      · have heq36 := length_eq_36_of_eq_40 hlen_eq hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        have hvm_after1 : VmPreserved s0 sf := by
          refine VmPreserved.trans ?_ ‹VmPreserved _ sf›
          simp only [wp_norm, arm64_norm, hvm1]
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          exact sepWP_trans_vm hvm_after1 (by by_vm_steps (wp_steps; wp_done))
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          exact sepWP_trans_vm hvm_after1 (by by_vm_steps (wp_steps; wp_done))
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 hlen_eq hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        apply sepWP_trans_vm
        · simp only [wp_norm, arm64_norm, hvm1]
        · by_vm_steps (wp_steps; wp_done)
      · have heq36 := length_eq_36_of_eq_36 hlen_eq hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        have hvm_after2 : VmPreserved s0 sf := by
          refine VmPreserved.trans ?_ ‹VmPreserved _ sf›
          simp only [wp_norm, arm64_norm, hvm1]
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          exact sepWP_trans_vm hvm_after2 (by by_vm_steps (wp_steps; wp_done))
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          exact sepWP_trans_vm hvm_after2 (by by_vm_steps (wp_steps; wp_done))

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
plain `uuidTryParseStackBudgetSpec hookStack` on Block `252`. -/
theorem parseSid_placed_ok_of_plain_contract_stack [LibsignalPlacement]
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (uuidTryParseStackBudgetSpec hookStack)) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec hookStack)) :=
  parseSid_placed_ok_of_contract_stack H hookStack
    (subroutine_ok_withLsCodeLoaded_of_plain huuid)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse)` on Block `252`. -/
theorem parseSid_placed_ok_of_code [LibsignalPlacement]
    (H : String → Option (State → State))
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec uuidTryParse)) := by
  have h0 := parseSid_placed_ok_of_contract_stack H uuidTryParseStack huuid
  have hspec : parseSidCodeStackBudgetSpec uuidTryParseStack = parseSidCodeBudgetSpec uuidTryParse := by
    simp only [parseSidCodeStackBudgetSpec, parseSidCodeBudgetSpec, withVmPreserved,
      parseSidCodeStackSpec, parseSidCodeSpec, stackAt_parseSid_eq_frame]
  rwa [hspec] at h0

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`uuidTryParseBudgetSpec uuidTryParse` on Block `252`. -/
theorem parseSid_placed_ok_of_contract [LibsignalPlacement]
    (H : String → Option (State → State))
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (uuidTryParseBudgetSpec uuidTryParse)) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec uuidTryParse)) :=
  parseSid_placed_ok_of_code H
    (subroutine_ok_withLsCodeLoaded_of_plain
      (uuidTryParseStackBudget_of_spec uuidTryParseStack huuid))

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
