/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Front-Pop Loop of `<spqr::chain::Chain>::send_key` (Block `367`)

Proves the relocatable `[LibsignalPlacement]` front-epoch pop loop (`sendKey_pop_step_placed`,
`sendKey_pop_loop_placed`) and front-clear block (`sendKey_from_344_placed`) of Block `367` under
`RustCliAllocBudget M` with `chainEpochPopEvents`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPopBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_367 blkPl_367)
open CryptoVerification.LibsignalSpqrV1 (ChainEpoch)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost
  SepWP.conseq SepWP.seq_cps SepWP.seq_entails_plain
  cap_ne_neg_one chainEpochAlign chainEpochAt chainEpochAt_pack_clearNext
  chainEpochAt_unpack_send_next chainEpochSize clearFrontPre iterHead iterL2 k_plus_3_props
  ofNat_cons_len_props vecDequePhysIdx vecDequeRingBuf vecDequeRingBuf_get_front
  vecDequeRingBuf_pop_front_mul vecU8Rest_eq_zero zip_set_snd
)
open CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts (
  chainEpochAt_unpack_pop chainEpochSlot_entails_memRegion_112 physIdx_one_eq physIdx_zero_madd_eq
  vecDequeRingBuf_get_physIdx vecDequeRingBuf_set_physIdx
)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochFacts (
  vecU8Rest vecU8Rest_nonzero_entails
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (SepWP.pure_left_focus)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (allocCallPreserved_trans)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainEpochPopEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocSpecWithStack)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

/-- State-indexed sequential entailment combinator for `SepWP` when `P_mid` depends on `sm`
(e.g., via `A.pool lim st sm`). -/
theorem SepWP.seq_entails_state {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => Q sm ∧ (Pm ⊢ P_mid sm)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  unfold SepWP
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hQ, hent⟩ | ⟨hoom, hfalse⟩⟩
  · rcases (h2 sm hpcm hrunm hQ).elim
      (Satisfies.mono (sepConj_mono_left hent) hmm) (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, hfalse⟩⟩

/-- State-indexed join combinator for `SepWP` carrying `AllocCallPreserved` across conditional
`__rust_dealloc` branches. -/
theorem SepWP.join_plain_acp {prog : Program}
    {join_pc target : BitVec 64} {s : State} {P : SepProp} {P_join : State → SepProp}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog join_pc s P (fun sm Pm =>
      sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ AllocCallPreserved s sm ∧ (Pm ⊢ P_join sm)))
    (h2 : ∀ sm, sm.pc = join_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → AllocCallPreserved s sm →
      SepWP prog target sm (P_join sm) post) :
    SepWP prog target s P post := by
  unfold SepWP
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hsp, hcs, hacp, hent⟩ | ⟨hoom, hfalse⟩⟩
  · rcases (h2 sm hpcm hrunm hsp hcs hacp).elim
      (Satisfies.mono (sepConj_mono_left hent) hmm) (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, hfalse⟩⟩

/-- Budget-threaded heap footprint of the front-epoch pop loop in `Chain::send_key`. -/
def popLoopPre (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) (selfPtr cap ptr head l2 : BitVec 64)
    (epochs : List ChainEpochGhost) (links : List ChainEpoch) : SepProp :=
  ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ l2) ∗
  ((selfPtr + 16#64) ↦₆₄ head) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links.length) ∗
  vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
    cap ptr head (epochs.zip links) ∗
  A.pool lim st s ∗ stackAt s.sp extHookStack

set_option maxHeartbeats 1600000 in
/-- Single iteration of `Chain::send_key`'s front-epoch pop loop (`+164 -> +148`), advancing the
cost-model state by `chainEpochPopEvents gce` and preserving `AllocCallPreserved`. -/
theorem sendKey_pop_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack))
    (selfPtr cap ptr head l2 : BitVec 64) (gce : ChainEpochGhost) (epochs' : List ChainEpochGhost)
    (ce : ChainEpoch) (links' : List ChainEpoch)
    (hlen_le : (ce :: links').length ≤ cap.toNat) (hlen_eq : epochs'.length = links'.length)
    (st : M.σ) (s : State) (hpc : s.pc = (blkPl_367).base + 164#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (ce :: links').length)
    (hx20 : s.readReg64 (.gpr 20#5) = selfPtr) (hx22 : s.readReg64 (.gpr 22#5) = head) :
    let head1 := BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 148#64) s
      (popLoopPre M A lim st s selfPtr cap ptr head l2 (gce :: epochs') (ce :: links'))
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 22#5) = head1 ∧ sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links'.length ∧
         sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
         AllocCallPreserved s sf) ∧
        (P' ⊢ popLoopPre M A lim (M.stepEvents (chainEpochPopEvents gce) st) sf
          selfPtr cap ptr head1 gce.recv.prev.ptr epochs' links')) := by
  intro head1; dsimp only [head1] at *; unfold popLoopPre; simp only [List.zip_cons_cons]
  let ev1 := if gce.send.next.cap = 0#64 then ([] : List LibsignalBinary.Heap.AllocEvent) else rustDeallocEvents gce.send.next.cap.toNat 1
  let ev2 := if gce.send.prev.cap = 0#64 then ([] : List LibsignalBinary.Heap.AllocEvent) else rustDeallocEvents gce.send.prev.cap.toNat 1
  let ev3 := if gce.recv.next.cap = 0#64 then ([] : List LibsignalBinary.Heap.AllocEvent) else rustDeallocEvents gce.recv.next.cap.toNat 1
  let ev4 := if gce.recv.prev.cap = 0#64 then ([] : List LibsignalBinary.Heap.AllocEvent) else rustDeallocEvents gce.recv.prev.cap.toNat 1
  let st1 := M.stepEvents ev1 st
  let st2 := M.stepEvents ev2 st1
  let st3 := M.stepEvents ev3 st2
  let st4 := M.stepEvents ev4 st3
  have hst4_eq : st4 = M.stepEvents (chainEpochPopEvents gce) st := by
    simp only [st4, st3, st2, st1, ev4, ev3, ev2, ev1,
      ← LibsignalBinary.Heap.AllocCostModel.stepEvents_append, chainEpochPopEvents,
      List.append_assoc]
  have hzip_le : ((gce, ce) :: epochs'.zip links').length ≤ cap.toNat := by
    simp only [List.length_cons, List.length_zip, hlen_eq, Nat.min_self] at hlen_le ⊢; exact hlen_le
  refine SepWP.fold (vecDequeRingBuf_get_front A.repAlloc cap ptr head (gce, ce) (epochs'.zip links') hzip_le) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
  refine SepWP.fold (chainEpochAt_unpack_pop A.repAlloc gce ce (ptr + head * 112#64)) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hs_n_le, hs_n_lt, hs_n_ptr, hs_p_le, hs_p_lt, hs_p_ptr, hr_n_le, hr_n_lt, hr_n_ptr, hr_p_le, hr_p_lt, hr_p_ptr⟩
  have ⟨hx8_ne0, hx8_add, hx8_sub⟩ := ofNat_cons_len_props ce links' hlen_le hcap_lt
  have hhead1_eq := physIdx_one_eq hhead hcap_lt; have hcmn := cap_ne_neg_one hs_n_lt
  wp_norm_hyp hsp_align; wp_norm_hyp hx8; wp_norm_hyp hx20; wp_norm_hyp hx22
  wp_norm_hyp hx8_ne0; wp_norm_hyp hx8_add; wp_norm_hyp hx8_sub; wp_norm_hyp hhead1_eq; wp_norm_hyp hcmn
  apply SepWP.seq_cps (mid := (blkPl_367).base + 232#64)
  wp_steps_sync_pool ((blkPl_367).base + 232#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine SepWP.join_plain_acp (join_pc := (blkPl_367).base + 248#64)
    (P_join := fun sm =>
      ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
      vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc) cap ptr head1 (epochs'.zip links') ∗
      (gce.send.prev.ptr ↦ₛ ce.send.prev.data) ∗ vecU8Rest A.repAlloc gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data.length ∗
      (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
      (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
      A.pool lim st1 sm ∗ stackAt s.sp extHookStack) ?_ ?_
  · by_cases hcap1 : gce.send.next.cap = 0#64
    · have hcap1_beq : (gce.send.next.cap == 0#64) = true := by simp [hcap1]
      wp_norm_hyp hcap1_beq
      refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A.repAlloc gce.send.next.ptr hcap1 hs_n_le)) (by sep_focus) ?_
      wp_steps_sync_pool ((blkPl_367).base + 248#64)
      refine SepWP.fold (chainEpochSlot_entails_memRegion_112 (ptr + head * 112#64)
        gce.send.next.cap gce.send.next.ptr (BitVec.ofNat 64 ce.send.next.length)
        gce.send.prev.cap gce.send.prev.ptr (BitVec.ofNat 64 ce.send.prev.data.length)
        gce.recv.next.cap gce.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)
        gce.recv.prev.cap gce.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)
        ce.send.ctr ce.recv.ctr) (by sep_focus) ?_
      refine SepWP.fold (vecDequeRingBuf_pop_front_mul A.repAlloc cap ptr head (gce, ce) (epochs'.zip links')
        hhead hcap_lt hptr hzip_le) (by sep_focus) ?_
      have hst1 : st1 = st := by
        simp only [st1, ev1, hcap1, ite_true, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
        by unfold AllocCallPreserved; wp_norm_goal, ?_⟩
      rw [hst1]; simp only [wp_norm, arm64_norm]; sep_frame
    · have hcap1_beq : (gce.send.next.cap == 0#64) = false := beq_false_of_ne hcap1
      wp_norm_hyp hcap1_beq
      refine SepWP.fold (vecU8Rest_nonzero_entails A.repAlloc gce.send.next.ptr hcap1 hs_n_le hs_n_lt) (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos1, _, hisize1⟩
      apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      refine SepWP.fold (chainEpochSlot_entails_memRegion_112 (ptr + head * 112#64)
        gce.send.next.cap gce.send.next.ptr (BitVec.ofNat 64 ce.send.next.length)
        gce.send.prev.cap gce.send.prev.ptr (BitVec.ofNat 64 ce.send.prev.data.length)
        gce.recv.next.cap gce.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)
        gce.recv.prev.cap gce.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)
        ce.send.ctr ce.recv.ctr) (by sep_focus) ?_
      refine SepWP.fold (vecDequeRingBuf_pop_front_mul A.repAlloc cap ptr head (gce, ce) (epochs'.zip links')
        hhead hcap_lt hptr hzip_le) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      wp_call hdealloc (gce.send.next.ptr, gce.send.next.cap.toNat, 1, st)
      have hst1 : st1 = M.stepEvents (rustDeallocEvents gce.send.next.cap.toNat 1) st := by
        simp only [st1, ev1, hcap1, ite_false]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
        by have h := ‹AllocCallPreserved _ _›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h, ?_⟩
      rw [hst1]; sep_frame
  · intro sf1 hpc1 hrun1 hsp1 hcs1 hacp1
    have hsp1_eq : sf1.sp = s.sp := hsp1
    have htr1 : sf1.trace = s.trace := hacp1.2.1
    wp_split_join hsp1 hcs1; wp_norm_hyp htr1
    refine SepWP.join_plain_acp (join_pc := (blkPl_367).base + 268#64)
      (P_join := fun sm =>
        ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
        vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc) cap ptr head1 (epochs'.zip links') ∗
        (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
        (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
        A.pool lim st2 sm ∗ stackAt s.sp extHookStack) ?_ ?_
    · by_cases hcap2 : gce.send.prev.cap = 0#64
      · have hcap2_beq : (gce.send.prev.cap == 0#64) = true := by simp [hcap2]
        wp_norm_hyp hcap2_beq
        refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A.repAlloc gce.send.prev.ptr hcap2 hs_p_le)) (by sep_focus) ?_
        wp_steps_sync_pool ((blkPl_367).base + 268#64)
        have hst2 : st2 = st1 := by
          simp only [st2, ev2, hcap2, ite_true, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
          by unfold AllocCallPreserved; wp_norm_goal, ?_⟩
        rw [hst2]; simp only [wp_norm, arm64_norm]; sep_frame
      · have hcap2_beq : (gce.send.prev.cap == 0#64) = false := beq_false_of_ne hcap2
        wp_norm_hyp hcap2_beq
        refine SepWP.fold (vecU8Rest_nonzero_entails A.repAlloc gce.send.prev.ptr hcap2 hs_p_le hs_p_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos2, _, hisize2⟩
        apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf1.sp extHookStack by rw [hsp1_eq])) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        wp_call hdealloc (gce.send.prev.ptr, gce.send.prev.cap.toNat, 1, st1)
        refine SepWP.fold (Entails.of_eq (show stackAt sf1.sp extHookStack = stackAt s.sp extHookStack by rw [hsp1_eq])) (by sep_focus) ?_
        have hst2 : st2 = M.stepEvents (rustDeallocEvents gce.send.prev.cap.toNat 1) st1 := by
          simp only [st2, ev2, hcap2, ite_false]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
          by have h := ‹AllocCallPreserved _ _›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h, ?_⟩
        rw [hst2]; sep_frame
    · intro sf2 hpc2 hrun2 hsp2 hcs2 hacp2
      have hsp2_eq : sf2.sp = s.sp := hsp2.trans hsp1_eq
      have hacp02 : AllocCallPreserved s sf2 := allocCallPreserved_trans hacp1 hacp2
      have htr2 : sf2.trace = s.trace := hacp02.2.1
      wp_split_join hsp2 hcs2; wp_norm_hyp htr2
      refine SepWP.join_plain_acp (join_pc := (blkPl_367).base + 288#64)
        (P_join := fun sm =>
          ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
          ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
          vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc) cap ptr head1 (epochs'.zip links') ∗
          (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
          A.pool lim st3 sm ∗ stackAt s.sp extHookStack) ?_ ?_
      · by_cases hcap3 : gce.recv.next.cap = 0#64
        · have hcap3_beq : (gce.recv.next.cap == 0#64) = true := by simp [hcap3]
          wp_norm_hyp hcap3_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A.repAlloc gce.recv.next.ptr hcap3 hr_n_le)) (by sep_focus) ?_
          wp_steps_sync_pool ((blkPl_367).base + 288#64)
          have hst3 : st3 = st2 := by
            simp only [st3, ev3, hcap3, ite_true, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
            by unfold AllocCallPreserved; wp_norm_goal, ?_⟩
          rw [hst3]; simp only [wp_norm, arm64_norm]; sep_frame
        · have hcap3_beq : (gce.recv.next.cap == 0#64) = false := beq_false_of_ne hcap3
          wp_norm_hyp hcap3_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A.repAlloc gce.recv.next.ptr hcap3 hr_n_le hr_n_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos3, _, hisize3⟩
          apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf2.sp extHookStack by rw [hsp2_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          wp_call hdealloc (gce.recv.next.ptr, gce.recv.next.cap.toNat, 1, st2)
          refine SepWP.fold (Entails.of_eq (show stackAt sf2.sp extHookStack = stackAt s.sp extHookStack by rw [hsp2_eq])) (by sep_focus) ?_
          have hst3 : st3 = M.stepEvents (rustDeallocEvents gce.recv.next.cap.toNat 1) st2 := by
            simp only [st3, ev3, hcap3, ite_false]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
            by have h := ‹AllocCallPreserved _ _›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h, ?_⟩
          rw [hst3]; sep_frame
      · intro sf3 hpc3 hrun3 hsp3 hcs3 hacp3
        have hsp3_eq : sf3.sp = s.sp := hsp3.trans hsp2_eq
        have hacp03 : AllocCallPreserved s sf3 := allocCallPreserved_trans hacp02 hacp3
        have htr3 : sf3.trace = s.trace := hacp03.2.1
        wp_split_join hsp3 hcs3; wp_norm_hyp htr3
        by_cases hcap4 : gce.recv.prev.cap = 0#64
        · have hcap4_beq : (gce.recv.prev.cap == 0#64) = true := by simp [hcap4]
          wp_norm_hyp hcap4_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A.repAlloc gce.recv.prev.ptr hcap4 hr_p_le)) (by sep_focus) ?_
          wp_steps_sync_pool ((blkPl_367).base + 148#64)
          have hst4 : st3 = M.stepEvents (chainEpochPopEvents gce) st := by
            rw [← hst4_eq]
            simp only [st4, ev4, hcap4, ite_true, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            allocCallPreserved_trans hacp03 (by unfold AllocCallPreserved; wp_norm_goal)⟩, ?_⟩
          rw [← hst4]; simp only [hsp3_eq, wp_norm, arm64_norm]; sep_frame
        · have hcap4_beq : (gce.recv.prev.cap == 0#64) = false := beq_false_of_ne hcap4
          wp_norm_hyp hcap4_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A.repAlloc gce.recv.prev.ptr hcap4 hr_p_le hr_p_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos4, _, hisize4⟩
          apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf3.sp extHookStack by rw [hsp3_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          wp_call hdealloc (gce.recv.prev.ptr, gce.recv.prev.cap.toNat, 1, st3)
          wp_steps_sync_pool ((blkPl_367).base + 148#64)
          refine SepWP.fold (Entails.of_eq (show stackAt sf3.sp extHookStack = stackAt s.sp extHookStack by rw [hsp3_eq])) (by sep_focus) ?_
          have hst4 : M.stepEvents (rustDeallocEvents gce.recv.prev.cap.toNat 1) st3 =
              M.stepEvents (chainEpochPopEvents gce) st := by
            rw [← hst4_eq]
            simp only [st4, ev4, hcap4, ite_false]
          have hacp4 : AllocCallPreserved sf3 sf := by
            have h := ‹AllocCallPreserved _ sf›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
          have htr4 : sf.trace = s.trace := (allocCallPreserved_trans hacp03 hacp4).2.1
          wp_norm_hyp htr4
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            allocCallPreserved_trans hacp03 (allocCallPreserved_trans hacp4 (by unfold AllocCallPreserved; wp_norm_goal))⟩, ?_⟩
          rw [← hst4]; simp only [hsp3_eq, wp_norm, arm64_norm]; sep_frame

/-- Base-case loop exit check (`+148 -> +344`) preserving `popLoopPre` and `AllocCallPreserved`. -/
theorem sendKey_pop_check_zero_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (s sm : State) (st : M.σ) (selfPtr cap ptr l2 : BitVec 64)
    (epochs' : List ChainEpochGhost) (ce2 : ChainEpoch) (links'' : List ChainEpoch)
    (hlen'_le : (ce2 :: links'').length ≤ cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hpcm : sm.pc = (blkPl_367).base + 148#64) (hrunm : sm.status = .Running)
    (hsp_m : sm.sp = s.sp) (hsp_align_m : sm.spAligned = true)
    (hx19_m : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)) (hx20_m : sm.readReg64 (.gpr 20#5) = selfPtr)
    (hx22_m : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1))
    (hx27_m : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (ce2 :: links'').length)
    (hx28_m : sm.readReg64 (.gpr 28#5) = 2#64) (hx29_m : sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5))
    (htr_m : sm.trace = s.trace) (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s) :
    let head1 := BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1)
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 344#64) sm
      (popLoopPre M A lim st sm selfPtr cap ptr head1 l2 epochs' (ce2 :: links''))
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 22#5) = head1 ∧
         sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (ce2 :: links'').length ∧
         sf.readReg64 (.gpr 28#5) = 1#64 ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
         AllocCallPreserved sm sf) ∧
        (P' ⊢ popLoopPre M A lim st sf selfPtr cap ptr head1 l2 epochs' (ce2 :: links''))) := by
  intro head1; dsimp only [head1] at *; unfold popLoopPre
  have ⟨hx27_ne0, _, _⟩ := ofNat_cons_len_props ce2 links'' hlen'_le hcap_lt
  wp_norm_hyp hx19_m; wp_norm_hyp hx20_m; wp_norm_hyp hx22_m; wp_norm_hyp hx27_m
  wp_norm_hyp hx28_m; wp_norm_hyp hx29_m; wp_norm_hyp htr_m; wp_norm_hyp hv_m; wp_norm_hyp hx27_ne0
  wp_steps_sync_pool ((blkPl_367).base + 344#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨hsp_m, hsp_align_m, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by unfold AllocCallPreserved; wp_norm_goal⟩, ?_⟩
  simp only [wp_norm, arm64_norm]; sep_frame

/-- Inductive-step loop continuation check (`+148 -> +164`) preserving `popLoopPre` and `AllocCallPreserved`. -/
theorem sendKey_pop_check_succ_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (s sm : State) (st : M.σ) (selfPtr cap ptr head1 l2 : BitVec 64)
    (k : Nat) (epochs' : List ChainEpochGhost) (links' : List ChainEpoch)
    (hk_lt_cap : k + 2 < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hpcm : sm.pc = (blkPl_367).base + 148#64) (hrunm : sm.status = .Running) (hsp_align_m : sm.spAligned = true)
    (hx19_m : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)) (hx20_m : sm.readReg64 (.gpr 20#5) = selfPtr)
    (hx22_m : sm.readReg64 (.gpr 22#5) = head1) (hx27_m : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links'.length)
    (hx28_m : sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 3)) (hx29_m : sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5))
    (htr_m : sm.trace = s.trace) (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s) :
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 164#64) sm
      (popLoopPre M A lim st sm selfPtr cap ptr head1 l2 epochs' links')
      (fun sm2 P2 =>
        (sm2.sp = sm.sp ∧ sm2.spAligned = true ∧
         sm2.readReg64 (.gpr 8#5) = BitVec.ofNat 64 links'.length ∧
         sm2.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sm2.readReg64 (.gpr 20#5) = selfPtr ∧
         sm2.readReg64 (.gpr 22#5) = head1 ∧ sm2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 2) ∧
         sm2.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sm2.trace = s.trace ∧ calleeSavedVRegs sm2 = calleeSavedVRegs s ∧
         AllocCallPreserved sm sm2) ∧
        (P2 ⊢ popLoopPre M A lim st sm2 selfPtr cap ptr head1 l2 epochs' links')) := by
  unfold popLoopPre
  have ⟨hk_add, hk_sub, hk_ule, hk_ult1, hk_ne1, hk_ult2⟩ := k_plus_3_props k hk_lt_cap hcap_lt
  wp_norm_hyp hx19_m; wp_norm_hyp hx20_m; wp_norm_hyp hx22_m; wp_norm_hyp hx27_m
  wp_norm_hyp hx28_m; wp_norm_hyp hx29_m; wp_norm_hyp htr_m; wp_norm_hyp hv_m
  wp_norm_hyp hk_add; wp_norm_hyp hk_sub; wp_norm_hyp hk_ule; wp_norm_hyp hk_ult1
  wp_norm_hyp hk_ne1; wp_norm_hyp hk_ult2
  wp_steps_sync_pool ((blkPl_367).base + 164#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨by wp_norm_goal, hsp_align_m, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by unfold AllocCallPreserved; wp_norm_goal⟩, ?_⟩
  simp only [wp_norm, arm64_norm]; sep_frame

/-- Full front-epoch pop loop (`+164 -> +344`) of `Chain::send_key`, popping `k + 1` front epochs
and stepping the cost-model state by `((epochs.take (k + 1)).flatMap chainEpochPopEvents)`. -/
theorem sendKey_pop_loop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack))
    (selfPtr cap ptr : BitVec 64) (hcap_lt : cap.toNat * 112 < 2 ^ 63) (k : Nat) :
    ∀ (head l2 : BitVec 64) (epochs : List ChainEpochGhost) (links : List ChainEpoch)
      (_ : k + 1 < links.length) (_ : links.length ≤ cap.toNat) (_ : epochs.length = links.length)
      (st : M.σ) (s : State) (_ : s.pc = (blkPl_367).base + 164#64) (_ : s.status = .Running)
      (_ : s.spAligned = true) (_ : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 links.length)
      (_ : s.readReg64 (.gpr 20#5) = selfPtr) (_ : s.readReg64 (.gpr 22#5) = head)
      (_ : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 2)),
      SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 344#64) s
        (popLoopPre M A lim st s selfPtr cap ptr head l2 epochs links)
        (fun sf P' =>
          (sf.sp = s.sp ∧ sf.spAligned = true ∧
           sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
           sf.readReg64 (.gpr 22#5) = iterHead cap.toNat head (k + 1) ∧
           sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (links.drop (k + 1)).length ∧
           sf.readReg64 (.gpr 28#5) = 1#64 ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
           sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
           AllocCallPreserved s sf) ∧
          (P' ⊢ popLoopPre M A lim
            (M.stepEvents ((epochs.take (k + 1)).flatMap chainEpochPopEvents) st) sf
            selfPtr cap ptr
            (iterHead cap.toNat head (k + 1)) (iterL2 l2 epochs (k + 1))
            (epochs.drop (k + 1)) (links.drop (k + 1)))) := by
  induction k with
  | zero =>
    intro head l2 epochs links hk hlen_le hlen_eq st s hpc hrun hsp_align hx8 hx20 hx22 hx28
    rcases links with _ | ⟨ce, links'⟩; · simp at hk
    rcases epochs with _ | ⟨gce, epochs'⟩; · simp at hlen_eq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq
    have hstep := sendKey_pop_step_placed hdealloc selfPtr cap ptr head l2 gce epochs' ce links'
      hlen_le hlen_eq st s hpc hrun hsp_align hx8 hx20 hx22
    dsimp only at hstep; refine SepWP.seq_entails_state hstep ?_
    rintro sm hpcm hrunm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m, hacp_m⟩
    rcases links' with _ | ⟨ce2, links''⟩; · simp at hk
    have hlen'_le : (ce2 :: links'').length ≤ cap.toNat := by simp only [List.length_cons] at hlen_le ⊢; omega
    have hx22_m' : sm.readReg64 (.gpr 22#5) =
        BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1) := by rw [hx22]; exact hx22_m
    have hchk := sendKey_pop_check_zero_placed (M := M) (A := A) (lim := lim) (H := H)
      s sm (M.stepEvents (chainEpochPopEvents gce) st) selfPtr cap ptr gce.recv.prev.ptr epochs' ce2 links''
      hlen'_le hcap_lt hpcm hrunm hsp_m hsp_align_m hx19_m hx20_m hx22_m' hx27_m (hx28_m.trans hx28) hx29_m htr_m hv_m
    dsimp only at hchk
    rw [hx22] at hchk
    simp only [iterHead, iterL2, List.drop_succ_cons, List.drop_zero,
      List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine SepWP.conseq hchk ?_
    rintro sf P' ⟨⟨hsp_f, hsp_align_f, hx19_f, hx20_f, hx22_f, hx27_f, hx28_f, hx29_f, htr_f, hv_f, hacp_f⟩, hent_f⟩
    exact ⟨⟨hsp_f, hsp_align_f, hx19_f, hx20_f, hx22_f, hx27_f, hx28_f, hx29_f, htr_f, hv_f,
      allocCallPreserved_trans hacp_m hacp_f⟩, hent_f⟩
  | succ k ih =>
    intro head l2 epochs links hk hlen_le hlen_eq st s hpc hrun hsp_align hx8 hx20 hx22 hx28
    rcases links with _ | ⟨ce, links'⟩; · simp at hk
    rcases epochs with _ | ⟨gce, epochs'⟩; · simp at hlen_eq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq
    have hstep := sendKey_pop_step_placed hdealloc selfPtr cap ptr head l2 gce epochs' ce links'
      hlen_le hlen_eq st s hpc hrun hsp_align hx8 hx20 hx22
    dsimp only at hstep; refine SepWP.seq_entails_state hstep ?_
    rintro sm hpcm hrunm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m, hacp_m⟩
    have hk_lt_cap : k + 2 < cap.toNat := by simp only [List.length_cons] at hk hlen_le; omega
    have hchk := sendKey_pop_check_succ_placed (M := M) (A := A) (lim := lim) (H := H)
      s sm (M.stepEvents (chainEpochPopEvents gce) st) selfPtr cap ptr
      (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr k epochs' links'
      hk_lt_cap hcap_lt hpcm hrunm hsp_align_m hx19_m hx20_m hx22_m hx27_m (hx28_m.trans hx28) hx29_m htr_m hv_m
    refine SepWP.seq_entails_state hchk ?_
    rintro sm2 hpcm2 hrunm2 ⟨hsp_m2, hsp_align_m2, hx8_m2, hx19_m2, hx20_m2, hx22_m2, hx28_m2, hx29_m2, htr_m2, hv_m2, hacp_m2⟩
    have hk' : k + 1 < links'.length := by simp only [List.length_cons] at hk; omega
    have hlen'_le : links'.length ≤ cap.toNat := by simp only [List.length_cons] at hlen_le; omega
    have hih := ih (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr
      epochs' links' hk' hlen'_le hlen_eq (M.stepEvents (chainEpochPopEvents gce) st)
      sm2 hpcm2 hrunm2 hsp_align_m2 hx8_m2 hx20_m2 hx22_m2 hx28_m2
    simp only [iterHead, iterL2, List.drop_succ_cons, List.take_succ_cons, List.flatMap_cons,
      LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    refine SepWP.conseq hih ?_
    rintro sf P' ⟨⟨hsp_f, hsp_align_f, hx19_f, hx20_f, hx22_f, hx27_f, hx28_f, hx29_f, htr_f, hv_f, hacp_f⟩, hent_f⟩
    exact ⟨⟨hsp_f.trans (hsp_m2.trans hsp_m), hsp_align_f, hx19_f.trans hx19_m2, hx20_f, hx22_f,
      hx27_f, hx28_f, hx29_f.trans hx29_m2, htr_f.trans htr_m2, hv_f.trans hv_m2,
      allocCallPreserved_trans hacp_m (allocCallPreserved_trans hacp_m2 hacp_f)⟩, hent_f⟩

/-- Relocatable `+344 -> +380` front-clear block of `Chain::send_key`, preserving both
`AllocCallPreserved` and `VmPreserved` so `A.pool lim st` transports across it. -/
theorem sendKey_from_344_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {H : String → Option (State → State)}
    (selfPtr cap ptr head1 : BitVec 64) (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch)
    (h0 : 0 < links1.length) (hlen_le : links1.length ≤ cap.toNat) (hlen_eq : epochs1.length = links1.length)
    (s : State) (hpc : s.pc = (blkPl_367).base + 344#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hx20 : s.readReg64 (.gpr 20#5) = selfPtr) :
    let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 380#64) s
      (clearFrontPre A.repAlloc selfPtr cap ptr head1 epochs1 links1)
      (fun sf P' =>
        VmPreserved s sf ∧
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧ sf.readReg64 (.gpr 28#5) = 1#64 ∧
         sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sf.trace = s.trace ∧
         calleeSavedVRegs sf = calleeSavedVRegs s ∧
         AllocCallPreserved s sf) ∧
        (P' ⊢ clearFrontPre A.repAlloc selfPtr cap ptr head1 epochs1 links2)) := by
  intro links2; dsimp only [links2] at *; unfold clearFrontPre
  have hzip_len : (epochs1.zip links1).length = links1.length := by simp [hlen_eq]
  have hzip_le : (epochs1.zip links1).length ≤ cap.toNat := by omega
  have hzip_0 : 0 < (epochs1.zip links1).length := by omega
  have hzip_get0 : (epochs1.zip links1)[0] = (epochs1[0]'(by omega), links1[0]'h0) := by simp [List.getElem_zip]
  have hzip_set : (epochs1.zip links1).set 0
      (epochs1[0]'(by omega), { links1[0] with send := links1[0].send.clearNext }) =
      epochs1.zip (links1.set 0 { links1[0] with send := links1[0].send.clearNext }) :=
    zip_set_snd epochs1 links1 0 (epochs1[0]'(by omega)) _ (List.getElem?_eq_getElem (by omega))
  by_vm_steps
    refine SepWP.fold (vecDequeRingBuf_get_physIdx A.repAlloc cap ptr head1 (epochs1.zip links1) hzip_le hzip_0) (by sep_focus) ?_
    refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
    rw [hzip_get0]
    refine SepWP.fold (chainEpochAt_unpack_send_next A.repAlloc (epochs1[0]'(by omega)) (links1[0]'h0)
      (ptr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap.toNat 0 * 112))) (by sep_focus) ?_
    refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hle0, hcap0, hptr0⟩
    have hmadd0 := physIdx_zero_madd_eq (ptr := ptr) hhead hcap_lt
    have hpack_ce := chainEpochAt_pack_clearNext A.repAlloc (epochs1[0]'(by omega)) (links1[0]'h0)
      (ptr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap.toNat 0 * 112)) hle0 hcap0 hptr0
    have hset := vecDequeRingBuf_set_physIdx A.repAlloc cap ptr head1 (epochs1.zip links1)
      (epochs1[0]'(by omega), { links1[0] with send := links1[0].send.clearNext })
      hhead hcap_lt hptr hzip_le hzip_0
    dsimp only at hset
    rw [hzip_set] at hset
    wp_norm_hyp hx20; wp_norm_hyp hmadd0; wp_steps
    refine SepWP.fold hpack_ce (by sep_focus) ?_
    refine SepWP.fold hset (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine ⟨by wp_norm_goal, ⟨by wp_norm_goal, hsp_align, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by unfold AllocCallPreserved; wp_norm_goal⟩, ?_⟩
    sep_frame

end LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPopBudget
