/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Base
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializeBudget
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.BasePlacedBudget
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Top-Level Verification of `<Message>::deserialize`

Proves the allocation-budget `MessageDeserializePlacedOkX` and `blockProgram` theorems for
`<spqr::v1::chunked::states::Message>::deserialize` (Block `351`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsρ lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Message PolyApi decodeVarintLoop decodeVarintLoop_eq_spqrVarintAux spqrPolyApi)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (LsCallInv withLsCallInv)
open CryptoVerification.SpqrV1.Top.MessageDeserialize
  (DeserHighCalleeSaved MessageDeserializeCall PolyApiChunkLaw add_one_beq_zero_of_lt
   byte_word64_swap chunk32AtomsAt deserAfterVarint deserialize_eq_deserAfterVarint
   deserialize_err_of_gt_6 fold_messageErrorAt_region hiByte memRegion_48_eq_rawOutBufAt
   messageDeserializeStackX messageResultAt msgDeserFramePad msgDeserSavedAt msgDeserScratchAt
   msgDeser_fmt_slot_fold msgDeser_stack_restore ofNat_cons_length_beq_zero
   pointsTo64_entails_byte_memRegion7 rawOkOutAt rawOkOutAt_entails_ct1Ack rawOkOutAt_entails_none
   rawOutBufAt rawOutBufAt_entails_err_split shiftWord shiftWord_byte_swap sp_sub_144_aligned
   spqrDeallocSym spqrFormatInnerSym spqrPolyApi_chunkLaw stackAt_msgDeser_split tag_cases
   ule_five_32_of_gt_6 ule_five_64_of_gt_6 ule_sub_five_one_32_of_gt_6 ult_five_of_gt_6
   ult_one_sub_five_32_of_gt_6 ult_one_sub_five_64_of_gt_6 unshiftWord vecU8_live_entails_dealloc)
open CryptoVerification.SpqrV1.Top.Placed (blkLib_eq_351 blkPC_351 blkPl_351)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget (messageDeserializeSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
  (MessageDeserializePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.BasePlacedBudget
  (VarintPreStmtPlaced step_varint_pre_1_placed step_varint_pre_2_placed step_varint_pre_3_placed
   step_varint_pre_5_placed step_varint_pre_6_placed)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  ule_five_64_of_gt_6 ule_five_32_of_gt_6 ult_five_of_gt_6
  ule_sub_five_one_32_of_gt_6 ult_one_sub_five_32_of_gt_6 ult_one_sub_five_64_of_gt_6

private theorem align_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

private theorem align_pre_p {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post panicPost : State → SepProp → Prop} {oom : State → SepProp}
    (heq : P = P') (hwp : SepWPp prog target_pc s P' post panicPost oom) :
    SepWPp prog target_pc s P post panicPost oom :=
  heq ▸ hwp

private theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

private theorem sepWP_of_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q : State → SepProp → Prop}
    (h : SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → SepWP prog ret sm Pm Q))) :
    SepWP prog ret s Pre Q :=
  SepWP.seq h fun _ _ _ _ ⟨hvmp, hnext⟩ => hnext hvmp

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · exact let ⟨sf, hsteps', hout⟩ := hnext hvmp R hmm (hsteps.codeLoaded hL)
      ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem sepWP_msgDeser_finish [LibsignalPlacement]
    {P_poly : PolyApi} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)}
    {call : MessageDeserializeCall} {st : M.σ} {evs : List AllocEvent}
    (hevs : FreeOnlyEvs evs)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hwp : SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) ∗
          (call.fromPtr ↦ₛ call.fromBytes) ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt s0.sp messageDeserializeStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post := by
  subst hpost
  refine SepWP.mono hwp ?_
  intro sf P_f _ _ ⟨hvm, hent, hspf, hcsf, htrf⟩
  refine ⟨fun hmR => ?_, hspf, hcsf⟩
  have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
  rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs st) hvm] at hm1
  dsimp only [messageDeserializeSpecX]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, hevs⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1⟩

set_option maxHeartbeats 1600000 in
/-- Error branch for invalid tag `tag > 6` (`+700..+844`, 37 insns) on `Block 351`. -/
theorem step_err_fmt_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (ext : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (hFmt : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hpc : s.pc = (blkPl_351).base + 700#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hsp_align : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hcs_hi : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim st s ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).onPanic (call, st) s0 sf ∗ R)) := by
  have hsp_sub_align : (s0.sp - 144#64 &&& 15#64 == 0#64) = true := sp_sub_144_aligned s0 hsp_align
  rcases hcs_hi with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP
  unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt
  dsimp only [spqrFormatInnerSym, spqrDeallocSym] at hFmt hDealloc
  have hafter_fmt : ∀ (s1 : State) (bs : List (BitVec 8)) (cap ptr : BitVec 64),
      s1.pc = (blkPl_351).base + 752#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 144#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = call.out →
      s1.readReg64 .x29 = s0.sp - 48#64 →
      DeserHighCalleeSaved s0 s1 →
      bs.length ≤ cap.toNat →
      cap.toNat < 2 ^ 63 →
      SepWP ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext)) (s0.readReg64 .lr) s1
        ((((s0.sp - 136#64) ↦₆₄ cap) ∗
          ((s0.sp - 136#64 + 8#64) ↦₆₄ ptr) ∗
          ((s0.sp - 136#64 + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool lim st s1 ∗
          stackAt (s0.sp - 144#64) CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗
        (call.fromPtr ↦ₛ call.fromBytes) ∗
        rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
        memRegion (s0.sp - 144#64) 8 ∗
        memRegion (s0.sp - 87#64) 11 ∗
        memRegion (s0.sp - 70#64) 2 ∗
        memRegion (s0.sp - 67#64) 3 ∗
        ((s0.sp - 112#64) ↦₆₄ st3) ∗
        ((s0.sp - 104#64) ↦₈ st4) ∗
        ((s0.sp - 103#64) ↦₆₄ st5) ∗
        ((s0.sp - 95#64) ↦₆₄ st6) ∗
        ((s0.sp - 76#64) ↦₃₂ st0) ∗
        ((s0.sp - 72#64) ↦₁₆ st1) ∗
        ((s0.sp - 68#64) ↦₈ fb0) ∗
        ((s0.sp - 64#64) ↦₆₄ (s0.sp - 68#64)) ∗
        ((s0.sp - 56#64) ↦₆₄ lsmpl.ρ "_RNvXNtNtNtCskxtBwYRO61I_4core3fmt3num3imphNtB6_7Display3fmt") ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) post := by
    intro s1 bs cap ptr hpc1 hrun1 hsp1 htr1 hx19_1 hx29_1 hcs1_hi hle hlt
    rcases hcs1_hi with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩
    have ha8 : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_omega
    have ha16 : s0.sp - 136#64 + 16#64 = s0.sp - 120#64 := by bv_omega
    rw [ha8, ha16]
    by_cases hcap : cap = 0#64
    · subst hcap
      simp only [↓reduceIte, emp_sepConj]
      have hstep_nil : A.pool lim st s1 = A.pool lim (M.stepEvents ([] : List AllocEvent) st) s1 := by
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      rw [hstep_nil]
      refine sepWP_msgDeser_finish (evs := []) (by simp [FreeOnlyEvs]) hpost ?_
      by_vm_steps (
        refine SepWP.fold (pointsTo64_entails_byte_memRegion7 s0.sp ptr) (by sep_focus) ?_
        refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
          (by sep_focus) ?_
        wp_steps
        rw [herr]
        dsimp only [messageResultAt]
        refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
        refine SepWP.fold (msgDeser_stack_restore s0.sp 0#64 (ptr.extractLsb' 0 8)
          (BitVec.ofNat 64 bs.length) st3 st4 st5 st6 st0 st1 fb0
          (s0.sp - 68#64) (lsρ "_RNvXNtNtNtCskxtBwYRO61I_4core3fmt3num3imphNtB6_7Display3fmt")
          (s0.readReg64 .x29) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt; sep_focus) ?_
        refine align_pre (by sep_ac_rfl) ?_
        wp_done
      )
    · have hcbz : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      have hcmn : (cap + 1#64 == 0#64) = false := add_one_beq_zero_of_lt hlt
      simp only [hcap, ↓reduceIte]
      apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
        (Q := (blkPC_351).rebase (blkPl_351).base
          (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
        blkLib_eq_351 (mid := lsρ spqrDeallocSym)
      intro _m_strip
      wp_steps
      refine SepWP.fold (vecU8_live_entails_dealloc A.repAlloc ptr bs cap hle hlt) (by sep_focus) ?_
      refine SepWP.done (by wp_norm_goal; rfl) (by wp_norm_goal) fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm])) (hnext := ?_)
      apply (LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializeBudget.call_dealloc
        hDealloc ptr (s0.sp - 144#64) cap.toNat st (s0 := s0))
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_sub_align
      · wp_focus_close wp_norm_lhs
      · simp only [wp_norm, arm64_norm, blkPl_351]
        apply lsRetAddr624_blockPlacement_base_add <;> decide
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · sep_focus
      · intro s2 hpc2 hrun2 hsp2 htr2 _hacp2 hcs2
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
        simp only [arm64_norm, wp_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
        refine sepWP_msgDeser_finish (evs := rustDeallocEvents cap.toNat 1)
          (by simp [rustDeallocEvents, FreeOnlyEvs]) hpost ?_
        by_vm_steps (
          refine SepWP.fold (pointsTo64_entails_byte_memRegion7 s0.sp ptr) (by sep_focus) ?_
          refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
            (by sep_focus) ?_
          wp_steps
          rw [herr]
          dsimp only [messageResultAt]
          refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
          refine SepWP.fold (msgDeser_stack_restore s0.sp cap (ptr.extractLsb' 0 8)
            (BitVec.ofNat 64 bs.length) st3 st4 st5 st6 st0 st1 fb0
            (s0.sp - 68#64) (lsρ "_RNvXNtNtNtCskxtBwYRO61I_4core3fmt3num3imphNtB6_7Display3fmt")
            (s0.readReg64 .x29) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt; sep_focus) ?_
          refine align_pre (by sep_ac_rfl) ?_
          wp_done
        )
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWPp_seg_ls_vm
    (Q := (blkPC_351).rebase (blkPl_351).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_351 (mid := lsmpl.ρ "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner")
  intro _m_strip
  wp_steps
  refine SepWP.fold (msgDeser_fmt_slot_fold s0.sp f08 f10 f18) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real _hnsp => ?_
  refine ProofLib.SepWPp.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm])) (hnext := ?_)
  apply (LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializeBudget.call_formatInner_then_sepWP
    hFmt (s0.sp - 136#64) (s0.sp - 144#64) st (s0 := s0))
  · wp_focus_close wp_norm_goal
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · exact hsp_sub_align
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · sep_focus
  · intro s1 bs cap ptr hpc1 hrun1 hsp1 htr1 hcs1 hle hlt _hptr
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    refine align_pre (by sep_ac_rfl)
      (hafter_fmt s1 bs cap ptr hpc1 hrun1 hsp1 htr1 hx19_1
        (hx29_1.trans hx29)
        ⟨hx23_1.trans hx23, hx24_1.trans hx24, hx25_1.trans hx25,
         hx26_1.trans hx26, hx27_1.trans hx27, hx28_1.trans hx28,
         hvregs_1.trans hvregs⟩ hle hlt)

/-- Entry dispatch for `call.fromBytes = []` (`+0: cbz x3, +144` → `+144..+160`) on `Block 351`. -/
theorem step_entry_empty_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hempty : call.fromBytes = [])
    (hpc : s0.pc = (blkPl_351).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = call.out)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim st s0 ∗
      stackAt s0.sp messageDeserializeStackX) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s0 P post := by
  have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
    rw [hempty]; rfl
  have hx3_0 : s0.readReg64 .x3 = 0#64 := by rw [hx3, hempty]; rfl
  subst hP
  have hstep_nil : A.pool lim st s0 = A.pool lim (M.stepEvents ([] : List AllocEvent) st) s0 := by
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
  rw [hstep_nil]
  refine sepWP_msgDeser_finish (evs := []) (by simp [FreeOnlyEvs]) hpost ?_
  by_vm_steps (
    refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
      (by sep_focus) ?_
    wp_steps
    rw [herr]
    dsimp only [messageResultAt]
    refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  )

set_option maxHeartbeats 1200000 in
/-- Entry dispatch for `call.fromBytes = tag :: rest` with `6 < tag.toNat` (`+0..+36` →
    `+164..+168` → `+700..+844`) on `Block 351`. -/
theorem step_entry_tag_gt_6_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (ext : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (hFmt : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s29 s30 s22 s21 s20 s19 : BitVec 64)
    (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hbytes : call.fromBytes = tag :: rest)
    (htag : 6 < tag.toNat)
    (hlen : call.fromBytes.length < 2 ^ 63)
    (hpc : s0.pc = (blkPl_351).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = call.out)
    (hx2 : s0.readReg64 .x2 = call.fromPtr)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim st s0 ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp s29 s30 s22 s21 s20 s19) :
    SepWPp ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext)) (s0.readReg64 .lr)
      s0 P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).onPanic (call, st) s0 sf ∗ R)) := by
  have hlen' : (tag :: rest).length < 2 ^ 63 := hbytes ▸ hlen
  have hcbz : (BitVec.ofNat 64 (tag :: rest).length == 0#64) = false :=
    ofNat_cons_length_beq_zero tag rest hlen'
  have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
    rw [hbytes]; exact deserialize_err_of_gt_6 P_poly call.epoch tag rest htag
  have h_cont := step_err_fmt_placed P_poly ext A lim st hFmt hDealloc call
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 tag f50 f58 s0
  subst hP
  rw [hbytes, pointsToBytes_cons]
  rw [hbytes] at hx3
  unfold msgDeserScratchAt msgDeserSavedAt
  apply sepWPp_of_sepWP_vm (mid := (blkPl_351).base + 700#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [arm64_norm, wp_norm])
    intro hvmp
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvmp]
    apply h_cont _ _ R post hpost herr
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
  )

set_option maxHeartbeats 1200000 in
/-- Direct `Ok` epilogue (`+588..+660`) for non-chunk tags (`0#8`, `4#8`) on `Block 351`. -/
theorem step_ok_tail_direct_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (call : MessageDeserializeCall)
    (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hok : ∀ (c2 : BitVec 8) (idx16 : BitVec 16),
      rawOkOutAt call.out call.epoch tag st0 st1 c2 st3 st4 st5 st6 idx16 ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes))
    (hpc : s.pc = (blkPl_351).base + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx29 : s.readReg64 .fp = s0.sp - 48#64)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim (M.stepEvents evs st) s ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post := by
  refine sepWP_msgDeser_finish hevs hpost ?_
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP
  have hswap_st : (((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5)) ⊢
      ((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5) := by
    have h1 := byte_word64_swap (s0.sp - 104#64) st4 st5
    have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
    have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
    rw [ha1, ha8] at h1
    exact Entails.of_eq h1
  have hunswap_st : (((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5)) ⊢
      ((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5) := by
    have h1 := (byte_word64_swap (s0.sp - 104#64) st4 st5).symm
    have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
    have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
    rw [ha1, ha8] at h1
    exact Entails.of_eq h1
  have hswap_out : (((call.out + 25#64) ↦₈ oc4) ∗ ((call.out + 26#64) ↦₆₄ oc5)) ⊢
      ((call.out + 25#64) ↦₆₄ shiftWord oc4 oc5) ∗ ((call.out + 33#64) ↦₈ hiByte oc5) := by
    have h1 := byte_word64_swap (call.out + 25#64) oc4 oc5
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
    exact Entails.of_eq h1
  have hunswap_out : (((call.out + 25#64) ↦₆₄ shiftWord st4 st5) ∗ ((call.out + 33#64) ↦₈ hiByte oc5)) ⊢
      ((call.out + 25#64) ↦₈ st4) ∗ ((call.out + 26#64) ↦₆₄ unshiftWord (shiftWord st4 st5) (hiByte oc5)) := by
    have h1 := shiftWord_byte_swap (call.out + 25#64) st4 st5 (hiByte oc5)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
    exact Entails.of_eq h1
  let c2_val : BitVec 8 := BitVec.zeroExtend 8 (s.readReg64 (Reg.gpr 10#5))
  let idx16_val : BitVec 16 := BitVec.truncate 16 (BitVec.truncate 32 (s.readReg64 (Reg.gpr 9#5)))
  have hfold_ok :
      ((call.out ↦₆₄ call.epoch) ∗ ((call.out + 8#64) ↦₈ tag) ∗ ((call.out + 9#64) ↦₈ 1#8) ∗
        ((call.out + 10#64) ↦₃₂ st0) ∗ ((call.out + 14#64) ↦₁₆ st1) ∗
        ((call.out + 16#64) ↦₈ c2_val) ∗
        ((call.out + 17#64) ↦₆₄ st3) ∗ ((call.out + 25#64) ↦₈ st4) ∗
        ((call.out + 26#64) ↦₆₄ st5) ∗ ((call.out + 34#64) ↦₆₄ st6) ∗
        ((call.out + 42#64) ↦₁₆ idx16_val) ∗
        memRegion (call.out + 44#64) 4) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) := by
    refine Entails.trans ?_ (hok c2_val idx16_val)
    unfold rawOkOutAt chunk32AtomsAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  by_vm_steps (
    unfold rawOutBufAt chunk32AtomsAt msgDeserScratchAt msgDeserSavedAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps 5
    refine SepWP.fold hswap_st (by sep_focus) ?_
    wp_steps 1
    refine SepWP.fold hunswap_st (by sep_focus) ?_
    wp_steps 5
    refine SepWP.fold hswap_out (by sep_focus) ?_
    wp_steps 1
    refine SepWP.fold hunswap_out (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hfold_ok (by dsimp only [c2_val, idx16_val]; sep_focus) ?_
    refine SepWP.fold (msgDeser_stack_restore s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold msgDeserScratchAt msgDeserSavedAt
      sep_focus) ?_
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  )

set_option maxHeartbeats 1600000 in
/-- Entry dispatch for `call.fromBytes = tag :: rest` with `tag ∈ {0#8, 1#8, 2#8, 3#8, 4#8, 5#8,
    6#8}` on `Block 351`. -/
theorem step_entry_tag_le_6_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s29 s30 s22 s21 s20 s19 : BitVec 64)
    (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hbytes : call.fromBytes = tag :: rest)
    (htag : tag = 0#8 ∨ tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨
      tag = 4#8 ∨ tag = 5#8 ∨ tag = 6#8)
    (hlen : call.fromBytes.length < 2 ^ 63)
    (hpc : s0.pc = (blkPl_351).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = call.out)
    (hx1 : s0.readReg64 .x1 = call.epoch)
    (hx2 : s0.readReg64 .x2 = call.fromPtr)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim st s0 ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp s29 s30 s22 s21 s20 s19) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s0 P post := by
  have hevs : FreeOnlyEvs ([] : List AllocEvent) := by simp [FreeOnlyEvs]
  have hlen' : (tag :: rest).length < 2 ^ 63 := hbytes ▸ hlen
  have hcbz : (BitVec.ofNat 64 (tag :: rest).length == 0#64) = false :=
    ofNat_cons_length_beq_zero tag rest hlen'
  have h_ok0 := step_ok_tail_direct_placed P_poly hooks A lim st [] hevs call 0#8
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 0#8 f50 f58 s0
  have h_ok4 := step_ok_tail_direct_placed P_poly hooks A lim st [] hevs call 4#8
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 4#8 f50 f58 s0
  have h_pre3 := step_varint_pre_3_placed P_poly hPoly hooks A lim st [] call 3#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 3#8 f50 f58 s0
  have h_pre1 := step_varint_pre_1_placed P_poly hPoly hooks A lim st [] call 1#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 1#8 f50 f58 s0
  have h_pre2 := step_varint_pre_2_placed P_poly hPoly hooks A lim st [] call 2#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 2#8 f50 f58 s0
  have h_pre5 := step_varint_pre_5_placed P_poly hPoly hooks A lim st [] call 5#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 5#8 f18 st3 st4 st5 st6 st0 st1 5#8 f50 f58 s0
  have h_pre6 := step_varint_pre_6_placed P_poly hPoly hooks A lim st [] call 6#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 6#8 f18 st3 st4 st5 st6 st0 st1 6#8 f50 f58 s0
  unfold VarintPreStmtPlaced at h_pre3 h_pre1 h_pre2 h_pre5 h_pre6
  subst hP
  have hstep_nil : A.pool lim st s0 = A.pool lim (M.stepEvents ([] : List AllocEvent) st) s0 := by
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
  rw [hstep_nil]
  rw [hbytes, pointsToBytes_cons]
  rw [hbytes] at hx3
  unfold msgDeserScratchAt msgDeserSavedAt
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply sepWP_of_vm (mid := (blkPl_351).base + 588#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      apply h_ok0 _ _ R post hpost
      · intro c2 idx16
        have hres : Message.deserialize P_poly call.epoch call.fromBytes =
            .ok { epoch := call.epoch, payload := .none } := by rw [hbytes]; rfl
        rw [hres]; dsimp only [messageResultAt]
        exact rawOkOutAt_entails_none P_poly call.out call.epoch st0 st1 c2 st3 st4 st5 st6 idx16
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )
  · apply sepWP_of_vm (mid := (blkPl_351).base + 196#64)
    by_vm_steps (
      wp_steps 15
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
          deserAfterVarint P_poly call.epoch 1#8 (decodeVarintLoop 0 0#64 rest) := by
        rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 1#8 rest (Or.inl rfl),
          decodeVarintLoop_eq_spqrVarintAux]
        rfl
      apply h_pre1 _ _ R post hevs hpost (Or.inl rfl) hbytes hlen hdeser
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rw [hbytes]; wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )
  · apply sepWP_of_vm (mid := (blkPl_351).base + 364#64)
    by_vm_steps (
      wp_steps 15
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
          deserAfterVarint P_poly call.epoch 2#8 (decodeVarintLoop 0 0#64 rest) := by
        rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 2#8 rest (Or.inr (Or.inl rfl)),
          decodeVarintLoop_eq_spqrVarintAux]
        rfl
      apply h_pre2 _ _ R post hevs hpost (Or.inr (Or.inl rfl)) hbytes hlen hdeser
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rw [hbytes]; wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )
  · apply sepWP_of_vm (mid := (blkPl_351).base + 64#64)
    by_vm_steps (
      wp_steps 16
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
          deserAfterVarint P_poly call.epoch 3#8 (decodeVarintLoop 0 0#64 rest) := by
        rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 3#8 rest (Or.inr (Or.inr (Or.inl rfl))),
          decodeVarintLoop_eq_spqrVarintAux]
        rfl
      apply h_pre3 _ _ R post hevs hpost (Or.inr (Or.inr (Or.inl rfl))) hbytes hlen hdeser
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rw [hbytes]; wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )
  · apply sepWP_of_vm (mid := (blkPl_351).base + 588#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      apply h_ok4 _ _ R post hpost
      · intro c2 idx16
        have hres : Message.deserialize P_poly call.epoch call.fromBytes =
            .ok { epoch := call.epoch, payload := .ct1Ack true } := by rw [hbytes]; rfl
        rw [hres]; dsimp only [messageResultAt]
        exact rawOkOutAt_entails_ct1Ack P_poly call.out call.epoch st0 st1 c2 st3 st4 st5 st6 idx16
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )
  · apply sepWP_of_vm (mid := (blkPl_351).base + 284#64)
    by_vm_steps (
      wp_steps 19
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
          deserAfterVarint P_poly call.epoch 5#8 (decodeVarintLoop 0 0#64 rest) := by
        rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 5#8 rest (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          decodeVarintLoop_eq_spqrVarintAux]
        rfl
      apply h_pre5 _ _ R post hevs hpost (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hbytes hlen hdeser
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rw [hbytes]; wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )
  · apply sepWP_of_vm (mid := (blkPl_351).base + 444#64)
    by_vm_steps (
      wp_steps 19
      apply sepWP_done_tpidr_placed (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm])
      intro hvmp
      rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents ([] : List AllocEvent) st) hvmp]
      have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
          deserAfterVarint P_poly call.epoch 6#8 (decodeVarintLoop 0 0#64 rest) := by
        rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 6#8 rest (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
          decodeVarintLoop_eq_spqrVarintAux]
        rfl
      apply h_pre6 _ _ R post hevs hpost (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hbytes hlen hdeser
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rw [hbytes]; wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · rw [hbytes, pointsToBytes_cons]
        unfold msgDeserScratchAt msgDeserSavedAt; sep_ac_rfl
    )

attribute [local irreducible] rawOutBufAt msgDeserFramePad msgDeserScratchAt
  msgDeserSavedAt messageResultAt Message.deserialize

set_option maxHeartbeats 1600000 in
/-- Entry-point verification of `<spqr::v1::chunked::states::Message>::deserialize` (`Block
    351`, 212 insns). -/
theorem messageDeserialize_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (ext : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hFmt : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (blkPl_351).base
      (messageDeserializeSpecX P_poly M A lim) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨call, st⟩ R s0 hpc hrun hpre hsp_align
  change s0.mem ⊨
    (⌜s0.readReg64 .x0 = call.out ∧
      s0.readReg64 .x1 = call.epoch ∧
      s0.readReg64 .x2 = call.fromPtr ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length ∧
      call.fromBytes.length < 2 ^ 63⌝ ∗
     (memRegion call.out 48 ∗
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      A.pool lim st s0 ∗
      stackAt s0.sp messageDeserializeStackX)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen⟩, hpre⟩
  refine ⟨memRegion call.out 48 ∗
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      A.pool lim st s0 ∗
      stackAt s0.sp messageDeserializeStackX, R, hpre, ?_⟩
  conv =>
    arg 4
    simp only [memRegion_48_eq_rawOutBufAt call.out, sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro o2a
  apply SepWPp.exists_elim; intro oc6
  apply SepWPp.exists_elim; intro oc5
  apply SepWPp.exists_elim; intro oc4
  apply SepWPp.exists_elim; intro oc3
  apply SepWPp.exists_elim; intro oc2
  apply SepWPp.exists_elim; intro oc1
  apply SepWPp.exists_elim; intro oc0
  apply SepWPp.exists_elim; intro o9
  apply SepWPp.exists_elim; intro o8
  apply SepWPp.exists_elim; intro o0
  have hbytes_cases : call.fromBytes = [] ∨ ∃ tag rest, call.fromBytes = tag :: rest := by
    cases call.fromBytes with
    | nil => exact Or.inl rfl
    | cons t r => exact Or.inr ⟨t, r, rfl⟩
  rcases hbytes_cases with hbytes | ⟨tag, rest, hbytes⟩
  · apply SepWPp.of_sepWP_ret
    exact step_entry_empty_placed P_poly (Rust.withPanics ext) A lim st call
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a s0 _ R _ rfl
      hbytes hpc hrun hx0 hx3 (by sep_ac_rfl)
  · conv =>
      arg 4
      simp only [stackAt_msgDeser_split s0.sp, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro s19
    apply SepWPp.exists_elim; intro s20
    apply SepWPp.exists_elim; intro s21
    apply SepWPp.exists_elim; intro s22
    apply SepWPp.exists_elim; intro s30
    apply SepWPp.exists_elim; intro s29
    apply SepWPp.exists_elim; intro f58
    apply SepWPp.exists_elim; intro f50
    apply SepWPp.exists_elim; intro fb0
    apply SepWPp.exists_elim; intro st1
    apply SepWPp.exists_elim; intro st0
    apply SepWPp.exists_elim; intro st6
    apply SepWPp.exists_elim; intro st5
    apply SepWPp.exists_elim; intro st4
    apply SepWPp.exists_elim; intro st3
    apply SepWPp.exists_elim; intro f18
    apply SepWPp.exists_elim; intro f10
    apply SepWPp.exists_elim; intro f08
    rcases tag_cases tag with h0 | h1 | h2 | h3 | h4 | h5 | h6 | hgt6
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inl h0) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inl h1)) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inl h2))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inl h3)))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6_placed P_poly hPoly (Rust.withPanics ext) A lim st call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6)))))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by sep_ac_rfl)
    · exact step_entry_tag_gt_6_placed P_poly ext A lim st hFmt hDealloc call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes hgt6 hlen hpc hrun hsp_align
        hx0 hx2 hx3 (by sep_ac_rfl)

/-- `<spqr::v1::chunked::states::Message>::deserialize` (`Block 351`, 212 insns) meets
    `MessageDeserializePlacedOkX P_poly M A lim ext`. -/
theorem messageDeserialize_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State))
    (hFmt : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    MessageDeserializePlacedOkX P_poly M A lim ext :=
  subroutine_ok_mono (messageDeserialize_placed_ok_ext P_poly hPoly ext A lim hFmt hDealloc)
    (fun call R s0 hpre => by
      change s0.mem ⊨ (⌜LsCallInv lsmpl s0.mem⌝ ∗
        (messageDeserializeSpecX P_poly M A lim).pre call s0) ∗ R at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact hpre.2)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

theorem messageDeserialize_spqrPolyApi_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State))
    (hFmt : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    MessageDeserializePlacedOkX spqrPolyApi M A lim ext :=
  messageDeserialize_placed_ok_x spqrPolyApi spqrPolyApi_chunkLaw A lim ext hFmt hDealloc

theorem messageDeserialize_placed_ok_blockProgram [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (ext : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hFmt : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 351 (Rust.withPanics ext))
      (lsmpl.base 351)
      (messageDeserializeSpecX P_poly M A lim) := by
  have hok := messageDeserialize_placed_ok_ext P_poly hPoly ext A lim hFmt hDealloc
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))] at hok
  exact hok

end LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializePlacedBudget
