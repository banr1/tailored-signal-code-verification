/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Base
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Base Step Lemmas for `<Message>::deserialize`

`VmPreserved`-strengthened relocatable base steppers for
`<spqr::v1::chunked::states::Message>::deserialize` (Block `351`) under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.BasePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1 (Message PolyApi decodeVarintLoop)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Top.MessageDeserialize
  (DeserHighCalleeSaved MessageDeserializeCall PolyApiChunkLaw byte_word64_swap chunk32AtX10
   chunk32AtomsAt decodeVarintLoop_cont_end decodeVarintLoop_cont_step decodeVarintLoop_stop
   deserAfterVarint exists_chunk32Bytes_of_length_32 fold_messageErrorAt_region
   fromBytes_expose_byte fromBytes_expose_chunk32 fromBytes_unexpose_byte
   fromBytes_unexpose_chunk32 hiByte index_gt65535_of_lsr16 index_le65535_of_lsr16
   messageDeserializeStackX messageResultAt msgDeserFramePad msgDeserSavedAt msgDeserScratchAt
   msgDeser_stack_restore rawOkOutAt rawOkOutAt_entails_mkChunkMsg rawOutBufAt
   rawOutBufAt_entails_err_split rest2_ge32_of_not_ult rest2_lt32_of_ult sbfm8Val
   sbfm8_bit31_nz sbfm8_bit31_z shiftWord shiftWord_byte_swap sp_sub_144_aligned unshiftWord
   varint_cs_false varint_cs_true varint_orr_lsl_eq varint_pre_csel_eq varint_pre_eq_zero
   varint_pre_ne_zero)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_351 blkPl_351)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget (messageDeserializeSpecX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem align_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

private theorem sepWP_seq_vmPreserved {prog : Program} {mid target : BitVec 64}
    {s0 s_cur : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h0 : VmPreserved s0 s_cur)
    (h1 : SepWP prog mid s_cur P (fun sm Pm => VmPreserved s_cur sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s0 sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s_cur P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hvm1, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun (h0.trans hvm1) hQ)

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

set_option maxHeartbeats 800000 in
private theorem step_err_tail_core [LibsignalPlacement] (P_poly : PolyApi)
    (hooks : String → Option (State → State))
    (Pool : SepProp) (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P : SepProp)
    (herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hpc : s.pc = (blkPl_351).base + 664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      Pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) ∗
          (call.fromPtr ↦ₛ call.fromBytes) ∗
          Pool ∗
          stackAt s0.sp messageDeserializeStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP
  by_vm_steps (
    refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
      (by sep_focus) ?_
    unfold msgDeserSavedAt
    wp_steps
    rw [herr]
    dsimp only [messageResultAt]
    refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
    refine SepWP.fold (msgDeser_stack_restore s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold msgDeserSavedAt
      sep_focus) ?_
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  )

/-- Shared `Err(.msgDecode)` epilogue (`+664..+696`, 9 instructions) on `Block 351`. -/
theorem step_err_tail_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
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
    (hpc : s.pc = (blkPl_351).base + 664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim (M.stepEvents evs st) s ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post :=
  sepWP_msgDeser_finish hevs hpost
    (step_err_tail_core P_poly hooks (A.pool lim (M.stepEvents evs st) s) call
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P
      herr hpc hrun hsp hs0A htr hx0 hcs hP)

set_option maxHeartbeats 1200000 in
private theorem step_ok_tail_core [LibsignalPlacement] (P_poly : PolyApi)
    (hooks : String → Option (State → State))
    (Pool : SepProp) (call : MessageDeserializeCall)
    (tag : BitVec 8) (idxReg : BitVec 64) (c2 : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P : SepProp)
    (hok : rawOkOutAt call.out call.epoch tag st0 st1 c2 st3 st4 st5 st6 (idxReg.truncate 16) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes))
    (hpc : s.pc = (blkPl_351).base + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = idxReg)
    (hx10 : s.readReg64 .x10 = c2.zeroExtend 64)
    (hx29 : s.readReg64 .fp = s0.sp - 48#64)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      Pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) ∗
          (call.fromPtr ↦ₛ call.fromBytes) ∗
          Pool ∗
          stackAt s0.sp messageDeserializeStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
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
  have hfold_ok :
      ((call.out ↦₆₄ call.epoch) ∗ ((call.out + 8#64) ↦₈ tag) ∗ ((call.out + 9#64) ↦₈ 1#8) ∗
        ((call.out + 10#64) ↦₃₂ st0) ∗ ((call.out + 14#64) ↦₁₆ st1) ∗ ((call.out + 16#64) ↦₈ c2) ∗
        ((call.out + 17#64) ↦₆₄ st3) ∗ ((call.out + 25#64) ↦₈ st4) ∗
        ((call.out + 26#64) ↦₆₄ st5) ∗ ((call.out + 34#64) ↦₆₄ st6) ∗
        ((call.out + 42#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 idxReg)) ∗
        memRegion (call.out + 44#64) 4) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) := by
    have htr16 : BitVec.truncate 16 (BitVec.truncate 32 idxReg) = idxReg.truncate 16 :=
      BitVec.setWidth_setWidth_of_le (x := idxReg) (by decide)
    rw [htr16]
    refine Entails.trans ?_ hok
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
    refine SepWP.fold hfold_ok (by sep_focus) ?_
    refine SepWP.fold (msgDeser_stack_restore s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
      unfold msgDeserScratchAt msgDeserSavedAt
      sep_focus) ?_
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  )

/-- Shared `Ok` epilogue (`+588..+660`, 19 instructions) on `Block 351`. -/
theorem step_ok_tail_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (call : MessageDeserializeCall)
    (tag : BitVec 8) (idxReg : BitVec 64) (c2 : BitVec 8)
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
    (hok : rawOkOutAt call.out call.epoch tag st0 st1 c2 st3 st4 st5 st6 (idxReg.truncate 16) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes))
    (hpc : s.pc = (blkPl_351).base + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = idxReg)
    (hx10 : s.readReg64 .x10 = c2.zeroExtend 64)
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
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post :=
  sepWP_msgDeser_finish hevs hpost
    (step_ok_tail_core P_poly hooks (A.pool lim (M.stepEvents evs st) s) call
      tag idxReg c2 o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P
      hok hpc hrun hsp hs0A htr hx0 hx1 hx8 hx9 hx10 hx29 hcs hP)

set_option maxHeartbeats 1600000 in
/-- Post-varint length & `u16` range check plus 32-byte chunk copy (`+524..+588`) on `Block
    351`. -/
theorem step_after_varint_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (call : MessageDeserializeCall)
    (tag : BitVec 8) (pre₁ rest2 : List (BitVec 8)) (index : BitVec 64)
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
    (htag : tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8)
    (hsplit : call.fromBytes = (tag :: pre₁) ++ rest2)
    (hlen_lt : call.fromBytes.length < 2 ^ 63)
    (hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
      deserAfterVarint P_poly call.epoch tag (some (index, rest2)))
    (hpc : s.pc = (blkPl_351).base + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx2 : s.readReg64 .x2 = call.fromPtr)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = index)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pre₁.length)
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
  have herr_tail := step_err_tail_core P_poly hooks (A.pool lim (M.stepEvents evs st) s) call
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  have hfrom_len : call.fromBytes.length = 1 + pre₁.length + rest2.length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hlen_lt' : (tag :: (pre₁ ++ rest2)).length < 2 ^ 63 := by
    have : call.fromBytes = tag :: (pre₁ ++ rest2) := by simpa using hsplit
    rwa [← this]
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  wp_steps 3
  wp_if hhi
  · have hlt32 : rest2.length < 32 := rest2_lt32_of_ult hlen_lt' hhi
    have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
      rw [hdeser]; unfold deserAfterVarint; simp [hlt32]
    refine SepWP.mono (herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm])
      (by simp [hx0, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
       by simp [hvregs, arm64_norm]⟩ hP) ?_
    intro sf Pf _ _ ⟨hvm2, hrest⟩
    exact ⟨(by simp [arm64_norm] : VmPreserved s _).trans hvm2, hrest⟩
  · have hge32 : ¬ rest2.length < 32 := rest2_ge32_of_not_ult hlen_lt' hhi
    clear hhi
    wp_steps 2
    wp_if hcbnz
    · have hgt16 : index.toNat > 65535 := index_gt65535_of_lsr16 hcbnz
      have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
        rw [hdeser]; unfold deserAfterVarint; simp [hge32, hgt16]
      refine SepWP.mono (herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm])
        (by simp [hx0, arm64_norm])
        ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
         by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
         by simp [hvregs, arm64_norm]⟩ hP) ?_
      intro sf Pf _ _ ⟨hvm2, hrest⟩
      exact ⟨(by simp [arm64_norm] : VmPreserved s _).trans hvm2, hrest⟩
    · have hle16 : ¬ index.toNat > 65535 := index_le65535_of_lsr16 hcbnz
      clear hcbnz herr_tail
      have hlen32 : (rest2.take 32).length = 32 := by rw [List.length_take]; omega
      obtain ⟨c0, c1, c2, c3, c4, c5, c6, htake⟩ :=
        exists_chunk32Bytes_of_length_32 hlen32
      have hok : rawOkOutAt call.out call.epoch tag c0 c1 c2 c3 c4 c5 c6 (index.truncate 16) ⊢
          messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) := by
        rw [hdeser]
        unfold deserAfterVarint
        simp only [hge32, ↓reduceDIte, hle16, ↓reduceIte]
        exact rawOkOutAt_entails_mkChunkMsg P_poly hPoly call.out call.epoch tag (index.truncate 16)
          c0 c1 c2 c3 c4 c5 c6 ⟨rest2.take 32, hlen32⟩ htake htag
      have hok_tail := step_ok_tail_core P_poly hooks (A.pool lim (M.stepEvents evs st) s) call
        tag index c2 o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 c3 c4 c5 c6 c0 c1 fb0 f50 f58 s0
      have hexp := fromBytes_expose_chunk32 call.fromPtr call.fromBytes pre₁ rest2
        tag c0 c1 c2 c3 c4 c5 c6 hsplit htake
      have hunexp := fromBytes_unexpose_chunk32 call.fromPtr call.fromBytes pre₁ rest2
        tag c0 c1 c2 c3 c4 c5 c6 hsplit htake
      let x10_ptr := call.fromPtr + (BitVec.ofNat 64 pre₁.length - 1#64)
      have hswap_in : (((x10_ptr + 17#64) ↦₈ c4) ∗ ((x10_ptr + 18#64) ↦₆₄ c5)) ⊢
          ((x10_ptr + 17#64) ↦₆₄ shiftWord c4 c5) ∗ ((x10_ptr + 25#64) ↦₈ hiByte c5) := by
        have h1 := byte_word64_swap (x10_ptr + 17#64) c4 c5
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
        exact Entails.of_eq h1
      have hunswap_in : (((x10_ptr + 17#64) ↦₆₄ shiftWord c4 c5) ∗ ((x10_ptr + 25#64) ↦₈ hiByte c5)) ⊢
          ((x10_ptr + 17#64) ↦₈ c4) ∗ ((x10_ptr + 18#64) ↦₆₄ c5) := by
        have h1 := (byte_word64_swap (x10_ptr + 17#64) c4 c5).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
        exact Entails.of_eq h1
      have hswap_st : (((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5)) ⊢
          ((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5) := by
        have h1 := byte_word64_swap (s0.sp - 104#64) st4 st5
        have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
        have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
        rw [ha1, ha8] at h1
        exact Entails.of_eq h1
      have hunswap_st : (((s0.sp - 104#64) ↦₆₄ shiftWord c4 c5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5)) ⊢
          ((s0.sp - 104#64) ↦₈ c4) ∗ ((s0.sp - 103#64) ↦₆₄ unshiftWord (shiftWord c4 c5) (hiByte st5)) := by
        have h1 := shiftWord_byte_swap (s0.sp - 104#64) c4 c5 (hiByte st5)
        have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
        have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
        rw [ha1, ha8] at h1
        exact Entails.of_eq h1
      subst hP
      let P_mid : SepProp :=
        (call.fromPtr ↦ₛ call.fromBytes) ∗
        rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
        A.pool lim (M.stepEvents evs st) s ∗
        msgDeserFramePad s0.sp ∗
        msgDeserScratchAt s0.sp f08 f10 f18 c3 c4 c5 c6 c0 c1 fb0 f50 f58 ∗
        msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
      clear hok_tail
      refine sepWP_seq_vmPreserved (s0 := s) (mid := (blkPl_351).base + 588#64) (P_mid := P_mid)
        (Q := fun sm =>
          sm.sp = s0.sp - 144#64 ∧
          sm.trace = s0.trace ∧
          sm.readReg64 .x0 = call.out ∧
          sm.readReg64 .x1 = call.epoch ∧
          sm.readReg64 .x8 = tag.zeroExtend 64 ∧
          sm.readReg64 .x9 = index ∧
          sm.readReg64 .x10 = c2.zeroExtend 64 ∧
          sm.readReg64 .fp = s0.sp - 48#64 ∧
          DeserHighCalleeSaved s0 sm)
        (by simp [arm64_norm]) ?_ ?_
      · by_vm_steps (
          wp_steps 2
          refine SepWP.fold hexp (by sep_focus) ?_
          unfold chunk32AtX10
          wp_steps 2
          refine SepWP.fold hswap_in (by sep_focus) ?_
          wp_steps 1
          refine SepWP.fold hunswap_in (by sep_focus) ?_
          wp_steps 2
          refine SepWP.fold hunexp (by
            unfold chunk32AtX10
            sep_focus) ?_
          unfold msgDeserScratchAt
          wp_steps 2
          refine SepWP.fold hswap_st (by sep_focus) ?_
          wp_steps 1
          refine SepWP.fold hunswap_st (by sep_focus) ?_
          wp_steps 1
          dsimp only [P_mid, msgDeserScratchAt, DeserHighCalleeSaved]
          refine align_pre (by sep_ac_rfl) ?_
          wp_done
        )
      · intro sm hpcm hrunm hvm1 ⟨hspm, htrm, hx0m, hx1m, hx8m, hx9m, hx10m, hx29m, hcsm⟩
        refine SepWP.mono
          (step_ok_tail_core P_poly hooks (A.pool lim (M.stepEvents evs st) s) call
            tag index c2 o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
            f08 f10 f18 c3 c4 c5 c6 c0 c1 fb0 f50 f58 s0 sm P_mid
            hok hpcm hrunm hspm hs0A htrm hx0m hx1m hx8m hx9m hx10m hx29m hcsm rfl) ?_
        intro sf Pf _ _ ⟨hvm2, hrest⟩
        exact ⟨hvm1.trans hvm2, hrest⟩

theorem step_at_520_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (call : MessageDeserializeCall)
    (tag b : BitVec 8) (pre₁' rest2 : List (BitVec 8)) (index : BitVec 64)
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
    (htag : tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8)
    (hsplit : call.fromBytes = (tag :: pre₁') ++ rest2)
    (hlen_lt : call.fromBytes.length < 2 ^ 63)
    (herr_case : b &&& 0x80#8 ≠ 0#8 →
      Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hok_case : b &&& 0x80#8 = 0#8 →
      Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch tag (some (index, rest2)))
    (hpc : s.pc = (blkPl_351).base + 520#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx2 : s.readReg64 .x2 = call.fromPtr)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = index)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pre₁'.length)
    (hx14 : s.readReg64 .x14 = sbfm8Val b)
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
  have herr_tail := step_err_tail_placed P_poly hooks A lim st evs hevs call
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  have hafter := step_after_varint_placed P_poly hPoly hooks A lim st evs hevs call
    tag pre₁' rest2 index
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  wp_steps 1
  wp_if htb
  · have hb : b &&& 0x80#8 ≠ 0#8 := sbfm8_bit31_nz htb
    exact herr_tail _ P R post hpost (herr_case hb)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
       by simp [hvregs, arm64_norm]⟩
      (by simp only [hP, arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])
  · have hb : b &&& 0x80#8 = 0#8 := sbfm8_bit31_z htb
    exact hafter _ P R post hpost htag hsplit hlen_lt (hok_case hb)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
      (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]) (by simp [hx29, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
       by simp [hvregs, arm64_norm]⟩
      (by simp only [hP, arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])

abbrev VarintLoopStmtPlaced [LibsignalPlacement] {M : AllocCostModel} (loopOff : BitVec 64)
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) : Prop :=
  FreeOnlyEvs evs →
  (post = fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) →
  (tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8) →
  call.fromBytes.length < 2 ^ 63 →
  s0.spAligned = true →
  ∀ (rest1 pre₁ : List (BitVec 8)) (out : BitVec 64) (s : State) (P : SepProp),
    rest1 ≠ [] →
    pre₁.length < 10 →
    call.fromBytes = (tag :: pre₁) ++ rest1 →
    Message.deserialize P_poly call.epoch call.fromBytes =
      deserAfterVarint P_poly call.epoch tag (decodeVarintLoop pre₁.length out rest1) →
    s.pc = (blkPl_351).base + loopOff →
    s.status = .Running →
    s.sp = s0.sp - 144#64 →
    s.trace = s0.trace →
    s.readReg64 .x0 = call.out →
    s.readReg64 .x1 = call.epoch →
    s.readReg64 .x2 = call.fromPtr →
    s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length →
    s.readReg64 .x8 = tag.zeroExtend 64 →
    s.readReg64 .x9 = out →
    s.readReg64 .x10 = BitVec.ofNat 64 pre₁.length →
    s.readReg64 .x11 = BitVec.ofNat 64 (7 * pre₁.length) →
    s.readReg64 .x12 = BitVec.ofNat 64 (min (pre₁.length + rest1.length) 10) →
    s.readReg64 .x13 = call.fromPtr + 1#64 →
    s.readReg64 .fp = s0.sp - 48#64 →
    DeserHighCalleeSaved s0 s →
    P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim (M.stepEvents evs st) s ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) →
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post

set_option hygiene false in
local macro "prove_varint_loop_placed" tail_step:tactic : tactic => `(tactic| (
  intro hevs hpost htag hlen_lt hs0A rest1 pre₁ out s P hne hj hsplit hdeser
    hpc hrun hsp htr hx0 hx1 hx2 hx3 hx8 hx9 hx10 hx11 hx12 hx13 hx29 hcs hP
  induction rest1 generalizing pre₁ out s P with
  | nil => exact absurd rfl hne
  | cons b rest2 ih =>
    clear hne
    have hlen_rest : pre₁.length + (b :: rest2).length = pre₁.length + 1 + rest2.length := by
      simp only [List.length_cons]; omega
    rw [hlen_rest] at hx12
    have hsplit' : call.fromBytes = (tag :: (pre₁ ++ [b])) ++ rest2 := by
      simp [hsplit]
    have hlen_pre1' : (pre₁ ++ [b]).length = pre₁.length + 1 := by simp
    have h10_add : BitVec.ofNat 64 pre₁.length + 1#64 = BitVec.ofNat 64 (pre₁ ++ [b]).length := by
      rw [hlen_pre1']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h11_add : BitVec.ofNat 64 (7 * pre₁.length) + 7#64 = BitVec.ofNat 64 (7 * (pre₁ ++ [b]).length) := by
      rw [hlen_pre1']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    let out' := out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * pre₁.length))
    have horr := varint_orr_lsl_eq pre₁.length hj out b
    have h520 := step_at_520_placed P_poly hPoly hooks A lim st evs hevs call tag b (pre₁ ++ [b]) rest2 out'
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
    have haddr_b : call.fromPtr + (1#64 + BitVec.ofNat 64 pre₁.length) =
        call.fromPtr + BitVec.ofNat 64 (tag :: pre₁).length := by
      simp only [List.length_cons]; bv_omega
    have hexp := fromBytes_expose_byte call.fromPtr call.fromBytes (tag :: pre₁) rest2 b
      (call.fromPtr + (1#64 + BitVec.ofNat 64 pre₁.length)) hsplit haddr_b
    have hunexp := fromBytes_unexpose_byte call.fromPtr call.fromBytes (tag :: pre₁) rest2 b
      (call.fromPtr + (1#64 + BitVec.ofNat 64 pre₁.length)) hsplit haddr_b
    rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
    subst hP
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps 1
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_steps 7
    wp_if hcs_br
    · have hend : min (pre₁.length + 1 + rest2.length) 10 ≤ pre₁.length + 1 :=
        varint_cs_true hj hcs_br
      have herr_case : b &&& 0x80#8 ≠ 0#8 →
          Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
        intro hb; rw [hdeser, decodeVarintLoop_cont_end pre₁.length out b rest2 hj hb hend]; rfl
      have hok_case : b &&& 0x80#8 = 0#8 →
          Message.deserialize P_poly call.epoch call.fromBytes =
            deserAfterVarint P_poly call.epoch tag (some (out', rest2)) := by
        intro hb; rw [hdeser, decodeVarintLoop_stop pre₁.length out b rest2 hb]
      exact h520 _ _ R post hpost htag hsplit' hlen_lt herr_case hok_case
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
        (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
        (by simp [out', arm64_norm]) (by simp [arm64_norm])
        (by simp [sbfm8Val, arm64_norm]) (by simp [hx29, arm64_norm])
        ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
         by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
         by simp [hvregs, arm64_norm]⟩
        (by simp only [arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])
    · have hmore : pre₁.length + 1 < min (pre₁.length + 1 + rest2.length) 10 :=
        varint_cs_false hj hcs_br
      clear hcs_br
      have hj1 : pre₁.length + 1 < 10 := by omega
      have hne2 : rest2 ≠ [] := by
        intro hnil; subst hnil; simp at hmore
      wp_steps 2
      wp_if htb
      · have hb : b &&& 0x80#8 ≠ 0#8 := sbfm8_bit31_nz htb
        have hdeser' : Message.deserialize P_poly call.epoch call.fromBytes =
            deserAfterVarint P_poly call.epoch tag (decodeVarintLoop (pre₁ ++ [b]).length out' rest2) := by
          rw [hdeser, hlen_pre1', decodeVarintLoop_cont_step pre₁.length out b rest2 hj1 hb]
        exact ih (pre₁ ++ [b]) out' _ _ hne2 (by rw [hlen_pre1']; exact hj1) hsplit' hdeser'
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
          (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [out', arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by rw [hlen_pre1']; simp [hx12, arm64_norm])
          (by simp [hx13, arm64_norm]) (by simp [hx29, arm64_norm])
          ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
           by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
           by simp [hvregs, arm64_norm]⟩
          (by simp only [arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])
      · have hb : b &&& 0x80#8 = 0#8 := sbfm8_bit31_z htb
        $tail_step
        have herr_case : b &&& 0x80#8 ≠ 0#8 →
            Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode :=
          fun h => absurd hb h
        have hok_case : b &&& 0x80#8 = 0#8 →
            Message.deserialize P_poly call.epoch call.fromBytes =
              deserAfterVarint P_poly call.epoch tag (some (out', rest2)) := by
          intro _; rw [hdeser, decodeVarintLoop_stop pre₁.length out b rest2 hb]
        exact h520 _ _ R post hpost htag hsplit' hlen_lt herr_case hok_case
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
          (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [out', arm64_norm]) (by simp [arm64_norm])
          (by simp [sbfm8Val, arm64_norm]) (by simp [hx29, arm64_norm])
          ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
           by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
           by simp [hvregs, arm64_norm]⟩
          (by simp only [arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])
))

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_3_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmtPlaced 100#64 P_poly hooks A lim st evs call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop_placed (wp_steps 1)

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_1_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmtPlaced 232#64 P_poly hooks A lim st evs call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop_placed (wp_steps 1)

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_5_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmtPlaced 320#64 P_poly hooks A lim st evs call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop_placed (wp_steps 1)

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_2_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmtPlaced 400#64 P_poly hooks A lim st evs call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop_placed (wp_steps 1)

set_option linter.unusedTactic false in
set_option maxHeartbeats 1600000 in
theorem step_varint_loop_6_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmtPlaced 480#64 P_poly hooks A lim st evs call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop_placed (skip)

abbrev VarintPreStmtPlaced [LibsignalPlacement] {M : AllocCostModel} (preOff : BitVec 64)
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) : Prop :=
  FreeOnlyEvs evs →
  (post = fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) →
  (tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8) →
  call.fromBytes = tag :: rest →
  call.fromBytes.length < 2 ^ 63 →
  Message.deserialize P_poly call.epoch call.fromBytes =
    deserAfterVarint P_poly call.epoch tag (decodeVarintLoop 0 0#64 rest) →
  s.pc = (blkPl_351).base + preOff →
  s.status = .Running →
  s.sp = s0.sp - 144#64 →
  s0.spAligned = true →
  s.trace = s0.trace →
  s.readReg64 .x0 = call.out →
  s.readReg64 .x1 = call.epoch →
  s.readReg64 .x2 = call.fromPtr →
  s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length →
  s.readReg64 .x8 = tag.zeroExtend 64 →
  s.readReg64 .fp = s0.sp - 48#64 →
  DeserHighCalleeSaved s0 s →
  P =
    (call.fromPtr ↦ₛ call.fromBytes) ∗
    rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
    A.pool lim (M.stepEvents evs st) s ∗
    msgDeserFramePad s0.sp ∗
    msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
    msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) →
  SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post

set_option hygiene false in
local macro "prove_varint_pre_placed" loop_thm:ident : tactic => `(tactic| (
  intro hevs hpost htag hsplit0 hlen_lt hdeser0 hpc hrun hsp hs0A htr hx0 hx1 hx2 hx3 hx8 hx29 hcs hP
  have herr_tail := step_err_tail_placed P_poly hooks A lim st evs hevs call
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  have hloop := $loop_thm P_poly hPoly hooks A lim st evs call tag
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post hevs hpost htag hlen_lt hs0A
  have hlen_lt' : (tag :: rest).length < 2 ^ 63 := by rwa [← hsplit0]
  have hcsel := varint_pre_csel_eq hlen_lt'
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  wp_steps 2
  wp_if heq
  · have hnil : rest = [] := varint_pre_eq_zero hlen_lt' heq
    have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
      rw [hdeser0, hnil]; rfl
    exact herr_tail _ P R post hpost herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
       by simp [hvregs, arm64_norm]⟩
      (by simp only [hP, arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])
  · have hne : rest ≠ [] := varint_pre_ne_zero heq
    clear heq herr_tail
    wp_steps 7
    exact hloop rest [] 0#64 _ P hne (by decide) (by simp [hsplit0]) (by simpa using hdeser0)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [hcsel, arm64_norm]) (by simp [hx2, arm64_norm]) (by simp [hx29, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm],
       by simp [hvregs, arm64_norm]⟩
      (by simp only [hP, arm64_norm, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg])
))

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_3_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmtPlaced 64#64 P_poly hooks A lim st evs call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre_placed step_varint_loop_3_placed

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_1_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmtPlaced 196#64 P_poly hooks A lim st evs call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre_placed step_varint_loop_1_placed

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_5_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmtPlaced 284#64 P_poly hooks A lim st evs call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre_placed step_varint_loop_5_placed

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_2_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmtPlaced 364#64 P_poly hooks A lim st evs call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre_placed step_varint_loop_2_placed

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_6_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent)
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmtPlaced 444#64 P_poly hooks A lim st evs call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre_placed step_varint_loop_6_placed

/-- Empty-slice (`from.is_empty()`, `+0: cbz x3, +144`) error return (`+144..+160`, 5 insns) on
    `Block 351`. -/
theorem step_err_empty_placed [LibsignalPlacement] {M : AllocCostModel}
    (P_poly : PolyApi) (hooks : String → Option (State → State))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly M A lim).post (call, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hpc : s.pc = (blkPl_351).base + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hcs : CalleeSavedPreserved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool lim (M.stepEvents evs st) s ∗
      stackAt s0.sp messageDeserializeStackX) :
    SepWP ((blkPC_351).rebase (blkPl_351).base hooks) (s0.readReg64 .lr) s P post := by
  refine sepWP_msgDeser_finish hevs hpost ?_
  rcases hcs with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs⟩
  subst hP
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

end LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.BasePlacedBudget
