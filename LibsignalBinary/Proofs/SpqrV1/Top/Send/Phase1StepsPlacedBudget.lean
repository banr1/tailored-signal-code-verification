/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable `spqr::send::<HookRng>` Phase 1a Steps (Block 124)

Verifies `spqr_send_decode_state_err_step_placed` and `spqr_send_decode_state_ok_to_156_placed`
with `VmPreserved` and `RustCliAllocBudget` pool transport.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Top.Send.Placed
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.LibsignalSpqrV1 (Error PqRatchetState)
open CryptoVerification.LibsignalTripleRatchet
  (sessionMemcpyRegionSpec sessionMemcpySpec spqrSendResultAt spqrSendStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (V1InnerHeapPred decodeStateResultAt optProtoPqRatchetInnerAt
   relocOptVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Send
  (bv_add_add_lit1 bv_add_add_lit2 decodeStateResultAt_err_entails_head32_320
   decode_state_err_frame_rejoin err_ret_entails_sendResultAt_none fsp_1260_add_18
   fsp_1260_add_20 fsp_1260_add_8 fsp_1268_add_8 fsp_190_add_8 fsp_30_add_20 fsp_30_add_80
   fsp_38_add_8 memRegion_1260_split_190 memRegion_190_split_30_50 memRegion_ret_72_split_err
   ne_none2Cap_add_two_beq_zero_false protoPqRatchetStateAt_entails_split32_16_304
   reassemble_chain_and_inner_after_memcpy relocChainAndInnerAt ret_8_add_8
   spqrSendCalleeStack spqrSendPlacedEntry spqrSendPlacedProg spqrSendSavedRegs
   src352_rejoin_1a8_to_1f20)
open CryptoVerification.SpqrV1.Top.Send.Placed (blkPC_124 blkPl_124)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1PlacedBudget (spqr_send_epilogue_4632_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
  CryptoVerification.SpqrV1.Top.DecodeState.none3Cap_add_three_beq_zero
attribute [local arm64_norm, local wp_norm]
  bv_add_add_lit1 bv_add_add_lit2
attribute [local simp, local arm64_norm, local wp_norm]
  fsp_1260_add_8 fsp_1268_add_8 fsp_190_add_8 fsp_38_add_8 ret_8_add_8
  fsp_1260_add_18 fsp_1260_add_20 fsp_30_add_20 fsp_30_add_80

/-! ## Alignment and `AllocCallPreserved` Helpers -/

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg128_pre (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg64_pre (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg32_pre (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

private theorem acp_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem acp_trans {s₀ s₁ s₂ : State}
    (h01 : AllocCallPreserved s₀ s₁) (h12 : AllocCallPreserved s₁ s₂) :
    AllocCallPreserved s₀ s₂ :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

private theorem acp_symm {s₀ s₁ : State} (h : AllocCallPreserved s₀ s₁) :
    AllocCallPreserved s₁ s₀ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm,
   h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

private theorem acp_right_congr {s s₁ s₂ : State} (h : AllocCallPreserved s₁ s₂) :
    AllocCallPreserved s s₂ ↔ AllocCallPreserved s s₁ :=
  ⟨fun h02 => acp_trans h02 (acp_symm h), fun h01 => acp_trans h01 h⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_refl_iff (s : State) : AllocCallPreserved s s ↔ True :=
  ⟨fun _ => trivial, fun _ => acp_refl s⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_setPC (s s' : State) (pc : BitVec 64) :
    AllocCallPreserved s (s'.setPC pc) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_advancePC (s s' : State) :
    AllocCallPreserved s s'.advancePC ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_setPState (s s' : State) (ps : PState) :
    AllocCallPreserved s (s'.setPState ps) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeReg64 (s s' : State) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved s (s'.writeReg64 r v) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl, by cases s'; cases r <;> rfl,
    by cases s'; cases r <;> rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeReg32 (s s' : State) (r : Reg) (v : BitVec 32) :
    AllocCallPreserved s (s'.writeReg32 r v) ↔ AllocCallPreserved s s' :=
  acp_right_writeReg64 s s' r _

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeReg (s s' : State) (w : Width) (r : Reg) (v : BitVec 64) :
    AllocCallPreserved s (s'.writeReg w r v) ↔ AllocCallPreserved s s' :=
  acp_right_writeReg64 s s' r _

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeVReg128 (s s' : State) (i : BitVec 5) (v : BitVec 128) :
    AllocCallPreserved s (s'.writeVReg128 i v) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeVReg64 (s s' : State) (i : BitVec 5) (v : BitVec 64) :
    AllocCallPreserved s (s'.writeVReg64 i v) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_writeVReg32 (s s' : State) (i : BitVec 5) (v : BitVec 32) :
    AllocCallPreserved s (s'.writeVReg32 i v) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem acp_right_applyWriteback (s s' : State) (wb : Option (Reg × BitVec 64)) :
    AllocCallPreserved s (applyWriteback s' wb) ↔ AllocCallPreserved s s' := by
  cases wb with
  | none => rfl
  | some p => exact acp_right_writeReg64 s s' p.1 p.2

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem acp_right_setMem (s s' : State) (m : Memory) :
    AllocCallPreserved s (s'.setMem m) ↔ AllocCallPreserved s s' :=
  acp_right_congr ⟨by cases s'; rfl, by cases s'; rfl, by cases s'; rfl,
    by cases s'; rfl, by cases s'; rfl, by cases s'; rfl, by cases s'; rfl⟩

private theorem align_pre_vm_acp {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ AllocCallPreserved s0 sm ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ AllocCallPreserved s0 sm ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hacp, hPm, hQ⟩ => ⟨htp, hacp, Entails.trans hPm h, hQ⟩

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hPm, hQ⟩ => ⟨htp, Entails.trans hPm h, hQ⟩

variable [LibsignalPlacement]

/-! ## `memcpy` Region Contract on `spqrSendPlacedProg` -/

/-- Derive `subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionBudgetSpec`
    from `AllocContractsPlaced M A lim ext`. -/
theorem spqrSend_session_memcpy_region_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionBudgetSpec := by
  have h0 : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") (sessionMemcpyBudgetSpec 0) :=
    spqr_hook_ok_of_mem (hA.session_memcpy 0)
  refine subroutine_ok_mono h0 ?_ ?_
  · intro ⟨dst, src, srcBytes⟩ R s hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro ⟨dst, src, srcBytes⟩ R s0 sf hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sessionMemcpyBudgetSpec, sessionMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

theorem spqrSend_session_memcpy_region_raw_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionSpec := by
  refine subroutine_ok_mono (spqrSend_session_memcpy_region_ok_placed hA)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [sessionMemcpyRegionBudgetSpec] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-! ## `Err(e)` Return Path After `spqr::decode_state` (`+80 -> s0.lr`) -/

/-- Relocatable `Err(e)` return path after `spqr::decode_state` (`+80 -> s0.lr`) with
    `VmPreserved` and `AllocCallPreserved`: writes `spqrSendResultAt A ret none`, rejoins the stack
    frame, and executes `spqr_send_epilogue_4632_placed`. -/
theorem spqr_send_decode_state_err_step_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (ret : BitVec 64) (e : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        memRegion ret 72 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ spqrSendResultAt A ret none ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine SepWP.seq
    (mid := spqrSendPlacedEntry + 4632#64)
    (Mid := fun sm Pm =>
      VmPreserved s sm ∧
      AllocCallPreserved s sm ∧
      (Pm ⊢
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        (spqrSendResultAt A ret none ∗ Rest)) ∧
      sm.sp = s0.sp - 0x1f80#64 ∧
      sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_right
        (sepConj_mono (memRegion_1260_split_190 fsp)
          (sepConj_mono (decodeStateResultAt_err_entails_head32_320 H_inner A (fsp + 4704#64) e)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion_ret_72_split_err ret))))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro r0
    apply ProofLib.SepWP.exists_left; intro rw8
    apply ProofLib.SepWP.exists_left; intro rw16
    apply ProofLib.SepWP.exists_left; intro rw24
    apply ProofLib.SepWP.exists_left; intro w1
    apply ProofLib.SepWP.exists_left; intro w2
    apply ProofLib.SepWP.exists_left; intro w3
    apply ProofLib.SepWP.exists_left; intro w190
    apply ProofLib.SepWP.exists_left; intro w198
    apply ProofLib.SepWP.exists_left; intro w1a0
    by_vm_steps (
      wp_steps
      refine align_pre_vm_acp ?_ ?_
      · have hframe := decode_state_err_frame_rejoin fsp w1 w2 w3
        have hret := err_ret_entails_sendResultAt_none A ret w1 w2 w3
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 400 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
             ((fsp + 4704#64) ↦₆₄ CryptoVerification.SpqrV1.Top.DecodeState.none2Cap) ∗
             ((fsp + 4712#64) ↦₆₄ w1) ∗
             ((fsp + 4720#64) ↦₆₄ w2) ∗
             ((fsp + 4728#64) ↦₆₄ w3) ∗
             memRegion (fsp + 4736#64) 320 ∗
             memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
            ((ret ↦₆₄ noneCap) ∗
             ((ret + 8#64) ↦₆₄ w1) ∗
             ((ret + 16#64) ↦₆₄ w2) ∗
             ((ret + 24#64) ↦₆₄ w3) ∗
             memRegion (ret + 32#64) 40) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             spqrSendSavedRegs fsp s0 ∗
             Rest) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hframe (sepConj_mono_left hret)) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  · intro s2 P2 hpc2 hrun2 ⟨hvm1, hacp1, hP2, hsp2, htr2, hvregs2⟩
    refine SepWP.weaken_pre hP2 ?_
    have hep := spqr_send_epilogue_4632_placed (ext := ext) s0 s2
      (spqrSendResultAt A ret none ∗ Rest) hsp0_align hpc2 hrun2 hsp2 hvregs2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hvm2, hacp2, hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨hvm1.trans hvm2, acp_trans hacp1 hacp2,
      Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

theorem spqr_send_decode_state_err_step_pool_placed {H_inner : V1InnerHeapPred}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (s0 s : State) (st : M.σ) (ret : BitVec 64) (e : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim st sf ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have herr := spqr_send_decode_state_err_step_placed (H_inner := H_inner) (A := A.repAlloc)
    (ext := ext) s0 s ret e (A.pool lim st s ∗ Rest)
    hsp0_align hpc hrun hsp hx19 hx26 hvregs
  refine SepWP.mono herr ?_
  intro sf Pf _ _ ⟨hvm, hacp, hPf, hsp_f, hcc_f, htr_f⟩
  refine ⟨hvm, hacp, ?_, hsp_f, hcc_f, htr_f⟩
  rw [A.pool_transport lim st s sf hvm]
  exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-! ## `Ok(pq)` Relocation Step (`+80 -> +156`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `Ok(pq)` relocation step from `+80` to `+156` with `VmPreserved`:
    loads the 32-byte header of `pq` into `x23 = w0` and `[sp + 0x190..0x1a8]`,
    checks `w0 ≠ none2Cap`, calls `memcpy(sp + 0x50, sp + 0x1280, 320)` via
    `sessionMemcpyRegionBudgetSpec`, and reassembles
    `optChainPBAt A.repAlloc (sp + 0x60) pq.chain` and
    `optProtoPqRatchetInnerAt H_inner A.repAlloc (sp + 0xb0) pq.inner`. -/
theorem spqr_send_decode_state_ok_to_156_placed {H_inner : V1InnerHeapPred}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (ret : BitVec 64) (pq : PqRatchetState) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 156#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        ∃ w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64,
        ∃ bs16 : List (BitVec 8),
          w0 ≠ CryptoVerification.SpqrV1.Top.DecodeState.none2Cap ∧
          bs16.length = 16 ∧
          (Pm ⊢
            stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
            (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
            (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
            (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
            (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
            (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
            (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
            memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
            (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
              ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
            Rest) ∧
          sm.sp = s0.sp - 0x1f80#64 ∧
          sm.readReg64 .x19 = ret ∧
          sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
          sm.readReg64 .x23 = w0 ∧
          sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hmemcpy_flat : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy")
      { pre := memcpyRegionSpec.pre
        post := fun (dst, src, bs) s0 sf =>
          ⌜VmPreserved s0 sf ∧ sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
            (dst ↦ₛ bs) ∗ (src ↦ₛ bs) } := by
    refine subroutine_ok_mono (spqrSend_session_memcpy_region_ok_placed hA)
      (fun _ _ _ hp => hp) (fun ⟨dst, src, bs⟩ R s0 sf hq => ?_)
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hvm, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hvm, hq.1.1, hq.1.2⟩, hq.2⟩
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, decodeStateResultAt, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy_flat ⊢
  generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx21 hx26 ⊢
  refine SepWP.weaken_pre
    (sepConj_mono_right
      (sepConj_mono
        (Entails.trans (memRegion_1260_split_190 fsp)
          (Entails.sepExists_elim fun w190 => Entails.sepExists_elim fun w198 => Entails.sepExists_elim fun w1a0 =>
            Entails.sepExists_right w190 (Entails.sepExists_right w198 (Entails.sepExists_right w1a0
              (sepConj_mono_left (memRegion_190_split_30_50 fsp))))))
        (sepConj_mono_left (protoPqRatchetStateAt_entails_split32_16_304 H_inner A.repAlloc (fsp + 4704#64) pq)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro bs16
  apply ProofLib.SepWP.exists_left; intro bs304
  apply ProofLib.SepWP.exists_left; intro w190
  apply ProofLib.SepWP.exists_left; intro w198
  apply ProofLib.SepWP.exists_left; intro w1a0
  apply ProofLib.SepWP.exists_left; intro w30
  apply ProofLib.SepWP.exists_left; intro w38
  apply ProofLib.SepWP.exists_left; intro w40
  apply ProofLib.SepWP.exists_left; intro w48
  wp_focus_pure; rintro ⟨hw0, hl16, hl304⟩
  have hne2 := ne_none2Cap_add_two_beq_zero_false hw0
  have hlen_src : (bs16 ++ bs304).length = 320 := by rw [List.length_append, hl16, hl304]
  have hlen_lt64 : (bs16 ++ bs304).length < 2 ^ 64 := by rw [hlen_src]; decide
  refine SepWP.seq
    (mid := lsρ "memcpy")
    (Mid := fun s1 P1 =>
      VmPreserved s s1 ∧
      (P1 ⊢
        memRegion (fsp + 80#64) 320 ∗
        ((fsp + 4736#64) ↦ₛ (bs16 ++ bs304)) ∗
        (relocChainAndInnerAt H_inner A.repAlloc pq).1 bs304 ∗
        memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
        ((fsp + 4704#64) ↦₆₄ w0) ∗
        ((fsp + 4712#64) ↦₆₄ w1) ∗
        ((fsp + 4720#64) ↦₆₄ w2) ∗
        ((fsp + 4728#64) ↦₆₄ w3) ∗
        memRegion (fsp + 5056#64) (0x1f20 - 0x13c0) ∗
        stackAt fsp spqrSendCalleeStack ∗
        memRegion fsp 48 ∗
        ((fsp + 48#64) ↦₆₄ w30) ∗
        ((fsp + 56#64) ↦₆₄ w38) ∗
        ((fsp + 64#64) ↦₆₄ w40) ∗
        ((fsp + 72#64) ↦₆₄ w48) ∗
        ((fsp + 400#64) ↦₆₄ w1) ∗
        ((fsp + 408#64) ↦₆₄ w2) ∗
        ((fsp + 416#64) ↦₆₄ w3) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        spqrSendSavedRegs fsp s0 ∗
        Rest) ∧
      s1.sp = fsp ∧
      s1.readReg64 .x0 = fsp + 80#64 ∧
      s1.readReg64 .x1 = fsp + 4736#64 ∧
      s1.readReg64 .x2 = 320#64 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x20 = fsp + 48#64 ∧
      s1.readReg64 .x23 = w0 ∧
      s1.readReg64 .x26 = fsp + 4704#64 ∧
      s1.readReg64 .x30 = (blkPl_124).base + 156#64 ∧
      s1.trace = s.trace ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      refine align_pre_vm ?_ ?_
      · exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  · intro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, hsp1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx23_1, hx26_1, hx30_1, htr1, hvregs1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hs1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
    have hx2_nat : (s1.readReg64 .x2).toNat = (bs16 ++ bs304).length := by
      rw [hx2_1, hlen_src]; rfl
    have hmem320 : memRegion (fsp + 80#64) 320 = memRegion (fsp + 80#64) (bs16 ++ bs304).length := by
      rw [hlen_src]
    wp_conv_pre => rw [hmem320]
    wp_call hmemcpy_flat (fsp + 80#64, fsp + 4736#64, bs16 ++ bs304)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
    refine ⟨hvm1.trans (by assumption), w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, ?_,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
    have hci := reassemble_chain_and_inner_after_memcpy H_inner A.repAlloc (fsp + 48#64) bs16 bs304 pq hl16 hl304
    have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := bv_add_add_lit1 fsp 48 32
    have ha96 : (fsp + 48#64) + 48#64 = fsp + 96#64 := bv_add_add_lit1 fsp 48 48
    have ha176 : (fsp + 48#64) + 128#64 = fsp + 176#64 := bv_add_add_lit1 fsp 48 128
    rw [ha80, ha96, ha176] at hci
    have hsrc := src352_rejoin_1a8_to_1f20 fsp w0 w1 w2 w3 (bs16 ++ bs304) hlen_src
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((fsp + 80#64) ↦ₛ (bs16 ++ bs304)) ∗ (relocChainAndInnerAt H_inner A.repAlloc pq).1 bs304) ∗
        (memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
         ((fsp + 4704#64) ↦₆₄ w0) ∗
         ((fsp + 4712#64) ↦₆₄ w1) ∗
         ((fsp + 4720#64) ↦₆₄ w2) ∗
         ((fsp + 4728#64) ↦₆₄ w3) ∗
         ((fsp + 4736#64) ↦ₛ (bs16 ++ bs304)) ∗
         memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
        (stackAt fsp spqrSendCalleeStack ∗
         memRegion fsp 48 ∗
         ((fsp + 48#64) ↦₆₄ w30) ∗
         ((fsp + 56#64) ↦₆₄ w38) ∗
         ((fsp + 64#64) ↦₆₄ w40) ∗
         ((fsp + 72#64) ↦₆₄ w48) ∗
         ((fsp + 400#64) ↦₆₄ w1) ∗
         ((fsp + 408#64) ↦₆₄ w2) ∗
         ((fsp + 416#64) ↦₆₄ w3) ∗
         (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
           ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
         spqrSendSavedRegs fsp s0 ∗
         Rest) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hci (sepConj_mono_left hsrc)) ?_
    exact Entails.of_eq (by sep_ac_rfl)

theorem spqr_send_decode_state_ok_to_156_pool_placed {H_inner : V1InnerHeapPred}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (st : M.σ) (ret : BitVec 64) (pq : PqRatchetState) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 156#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗
        Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        ∃ w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64,
        ∃ bs16 : List (BitVec 8),
          w0 ≠ CryptoVerification.SpqrV1.Top.DecodeState.none2Cap ∧
          bs16.length = 16 ∧
          (Pm ⊢
            stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
            (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
            (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
            (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
            (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
            (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
            (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
            memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
            (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
              ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
            A.pool lim st sm ∗
            Rest) ∧
          sm.sp = s0.sp - 0x1f80#64 ∧
          sm.readReg64 .x19 = ret ∧
          sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
          sm.readReg64 .x23 = w0 ∧
          sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have h156 := spqr_send_decode_state_ok_to_156_placed (H_inner := H_inner) hA s0 s ret pq
    (A.pool lim st s ∗ Rest) hsp0_align hpc hrun hsp hx19 hx21 hx26
  refine SepWP.mono h156 ?_
  rintro sm Pm _ _ ⟨hvm, w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, hPm,
    hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩
  refine ⟨hvm, w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, ?_,
    hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩
  rw [A.pool_transport lim st s sm hvm]
  exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlacedBudget
