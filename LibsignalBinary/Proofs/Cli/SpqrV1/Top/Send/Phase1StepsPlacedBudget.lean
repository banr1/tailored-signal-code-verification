/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 1a Steps for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Threads `VmPreserved` through the `decode_state` `Err(e)` early-return path (`+80 -> s0.lr`)
and `Ok(pq)` header relocation (`+80 -> +156`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (sessionMemcpyRegionSpec sessionMemcpySpec spqrSendResultAt spqrSendStack)
open CryptoVerification.LibsignalSpqrV1 (Error PqRatchetState)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (V1InnerHeapPred decodeStateResultAt none2Cap optProtoPqRatchetInnerAt
   relocOptVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Send
  (bv_add_add_lit1 bv_add_add_lit2 decodeStateResultAt_err_entails_head32_320
   decode_state_err_frame_rejoin err_ret_entails_sendResultAt_none
   fsp_1260_add_18 fsp_1260_add_20 fsp_1260_add_8 fsp_1268_add_8
   fsp_190_add_8 fsp_30_add_20 fsp_30_add_80 fsp_38_add_8
   memRegion_1260_split_190 memRegion_190_split_30_50 memRegion_ret_72_split_err
   ne_none2Cap_add_two_beq_zero_false protoPqRatchetStateAt_entails_split32_16_304
   reassemble_chain_and_inner_after_memcpy relocChainAndInnerAt ret_8_add_8
   spqrSendCalleeStack spqrSendSavedRegs src352_rejoin_1a8_to_1f20)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
  (spqr_send_epilogue_4632_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp] do
    Lean.Attribute.erase nm `arm64_norm
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
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg

/-! ## 1. `VmPreserved`-Strengthened `memcpy` Contract on `spqrSendPlacedProg` -/

/-- Derive `subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionBudgetSpec`
    (carrying `⌜VmPreserved s0 sf⌝`) from `AllocContractsPlaced M A lim ext`. -/
theorem spqrSend_session_memcpy_region_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
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

/-- Plain `sessionMemcpyRegionSpec` weakening of `spqrSend_session_memcpy_region_ok_placed`. -/
theorem spqrSend_session_memcpy_region_plain_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionSpec := by
  refine subroutine_ok_mono (spqrSend_session_memcpy_region_ok_placed hA)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [sessionMemcpyRegionBudgetSpec] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-! ## 2. VM-Preserving `Err(e)` Return Path (`+80 -> s0.lr`) -/

/-- Relocatable VM-preserving `Err(e)` return path after `spqr::decode_state` (`+80 -> s0.lr`):
    writes `spqrSendResultAt A ret none`, rejoins the stack frame, and executes
    `spqr_send_epilogue_4632_placed`, preserving `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
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
    by_vm_steps (
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
      wp_steps
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], ?_,
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      have hframe := decode_state_err_frame_rejoin fsp w1 w2 w3
      have hret := err_ret_entails_sendResultAt_none A ret w1 w2 w3
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 400 ∗
           ((fsp + 400#64) ↦₆₄ w1) ∗
           ((fsp + 408#64) ↦₆₄ w2) ∗
           ((fsp + 416#64) ↦₆₄ w3) ∗
           memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
           ((fsp + 4704#64) ↦₆₄ none2Cap) ∗
           ((fsp + 4712#64) ↦₆₄ w1) ∗
           ((fsp + 4720#64) ↦₆₄ w2) ∗
           ((fsp + 4728#64) ↦₆₄ w3) ∗
           memRegion (fsp + 4736#64) 320 ∗
           memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
          ((ret ↦₆₄ 18446744073709551615#64) ∗
           ((ret + 8#64) ↦₆₄ w1) ∗
           ((ret + 16#64) ↦₆₄ w2) ∗
           ((ret + 24#64) ↦₆₄ w3) ∗
           memRegion (ret + 32#64) 40) ∗
          (stackAt fsp spqrSendCalleeStack ∗
           spqrSendSavedRegs fsp s0 ∗
           Rest) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hframe (sepConj_mono_left hret)) ?_
      exact Entails.of_eq (by sep_ac_rfl))
  · intro s2 P2 hpc2 hrun2 ⟨hvm1, hacp1, hP2, hsp2, htr2, hvregs2⟩
    refine SepWP.weaken_pre hP2 ?_
    have hep := spqr_send_epilogue_4632_placed (ext := ext) s0 s2
      (spqrSendResultAt A ret none ∗ Rest) hsp0_align hpc2 hrun2 hsp2 hvregs2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hvm2, hacp2, hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨hvm1.trans hvm2, hacp1.trans hacp2,
      Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

/-- Pool-threading corollary of `spqr_send_decode_state_err_step_placed`, transporting
    `A.pool lim st s` to `A.pool lim st sf` across `VmPreserved s sf`. -/
theorem spqr_send_decode_state_err_step_placed_pool {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
        (Pf ⊢
          stackAt s0.sp spqrSendStack ∗
          spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim st sf ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have herr := spqr_send_decode_state_err_step_placed (H_inner := H_inner) (A := A.repAlloc)
    (ext := ext) s0 s ret e (A.pool lim st s ∗ Rest) hsp0_align hpc hrun hsp hx19 hx26 hvregs
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono herr ?_)
  intro sf Pf _ _ ⟨hvm, hacp, hPf, hspf, hccf, htrf⟩
  refine ⟨hvm, hacp, ?_, hspf, hccf, htrf⟩
  rw [A.pool_transport lim st s sf hvm]
  exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. VM-Preserving `Ok(pq)` Relocation Step (`+80 -> +156`) -/

private theorem fsp_48_add_32 (fsp : BitVec 64) : (fsp + 48#64) + 32#64 = fsp + 80#64 := by
  bv_omega

private theorem fsp_48_add_48 (fsp : BitVec 64) : (fsp + 48#64) + 48#64 = fsp + 96#64 := by
  bv_omega

private theorem fsp_48_add_128 (fsp : BitVec 64) : (fsp + 48#64) + 128#64 = fsp + 176#64 := by
  bv_omega

/-- Relocatable VM-preserving `Ok(pq)` relocation step from `+80` to `+156`:
    loads the 32-byte header of `pq` into `x23 = w0` and `[sp + 0x190..0x1a8]`,
    checks `w0 ≠ none2Cap`, calls `memcpy(sp + 0x50, sp + 0x1280, 320)` via
    `sessionMemcpyRegionBudgetSpec`, and reassembles `optChainPBAt A.repAlloc (sp + 0x60) pq.chain`
    and `optProtoPqRatchetInnerAt H_inner A.repAlloc (sp + 0xb0) pq.inner` while preserving
    `VmPreserved s sm`. -/
theorem spqr_send_decode_state_ok_to_156_placed {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
          w0 ≠ none2Cap ∧
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
  have hmemcpy_raw : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec :=
    spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, decodeStateResultAt,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
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
      s1.sp = fsp ∧
      s1.readReg64 .x30 = (blkPl_427).base + 156#64 ∧
      s1.readReg64 .x0 = fsp + 80#64 ∧
      s1.readReg64 .x1 = fsp + 4736#64 ∧
      s1.readReg64 .x2 = BitVec.ofNat 64 (bs16 ++ bs304).length ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x20 = fsp + 48#64 ∧
      s1.readReg64 .x23 = w0 ∧
      s1.readReg64 .x26 = fsp + 4704#64 ∧
      s1.trace = s.trace ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s ∧
      (P1 ⊢
        memRegion (fsp + 80#64) (bs16 ++ bs304).length ∗
        ((fsp + 4736#64) ↦ₛ (bs16 ++ bs304)) ∗
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
        (relocChainAndInnerAt H_inner A.repAlloc pq).1 bs304 ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        spqrSendSavedRegs fsp s0 ∗
        Rest))
    ?_ ?_
  · by_vm_steps (
      wp_steps
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hlen_src]; simp only [wp_norm, arm64_norm, BitVec.ofNat_eq_ofNat, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hlen_src]; exact Entails.of_eq (by sep_ac_rfl)⟩)
  · intro s1 P1 hpc1 hrun1
      ⟨hvm1, hsp1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx23_1, hx26_1, htr1, hvregs1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    wp_call hmemcpy_raw (fsp + 80#64, fsp + 4736#64, bs16 ++ bs304)
    have hvm2 : VmPreserved s1 sf := by assumption
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ?_
    refine ⟨hvm1.trans hvm2, w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, ?_,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
    clear hmemcpy_raw hpc hrun hsp hx19 hx21 hx26 hpc1 hrun1 hvm1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      hx19_1 hx20_1 hx23_1 hx26_1 htr1 hvregs1 hvm2
    have hci := reassemble_chain_and_inner_after_memcpy H_inner A.repAlloc (fsp + 48#64) bs16 bs304 pq hl16 hl304
    rw [fsp_48_add_32 fsp, fsp_48_add_48 fsp, fsp_48_add_128 fsp] at hci
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

/-- Pool-threading corollary of `spqr_send_decode_state_ok_to_156_placed`, transporting
    `A.pool lim st s` to `A.pool lim st sm` across `VmPreserved s sm`. -/
theorem spqr_send_decode_state_ok_to_156_placed_pool {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        ∃ w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64,
        ∃ bs16 : List (BitVec 8),
          w0 ≠ none2Cap ∧
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
            A.pool lim st sm ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
            Rest) ∧
          sm.sp = s0.sp - 0x1f80#64 ∧
          sm.readReg64 .x19 = ret ∧
          sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
          sm.readReg64 .x23 = w0 ∧
          sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hok := spqr_send_decode_state_ok_to_156_placed (H_inner := H_inner)
    hA s0 s ret pq (A.pool lim st s ∗ Rest) hsp0_align hpc hrun hsp hx19 hx21 hx26
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hok ?_)
  rintro sm Pm _ _
    ⟨hvm, w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, hPm,
     hspm, hx19m, hx20m, hx23m, hx26m, htrm, hvregsm⟩
  refine ⟨hvm, w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, ?_,
    hspm, hx19m, hx20m, hx23m, hx26m, htrm, hvregsm⟩
  rw [A.pool_transport lim st s sm hvm]
  exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
