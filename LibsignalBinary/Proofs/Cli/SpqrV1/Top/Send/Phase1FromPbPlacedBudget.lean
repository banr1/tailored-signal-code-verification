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
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 1b: `pq.inner` Unpack (`+156`, Block `427`)

Threads `RustCliAllocBudget` and `VmPreserved` through the `pq.inner = none` early-return path
(`+156 -> s0.lr`) and `pq.inner = some (.v1 v1)` relocation step (`+156 -> +224`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded spqrSendResultAt spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (ChainPB V1State VersionNegotiationPB)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (align_pre)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (V1InnerHeapPred none3Cap optProtoPqRatchetInnerAt optVersionNegotiationPBTailAt
   relocOptVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Send
  (bv_add_add_lit1 bv_add_add_lit2 empty_ok_sendResult_entails inner_none_b0_rejoin
   memRegion_rejoin_30_48 memRegion_sendResult_split_56 ne_none3Cap_add_three_beq_zero_false
   ne_none3Cap_add_three_bne_zero_true none3Cap_add_three_beq_zero
   optProtoInnerStateAt_expose_head optProtoInnerStateAt_unexpose_head
   optProtoInnerStateHeadRest optVersionNegotiationPBTail_cleanup_entails
   reassemble_optVersionNegotiationPBTail_raw rejoin_190_to_1f20
   slt_one_false_iff slt_one_true_iff spqrSendCalleeStack spqrSendSavedRegs)
open CryptoVerification.Cli.SpqrV1.Top.Send (seq_lscro)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
  (seq_vm_lscro spqr_send_chain_drop_epilogue_4608_placed
   spqr_send_vn_chain_drop_epilogue_904_placed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)

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
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_add_add_lit1 bv_add_add_lit2
attribute [local simp, local arm64_norm, local wp_norm]
  none3Cap_add_three_beq_zero
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg

/-! ## 1. Re-Export of `seq_lscro` -/

export CryptoVerification.Cli.SpqrV1.Top.Send (seq_lscro)

/-! ## 2. Budget-Threaded `pq.inner = none` Path (`+156 -> s0.lr`) -/

/-- Budget-threaded relocatable `pq.inner = none` path from `+156` to `s0.lr`:
    loads `[sp + 0xb0] = none3Cap`, finishes relocating `pq.versionNegotiation` to `sp + 0x30`,
    writes `Ok(Send { state: [], msg: [], key: None })` to `*ret`, and drops
    `pq.versionNegotiation` and `pq.chain` before returning, emitting `FreeOnlyEvs evs`. -/
theorem spqr_send_inner_none_step_placed {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB)
    (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hlen16 : bs16.length = 16)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢
            spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp spqrSendStack ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  by_cases hslt : BitVec.slt w0 1#64 = true
  · have hge_false := slt_one_true_iff hslt
    refine seq_vm_lscro hcrl
      (mid := spqrSendPlacedEntry + 4608#64)
      (P_mid :=
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗
        (spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗ Rest))
      (Q := fun sm =>
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 0x1f80#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoPqRatchetInnerAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 ⊢
      by_vm_steps (
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left (memRegion_sendResult_split_56 ret)))))))))))))))) ?_
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply ProofLib.SepWP.exists_left; intro r0
        apply ProofLib.SepWP.exists_left; intro r8
        apply ProofLib.SepWP.exists_left; intro r16
        apply ProofLib.SepWP.exists_left; intro r24
        apply ProofLib.SepWP.exists_left; intro r32
        apply ProofLib.SepWP.exists_left; intro r40
        apply ProofLib.SepWP.exists_left; intro r48
        wp_steps
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *], ?_,
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *]⟩
        have hvn_raw := reassemble_optVersionNegotiationPBTail_raw A.repAlloc (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
        have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
        have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
        have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
        have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
        rw [ha56, ha64, ha72, ha80] at hvn_raw
        have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A.repAlloc (fsp + 48#64) w0 w1 vn
        rw [ha56, ha64, hslt] at hvn_drop
        simp only [↓reduceIte] at hvn_drop
        have hvn48 := Entails.trans hvn_raw hvn_drop
        have h60 : memRegion fsp 48 ∗ memRegion (fsp + 48#64) 48 ⊢ memRegion fsp 96 := by
          rw [memRegion_rejoin_30_48 fsp]
          exact Entails.refl _
        have hb0 := inner_none_b0_rejoin fsp w1 w2 w3
        have hret := empty_ok_sendResult_entails A.repAlloc ret
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 48 ∗
             (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
              ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
              ((fsp + 80#64) ↦ₛ bs16) ∗
              (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 vn).1
                ((unpack64 w2 ++ unpack64 w3) ++ bs16))) ∗
            (((fsp + 176#64) ↦₆₄ none3Cap) ∗
             memRegion (fsp + 184#64) 216 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
            ((ret ↦₆₄ 0#64) ∗
             ((ret + 8#64) ↦₆₄ 1#64) ∗
             ((ret + 16#64) ↦₆₄ 0#64) ∗
             ((ret + 24#64) ↦₆₄ 0#64) ∗
             ((ret + 32#64) ↦₆₄ 1#64) ∗
             ((ret + 40#64) ↦₆₄ 0#64) ∗
             ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion (ret + 56#64) 16) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             optChainPBAt A.repAlloc (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by sep_ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hvn48) h60)
            (sepConj_mono hb0 (sepConj_mono_left hret))) ?_
        exact Entails.of_eq (by sep_ac_rfl))
    · intro s2 hpc2 hrun2 hcrl2 hvm2 ⟨hacp2, hsp2, htr2, hvregs2⟩
      rw [← A.pool_transport lim st s s2 hvm2]
      have hep := spqr_send_chain_drop_epilogue_4608_placed hdropChain s0 s2 st chain
        (spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗ Rest)
        hcrl2 hsp0_align hpc2 hrun2 hsp2 hvregs2
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨evs, hevs, hacp_f, hPf, hsp_f, hcc_f, htr_f⟩
      exact ⟨evs, hevs, hacp2.trans hacp_f,
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩
  · have hslt_f : BitVec.slt w0 1#64 = false := Bool.eq_false_iff.mpr hslt
    have hge_true := slt_one_false_iff hslt_f
    refine seq_lscro hcrl (mid := spqrSendPlacedEntry + 904#64)
      (Mid := fun s1 P1 =>
        VmPreserved s s1 ∧
        AllocCallPreserved s s1 ∧
        0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
          A.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim st s ∗
          (spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗ Rest)) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.trace = s.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoPqRatchetInnerAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 ⊢
      have hvn_raw := reassemble_optVersionNegotiationPBTail_raw A.repAlloc (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
      have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
      have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
      have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
      have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
      rw [ha56, ha64, ha72, ha80] at hvn_raw
      have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A.repAlloc (fsp + 48#64) w0 w1 vn
      rw [ha56, ha64, hslt_f] at hvn_drop
      simp only [Bool.false_eq_true, ↓reduceIte] at hvn_drop
      dsimp only [RustCliAllocBudget.repAlloc] at hvn_drop
      by_vm_steps (
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left (memRegion_sendResult_split_56 ret)))))))))))))))) ?_
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply ProofLib.SepWP.exists_left; intro r0
        apply ProofLib.SepWP.exists_left; intro r8
        apply ProofLib.SepWP.exists_left; intro r16
        apply ProofLib.SepWP.exists_left; intro r24
        apply ProofLib.SepWP.exists_left; intro r32
        apply ProofLib.SepWP.exists_left; intro r40
        apply ProofLib.SepWP.exists_left; intro r48
        wp_steps
        have hvn_all := Entails.trans hvn_raw hvn_drop
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ =
              (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
               ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
               ((fsp + 80#64) ↦ₛ bs16) ∗
               (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 vn).1
                 ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
              (stackAt fsp spqrSendCalleeStack ∗
               memRegion fsp 48 ∗
               optChainPBAt A.repAlloc (fsp + 96#64) chain ∗
               ((fsp + 176#64) ↦₆₄ none3Cap) ∗
               memRegion (fsp + 184#64) 216 ∗
               ((fsp + 400#64) ↦₆₄ w1) ∗
               ((fsp + 408#64) ↦₆₄ w2) ∗
               ((fsp + 416#64) ↦₆₄ w3) ∗
               memRegion (fsp + 424#64) (0x1f20 - 0x1a8) ∗
               (ret ↦₆₄ 0#64) ∗
               ((ret + 8#64) ↦₆₄ 1#64) ∗
               ((ret + 16#64) ↦₆₄ 0#64) ∗
               ((ret + 24#64) ↦₆₄ 0#64) ∗
               ((ret + 32#64) ↦₆₄ 1#64) ∗
               ((ret + 40#64) ↦₆₄ 0#64) ∗
               ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
               memRegion (ret + 56#64) 16 ∗
               A.pool lim st s ∗
               spqrSendSavedRegs fsp s0 ∗
               Rest) by sep_ac_rfl))
            (sepConj_mono_left hvn_all)) ?_
        wp_focus_pure; rintro ⟨hw0_pos, hw0_lt, hw1_ne⟩
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) ?_
        refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          hw0_pos, hw0_lt, hw1_ne, ?_,
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
        have hb0 := inner_none_b0_rejoin fsp w1 w2 w3
        have hret := empty_ok_sendResult_entails A.repAlloc ret
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 176#64) ↦₆₄ none3Cap) ∗
             memRegion (fsp + 184#64) 216 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
            ((ret ↦₆₄ 0#64) ∗
             ((ret + 8#64) ↦₆₄ 1#64) ∗
             ((ret + 16#64) ↦₆₄ 0#64) ∗
             ((ret + 24#64) ↦₆₄ 0#64) ∗
             ((ret + 32#64) ↦₆₄ 1#64) ∗
             ((ret + 40#64) ↦₆₄ 0#64) ∗
             ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion (ret + 56#64) 16) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 48 ∗
             memRegion (fsp + 48#64) 8 ∗
             ((fsp + 56#64) ↦₆₄ w1) ∗
             memRegion (fsp + 64#64) 32 ∗
             A.live w1 w0.toNat 1 ∗
             memRegion w1 w0.toNat ∗
             optChainPBAt A.repAlloc (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hb0 (sepConj_mono_left hret)) ?_
        exact Entails.of_eq (by sep_ac_rfl))
    · intro s1 P1 hpc1 hrun1 hcrl1
        ⟨hvm1, hacp1, hw0_pos, hw0_lt, hw1_ne, hP1, hsp1, hx23_1, htr1, hvregs1⟩
      rw [← A.pool_transport lim st s s1 hvm1] at hP1
      refine SepWP.weaken_pre hP1 ?_
      have hep := spqr_send_vn_chain_drop_epilogue_904_placed hA hdropChain s0 s1 st w0 w1 chain
        (spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗ Rest)
        hcrl1 hsp0_align hpc1 hrun1 hsp1 hx23_1 hw0_pos hw0_lt hw1_ne hvregs1
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨evs, hevs, hacp_f, hPf, hsp_f, hcc_f, htr_f⟩
      exact ⟨evs, hevs, hacp1.trans hacp_f,
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f.trans htr1⟩

/-! ## 3. VM-Preserving `pq.inner = some (.v1 v1)` Step (`+156 -> +224`) -/

/-- Relocatable VM-preserving `pq.inner = some (.v1 v1)` step (`+156 -> +224`):
    loads `w_in ≠ none3Cap` from `[sp + 0xb0]`, completes the 32-byte relocation of
    `pq.versionNegotiation` into `[sp + 0x30..0x50)`, and branches to `+224`, preserving
    `VmPreserved s sm` and `AllocCallPreserved s sm`. -/
theorem spqr_send_inner_some_to_224_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A a st =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a st)
    (s0 s : State) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 224#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        AllocCallPreserved s sm ∧
        (Pm ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64)
            v1.innerState ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
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
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoPqRatchetInnerAt,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [h_inner_eq]
  generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 hx26 ⊢
  by_vm_steps (
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (optProtoInnerStateAt_expose_head A (fsp + 176#64) v1.innerState)))))))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro win
    wp_focus_pure; intro hwin_ne
    have hwin_br := ne_none3Cap_add_three_beq_zero_false hwin_ne
    have hwin_bne := ne_none3Cap_add_three_bne_zero_true hwin_ne
    wp_steps
    refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], ?_,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
    have hvn := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
    have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
    have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
    have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
    have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
    rw [ha56, ha64, ha72, ha80] at hvn
    have hin := optProtoInnerStateAt_unexpose_head A (fsp + 176#64) win v1.innerState
    have h190 := rejoin_190_to_1f20 fsp w1 w2 w3
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
         ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
         ((fsp + 80#64) ↦ₛ bs16) ∗
         (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
           ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
        (((fsp + 176#64) ↦₆₄ win) ∗ optProtoInnerStateHeadRest A (fsp + 176#64) win v1.innerState) ∗
        (((fsp + 400#64) ↦₆₄ w1) ∗ ((fsp + 408#64) ↦₆₄ w2) ∗
         ((fsp + 416#64) ↦₆₄ w3) ∗ memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
        (stackAt fsp spqrSendCalleeStack ∗
         memRegion fsp 48 ∗
         optChainPBAt A (fsp + 96#64) chain ∗
         spqrSendSavedRegs fsp s0 ∗
         Rest) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hvn (sepConj_mono hin (sepConj_mono_left h190))) ?_
    exact Entails.of_eq (by sep_ac_rfl))

/-- Pool-threading corollary of `spqr_send_inner_some_to_224_placed`, transporting `A.pool lim st s`
    to `A.pool lim st sm` across `VmPreserved s sm`. -/
theorem spqr_send_inner_some_to_224_placed_pool {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a st)
    (s0 s : State) (st : M.σ) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 224#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        VmPreserved s sm ∧
        AllocCallPreserved s sm ∧
        (Pm ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc
            ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
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
  have hst := spqr_send_inner_some_to_224_placed (H_inner := H_inner) (A := A.repAlloc)
    (ext := ext) h_inner_eq s0 s ret w0 w1 w2 w3 w30 w38 w40 w48 bs16 vn chain v1
    (A.pool lim st s ∗ Rest) hsp0_align hpc hrun hsp hx19 hx20 hx23 hx26 hlen16
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hst ?_)
  intro sm Pm _ _ ⟨hvm, hacp, hPm, hspm, hx19m, hx20m, hx23m, hx26m, htrm, hvregsm⟩
  refine ⟨hvm, hacp, ?_, hspm, hx19m, hx20m, hx23m, hx26m, htrm, hvregsm⟩
  rw [A.pool_transport lim st s sm hvm]
  exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlacedBudget
