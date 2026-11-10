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
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves2
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base

/-!
# Budget-Threaded Relocatable `States::send` Leaf-Call Arms (Block `427`)

Threads `RustCliAllocBudget` through arms 4–6 (`ct1Sampled`, `ct2Sampled`, `ekReceivedCt1Sampled`)
and re-exports arms 1–3 (`headerSent`, `ct1Received`, `keysSampled`) from `Aux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudget

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux
  (step_send_arm_headerSent_placed_ofEnv
   step_send_arm_ct1Received_placed_ofEnv
   step_send_arm_keysSampled_placed_ofEnv)

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1 (Chunk EncoderState States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled Ct2Sampled EkReceivedCt1Sampled)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1SampledAt chunkedCt2SampledAt chunkedEkReceivedCt1SampledAt chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize)
open CryptoVerification.SpqrV1.Poly.NextChunk (polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost Relocatable)
open CryptoVerification.SpqrV1.Top.Send
  (chunkAt_extract_words chunkAt_sp_add_eq chunkedCt1SampledAt_eq_tag_tail920
   chunkedCt1SampledTail920At chunkedStatesAt_eq_word0_tail920 chunkedStatesTail920At
   chunkedStatesWord0 expose_epoch_ct1Sampled expose_epoch_ct2Sampled
   expose_epoch_ekReceivedCt1Sampled memRegion_38_eq_chunk_slot polyEncoderTagVal
   scratch_and_chunk_entails_memRegion spqrSendCalleeStack spqrSendKeySlotAt spqrSendPayloadSlotAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced Ct1SampledSendCt1ChunkPlacedOkX
   Ct1SampledSendCt1ChunkPlacedOkXOfEnv Ct1SampledSendCt1ChunkTightPlacedOkX
   Ct2SampledSendCt2ChunkPlacedOkX Ct2SampledSendCt2ChunkPlacedOkXOfEnv
   Ct2SampledSendCt2ChunkTightPlacedOkX EkReceivedCt1SampledSendCt1ChunkPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX
   spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (SpqrSendChunkEnv ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct2SampledSendCt2ChunkPlacedSpecOfEnv ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
  (SpqrSendJoinStatePlaced call_lscro_calleeStack_evs_sepWP call_memcpy_relocate_vm
   leaf_arm_post_entails_placed of_sepWP_lscro of_sepWP_lscro_plain)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux (sepWP_vm_mono)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
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
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Arm 4: `.ct1Sampled s` (`+1128 -> +2356 -> +3068`, Block `335`) -/

/-- Budget-threaded post-entailment for `.ct1Sampled` at the post-`States::send` join point. -/
theorem ct1Sampled_arm_post_entails_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp w0 x21 x27 : BitVec 64) (x24_8 : BitVec 8)
    (P : SepProp) (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (Frame : SepProp) (hx21 : x21 = noneCap)
    (hpay : chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4 ⊢
      spqrSendPayloadSlotAt sp x24_8 (.ct1 chunk))
    (hP_eq : P =
      (stackAt sp spqrSendCalleeStack ∗ A.pool lim st s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗
        (((sp + 0x1260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x1268#64) 920 ∗
          chunkAt ((sp + 0x1260#64) + 928#64) chunk) ∗
        (chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4) ∗
        memRegion (sp + 0x580#64) 16 ∗
        chunkedCt1SampledTail920At A.repAlloc (sp + 0x590#64) outSt) ∗ Frame) :
    P ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool lim st s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
        spqrSendPayloadSlotAt sp x24_8 (.ct1 chunk) ∗ spqrSendKeySlotAt A.repAlloc sp x21 x27 none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame := by
  have hkey : memRegion (sp + 0x580#64) 16 ⊢ spqrSendKeySlotAt A.repAlloc sp x21 x27 none := by
    dsimp only [spqrSendKeySlotAt]; exact Entails.pure_right hx21 (Entails.refl _)
  have h8 : ((sp + 0x1260#64) ↦₆₄ w0) ⊢ memRegion (sp + 0x1260#64) 8 := by
    rw [pointsTo64_eq_pointsToBytes, ← unpack64_length w0]; exact pointsToBytes_entails_memRegion _ _
  have h928 : ((sp + 0x1260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x1268#64) 920 ⊢ memRegion (sp + 0x1260#64) 928 := by
    refine Entails.trans (sepConj_mono_left h8) ?_
    rw [ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 8) (k := 920) (b' := sp + 0x1268#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    exact Entails.refl _
  have h2 : (((sp + 0x1260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x1268#64) 920 ∗
      chunkAt ((sp + 0x1260#64) + 928#64) chunk) ⊢ memRegion (sp + 0x1260#64) (928 + chunkSize) := by
    rw [← sepConj_assoc]
    exact Entails.trans (sepConj_mono_left h928) (scratch_and_chunk_entails_memRegion sp 928 chunk)
  rw [hP_eq]; dsimp only [chunkedStatesTail920At]
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono h2 (sepConj_mono hpay (sepConj_mono_left hkey))))))))

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem polyEncoderTagVal_beq_neg1 (es : EncoderState) :
    (polyEncoderTagVal es == 18446744073709551615#64) = false := by cases es <;> rfl

/-- Non-panicking `SepWP` relocatable leaf-call arm 4: `.ct1Sampled s` (`+1128 -> +2356 -> +3068`). -/
theorem step_send_arm_ct1Sampled_placed_sepWP_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk }))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (928 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 335) (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP; dsimp only [chunkedStatesAt]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Sampled A.repAlloc sp st; rw [h_ep]
  apply of_sepWP_lscro_plain (mid := lsmpl.base 335) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack_evs_sepWP (x := (({
      outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } :
      Ct1SampledSendCt1ChunkGhost F), st0))
    sp (polyNextChunkStack + 1376) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (928 + chunkSize) ∗ chunkedCt1SampledAt A.repAlloc (sp + 0x950#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st0 s)
    (T_post := fun evs sm => chunkedCt1SampledAt A.repAlloc (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 928#64) chunk ∗ memRegion (sp + 0x950#64) 928 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st0) sm)
    (F := memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := True)
    (φ_post := fun evs sf => sf.trace = s.trace ∧
      Env { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } evs)
    hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1156#64) (by simp only [arm64_norm, *])
    (by dsimp only [ct1SampledSendCt1ChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc, hsend, hfit])
    trivial
    (by rw [h_ep]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [ct1SampledSendCt1ChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc]) ?_
  rintro sm evs hpc_sm hrun_sm hsp_sm ⟨htr_sm, hevs⟩ hcrl_sm hx19_sm _ _ hx22_sm _ hx24_sm hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx22_sm hx24_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  rw [chunkedCt1SampledAt_eq_tag_tail920 A.repAlloc (sp + 0x1260#64) outSt,
      show (sp + 0x1260#64) + 8#64 = sp + 0x1268#64 by rw [BitVec.add_assoc]; rfl]
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_sm; wp_steps
  refine call_memcpy_relocate_vm hmemcpy
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedCt1SampledTail920At A.repAlloc outSt)
    (sp + 0x590#64) (sp + 0x1268#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      memRegion (sp + 0x950#64) 928 ∗ ((sp + 0x1260#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗
      chunkAt ((sp + 0x1260#64) + 928#64) chunk ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1176#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ hx24_sf hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_sm_sf : VmPreserved sm sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx24_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1600 : (sp + 0x1260#64) + 928#64 = sp + 0x1600#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1600#64 0x1608#64 0x1610#64 0x1618#64 0x1620#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1600, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  refine sepWP_vm_mono
    (Q := fun sf_end P_end =>
      SpqrSendJoinStatePlaced sp ext s0 sf_end { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) ∧
      (P_end ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((sf_end.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf_end.readReg64 .x21) (sf_end.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame))
    ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, wp_norm],
          ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *]⟩, ?_⟩
      exact ct1Sampled_arm_post_entails_placed A lim (M.stepEvents evs st0) sm sp
        (polyEncoderTagVal outSt.sending_ct1.s) _ _ _ _ outSt chunk Frame
        (by simp only [arm64_norm]; rfl)
        (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm, *]) (Entails.refl _))
        (by rw [h1600, hchunk_src, hchunk_dst]; sep_ac_rfl)
  · rintro sf_end P_end hvm_end ⟨hjoin, hent⟩ hcrl_f
    rw [← A.pool_of_vmPreserved (hvm_sm_sf.trans hvm_end)] at hent
    refine SepWP.fold hent (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf_end evs hevs hcrl_f hjoin

/-- Envelope-parametric `SepWPp` relocatable leaf-call arm 4: `.ct1Sampled s` (`+1128 -> +2356 -> +3068`). -/
theorem step_send_arm_ct1Sampled_placed_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (928 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hcrl
  refine step_send_arm_ct1Sampled_placed_sepWP_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP
    fun sf evs hevs hcrl_f hjoin => ?_
  exact SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hcrl_f hjoin

/-- Peer-seam default (`SpqrSendChunkEnv`) relocatable leaf-call arm 4: `.ct1Sampled s`. -/
theorem step_send_arm_ct1Sampled_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1SampledSendCt1ChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0 SpqrSendChunkEnv)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (928 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      SpqrSendChunkEnv evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ct1Sampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-- Tight exact-envelope (`Ct1SampledSendCt1ChunkEnv`) relocatable leaf-call arm 4: `.ct1Sampled s`. -/
theorem step_send_arm_ct1Sampled_tight_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1SampledSendCt1ChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Ct1SampledSendCt1ChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (928 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Ct1SampledSendCt1ChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ct1Sampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-! ## 2. Arm 5: `.ct2Sampled s` (`+2372 -> +3068`, Block `354`) -/

/-- Non-panicking `SepWP` relocatable leaf-call arm 5: `.ct2Sampled s` (`+2372 -> +3068`). -/
theorem step_send_arm_ct2Sampled_placed_sepWP_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct2Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct2_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct2Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (456 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct2 chunk } (.ct2Sampled outSt) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (456 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct2 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct2Sampled outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 354) (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Env)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ct2Sampled st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct2Sampled A.repAlloc sp st; rw [h_ep]
  apply of_sepWP_lscro_plain (mid := lsmpl.base 354) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack_evs_sepWP (x := (({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } :
      Ct2SampledSendCt2ChunkGhost F), st0))
    sp (polyNextChunkStack + 896) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (456 + chunkSize) ∗ chunkedCt2SampledAt A.repAlloc (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st0 s)
    (T_post := fun evs sm => chunkedCt2SampledAt A.repAlloc (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 456#64) chunk ∗ memRegion (sp + 0x958#64) 456 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st0) sm)
    (F := ((sp + 0x950#64) ↦₆₄ 12#64) ∗ memRegion ((sp + 0x958#64) + 456#64) 464 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := True)
    (φ_post := fun evs sf => sf.trace = s.trace ∧
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs)
    hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 2400#64) (by simp only [arm64_norm, *])
    (by dsimp only [ct2SampledSendCt2ChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc, hsend, hfit])
    trivial
    (by rw [h_ep]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [ct2SampledSendCt2ChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc]) ?_
  rintro sm evs hpc_sm hrun_sm hsp_sm ⟨htr_sm, hevs⟩ hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 456) (k := 464) (b' := (sp + 0x590#64) + 456#64) rfl rfl (by decide)]
  refine call_memcpy_relocate_vm hmemcpy (Relocatable.of_chunkedCt2SampledAt A.repAlloc outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 12#64) ∗ memRegion (sp + 0x958#64) 456 ∗
      memRegion ((sp + 0x958#64) + 456#64) 464 ∗ chunkAt ((sp + 0x1260#64) + 456#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 456#64) 464 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 2420#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_sm_sf : VmPreserved sm sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1428 : (sp + 0x1260#64) + 456#64 = sp + 0x1428#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1428#64 0x1430#64 0x1438#64 0x1440#64 0x1448#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1428, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  refine sepWP_vm_mono
    (Q := fun sf_end P_end =>
      SpqrSendJoinStatePlaced sp ext s0 sf_end { epoch := st.uc.epoch, payload := .ct2 chunk } (.ct2Sampled outSt) ∧
      (P_end ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (456 + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((sf_end.readReg64 .x24).setWidth 8) (.ct2 chunk) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf_end.readReg64 .x21) (sf_end.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct2Sampled outSt)) ∗ Frame))
    ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, wp_norm],
          ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *]⟩, ?_⟩
      exact leaf_arm_post_entails_placed A lim (M.stepEvents evs st0) sm sp 12#64 _ _ _ 456 _
        (chunkedCt2SampledAt A.repAlloc (sp + 0x590#64) outSt) chunk (.ct2 chunk) (.ct2Sampled outSt) Frame
        (by decide) (by simp only [arm64_norm]; rfl)
        (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
        rfl (by rw [h1428, hchunk_src, hchunk_dst]; sep_ac_rfl)
  · rintro sf_end P_end hvm_end ⟨hjoin, hent⟩ hcrl_f
    rw [← A.pool_of_vmPreserved (hvm_sm_sf.trans hvm_end)] at hent
    refine SepWP.fold hent (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf_end evs hevs hcrl_f hjoin

/-- Envelope-parametric `SepWPp` relocatable leaf-call arm 5: `.ct2Sampled s` (`+2372 -> +3068`). -/
theorem step_send_arm_ct2Sampled_placed_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct2Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct2_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct2Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (456 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct2 chunk } (.ct2Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (456 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct2 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct2Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hcrl
  refine step_send_arm_ct2Sampled_placed_sepWP_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP
    fun sf evs hevs hcrl_f hjoin => ?_
  exact SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hcrl_f hjoin

/-- Peer-seam default (`SpqrSendChunkEnv`) relocatable leaf-call arm 5: `.ct2Sampled s`. -/
theorem step_send_arm_ct2Sampled_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct2SampledSendCt2ChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct2Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct2_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0 SpqrSendChunkEnv)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct2Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (456 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      SpqrSendChunkEnv evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct2 chunk } (.ct2Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (456 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct2 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct2Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ct2Sampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-- Tight exact-envelope (`Ct2SampledSendCt2ChunkEnv`) relocatable leaf-call arm 5: `.ct2Sampled s`. -/
theorem step_send_arm_ct2Sampled_tight_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct2SampledSendCt2ChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct2Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct2_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Ct2SampledSendCt2ChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct2Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (456 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Ct2SampledSendCt2ChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct2 chunk } (.ct2Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (456 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct2 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct2Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ct2Sampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-! ## 3. Arm 6: `.ekReceivedCt1Sampled s` (`+2460 -> +3068`, Block `344`) -/

/-- Non-panicking `SepWP` relocatable leaf-call arm 6: `.ekReceivedCt1Sampled s` (`+2460 -> +3068`). -/
theorem step_send_arm_ekReceivedCt1Sampled_placed_sepWP_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2460#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekReceivedCt1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (528 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ekReceivedCt1Sampled outSt) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (528 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekReceivedCt1Sampled outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 344) (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ekReceivedCt1Sampled st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekReceivedCt1Sampled A.repAlloc sp st; rw [h_ep]
  apply of_sepWP_lscro_plain (mid := lsmpl.base 344) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack_evs_sepWP (x := (({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } :
      EkReceivedCt1SampledSendCt1ChunkGhost F), st0))
    sp (polyNextChunkStack + 960) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (528 + chunkSize) ∗ chunkedEkReceivedCt1SampledAt A.repAlloc (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st0 s)
    (T_post := fun evs sm => chunkedEkReceivedCt1SampledAt A.repAlloc (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 528#64) chunk ∗ memRegion (sp + 0x958#64) 528 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st0) sm)
    (F := ((sp + 0x950#64) ↦₆₄ 10#64) ∗ memRegion ((sp + 0x958#64) + 528#64) 392 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := True)
    (φ_post := fun evs sf => sf.trace = s.trace ∧
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs)
    hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 2480#64) (by simp only [arm64_norm, *])
    (by dsimp only [ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc, hsend, hfit])
    trivial
    (by rw [h_ep]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc]) ?_
  rintro sm evs hpc_sm hrun_sm hsp_sm ⟨htr_sm, hevs⟩ hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 528) (k := 392) (b' := (sp + 0x590#64) + 528#64) rfl rfl (by decide)]
  refine call_memcpy_relocate_vm hmemcpy (Relocatable.of_chunkedEkReceivedCt1SampledAt A.repAlloc outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 10#64) ∗ memRegion (sp + 0x958#64) 528 ∗
      memRegion ((sp + 0x958#64) + 528#64) 392 ∗ chunkAt ((sp + 0x1260#64) + 528#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 528#64) 392 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 2500#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_sm_sf : VmPreserved sm sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1470 : (sp + 0x1260#64) + 528#64 = sp + 0x1470#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1470#64 0x1478#64 0x1480#64 0x1488#64 0x1490#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1470, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  refine sepWP_vm_mono
    (Q := fun sf_end P_end =>
      SpqrSendJoinStatePlaced sp ext s0 sf_end { epoch := st.uc.epoch, payload := .ct1 chunk } (.ekReceivedCt1Sampled outSt) ∧
      (P_end ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (528 + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((sf_end.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf_end.readReg64 .x21) (sf_end.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekReceivedCt1Sampled outSt)) ∗ Frame))
    ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, wp_norm],
          ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *]⟩, ?_⟩
      exact leaf_arm_post_entails_placed A lim (M.stepEvents evs st0) sm sp 10#64 _ _ _ 528 _
        (chunkedEkReceivedCt1SampledAt A.repAlloc (sp + 0x590#64) outSt) chunk (.ct1 chunk)
        (.ekReceivedCt1Sampled outSt) Frame (by decide) (by simp only [arm64_norm]; rfl)
        (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
        rfl (by rw [h1470, hchunk_src, hchunk_dst]; sep_ac_rfl)
  · rintro sf_end P_end hvm_end ⟨hjoin, hent⟩ hcrl_f
    rw [← A.pool_of_vmPreserved (hvm_sm_sf.trans hvm_end)] at hent
    refine SepWP.fold hent (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf_end evs hevs hcrl_f hjoin

/-- Envelope-parametric `SepWPp` relocatable leaf-call arm 6: `.ekReceivedCt1Sampled s` (`+2460 -> +3068`). -/
theorem step_send_arm_ekReceivedCt1Sampled_placed_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2460#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekReceivedCt1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (528 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ekReceivedCt1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (528 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekReceivedCt1Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hcrl
  refine step_send_arm_ekReceivedCt1Sampled_placed_sepWP_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP
    fun sf evs hevs hcrl_f hjoin => ?_
  exact SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hcrl_f hjoin

/-- Peer-seam default (`SpqrSendChunkEnv`) relocatable leaf-call arm 6: `.ekReceivedCt1Sampled s`. -/
theorem step_send_arm_ekReceivedCt1Sampled_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : EkReceivedCt1SampledSendCt1ChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0 SpqrSendChunkEnv)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2460#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekReceivedCt1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (528 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      SpqrSendChunkEnv evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ekReceivedCt1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (528 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekReceivedCt1Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ekReceivedCt1Sampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-- Tight exact-envelope (`EkReceivedCt1SampledSendCt1ChunkEnv`) relocatable leaf-call arm 6: `.ekReceivedCt1Sampled s`. -/
theorem step_send_arm_ekReceivedCt1Sampled_tight_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (EkReceivedCt1SampledSendCt1ChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2460#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ekReceivedCt1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (528 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      EkReceivedCt1SampledSendCt1ChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ekReceivedCt1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (528 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ekReceivedCt1Sampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ekReceivedCt1Sampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudget
