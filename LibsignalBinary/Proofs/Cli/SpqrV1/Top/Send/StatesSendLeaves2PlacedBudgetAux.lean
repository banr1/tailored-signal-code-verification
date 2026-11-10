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
# Budget-Threaded Relocatable `States::send` Leaf-Call Arms 1–3 (`Aux`, Block `427`)

Threads `RustCliAllocBudget` through leaf-call arms `headerSent`, `ct1Received`, and
`keysSampled` of `<States>::send` in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1 (Chunk States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled Ct2Sampled EkReceivedCt1Sampled)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (Ct1Received HeaderSent KeysSampled)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1ReceivedAt chunkedCt1SampledAt chunkedCt2SampledAt chunkedEkReceivedCt1SampledAt
   chunkedHeaderSentAt chunkedKeysSampledAt chunkedKeysSampledAt_eq_ct1ReceivedAt
   chunkedKeysSampledToCt1Received chunkedStatesAt unchunkedHeaderSentToEkSentCt1Received)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize)
open CryptoVerification.SpqrV1.Poly.NextChunk (polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost Relocatable)
open CryptoVerification.SpqrV1.Top.Send
  (chunkAt_extract_words chunkAt_sp_add_eq chunkedCt1SampledAt_eq_tag_tail920
   chunkedCt1SampledTail920At chunkedStatesAt_eq_word0_tail920 chunkedStatesTail920At
   chunkedStatesWord0 expose_epoch_ct1Received expose_epoch_ct1Sampled expose_epoch_ct2Sampled
   expose_epoch_ekReceivedCt1Sampled expose_epoch_headerSent keysSampled_send_hdr_chunk_to_ct1Received
   memRegion_38_eq_chunk_slot polyEncoderTagVal scratch_and_chunk_entails_memRegion
   spqrSendCalleeStack spqrSendKeySlotAt spqrSendPayloadSlotAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced Ct1ReceivedSendEkChunkPlacedOkX Ct1ReceivedSendEkChunkPlacedOkXOfEnv
   Ct1ReceivedSendEkChunkTightPlacedOkX Ct1SampledSendCt1ChunkPlacedOkX
   Ct1SampledSendCt1ChunkPlacedOkXOfEnv Ct1SampledSendCt1ChunkTightPlacedOkX
   Ct2SampledSendCt2ChunkPlacedOkX Ct2SampledSendCt2ChunkPlacedOkXOfEnv
   Ct2SampledSendCt2ChunkTightPlacedOkX EkReceivedCt1SampledSendCt1ChunkPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX
   HeaderSentSendEkChunkPlacedOkX HeaderSentSendEkChunkPlacedOkXOfEnv
   HeaderSentSendEkChunkTightPlacedOkX spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (SpqrSendChunkEnv ct1ReceivedSendEkChunkPlacedSpecOfEnv ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct2SampledSendCt2ChunkPlacedSpecOfEnv ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv
   headerSentSendEkChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
  (SpqrSendJoinStatePlaced call_lscro_calleeStack_evs_sepWP call_memcpy_relocate_vm
   leaf_arm_post_entails_placed of_sepWP_lscro of_sepWP_lscro_plain)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv)

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

omit [LibsignalPlacement] in
theorem sepWP_vm_mono {P : Program} {b tgt : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {Q post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) tgt s Pre (fun sf Pf => VmPreserved s sf ∧ Q sf Pf))
    (h2 : ∀ sf Pf, VmPreserved s sf → Q sf Pf → post sf Pf) :
    SepWP (P.rebase b Hk) tgt s Pre post :=
  SepWP.mono h1 fun sf Pf _ _ ⟨hvm, hq⟩ => h2 sf Pf hvm hq

/-! ## 1. Arm 1: `.headerSent s` (`+960 -> +3068`, Block `336`) -/

/-- Non-panicking `SepWP` relocatable leaf-call arm 1: `.headerSent s` (`+960 -> +3068`). -/
theorem step_send_arm_headerSent_placed_sepWP_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : HeaderSent spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 960#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerSent st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (880 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ek chunk } (.headerSent outSt) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (880 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ek chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.headerSent outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 336) (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpecOfEnv M A lim F Env)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.headerSent st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_headerSent A.repAlloc sp st; rw [h_ep]
  apply of_sepWP_lscro_plain (mid := lsmpl.base 336) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack_evs_sepWP (x := (({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } :
      HeaderSentSendEkChunkGhost F), st0))
    sp (polyNextChunkStack + 1328) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (880 + chunkSize) ∗ chunkedHeaderSentAt A.repAlloc (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st0 s)
    (T_post := fun evs sm => chunkedHeaderSentAt A.repAlloc (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 880#64) chunk ∗ memRegion (sp + 0x958#64) 880 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st0) sm)
    (F := ((sp + 0x950#64) ↦₆₄ 4#64) ∗ memRegion ((sp + 0x958#64) + 880#64) 40 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := True)
    (φ_post := fun evs sf => sf.trace = s.trace ∧
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs)
    hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 980#64) (by simp only [arm64_norm, *])
    (by dsimp only [headerSentSendEkChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc, hsend, hfit])
    trivial
    (by rw [h_ep]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [headerSentSendEkChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc]) ?_
  rintro sm evs hpc_sm hrun_sm hsp_sm ⟨htr_sm, hevs⟩ hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 880) (k := 40) (b' := (sp + 0x590#64) + 880#64) rfl rfl (by decide)]
  refine call_memcpy_relocate_vm hmemcpy (Relocatable.of_chunkedHeaderSentAt A.repAlloc outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 4#64) ∗ memRegion (sp + 0x958#64) 880 ∗
      memRegion ((sp + 0x958#64) + 880#64) 40 ∗ chunkAt ((sp + 0x1260#64) + 880#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 880#64) 40 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1000#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_sm_sf : VmPreserved sm sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h15d0 : (sp + 0x1260#64) + 880#64 = sp + 0x15d0#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x15d0#64 0x15d8#64 0x15e0#64 0x15e8#64 0x15f0#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h15d0, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  refine sepWP_vm_mono
    (Q := fun sf_end P_end =>
      SpqrSendJoinStatePlaced sp ext s0 sf_end { epoch := st.uc.epoch, payload := .ek chunk } (.headerSent outSt) ∧
      (P_end ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (880 + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((sf_end.readReg64 .x24).setWidth 8) (.ek chunk) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf_end.readReg64 .x21) (sf_end.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.headerSent outSt)) ∗ Frame))
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
      exact leaf_arm_post_entails_placed A lim (M.stepEvents evs st0) sm sp 4#64 _ _ _ 880 _
        (chunkedHeaderSentAt A.repAlloc (sp + 0x590#64) outSt) chunk (.ek chunk) (.headerSent outSt) Frame
        (by decide) (by simp only [arm64_norm]; rfl)
        (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
        rfl (by rw [h15d0, hchunk_src, hchunk_dst]; sep_ac_rfl)
  · rintro sf_end P_end hvm_end ⟨hjoin, hent⟩ hcrl_f
    rw [← A.pool_of_vmPreserved (hvm_sm_sf.trans hvm_end)] at hent
    refine SepWP.fold hent (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf_end evs hevs hcrl_f hjoin

/-- Envelope-parametric `SepWPp` relocatable leaf-call arm 1: `.headerSent s` (`+960 -> +3068`). -/
theorem step_send_arm_headerSent_placed_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : HeaderSent spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 960#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerSent st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (880 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ek chunk } (.headerSent outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (880 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ek chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.headerSent outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hcrl
  refine step_send_arm_headerSent_placed_sepWP_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP
    fun sf evs hevs hcrl_f hjoin => ?_
  exact SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hcrl_f hjoin

/-- Peer-seam default (`SpqrSendChunkEnv`) relocatable leaf-call arm 1: `.headerSent s`. -/
theorem step_send_arm_headerSent_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : HeaderSentSendEkChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : HeaderSent spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0 SpqrSendChunkEnv)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 960#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerSent st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (880 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      SpqrSendChunkEnv evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ek chunk } (.headerSent outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (880 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ek chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.headerSent outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_headerSent_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-- Tight exact-envelope (`HeaderSentSendEkChunkEnv`) relocatable leaf-call arm 1: `.headerSent s`. -/
theorem step_send_arm_headerSent_tight_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : HeaderSentSendEkChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : HeaderSent spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (HeaderSentSendEkChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 960#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerSent st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (880 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      HeaderSentSendEkChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ek chunk } (.headerSent outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (880 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ek chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.headerSent outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_headerSent_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-! ## 2. Arm 2: `.ct1Received s` (`+1040 -> +3068`, Block `345`) -/

/-- Non-panicking `SepWP` relocatable leaf-call arm 2: `.ct1Received s` (`+1040 -> +3068`). -/
theorem step_send_arm_ct1Received_placed_sepWP_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1040#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Received st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ekCt1Ack chunk } (.ct1Received outSt) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ekCt1Ack chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Received outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Env)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.ct1Received st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Received A.repAlloc sp st; rw [h_ep]
  apply of_sepWP_lscro_plain (mid := lsmpl.base 345) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack_evs_sepWP (x := (({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } :
      Ct1ReceivedSendEkChunkGhost F), st0))
    sp (polyNextChunkStack + 944) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (504 + chunkSize) ∗ chunkedCt1ReceivedAt A.repAlloc (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st0 s)
    (T_post := fun evs sm => chunkedCt1ReceivedAt A.repAlloc (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗ memRegion (sp + 0x958#64) 504 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st0) sm)
    (F := ((sp + 0x950#64) ↦₆₄ 5#64) ∗ memRegion ((sp + 0x958#64) + 504#64) 416 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := True)
    (φ_post := fun evs sf => sf.trace = s.trace ∧
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs)
    hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1068#64) (by simp only [arm64_norm, *])
    (by dsimp only [ct1ReceivedSendEkChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc, hsend, hfit])
    trivial
    (by rw [h_ep]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [ct1ReceivedSendEkChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc]) ?_
  rintro sm evs hpc_sm hrun_sm hsp_sm ⟨htr_sm, hevs⟩ hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 504) (k := 416) (b' := (sp + 0x590#64) + 504#64) rfl rfl (by decide)]
  refine call_memcpy_relocate_vm hmemcpy (Relocatable.of_chunkedCt1ReceivedAt A.repAlloc outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 5#64) ∗ memRegion (sp + 0x958#64) 504 ∗
      memRegion ((sp + 0x958#64) + 504#64) 416 ∗ chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 504#64) 416 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1088#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_sm_sf : VmPreserved sm sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1458 : (sp + 0x1260#64) + 504#64 = sp + 0x1458#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1458#64 0x1460#64 0x1468#64 0x1470#64 0x1478#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1458, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  refine sepWP_vm_mono
    (Q := fun sf_end P_end =>
      SpqrSendJoinStatePlaced sp ext s0 sf_end { epoch := st.uc.epoch, payload := .ekCt1Ack chunk } (.ct1Received outSt) ∧
      (P_end ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((sf_end.readReg64 .x24).setWidth 8) (.ekCt1Ack chunk) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf_end.readReg64 .x21) (sf_end.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Received outSt)) ∗ Frame))
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
      exact leaf_arm_post_entails_placed A lim (M.stepEvents evs st0) sm sp 5#64 _ _ _ 504 _
        (chunkedCt1ReceivedAt A.repAlloc (sp + 0x590#64) outSt) chunk (.ekCt1Ack chunk) (.ct1Received outSt) Frame
        (by decide) (by simp only [arm64_norm]; rfl)
        (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
        rfl (by rw [h1458, hchunk_src, hchunk_dst]; sep_ac_rfl)
  · rintro sf_end P_end hvm_end ⟨hjoin, hent⟩ hcrl_f
    rw [← A.pool_of_vmPreserved (hvm_sm_sf.trans hvm_end)] at hent
    refine SepWP.fold hent (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf_end evs hevs hcrl_f hjoin

/-- Envelope-parametric `SepWPp` relocatable leaf-call arm 2: `.ct1Received s` (`+1040 -> +3068`). -/
theorem step_send_arm_ct1Received_placed_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1040#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Received st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ekCt1Ack chunk } (.ct1Received outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ekCt1Ack chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Received outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hcrl
  refine step_send_arm_ct1Received_placed_sepWP_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP
    fun sf evs hevs hcrl_f hjoin => ?_
  exact SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hcrl_f hjoin

/-- Peer-seam default (`SpqrSendChunkEnv`) relocatable leaf-call arm 2: `.ct1Received s`. -/
theorem step_send_arm_ct1Received_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0 SpqrSendChunkEnv)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1040#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Received st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      SpqrSendChunkEnv evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ekCt1Ack chunk } (.ct1Received outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ekCt1Ack chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Received outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ct1Received_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-- Tight exact-envelope (`Ct1ReceivedSendEkChunkEnv`) relocatable leaf-call arm 2: `.ct1Received s`. -/
theorem step_send_arm_ct1Received_tight_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Ct1ReceivedSendEkChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1040#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.ct1Received st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Ct1ReceivedSendEkChunkEnv { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ekCt1Ack chunk } (.ct1Received outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ekCt1Ack chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Received outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_ct1Received_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-! ## 3. Arm 3: `.keysSampled s` (`+1208 -> +3056 -> +3068`, Block `345`) -/

/-- Non-panicking `SepWP` relocatable leaf-call arm 3: `.keysSampled s` (`+1208 -> +3056 -> +3068`). -/
theorem step_send_arm_keysSampled_placed_sepWP_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : KeysSampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_hdr_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk }))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1208#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.keysSampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Env)) := hcall
  have hsend' := keysSampled_send_hdr_chunk_to_ct1Received hsend
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A.repAlloc (sp + 0x950#64) (.keysSampled st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Received A.repAlloc sp (chunkedKeysSampledToCt1Received st); rw [h_ep]
  apply of_sepWP_lscro_plain (mid := lsmpl.base 345) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack_evs_sepWP (x := (({
      outA := sp + 0x1260#64, stA := sp + 0x958#64,
      st := chunkedKeysSampledToCt1Received st,
      outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } :
      Ct1ReceivedSendEkChunkGhost F), st0))
    sp (polyNextChunkStack + 944) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A.repAlloc (sp + 0x958#64) (chunkedKeysSampledToCt1Received st) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st0 s)
    (T_post := fun evs sm => chunkedCt1ReceivedAt A.repAlloc (sp + 0x1260#64) (chunkedKeysSampledToCt1Received outSt) ∗
      chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗ memRegion (sp + 0x958#64) 504 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st0) sm)
    (F := ((sp + 0x950#64) ↦₆₄ 3#64) ∗ memRegion ((sp + 0x958#64) + 504#64) 416 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := True)
    (φ_post := fun evs sf => sf.trace = s.trace ∧
      Env
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } evs)
    hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1236#64) (by simp only [arm64_norm, *])
    (by dsimp only [ct1ReceivedSendEkChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc, hsend', hfit])
    trivial
    (by rw [h_ep]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [ct1ReceivedSendEkChunkPlacedSpecOfEnv]; simp only [arm64_norm, sepConj_assoc]) ?_
  rintro sm evs hpc_sm hrun_sm hsp_sm ⟨htr_sm, hevs⟩ hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  rw [← chunkedKeysSampledAt_eq_ct1ReceivedAt]
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 504) (k := 416) (b' := (sp + 0x590#64) + 504#64) rfl rfl (by decide)]
  refine call_memcpy_relocate_vm hmemcpy
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedKeysSampledAt A.repAlloc outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 3#64) ∗ memRegion (sp + 0x958#64) 504 ∗
      memRegion ((sp + 0x958#64) + 504#64) 416 ∗ chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 504#64) 416 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 1256#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  have hvm_sm_sf : VmPreserved sm sf := VmPreserved.trans (by simp only [arm64_norm, wp_norm]) hvm_sf
  simp only [arm64_norm, chunkedKeysSampledToCt1Received,
    unchunkedHeaderSentToEkSentCt1Received, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1458 : (sp + 0x1260#64) + 504#64 = sp + 0x1458#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1458#64 0x1460#64 0x1468#64 0x1470#64 0x1478#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1458, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  refine sepWP_vm_mono
    (Q := fun sf_end P_end =>
      SpqrSendJoinStatePlaced sp ext s0 sf_end { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) ∧
      (P_end ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sm ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((sf_end.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
        spqrSendKeySlotAt A.repAlloc sp (sf_end.readReg64 .x21) (sf_end.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt)) ∗ Frame))
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
      exact leaf_arm_post_entails_placed A lim (M.stepEvents evs st0) sm sp 3#64 _ _ _ 504 _
        (chunkedKeysSampledAt A.repAlloc (sp + 0x590#64) outSt) chunk (.hdr chunk) (.keysSampled outSt) Frame
        (by decide) (by simp only [arm64_norm]; rfl)
        (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
        rfl (by rw [h1458, hchunk_src, hchunk_dst]; sep_ac_rfl)
  · rintro sf_end P_end hvm_end ⟨hjoin, hent⟩ hcrl_f
    rw [← A.pool_of_vmPreserved (hvm_sm_sf.trans hvm_end)] at hent
    refine SepWP.fold hent (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf_end evs hevs hcrl_f hjoin

/-- Envelope-parametric `SepWPp` relocatable leaf-call arm 3: `.keysSampled s` (`+1208 -> +3056 -> +3068`). -/
theorem step_send_arm_keysSampled_placed_ofEnv {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F Env ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : KeysSampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_hdr_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Env
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1208#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.keysSampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Env
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hcrl
  refine step_send_arm_keysSampled_placed_sepWP_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP
    fun sf evs hevs hcrl_f hjoin => ?_
  exact SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hcrl_f hjoin

/-- Peer-seam default (`SpqrSendChunkEnv`) relocatable leaf-call arm 3: `.keysSampled s`. -/
theorem step_send_arm_keysSampled_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : KeysSampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_hdr_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0 SpqrSendChunkEnv)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1208#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.keysSampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      SpqrSendChunkEnv evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_keysSampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext

/-- Tight exact-envelope (`Ct1ReceivedSendEkChunkEnv`) relocatable leaf-call arm 3: `.keysSampled s`. -/
theorem step_send_arm_keysSampled_tight_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcall : Ct1ReceivedSendEkChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp : BitVec 64)
    (st outSt : KeysSampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_hdr_chunk = .ok (outSt, chunk))
    (hfit : FitsEnv M lim st0
      (Ct1ReceivedSendEkChunkEnv
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk }))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1208#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.keysSampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      Ct1ReceivedSendEkChunkEnv
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt)) ∗ Frame)
        post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost :=
  step_send_arm_keysSampled_placed_ofEnv A lim st0 ext hA hcall sp st outSt chunk
    hsend hfit hcrl hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28 hvregs hP hnext


end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux
