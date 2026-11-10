/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSym
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSymPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (Block `349`, `RustCliAllocBudget`)

Relocatable `[LibsignalPlacement]` verification of `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`,
153 instructions) under `RustCliAllocBudget M`, proving the `.ok (.done ...)` branch,
`ct1_acknowledged_recv_ek_chunk_placed_cl_ext`, and `ct1_acknowledged_recv_ek_chunk_placed_ok_x`
(discharging Blocks `338`, `382`, and `264`) in two-envelope, single-envelope, and canonical forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_349 blkPl_349 lsProg_349
   ls_subroutine_ok_of_block lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk Error Mac MlKem PolyDecoder PolyEncoder StatesResult
   mlkemValidatePkSpec spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded
   sessionMemcpyRegionSpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1AcknowledgedAt chunkedCt2SampledAt unchunkedCt1SentAt unchunkedCt2SentAt
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal decodedMessage_eq_ok)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1AckDoneSaved Ct1AcknowledgedRecvEkChunkGhost Relocatable authWordsList bv_sub_sub
   cells_1_unfold cells_3_unfold cells_7_unfold cells_8_unfold cells_16_unfold
   ct1AckEk_trace_writeVReg128 ct1AckSavedRegs
   ct1Ack_done_outA_recompose ct1Ack_done_scratch_join ct1Ack_done_stack_1160_rejoin
   ct1Ack_done_uc1_copy_recompose ct1Ack_done_uc56_and_headers_recompose
   ct1Ack_some_post_recvEk ct1Ack_some_pre_recvEk
   ct1AcknowledgedRecvEkChunkResAt ct1AcknowledgedRecvEkChunkStack
   ct1_acknowledged_recv_ek_chunk_elim ct2SentWordsList fiveVecWordsList
   fold_ct1AckSavedRegs of_sepWP_lscl of_sepWP_lscro optVecU8At
   polyDecoderAt_dup_pts_len relocate_post_entails relocate_pre_entails relocatedHeap
   sendCt2EncoderStack sepWP_seq_lscl
   slice_and_tail_entails_vecCapPtrDealloc
   stackAt_1760_entry_split stackAt_sendCt2Encoder_eq_addChunk
   stackAt_sendCt2Encoder_eq_allocHook stackAt_sendCt2Encoder_eq_decodedMessage
   stackAt_sendCt2Encoder_eq_unchunkedRecvEk stackAt_sendCt2Encoder_eq_unchunkedSendCt2
   subroutine_ok_withLsCodeRoLoaded_of_left
   unchunkedCt1SentEkReceivedAt_extract_nonNone unchunkedCt1SentRecvEkResAt
   unchunkedCt1SentAt_extract unchunkedCt2SentAt_extract
   vecU8_entails_slice_and_tail vecU8_extract_nonNone vecWordsList
   wordsAt wordsAt_7 wordsAt_16 wordsAt_cons_off wordsAt_fiveVec wordsAt_nil
   wordsAt_sp592_fiveVec wordsAt_sp1176_fiveVec wordsAt_sp1760_fiveVec wordsBytes)
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget SeqEnv fitsEvents_append rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec rustCliReallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
  (dropGlueSortedSetPt16Spec drop_glue_sorted_set_pt16_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkEnv AddChunkSlotsEnv addChunkSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (Ct1AckRecvEkTailPreEnv Ct1AcknowledgedRecvEkChunkEnv
   Ct1AcknowledgedRecvEkChunkPlacedOkX Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv
   Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv
   Ct1AcknowledgedRecvEkChunkPostEnv Ct1AcknowledgedRecvEkChunkPreEnv
   PolyDecoderDecodedMessageEnv SendCt2EncoderBytesPostEnv SendCt2EncoderBytesPreEnv
   SendCt2EncoderPostEnv SendCt2EncoderPreEnv UnchunkedCt1SentRecvEkPostEnv
   ct1AckRecvEkTailPreEnv_nonempty ct1AcknowledgedRecvEkChunkEnv_nonempty
   ct1AcknowledgedRecvEkChunkPlacedSpec ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv
   ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv ct1AcknowledgedRecvEkChunkPreEnv_nonempty
   polyDecoderDecodedMessagePlacedSpec sendCt2EncoderSpec
   unchunkedCt1SentRecvEkSpec unchunkedCt1SentRecvEkSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSymPlacedBudget
  (ct1AckEk_call_addChunk_cro ct1AckEk_call_decodedMessage_cro
   ct1AckEk_call_unchunkedRecvEk_cl ct1AckEk_call_unchunkedRecvEk_cl_ofPrePostEnv
   ct1_ack_recv_ek_epilogue_244_placed
   ct1_ack_recv_ek_err_branch_placed ct1_ack_recv_ek_none_branch_placed_evs)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
  (call_sendCt2_cl_tight)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
  (call_sendCt2Encoder_cl send_ct2_encoder_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
  (unchunked_ct1_sent_recv_ek_placed_cl_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  addChunkTotal DecodedMessageEnv
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
  ct1AckEk_trace_writeVReg128

/-! ## 1. Re-Exports from `Batch2DefsPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (Ct1AckRecvEkTailPreEnv ct1AckRecvEkTailPreEnv_nonempty
   Ct1AcknowledgedRecvEkChunkPreEnv Ct1AcknowledgedRecvEkChunkPostEnv
   Ct1AcknowledgedRecvEkChunkEnv)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (ct1AcknowledgedRecvEkChunkPreEnv_nonempty ct1AcknowledgedRecvEkChunkEnv_nonempty
   ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv
   ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv
   ct1AcknowledgedRecvEkChunkPlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv
   Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv
   Ct1AcknowledgedRecvEkChunkPlacedOkX)

/-! ## 2. Sequencing, Deallocation & Relocation Helpers -/

private theorem ct1AckEk_sepWP_congr_pre {prog : Program} {tgt : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post1 post2 : State → SepProp → Prop}
    (h : SepWP prog tgt s P2 post2) (hP : P1 = P2) (hpost : post1 = post2) :
    SepWP prog tgt s P1 post1 := by
  subst hP hpost; exact h

private theorem ct1AckEk_sepWPp_congr_pre {prog : Program} {tgt : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post1 post2 Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : SepWPp prog tgt s P2 post2 Qp oom) (hP : P1 = P2)
    (hpost : post1 = post2) :
    SepWPp prog tgt s P1 post1 Qp oom := by
  subst hP hpost; exact h

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem call_memcpy_relocate_cs_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec))
    {n : Nat} {P_rel : BitVec 64 → SepProp} (hrel : Relocatable n P_rel)
    (dst src : BitVec 64) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ P_rel src ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((P_rel dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  have hpre_eq : P = (memRegion dst n ∗ P_rel src) ∗ (A.pool lim st s ∗ Frame) := by
    rw [hsplit]; sep_ac_rfl
  rw [hpre_eq]
  refine SepWP.fold (relocate_pre_entails hrel dst src (A.pool lim st s ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap P_rel bs ∗ (A.pool lim st s ∗ Frame))
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [withVmPreserved, sessionMemcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWP.fold (relocate_post_entails dst src hlen (A.pool lim st sf ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq :
        (P_rel dst ∗ memRegion src n) ∗ (A.pool lim st sf ∗ Frame) =
        (P_rel dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame := by sep_ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 3. Done Branch (`+0x098..+0x184`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.ok (.done ...)` branch of `<Ct1Acknowledged>::recv_ek_chunk`
    (Block `349`). -/
theorem ct1_ack_recv_ek_done_branch_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hsendCt2_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (hdealloc_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "memcpy") (withVmPreserved sessionMemcpyRegionSpec))
    (hsortedSet16_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)))
    (outA stA chunkA : BitVec 64)
    (chunk : Chunk) (receivingEk : PolyDecoder)
    (uc1 : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (sendingCt2 : PolyEncoder)
    (res : Except Error
      (CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1AcknowledgedRecvChunk
        spqrPolyApi (spqrAuthApi F)))
    (hsc_ok : uc1.send_ct2 K = .ok (outUc, ct2, mac))
    (henc_ok : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac =
      .ok sendingCt2)
    (hres : res = .ok (.done { uc := outUc, sending_ct2 := sendingCt2 }))
    (st_0 : M.σ) (evs_pre : List AllocEvent)
    {PostOut : List AllocEvent → Prop}
    (hfit_tail : FitsEnv M lim (M.stepEvents evs_pre st_0)
      (SeqEnv (UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩)
        (SendCt2EncoderBytesPreEnv ct2.length mac.length)))
    (hpost : ∀ evs_sc evs_enc evs_free,
      UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩ evs_sc →
      SendCt2EncoderBytesPostEnv ct2.length mac.length evs_enc →
      FreeOnlyEvs evs_free →
      PostOut (evs_pre ++ evs_sc ++ evs_enc ++ evs_free))
    (s0 s : State) (R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (blkPl_349).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        polyDecoderAt A.repAlloc (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 632 ∗
        unchunkedCt1SentRecvEkResAt A.repAlloc (F := F) (s0.sp - 592#64) (.ok uc1) ∗
        memRegion (s0.sp - 464#64) 400 ∗ ct1AckSavedRegs s0 ∗
        A.pool lim (M.stepEvents evs_pre st_0) s ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ PostOut evs⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2PlacedRoAt ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st_0) sf ∗
            stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfit_send : FitsEnv M lim (M.stepEvents evs_pre st_0)
      (UnchunkedSendCt2PreEnv ⟨s0.sp - 592#64, s0.sp - 1176#64, uc1, outUc, ct2, mac⟩) := by
    intro evs hevs
    have hevs0 : UnchunkedSendCt2PreEnv ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩ evs := hevs
    exact hfit_tail evs (Or.inl (UnchunkedSendCt2PostEnv.of_pre hevs0))
  apply of_sepWP_lscl hcl (mid := lsmpl.base 347)
  wp_conv_pre =>
    dsimp only [unchunkedCt1SentRecvEkResAt]
    rw [ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 24) (k := 608) (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 24) (k := 584) (b' := s0.sp - 1176#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1176#64) (n := 128) (k := 456) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 400) (k := 56) (b' := s0.sp - 648#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (unchunkedCt1SentEkReceivedAt_extract_nonNone A.repAlloc (s0.sp - 592#64) uc1)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc1
  wp_focus_pure; intro _hne_uc1
  refine SepWP.fold (cells_3_unfold (s0.sp - 1200#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 1176#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  wp_steps_sync_pool (lsmpl.base 347)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1176_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc1_copy_recompose s0.sp uc1 g_uc1 _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_sendCt2_cl_tight hsendCt2_raw
    (s0.sp - 592#64) (s0.sp - 1176#64) uc1 outUc ct2 mac (M.stepEvents evs_pre st_0)
    hsc_ok hfit_send
    (ret_pc := (blkPl_349).base + 256#64) (next_pc := lsmpl.base 382) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by sep_focus)
    (fun sf1 evs_sc hpc1 hrun1 hsp1 hcs1 htr1 hevs_sc => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx23, hx24, hx25, hx26, hx27, hsp, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have h56_eq : (s0.sp - 592#64) + 56#64 = s0.sp - 536#64 := by bv_omega
  have h80_eq : (s0.sp - 592#64) + 80#64 = s0.sp - 512#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (unchunkedCt2SentAt_extract A.repAlloc (s0.sp - 592#64) outUc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_outUc
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s0.sp - 536#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s0.sp - 512#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  refine SepWP.fold (cells_7_unfold (s0.sp - 648#64)) (by sep_focus) ?_
  wp_pull_exists
  have hsp_outUc_words :
      wordsAt (s0.sp - 592#64) (ct2SentWordsList g_outUc outUc.epoch) =
      (((s0.sp - 592#64) ↦₆₄ g_outUc.v1.w0) ∗ ((s0.sp - 584#64) ↦₆₄ g_outUc.v1.w1) ∗
       ((s0.sp - 576#64) ↦₆₄ g_outUc.v1.w2) ∗ ((s0.sp - 568#64) ↦₆₄ g_outUc.v2.w0) ∗
       ((s0.sp - 560#64) ↦₆₄ g_outUc.v2.w1) ∗ ((s0.sp - 552#64) ↦₆₄ g_outUc.v2.w2) ∗
       ((s0.sp - 544#64) ↦₆₄ outUc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  have h648_outUc_words :
      wordsAt (s0.sp - 648#64) (ct2SentWordsList g_outUc outUc.epoch) =
      (((s0.sp - 648#64) ↦₆₄ g_outUc.v1.w0) ∗ ((s0.sp - 640#64) ↦₆₄ g_outUc.v1.w1) ∗
       ((s0.sp - 632#64) ↦₆₄ g_outUc.v1.w2) ∗ ((s0.sp - 624#64) ↦₆₄ g_outUc.v2.w0) ∗
       ((s0.sp - 616#64) ↦₆₄ g_outUc.v2.w1) ∗ ((s0.sp - 608#64) ↦₆₄ g_outUc.v2.w2) ∗
       ((s0.sp - 600#64) ↦₆₄ outUc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  wp_conv_pre => rw [hsp_outUc_words]; simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_steps_sync_pool (lsmpl.base 382)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq hsp_outUc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq h648_outUc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc56_and_headers_recompose s0.sp outUc g_outUc _ _ _ _ _ _)
    (by sep_focus) ?_
  have hfit_enc : FitsEnv M lim (M.stepEvents evs_sc (M.stepEvents evs_pre st_0))
      (SendCt2EncoderPreEnv ⟨s0.sp - 1048#64, ct2Ptr, ct2, macPtr, mac, sendingCt2⟩) := by
    intro e2 he2
    have hevs_sc0 : UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩ evs_sc := hevs_sc
    have he2_0 : SendCt2EncoderBytesPreEnv ct2.length mac.length e2 := he2
    exact ((fitsEvents_append M lim evs_sc e2 (M.stepEvents evs_pre st_0)).mp
      (hfit_tail (evs_sc ++ e2) (SeqEnv.append hevs_sc0 he2_0))).2
  refine call_sendCt2Encoder_cl hsendCt2Enc_raw
    (s0.sp - 1048#64) ct2Ptr macPtr ct2 mac sendingCt2
    (M.stepEvents evs_sc (M.stepEvents evs_pre st_0))
    hct2_ne hmac_ne henc_ok hfit_enc
    (ret_pc := (blkPl_349).base + 324#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf2 evs_enc hpc2 hrun2 hsp2 hcs2 htr2 hevs_enc hcl2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 264)
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  have hstack_alloc :
      stackAt (s0.sp - 1760#64) sendCt2EncoderStack =
      memRegion (s0.sp - 19216#64) 13360 ∗ stackAt (s0.sp - 1760#64) allocHookStack := by
    have h19216_sub : (s0.sp - 1760#64) - 17456#64 = s0.sp - 19216#64 := by bv_omega
    rw [stackAt_sendCt2Encoder_eq_allocHook (s0.sp - 1760#64), h19216_sub]
  refine SepWP.fold (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsampled_join :
      polyEncoderAt A.repAlloc (s0.sp - 1048#64) sendingCt2 ∗
        unchunkedCt2SentAt A.repAlloc (s0.sp - 648#64) outUc ⊢
      chunkedCt2SampledAt A.repAlloc (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } := by
    dsimp only [chunkedCt2SampledAt]
    have h400 : (s0.sp - 1048#64) + 400#64 = s0.sp - 648#64 := by bv_omega
    rw [h400]; exact Entails.refl _
  refine SepWP.fold hsampled_join (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_scratch_join s0.sp) (by sep_focus) ?_
  refine seq_clean_evs (mid := (blkPl_349).base + 344#64)
    (P_evs := fun evs_d1 sm =>
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        polyDecoderAt A.repAlloc (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 176 ∗
        chunkedCt2SampledAt A.repAlloc (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
        memRegion (s0.sp - 592#64) 528 ∗
        vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗
        memRegion (s0.sp - 19216#64) 13360 ∗ ct1AckSavedRegs s0) ∗
        A.pool lim (M.stepEvents evs_d1 (M.stepEvents evs_enc (M.stepEvents evs_sc (M.stepEvents evs_pre st_0)))) sm ∗
        stackAt (s0.sp - 1760#64) allocHookStack)
    (Q := fun sm => Ct1AckDoneSaved s0 sm (s0.sp - 1760#64) outA ct2Cap ct2Ptr)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hmac : (macCap == 0#64) = true <;>
      simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hsp2, htr2, hvregs_2]⟩
    · apply sepWP_evs_dealloc macCap.toNat 1
      wp_steps; wp_apply
      refine align_pre_st (by rw [hsp2]; sep_ac_rfl) ?_
      wp_done
  · intro evs_d1 s3 hevs_d1 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hsp3, htr3, hvregs_3⟩
    refine seq_clean_evs (mid := (blkPl_349).base + 364#64)
      (P_evs := fun evs_d2 sm =>
        (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          polyDecoderAt A.repAlloc (s0.sp - 1624#64) receivingEk ∗
          memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 176 ∗
          chunkedCt2SampledAt A.repAlloc (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
          memRegion (s0.sp - 592#64) 528 ∗
          memRegion (s0.sp - 19216#64) 13360 ∗ ct1AckSavedRegs s0) ∗
          A.pool lim (M.stepEvents evs_d2 (M.stepEvents evs_d1 (M.stepEvents evs_enc (M.stepEvents evs_sc (M.stepEvents evs_pre st_0))))) sm ∗
          stackAt (s0.sp - 1760#64) allocHookStack)
      (Q := fun sm => Ct1AckDoneSaved s0 sm (s0.sp - 1760#64) outA ct2Cap ct2Ptr)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hct2 : (ct2Cap == 0#64) = true <;>
        simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine align_pre_st (by simp only [arm64_norm]) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hsp3, htr3, hvregs_3]⟩
      · apply sepWP_evs_dealloc ct2Cap.toNat 1
        wp_steps; wp_apply
        refine align_pre_st (by rw [hsp3]; sep_ac_rfl) ?_
        wp_done
    · intro evs_d2 s4 hevs_d2 hpc4 hrun4 ⟨hx19_4, _hx20_4, _hx21_4, hx24_4, hx25_4, hx26_4, hx27_4, hsp4, htr4, hvregs_4⟩
      have hstep4 :
          M.stepEvents evs_d2 (M.stepEvents evs_d1 (M.stepEvents evs_enc (M.stepEvents evs_sc (M.stepEvents evs_pre st_0)))) =
          M.stepEvents (evs_pre ++ evs_sc ++ evs_enc ++ evs_d1 ++ evs_d2) st_0 := by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      rw [hstep4]
      refine SepWP.fold (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
      wp_conv_pre =>
        rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 520) (b' := outA + 8#64) rfl rfl (by decide),
            ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 64) (b' := outA + 464#64) rfl (by bv_omega) (by decide)]
      refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
      wp_pull_exists
      wp_steps_sync_pool (lsmpl.ρ "memcpy")
      simp only [State.setMem_setMem]
      refine call_memcpy_relocate_cs_pool hmemcpy_raw
        (Relocatable.of_chunkedCt2SampledAt A.repAlloc { uc := outUc, sending_ct2 := sendingCt2 })
        (outA + 8#64) (s0.sp - 1048#64)
        (M.stepEvents (evs_pre ++ evs_sc ++ evs_enc ++ evs_d1 ++ evs_d2) st_0)
        (ret_pc := (blkPl_349).base + 388#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
        (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun4)
        (by simp only [State.sp, arm64_norm, hsp4]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr4])
        (by simp only [Reg.x0, arm64_norm, hx19_4]) (by simp only [Reg.x1, arm64_norm, hsp4])
        (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
        (fun sf5 hpc5 hrun5 hsp5 hcs5 htr5 => ?_)
      rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp_5, hvregs_5⟩
      simp only [arm64_norm, hx19_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4] at hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hfp_5 hvregs_5
      wp_steps_sync_pool (lsmpl.base 264)
      simp only [State.setMem_setMem]
      refine SepWP.fold (ct1Ack_done_outA_recompose A.repAlloc outA outUc sendingCt2 res hres)
        (by sep_focus) ?_
      refine SepWP.fold (ct1Ack_done_stack_1160_rejoin s0.sp) (by sep_focus) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun5) fun hcl_ep => ?_
      have hepilogue := ct1_ack_recv_ek_epilogue_244_placed (F := F) hsortedSet16_raw
        outA stA chunkA chunk receivingEk res st_0
        (evs_pre ++ evs_sc ++ evs_enc ++ evs_d1 ++ evs_d2)
        (PostOut := PostOut)
        (fun evs_ep hevs_ep => by
          have hsc0 : UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩ evs_sc := hevs_sc
          have henc0 : SendCt2EncoderBytesPostEnv ct2.length mac.length evs_enc := hevs_enc
          simpa only [List.append_assoc] using
            hpost evs_sc evs_enc (evs_d1 ++ evs_d2 ++ evs_ep) hsc0 henc0
              ((hevs_d1.append hevs_d2).append hevs_ep))
        s0
      apply ct1AckEk_sepWP_congr_pre
      · refine hepilogue _ R hcl_ep hsp0_align (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · simpa only [arm64_norm] using hrun5
        · simp only [State.sp, arm64_norm, hsp5]
        · simp only [Reg.lr, arm64_norm]
        · simp only [arm64_norm, htr5]
        · simp only [Reg.x0, arm64_norm, hsp5]
        · simp only [arm64_norm, hx24_5]
        · simp only [arm64_norm, hx25_5]
        · simp only [arm64_norm, hx26_5]
        · simp only [arm64_norm, hx27_5]
        · simp only [arm64_norm, hvregs_5]
      · sep_ac_rfl
      · funext sf P_f; simp only [sepExists_sepConj_left, sepConj_assoc]

/-! ## 4. Top-Level Theorems: `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`, 153 insns) -/

set_option maxHeartbeats 1200000 in
private theorem ct1_acknowledged_recv_ek_chunk_placed_core [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {RekPre : List AllocEvent → Prop}
    {OuterPre : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpre_from_pre : ∀ x evs, Ct1AcknowledgedRecvEkChunkPreEnv K x evs → OuterPre x evs)
    (hpre_rek : ∀ x evs_add evs_dec e_r,
      AddChunkSlotsEnv x.st.receiving_ek.pts evs_add →
      DecodedMessageEnv (addChunkTotal x.st.receiving_ek x.chunk) evs_dec →
      RekPre e_r →
      OuterPre x ((evs_add ++ evs_dec) ++ e_r))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K
          (fun _ => RekPre) UnchunkedCt1SentRecvEkPostEnv)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (hdrop : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K
      OuterPre (Ct1AcknowledgedRecvEkChunkPostEnv K) ext := by
  unfold Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  have hmemcpy_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "memcpy") (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy
  have hdealloc_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc
  dsimp only [lsProg_349] at hadd hdec hrecv_ek hsend_ct2 henc hdrop
  simp only [ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv, lsProg_349]
  wpp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, chunkA, st, chunk, res⟩, st_b⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hfit0 : FitsEnv M lim st_b
      (OuterPre
        ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
          s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩) := by
    assumption
  have hfit_add : FitsEnv M lim st_b
      (AddChunkEnv ⟨s0.sp - 1624#64, s0.readReg64 (Reg.gpr 3#5), st.receiving_ek, chunk⟩) :=
    fun evs hevs => hfit0 evs (hpre_from_pre _ evs (Or.inl hevs))
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 (by assumption) (by decide)
  apply of_sepWP_lscro hcro0 (mid := lsmpl.base 419)
  wp_conv_pre =>
    rw [stackAt_1760_entry_split s0.sp]
    unfold chunkedCt1AcknowledgedAt
  refine SepWP.fold (polyDecoderAt_dup_pts_len A.repAlloc
    (s0.readReg64 (Reg.gpr 1#5) + 128#64) st.receiving_ek) (by sep_focus) ?_
  wp_focus_pure; intro h16
  obtain ⟨decoded?, hdm, hcases⟩ := ct1_acknowledged_recv_ek_chunk_elim h16 (by assumption)
  refine SepWP.fold (unchunkedCt1SentAt_extract A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.uc)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (cells_16_unfold (s0.sp - 1760#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_fiveVec (s0.readReg64 (Reg.gpr 1#5)) g_uc st.uc.epoch]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  wp_steps_sync_pool (lsmpl.ρ "memcpy")
  simp only [State.setMem_setMem]
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_fiveVec (s0.readReg64 (Reg.gpr 1#5)) g_uc st.uc.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1760_fiveVec s0.sp g_uc st.uc.epoch).symm)
    (by sep_focus) ?_
  refine call_memcpy_relocate_cs_pool hmemcpy_raw
    (Relocatable.of_polyDecoderAt A.repAlloc st.receiving_ek)
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 1#5) + 128#64) st_b
    (ret_pc := (blkPl_349).base + 96#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps_sync_pool (lsmpl.base 419)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_addChunk (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine ct1AckEk_call_addChunk_cro hadd
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ek chunk st_b
    (by assumption) hfit_add
    (ret_pc := (blkPl_349).base + 108#64) (next_pc := lsmpl.base 418) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx23_1]) (by simp only [Reg.x1, arm64_norm, hx22_1])
    (by sep_focus)
    (fun sf2 evs_add hpc2 hrun2 hsp2 hcs2 htr2 _hacp2 hevs_add hsorted' => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (polyDecoderAt_dup_pts_len A.repAlloc
    (s0.sp - 1624#64) (addChunkTotal st.receiving_ek chunk)) (by sep_focus) ?_
  wp_focus_pure; intro h16_dec1
  have hdec_tot_eq : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = decoded? := by
    have hok := decodedMessage_eq_ok (addChunkTotal st.receiving_ek chunk) h16_dec1 hsorted'
    have hdm' := hdm
    dsimp only [spqrPolyApi] at hdm'
    rw [hok] at hdm'
    exact Except.ok.inj hdm'
  have hfit_dec : FitsEnv M lim (M.stepEvents evs_add st_b)
      (PolyDecoderDecodedMessageEnv
        ⟨s0.sp - 1224#64, s0.sp - 1624#64, addChunkTotal st.receiving_ek chunk, decoded?⟩) := by
    intro e_dec he_dec
    have hevs_add0 : AddChunkSlotsEnv st.receiving_ek.pts evs_add := hevs_add
    have he_dec0 : DecodedMessageEnv (addChunkTotal st.receiving_ek chunk) e_dec := he_dec
    exact ((fitsEvents_append M lim evs_add e_dec st_b).mp
      (hfit0 (evs_add ++ e_dec)
        (hpre_from_pre _ _ (SeqEnv.append hevs_add0 (Or.inl he_dec0))))).2
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_addChunk (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)))
    (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 418)
  simp only [State.setMem_setMem]
  refine ct1AckEk_call_decodedMessage_cro hdec
    (s0.sp - 1224#64) (s0.sp - 1624#64) (addChunkTotal st.receiving_ek chunk) decoded?
    (M.stepEvents evs_add st_b) hsorted' hdm hfit_dec
    (ret_pc := (blkPl_349).base + 120#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hx23_2])
    (by sep_focus)
    (fun sf3 evs_dec hpc3 hrun3 hsp3 hcs3 htr3 hevs_dec hcro3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  rw [← M.stepEvents_append]
  cases decoded? with
  | none =>
    have hpost_none : Ct1AcknowledgedRecvEkChunkPostEnv K
        ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
          s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
        (evs_add ++ evs_dec) := by
      have hevs_add0 : AddChunkSlotsEnv st.receiving_ek.pts evs_add := hevs_add
      have hevs_dec0 : DecodedMessageEnv (addChunkTotal st.receiving_ek chunk) evs_dec := hevs_dec
      exact Or.inl (SeqEnv.append hevs_add0 (Or.inl hevs_dec0))
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    apply ct1AckEk_sepWP_congr_pre
    · exact ct1_ack_recv_ek_none_branch_placed_evs (A := A) (lim := lim) (F := F) hmemcpy_raw
        (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
        st.uc chunk (addChunkTotal st.receiving_ek chunk) g_uc res hcases
        st_b (evs_add ++ evs_dec) hpost_none s0 sf3 R
        (by assumption) hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hvregs_3
    · sep_ac_rfl
    · funext sf P_f
      simp only [sepExists_sepConj_left, satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
  | some decoded =>
    rcases hcases with ⟨ucRes, huc, huc_cases⟩
    have hfit_rek : FitsEnv M lim (M.stepEvents (evs_add ++ evs_dec) st_b) RekPre := by
      intro e_r he_r
      have hevs_add0 : AddChunkSlotsEnv st.receiving_ek.pts evs_add := hevs_add
      have hevs_dec0 : DecodedMessageEnv (addChunkTotal st.receiving_ek chunk) evs_dec := hevs_dec
      have hout_rek : OuterPre
          ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
            s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
          ((evs_add ++ evs_dec) ++ e_r) := by
        simpa only [List.append_assoc] using
          hpre_rek ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
            s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            evs_add evs_dec e_r hevs_add0 hevs_dec0 he_r
      exact ((fitsEvents_append M lim (evs_add ++ evs_dec) e_r st_b).mp
        (hfit0 ((evs_add ++ evs_dec) ++ e_r) hout_rek)).2
    apply of_sepWP_lscl hcro3.1 (mid := lsmpl.base 338)
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    wp_conv_pre => dsimp only [optVecU8At]
    refine SepWP.fold (vecU8_extract_nonNone A.repAlloc (s0.sp - 1224#64) decoded) (by sep_focus) ?_
    wp_pull_exists; rename_i v_dec
    wp_focus_pure; intro _hne_dec
    have hdec_words :
        wordsAt (s0.sp - 1224#64) (vecWordsList v_dec) =
        (((s0.sp - 1224#64) ↦₆₄ v_dec.w0) ∗ ((s0.sp - 1216#64) ↦₆₄ v_dec.w1) ∗
         ((s0.sp - 1208#64) ↦₆₄ v_dec.w2)) := by
      simp only [vecWordsList, wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    wp_conv_pre => rw [hdec_words]; simp only [arm64_norm]
    wp_steps_sync_pool (lsmpl.base 338)
    simp only [State.setMem_setMem]
    refine SepWP.fold (Entails.of_eq hdec_words.symm) (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_pre_recvEk A.repAlloc s0.sp (s0.readReg64 (Reg.gpr 1#5))
      st.uc decoded g_uc v_dec) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)))
      (by sep_focus) ?_
    refine ct1AckEk_call_unchunkedRecvEk_cl_ofPrePostEnv
      (PreEnv := fun _ => RekPre) (PostEnv := UnchunkedCt1SentRecvEkPostEnv) hrecv_ek
      (s0.sp - 592#64) (s0.sp - 1760#64) (s0.sp - 1224#64) st.uc decoded ucRes
      (M.stepEvents (evs_add ++ evs_dec) st_b) huc hfit_rek
      (ret_pc := (blkPl_349).base + 152#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
      (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3)
      (by simp only [State.sp, arm64_norm, hsp3]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hsp3]) (by simp only [Reg.x1, arm64_norm, hsp3])
      (by simp only [Reg.x2, arm64_norm, hx21_3, ‹s0.readReg64 .x2 = st.uc.epoch›])
      (by simp only [Reg.x3, arm64_norm, hsp3])
      (by sep_focus)
      (fun sf4 evs_rek hpc4 hrun4 hsp4 hcs4 htr4 hevs_rek hcl4 => ?_)
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩
    simp only [arm64_norm, hx19_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hvregs_4
    rw [← M.stepEvents_append]
    apply of_sepWP_lscl hcl4 (mid := (blkPl_349).base + 152#64)
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_post_recvEk s0.sp) (by sep_focus) ?_
    apply SepWP.done hpc4 hrun4
    intro hcl4'
    cases ucRes with
    | error e =>
      have hpost_err : ∀ evs_ep, FreeOnlyEvs evs_ep →
          Ct1AcknowledgedRecvEkChunkPostEnv K
            ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
              s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            ((evs_add ++ evs_dec ++ evs_rek) ++ evs_ep) := by
        intro evs_ep hevs_ep
        have hevs_add0 : AddChunkSlotsEnv st.receiving_ek.pts evs_add := hevs_add
        have hevs_dec0 : DecodedMessageEnv (addChunkTotal st.receiving_ek chunk) evs_dec := hevs_dec
        have hevs_rek0 : FreeOnlyEvs evs_rek := hevs_rek
        have hpre_err : Ct1AcknowledgedRecvEkChunkPreEnv K
            ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
              s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            (evs_add ++ evs_dec) :=
          SeqEnv.append hevs_add0 (Or.inl hevs_dec0)
        have hpost_raw : Ct1AcknowledgedRecvEkChunkPostEnv K
            ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
              s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            ((evs_add ++ evs_dec) ++ (evs_rek ++ evs_ep)) :=
          SeqEnv.append hpre_err (hevs_rek0.append hevs_ep)
        simpa only [List.append_assoc] using hpost_raw
      apply SepWPp.of_sepWP_ret
      apply ct1AckEk_sepWP_congr_pre
      · exact ct1_ack_recv_ek_err_branch_placed (F := F) hdrop
          (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
          chunk (addChunkTotal st.receiving_ek chunk) e res huc_cases
          st_b (evs_add ++ evs_dec ++ evs_rek) hpost_err
          s0 sf4 R hcl4' (by assumption) hpc4 hrun4 hsp4 htr4
          hx19_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · sep_ac_rfl
      · funext sf P_f
        simp only [sepExists_sepConj_left, satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
    | ok uc1 =>
      rcases huc_cases with ⟨outUc, ct2, mac, sendingCt2, hsc_ok, henc_ok, hres⟩
      have hevs_add0 : AddChunkSlotsEnv st.receiving_ek.pts evs_add := hevs_add
      have hevs_dec0 : DecodedMessageEnv (addChunkTotal st.receiving_ek chunk) evs_dec := hevs_dec
      have hevs_rek0 : FreeOnlyEvs evs_rek := hevs_rek
      have huc_ok : st.uc.recv_ek K st.uc.epoch decoded = .ok uc1 := huc
      have htail_of : ∀ {e_tail : List AllocEvent},
          SeqEnv (UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩)
            (SendCt2EncoderBytesPreEnv ct2.length mac.length) e_tail →
          Ct1AckRecvEkTailPreEnv K st.uc
            (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
            (evs_rek ++ e_tail) := by
        intro e_tail he_tail
        rw [hdec_tot_eq]
        simp only [Ct1AckRecvEkTailPreEnv, huc_ok, hsc_ok]
        exact SeqEnv.append hevs_rek0 he_tail
      have hfit_tail : FitsEnv M lim (M.stepEvents (evs_add ++ evs_dec ++ evs_rek) st_b)
          (SeqEnv (UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩)
            (SendCt2EncoderBytesPreEnv ct2.length mac.length)) := by
        intro e_tail he_tail
        have hpre_raw : Ct1AcknowledgedRecvEkChunkPreEnv K
            ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
              s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            (evs_add ++ (evs_dec ++ (evs_rek ++ e_tail))) :=
          SeqEnv.append hevs_add0 (SeqEnv.append hevs_dec0 (htail_of he_tail))
        have hpre_tail : Ct1AcknowledgedRecvEkChunkPreEnv K
            ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
              s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            ((evs_add ++ evs_dec ++ evs_rek) ++ e_tail) := by
          simpa only [List.append_assoc] using hpre_raw
        exact ((fitsEvents_append M lim (evs_add ++ evs_dec ++ evs_rek) e_tail st_b).mp
          (hfit0 _ (hpre_from_pre _ _ hpre_tail))).2
      have hpost_done : ∀ evs_sc evs_enc evs_free,
          UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩ evs_sc →
          SendCt2EncoderBytesPostEnv ct2.length mac.length evs_enc →
          FreeOnlyEvs evs_free →
          Ct1AcknowledgedRecvEkChunkPostEnv K
            ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
              s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
            ((evs_add ++ evs_dec ++ evs_rek) ++ evs_sc ++ evs_enc ++ evs_free) := by
        intro evs_sc evs_enc evs_free hevs_sc hevs_enc hevs_free
        rcases hevs_enc with henc_p | ⟨e_enc_p, e_enc_f, rfl, henc_p, henc_f⟩
        · have hpre_ok : Ct1AcknowledgedRecvEkChunkPreEnv K
              ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
                s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
              (evs_add ++ (evs_dec ++ (evs_rek ++ (evs_sc ++ evs_enc)))) :=
            SeqEnv.append hevs_add0
              (SeqEnv.append hevs_dec0 (htail_of (SeqEnv.append hevs_sc henc_p)))
          have hpost_raw : Ct1AcknowledgedRecvEkChunkPostEnv K
              ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
                s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
              ((evs_add ++ (evs_dec ++ (evs_rek ++ (evs_sc ++ evs_enc)))) ++ evs_free) :=
            SeqEnv.append hpre_ok hevs_free
          simpa only [List.append_assoc] using hpost_raw
        · have hpre_ok : Ct1AcknowledgedRecvEkChunkPreEnv K
              ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
                s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
              (evs_add ++ (evs_dec ++ (evs_rek ++ (evs_sc ++ e_enc_p)))) :=
            SeqEnv.append hevs_add0
              (SeqEnv.append hevs_dec0 (htail_of (SeqEnv.append hevs_sc henc_p)))
          have hpost_raw : Ct1AcknowledgedRecvEkChunkPostEnv K
              ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
                s0.readReg64 (Reg.gpr 3#5), st, chunk, res⟩
              ((evs_add ++ (evs_dec ++ (evs_rek ++ (evs_sc ++ e_enc_p)))) ++ (e_enc_f ++ evs_free)) :=
            SeqEnv.append hpre_ok (henc_f.append hevs_free)
          simpa only [List.append_assoc] using hpost_raw
      apply ct1AckEk_sepWPp_congr_pre
      · exact ct1_ack_recv_ek_done_branch_placed (F := F) (K := K)
          hsend_ct2 henc hdealloc_raw hmemcpy_raw hdrop
          (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
          chunk (addChunkTotal st.receiving_ek chunk)
          uc1 outUc ct2 mac sendingCt2 res hsc_ok henc_ok hres
          st_b (evs_add ++ evs_dec ++ evs_rek) hfit_tail hpost_done
          s0 sf4 R hcl4' (by assumption) hpc4 hrun4 hsp4 htr4
          hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · sep_ac_rfl
      · funext sf P_f
        simp only [sepExists_sepConj_left, satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]

private theorem ct1AckEk_mono_prePost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {Pre1 Post1 Pre2 Post2 : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpre : ∀ x st, FitsEnv M lim st (Pre2 x) → FitsEnv M lim st (Pre1 x))
    (hpost : ∀ x evs, Post1 x evs → Post2 x evs)
    (hok : Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K Pre1 Post1 ext) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K Pre2 Post2 ext := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hp
    dsimp only [ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv] at hpre0
    dsimp only [withLsCodeRoLoaded, ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨h0, h1, h2, h3, hsort, hok_st, hfit⟩, hmem⟩
    exact ⟨⟨h0, h1, h2, h3, hsort, hok_st, hpre x st hfit⟩, hmem⟩
  · dsimp only [withLsCodeRoLoaded, ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hpost x evs hq.1.2⟩, hq.2⟩

private theorem b2_recv_ek_to_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl
      (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentRecvEkSpec M A lim F K))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl
      (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K (fun _ => FreeOnlyEvs) UnchunkedCt1SentRecvEkPostEnv)) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)

/-- `[LibsignalPlacement]` contract for Block `349` (`Ct1Acknowledged::recv_ek_chunk`) with `hdrop`. -/
theorem ct1_acknowledged_recv_ek_chunk_placed_cl_ext_of_drop [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (hdrop : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX M A lim F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_core (RekPre := (· = [])) (fun _ _ h => h)
    (by rintro x evs_add evs_dec _ hevs_add hevs_dec rfl; rw [List.append_nil]; exact SeqEnv.append hevs_add (Or.inl hevs_dec))
    hdealloc hmemcpy hadd hdec hrecv_ek hsend_ct2 henc hdrop

/-- `[LibsignalPlacement]` budget contract for Block `349` (`Ct1Acknowledged::recv_ek_chunk`), discharging Block `264`. -/
theorem ct1_acknowledged_recv_ek_chunk_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX M A lim F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext_of_drop hdealloc hmemcpy hadd hdec hrecv_ek hsend_ct2 henc
    (ls_subroutine_ok_of_block (i := 349) (j := 264) (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_glue_sorted_set_pt16_placed_ok (spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc))))

theorem ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpre_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPreEnv K x evs → PreEnv x evs)
    (hpost_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPostEnv K x evs → PostEnv x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K PreEnv PostEnv ext :=
  ct1AckEk_mono_prePost (fun x _ hfit => FitsEnv.mono (hpre_sub x) hfit) hpost_sub
    (ct1_acknowledged_recv_ek_chunk_placed_cl_ext (F := F) (K := K) hdealloc hmemcpy hadd hdec hrecv_ek hsend_ct2 henc)

theorem ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} {Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpost_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPostEnv K x evs → Env x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv M A lim F K Env ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext_ofPrePostEnv
    (fun x evs h => hpost_sub x evs (Or.inl h)) hpost_sub hdealloc hmemcpy hadd hdec hrecv_ek hsend_ct2 henc

/-- Closed-callee single-envelope (`Env`) contract for Block `349`, discharging Blocks `338`, `382`, `264`. -/
theorem ct1_acknowledged_recv_ek_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} {Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hpost_sub : ∀ x evs, Ct1AcknowledgedRecvEkChunkPostEnv K x evs → Env x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (withVmPreserved (mlkemValidatePkSpec K)))
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv M A lim F K Env ext :=
  ct1AckEk_mono_prePost (fun x _ hfit => FitsEnv.mono (hpost_sub x) hfit) hpost_sub
    (ct1_acknowledged_recv_ek_chunk_placed_core (RekPre := FreeOnlyEvs) (fun _ _ h => Or.inl h)
      (fun _ _ _ _ hadd0 hdec0 hfree => SeqEnv.append (SeqEnv.append hadd0 (Or.inl hdec0)) hfree)
      hdealloc hmemcpy hadd hdec
      (ls_subroutine_ok_of_block (i := 349) (j := 338) (b2_recv_ek_to_placed (unchunked_ct1_sent_recv_ek_placed_cl_ok_x (F := F) hdealloc hval_pk)))
      hsend_ct2
      (ls_subroutine_ok_of_block (i := 349) (j := 382) (send_ct2_encoder_placed_ok_x h_panic hshim halloc hrealloc hdealloc hmemcpy))
      (ls_subroutine_ok_of_block (i := 349) (j := 264) (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok (spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc)))))

theorem ct1_acknowledged_recv_ek_chunk_placed_ok_x_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (withVmPreserved (mlkemValidatePkSpec K)))
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv M A lim F K (Ct1AcknowledgedRecvEkChunkEnv K) ext :=
  ct1_acknowledged_recv_ek_chunk_placed_ok_x_ofEnv (fun _ _ h => h)
    h_panic hshim halloc hrealloc hdealloc hmemcpy hval_pk hadd hdec hsend_ct2

/-- Two-envelope (`PreEnv` / `PostEnv`) closed-callee contract for Block `349`. -/
theorem ct1_acknowledged_recv_ek_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    (hfit_free : ∀ (x : Ct1AcknowledgedRecvEkChunkGhost F) st,
      FitsEnv M lim st (@Ct1AcknowledgedRecvEkChunkPreEnv F K x) →
      FitsEnv M lim st (@Ct1AcknowledgedRecvEkChunkPostEnv F K x))
    (hpre_sub : ∀ (x : Ct1AcknowledgedRecvEkChunkGhost F) evs,
      @Ct1AcknowledgedRecvEkChunkPreEnv F K x evs → PreEnv x evs)
    (hpost_sub : ∀ (x : Ct1AcknowledgedRecvEkChunkGhost F) evs,
      @Ct1AcknowledgedRecvEkChunkPostEnv F K x evs → PostEnv x evs)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (withVmPreserved (mlkemValidatePkSpec K)))
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K PreEnv PostEnv ext :=
  ct1AckEk_mono_prePost (fun x st hfit => hfit_free x st (FitsEnv.mono (hpre_sub x) hfit)) hpost_sub
    (ct1_acknowledged_recv_ek_chunk_placed_ok_x_env h_panic hshim halloc hrealloc hdealloc hmemcpy hval_pk hadd hdec hsend_ct2)

theorem ct1_acknowledged_recv_ek_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hfit_free : ∀ (x : Ct1AcknowledgedRecvEkChunkGhost F) st,
      FitsEnv M lim st (@Ct1AcknowledgedRecvEkChunkPreEnv F K x) →
      FitsEnv M lim st (@Ct1AcknowledgedRecvEkChunkPostEnv F K x))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (withVmPreserved (mlkemValidatePkSpec K)))
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext)) (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX M A lim F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_ok_x_ofPrePostEnv hfit_free (fun _ _ h => h) (fun _ _ h => h)
    h_panic hshim halloc hrealloc hdealloc hmemcpy hval_pk hadd hdec hsend_ct2

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkPlacedBudget
