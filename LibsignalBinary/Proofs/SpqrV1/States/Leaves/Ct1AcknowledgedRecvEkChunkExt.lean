/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk`: `.inImage` & `StatesRecvContractsAx`

Verifies the native-stack (`19216` B) `.inImage img` contract `ct1_acknowledged_recv_ek_chunk_ok_inImage`
and the `35936` B `growToCalleeExt` contract `ct1_acknowledged_recv_ek_chunk_ok_ax`
(`StatesRecvContractsAx.ct1AcknowledgedRecvEkChunk_ok`).
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn allocHookStack rustDeallocSpec vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (AllocContractsX ImgCallInv extHookStack session2MemcpySpecX sub_ok_at_of_fnAddr
   tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk Error Mac MlKem PolyDecoder PolyEncoder StatesResult spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Acknowledged Ct1AcknowledgedRecvChunk Ct2Sampled send_ct2_encoder)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1Sent Ct1SentEkReceived Ct2Sent)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (AddChunkOkX PolyDecoderStrictSorted addChunkSpecX addChunkStackX addChunkTotal)
open CryptoVerification.SpqrV1.Drop
  (DeallocOkExt align_pre chunkedCt1AcknowledgedAt chunkedCt2SampledAt
   dropGlueSortedSetPt16Spec dropProgAtExt dropSortedSetPt16Name
   drop_glue_sorted_set_pt16_ok_ext seq_clean unchunkedCt1SentAt
   unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.States.Leaves
  (AuthWords Ct1AckDoneSaved FiveVecWords Relocatable Relocatable.of_chunkedCt2SampledAt
   Relocatable.of_polyDecoderAt VecWords authWordsList bv_sub_sub cells_15_unfold
   cells_16_unfold cells_1_unfold cells_3_unfold cells_7_unfold cells_8_unfold
   ct1AckSavedRegs ct1AckEk_sepWP_congr_pre ct1AckEk_sepWPp_congr_pre
   ct1Ack_done_outA_recompose ct1Ack_done_scratch_join ct1Ack_done_stack_1160_rejoin
   ct1Ack_done_uc1_copy_recompose ct1Ack_done_uc56_and_headers_recompose
   ct1Ack_none_outA_recompose ct1Ack_none_stack_rejoin ct1Ack_some_post_recvEk
   ct1Ack_some_pre_recvEk ct1AcknowledgedRecvEkChunkName ct1AcknowledgedRecvEkChunkResAt
   ct1AcknowledgedRecvEkChunkSpec ct1AcknowledgedRecvEkChunkStack
   ct1AcknowledgedRecvEkChunk_fnOff ct1_ack_recv_ek_epilogue_244 ct1_ack_recv_ek_err_branch
   ct1_acknowledged_recv_ek_chunk_elim ct2SentWordsList dec_slice_400_combine
   dec_slice_400_split_dst dec_slice_400_split_src fiveVecTail15 fiveVecWordsList
   fold_ct1AckSavedRegs leavesProgAtExt length_fiveVecTail15 length_wordsBytes optVecU8At
   polyDecoderAt_dup_pts_len polyDecoderAt_extract_336_64 polyDecoderDecodedMessageName
   polyDecoderDecodedMessageSpec polyDecoderDecodedMessageStack relocate_post_entails
   relocate_pre_entails relocatedHeap sendCt2EncoderName sendCt2EncoderSpec
   sendCt2EncoderStack slice_and_tail_entails_vecCapPtrDealloc stackAt_1760_entry_split
   stackAt_sendCt2Encoder_eq_allocHook stackAt_sendCt2Encoder_eq_decodedMessage
   stackAt_sendCt2Encoder_eq_unchunkedRecvEk stackAt_sendCt2Encoder_eq_unchunkedSendCt2
   tail15_and_bs1_combine unchunkedCt1SentAt_extract
   unchunkedCt1SentEkReceivedAt_extract_nonNone unchunkedCt1SentEkReceivedSendCt2Name
   unchunkedCt1SentEkReceivedSendCt2Spec unchunkedCt1SentRecvEkName
   unchunkedCt1SentRecvEkResAt unchunkedCt1SentRecvEkSpec unchunkedCt2SentAt_extract
   unchunkedRecvEkStack unchunkedSendCt2RoAt unchunkedSendCt2Stack
   vecU8_entails_slice_and_tail vecU8_extract_nonNone vecWordsList wordsAt wordsAt_16
   wordsAt_7 wordsAt_8 wordsAt_cons_off wordsAt_entails_memRegion wordsAt_fiveVec
   wordsAt_nil wordsAt_sp1176_fiveVec wordsAt_sp1760_fiveVec wordsAt_sp592_fiveVec
   wordsAt_sp592_fiveVecTail15 wordsBytes)
open CryptoVerification.SpqrV1.States.Recv
  (growToCalleeExt sessionMemcpyRegionSpecAx session_memcpy_region_ok_at_ax
   sub_ok_inImage_growToCalleeExt_ax)

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff addChunkTotal
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem ct1AckEkExt_trace_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := rfl

@[local arm64_norm, local wp_norm]
private theorem hsp_add_8 (s₀ : State) :
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s₀ + 8#64 = s₀.sp - 680#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm]
private theorem hsp_592_add_8 (s₀ : State) :
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s₀ + 592#64) + 8#64 = s₀.sp - 88#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm]
private theorem esp_add_8 (s₀ : State) :
    CryptoVerification.LibsignalTripleRatchet.Expand.esp s₀ + 8#64 = s₀.sp - 488#64 := by
  unfold CryptoVerification.LibsignalTripleRatchet.Expand.esp; bv_omega

gen_decodes libsignalSessionCode_tree spqrCt1AcknowledgedRecvEkChunk4KBin [
  0x595d0 → 0x59834
]

/-! ## 1. Stack Layout Helpers for `addChunkStackX` (`16480` B) & `extHookStack` (`16384` B) -/

private theorem stackAt_sendCt2Encoder_eq_addChunkX (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 976 ∗ stackAt fsp addChunkStackX := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 976 ∗ memRegion (fsp - 16480#64) 16480
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 976) (k := 16480) (b' := fsp - 16480#64) rfl (by bv_omega) (by decide)

private theorem stackAt_sendCt2Encoder_eq_extHook (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 1072 ∗ stackAt fsp extHookStack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 1072 ∗ memRegion (fsp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 1072) (k := 16384) (b' := fsp - 16384#64) rfl (by bv_omega) (by decide)

/-! ## 2. `.inImage img` Invariant & Framed Call Helpers -/

private structure Ct1AckInv (img : Obj.Image) (s : State) : Prop where val : ImgCallInv img s

private theorem sepWPp_of_inv {img : Obj.Image} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} (hinv : Ct1AckInv img s)
    (h : SepWP prog mid s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem sepWP_of_inv {img : Obj.Image} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} (hinv : Ct1AckInv img s)
    (h : SepWP prog mid s P (fun sm Pm => Ct1AckInv img sm → SepWP prog ret sm Pm Q)) :
    SepWP prog ret s P Q :=
  CryptoVerification.SepWP.of_sepWP_inv hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem call_memcpy_relocate_cs_inImage {img : Obj.Image} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    {n : Nat} {R : BitVec 64 → SepProp} (hrel : Relocatable n R) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src) (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ R src ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace → Ct1AckInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf ((R dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun; intro hinv
  have hsplit' : P = (memRegion dst n ∗ R src) ∗ (stackAt sp_call extHookStack ∗ Frame) := by rw [hsplit]; sep_ac_rfl
  rw [hsplit']; refine SepWP.fold (relocate_pre_entails hrel dst src (stackAt sp_call extHookStack ∗ Frame)) (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs; refine SepWP.pure_elim fun hlen => ?_
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := (dst, src, bs)) (F := relocatedHeap R bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, hlen]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hreord : ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗ (relocatedHeap R bs ∗ Frame) =
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap R bs ∗ (stackAt sp_call extHookStack ∗ Frame))) := by sep_ac_rfl
    rw [hreord]; refine SepWP.fold (relocate_post_entails dst src hlen (stackAt sp_call extHookStack ∗ Frame)) (sepConj_emp _).symm ?_
    rw [sepConj_emp]; exact ct1AckEk_sepWP_congr_pre
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩) (by sep_ac_rfl) rfl

private theorem call_memcpy_relocate_cs_p_inImage {img : Obj.Image} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    {n : Nat} {R : BitVec 64 → SepProp} (hrel : Relocatable n R) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R_post : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src) (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ R src ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog next_pc sf ((R dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame)
        (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R_post) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R_post)))) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R_post) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R_post))) := by
  apply SepWP.done hpc hrun; intro hinv; apply SepWPp.of_sepWP (mid := ret_pc)
  have hsplit' : P = (memRegion dst n ∗ R src) ∗ (stackAt sp_call extHookStack ∗ Frame) := by rw [hsplit]; sep_ac_rfl
  rw [hsplit']; refine SepWP.fold (relocate_pre_entails hrel dst src (stackAt sp_call extHookStack ∗ Frame)) (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs; refine SepWP.pure_elim fun hlen => ?_
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := (dst, src, bs)) (F := relocatedHeap R bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, hlen]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hreord : ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗ (relocatedHeap R bs ∗ Frame) =
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap R bs ∗ (stackAt sp_call extHookStack ∗ Frame))) := by sep_ac_rfl
    rw [hreord]; refine SepWP.fold (relocate_post_entails dst src hlen (stackAt sp_call extHookStack ∗ Frame)) (sepConj_emp _).symm ?_
    rw [sepConj_emp]; apply SepWP.done hpc_sf hrun_sf; refine sepWPp_of_inv (mid := next_pc) ⟨hinv_sf⟩ ?_
    exact ct1AckEk_sepWP_congr_pre
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)) (by sep_ac_rfl) rfl

private theorem call_memcpy_bytes_cs_inImage {img : Obj.Image} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    (dst src : BitVec 64) (bs : List (BitVec 8)) {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src) (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs) ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace → Ct1AckInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun; intro hinv; rw [hsplit]
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX, memcpyRegionSpec]
    rw [hlen, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact ct1AckEk_sepWP_congr_pre
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩) (by sep_ac_rfl) rfl

private theorem call_addChunkX_mid_inImage {img : Obj.Image} {A : RustAlloc} {prog : Program}
    {entry ret_pc next_pc : BitVec 64} (hcall : subroutine_ok prog entry ((addChunkSpecX A).inImage img))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk) (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗ A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace → PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗ A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [addChunkSpecX]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]; refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [addChunkSpecX]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => sepWPp_of_inv (mid := next_pc) ⟨hinv_sf⟩ ?_
    have hassoc : (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
        A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
      (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ (chunkAt chunkA chunk ∗
        (A.pool ∗ stackAt sp_call addChunkStackX))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

private theorem call_decodedMessage_p_inImage {img : Obj.Image} {A : RustAlloc} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((polyDecoderDecodedMessageSpec A img.base).inImage img))
    (hb : img.base &&& 0xfff#64 = 0#64) (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec) (hdm : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = outA) (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗ tokenInitAt img.base ∗
      reduceTableAt img.base ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace → Ct1AckInv img sf →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗ tokenInitAt img.base ∗
          reduceTableAt img.base ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [polyDecoderDecodedMessageSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hb, hx8, hx0, hsorted, hdm⟩, hm⟩
  · rw [← sepConj_assoc]; refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [polyDecoderDecodedMessageSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hassoc : (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗ tokenInitAt img.base ∗
        reduceTableAt img.base ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
      (optVecU8At A outA outMsg ∗ (polyDecoderAt A decA dec ∗ (tokenInitAt img.base ∗
        (reduceTableAt img.base ∗ (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

private theorem call_unchunkedRecvEk_p_inImage {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((unchunkedCt1SentRecvEkSpec A F K).inImage img))
    (outA stA ekA : BitVec 64) (st : Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (ucRes : Except Error (Ct1SentEkReceived (spqrAuthApi F)))
    (hrecv : st.recv_ek K st.epoch ek = StatesResult.ofError ucRes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.epoch) (hx3 : s.readReg64 Reg.x3 = ekA)
    (hsplit : P = (memRegion outA 128 ∗ unchunkedCt1SentAt A stA st ∗ vecU8 A ekA ek ∗
      A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog next_pc sf
        ((unchunkedCt1SentRecvEkResAt A outA ucRes ∗ memRegion stA 128 ∗ memRegion ekA 24 ∗
          A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame)
        (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv; apply SepWPp.of_sepWP (mid := ret_pc); rw [hsplit]
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := ⟨outA, stA, ekA, st, ek, ucRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; dsimp only [unchunkedCt1SentRecvEkSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, hm⟩
  · dsimp only [unchunkedCt1SentRecvEkSpec]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_; apply SepWP.done hpc_sf hrun_sf
    refine sepWPp_of_inv (mid := next_pc) ⟨hinv_sf⟩ ?_
    have hassoc : (unchunkedCt1SentRecvEkResAt A outA ucRes ∗ memRegion stA 128 ∗
        memRegion ekA 24 ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame =
      (unchunkedCt1SentRecvEkResAt A outA ucRes ∗ (memRegion stA 128 ∗
        (memRegion ekA 24 ∗ (A.pool ∗ stackAt sp_call unchunkedRecvEkStack)))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

private theorem call_sendCt2_inImage {A : RustAlloc} {F : ShaCompress} {K : MlKem} {img : Obj.Image}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hb : img.base &&& 0xfff#64 = 0#64) (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F)) (outUc : Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = Except.ok (outUc, ct2, mac))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A stA st ∗
      unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗ vecU8 A (outA + 80#64) mac ∗
          memRegion stA 128 ∗ unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨outA, stA, st, outUc, ct2, mac⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hb, hx0, hx1, hsc⟩, hm⟩
  · rw [← sepConj_assoc]; refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => sepWPp_of_inv (mid := next_pc) ⟨hinv_sf⟩ ?_
    have hassoc : (unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
        vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗ unchunkedSendCt2RoAt img.base ∗
        A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
      (unchunkedCt2SentAt A outA outUc ∗ (vecU8 A (outA + 56#64) ct2 ∗
        (vecU8 A (outA + 80#64) mac ∗ (memRegion stA 128 ∗ (unchunkedSendCt2RoAt img.base ∗
          (A.pool ∗ stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

private theorem call_sendCt2Encoder_inImage {A : RustAlloc} {img : Obj.Image} {prog : Program}
    {entry ret_pc : BitVec 64} (hcall : subroutine_ok prog entry ((sendCt2EncoderSpec A).inImage img))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = Except.ok enc)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace → Ct1AckInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post) :
    SepWP prog entry s P (fun sm Pm => Ct1AckInv img sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [sendCt2EncoderSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc⟩, hm⟩
  · rw [← sepConj_assoc]; refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [sendCt2EncoderSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_; apply SepWPp.of_sepWP_ret
    have hassoc : (polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
        A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
      (polyEncoderAt A outA enc ∗ ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
        (A.pool ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

/-! ## 3. Branch `decoded? = none` (`+0x078..+0x228`) under `.inImage img` -/

set_option maxHeartbeats 1200000 in
private theorem ct1_ack_recv_ek_none_branch_inImage {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img))
    (outA stA chunkA : BitVec 64) (uc : Ct1Sent (spqrAuthApi F))
    (chunk : Chunk) (receivingEk : PolyDecoder) (g_uc : FiveVecWords)
    (res : Except Error (Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .ok (.stillReceiving { uc := uc, receiving_ek := receivingEk }))
    (s0 s : State) (R : SepProp) (hsp0_align : s0.spAligned = true) (hinv : Ct1AckInv img s)
    (hpc : s.pc = (leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA) (hx20 : s.readReg64 (Reg.gpr 20#5) = stA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (leavesProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗
        wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ∗
        relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
          (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ∗
        chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt img.base ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗
        wordsAt (s0.sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
        memRegion (s0.sp - 1632#64) 8 ∗ polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        optVecU8At A (s0.sp - 1224#64) none ∗ memRegion (s0.sp - 1200#64) 1136 ∗
        ct1AckSavedRegs s0 ∗ A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt img.base ∗
            tokenInitAt img.base ∗ reduceTableAt img.base ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  code_fetches CryptoVerification.libsignalSessionCode spqrCt1AcknowledgedRecvEkChunk4KBin img.base
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 0x595d0 612
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, ct1AcknowledgedRecvEkChunkName,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_extHook (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))
    hinv ?_
  wp_conv_pre =>
    dsimp only [optVecU8At]
    rw [ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 152) (k := 984) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 456) (k := 528) (b' := s0.sp - 592#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 592#64) (n := 120) (k := 408) (b' := s0.sp - 472#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 472#64) (n := 400) (k := 8) (b' := s0.sp - 72#64) rfl (by bv_omega) (by decide)]
  wp_steps
  have h1224_fold :
      ((s0.sp - 1224#64) ↦₆₄ noneCap) ∗ memRegion ((s0.sp - 1224#64) + 8#64) 16 ⊢
      memRegion (s0.sp - 1224#64) 24 := by
    refine Entails.trans (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (s0.sp - 1224#64) noneCap)) ?_
    rw [← ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 8) (k := 16) (b' := (s0.sp - 1224#64) + 8#64) rfl rfl (by decide)]
    exact Entails.refl _
  refine SepWP.fold h1224_fold (by sep_focus) ?_
  refine SepWP.fold (polyDecoderAt_extract_336_64 A (s0.sp - 1624#64) receivingEk) (by sep_focus) ?_
  wp_pull_exists; rename_i bs1 d0 d1 d2 d3 d4 d5 d6 d7
  wp_focus_pure; intro hbs1
  refine SepWP.fold (Entails.of_eq (dec_slice_400_combine (s0.sp - 1624#64) bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7))
    (by sep_focus) ?_
  have hlen400 : (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]).length = 400 := by simp [hbs1]
  refine call_memcpy_bytes_cs_inImage hmemcpy_raw (s0.sp - 472#64) (s0.sp - 1624#64)
    (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]) hlen400
    (ret_pc := entry + 412#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx23, hx24, hx25, hx26, hx27, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))
    hinv1 ?_
  refine SepWP.fold (dec_slice_400_split_dst s0.sp bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  refine SepWP.fold (dec_slice_400_split_src s0.sp bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  refine SepWP.fold (cells_15_unfold (s0.sp - 592#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_fiveVec stA g_uc uc.epoch, wordsAt_sp1760_fiveVec s0.sp g_uc uc.epoch]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  wp_conv_pre => unfold CryptoVerification.LibsignalTripleRatchet.Expand.esp
  refine SepWP.fold (Entails.of_eq (wordsAt_fiveVec stA g_uc uc.epoch).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1760_fiveVec s0.sp g_uc uc.epoch).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVecTail15 s0.sp g_uc uc.epoch).symm) (by sep_focus) ?_
  have hstA_528 :
      wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ⊢
      memRegion stA 528 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ stA 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := stA) (n := 128) (k := 400) (b' := stA + 128#64) rfl rfl (by decide)]
    exact Entails.refl _
  have hsp1760_136 :
      wordsAt (s0.sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (s0.sp - 1632#64) 8 ⊢
      memRegion (s0.sp - 1760#64) 136 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ (s0.sp - 1760#64) 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := s0.sp - 1760#64) (n := 128) (k := 8) (b' := s0.sp - 1632#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWP.fold hstA_528 (by sep_focus) ?_
  refine SepWP.fold hsp1760_136 (by sep_focus) ?_
  refine SepWP.fold (tail15_and_bs1_combine s0.sp uc g_uc bs1) (by sep_focus) ?_
  have hlen456 : (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1).length = 456 := by
    rw [List.length_append, length_wordsBytes, length_fiveVecTail15, hbs1]
  refine call_memcpy_bytes_cs_inImage hmemcpy_raw (s0.sp - 1048#64) (s0.sp - 592#64)
    (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1) hlen456
    (ret_pc := entry + 496#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))
    hinv2 ?_
  have h592_mem :
      ((s0.sp - 592#64) ↦ₛ (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1)) ⊢
      memRegion (s0.sp - 592#64) 456 := by
    rw [← hlen456]; exact pointsToBytes_entails_memRegion (s0.sp - 592#64) _
  refine SepWP.fold h592_mem (by sep_focus) ?_
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 520) (b' := outA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 64) (b' := outA + 464#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
  wp_pull_exists
  wp_steps
  refine call_memcpy_bytes_cs_inImage hmemcpy_raw (outA + 8#64) (s0.sp - 1048#64)
    (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1) hlen456
    (ret_pc := entry + 516#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 _ => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_extHook (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  have h1048_mem :
      ((s0.sp - 1048#64) ↦ₛ (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1)) ⊢
      memRegion (s0.sp - 1048#64) 456 := by
    rw [← hlen456]; exact pointsToBytes_entails_memRegion (s0.sp - 1048#64) _
  refine SepWP.fold h1048_mem (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (outA + 464#64)) (by sep_focus) ?_
  wp_pull_exists
  have hd_1288 :
      wordsAt (s0.sp - 1288#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (((s0.sp - 1288#64) ↦₆₄ d0) ∗ ((s0.sp - 1280#64) ↦₆₄ d1) ∗
       ((s0.sp - 1272#64) ↦₆₄ d2) ∗ ((s0.sp - 1264#64) ↦₆₄ d3) ∗
       ((s0.sp - 1256#64) ↦₆₄ d4) ∗ ((s0.sp - 1248#64) ↦₆₄ d5) ∗
       ((s0.sp - 1240#64) ↦₆₄ d6) ∗ ((s0.sp - 1232#64) ↦₆₄ d7)) := by
    simp only [wordsAt_8, arm64_norm]
  have hd_out464 :
      wordsAt (outA + 464#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (((outA + 464#64) ↦₆₄ d0) ∗ ((outA + 472#64) ↦₆₄ d1) ∗
       ((outA + 480#64) ↦₆₄ d2) ∗ ((outA + 488#64) ↦₆₄ d3) ∗
       ((outA + 496#64) ↦₆₄ d4) ∗ ((outA + 504#64) ↦₆₄ d5) ∗
       ((outA + 512#64) ↦₆₄ d6) ∗ ((outA + 520#64) ↦₆₄ d7)) := by
    simp only [wordsAt_8, BitVec.add_assoc, arm64_norm]
  wp_conv_pre =>
    unfold ct1AckSavedRegs
    rw [hd_1288]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hd_1288.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hd_out464.symm) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_none_outA_recompose A outA uc receivingEk g_uc bs1 hbs1
    d0 d1 d2 d3 d4 d5 d6 d7 res hres) (by sep_focus) ?_
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_none_stack_rejoin s0 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  wp_done

/-! ## 4. Done Branch (`+0x098..+0x184`) under `.inImage img` -/

set_option maxHeartbeats 1600000 in
private theorem ct1_ack_recv_ek_done_branch_inImage {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hsendCt2_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709550136#64)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 20832#64)
      ((sendCt2EncoderSpec A).inImage img))
    (hdealloc_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A))
    (hmemcpy_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img))
    (hsortedSet16_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
      (dropGlueSortedSetPt16Spec A))
    (outA stA chunkA : BitVec 64) (chunk : Chunk) (receivingEk : PolyDecoder)
    (uc1 : Ct1SentEkReceived (spqrAuthApi F)) (outUc : Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (sendingCt2 : PolyEncoder)
    (res : Except Error (Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hsc_ok : uc1.send_ct2 K = .ok (outUc, ct2, mac))
    (henc_ok : send_ct2_encoder spqrPolyApi ct2 mac = .ok sendingCt2)
    (hres : res = .ok (.done { uc := outUc, sending_ct2 := sendingCt2 }))
    (s0 s : State) (R : SepProp) (hsp0_align : s0.spAligned = true) (hinv : Ct1AckInv img s)
    (hpc : s.pc = (leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (leavesProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 632 ∗
        unchunkedCt1SentRecvEkResAt A (F := F) (s0.sp - 592#64) (.ok uc1) ∗
        memRegion (s0.sp - 464#64) 400 ∗ ct1AckSavedRegs s0 ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt img.base ∗
            tokenInitAt img.base ∗ reduceTableAt img.base ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  have hepilogue := ct1_ack_recv_ek_epilogue_244 (F := F) hsortedSet16_raw
    outA stA chunkA chunk receivingEk res s0
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches CryptoVerification.libsignalSessionCode spqrCt1AcknowledgedRecvEkChunk4KBin img.base
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 0x595d0 612
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, ct1AcknowledgedRecvEkChunkName,
    BitVec.ofNat_eq_ofNat] at hsendCt2_raw hsendCt2Enc_raw hdealloc_raw hmemcpy_raw hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  refine sepWPp_of_inv (mid := entry + 18446744073709550136#64) hinv ?_
  wp_conv_pre =>
    dsimp only [unchunkedCt1SentRecvEkResAt]
    rw [ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 24) (k := 608) (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 24) (k := 584) (b' := s0.sp - 1176#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1176#64) (n := 128) (k := 456) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 400) (k := 56) (b' := s0.sp - 648#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (unchunkedCt1SentEkReceivedAt_extract_nonNone A (s0.sp - 592#64) uc1)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc1
  wp_focus_pure; intro hne_uc1
  refine SepWP.fold (cells_3_unfold (s0.sp - 1200#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 1176#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  wp_steps
  wp_conv_pre => unfold CryptoVerification.LibsignalTripleRatchet.Expand.esp
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1176_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc1_copy_recompose s0.sp uc1 g_uc1 _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_sendCt2_inImage hsendCt2_raw hb
    (s0.sp - 592#64) (s0.sp - 1176#64) uc1 outUc ct2 mac hsc_ok
    (ret_pc := entry + 256#64) (next_pc := entry + 20832#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx24, hx25, hx26, hx27, hsp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have h56_eq : (s0.sp - 592#64) + 56#64 = s0.sp - 536#64 := by bv_omega
  have h80_eq : (s0.sp - 592#64) + 80#64 = s0.sp - 512#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (unchunkedCt2SentAt_extract A (s0.sp - 592#64) outUc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_outUc
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 536#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 512#64) mac) (by sep_focus) ?_
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
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_outUc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq h648_outUc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc56_and_headers_recompose s0.sp outUc g_outUc _ _ _ _ _ _)
    (by sep_focus) ?_
  refine call_sendCt2Encoder_inImage hsendCt2Enc_raw
    (s0.sp - 1048#64) ct2Ptr macPtr ct2 mac sendingCt2
    hct2_ne hmac_ne henc_ok (ret_pc := entry + 324#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  have hstack_alloc :
      stackAt (s0.sp - 1760#64) sendCt2EncoderStack =
      memRegion (s0.sp - 19216#64) 13360 ∗ stackAt (s0.sp - 1760#64) allocHookStack := by
    have h19216_sub : (s0.sp - 1760#64) - 17456#64 = s0.sp - 19216#64 := by bv_omega
    rw [stackAt_sendCt2Encoder_eq_allocHook (s0.sp - 1760#64), h19216_sub]
  refine SepWP.fold (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsampled_join :
      polyEncoderAt A (s0.sp - 1048#64) sendingCt2 ∗
        unchunkedCt2SentAt A (s0.sp - 648#64) outUc ⊢
      chunkedCt2SampledAt A (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } := by
    dsimp only [chunkedCt2SampledAt]
    have h400 : (s0.sp - 1048#64) + 400#64 = s0.sp - 648#64 := by bv_omega
    rw [h400]; exact Entails.refl _
  refine SepWP.fold hsampled_join (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_scratch_join s0.sp) (by sep_focus) ?_
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))
    hinv2 ?_
  refine seq_clean (mid := entry + 344#64)
    (P_mid := (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
      polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
      memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 176 ∗
      chunkedCt2SampledAt A (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
      memRegion (s0.sp - 592#64) 528 ∗
      vecCapPtrDealloc A ct2Cap ct2Ptr ∗
      memRegion (s0.sp - 19216#64) 13360 ∗ ct1AckSavedRegs s0) ∗
      A.pool ∗ stackAt (s0.sp - 1760#64) allocHookStack)
    (Q := fun sm => Ct1AckDoneSaved s0 sm (s0.sp - 1760#64) outA ct2Cap ct2Ptr)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hmac : (macCap == 0#64) = true <;>
      simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine align_pre (by sep_ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hsp2, htr2, hvregs_2]⟩
    · wp_steps; wp_apply
      refine align_pre (by rw [hsp2]; sep_ac_rfl) ?_
      wp_done
  · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hsp3, htr3, hvregs_3⟩
    refine seq_clean (mid := entry + 364#64)
      (P_mid := (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 176 ∗
        chunkedCt2SampledAt A (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
        memRegion (s0.sp - 592#64) 528 ∗
        memRegion (s0.sp - 19216#64) 13360 ∗ ct1AckSavedRegs s0) ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) allocHookStack)
      (Q := fun sm => Ct1AckDoneSaved s0 sm (s0.sp - 1760#64) outA ct2Cap ct2Ptr)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
      by_cases hct2 : (ct2Cap == 0#64) = true <;>
        simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine align_pre (by sep_ac_rfl) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hsp3, htr3, hvregs_3]⟩
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp3]; sep_ac_rfl) ?_
        wp_done
    · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx24_4, hx25_4, hx26_4, hx27_4, hsp4, htr4, hvregs_4⟩
      refine SepWP.fold (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_extHook (s0.sp - 1760#64)))
        (by sep_focus) ?_
      wp_conv_pre =>
        rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 520) (b' := outA + 8#64) rfl rfl (by decide),
            ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 64) (b' := outA + 464#64) rfl (by bv_omega) (by decide)]
      refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
      wp_pull_exists
      wp_steps
      refine call_memcpy_relocate_cs_inImage hmemcpy_raw
        (Relocatable.of_chunkedCt2SampledAt A { uc := outUc, sending_ct2 := sendingCt2 })
        (outA + 8#64) (s0.sp - 1048#64)
        (ret_pc := entry + 388#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
        (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun4)
        (by simp only [State.sp, arm64_norm, hsp4]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr4])
        (by simp only [Reg.x0, arm64_norm, hx19_4]) (by simp only [Reg.x1, arm64_norm, hsp4])
        (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
        (fun sf5 hpc5 hrun5 hsp5 hcs5 htr5 _ => ?_)
      rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp_5, hvregs_5⟩
      simp only [arm64_norm, hx19_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4]
        at hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hfp_5 hvregs_5
      refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_extHook (s0.sp - 1760#64)).symm)
        (by sep_focus) ?_
      wp_steps
      refine SepWP.fold (ct1Ack_done_outA_recompose A outA outUc sendingCt2 res hres)
        (by sep_focus) ?_
      refine SepWP.fold (ct1Ack_done_stack_1160_rejoin s0.sp) (by sep_focus) ?_
      apply ct1AckEk_sepWP_congr_pre
      · refine hepilogue _ R hsp0_align ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · simp only [arm64_norm]
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
      · funext sf P_f; simp only [sepConj_assoc]

/-! ## 5. Main Theorems: `ct1_acknowledged_recv_ek_chunk_ok_inImage` & `ct1_acknowledged_recv_ek_chunk_ok_ax` -/

set_option maxHeartbeats 4000000 in
/-- Native-stack (`ct1AcknowledgedRecvEkChunkStack = 19216` B) `.inImage img` contract for
    `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`). -/
theorem ct1_acknowledged_recv_ek_chunk_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hdecodedMsg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img))
    (hrecvEk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((unchunkedCt1SentRecvEkSpec A F K).inImage img))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      ((ct1AcknowledgedRecvEkChunkSpec A F K img.base).inImage img) := by
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img) :=
    session_memcpy_region_ok_at_ax hAx ct1AcknowledgedRecvEkChunkName
      (num% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))
  have hadd_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 55896#64)
      ((addChunkSpecX A).inImage img) :=
    sub_ok_at_of_fnAddr haddChunk ct1AcknowledgedRecvEkChunkName 55896 (by fnoff_eq)
  have hdecodedMsg_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 53688#64)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img) :=
    sub_ok_at_of_fnAddr hdecodedMsg ct1AcknowledgedRecvEkChunkName 53688 (by fnoff_eq)
  have hrecvEk_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709547768#64)
      ((unchunkedCt1SentRecvEkSpec A F K).inImage img) := by
    have hrel : (leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName =
        (leavesProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName + BitVec.ofNat 64 3848 :=
      Program.fnAddr_rel (k := 3848) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) ct1AcknowledgedRecvEkChunk_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ hrecvEk
    dsimp only [leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  have hsendCt2_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709550136#64)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img) := by
    have hrel : (leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName =
        (leavesProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + BitVec.ofNat 64 1480 :=
      Program.fnAddr_rel (k := 1480) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) ct1AcknowledgedRecvEkChunk_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ hsendCt2
    dsimp only [leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  have hsendCt2Enc_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 20832#64)
      ((sendCt2EncoderSpec A).inImage img) :=
    sub_ok_at_of_fnAddr hsendCt2Enc ct1AcknowledgedRecvEkChunkName 20832 (by fnoff_eq)
  have hdealloc_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
    CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq
      (Program.fnAddr_rel
        (k := (num% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "__rustc::__rust_dealloc")))
        (b := img.base) (X := Rust.withPanics ext)
        ct1AcknowledgedRecvEkChunk_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hsortedSet16_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (leavesProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName =
        (leavesProgAtExt img.base ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 76976 :=
      Program.fnAddr_rel (k := 76976) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) ct1AcknowledgedRecvEkChunk_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_
      (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  have hnone := ct1_ack_recv_ek_none_branch_inImage (A := A) (F := F) hmemcpy_raw
  have herr := ct1_ack_recv_ek_err_branch (F := F) hsortedSet16_raw
  have hdone := fun (hb : img.base &&& 0xfff#64 = 0#64) =>
    ct1_ack_recv_ek_done_branch_inImage (F := F) (K := K) hb
      hsendCt2_raw hsendCt2Enc_raw hdealloc_raw hmemcpy_raw hsortedSet16_raw
  code_fetches CryptoVerification.libsignalSessionCode spqrCt1AcknowledgedRecvEkChunk4KBin img.base
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 0x595d0 612
  dsimp only [Spec.inImage, ct1AcknowledgedRecvEkChunkSpec]
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, ct1AcknowledgedRecvEkChunkName,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hadd_raw hdecodedMsg_raw hrecvEk_raw hnone herr hdone ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : Ct1AckInv img s0 := ⟨⟨by assumption, by assumption⟩⟩
  clear ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  rcases x with ⟨outA, stA, chunkA, st, chunk, res⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 (by assumption) (by decide)
  refine sepWPp_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))
    hinv0 ?_
  wp_conv_pre =>
    rw [stackAt_1760_entry_split s0.sp]
    unfold chunkedCt1AcknowledgedAt
  refine SepWP.fold (polyDecoderAt_dup_pts_len A (s0.readReg64 (Reg.gpr 1#5) + 128#64) st.receiving_ek)
    (by sep_focus) ?_
  wp_focus_pure; intro h16
  obtain ⟨decoded?, hdm, hcases⟩ := ct1_acknowledged_recv_ek_chunk_elim h16 (by assumption)
  refine SepWP.fold (unchunkedCt1SentAt_extract A (s0.readReg64 (Reg.gpr 1#5)) st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (cells_16_unfold (s0.sp - 1760#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_fiveVec (s0.readReg64 (Reg.gpr 1#5)) g_uc st.uc.epoch]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_fiveVec (s0.readReg64 (Reg.gpr 1#5)) g_uc st.uc.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1760_fiveVec s0.sp g_uc st.uc.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_extHook (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_memcpy_relocate_cs_p_inImage hmemcpy_raw
    (Relocatable.of_polyDecoderAt A st.receiving_ek)
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 1#5) + 128#64)
    (ret_pc := entry + 96#64) (next_pc := entry + 55896#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_extHook (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_addChunkX (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_addChunkX_mid_inImage hadd_raw
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ek chunk (by assumption)
    (ret_pc := entry + 108#64) (next_pc := entry + 53688#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx23_1]) (by simp only [Reg.x1, arm64_norm, hx22_1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hsorted' => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_addChunkX (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)))
    (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage_p_inImage hdecodedMsg_raw (by assumption)
    (s0.sp - 1224#64) (s0.sp - 1624#64) (addChunkTotal st.receiving_ek chunk) decoded?
    hsorted' hdm (ret_pc := entry + 120#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hx23_2])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 hinv3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  cases decoded? with
  | none =>
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    apply ct1AckEk_sepWP_congr_pre
    · exact hnone (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
        st.uc chunk (addChunkTotal st.receiving_ek chunk) g_uc res hcases s0 sf3 R
        (by assumption) hinv3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hvregs_3
    · sep_ac_rfl
    · funext sf P_f
      simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
  | some decoded =>
    rcases hcases with ⟨ucRes, huc, huc_cases⟩
    refine sepWPp_of_inv (mid := entry + 18446744073709547768#64) hinv3 ?_
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    wp_conv_pre => dsimp only [optVecU8At]
    refine SepWP.fold (vecU8_extract_nonNone A (s0.sp - 1224#64) decoded) (by sep_focus) ?_
    wp_pull_exists; rename_i v_dec
    wp_focus_pure; intro hne_dec
    have hdec_words :
        wordsAt (s0.sp - 1224#64) (vecWordsList v_dec) =
        (((s0.sp - 1224#64) ↦₆₄ v_dec.w0) ∗ ((s0.sp - 1216#64) ↦₆₄ v_dec.w1) ∗
         ((s0.sp - 1208#64) ↦₆₄ v_dec.w2)) := by
      simp only [vecWordsList, wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    wp_conv_pre => rw [hdec_words]; simp only [arm64_norm]
    wp_steps
    refine SepWP.fold (Entails.of_eq hdec_words.symm) (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_pre_recvEk A s0.sp (s0.readReg64 (Reg.gpr 1#5)) st.uc decoded g_uc v_dec)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)))
      (by sep_focus) ?_
    refine call_unchunkedRecvEk_p_inImage hrecvEk_raw
      (s0.sp - 592#64) (s0.sp - 1760#64) (s0.sp - 1224#64) st.uc decoded ucRes huc
      (ret_pc := entry + 152#64) (next_pc := entry + 152#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp3]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hsp3]) (by simp only [Reg.x1, arm64_norm, hsp3])
      (by simp only [Reg.x2, arm64_norm, hx21_3, ‹s0.readReg64 .x2 = st.uc.epoch›])
      (by simp only [Reg.x3, arm64_norm, hsp3])
      (by sep_focus)
      (fun sf4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩
    simp only [arm64_norm, hx19_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3]
      at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hvregs_4
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_post_recvEk s0.sp) (by sep_focus) ?_
    apply SepWP.done hpc4 hrun4
    intro hinv4
    cases ucRes with
    | error e =>
      apply SepWPp.of_sepWP_ret
      apply ct1AckEk_sepWP_congr_pre
      · exact herr (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
          chunk (addChunkTotal st.receiving_ek chunk) e res huc_cases s0 sf4 R
          (by assumption) hpc4 hrun4 hsp4 htr4 hx19_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · sep_ac_rfl
      · funext sf P_f
        simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
    | ok uc1 =>
      rcases huc_cases with ⟨outUc, ct2, mac, sendingCt2, hsc_ok, henc_ok, hres⟩
      apply ct1AckEk_sepWPp_congr_pre
      · exact hdone (by assumption) (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
          (s0.readReg64 (Reg.gpr 3#5)) chunk (addChunkTotal st.receiving_ek chunk)
          uc1 outUc ct2 mac sendingCt2 res hsc_ok henc_ok hres s0 sf4 R
          (by assumption) hinv4 hpc4 hrun4 hsp4 htr4 hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · sep_ac_rfl
      · funext sf P_f
        simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
      · funext sf P_f; simp only [satisfies_pure_sepConj]

/-- `StatesRecvContractsAx.ct1AcknowledgedRecvEkChunk_ok` (Field 12, `35936` B `growToCalleeExt` + `.inImage img`)
    from `AllocContractsX`, `DeallocOkExt`, `AddChunkOkX`, and `.inImage img` callee contracts. -/
theorem ct1_acknowledged_recv_ek_chunk_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hdecodedMsg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img))
    (hrecvEk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((unchunkedCt1SentRecvEkSpec A F K).inImage img))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      ((growToCalleeExt ct1AcknowledgedRecvEkChunkStack
        (ct1AcknowledgedRecvEkChunkSpec A F K img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax ct1AcknowledgedRecvEkChunkStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (ct1_acknowledged_recv_ek_chunk_ok_inImage
      hAx hdealloc haddChunk hdecodedMsg hrecvEk hsendCt2 hsendCt2Enc)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkExt
