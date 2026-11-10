/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridge
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# `<PolyDecoder as Decoder>::decoded_message` Bridge & `<HeaderSent>::recv_ct1_chunk` (`.inImage`)

Verifies `.inImage img` and `35936` B `growToCalleeExt` contracts for
`<PolyDecoder as Decoder>::decoded_message` (`StatesRecvContractsAx.polyDecodedMessage_ok`) and
`<HeaderSent>::recv_ct1_chunk` (`StatesRecvContractsAx.headerSentRecvCt1Chunk_ok`).
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (AllocContractsX ImgCallInv extHookStack session2MemcpySpecX sub_ok_at_of_fnAddr
   tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk NUM_POLYS PolyDecoder Pt spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyArrayBytes polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (AddChunkOkX PolyDecoderStrictSorted addChunkSpecX addChunkStackX addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (DecodedMessageGhost decodedMessageName decodedMessageSpec decodedMessageStack
   decodedMessageTotal decodedMessage_eq_ok optVecU8Of)
open CryptoVerification.SpqrV1.Drop
  (DeallocOkExt chunkedHeaderSentAt chunkedHeaderSentSize dropGluePoly16Stack
   dropGlueSortedSetPt16Spec dropProgAtExt dropSortedSetPt16Name
   drop_glue_sorted_set_pt16_ok_ext polyDecoderAt_entails_vecs_tail polyDecoder_post_join)
open CryptoVerification.SpqrV1.States.Leaves
  (AuthWords Relocatable VecWords authWordsList authenticatorAt_extract bv_sub_sub
   call_dropGlueSortedSetPt16_cs cap_add_one_beq_zero_false cell_0_rejoin_400
   cells_10_unfold cells_12_unfold cells_1_unfold cells_8_unfold
   headerSentRecvChunkAt headerSentRecvCt1ChunkName headerSentRecvCt1ChunkSpec
   headerSentRecvCt1ChunkStack headerSentRecvCt1Chunk_fnOff header_sent_recv_ct1_chunk_ok_elim
   optVecU8At optVecU8Of_eq_optVecU8At outA_done_recompose polyDecoderAt_dup_pts_len
   polyDecoderDecodedMessageName polyDecoderDecodedMessageSpec polyDecoderDecodedMessageStack
   recvCt1SavedCells relocate_post_entails relocate_pre_entails relocatedHeap
   sp_944_headerSent_recompose stA_880_rejoin stackAt_1568_rejoin stackAt_1568_split
   stackAt_decodedMessage_from_dropPoly16 stackAt_decodedMessage_to_dropPoly16
   trace_writeVReg128 unchunkedEkSentAt_400_eq vecU8_extract vecU8_extract_with_cap_lt
   vecWordsList wordsAt wordsAt_10 wordsAt_12 wordsAt_6 wordsAt_cons_off
   wordsAt_entails_memRegion wordsAt_nil wordsBytes)
open CryptoVerification.SpqrV1.States.Recv
  (growToCalleeExt sessionMemcpyRegionSpecAx session_memcpy_region_ok_at_ax
   sub_ok_inImage_growToCalleeExt_ax)

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgeExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. `<PolyDecoder as Decoder>::decoded_message` `.inImage img` Bridge (Field 7) -/

/-- Lift `subroutine_ok ... ((decodedMessageSpec A img.base).inImage img)` to
    `((polyDecoderDecodedMessageSpec A img.base).inImage img)`. -/
theorem poly_decoder_decoded_message_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodedMessageName)
      ((decodedMessageSpec A img.base).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre_pts : s0.mem ⊨
      (⌜ImgCallInv img s0⌝ ∗ (⌜img.base &&& 4095#64 = 0#64 ∧ s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧ PolyDecoderStrictSorted x.dec ∧
          spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗ memRegion x.outA 24 ∗
        (⌜x.dec.pts.length = 16⌝ ∗ polyDecoderAt A x.decA x.dec) ∗ tokenInitAt img.base ∗
        reduceTableAt img.base ∗ A.pool ∗ stackAt s0.sp polyDecoderDecodedMessageStack)) ∗ R := by
    refine Satisfies.mono ?_ hpre
    dsimp only [Spec.inImage, polyDecoderDecodedMessageSpec]
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (polyDecoderAt_dup_pts_len A x.decA x.dec)))))
  have hpts_sort :
      x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec ∧
        spqrPolyApi.decoded_message x.dec = .ok x.outMsg := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16⌝ ∗ ⌜img.base &&& 4095#64 = 0#64 ∧ s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧ PolyDecoderStrictSorted x.dec ∧
          spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
        (⌜ImgCallInv img s0⌝ ∗ memRegion x.outA 24 ∗ polyDecoderAt A x.decA x.dec ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
          stackAt s0.sp polyDecoderDecodedMessageStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre_pts
    rw [satisfies_pure_sepConj] at h1; rcases h1 with ⟨hlen, h2⟩
    rw [satisfies_pure_sepConj] at h2; exact ⟨hlen, h2.1.2.2.2.1, h2.1.2.2.2.2⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2.1
  have hout_eq : x.outMsg = decodedMessageTotal x.dec := by
    have hdm := hpts_sort.2.2; dsimp only [spqrPolyApi] at hdm; rw [hdec_eq] at hdm
    exact (Except.ok.inj hdm).symm
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨ ((decodedMessageSpec A img.base).inImage img).pre x' s0 ∗ R := by
    dsimp only [Spec.inImage, polyDecoderDecodedMessageSpec, decodedMessageSpec, x',
      CryptoVerification.SpqrV1.Poly.vecHeaderBytes, polyDecoderDecodedMessageStack,
      decodedMessageStack] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1, hpre.2.1.2.2.2.1⟩, hpre.2.2⟩
  refine h.mono_outcome x' R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcs, ?_⟩
    dsimp only [Spec.inImage, decodedMessageSpec, x'] at hpost
    dsimp only [Spec.inImage, polyDecoderDecodedMessageSpec, polyDecoderDecodedMessageStack]
    rw [hout_eq, ← optVecU8Of_eq_optVecU8At]
    exact hpost
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- `StatesRecvContractsAx.polyDecodedMessage_ok` (`35936` B `growToCalleeExt` + `.inImage img`). -/
theorem poly_decoder_decoded_message_ok_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodedMessageName)
      ((decodedMessageSpec A img.base).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((growToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax polyDecoderDecodedMessageStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (poly_decoder_decoded_message_ok_inImage h)

/-! ## 2. `.inImage img` Invariant & Call Helpers for `<HeaderSent>::recv_ct1_chunk` -/

gen_decodes libsignalSessionCode_tree spqrHeaderSentRecvCt1Chunk4KBin [
  0x58504 → 0x586c8
]

/-- Opaque wrapper around `ImgCallInv img s` so `dsimp`/`simp` never unfold `FrozenLoaded`. -/
structure RecvCt1Inv (img : Obj.Image) (s : State) : Prop where
  val : ImgCallInv img s

private theorem sepWPp_of_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : RecvCt1Inv img s)
    (h : SepWP prog mid s P (fun sm Pm => RecvCt1Inv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem sepWP_of_inv {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : RecvCt1Inv img s)
    (h : SepWP prog mid s P (fun sm Pm => RecvCt1Inv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  CryptoVerification.SepWP.of_sepWP_inv hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem call_memcpy_relocate_cs_inImage {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src) (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace → RecvCt1Inv img sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => RecvCt1Inv img sm → SepWP prog target_pc sm Pm post) := by
  apply SepWP.done hpc hrun; intro hinv
  have hsplit' : P = (memRegion dst n ∗ F src) ∗ (stackAt sp_call extHookStack ∗ Frame) := by
    rw [hsplit]; sep_ac_rfl
  rw [hsplit']
  refine SepWP.fold (relocate_pre_entails hrel dst src (stackAt sp_call extHookStack ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := (dst, src, bs)) (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, hlen]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hreord : ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗
        (relocatedHeap F bs ∗ Frame) =
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ (stackAt sp_call extHookStack ∗ Frame))) := by
      sep_ac_rfl
    rw [hreord]
    refine SepWP.fold (relocate_post_entails dst src hlen (stackAt sp_call extHookStack ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq : (F dst ∗ memRegion src n) ∗ (stackAt sp_call extHookStack ∗ Frame) =
        (F dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame := by sep_ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

private theorem call_memcpy_relocate_cs_p_inImage {img : Obj.Image} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop} {Qp : State → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src) (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace → RecvCt1Inv img sf →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((F dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Qp sf)) :
    SepWP prog entry s P
      (fun sm Pm => RecvCt1Inv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Qp sf)) := by
  apply SepWP.done hpc hrun; intro hinv
  have hsplit' : P = (memRegion dst n ∗ F src) ∗ (stackAt sp_call extHookStack ∗ Frame) := by
    rw [hsplit]; sep_ac_rfl
  rw [hsplit']
  refine SepWPp.fold (relocate_pre_entails hrel dst src (stackAt sp_call extHookStack ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bs => ?_
  refine SepWPp.pure_left fun hlen => ?_
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := (dst, src, bs)) (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ hm => by
      dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX] at hm
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, hlen]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr⟩ => ?_
    have hreord :
        ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗
          (relocatedHeap F bs ∗ Frame) =
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ (stackAt sp_call extHookStack ∗ Frame))) := by
      sep_ac_rfl
    rw [hreord]
    refine SepWPp.fold
      (relocate_post_entails dst src hlen (stackAt sp_call extHookStack ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq :
        (F dst ∗ memRegion src n) ∗ (stackAt sp_call extHookStack ∗ Frame) =
        (F dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame := by
      sep_ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

private theorem call_addChunkX_p_inImage {A : RustAlloc} {img : Obj.Image} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((addChunkSpecX A).inImage img))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) → RecvCt1Inv img sf →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWP prog entry s P
      (fun sm Pm => RecvCt1Inv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [addChunkSpecX]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [addChunkSpecX]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStackX))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted' ⟨hinv_sf⟩

private theorem call_decodedMessage_inImage {A : RustAlloc} {img : Obj.Image}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((polyDecoderDecodedMessageSpec A img.base).inImage img))
    (hb : img.base &&& 4095#64 = 0#64)
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdm : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = outA)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
      stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      RecvCt1Inv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
          stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => RecvCt1Inv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [polyDecoderDecodedMessageSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx8, hx0, hsorted, hdm⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [polyDecoderDecodedMessageSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
          stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        (optVecU8At A outA outMsg ∗ (polyDecoderAt A decA dec ∗
          (tokenInitAt img.base ∗ (reduceTableAt img.base ∗
            (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

/-! ## 3. Local Stack & Address Normalization Helpers (`1568`B Frame) -/

@[local arm64_norm, local wp_norm] private theorem sp_sub_64_align (sp : BitVec 64) :
    ((sp - 64#64) &&& 15#64 == 0#64) = (sp &&& 15#64 == 0#64) := by
  have h : (sp - 64#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  rw [h]
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_sub_1504 (sp : BitVec 64) : (sp - 64#64) - 1504#64 = sp - 1568#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_1504 (sp : BitVec 64) : (sp - 1568#64) + 1504#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_16 (sp : BitVec 64) : (sp - 64#64) + 16#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_24 (sp : BitVec 64) : (sp - 64#64) + 24#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_32 (sp : BitVec 64) : (sp - 64#64) + 32#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_40 (sp : BitVec 64) : (sp - 64#64) + 40#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_48 (sp : BitVec 64) : (sp - 64#64) + 48#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_56 (sp : BitVec 64) : (sp - 64#64) + 56#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_64 (sp : BitVec 64) : (sp - 64#64) + 64#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_8 (sp : BitVec 64) : (sp - 1568#64) + 8#64 = sp - 1560#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_16 (sp : BitVec 64) : (sp - 1568#64) + 16#64 = sp - 1552#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_24 (sp : BitVec 64) : (sp - 1568#64) + 24#64 = sp - 1544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_32 (sp : BitVec 64) : (sp - 1568#64) + 32#64 = sp - 1536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_40 (sp : BitVec 64) : (sp - 1568#64) + 40#64 = sp - 1528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_48 (sp : BitVec 64) : (sp - 1568#64) + 48#64 = sp - 1520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_56 (sp : BitVec 64) : (sp - 1568#64) + 56#64 = sp - 1512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_64 (sp : BitVec 64) : (sp - 1568#64) + 64#64 = sp - 1504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_72 (sp : BitVec 64) : (sp - 1568#64) + 72#64 = sp - 1496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_80 (sp : BitVec 64) : (sp - 1568#64) + 80#64 = sp - 1488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_88 (sp : BitVec 64) : (sp - 1568#64) + 88#64 = sp - 1480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_104 (sp : BitVec 64) : (sp - 1568#64) + 104#64 = sp - 1464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_249 (sp : BitVec 64) : (sp - 1568#64) + 249#64 = sp - 1319#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_504 (sp : BitVec 64) : (sp - 1568#64) + 504#64 = sp - 1064#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_520 (sp : BitVec 64) : (sp - 1568#64) + 520#64 = sp - 1048#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_528 (sp : BitVec 64) : (sp - 1568#64) + 528#64 = sp - 1040#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_592 (sp : BitVec 64) : (sp - 1568#64) + 592#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_616 (sp : BitVec 64) : (sp - 1568#64) + 616#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_624 (sp : BitVec 64) : (sp - 1568#64) + 624#64 = sp - 944#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_8 (sp : BitVec 64) : (sp - 1552#64) + 8#64 = sp - 1544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_16 (sp : BitVec 64) : (sp - 1552#64) + 16#64 = sp - 1536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_24 (sp : BitVec 64) : (sp - 1552#64) + 24#64 = sp - 1528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_8 (sp : BitVec 64) : (sp - 1520#64) + 8#64 = sp - 1512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_16 (sp : BitVec 64) : (sp - 1520#64) + 16#64 = sp - 1504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_24 (sp : BitVec 64) : (sp - 1520#64) + 24#64 = sp - 1496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1488_add_8 (sp : BitVec 64) : (sp - 1488#64) + 8#64 = sp - 1480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1319_add_255 (sp : BitVec 64) : (sp - 1319#64) + 255#64 = sp - 1064#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1064_add_8 (sp : BitVec 64) : (sp - 1064#64) + 8#64 = sp - 1056#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_944_add_480 (sp : BitVec 64) : (sp - 944#64) + 480#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_944_add_400 (sp : BitVec 64) : (sp - 944#64) + 400#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_8 (sp : BitVec 64) : (sp - 1040#64) + 8#64 = sp - 1032#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_16 (sp : BitVec 64) : (sp - 1040#64) + 16#64 = sp - 1024#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_24 (sp : BitVec 64) : (sp - 1040#64) + 24#64 = sp - 1016#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_32 (sp : BitVec 64) : (sp - 1040#64) + 32#64 = sp - 1008#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_40 (sp : BitVec 64) : (sp - 1040#64) + 40#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_48 (sp : BitVec 64) : (sp - 1040#64) + 48#64 = sp - 992#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_56 (sp : BitVec 64) : (sp - 1040#64) + 56#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_64 (sp : BitVec 64) : (sp - 1040#64) + 64#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_72 (sp : BitVec 64) : (sp - 1040#64) + 72#64 = sp - 968#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_80 (sp : BitVec 64) : (sp - 1040#64) + 80#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_88 (sp : BitVec 64) : (sp - 1040#64) + 88#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_496 (sp : BitVec 64) : (sp - 1040#64) + 496#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_504 (sp : BitVec 64) : (sp - 1040#64) + 504#64 = sp - 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_512 (sp : BitVec 64) : (sp - 1040#64) + 512#64 = sp - 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_520 (sp : BitVec 64) : (sp - 1040#64) + 520#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_528 (sp : BitVec 64) : (sp - 1040#64) + 528#64 = sp - 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_536 (sp : BitVec 64) : (sp - 1040#64) + 536#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_544 (sp : BitVec 64) : (sp - 1040#64) + 544#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_552 (sp : BitVec 64) : (sp - 1040#64) + 552#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_560 (sp : BitVec 64) : (sp - 1040#64) + 560#64 = sp - 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_568 (sp : BitVec 64) : (sp - 1040#64) + 568#64 = sp - 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_576 (sp : BitVec 64) : (sp - 1040#64) + 576#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_584 (sp : BitVec 64) : (sp - 1040#64) + 584#64 = sp - 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_8 (sp : BitVec 64) : (sp - 1024#64) + 8#64 = sp - 1016#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_16 (sp : BitVec 64) : (sp - 1024#64) + 16#64 = sp - 1008#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_24 (sp : BitVec 64) : (sp - 1024#64) + 24#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_8 (sp : BitVec 64) : (sp - 1008#64) + 8#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_16 (sp : BitVec 64) : (sp - 1008#64) + 16#64 = sp - 992#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_24 (sp : BitVec 64) : (sp - 1008#64) + 24#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_992_add_8 (sp : BitVec 64) : (sp - 992#64) + 8#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_8 (sp : BitVec 64) : (sp - 976#64) + 8#64 = sp - 968#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_16 (sp : BitVec 64) : (sp - 976#64) + 16#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_24 (sp : BitVec 64) : (sp - 976#64) + 24#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_968_add_8 (sp : BitVec 64) : (sp - 968#64) + 8#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_960_add_8 (sp : BitVec 64) : (sp - 960#64) + 8#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_8 (sp : BitVec 64) : (sp - 544#64) + 8#64 = sp - 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_16 (sp : BitVec 64) : (sp - 544#64) + 16#64 = sp - 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_24 (sp : BitVec 64) : (sp - 544#64) + 24#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_528_add_8 (sp : BitVec 64) : (sp - 528#64) + 8#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_8' (sp : BitVec 64) : (sp - 512#64) + 8#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_16' (sp : BitVec 64) : (sp - 512#64) + 16#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_24' (sp : BitVec 64) : (sp - 512#64) + 24#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_496_add_8' (sp : BitVec 64) : (sp - 496#64) + 8#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_8 (sp : BitVec 64) : (sp - 480#64) + 8#64 = sp - 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_16 (sp : BitVec 64) : (sp - 480#64) + 16#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_24 (sp : BitVec 64) : (sp - 480#64) + 24#64 = sp - 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_464_add_8 (sp : BitVec 64) : (sp - 464#64) + 8#64 = sp - 456#64 := by bv_omega

private theorem wordsAt_10_sp_1552 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    wordsAt (sp - 1552#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] =
    (((sp - 1552#64) ↦₆₄ v0) ∗ ((sp - 1544#64) ↦₆₄ v1) ∗ ((sp - 1536#64) ↦₆₄ v2) ∗
     ((sp - 1528#64) ↦₆₄ v3) ∗ ((sp - 1520#64) ↦₆₄ v4) ∗ ((sp - 1512#64) ↦₆₄ v5) ∗
     ((sp - 1504#64) ↦₆₄ v6) ∗ ((sp - 1496#64) ↦₆₄ v7) ∗ ((sp - 1488#64) ↦₆₄ v8) ∗
     ((sp - 1480#64) ↦₆₄ v9)) := by simp only [wordsAt_10, arm64_norm]

private theorem wordsAt_10_sp_544 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    wordsAt (sp - 544#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] =
    (((sp - 544#64) ↦₆₄ v0) ∗ ((sp - 536#64) ↦₆₄ v1) ∗ ((sp - 528#64) ↦₆₄ v2) ∗
     ((sp - 520#64) ↦₆₄ v3) ∗ ((sp - 512#64) ↦₆₄ v4) ∗ ((sp - 504#64) ↦₆₄ v5) ∗
     ((sp - 496#64) ↦₆₄ v6) ∗ ((sp - 488#64) ↦₆₄ v7) ∗ ((sp - 480#64) ↦₆₄ v8) ∗
     ((sp - 472#64) ↦₆₄ v9)) := by simp only [wordsAt_10, arm64_norm]

private theorem wordsAt_12_sp_1040 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    wordsAt (sp - 1040#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] =
    (((sp - 1040#64) ↦₆₄ v0) ∗ ((sp - 1032#64) ↦₆₄ v1) ∗ ((sp - 1024#64) ↦₆₄ v2) ∗
     ((sp - 1016#64) ↦₆₄ v3) ∗ ((sp - 1008#64) ↦₆₄ v4) ∗ ((sp - 1000#64) ↦₆₄ v5) ∗
     ((sp - 992#64) ↦₆₄ v6) ∗ ((sp - 984#64) ↦₆₄ v7) ∗ ((sp - 976#64) ↦₆₄ v8) ∗
     ((sp - 968#64) ↦₆₄ v9) ∗ ((sp - 960#64) ↦₆₄ v10) ∗ ((sp - 952#64) ↦₆₄ v11)) := by
  simp only [wordsAt_12, arm64_norm]

private theorem wordsAt_12_sp_544 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    wordsAt (sp - 544#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] =
    (((sp - 544#64) ↦₆₄ v0) ∗ ((sp - 536#64) ↦₆₄ v1) ∗ ((sp - 528#64) ↦₆₄ v2) ∗
     ((sp - 520#64) ↦₆₄ v3) ∗ ((sp - 512#64) ↦₆₄ v4) ∗ ((sp - 504#64) ↦₆₄ v5) ∗
     ((sp - 496#64) ↦₆₄ v6) ∗ ((sp - 488#64) ↦₆₄ v7) ∗ ((sp - 480#64) ↦₆₄ v8) ∗
     ((sp - 472#64) ↦₆₄ v9) ∗ ((sp - 464#64) ↦₆₄ v10) ∗ ((sp - 456#64) ↦₆₄ v11)) := by
  simp only [wordsAt_12, arm64_norm]

private theorem stackAt_decodedMessage_to_extHook (fsp : BitVec 64) :
    stackAt fsp polyDecoderDecodedMessageStack =
      memRegion (fsp - 17056#64) 672 ∗ stackAt fsp extHookStack := by
  change memRegion (fsp - 17056#64) 17056 =
    memRegion (fsp - 17056#64) 672 ∗ memRegion (fsp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := fsp - 17056#64) (n := 672) (k := 16384)
    (b' := fsp - 16384#64) rfl (by bv_omega) (by decide)

private theorem stackAt_decodedMessage_from_extHook (fsp : BitVec 64) :
    memRegion (fsp - 17056#64) 672 ∗ stackAt fsp extHookStack ⊢
      stackAt fsp polyDecoderDecodedMessageStack :=
  Entails.of_eq (stackAt_decodedMessage_to_extHook fsp).symm

private theorem stackAt_decodedMessage_to_addChunkX (fsp : BitVec 64) :
    stackAt fsp polyDecoderDecodedMessageStack =
      memRegion (fsp - 17056#64) 576 ∗ stackAt fsp addChunkStackX := by
  change memRegion (fsp - 17056#64) 17056 =
    memRegion (fsp - 17056#64) 576 ∗ memRegion (fsp - 16480#64) 16480
  exact ProofLib.memRegion_split' (b := fsp - 17056#64) (n := 576) (k := 16480)
    (b' := fsp - 16480#64) rfl (by bv_omega) (by decide)

private theorem stackAt_decodedMessage_from_addChunkX (fsp : BitVec 64) :
    memRegion (fsp - 17056#64) 576 ∗ stackAt fsp addChunkStackX ⊢
      stackAt fsp polyDecoderDecodedMessageStack :=
  Entails.of_eq (stackAt_decodedMessage_to_addChunkX fsp).symm

/-! ## 4. Branch 1 (`outMsg = none`) under `.inImage img` -/

set_option maxHeartbeats 800000 in
private theorem header_sent_recv_ct1_chunk_none_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img))
    (outA stA chunkA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec1 : PolyDecoder)
    (outRes : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSentRecvChunk
      spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .stillReceiving { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 })
    (g : AuthWords) (gdk : VecWords) (s0 s : State) {P : SepProp} (R : SepProp)
    (hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true)
    (hinv : RecvCt1Inv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1568#64)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = stA)
    (_hx21 : s.readReg64 .x21 = st.uc.epoch) (_hx22 : s.readReg64 .x22 = chunkA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1040#64) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (_hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hfp : s.readReg64 .fp = s0.sp - 64#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace)
    (hP : P = (
      optVecU8At A (s0.sp - 1064#64) none ∗ polyDecoderAt A (s0.sp - 1464#64) dec1 ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
      stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion outA 880 ∗ polyEncoderAt A stA st.sending_ek ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      ((stA + 472#64) ↦₆₄ st.uc.epoch) ∗ memRegion (stA + 480#64) 400 ∗ chunkAt chunkA chunk ∗
      ((s0.sp - 1568#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1560#64) ↦₆₄ st.uc.epoch) ∗
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      memRegion (s0.sp - 1472#64) 8 ∗ memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 400 ∗ memRegion (s0.sp - 544#64) 480 ∗ recvCt1SavedCells s0)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜ImgCallInv img sf⌝ ∗ ⌜sf.trace = s0.trace⌝ ∗
            headerSentRecvChunkAt A outA outRes ∗ memRegion stA chunkedHeaderSentSize ∗
            chunkAt chunkA chunk ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
            A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  code_fetches CryptoVerification.libsignalSessionCode spqrHeaderSentRecvCt1Chunk4KBin img.base
    (Rust.withPanics ext) headerSentRecvCt1Chunk_fnOff 0x58504 452
  dsimp only [tripleRatchetProgAtExt, headerSentRecvCt1ChunkName, chunkedHeaderSentSize,
    optVecU8At, noneCap, AsmConstants.optionVecNoneWord,
    BitVec.ofNat_eq_ofNat] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" = entry
  examples_hide_fetches
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
    hinv ?_
  wp_conv_pre =>
    rw [stackAt_decodedMessage_to_extHook (s0.sp - 1568#64),
        ProofLib.memRegion_split' (b := s0.sp - 544#64) (n := 80) (k := 400)
          (b' := s0.sp - 464#64) rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
  wp_steps
  refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_polyDecoderAt A dec1)
    (s0.sp - 464#64) (s0.sp - 1464#64)
    (ret_pc := entry + 312#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
    hinv1 ?_
  have hst_auth :
      wordsAt (stA + 400#64) (authWordsList g) =
      (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((stA + 416#64) ↦₆₄ g.v1.w2) ∗ ((stA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk : wordsAt (stA + 448#64) (vecWordsList gdk) =
      (((stA + 448#64) ↦₆₄ gdk.w0) ∗ ((stA + 456#64) ↦₆₄ gdk.w1) ∗ ((stA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]; simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_544_words : wordsAt (s0.sp - 544#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 544#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 536#64) ↦₆₄ g.v1.w1) ∗ ((s0.sp - 528#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 520#64) ↦₆₄ g.v2.w0) ∗ ((s0.sp - 512#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 504#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 496#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 488#64) ↦₆₄ gdk.w1) ∗ ((s0.sp - 480#64) ↦₆₄ gdk.w2) ∗
       ((s0.sp - 472#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_10, arm64_norm]
  refine SepWP.fold (cells_10_unfold (s0.sp - 544#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hst_auth, hst_dk, wordsAt_10_sp_544]; simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_544_words.symm) (by sep_focus) ?_
  refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_polyEncoderAt A st.sending_ek)
    (s0.sp - 944#64) stA
    (ret_pc := entry + 352#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hx20_1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
    hinv2 ?_
  let outSt : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent
      spqrPolyApi (spqrAuthApi F) :=
    { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 }
  refine SepWP.fold (stA_880_rejoin stA g gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (sp_944_headerSent_recompose A s0.sp st outSt dec1 rfl g gdk) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_chunkedHeaderSentAt A outSt)
    outA (s0.sp - 944#64)
    (ret_pc := entry + 368#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hx19_2]) (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 hinv3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  refine sepWP_of_inv (mid := s0.readReg64 Reg.lr) hinv3 ?_
  have hnone_24 :
      ((s0.sp - 1064#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (s0.sp - 1056#64) 16 ⊢
      memRegion (s0.sp - 1064#64) 24 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1064#64) (n := 8) (k := 16)
        (b' := s0.sp - 1056#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
  refine SepWP.fold (stackAt_decodedMessage_from_extHook (s0.sp - 1568#64)) (by sep_focus) ?_
  refine SepWP.fold hnone_24 (by sep_focus) ?_
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    have h : (s0.sp &&& 15#64) = ((s0.sp - 1568#64) &&& 15#64) := by bv_bits
    rw [h]; exact hfsp_align
  wp_conv_pre => unfold recvCt1SavedCells
  wp_steps
  refine SepWP.fold (stackAt_1568_rejoin s0 0#64 st.uc.epoch
    (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) rfl)
    (by dsimp only [recvCt1SavedCells]; sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_f
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  subst hout
  dsimp only [headerSentRecvChunkAt]
  refine ⟨fun hm => ?_, by simp only [State.sp, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨hinv_f.val, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨by simp only [arm64_norm, htr3], Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Reg.x19, arm64_norm]
    · simp only [Reg.x20, arm64_norm]
    · simp only [Reg.x21, arm64_norm]
    · simp only [Reg.x22, arm64_norm]
    · simp only [Reg.x23, arm64_norm]
    · simp only [Reg.x24, arm64_norm, hx24_3]
    · simp only [Reg.x25, arm64_norm, hx25_3]
    · simp only [Reg.x26, arm64_norm, hx26_3]
    · simp only [Reg.x27, arm64_norm, hx27_3]
    · simp only [Reg.x28, arm64_norm]
    · simp only [Reg.fp, arm64_norm]
    · simp only [arm64_norm, hvregs_3]

/-! ## 5. Branch 2 (`outMsg = some ct1`) under `.inImage img` -/

set_option maxHeartbeats 800000 in
private theorem header_sent_recv_ct1_chunk_some_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img))
    (hpt16 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName + 18446744073709478940#64)
      (dropGlueSortedSetPt16Spec A))
    (outA stA chunkA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec1 : PolyDecoder) (ct1 : Bytes)
    (outRes : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSentRecvChunk
      spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .done { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk, ct1 := ct1 },
                             sending_ek := st.sending_ek })
    (g : AuthWords) (gdk : VecWords) (s0 s : State) {P : SepProp} (R : SepProp)
    (hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true)
    (hinv : RecvCt1Inv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1568#64)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = st.uc.epoch) (_hx22 : s.readReg64 .x22 = chunkA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1040#64) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (_hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hfp : s.readReg64 .fp = s0.sp - 64#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace)
    (hP : P = (
      optVecU8At A (s0.sp - 1064#64) (some ct1) ∗ polyDecoderAt A (s0.sp - 1464#64) dec1 ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
      stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion outA 880 ∗ polyEncoderAt A stA st.sending_ek ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      ((stA + 472#64) ↦₆₄ st.uc.epoch) ∗ memRegion (stA + 480#64) 400 ∗ chunkAt chunkA chunk ∗
      ((s0.sp - 1568#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1560#64) ↦₆₄ st.uc.epoch) ∗
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      memRegion (s0.sp - 1472#64) 8 ∗ memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 400 ∗ memRegion (s0.sp - 544#64) 480 ∗ recvCt1SavedCells s0)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜ImgCallInv img sf⌝ ∗ ⌜sf.trace = s0.trace⌝ ∗
            headerSentRecvChunkAt A outA outRes ∗ memRegion stA chunkedHeaderSentSize ∗
            chunkAt chunkA chunk ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
            A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  code_fetches CryptoVerification.libsignalSessionCode spqrHeaderSentRecvCt1Chunk4KBin img.base
    (Rust.withPanics ext) headerSentRecvCt1Chunk_fnOff 0x58504 452
  dsimp only [tripleRatchetProgAtExt, headerSentRecvCt1ChunkName, chunkedHeaderSentSize,
    optVecU8At, BitVec.ofNat_eq_ofNat] at hmemcpy hpt16 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" = entry
  examples_hide_fetches
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
    hinv ?_
  refine SepWP.fold (vecU8_extract_with_cap_lt A (s0.sp - 1064#64) ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i gct1
  wp_focus_pure; intro hcap_lt
  have hadds_z := cap_add_one_beq_zero_false hcap_lt
  have hct1_words : wordsAt (s0.sp - 1064#64) (vecWordsList gct1) =
      (((s0.sp - 1064#64) ↦₆₄ gct1.w0) ∗ ((s0.sp - 1056#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 1048#64) ↦₆₄ gct1.w2)) := by
    dsimp only [vecWordsList]; simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, arm64_norm]
  have hsp_1552_words : wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 1552#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1544#64) ↦₆₄ g.v1.w1) ∗ ((s0.sp - 1536#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 1528#64) ↦₆₄ g.v2.w0) ∗ ((s0.sp - 1520#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1512#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 1504#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 1496#64) ↦₆₄ gdk.w1) ∗ ((s0.sp - 1488#64) ↦₆₄ gdk.w2) ∗
       ((s0.sp - 1480#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_10, arm64_norm]
  have hst_auth : wordsAt (stA + 400#64) (authWordsList g) =
      (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗ ((stA + 416#64) ↦₆₄ g.v1.w2) ∗
       ((stA + 424#64) ↦₆₄ g.v2.w0) ∗ ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk : wordsAt (stA + 448#64) (vecWordsList gdk) =
      (((stA + 448#64) ↦₆₄ gdk.w0) ∗ ((stA + 456#64) ↦₆₄ gdk.w1) ∗ ((stA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]; simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_544_words12 : wordsAt ((s0.sp - 944#64) + 400#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
      (((s0.sp - 544#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 536#64) ↦₆₄ g.v1.w1) ∗ ((s0.sp - 528#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 520#64) ↦₆₄ g.v2.w0) ∗ ((s0.sp - 512#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 504#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 496#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 488#64) ↦₆₄ gdk.w1) ∗ ((s0.sp - 480#64) ↦₆₄ gdk.w2) ∗
       ((s0.sp - 472#64) ↦₆₄ gct1.w0) ∗ ((s0.sp - 464#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 456#64) ↦₆₄ gct1.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_12, arm64_norm]
  have hsp_1040_words12 : wordsAt (s0.sp - 1040#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
      (((s0.sp - 1040#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1032#64) ↦₆₄ g.v1.w1) ∗ ((s0.sp - 1024#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 1016#64) ↦₆₄ g.v2.w0) ∗ ((s0.sp - 1008#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1000#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 992#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 984#64) ↦₆₄ gdk.w1) ∗ ((s0.sp - 976#64) ↦₆₄ gdk.w2) ∗
       ((s0.sp - 968#64) ↦₆₄ gct1.w0) ∗ ((s0.sp - 960#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 952#64) ↦₆₄ gct1.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_12, arm64_norm]
  wp_conv_pre =>
    rw [stackAt_decodedMessage_to_extHook (s0.sp - 1568#64),
        hct1_words, hsp_1552_words, hst_auth, hst_dk,
        ProofLib.memRegion_split' (b := outA) (n := 8) (k := 872) (b' := outA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 8#64) (n := 496) (k := 376) (b' := outA + 504#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 504#64) (n := 8) (k := 368) (b' := outA + 512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 8) (k := 392)
          (b' := s0.sp - 936#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 544#64) (n := 96) (k := 384)
          (b' := s0.sp - 448#64) rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
  refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (outA + 504#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 944#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_12_unfold (s0.sp - 1040#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_12_unfold (s0.sp - 544#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [wordsAt_12_sp_1040, wordsAt_12_sp_544]; simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_1552_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hct1_words.symm) (by sep_focus) ?_
  refine SepWP.fold (wordsAt_entails_memRegion (vecWordsList gct1) (s0.sp - 1064#64) 24 rfl) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_1040_words12.symm) (by sep_focus) ?_
  refine SepWP.fold
    (wordsAt_entails_memRegion (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1)
      (s0.sp - 1040#64) 96 rfl) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_544_words12.symm) (by sep_focus) ?_
  refine SepWP.fold (cell_0_rejoin_400 s0.sp 944#64 936#64 st.uc.epoch (by bv_omega)) (by sep_focus) ?_
  refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_polyEncoderAt A st.sending_ek)
    (s0.sp - 944#64) stA
    (ret_pc := entry + 232#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hx20])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
    hinv1 ?_
  refine SepWP.fold (stA_880_rejoin stA g gdk st.uc.epoch) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_polyEncoder_and_words12 A st.sending_ek
      (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) rfl)
    (outA + 8#64) (s0.sp - 944#64)
    (ret_pc := entry + 248#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx19_1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine sepWP_of_inv (mid := s0.readReg64 Reg.lr) hinv2 ?_
  have hrejoin_880 :
      memRegion (s0.sp - 944#64) 496 ∗ memRegion (s0.sp - 448#64) 384 ⊢
      memRegion (s0.sp - 944#64) 880 := by
    rw [← ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 496) (k := 384)
        (b' := s0.sp - 448#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWP.fold (stackAt_decodedMessage_from_extHook (s0.sp - 1568#64)) (by sep_focus) ?_
  refine SepWP.fold hrejoin_880 (by sep_focus) ?_
  refine SepWP.fold (polyDecoderAt_entails_vecs_tail A (s0.sp - 1464#64) dec1) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs
  wp_focus_pure; intro hvecs_len
  wp_conv_pre => rw [stackAt_decodedMessage_to_dropPoly16 (s0.sp - 1568#64)]
  wp_steps
  refine SepWP.fold (outA_done_recompose A outA st ct1 outRes hout g gdk gct1) (by sep_focus) ?_
  refine call_dropGlueSortedSetPt16_cs hpt16 (s0.sp - 1464#64) vecs hvecs_len (s0 := s0)
    (ret_pc := entry + 268#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hsp2]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  refine SepWP.fold (polyDecoder_post_join (s0.sp - 1464#64)) (by sep_focus) ?_
  refine SepWP.fold (stackAt_decodedMessage_from_dropPoly16 (s0.sp - 1568#64)) (by sep_focus) ?_
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    have h : (s0.sp &&& 15#64) = ((s0.sp - 1568#64) &&& 15#64) := by bv_bits
    rw [h]; exact hfsp_align
  wp_conv_pre => unfold recvCt1SavedCells
  wp_steps
  refine SepWP.fold (stackAt_1568_rejoin s0 0#64 st.uc.epoch
    (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) rfl)
    (by dsimp only [recvCt1SavedCells]; sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_f
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨fun hm => ?_, by simp only [State.sp, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨hinv_f.val, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨by simp only [arm64_norm, htr3], Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Reg.x19, arm64_norm]
    · simp only [Reg.x20, arm64_norm]
    · simp only [Reg.x21, arm64_norm]
    · simp only [Reg.x22, arm64_norm]
    · simp only [Reg.x23, arm64_norm]
    · simp only [Reg.x24, arm64_norm, hx24_3]
    · simp only [Reg.x25, arm64_norm, hx25_3]
    · simp only [Reg.x26, arm64_norm, hx26_3]
    · simp only [Reg.x27, arm64_norm, hx27_3]
    · simp only [Reg.x28, arm64_norm]
    · simp only [Reg.fp, arm64_norm]
    · simp only [arm64_norm, hvregs_3]

/-! ## 6. Main Theorem: `<HeaderSent>::recv_ct1_chunk` `.inImage img` & `growToCalleeExt` (Field 2) -/

attribute [local irreducible] CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.recv_ct1_chunk

set_option maxHeartbeats 800000 in
/-- `<HeaderSent>::recv_ct1_chunk` meets `(headerSentRecvCt1ChunkSpec A F img.base).inImage img`
    from `AllocContractsX`, `DeallocOkExt`, `AddChunkOkX`, and
    `polyDecoderDecodedMessageSpec.inImage img`. -/
theorem header_sent_recv_ct1_chunk_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hdecoded : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((headerSentRecvCt1ChunkSpec A F img.base).inImage img) := by
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img) :=
    session_memcpy_region_ok_at_ax hAx headerSentRecvCt1ChunkName
      (num% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
  have hadd_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName + 60196#64)
      ((addChunkSpecX A).inImage img) :=
    sub_ok_at_of_fnAddr haddChunk headerSentRecvCt1ChunkName 60196 (by fnoff_eq)
  have hdec_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName + 57988#64)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img) :=
    sub_ok_at_of_fnAddr hdecoded headerSentRecvCt1ChunkName 57988 (by fnoff_eq)
  have hpt16_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName + 18446744073709478940#64)
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName =
        (tripleRatchetProgAtExt img.base ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 72676 :=
      Program.fnAddr_rel (k := 72676) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) headerSentRecvCt1Chunk_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_
      (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, tripleRatchetProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  code_fetches CryptoVerification.libsignalSessionCode spqrHeaderSentRecvCt1Chunk4KBin img.base
    (Rust.withPanics ext) headerSentRecvCt1Chunk_fnOff 0x58504 452
  have h_none := header_sent_recv_ct1_chunk_none_inImage (A := A) (F := F) hmemcpy_raw
  have h_some := header_sent_recv_ct1_chunk_some_inImage (A := A) (F := F) hmemcpy_raw hpt16_raw
  dsimp only [Spec.inImage, headerSentRecvCt1ChunkSpec]
  dsimp only [tripleRatchetProgAtExt, headerSentRecvCt1ChunkName,
    chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hadd_raw hdec_raw hpt16_raw h_none h_some ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : RecvCt1Inv img s0 := ⟨⟨by assumption, by assumption⟩⟩
  clear ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  rcases x with ⟨outA, stA, chunkA, st, chunk, outRes⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hb : img.base &&& 4095#64 = 0#64 := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = st.uc.epoch := by assumption
  have hsorted : PolyDecoderStrictSorted st.receiving_ct1 := by assumption
  have hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes := by assumption
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1568#64 hsp0_align (by decide)
  refine sepWPp_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))
    hinv0 ?_
  wp_conv_pre =>
    rw [stackAt_1568_split s0.sp, stackAt_decodedMessage_to_extHook (s0.sp - 1568#64)]
    unfold chunkedHeaderSentAt
  refine SepWP.fold
    (polyDecoderAt_dup_pts_len A (s0.readReg64 (Reg.gpr 1#5) + 480#64) st.receiving_ct1)
    (by sep_focus) ?_
  wp_focus_pure; intro hpts
  obtain ⟨outMsg, hdm, hcases⟩ := header_sent_recv_ct1_chunk_ok_elim hpts hrecv
  wp_conv_pre => rw [unchunkedEkSentAt_400_eq]
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_extract A (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.dk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i gdk
  have hst_auth : wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗ ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗ ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗ ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk : wordsAt (s0.readReg64 (Reg.gpr 1#5) + 448#64) (vecWordsList gdk) =
      (((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ gdk.w0) ∗ ((s0.readReg64 (Reg.gpr 1#5) + 456#64) ↦₆₄ gdk.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]; simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_1552_words : wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 1552#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1544#64) ↦₆₄ g.v1.w1) ∗ ((s0.sp - 1536#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 1528#64) ↦₆₄ g.v2.w0) ∗ ((s0.sp - 1520#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1512#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 1504#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 1496#64) ↦₆₄ gdk.w1) ∗ ((s0.sp - 1488#64) ↦₆₄ gdk.w2) ∗
       ((s0.sp - 1480#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_10, arm64_norm]
  refine SepWP.fold (cells_1_unfold (s0.sp - 1568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 1560#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 1552#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hst_auth, hst_dk, wordsAt_10_sp_1552, sp_sub_64_add_8, sp_sub_64_add_16,
    sp_sub_64_add_24, sp_sub_64_add_32, sp_sub_64_add_40, sp_sub_64_add_48, sp_sub_64_add_56]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_1552_words.symm) (by sep_focus) ?_
  have hfold_saved :
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      recvCt1SavedCells s0 := Entails.refl _
  refine SepWP.fold hfold_saved
    (by dsimp only [Reg.fp, Reg.lr, Reg.x28, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_focus) ?_
  refine call_memcpy_relocate_cs_p_inImage hmemcpy_raw
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_polyDecoderAt A st.receiving_ct1)
    (s0.sp - 1464#64) (s0.readReg64 (Reg.gpr 1#5) + 480#64)
    (s0 := s0) (ret_pc := entry + 104#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx2]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine sepWPp_of_inv (mid := entry + 60196#64) hinv1 ?_
  refine SepWP.fold (stackAt_decodedMessage_from_extHook (s0.sp - 1568#64)) (by sep_focus) ?_
  wp_conv_pre => rw [stackAt_decodedMessage_to_addChunkX (s0.sp - 1568#64)]
  wp_steps
  refine call_addChunkX_p_inImage hadd_raw
    (s0.sp - 1464#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ct1 chunk hsorted
    (s0 := s0) (ret_pc := entry + 116#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) htr1
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hx22_1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hsorted1 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine sepWPp_of_inv (mid := entry + 57988#64) hinv2 ?_
  refine SepWP.fold (stackAt_decodedMessage_from_addChunkX (s0.sp - 1568#64)) (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage_inImage hdec_raw hb (s0.sp - 1064#64) (s0.sp - 1464#64)
    (addChunkTotal st.receiving_ct1 chunk) outMsg hsorted1 hdm
    (s0 := s0) (ret_pc := entry + 128#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) htr2
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hsp2])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 hinv3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  rcases hcases with ⟨rfl, hout⟩ | ⟨ct1, rfl, hout⟩
  · refine SepWP.mono
      (h_none (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
        st chunk (addChunkTotal st.receiving_ct1 chunk) outRes hout g gdk s0 sf3 R
        hsp0_align hinv3 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
        hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3 htr3 (by sep_ac_rfl)) ?_
    intro sf P_f _ _ ⟨hm, hsp_sf, hcs_sf⟩
    exact ⟨fun h => (satisfies_pure_sepConj _ _ _).mpr
      ⟨(hm h).1.2, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (hm h).2⟩, hsp_sf, hcs_sf⟩
  · refine SepWP.mono
      (h_some (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
        st chunk (addChunkTotal st.receiving_ct1 chunk) ct1 outRes hout g gdk s0 sf3 R
        hsp0_align hinv3 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
        hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3 htr3 (by sep_ac_rfl)) ?_
    intro sf P_f _ _ ⟨hm, hsp_sf, hcs_sf⟩
    exact ⟨fun h => (satisfies_pure_sepConj _ _ _).mpr
      ⟨(hm h).1.2, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (hm h).2⟩, hsp_sf, hcs_sf⟩

/-- `StatesRecvContractsAx.headerSentRecvCt1Chunk_ok` (`35936` B `growToCalleeExt` + `.inImage img`). -/
theorem header_sent_recv_ct1_chunk_ok_ax {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) (haddChunk : AddChunkOkX img A ext)
    (hdecoded : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((polyDecoderDecodedMessageSpec A img.base).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax headerSentRecvCt1ChunkStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (header_sent_recv_ct1_chunk_ok_inImage hAx hdealloc haddChunk hdecoded)

theorem header_sent_recv_ct1_chunk_ok_ax_of_decodedMessage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hdecoded : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodedMessageName)
      ((decodedMessageSpec A img.base).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img) :=
  header_sent_recv_ct1_chunk_ok_ax hAx hdealloc haddChunk
    (poly_decoder_decoded_message_ok_inImage hdecoded)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgeExt
