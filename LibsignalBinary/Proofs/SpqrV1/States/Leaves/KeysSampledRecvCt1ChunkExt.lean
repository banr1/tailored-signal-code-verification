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
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk`: `.inImage` & `StatesRecvContractsAx`

Verifies the native-stack (`17920` B) `.inImage img` contract `keys_sampled_recv_ct1_chunk_ok_inImage`
and the `35936` B `growToCalleeExt` contract `keys_sampled_recv_ct1_chunk_ok_ax`
(`StatesRecvContractsAx.keysSampledRecvCt1Chunk_ok`).
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn rustDeallocSpec vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (AllocContractsX ImgCallInv extHookStack session2MemcpySpecX sub_ok_at_of_fnAddr
   tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk PolyDecoder PolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (HeaderSent KeysSampled)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyDecoderAt polyEncoderAt polyEncoderSize resultPolyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (AddChunkOkX PolyDecoderStrictSorted addChunkSpecX addChunkStackX addChunkTotal)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (EncodeBytesOkExt EncodeBytesOkX bytesAt encodeBytesName encodeBytesResult
   encodeBytesSpecX encodeBytesStackX)
open CryptoVerification.SpqrV1.Drop
  (DeallocOkExt chunkedHeaderSentAt chunkedHeaderSentSize chunkedKeysSampledAt
   dropGluePoly16Spec dropPoly16Name dropProgAtExt drop_glue_poly16_ok_ext)
open CryptoVerification.SpqrV1.States.Leaves
  (AuthWords Relocatable Relocatable.of_polyDecoderAt Relocatable.of_polyEncoderAt
   VecWords authWordsList authenticatorAt_extract bv_sub_sub
   byte_1_unfold cells_10_unfold cells_16_unfold cells_1_unfold cells_9_unfold
   emptyPolyDecoder emptyPolyDecoder_recompose emptyPolyDecoder_strictSorted
   encodeBytesSpecX_of_encodeBytesSpec' fold_sendCt2SavedCells
   keysSampledRecvCt1ChunkName keysSampledRecvCt1ChunkSpec
   keysSampledRecvCt1ChunkStack keysSampledRecvCt1Chunk_fnOff
   keys_sampled_recv_ct1_chunk_ok_elim keys_sampled_recv_ct1_chunk_tail
   leavesProgAtExt polyEncoderAt_split_tag relocate_post_entails relocate_pre_entails
   relocatedHeap sendCt2SavedCells sepWP_congr_pre
   sp_sub_80_add_16' sp_sub_80_add_24' sp_sub_80_add_32' sp_sub_80_add_40'
   sp_sub_80_add_48' sp_sub_80_add_56' sp_sub_80_add_64' sp_sub_80_add_72'
   sp_sub_80_add_80' sp_sub_80_sub_16 sp_sub_80_sub_80 sp_sub_80_sub_896
   sp_sub_976_add_896 stA_400_104_fold
   trace_writeVReg128 unchunkedHeaderSentAt_400_eq vecU8Tail
   vecU8_entails_slice_and_tail vecU8_extract vecWordsList wordsAt wordsAt_10
   wordsAt_16 wordsAt_6 wordsAt_9 wordsAt_cons_off wordsAt_nil wordsBytes)
open CryptoVerification.SpqrV1.States.Recv
  (growToCalleeExt sessionMemcpyRegionSpecAx session_memcpy_region_ok_at_ax
   sub_ok_inImage_growToCalleeExt_ax sub_ok_inImage_of_sub_ok_ax)

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local irreducible] addChunkTotal emptyPolyDecoder
attribute [local arm64_norm, local wp_norm]
  sp_sub_80_sub_896 sp_sub_976_add_896 sp_sub_80_sub_80 sp_sub_80_sub_16
  sp_sub_80_add_16' sp_sub_80_add_24' sp_sub_80_add_32' sp_sub_80_add_40'
  sp_sub_80_add_48' sp_sub_80_add_56' sp_sub_80_add_64' sp_sub_80_add_72'
  sp_sub_80_add_80'

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

gen_decodes libsignalSessionCode_tree spqrKeysSampledRecvCt1Chunk4KBin [
  0x5c370 → 0x5c518
]

/-! ## 1. Stack Layout Helpers for `addChunkStackX` (`16480` B) & `extHookStack` (`16384` B) -/

private theorem stackAt_976_split_X (sp : BitVec 64) :
    stackAt sp keysSampledRecvCt1ChunkStack =
      memRegion (sp - 17920#64) 464 ∗ stackAt (sp - 976#64) addChunkStackX ∗
      memRegion (sp - 976#64) 8 ∗ memRegion (sp - 968#64) 8 ∗
      memRegion (sp - 960#64) 128 ∗ memRegion (sp - 832#64) 128 ∗ memRegion (sp - 704#64) 128 ∗
      memRegion (sp - 576#64) 8 ∗ memRegion (sp - 568#64) 1 ∗ memRegion (sp - 567#64) 7 ∗
      memRegion (sp - 560#64) 400 ∗
      memRegion (sp - 160#64) 72 ∗ memRegion (sp - 88#64) 8 ∗
      memRegion (sp - 80#64) 80 := by
  change memRegion (sp - 17920#64) 17920 =
    memRegion (sp - 17920#64) 464 ∗ memRegion (sp - 976#64 - 16480#64) 16480 ∗ _
  have hsub : sp - 976#64 - 16480#64 = sp - 17456#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17920#64) (n := 464) (k := 17456) (b' := sp - 17456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 17456#64) (n := 16480) (k := 976) (b' := sp - 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 8) (k := 968) (b' := sp - 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 968#64) (n := 8) (k := 960) (b' := sp - 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 960#64) (n := 128) (k := 832) (b' := sp - 832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 832#64) (n := 128) (k := 704) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 128) (k := 576) (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 8) (k := 568) (b' := sp - 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 568#64) (n := 1) (k := 567) (b' := sp - 567#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 567#64) (n := 7) (k := 560) (b' := sp - 560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 560#64) (n := 400) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 72) (k := 88) (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide)]

private theorem stackAt_976_addChunkX_to_encodeBytesX (sp : BitVec 64) :
    memRegion (sp - 17920#64) 464 ∗ stackAt (sp - 976#64) addChunkStackX ⊢
    stackAt (sp - 976#64) encodeBytesStackX := by
  change memRegion (sp - 17920#64) 464 ∗ memRegion (sp - 976#64 - 16480#64) 16480 ⊢
    memRegion (sp - 976#64 - 16944#64) 16944
  have h1 : sp - 976#64 - 16480#64 = sp - 17456#64 := by bv_omega
  have h2 : sp - 976#64 - 16944#64 = sp - 17920#64 := by bv_omega
  rw [h1, h2, ← ProofLib.memRegion_split' (b := sp - 17920#64) (n := 464) (k := 16480) (b' := sp - 17456#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

private theorem stackAt_encodeBytesX_to_extHook (fsp : BitVec 64) :
    stackAt fsp encodeBytesStackX ⊢
    memRegion (fsp - 16944#64) 560 ∗ stackAt fsp extHookStack := by
  change memRegion (fsp - 16944#64) 16944 ⊢
    memRegion (fsp - 16944#64) 560 ∗ memRegion (fsp - 16384#64) 16384
  rw [ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 560) (k := 16384) (b' := fsp - 16384#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

private theorem stackAt_encodeBytesX_from_extHook (fsp : BitVec 64) :
    memRegion (fsp - 16944#64) 560 ∗ stackAt fsp extHookStack ⊢
    stackAt fsp encodeBytesStackX := by
  change memRegion (fsp - 16944#64) 560 ∗ memRegion (fsp - 16384#64) 16384 ⊢
    memRegion (fsp - 16944#64) 16944
  rw [← ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 560) (k := 16384) (b' := fsp - 16384#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-! ## 2. `.inImage img` Invariant & Framed Call Rules -/

/-- Opaque wrapper around `ImgCallInv img s` so `dsimp`/`simp` never unfold `FrozenLoaded`. -/
private structure KsInv (img : Obj.Image) (s : State) : Prop where
  val : ImgCallInv img s

private theorem sepWPp_of_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : KsInv img s)
    (h : SepWP prog mid s P (fun sm Pm => KsInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem sepWP_of_inv {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : KsInv img s)
    (h : SepWP prog mid s P (fun sm Pm => KsInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  CryptoVerification.SepWP.of_sepWP_inv hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem call_memcpy_relocate_cs_inImage {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    {n : Nat} {G : BitVec 64 → SepProp} (hrel : Relocatable n G) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src) (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ G src ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace → KsInv img sf →
      SepWP prog target_pc sf ((G dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => KsInv img sm → SepWP prog target_pc sm Pm post) := by
  apply SepWP.done hpc hrun; intro hinv
  have hsplit' : P = (memRegion dst n ∗ G src) ∗ (stackAt sp_call extHookStack ∗ Frame) := by
    rw [hsplit]; sep_ac_rfl
  rw [hsplit']
  refine SepWP.fold (relocate_pre_entails hrel dst src (stackAt sp_call extHookStack ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := (dst, src, bs)) (F := relocatedHeap G bs ∗ Frame)
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
        (relocatedHeap G bs ∗ Frame) =
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap G bs ∗ (stackAt sp_call extHookStack ∗ Frame))) := by
      sep_ac_rfl
    rw [hreord]
    refine SepWP.fold (relocate_post_entails dst src hlen (stackAt sp_call extHookStack ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq : (G dst ∗ memRegion src n) ∗ (stackAt sp_call extHookStack ∗ Frame) =
        (G dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame := by sep_ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

private theorem call_addChunkX_next_inImage {A : RustAlloc} {img : Obj.Image} {prog : Program}
    {entry ret_pc next_pc : BitVec 64}
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
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        (fun sm Pm => KsInv img sm →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm => KsInv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv
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
    refine sepWPp_of_inv (mid := next_pc) ⟨hinv_sf⟩ ?_
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStackX))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

private theorem call_encodeBytesX_inImage {A : RustAlloc} {img : Obj.Image} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((encodeBytesSpecX A).inImage img))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = out)
    (hx0 : s.readReg64 Reg.x0 = msgA)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace → KsInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => KsInv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun; intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨out, false, msgA, msg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encodeBytesSpecX, polyEncoderSize, bytesAt]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [encodeBytesSpecX]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    change SepWPp prog (s0.readReg64 Reg.lr) sf
      (⌜sf.trace = s.trace⌝ ∗
        ((polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame)) post _
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame =
        (polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

/-! ## 3. Phase 2 (`entry + 236#64`): `.inImage img` `memcpy`s + Black-Box `keys_sampled_recv_ct1_chunk_tail` -/

set_option maxHeartbeats 600000 in
private theorem keys_sampled_recv_ct1_chunk_finish_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img))
    (hdealloc : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A))
    (hpoly16 : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName + 18446744073709463380#64)
      (dropGluePoly16Spec A))
    (outA stA chunkA : BitVec 64)
    (st : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (g : AuthWords) (gdk : VecWords)
    (ekCap ekPtr d56 : BitVec 64)
    (hek_le : st.uc.ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true)
    (hinv : KsInv img s)
    (hpc : s.pc = (leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 976#64)
    (hx19 : s.readReg64 .x19 = stA)
    (hx20 : s.readReg64 .x20 = st.uc.epoch)
    (hx21 : s.readReg64 .x21 = outA)
    (hx22 : s.readReg64 .x22 = ekCap)
    (hx23 : s.readReg64 .x23 = ekPtr)
    (hx24 : s.readReg64 .x24 = s0.sp - 160#64)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hfp : s.readReg64 .fp = s0.sp - 80#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 880 ∗
      polyEncoderAt A stA st.sending_hdr ∗
      memRegion (stA + 400#64) 104 ∗
      chunkAt chunkA chunk ∗
      polyDecoderAt A (s0.sp - 960#64) dec ∗
      polyEncoderAt A (s0.sp - 560#64) outSt.sending_ek ∗
      (ekPtr ↦ₛ st.uc.ek) ∗
      vecU8Tail A ekCap ekPtr st.uc.ek ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
      memRegion (s0.sp - 976#64) 8 ∗
      ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (s0.sp - 88#64) 8 ∗
      sendCt2SavedCells s0 d56 ∗
      A.pool ∗
      stackAt (s0.sp - 976#64) encodeBytesStackX)) :
    SepWP (leavesProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜ImgCallInv img sf⌝ ∗ ⌜sf.trace = s0.trace⌝ ∗
            chunkedHeaderSentAt A outA outSt ∗
            memRegion stA 504 ∗
            chunkAt chunkA chunk ∗
            A.pool ∗
            stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  have h_tail := keys_sampled_recv_ct1_chunk_tail (F := F) hdealloc hpoly16
  code_fetches CryptoVerification.libsignalSessionCode spqrKeysSampledRecvCt1Chunk4KBin img.base
    (Rust.withPanics ext) keysSampledRecvCt1Chunk_fnOff 0x5c370 428
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, keysSampledRecvCt1ChunkName,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 400) (k := 480) (b' := outA + 400#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 400#64) (n := 80) (k := 400) (b' := outA + 480#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (stackAt_encodeBytesX_to_extHook (s0.sp - 976#64)) (by sep_focus) ?_
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (s0.sp - 560#64) outSt.sending_ek
  suffices h_mc1 : ∀ sf1 : State,
      sf1.pc = entry + 264#64 → sf1.status = .Running →
      sf1.sp = s0.sp - 976#64 → CalleeSavedPreserved s sf1 → sf1.trace = s0.trace →
      KsInv img sf1 →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf1
        ((polyEncoderAt A outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400 ∗
            stackAt (s0.sp - 976#64) extHookStack) ∗
          (memRegion ((s0.sp - 976#64) - 16944#64) 560 ∗
           memRegion (outA + 400#64) 80 ∗ memRegion (outA + 480#64) 400 ∗
           polyEncoderAt A stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
           chunkAt chunkA chunk ∗ polyDecoderAt A (s0.sp - 960#64) dec ∗
           (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A ekCap ekPtr st.uc.ek ∗
           relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
           relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
           wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
           memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
           memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
           A.pool))
        (fun sf P_f =>
          (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜ImgCallInv img sf⌝ ∗ ⌜sf.trace = s0.trace⌝ ∗
              chunkedHeaderSentAt A outA outSt ∗
              memRegion stA 504 ∗
              chunkAt chunkA chunk ∗
              A.pool ∗
              stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) by
    refine sepWP_of_inv
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy"))
      hinv ?_
    rcases htag01 with rfl | rfl
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
        (Relocatable.of_polyEncoderAt A outSt.sending_ek) outA (s0.sp - 560#64)
        (ret_pc := entry + 264#64) (sp_call := s0.sp - 976#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 =>
          sepWP_congr_pre (by sep_ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1 hinv1))
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
        (Relocatable.of_polyEncoderAt A outSt.sending_ek) outA (s0.sp - 560#64)
        (ret_pc := entry + 264#64) (sp_call := s0.sp - 976#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 =>
          sepWP_congr_pre (by sep_ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1 hinv1))
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy"))
    hinv1 ?_
  wp_steps
  refine call_memcpy_relocate_cs_inImage hmemcpy (s0 := s0)
    (Relocatable.of_polyDecoderAt A dec) (outA + 480#64) (s0.sp - 960#64)
    (ret_pc := entry + 280#64) (sp_call := s0.sp - 976#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx21_1])
    (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (stackAt_encodeBytesX_from_extHook (s0.sp - 976#64)) (by sep_focus) ?_
  refine CryptoVerification.SepWP.of_sepWP_inv hinv2.val.1 hinv2.val.2
    (SepWP.mono
      (h_tail outA stA chunkA st chunk dec outSt hout_eq g gdk ekCap ekPtr d56
        hek_le hek_lt hsp0_align hfsp_align hpc2 hrun2 hsp2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2
        (by sep_ac_rfl)) ?_)
  intro sf P_f hpc_f hrun_f ⟨hmem, hsp_sf, hcs_sf⟩ hfl_f hsym_f
  refine SepWP.done hpc_f hrun_f ⟨fun R hm => ?_, hsp_sf, hcs_sf⟩
  have h1 := hmem R hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h1 ⊢
  exact ⟨⟨hfl_f, hsym_f⟩, h1⟩

/-! ## 4. Main Theorems: `keys_sampled_recv_ct1_chunk_ok_inImage` & `keys_sampled_recv_ct1_chunk_ok_ax` -/

set_option maxHeartbeats 800000 in
/-- Native-stack (`keysSampledRecvCt1ChunkStack = 17920` B) `.inImage img` contract for
    `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk`. -/
theorem keys_sampled_recv_ct1_chunk_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hencode : EncodeBytesOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((keysSampledRecvCt1ChunkSpec A F).inImage img) := by
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img) :=
    session_memcpy_region_ok_at_ax hAx keysSampledRecvCt1ChunkName
      (num% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy"))
  have hadd_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName + 44216#64)
      ((addChunkSpecX A).inImage img) :=
    sub_ok_at_of_fnAddr haddChunk keysSampledRecvCt1ChunkName 44216 (by fnoff_eq)
  have henc_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName + 40784#64)
      ((encodeBytesSpecX A).inImage img) :=
    sub_ok_at_of_fnAddr hencode keysSampledRecvCt1ChunkName 40784 (by fnoff_eq)
  have hdealloc_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
    CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq
      (Program.fnAddr_rel
        (k := (num% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc")))
        (b := img.base) (X := Rust.withPanics ext)
        keysSampledRecvCt1Chunk_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hpoly16_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName + 18446744073709463380#64)
      (dropGluePoly16Spec A) := by
    have hrel : (leavesProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName =
        (leavesProgAtExt img.base ext).fnAddr dropPoly16Name + BitVec.ofNat 64 88236 :=
      Program.fnAddr_rel (k := 88236) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) keysSampledRecvCt1Chunk_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  code_fetches CryptoVerification.libsignalSessionCode spqrKeysSampledRecvCt1Chunk4KBin img.base
    (Rust.withPanics ext) keysSampledRecvCt1Chunk_fnOff 0x5c370 428
  have h_finish := keys_sampled_recv_ct1_chunk_finish_inImage (F := F)
    hmemcpy_raw hdealloc_raw hpoly16_raw
  dsimp only [Spec.inImage, keysSampledRecvCt1ChunkSpec]
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, keysSampledRecvCt1ChunkName,
    chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hadd_raw henc_raw hdealloc_raw hpoly16_raw h_finish ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : KsInv img s0 := ⟨⟨by assumption, by assumption⟩⟩
  clear ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  rcases x with ⟨outA, stA, chunkA, st, chunk, outSt⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  obtain ⟨henc_res, hek_len_le, hout_eq⟩ := keys_sampled_recv_ct1_chunk_ok_elim (by assumption)
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 976#64 hsp0_align (by decide)
  refine sepWPp_of_inv (mid := entry + 44216#64) hinv0 ?_
  wp_conv_pre =>
    rw [stackAt_976_split_X s0.sp]
    unfold chunkedKeysSampledAt
    rw [unchunkedHeaderSentAt_400_eq A (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 968#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 960#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 832#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 704#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 80#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_16, wordsAt_10, arm64_norm]
  wp_steps
  refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
  have hdec0_1 :
      (((s0.sp - 960#64) ↦₆₄ 0#64) ∗ ((s0.sp - 952#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 944#64) ↦₆₄ 0#64) ∗ ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 928#64) ↦₆₄ 2#64) ∗ ((s0.sp - 920#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 912#64) ↦₆₄ 0#64) ∗ ((s0.sp - 904#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 896#64) ↦₆₄ 0#64) ∗ ((s0.sp - 888#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 880#64) ↦₆₄ 2#64) ∗ ((s0.sp - 872#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 864#64) ↦₆₄ 0#64) ∗ ((s0.sp - 856#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 848#64) ↦₆₄ 0#64) ∗ ((s0.sp - 840#64) ↦₆₄ 0#64)) =
      wordsAt (s0.sp - 960#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_2 :
      (((s0.sp - 832#64) ↦₆₄ 2#64) ∗ ((s0.sp - 824#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 816#64) ↦₆₄ 0#64) ∗ ((s0.sp - 808#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 800#64) ↦₆₄ 0#64) ∗ ((s0.sp - 792#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 784#64) ↦₆₄ 2#64) ∗ ((s0.sp - 776#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 752#64) ↦₆₄ 0#64) ∗ ((s0.sp - 744#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 736#64) ↦₆₄ 2#64) ∗ ((s0.sp - 728#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 720#64) ↦₆₄ 0#64) ∗ ((s0.sp - 712#64) ↦₆₄ 2#64)) =
      wordsAt ((s0.sp - 960#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_3 :
      (((s0.sp - 704#64) ↦₆₄ 0#64) ∗ ((s0.sp - 696#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 688#64) ↦₆₄ 2#64) ∗ ((s0.sp - 680#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 672#64) ↦₆₄ 0#64) ∗ ((s0.sp - 664#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 656#64) ↦₆₄ 0#64) ∗ ((s0.sp - 648#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 640#64) ↦₆₄ 2#64) ∗ ((s0.sp - 632#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 624#64) ↦₆₄ 0#64) ∗ ((s0.sp - 616#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 608#64) ↦₆₄ 0#64) ∗ ((s0.sp - 600#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 592#64) ↦₆₄ 2#64) ∗ ((s0.sp - 584#64) ↦₆₄ 0#64)) =
      wordsAt ((s0.sp - 960#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  refine SepWP.fold (Entails.of_eq hdec0_1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_2) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_3) (by sep_focus) ?_
  have hdec_recomp :
      wordsAt (s0.sp - 960#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
      wordsAt ((s0.sp - 960#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
      wordsAt ((s0.sp - 960#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
      ((s0.sp - 576#64) ↦₆₄ 480#64) ∗ ((s0.sp - 568#64) ↦₈ 0#8) ∗ memRegion (s0.sp - 567#64) 7 ⊢
      polyDecoderAt A (s0.sp - 960#64) (emptyPolyDecoder 480) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A (s0.sp - 960#64) 480 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunkX_next_inImage hadd_raw
    (s0.sp - 960#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 480) chunk
    (emptyPolyDecoder_strictSorted 480)
    (s0 := s0) (ret_pc := entry + 184#64) (next_pc := entry + 40784#64) (sp_call := s0.sp - 976#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 _ => ?_)
  generalize (addChunkTotal (emptyPolyDecoder 480) chunk) = dec1 at hout_eq ⊢
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stackAt_976_addChunkX_to_encodeBytesX s0.sp) (by sep_focus) ?_
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.ek)
    (by sep_focus) ?_
  wp_pull_exists; rename_i ekCap ekPtr
  wp_focus_pure; rintro ⟨hek_le, hek_lt, hek_ne⟩
  refine SepWP.fold (vecU8_extract A (s0.readReg64 (Reg.gpr 1#5) + 472#64) st.uc.dk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i gdk
  refine SepWP.fold (cells_9_unfold (s0.sp - 160#64)) (by sep_focus) ?_
  wp_pull_exists
  have hst_auth_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 472#64) (vecWordsList gdk) =
      (((s0.readReg64 (Reg.gpr 1#5) + 472#64) ↦₆₄ gdk.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 480#64) ↦₆₄ gdk.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 488#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (((s0.sp - 160#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 152#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 144#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 136#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 120#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 104#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ gdk.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_9, arm64_norm]
  wp_conv_pre =>
    rw [hst_auth_words, hst_dk_words]
    simp only [wordsAt_9, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk_words.symm) (by sep_focus) ?_
  refine SepWP.fold (stA_400_104_fold (s0.readReg64 (Reg.gpr 1#5)) g
    ekCap ekPtr (BitVec.ofNat 64 st.uc.ek.length) gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  have hek_lt64 : st.uc.ek.length < 2 ^ 64 := by omega
  refine call_encodeBytesX_inImage henc_raw
    (s0.sp - 560#64) ekPtr st.uc.ek outSt.sending_ek henc_res hek_lt64
    (s0 := s0) (ret_pc := entry + 236#64) (sp_call := s0.sp - 976#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x8, arm64_norm, hsp1])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx24_1, hx25_1, hx26_1, hx27_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.mono (h_finish
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
    st chunk dec1 outSt hout_eq g gdk ekCap ekPtr _ hek_le hek_lt
    (s0 := s0) (s := sf2) hsp0_align hsp0_align hinv2 hpc2 hrun2 hsp2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2
    (by sep_ac_rfl)) ?_
  intro sf P_f _ _ ⟨hmem, hsp_sf, hcs_sf⟩
  refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
  have h1 := hmem R hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h1 ⊢
  exact ⟨h1.1.2, h1.2⟩

/-- `StatesRecvContractsAx.keysSampledRecvCt1Chunk_ok` (Field 1, `35936` B `growToCalleeExt` + `.inImage img`)
    from `AllocContractsX`, `DeallocOkExt`, `AddChunkOkX`, and `EncodeBytesOkX`. -/
theorem keys_sampled_recv_ct1_chunk_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hencode : EncodeBytesOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((growToCalleeExt keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax keysSampledRecvCt1ChunkStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (keys_sampled_recv_ct1_chunk_ok_inImage hAx hdealloc haddChunk hencode)

theorem keys_sampled_recv_ct1_chunk_ok_ax_of_encodeBytesExt
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext)
    (hencode : EncodeBytesOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((growToCalleeExt keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img) :=
  keys_sampled_recv_ct1_chunk_ok_ax hAx hdealloc haddChunk
    (sub_ok_inImage_of_sub_ok_ax img (encodeBytesSpecX_of_encodeBytesSpec' hencode))

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkExt
