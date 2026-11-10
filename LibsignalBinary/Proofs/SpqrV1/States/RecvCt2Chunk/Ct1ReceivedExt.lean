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
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1Received
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<Ct1Received>::recv_ct2_chunk`: `.inImage` & Contract-Backed Proofs

Lifts `ct1_received_recv_ct2_chunk_ok_ext` (`0x5e2f4`) to `.inImage img` callees at both
`allocHookStack` (`15,664` B) and `extHookStack` (`16,384` B).
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalTripleRatchet
  (AllocContractsX ImgCallInv extHookStack session2MemcpySpecX sub_ok_at_of_fnAddr
   tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1
  (Chunk NUM_POLYS PolyDecoder spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Poly (chunkAt polyArrayBytes polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (AddChunkOkX PolyDecoderStrictSorted addChunkSpecX addChunkStackX addChunkTotal)
open CryptoVerification.SpqrV1.Drop
  (DeallocOkExt chunkedCt1ReceivedAt chunkedCt1ReceivedSize chunkedEkSentCt1ReceivedAt
   chunkedEkSentCt1ReceivedSize chunked_400_join dropGluePoly16Spec dropGluePoly16Stack
   dropPoly16Name dropProgAtExt drop_glue_poly16_ok_ext polyEncoderAt_entails_tag_vecs_tail
   unchunkedEkSentCt1ReceivedAt vecGF16ListOf)
open CryptoVerification.SpqrV1.States.Leaves
  (Relocatable authWordsList bv_sub_sub byte_1_unfold cells_13_unfold' cells_16_unfold
   cells_1_unfold cells_6_unfold chunkedEkSentCt1ReceivedAt_recompose
   ct1ReceivedRecvCt2ChunkName ct1ReceivedRecvCt2ChunkSpec ct1ReceivedRecvCt2ChunkStack
   ct1ReceivedRecvCt2Chunk_fnOff ct1_received_recv_ct2_chunk_ok_elim ct2SentWordsList
   ekSentCt1ReceivedWordsList ekSentWordsList emptyPolyDecoder emptyPolyDecoder_recompose
   emptyPolyDecoder_strictSorted relocate_post_entails relocate_pre_entails relocatedHeap
   stackAt_448_from_dropPoly16 uc_104_copy_recompose
   unchunkedEkSentCt1ReceivedAt_extract vecWordsList wordsAt wordsAt_13' wordsAt_16 wordsAt_6
   wordsAt_entails_memRegion)
open CryptoVerification.SpqrV1.States.Recv
  (growToCalleeExt sessionMemcpyRegionSpecAx session_memcpy_region_ok_at_ax
   sub_ok_inImage_growToCalleeExt_ax)

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Ct1ReceivedExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree spqrCt1Received4KBin [
  0x58efc → 0x59004
]

/-- Opaque wrapper around `ImgCallInv img s` so `dsimp`/`simp` never unfold `FrozenLoaded`. -/
structure Ct1RecvInv (img : Obj.Image) (s : State) : Prop where
  val : ImgCallInv img s

private theorem sepWPp_of_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Ct1RecvInv img s)
    (h : SepWP prog mid s P (fun sm Pm => Ct1RecvInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

private theorem sepWP_of_inv {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : Ct1RecvInv img s)
    (h : SepWP prog mid s P (fun sm Pm => Ct1RecvInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  CryptoVerification.SepWP.of_sepWP_inv hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

/-- Framed `.inImage img` call rule for `addChunkSpecX A`. -/
theorem call_addChunkX_inImage {A : RustAlloc} {img : Obj.Image} {prog : Program}
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
      PolyDecoderStrictSorted (addChunkTotal dec chunk) → Ct1RecvInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => Ct1RecvInv img sm →
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
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStackX))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted' ⟨hinv_sf⟩

/-- Framed `.inImage img` `memcpy` call rule at `extHookStack` (`sessionMemcpyRegionSpecAx`)
    relocating any `Relocatable n F` predicate from `src` to `dst`. -/
theorem call_memcpy_relocate_cs_inImage {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecAx.inImage img))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      Ct1RecvInv img sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => Ct1RecvInv img sm → SepWP prog target_pc sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hinv
  have hsplit' : P = (memRegion dst n ∗ F src) ∗ (stackAt sp_call extHookStack ∗ Frame) := by
    rw [hsplit]; sep_ac_rfl
  rw [hsplit']
  refine SepWP.fold
    (relocate_pre_entails hrel dst src (stackAt sp_call extHookStack ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    hcall hinv.val (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]
    rw [hsp, hlen]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · dsimp only [sessionMemcpyRegionSpecAx, session2MemcpySpecX]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hreord :
        ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗
          (relocatedHeap F bs ∗ Frame) =
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ (stackAt sp_call extHookStack ∗ Frame))) := by
      sep_ac_rfl
    rw [hreord]
    refine SepWP.fold
      (relocate_post_entails dst src hlen (stackAt sp_call extHookStack ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq :
        (F dst ∗ memRegion src n) ∗ (stackAt sp_call extHookStack ∗ Frame) =
        (F dst ∗ memRegion src n ∗ stackAt sp_call extHookStack) ∗ Frame := by
      sep_ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

private theorem stackAt_448_split_ax (sp : BitVec 64) :
    stackAt sp ct1ReceivedRecvCt2ChunkStack =
      memRegion (sp - 16976#64) 48 ∗ stackAt (sp - 448#64) addChunkStackX ∗
      memRegion (sp - 448#64) 128 ∗ memRegion (sp - 320#64) 128 ∗ memRegion (sp - 192#64) 128 ∗
      memRegion (sp - 64#64) 8 ∗ memRegion (sp - 56#64) 1 ∗ memRegion (sp - 55#64) 7 ∗
      memRegion (sp - 48#64) 48 := by
  change memRegion (sp - 16976#64) 16976 =
    memRegion (sp - 16976#64) 48 ∗ memRegion (sp - 448#64 - 16480#64) 16480 ∗ _
  have hsub : sp - 448#64 - 16480#64 = sp - 16928#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 16976#64) (n := 48) (k := 16928) (b' := sp - 16928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 16928#64) (n := 16480) (k := 448) (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 448#64) (n := 128) (k := 320) (b' := sp - 320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 320#64) (n := 128) (k := 192) (b' := sp - 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 192#64) (n := 128) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 55) (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 55#64) (n := 7) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide)]

private theorem stackAt_addChunkX_to_extHook (fsp : BitVec 64) :
    stackAt fsp addChunkStackX = memRegion (fsp - 16480#64) 96 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 96 (by decide)

private theorem stackAt_448_to_dropPoly16_ax (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    memRegion (sp - 16976#64) 48 ∗ memRegion (sp - 448#64 - 16480#64) 96 ∗
      stackAt (sp - 448#64) extHookStack ∗ memRegion (sp - 448#64) 400 ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
    memRegion (sp - 16976#64) 12848 ∗ stackAt sp dropGluePoly16Stack := by
  have h6 :
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 48#64) 48 := by
    have heq :
        (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
         ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) =
        wordsAt (sp - 48#64) [w0, w1, w2, w3, w4, w5] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp - 48#64) 48 rfl
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h6)))) ?_
  change memRegion (sp - 16976#64) 48 ∗
      (memRegion (sp - 448#64 - 16480#64) 96 ∗
        (memRegion (sp - 448#64 - 16384#64) 16384 ∗
          (memRegion (sp - 448#64) 400 ∗ memRegion (sp - 48#64) 48))) ⊢
    memRegion (sp - 16976#64) 12848 ∗ memRegion (sp - 4128#64) 4128
  have hsub1 : sp - 448#64 - 16480#64 = sp - 16928#64 := by bv_omega
  have hsub2 : sp - 448#64 - 16384#64 = sp - 16832#64 := by bv_omega
  rw [hsub1, hsub2,
      ← ProofLib.memRegion_split' (b := sp - 448#64) (n := 400) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16832#64) (n := 16384) (k := 448) (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16928#64) (n := 96) (k := 16832) (b' := sp - 16832#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 48) (k := 16928) (b' := sp - 16928#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12848) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

set_option maxHeartbeats 1200000 in
/-- `<Ct1Received>::recv_ct2_chunk` meets `(ct1ReceivedRecvCt2ChunkSpec A F).inImage img`
    from `AllocContractsX`, `DeallocOkExt`, and `AddChunkOkX`. -/
theorem ct1_received_recv_ct2_chunk_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((ct1ReceivedRecvCt2ChunkSpec A F).inImage img) := by
  have hadd_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName + 57644#64)
      ((addChunkSpecX A).inImage img) :=
    sub_ok_at_of_fnAddr haddChunk ct1ReceivedRecvCt2ChunkName 57644 (by fnoff_eq)
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" "memcpy")))
      (sessionMemcpyRegionSpecAx.inImage img) :=
    session_memcpy_region_ok_at_ax hAx ct1ReceivedRecvCt2ChunkName
      (num% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" "memcpy"))
  have hpoly16_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName + (0#64 - 74808#64))
      (dropGluePoly16Spec A) := by
    have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName =
        (tripleRatchetProgAtExt img.base ext).fnAddr dropPoly16Name + BitVec.ofNat 64 74808 :=
      Program.fnAddr_rel (k := 74808) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) ct1ReceivedRecvCt2Chunk_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, tripleRatchetProgAtExt] at hrel ⊢
    rw [hrel]; bv_omega
  have hpoly16_raw' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName +
        BitVec.ofNat 64 (2 ^ 64 - 74808))
      (dropGluePoly16Spec A) := by
    simpa only [show (0#64 - 74808#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 74808) by decide]
      using hpoly16_raw
  clear hpoly16_raw
  code_fetches CryptoVerification.libsignalSessionCode spqrCt1Received4KBin img.base
    (Rust.withPanics ext) ct1ReceivedRecvCt2Chunk_fnOff
    (num% (ls_off% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk")) 268
  dsimp only [Spec.inImage, ct1ReceivedRecvCt2ChunkSpec]
  dsimp only [tripleRatchetProgAtExt, ct1ReceivedRecvCt2ChunkName,
    chunkedEkSentCt1ReceivedSize, chunkedCt1ReceivedSize,
    BitVec.ofNat_eq_ofNat] at hadd_raw hmemcpy_raw hpoly16_raw' ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : Ct1RecvInv img s0 := ⟨⟨by assumption, by assumption⟩⟩
  clear ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  rcases x with ⟨outA, stA, chunkA, st, chunk, outSt⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hout_eq := ct1_received_recv_ct2_chunk_ok_elim (by assumption)
  have hfsp_align : ((s0.sp - 448#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 448#64 (by assumption) (by decide)
  have hrun0 : s0.status = .Running := by assumption
  refine sepWPp_of_inv (mid := entry + 57644#64) hinv0 ?_
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 0#5)) (n := 104) (k := 400)
        (b' := s0.readReg64 (Reg.gpr 0#5) + 104#64) rfl rfl (by decide),
        stackAt_448_split_ax s0.sp]
    unfold chunkedCt1ReceivedAt
  refine SepWP.fold (cells_16_unfold (s0.sp - 448#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 320#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 192#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 56#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_6_unfold (s0.sp - 48#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedEkSentCt1ReceivedAt_extract A
    (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 456#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 464#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 472#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 480#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 488#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 496#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_13', BitVec.add_assoc, arm64_norm]
  have hout_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5)) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5)) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_13', arm64_norm]
  have hhsp88 : s0.sp - 88#64 =
      CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s0 + 592#64 + 8#64 := by
    have h96 := CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 s0
    bv_omega
  wp_conv_pre => rw [hst_words]; simp only [wordsAt_16, arm64_norm]; rw [hhsp88]
  wp_steps
  wp_conv_pre => rw [← hhsp88]
  have hdec0_1 :
      (((s0.sp - 448#64) ↦₆₄ 0#64) ∗ ((s0.sp - 440#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 432#64) ↦₆₄ 0#64) ∗ ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ 2#64) ∗ ((s0.sp - 408#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 400#64) ↦₆₄ 0#64) ∗ ((s0.sp - 392#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 384#64) ↦₆₄ 0#64) ∗ ((s0.sp - 376#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 368#64) ↦₆₄ 2#64) ∗ ((s0.sp - 360#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 352#64) ↦₆₄ 0#64) ∗ ((s0.sp - 344#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 336#64) ↦₆₄ 0#64) ∗ ((s0.sp - 328#64) ↦₆₄ 0#64)) =
      wordsAt (s0.sp - 448#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_2 :
      (((s0.sp - 320#64) ↦₆₄ 2#64) ∗ ((s0.sp - 312#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 304#64) ↦₆₄ 0#64) ∗ ((s0.sp - 296#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 280#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 272#64) ↦₆₄ 2#64) ∗ ((s0.sp - 264#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 256#64) ↦₆₄ 0#64) ∗ ((s0.sp - 248#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 240#64) ↦₆₄ 0#64) ∗ ((s0.sp - 232#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 224#64) ↦₆₄ 2#64) ∗ ((s0.sp - 216#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 208#64) ↦₆₄ 0#64) ∗ ((s0.sp - 200#64) ↦₆₄ 2#64)) =
      wordsAt ((s0.sp - 448#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_3 :
      (((s0.sp - 192#64) ↦₆₄ 0#64) ∗ ((s0.sp - 184#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 176#64) ↦₆₄ 2#64) ∗ ((s0.sp - 168#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 160#64) ↦₆₄ 0#64) ∗ ((s0.sp - 152#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 144#64) ↦₆₄ 0#64) ∗ ((s0.sp - 136#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 128#64) ↦₆₄ 2#64) ∗ ((s0.sp - 120#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 112#64) ↦₆₄ 0#64) ∗ ((s0.sp - 104#64) ↦₆₄ 2#64) ∗
       ((CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s0 + 592#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 88#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 80#64) ↦₆₄ 2#64) ∗ ((s0.sp - 72#64) ↦₆₄ 0#64)) =
      wordsAt ((s0.sp - 448#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  refine SepWP.fold (Entails.of_eq hdec0_1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_2) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_3) (by sep_focus) ?_
  have hdec_recomp :
      wordsAt (s0.sp - 448#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
      wordsAt ((s0.sp - 448#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
      wordsAt ((s0.sp - 448#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
      ((s0.sp - 64#64) ↦₆₄ 80#64) ∗ ((s0.sp - 56#64) ↦₈ 0#8) ∗ memRegion (s0.sp - 55#64) 7 ⊢
      polyDecoderAt A (s0.sp - 448#64) (emptyPolyDecoder 80) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A (s0.sp - 448#64) 80 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunkX_inImage hadd_raw
    (s0.sp - 448#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 80) chunk
    (emptyPolyDecoder_strictSorted 80) (ret_pc := entry + 168#64) (sp_call := s0.sp - 448#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun0)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 _ hinv1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine sepWP_of_inv
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" "memcpy"))
    hinv1 ?_
  wp_conv_pre => rw [stackAt_addChunkX_to_extHook (s0.sp - 448#64)]
  refine SepWP.fold (cells_13_unfold' (s0.readReg64 (Reg.gpr 0#5))) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_13', arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_104_copy_recompose
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) st.uc g) (by sep_focus) ?_
  refine call_memcpy_relocate_cs_inImage hmemcpy_raw (s0 := s0)
    (CryptoVerification.SpqrV1.States.Leaves.Relocatable.of_polyDecoderAt A
      (addChunkTotal (emptyPolyDecoder 80) chunk))
    (s0.readReg64 (Reg.gpr 0#5) + 104#64) (s0.sp - 448#64)
    (ret_pc := entry + 216#64) (sp_call := s0.sp - 448#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx20_1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 _ => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_recompose A
    (s0.readReg64 (Reg.gpr 0#5)) st.uc (addChunkTotal (emptyPolyDecoder 80) chunk) outSt hout_eq)
    (by sep_focus) ?_
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A
    (s0.readReg64 (Reg.gpr 1#5)) st.sending_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i tag vecs
  wp_focus_pure; intro hvecs_len
  wp_steps
  refine SepWP.fold (stackAt_448_to_dropPoly16_ax s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  wp_call hpoly16_raw' ⟨s0.readReg64 (Reg.gpr 1#5) + 8#64, vecs⟩
  refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 104 504 rfl (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_448_from_dropPoly16 s0.sp) (by sep_focus) ?_
  wp_done

/-- `StatesRecvContractsAx.ct1ReceivedRecvCt2Chunk_ok` (`35936` B `growToCalleeExt` + `.inImage img`)
    from `AllocContractsX`, `DeallocOkExt`, and `AddChunkOkX`. -/
theorem ct1_received_recv_ct2_chunk_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax ct1ReceivedRecvCt2ChunkStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (ct1_received_recv_ct2_chunk_ok_inImage hAx hdealloc haddChunk)

theorem _root_.CryptoVerification.SpqrV1.States.RecvCt2Chunk.ct1_received_recv_ct2_chunk_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((ct1ReceivedRecvCt2ChunkSpec A F).inImage img) :=
  LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Ct1ReceivedExt.ct1_received_recv_ct2_chunk_ok_inImage
    hAx hdealloc haddChunk

theorem _root_.CryptoVerification.SpqrV1.States.RecvCt2Chunk.ct1_received_recv_ct2_chunk_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (haddChunk : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img) :=
  LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Ct1ReceivedExt.ct1_received_recv_ct2_chunk_ok_ax
    hAx hdealloc haddChunk

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Ct1ReceivedExt
