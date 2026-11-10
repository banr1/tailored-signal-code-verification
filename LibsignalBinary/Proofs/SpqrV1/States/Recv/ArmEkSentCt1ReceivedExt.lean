/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1ReceivedExt1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1ReceivedExt2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekSentCt1Received` Arm (`AllocContractsX`, Part 3)

Verifies the post-call `.done` path, contract-backed `<EkSentCt1Received>::recv_ct2_chunk` call
rule, `eq_ct2` branch, and top-level theorem `states_recv_ekSentCt1Received_ok_x_ax`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel
  BitVec.toNat_zero Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

/-! ## 1. Post-Call `.ok (.done (nhr, sec))` Path -/

set_option maxHeartbeats 1600000 in
private theorem ekSentCt1Received_post_call_done_ct2_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4384#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.done (nhr, sec))) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        ((img.base +
          bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := some sec, state := .noHeaderReceived nhr }) ∗
          ((img.base +
            bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) hinv_img
  have hadrp := fnAddr_adrp_59974 (b := img.base) (H := Rust.withPanics ext) hb
  have hwb := @states_recv_writeback_ct2_ax img A ext hAx (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range img.base (Rust.withPanics ext) 4384 28
  states_recv_fetches_range img.base (Rust.withPanics ext) 12612 348
  states_recv_fetches_range img.base (Rust.withPanics ext) 17660 124
  states_recv_fetches_range img.base (Rust.withPanics ext) 17960 188
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hadrp hwb ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (done_result_976_extract A ((s0.sp - 4240#64) + 976#64) nhr sec)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g p v_sec w_pad
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let w_out := mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At, mkWords63_done, noneCap]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨p.b4.w5, p.b2.w8, w_out.b3.w2, w_out.b3.w0, sp.b0.w4, p.b3.w4, sp.b0.w6,
             p.b3.w1, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, p.b4.w8, p.b3.w2, w_out.b3.w7, p.b4.w6, p.b3.w0, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨p.b4.w0, p.b4.w4, w_out.b5.w0, p.b3.w6, w_out.b4.w6, w_out.b0.w2, w_out.b4.w9,
             7#64, w_out.b5.w8, w_out.b4.w3⟩
      b3 := ⟨sp.b3.w0, sp.b3.w1, w_out.b1.w9, w_out.b2.w2, w_out.b2.w8, w_out.b0.w8,
             w_out.b1.w4, w_out.b2.w6, w_out.b3.w1, w_out.b2.w9⟩
      b4 := ⟨w_out.b2.w7, w_out.b1.w3, w_out.b2.w0, w_out.b1.w1, w_out.b2.w3, w_out.b0.w6,
             w_out.b0.w5, w_out.b1.w2, w_out.b2.w1, w_out.b2.w4⟩
      b5 := ⟨w_out.b1.w0, w_out.b4.w5, w_out.b1.w5, w_out.b0.w9, w_out.b1.w8, w_out.b5.w1,
             w_out.b0.w4, w_out.b2.w5, w_out.b4.w7, w_out.b5.w5⟩
      w60 := w_out.b5.w7, w61 := w_out.b0.w3, w62 := w_out.b0.w7
      q200 := w_out.q60, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 w_out.q60
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
       ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w_out.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono
      (words63At_376_entails_memRegion_880
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
      (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret) (wordsBytes (vecWordsList v_sec)) ∗
      ((img.base +
        bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, w_out, mkWords63_done, noneCap]
    simp only [pointsTo128_eq_pair64_recv, arm64_norm]; ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret) (wordsBytes (vecWordsList v_sec)) ∗
          ((img.base +
            bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0) =
        (P_rest ∗
          ((img.base +
            bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret) (wordsBytes (vecWordsList v_sec))) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          ((img.base +
            bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret) (wordsBytes (vecWordsList v_sec)))
        hinv_wb rfl hrun hsp hsp_align (by simp only [arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_noHeaderReceived_some_entails_resultV1RecvAt A (F := F) outA nhr sec g p
      v_sec p.b2.w5 sp.b3.w0 w_out.b5.w9 sp.q3c0 sp.b3.w1
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, w_out, mkWords63_done, mkWords63_nhr_tail,
      Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm]; ac_rfl

/-! ## 2. Contract-Backed `recv_ct2_chunk` Call Rule & `eq_ct2` Arm -/

private theorem call_ekSentCt1ReceivedRecvCt2Chunk_ext_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry ((recvCt2ChunkSpecExt K F A img.base).inImage img))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2)
    (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗ ekSentCt1ReceivedAt A stA st ∗
      chunkAt chunkA chunk ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool ∗ stackAt sp_call recvCt2ChunkStackExt) ∗ Frame)
    (hpanic : ∀ sf P_f, ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
          allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 → ImgCallInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA
            (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool ∗ stackAt sp_call recvCt2ChunkStackExt) ∗ Frame) post) :
    SepWPp prog (s0.readReg64 Reg.lr) s P post Q_panic := by
  refine SepWPp.call_inImage hcall hinv_img
    (x := ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [recvCt2ChunkSpecExt]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hsort, hroot⟩, hm⟩
  · dsimp only [Spec.inImage, recvCt2ChunkSpecExt] at hmem
    refine allowPanic_frame (fun ⟨hdisj, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hdisj ⊢; rw [htrace.1] at hdisj htr_sub; exact ⟨hdisj, htr_sub⟩
  · dsimp only [Spec.inImage, recvCt2ChunkSpecExt]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => SepWPp.of_sepWP_ret ?_
    have hassoc :
        (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA
            (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool ∗ stackAt sp_call recvCt2ChunkStackExt) ∗ Frame =
        (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA
            (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          (memRegion stA chunkedEkSentCt1ReceivedSize ∗ (chunkAt chunkA chunk ∗
            (tokenInitAt img.base ∗ (reduceTableAt img.base ∗
              (A.pool ∗ stackAt sp_call recvCt2ChunkStackExt)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf

set_option maxHeartbeats 1600000 in
private theorem ekSentCt1Received_arm_eq_ct2_ax {P_extra : SepProp}
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hcall : RecvCt2ChunkOkExt img K F A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hsplit_stk : stackAt (s0.sp - 4240#64) recvCt2ChunkStackExt =
      P_extra ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢ (P_rest ∗ P_extra) ∗
        resultV1RecvAt A (F := F) outA (States.recv K (.ekSentCt1Received st) msg) ∗
        memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
        ((img.base +
          bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗
        A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f, ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
          allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((img.base +
          bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) recvCt2ChunkStackExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      Q_post Q_panic := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy_raw := session_memcpy_region_ok_at_ct2_ax hAx statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  have hpost_err := @ekSentCt1Received_post_call_err_56574 A F img.base ext s0
  have hpost_still := @ekSentCt1Received_post_call_still_ct2_ax img A F ext hAx s0
  have hpost_done := @ekSentCt1Received_post_call_done_ct2_ax img A F ext hb hAx s0
  have hcall' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName)
      ((recvCt2ChunkSpecExt K F A img.base).inImage img) := hcall
  have hof_ct2 : ∀ {sm1 : State} {Pm1 : SepProp}, ImgCallInv img sm1 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName) sm1 Pm1
        (fun sm2 Pm2 => ImgCallInv img sm2 →
          SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2 Pm2 Q_post Q_panic) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm1 Pm1 Q_post Q_panic :=
    fun hinv1 hwp => SepWPp.of_sepWP_inImage hinv1 hwp
  rw [fnAddr_fwd_recvCt2Chunk] at hcall' hof_ct2
  apply SepWPp.of_sepWP_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv_img
  states_recv_fetches_range img.base (Rust.withPanics ext) 228 292
  states_recv_fetches_range img.base (Rust.withPanics ext) 4336 48
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw hcall' hof_ct2 hpost_err hpost_still hpost_done hdone ⊢
  rcases hinv with ⟨hsort, hroot⟩
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12, heq, hpay, messagePayloadAt_ct2 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 120
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, sp.b2.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             sp.b2.w8, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             sp.b3.w8, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, sp.b4.w5, w.b0.w4, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, w.b0.w3, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have hfold_pre_memcpy :
      (words63At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗
        (memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗ memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
        (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗ memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (recompose63 (selfA + 8#64) w)
      (sepConj_mono
        (Entails.of_eq (memRegion_880_split_504_376_ct2 ((s0.sp - 4240#64) + 976#64)
          ((s0.sp - 4240#64) + 1480#64) (by bv_omega)))
        (sepConj_mono_left
          (Entails.of_eq (memRegion_880_split_504_376_ct2 ((s0.sp - 4240#64) + 1856#64)
            ((s0.sp - 4240#64) + 2360#64) (by bv_omega)))))
  refine SepWP.fold
    (F := P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 512#64) 416 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      ((img.base +
        bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) recvCt2ChunkStackExt ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
    hfold_pre_memcpy ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12, heq]; simp only [pointsTo128_eq_pair64_recv, arm64_norm]; ac_rfl
  · refine SepWP.done rfl hrun fun hinv1 => hof_ct2 hinv1 ?_
    refine call_memcpy_relocate_cs_inImage_stk_ct2_ax
      (stk := recvCt2ChunkStackExt) (k_stk := 3888)
      hmemcpy_raw (Relocatable.of_chunkedEkSentCt1ReceivedAt A st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
      hinv1 rfl hrun hsp hfsp_align rfl htr
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by decide) (by decide) (by sep_frame) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv_sf1
    simp only [arm64_norm] at hpc1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [arm64_norm, hx19])
    have hx24_1 : sf1.readReg64 .x24 = msgA :=
      hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx24])
    have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])
    have hfold_self :
        chunkedEkSentCt1ReceivedAt A ((s0.sp - 4240#64) + 1856#64) st ∗
        ((selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 8#64) 504 ∗ memRegion (selfA + 512#64) 416) ⊢
          (ekSentCt1ReceivedUcAt A ((s0.sp - 4240#64) + 1856#64) st.uc ∗
           polyDecoderAt A ((s0.sp - 4240#64) + 1960#64) st.receiving_ct2) ∗
          memRegion selfA chunkedStatesSize := by
      unfold chunkedEkSentCt1ReceivedAt unchunkedEkSentCt1ReceivedAt
      rw [show ((s0.sp - 4240#64) + 1856#64) + 104#64 = (s0.sp - 4240#64) + 1960#64 by bv_omega]
      exact sepConj_mono_right (self_504_416_entails_memRegion_928 selfA 6#64)
    refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
    generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
    wp_steps 10
    subst hsp0
    refine SepWP.done rfl hrun1 fun hinv2 => ?_
    refine call_ekSentCt1ReceivedRecvCt2Chunk_ext_ax hb hcall'
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk hsort hroot (s0 := s0) (sp_call := s0.sp - 4240#64) (R := R)
      (Frame := P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        ((img.base +
          bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ statesRecvSavedCells s0)
      hinv2 rfl hrun1 hsp1 hfsp_align rfl htr1
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by dsimp only [chunkedEkSentCt1ReceivedSize, ekSentCt1ReceivedAt, BitVec.ofNat_eq_ofNat]
          simp only [arm64_norm]; ac_rfl)
      hpanic ?_
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv_sf2
    simp only [arm64_norm] at hpc2
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct2 msgA chunk]
    have hx19_2 : sf2.readReg64 .x19 = outA :=
      hcs2.1.trans (by simp only [arm64_norm, hx19_1])
    cases hres : st.recv_ct2_chunk K st.uc.epoch chunk with
    | error err =>
      cases err with
      | panic _ =>
        dsimp only [ekSentCt1ReceivedRecvChunkResultAt]; rw [sepConj_assoc]
        exact SepWP.pure_elim (fun hfalse => False.elim hfalse)
      | err e =>
        have he := recv_ct2_chunk_err_eq_macVerifyFailed st st.uc.epoch chunk e hres
        subst he
        have hmodel :=
          states_recv_ekSentCt1Received_eq_ct2_err K st msg chunk .macVerifyFailed heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_err sf2 outA sp1
              ((P_rest ∗ P_extra) ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               ((img.base +
                 bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
               tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f
                ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
                 hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq, hsplit_stk]; dsimp only [chunkedEkSentCt1ReceivedSize]
        simp only [arm64_norm]; ac_rfl
    | ok outRes =>
      cases outRes with
      | stillReceiving outSt =>
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_still K st msg chunk outSt heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_still sf2 outA outSt sp1
              ((P_rest ∗ P_extra) ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               ((img.base +
                 bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
               tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
              hinv_sf2 hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f
                ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
                 hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq, hsplit_stk]; dsimp only [chunkedEkSentCt1ReceivedSize]
        simp only [arm64_norm]; ac_rfl
      | done pair =>
        rcases pair with ⟨nhr, sec⟩
        have hmodel :=
          states_recv_ekSentCt1Received_eq_ct2_done K st msg chunk nhr sec heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_done sf2 outA nhr sec sp1
              ((P_rest ∗ P_extra) ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
              hinv_sf2 hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f
                ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
                 hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq, hsplit_stk]; dsimp only [chunkedEkSentCt1ReceivedSize]
        simp only [arm64_norm]; ac_rfl

/-! ## 3. Complete `.ekSentCt1Received` Arm & Variant Theorem (`states_recv_ekSentCt1Received_ok_x_ax`) -/

private theorem states_recv_arm_ekSentCt1Received_inImage_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : RecvCt2ChunkOkExt img K F A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hinv : statesRecvPreInv (.ekSentCt1Received st)) (himg_s : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ekSentCt1Received st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ekSentCt1Received st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hpre_comm :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
      (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384) ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗ messageAt spqrPolyApi msgA msg ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; ac_rfl
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
    rw [states_recv_ekSentCt1Received_gt K st msg hgt, hpre_comm]
    refine SepWP.mono
      (ekSentCt1Received_arm_gt hdealloc s0 s outA selfA msgA st msg
        (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
         hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
      rw [states_recv_ekSentCt1Received_lt K st msg hlt, hpre_comm]
      refine SepWP.mono
        (ekSentCt1Received_arm_lt_ct2_ax hAx s0 s outA selfA msgA st msg
          (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
          himg_s hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
           hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct2 chunk =>
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt img.base ∗
                (((img.base +
                  bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
                  ((img.base +
                    bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt img.base ∗ reduceTableAt img.base) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTableAt img.base ∗
                ((img.base +
                  bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
                memRegion (s0.sp - 40176#64) 15664) ∗
              memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              ((img.base +
                bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) recvCt2ChunkStackExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by
          rw [stackAt_statesRecvCalleeExt_eq_recvCt2Ext s0.sp]; ac_rfl]
        refine ekSentCt1Received_arm_eq_ct2_ax
          (P_extra := memRegion ((s0.sp - 4240#64) - 20272#64) 720)
          (K := K) hb hAx hcall s0 s outA selfA msgA st msg chunk
          (statesRecvJumpTableAt img.base ∗
            ((img.base +
              bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
            memRegion (s0.sp - 40176#64) 15664) R
          (stackAt_recvCt2ChunkExt_eq_X (s0.sp - 4240#64))
          hinv himg_s heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
          (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
          (fun sf Pf hpan hmem_f => ?_)
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpecExt]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          rw [stackAt_statesRecvStackXExt_eq_X s0.sp, ← memRegion_statesRecv_15664_720 s0.sp]
          ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpecExt, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          refine ⟨⟨?_, hpan'.1.2⟩, hpan'.2⟩
          cases hpan'.1.1 with
          | inl hp =>
            exact Or.inl (states_recv_ekSentCt1Received_eq_ct2_panic K st msg chunk heq hpay hp)
          | inr haf => exact Or.inr haf
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1 _ | ct1Ack _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
        rw [states_recv_ekSentCt1Received_eq_other K st msg heq hct2, hpre_comm]
        refine SepWP.mono
          (ekSentCt1Received_arm_eq_other_ct2_ax hAx s0 s outA selfA msgA st msg
            (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
            himg_s heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
             hsp_sf, hcs_sf, htr_sf⟩)

/-- Per-variant `.inImage img` specification proof for `States.ekSentCt1Received st`
    (`tag = 6#64`, `40176` bytes stack, `AllocContractsX` + `DeallocOkExt` + `RecvCt2ChunkOkExt`). -/
theorem states_recv_ekSentCt1Received_ok_x_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : RecvCt2ChunkOkExt img K F A ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ekSentCt1Received st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackXExt ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_ext (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_ct2 himg0 hpro ?_
  intro s1 hpc1 hrun1 himg1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, _, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 6#64
    (chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean_inImage_ct2 himg1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 himg2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; ac_rfl))
    (states_recv_arm_ekSentCt1Received_inImage_ax hb hAx hdealloc hcall s0 s2 outA selfA msgA st msg R
      hinv himg2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1))

end CryptoVerification.SpqrV1.States.Recv
