/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1ReceivedExt1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekSentCt1Received` Arm (`AllocContractsX`, Part 2)

`AllocContractsX`-backed proofs for the `msg.epoch = st.uc.epoch ∧ msg.payload ≠ .ct2 _` branch
and the post-call `.ok (.stillReceiving outSt)` branch of `.ekSentCt1Received`.
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

/-! ## 1. `.ekSentCt1Received` Arm: `msg.epoch = st.uc.epoch` & `msg.payload ≠ .ct2 _` -/

set_option maxHeartbeats 1200000 in
theorem ekSentCt1Received_arm_eq_other_ct2_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch) (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) hinv_img
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_6_of_not_ct2 hct2
  have hcond_tag2 := messagePayloadTag_bne_6_of_not_ct2 hct2
  have hwb := @states_recv_writeback_ct2_ax img A ext hAx (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range img.base (Rust.withPanics ext) 228 292
  states_recv_fetches_range img.base (Rust.withPanics ext) 4336 12
  states_recv_fetches_range img.base (Rust.withPanics ext) 10988 208
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
  have hfold_self :
      ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (((msgA + 8#64) ↦₈ messagePayloadTag msg.payload) ∗ messagePayloadTailAt msgA msg.payload) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        messagePayloadAt spqrPolyApi msgA msg.payload ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 6#64 w)
      (sepConj_mono_left (Entails.of_eq (messagePayloadAt_eq_tag_tail msgA msg.payload).symm))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
      (msgA ↦₆₄ msg.epoch) ∗ A.pool ∗ memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12, heq]; simp only [pointsTo128_eq_pair64_recv, arm64_norm]; ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          (msgA ↦₆₄ msg.epoch) ∗ A.pool ∗ memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
        hinv_wb rfl hrun hsp hsp_align (by simp only [arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    rw [hw12]; simp only [arm64_norm]; ac_rfl

/-! ## 2. Post-Call `.ok (.stillReceiving outSt)` Path -/

set_option maxHeartbeats 1200000 in
theorem ekSentCt1Received_post_call_still_ct2_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4384#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.stillReceiving outSt)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) hinv_img
  have hwb := @states_recv_writeback_ct2_ax img A ext hAx (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range img.base (Rust.withPanics ext) 4384 28
  states_recv_fetches_range img.base (Rust.withPanics ext) 12612 680
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (stillReceiving_result_976_extract A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun ⟨hcap, _⟩ => ?_
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hcond1 := cap_add_two_bne_zero_true hcap
  have hcond2 := cap_add_two_beq_zero_false hcap
  have hcond3 := cap_add_one_beq_zero_false_recv hcap
  have hcond4 := cap_add_one_bne_zero_true_recv hcap
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, w_out.b3.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6,
             sp.b0.w7, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, w_out.b3.w6, sp.b1.w4, sp.b1.w5, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨sp.b2.w0, sp.b2.w1, w_out.b4.w9, sp.b2.w3, w_out.b4.w5, w_out.b0.w1, w_out.b4.w8,
             6#64, noneCap, sp.b2.w9⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6, w61 := w_out.b0.w2, w62 := w_out.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w_out.q60 }
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 qac0
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
       ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ qac0) ∗
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
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt)
        (wordsBytes (words63List w_out)) ∗
      memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, noneCap]
    simp only [pointsTo128_eq_pair64_recv, arm64_norm]; ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt)
            (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt)
            (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt)
          (wordsBytes (words63List w_out)))
        hinv_wb rfl hrun hsp hsp_align (by simp only [arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    rcases w_out with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm]; ac_rfl

end CryptoVerification.SpqrV1.States.Recv
