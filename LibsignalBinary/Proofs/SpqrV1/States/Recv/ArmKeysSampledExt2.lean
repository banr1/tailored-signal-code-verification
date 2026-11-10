/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.keysSampled` Arm (`AllocContractsX`, Part 2)

**Checked by Lean.** Lifts `keysSampled_arm_eq_other`, `call_keysSampledRecvCt1Chunk`,
`keysSampled_arm_eq_ct1`, `states_recv_arm_keysSampled`, and `states_recv_keysSampled_ok_x_ext`
to `AllocContractsX` and `DeallocOkExt` at `statesRecvStackXExt` (`40176` B).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

/-! ## 1. `.keysSampled` (`+1796`): `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c` -/

set_option maxHeartbeats 1200000 in
/-- `.keysSampled` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    (`+1796 -> s0.x30`) under `AllocContractsX img A ext` at `statesRecvCalleeStackXExt`. -/
theorem keysSampled_arm_eq_other_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1796#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_5_of_not_ct1 hct1
  have hcond_tag2 := messagePayloadTag_bne_5_of_not_ct1 hct1
  have hwb := @states_recv_writeback_59e88_stk_ext img A ext hAx (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) hinv
  states_recv_fetches_range img.base (Rust.withPanics ext) 1796 300
  states_recv_fetches_range img.base (Rust.withPanics ext) 7084 16
  states_recv_fetches_range img.base (Rust.withPanics ext) 8212 160
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  refine SepWP.done rfl (by exact hrun) fun hinv1 => ?_
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 3#64,
             noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w.q60 }
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
      memRegion (s0.sp - 4240#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
      memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
        sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_self_unused :
      ((selfA ↦₆₄ 3#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 3#64 w)
      (sepConj_mono_left hfold_unused)
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      statesRecvSavedCells s0)
    hfold_self_unused ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl_recv_ext
  · refine sepWP_weaken_mono_recv_ext
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hinv1 rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_keysSampled_entails_resultV1RecvAt A (F := F) outA st w
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx1]
    sep_ac_rfl_recv_ext

/-! ## 2. `.keysSampled` (`+1796`): `msg.epoch = st.uc.epoch` and `msg.payload = .ct1 chunk` -/

/-- Framed `.inImage img` call rule for `growToCalleeExtSendEk keysSampledRecvCt1ChunkStack
    (keysSampledRecvCt1ChunkSpec A F)` at stack `statesRecvCalleeStackXExt` (`35936` B). -/
theorem call_keysSampledRecvCt1Chunk_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      ((growToCalleeExtSendEk keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch)
    (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A stA st ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      ImgCallInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkedHeaderSentAt A outA outSt ∗
          memRegion stA 504 ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame) post) :
    SepWPp prog (s0.readReg64 Reg.lr) s P post Q_panic := by
  refine SepWPp.call_imgInv hcall hinv_img
    (x := ⟨outA, stA, chunkA, st, chunk, outSt⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    refine satisfies_inImage_pre hinv_img ?_
    rw [hsplit] at hm
    dsimp only [growToCalleeExtSendEk, keysSampledRecvCt1ChunkSpec]
    rw [hsp]
    rw [stackAt_statesRecvCalleeExt_split sp_call keysSampledRecvCt1ChunkStack] at hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_recv_ext)) hm⟩
  · dsimp only [Spec.inImage, growToCalleeExtSendEk, keysSampledRecvCt1ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [Spec.inImage, growToCalleeExtSendEk, keysSampledRecvCt1ChunkSpec]
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf)
    rw [stackAt_statesRecvCalleeExt_split sp_call keysSampledRecvCt1ChunkStack]
    exact Entails.of_eq (by sep_ac_rfl_recv_ext)

set_option maxHeartbeats 1600000 in
/-- `.keysSampled` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct1 chunk`
    (`+1796 -> s0.x30`) under `AllocContractsX img A ext` at `statesRecvCalleeStackXExt`. -/
theorem keysSampled_arm_eq_ct1_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((growToCalleeExtSendEk keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1796#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢
        P_rest ∗
        resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
        memRegion selfA chunkedStatesSize ∗
        messageAt spqrPolyApi msgA msg ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗
        stackAt s0.sp statesRecvStackXExt) ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      sf.trace = s0.trace →
      Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      Q_post Q_panic := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hadrp := fnAddr_adrp_57010 (b := img.base) (H := Rust.withPanics ext) hb
  have hpost := @keysSampled_post_call_57298_ext img A F ext hAx s0
  apply SepWPp.of_sepWP_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName) hinv
  rw [fnAddr_fwd_keysSampledRecvCt1] at hcall ⊢
  states_recv_fetches_range img.base (Rust.withPanics ext) 1796 300
  states_recv_fetches_range img.base (Rust.withPanics ext) 7084 44
  states_recv_fetches_range img.base (Rust.withPanics ext) 7324 424
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hadrp hcall hpost hdone ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (memRegion_880_entails_words63_376
    ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)) (by sep_focus) ?_
  wp_pull_exists; rename_i w_arg
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62, heq, hpay, messagePayloadAt_ct1 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             msgA, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, sp.b4.w1, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, sp.b5.w1, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, sp.b5.w6, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
      memRegion (s0.sp - 4240#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
      memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
        sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_pre_call :
      ((selfA ↦₆₄ 3#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (words63At ((s0.sp - 4240#64) + 976#64) w ∗
       relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w))) ∗
      (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        chunkedKeysSampledAt A ((s0.sp - 4240#64) + 976#64) st ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 3#64 w)
      (sepConj_mono (recompose63 ((s0.sp - 4240#64) + 976#64) w)
        (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      statesRecvSavedCells s0)
    hfold_pre_call ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl_recv_ext
  · refine SepWP.done rfl (by exact hrun) fun hinv_call => ?_
    refine call_keysSampledRecvCt1Chunk_ext hcall
      ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 976#64) (msgA + 10#64)
      st chunk outSt hrecv
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := entry + 7748#64)
      (R := R)
      (Frame :=
        P_rest ∗
        memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hinv_call rfl hrun hsp hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      htr
      (by simp only [Reg.x0, arm64_norm])
      (by simp only [Reg.x1, arm64_norm])
      (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x3, arm64_norm])
      (by
        dsimp only [chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]
        sep_ac_rfl_recv_ext)
      hpanic
      ?_
    intro sf_c hpc_c hrun_c hsp_c hcs_c htr_c hinv_c
    have hrejoin_976 :
        memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ⊢
          memRegion ((s0.sp - 4240#64) + 976#64) 880 :=
      Entails.of_eq (memRegion_880_split_504_376
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)).symm
    refine SepWP.focus_weaken hrejoin_976 (by sep_focus) ?_
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct1 msgA chunk]
    have hx19_c : sf_c.readReg64 .x19 = outA := by
      rw [hcs_c.1]; simp only [Reg.x19, arm64_norm, hx19]
    have hx20_c : sf_c.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64 := by
      rw [hcs_c.2.1]; simp only [Reg.x20, arm64_norm, hsp]
    refine SepWP.weaken_pre (Entails.of_eq ?_)
      (SepWP.mono
        (hpost sf_c outA outSt sp1
          (P_rest ∗
           memRegion selfA chunkedStatesSize ∗
           ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
           ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
           A.pool)
          hinv_c hpc_c hrun_c hsp_c hsp_align hx19_c hx20_c htr_c)
        (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          hdone sf Pf hpc_f hrun_f
            ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)),
             hsp_sf, hcs_sf, htr_sf⟩))
    rw [← hmsg_eq]
    simp only [arm64_norm]
    sep_ac_rfl_recv_ext

/-! ## 3. Full `.keysSampled` Arm & Variant Theorem (`AllocContractsX`) -/

/-- Complete `.keysSampled` arm of `<States>::recv` (`+1796 -> s0.x30`) at `statesRecvStackXExt`
    (`40176` B) under `AllocContractsX img A ext` and `DeallocOkExt img.base A ext`. -/
theorem states_recv_arm_keysSampled_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((growToCalleeExtSendEk keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hinv_img : ImgCallInv img s)
    (hinv : statesRecvPreInv (.keysSampled st))
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1796#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoAt img.base ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.keysSampled st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.keysSampled st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.keysSampled st) msg _ R ?_
    rw [states_recv_keysSampled_gt K st msg hgt]
    refine sepWP_weaken_mono_recv_ext
      (keysSampled_arm_gt_ext hdealloc s0 s outA selfA msgA st msg (statesRecvRoAt img.base)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)), hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.keysSampled st) msg _ R ?_
      rw [states_recv_keysSampled_lt K st msg hlt]
      refine sepWP_weaken_mono_recv_ext
        (keysSampled_arm_lt_ext hAx s0 s outA selfA msgA st msg (statesRecvRoAt img.base)
          hinv_img hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct1 chunk =>
        obtain ⟨outSt, hrecv⟩ := keysSampled_recv_ct1_ok_of_preInv st hinv chunk
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl_recv_ext))
          (keysSampled_arm_eq_ct1_ext hb hAx hcall s0 s outA selfA msgA st msg chunk outSt
            (statesRecvJumpTableAt img.base ∗
              ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
              tokenInitAt img.base ∗ reduceTableAt img.base) R
            hinv_img heq hpay hrecv hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpecExt]
          rw [states_recv_keysSampled_eq_ct1_ok K st msg chunk outSt heq hpay hrecv,
              sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          sep_ac_rfl_recv_ext
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpecExt, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨Or.inr hpan'.1.1, hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
        have hct1 : ∀ c, msg.payload ≠ .ct1 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.keysSampled st) msg _ R ?_
        rw [states_recv_keysSampled_eq_other K st msg heq hct1]
        refine sepWP_weaken_mono_recv_ext
          (keysSampled_arm_eq_other_ext hAx s0 s outA selfA msgA st msg (statesRecvRoAt img.base)
            hinv_img heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)), hsp_sf, hcs_sf, htr_sf⟩)

/-- Per-variant `.inImage img` specification proof for `States.keysSampled st` (`tag = 3#64`) at
    `statesRecvStackXExt` (`40176` B) under `AllocContractsX img A ext` and
    `DeallocOkExt img.base A ext`. -/
theorem states_recv_keysSampled_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((growToCalleeExtSendEk keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.keysSampled st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hsym0⟩, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  have hinv0 : ImgCallInv img s0 := ⟨hF0, hsym0⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗
      (memRegion (s0.sp - 40176#64) 16384 ∗
       memRegion outA v1RecvSize ∗
       chunkedStatesAt A selfA (.keysSampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_recv_ext)) hmem, ?_⟩
  have hpro := states_recv_prologue (b := img.base) (ext := ext) s0
    (memRegion (s0.sp - 40176#64) 16384 ∗
     memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysSampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_sendek hinv0 hpro ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 3#64
    (memRegion (s0.sp - 40176#64) 16384 ∗
     chunkedKeysSampledAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean_inImage_sendek hinv1
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_recv_ext)) hdisp) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      dsimp only [chunkedStatesAt]
      rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
      sep_ac_rfl_recv_ext))
    (states_recv_arm_keysSampled_ext hb hAx hdealloc hcall s0 s2 outA selfA msgA st msg R
      hinv2 hinv hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 htr20)

alias states_recv_keysSampled_ok_x_ax := states_recv_keysSampled_ok_x_ext

end CryptoVerification.SpqrV1.States.Recv
