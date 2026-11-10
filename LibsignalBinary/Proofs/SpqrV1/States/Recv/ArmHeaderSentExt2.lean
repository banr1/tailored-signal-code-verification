/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.headerSent` Arm (`AllocContractsX`)

`AllocContractsX` and `.inImage img` post-call writeback blocks (`+5108`), `growToCalleeExt`
`<HeaderSent>::recv_ct1_chunk` call rule, and top-level `.headerSent` contracts
`states_recv_headerSent_ok_x_{ext,ax}` at `statesRecvStackXExt` (`40176` B).
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
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel
  BitVec.toNat_zero Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs bv880_toNat_hs

/-! ## 1. Post-Call Writeback Blocks (`+5108`) under `AllocContractsX` -/

set_option maxHeartbeats 1200000 in
theorem headerSent_post_call_done_56848_hs_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        headerSentRecvChunkAt A ((s0.sp - 4240#64) + 976#64) (.done outSt) ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) hinv_img
  have hadrp := fnAddr_adrp_569c0 (b := img.base) (H := Rust.withPanics ext) hb
  have hwb := @states_recv_writeback_59e88_ext img A ext hAx (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range img.base (Rust.withPanics ext) 5108 420
  states_recv_fetches_range img.base (Rust.withPanics ext) 5712 52
  states_recv_fetches_range img.base (Rust.withPanics ext) 14892 80
  dsimp only [tripleRatchetProgAtExt, statesRecvName, headerSentRecvChunkAt,
    BitVec.ofNat_eq_ofNat] at hpc hadrp hwb ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have h984 : ((s0.sp - 4240#64) + 976#64) + 8#64 = (s0.sp - 4240#64) + 984#64 := by bv_omega
  have h1488 : ((s0.sp - 4240#64) + 976#64) + 512#64 = (s0.sp - 4240#64) + 1488#64 := by bv_omega
  rw [h984, h1488]
  refine SepWP.fold (sendEkUnusedAt_split_f10 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_f10
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A ((s0.sp - 4240#64) + 984#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun _ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hx21 hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, sp.b1.w3, w_out.b5.w3, w_out.b3.w7, w_out.b0.w0,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, sp.b2.w4, sp.b2.w5, w_out.b4.w8,
             5#64, noneCap, w_out.b4.w2⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6
      w61 := w_out.b0.w2
      w62 := w_out.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w_out.q60 }
  have hfold_976 :
      (((s0.sp - 4240#64) + 976#64) ↦₆₄ 2#64) ∗
      words63At ((s0.sp - 4240#64) + 984#64) w_out ∗
      memRegion ((s0.sp - 4240#64) + 1488#64) 368 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 := by
    have h := done_976_entails_memRegion_880 ((s0.sp - 4240#64) + 976#64) w_out
    rw [h984, h1488] at h
    exact h
  have hfold_unused := sendEkUnusedAt_rejoin_f10 (s0.sp - 4240#64) w_out.q60
  have hfold_all :
      ((((s0.sp - 4240#64) + 976#64) ↦₆₄ 2#64) ∗
       words63At ((s0.sp - 4240#64) + 984#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1488#64) 368) ∗
      (((s0.sp - 4240#64 + 3856#64) ↦₁₂₈ w_out.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2736#64) 1120 ∗
       memRegion (s0.sp - 4240#64 + 3872#64) 272) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono hfold_976 (sepConj_mono_left hfold_unused)
  refine SepWP.fold
    (F := P_rest ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      statesRecvSavedCells s0)
    hfold_all ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        hinv_wb rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrec)))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    simp only [arm64_norm]
    ac_rfl

set_option maxHeartbeats 1200000 in
theorem headerSent_post_call_still_56848_hs_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        headerSentRecvChunkAt A ((s0.sp - 4240#64) + 976#64) (.stillReceiving outSt) ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv_img
  have hmemcpy_raw := session_memcpy_region_ok_at_ext_of_alloc hAx statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  states_recv_fetches_range img.base (Rust.withPanics ext) 5108 12
  states_recv_fetches_range img.base (Rust.withPanics ext) 14424 548
  dsimp only [tripleRatchetProgAtExt, statesRecvName, headerSentRecvChunkAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376_tag A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out tailBytes
  refine SepWP.pure_elim fun ⟨hw0, hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @states_recv_writeback_59e88_ext img A ext hAx (F_tail := fun a => a ↦ₛ tailBytes)
    hrel_tail s0
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hwb
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h1480 : ((s0.sp - 4240#64) + 976#64) + 504#64 = s0.sp - 2760#64 := by bv_omega
  rw [h1480]
  generalize hsp0 : s0.sp = sp0 at hsp hx21 hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  refine SepWP.done rfl (by exact hrun) fun hinv_call => ?_
  refine call_memcpy_relocate_cs_inImage_stk_ext (ret_pc := entry + 14836#64)
    (stk := statesRecvCalleeStackX) (k_stk := 3168) hmemcpy_raw hrel_tail
    (sp0 - 3664#64) (sp0 - 2760#64)
    hinv_call rfl (by exact hrun) (by exact hsp) hfsp_align rfl (by exact htr) rfl
    (by simp only [Reg.x1, arm64_norm, hx21]) rfl
    (by decide) (by decide) (by sep_frame) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1
  have hx19_1 : sf1.readReg64 .x19 = outA :=
    hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx20_1 : sf1.readReg64 .x20 = w_out.b5.w5 := hcs1.2.1
  have hx22_1 : sf1.readReg64 .x22 = w_out.b0.w1 := hcs1.2.2.2.1
  have hx23_1 : sf1.readReg64 .x23 = w_out.b1.w8 := hcs1.2.2.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = w_out.b3.w1 := hcs1.2.2.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w_out.b3.w4 := hcs1.2.2.2.2.2.2.1
  have hx26_1 : sf1.readReg64 .x26 = w_out.b3.w2 := hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : sf1.readReg64 .x27 = w_out.b3.w3 := hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w_out.b5.w2 := hcs1.2.2.2.2.2.2.2.2.2.1
  apply SepWP.seq_inImage (mid := entry + 18996#64) hinv1
  wp_steps
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, w_out.b3.w5, sp.b0.w2, w_out.b2.w9, sp.b0.w4, w_out.b4.w1, w_out.b4.w0,
             w_out.b3.w8, sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, w_out.b3.w9, w_out.b3.w6, w_out.b5.w3, w_out.b3.w7,
             w_out.b0.w0, w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, w_out.b4.w5, sp.b2.w5,
             w_out.b4.w8, 4#64, noneCap, w_out.b4.w2⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6
      w61 := w_out.b0.w2
      w62 := w_out.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w_out.q60 }
  have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
  have h2760 : s0.sp - 2760#64 = (s0.sp - 4240#64) + 1480#64 := by bv_omega
  rw [h3664, h2760]
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono_left (words63At_376_entails_memRegion_880
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, Reg.x23]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm, hx23_1, hw62]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes)) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun1 fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes))
        hinv_wb rfl hrun1 hsp1 hsp_align
        (by simp only [Reg.x19, arm64_norm, hx19_1])
        htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA outSt w_out tailBytes
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    simp only [arm64_norm, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hw62]
    ac_rfl

/-! ## 2. `.inImage img` + `growToCalleeExt` Call Rule & `eq_ct1` Arm -/

private theorem call_headerSentRecvCt1Chunk_hs_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes)
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
      chunkedHeaderSentAt A stA st ∗ chunkAt chunkA chunk ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      ImgCallInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame) post) :
    SepWPp prog (s0.readReg64 Reg.lr) s P post Q_panic := by
  refine SepWPp.call_inImage hcall hinv_img
    (x := ⟨outA, stA, chunkA, st, chunk, outRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by dsimp only [growToCalleeExt] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
    (h_no_oom := fun _ _ _ h => by
      dsimp only [growToCalleeExt] at h; exact (not_satisfies_false_sepConj h).elim)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [growToCalleeExt, headerSentRecvCt1ChunkSpec]
    rw [hsp]
    rw [stackAt_statesRecvCalleeExt_split sp_call headerSentRecvCt1ChunkStack] at hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hsort, hrecv⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl_recv_ext)) hm⟩
  · dsimp only [growToCalleeExt, headerSentRecvCt1ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [growToCalleeExt, headerSentRecvCt1ChunkSpec]
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf)
    rw [stackAt_statesRecvCalleeExt_split sp_call headerSentRecvCt1ChunkStack]
    exact Entails.of_eq (by sep_ac_rfl_recv_ext)

set_option maxHeartbeats 1600000 in
private theorem headerSent_arm_eq_ct1_hs_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 780#64)
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
        resultV1RecvAt A (F := F) outA (States.recv K (.headerSent st) msg) ∗
        memRegion selfA chunkedStatesSize ∗
        messageAt spqrPolyApi msgA msg ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      Q_post Q_panic := by
  refine SepWPp.of_sepWP_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
    hinv_img ?_
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv_img
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy_raw := session_memcpy_region_ok_at_ext_of_alloc hAx statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  have hpost_done := @headerSent_post_call_done_56848_hs_ax img A F ext hb hAx s0
  have hpost_still := @headerSent_post_call_still_56848_hs_ax img A F ext hAx s0
  rw [fnAddr_fwd_headerSentRecvCt1] at hcall ⊢
  states_recv_fetches_range img.base (Rust.withPanics ext) 780 356
  states_recv_fetches_range img.base (Rust.withPanics ext) 5056 52
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw hcall hpost_done hpost_still hdone ⊢
  refine SepWP.fold (chunkedHeaderSentAt_pts_length A (selfA + 8#64) st) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen_pts => ?_
  obtain ⟨outRes, hrecv, _⟩ := headerSent_recv_ct1_chunk_eq_ok st chunk hlen_pts hsort
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, _⟩ => ?_
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62, heq, hpay, messagePayloadAt_ct1 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 120
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, sp.b0.w3, w.b3.w2, w.b4.w1, w.b4.w0, sp.b0.w7,
             w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9,
             sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, sp.b2.w7,
             sp.b2.w8, w.b4.w2⟩
      b3 := ⟨sp.b3.w0, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, w.b1.w3, w.b2.w5,
             sp.b3.w8, sp.b3.w9⟩
      b4 := ⟨w.b2.w6, w.b1.w2, sp.b4.w2, w.b1.w0, sp.b4.w4, sp.b4.w5, w.b0.w4, sp.b4.w7,
             sp.b4.w8, w.b2.w3⟩
      b5 := ⟨sp.b5.w0, w.b4.w4, w.b1.w4, w.b0.w8, sp.b5.w4, w.b5.w0, sp.b5.w6, w.b2.w4,
             w.b4.w6, sp.b5.w9⟩
      w60 := w.b5.w6
      w61 := sp.w61
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have hfold_pre_memcpy :
      (words63At (selfA + 8#64) w ∗
       ((selfA + 8#64 + 504#64) ↦ₛ tailBytes) ∗
       relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes)) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        chunkedHeaderSentAt A (selfA + 8#64) st ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono_left (recompose63_376 (selfA + 8#64) w tailBytes)
  refine SepWP.fold
    (F := P_rest ∗
      memRegion outA v1RecvSize ∗
      (selfA ↦₆₄ 4#64) ∗
      memRegion (selfA + 888#64) 40 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_pre_memcpy ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · refine SepWP.done rfl hrun fun hinv_mc => ?_
    refine call_memcpy_relocate_cs_inImage_stk_ext (ret_pc := entry + 5084#64)
      (stk := statesRecvCalleeStackXExt) (k_stk := 19552)
      hmemcpy_raw (Relocatable.of_chunkedHeaderSentAt A st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
      hinv_mc rfl hrun hsp hfsp_align rfl htr
      (by simp only [Reg.x0, arm64_norm, hsp])
      (by simp only [Reg.x1, arm64_norm, hx1])
      rfl (by decide) (by decide) (by sep_frame) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
    have hx24_1 : sf1.readReg64 .x24 = msgA :=
      hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, arm64_norm, hx24])
    have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, arm64_norm])
    have hfold_self :
        (selfA ↦₆₄ 4#64) ∗ memRegion (selfA + 8#64) 880 ∗ memRegion (selfA + 888#64) 40 ⊢
          memRegion selfA chunkedStatesSize :=
      self_880_40_entails_memRegion_928 selfA 4#64
    refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
    generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
    wp_steps 10
    subst hsp0
    refine SepWP.done rfl hrun1 fun hinv_ct1 => ?_
    refine call_headerSentRecvCt1Chunk_hs_ax hb hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk outRes hsort hrecv
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := entry + 5108#64)
      (R := R)
      (Frame :=
        P_rest ∗
        memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hinv_ct1 rfl hrun1 hsp1 hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      htr1
      (by simp only [Reg.x0, arm64_norm, hsp1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm, hx25_1])
      (by simp only [Reg.x3, arm64_norm, hx24_1])
      (by
        dsimp only [chunkedHeaderSentSize]
        simp only [arm64_norm]
        ac_rfl)
      hpanic
      ?_
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct1 msgA chunk]
    have hx19_2 : sf2.readReg64 .x19 = outA :=
      hcs2.1.trans (by simp only [Reg.x19, arm64_norm, hx19_1])
    have hx21_2 : sf2.readReg64 .x21 = (s0.sp - 4240#64) + 976#64 :=
      hcs2.2.2.1.trans (by simp only [Reg.x21, arm64_norm, hsp1])
    cases hout : outRes with
    | done outSt =>
      rw [hout] at hrecv
      have hmodel := states_recv_headerSent_eq_ct1_done K st msg chunk outSt heq hpay hrecv
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (hpost_done sf2 outA outSt sp1
            (P_rest ∗
             memRegion (s0.sp - 40176#64) 16384 ∗
             memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             tokenInitAt img.base ∗ reduceTableAt img.base ∗
             A.pool)
            hinv2 hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone sf Pf hpc_f hrun_f
              ⟨by
                rw [hmodel, stackAt_statesRecvStackXExt_eq_X s0.sp]
                exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq, stackAt_statesRecvCalleeExt_eq_X s0.sp]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]
      ac_rfl
    | stillReceiving outSt =>
      rw [hout] at hrecv
      have hmodel := states_recv_headerSent_eq_ct1_still K st msg chunk outSt heq hpay hrecv
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (hpost_still sf2 outA outSt sp1
            (P_rest ∗
             memRegion (s0.sp - 40176#64) 16384 ∗
             memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
             tokenInitAt img.base ∗ reduceTableAt img.base ∗
             A.pool)
            hinv2 hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone sf Pf hpc_f hrun_f
              ⟨by
                rw [hmodel, stackAt_statesRecvStackXExt_eq_X s0.sp]
                exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq, stackAt_statesRecvCalleeExt_eq_X s0.sp]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]
      ac_rfl

/-! ## 3. Complete `.headerSent` Arm & Top-Level Variant Theorems -/

private theorem states_recv_arm_headerSent_inImage_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hinv : statesRecvPreInv (.headerSent st))
    (himg_s : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoAt img.base ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.headerSent st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.headerSent st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hpre_comm :
      memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoAt img.base ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 =
      (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384) ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; ac_rfl
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.headerSent st) msg _ R ?_
    rw [states_recv_headerSent_gt K st msg hgt, hpre_comm]
    refine SepWP.mono
      (headerSent_arm_gt hdealloc s0 s outA selfA msgA st msg
        (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
         hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.headerSent st) msg _ R ?_
      rw [states_recv_headerSent_lt K st msg hlt, hpre_comm]
      refine SepWP.mono
        (headerSent_arm_lt_hs_ax hAx s0 s outA selfA msgA st msg
          (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
          himg_s hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
           hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct1 chunk =>
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt img.base ∗
                (((img.base +
                  bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
                  ((img.base +
                    bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt img.base ∗ reduceTableAt img.base) ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 =
            (statesRecvJumpTableAt img.base ∗
              ((img.base +
                bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
              memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              ((img.base +
                bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              tokenInitAt img.base ∗ reduceTableAt img.base ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 by ac_rfl]
        refine headerSent_arm_eq_ct1_hs_ax (K := K) hb hAx hcall s0 s outA selfA msgA st msg chunk
          (statesRecvJumpTableAt img.base ∗
            ((img.base +
              bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) R
          hinv himg_s heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
          (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
          (fun sf Pf hpan hmem_f => ?_)
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpecExt]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpecExt, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨Or.inr hpan'.1.1, hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
        have hct1 : ∀ c, msg.payload ≠ .ct1 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.headerSent st) msg _ R ?_
        rw [states_recv_headerSent_eq_other K st msg heq hct1, hpre_comm]
        refine SepWP.mono
          (headerSent_arm_eq_other_hs_ax hAx s0 s outA selfA msgA st msg
            (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
            himg_s heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf
              (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
             hsp_sf, hcs_sf, htr_sf⟩)

/-- Per-variant `.inImage img` specification proof for `States.headerSent st`
    (`tag = 4#64`, arm entry `+780`, `40176` B stack, `AllocContractsX` + `DeallocOkExt`). -/
theorem states_recv_headerSent_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.headerSent st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackXExt ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_ext (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_sendek himg0 hpro ?_
  intro s1 hpc1 hrun1 himg1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, _, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 4#64
    (chunkedHeaderSentAt A (selfA + 8#64) st ∗ memRegion (selfA + 888#64) 40 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean_inImage_sendek himg1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 himg2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; ac_rfl))
    (states_recv_arm_headerSent_inImage_ax hb hAx hdealloc hcall s0 s2 outA selfA msgA st msg R
      hinv himg2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1))

theorem states_recv_headerSent_ok_x_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.headerSent st) msg).inImage img) :=
  states_recv_headerSent_ok_x_ext hAx hdealloc hcall st msg

theorem states_recv_headerSent_ok_x_of_contractsExt
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsExt img A F K ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.headerSent st) msg).inImage img) :=
  states_recv_headerSent_ok_x_ext hAx hdealloc hC.toAx.headerSentRecvCt1Chunk_ok st msg

end CryptoVerification.SpqrV1.States.Recv
