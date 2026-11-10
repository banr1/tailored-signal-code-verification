/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Chunked Braid Send-Chunk Leaf Transitions 2 (`SendChunk2`)

**Checked by Lean.** Verifies `<Ct1Received>::send_ek_chunk` (`0x5e250`, `41` insns) and
`<Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`, `41` insns).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. 13-Word Unfolding Helpers for `unchunkedEkSentCt1ReceivedAt` (`104` bytes) -/

theorem wordsAt_13 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl,
    show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]

theorem cells_13_unfold (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
      ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] := by
  rw [ProofLib.memRegion_cells a 13 (by decide), cells_succ]
  simp only [wordsAt_13, cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl,
    show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]
  exact Entails.refl _

/-! ## 2. Proof 5: `<Ct1Received>::send_ek_chunk` (`0x5e250`, 41 insns) -/

theorem stackAt_944_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 944) =
      stackAt (sp - 944#64) polyNextChunkStack ∗
      memRegion (sp - 944#64) 8 ∗
      memRegion (sp - 936#64) 400 ∗
      memRegion (sp - 536#64) 400 ∗
      memRegion (sp - 136#64) 104 ∗
      memRegion (sp - 32#64) 32 := by
  change memRegion (sp - 19376#64) 19376 =
    memRegion (sp - 944#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 944#64 - 18432#64 = sp - 19376#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19376#64) (n := 18432) (k := 944)
        (b' := sp - 944#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 944#64) (n := 8) (k := 936)
        (b' := sp - 936#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 936#64) (n := 400) (k := 536)
        (b' := sp - 536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 536#64) (n := 400) (k := 136)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 104) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]

theorem stackAt_944_rejoin (sp w0 w1 w2 w3 : BitVec 64) :
    stackAt (sp - 944#64) polyNextChunkStack ∗
      memRegion (sp - 944#64) 8 ∗
      memRegion (sp - 936#64) 400 ∗
      memRegion (sp - 536#64) 504 ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
    stackAt sp (polyNextChunkStack + 944) := by
  have h4 :
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      memRegion (sp - 32#64) 32 := by
    have heq :
        (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
         ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) =
        wordsAt (sp - 32#64) [w0, w1, w2, w3] := by
      simp only [wordsAt_4, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3] (sp - 32#64) 32 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h4)))) ?_
  rw [stackAt_944_split sp,
      ProofLib.memRegion_split' (b := sp - 536#64) (n := 400) (k := 104)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedCt1ReceivedAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ek := outSt.sending_ek }) :
    polyEncoderAt A (sp - 536#64) outSt.sending_ek ∗
      unchunkedEkSentCt1ReceivedAt A (sp - 136#64) st.uc ⊢
    chunkedCt1ReceivedAt A (sp - 536#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hoff : (sp - 536#64) + 400#64 = sp - 136#64 := by bv_omega
  unfold chunkedCt1ReceivedAt
  rw [huc, hoff]
  exact Entails.refl _

theorem ct1_received_send_ek_chunk_ok_ext {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hnextChunk : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr polyNextChunkName)
      ((polyNextChunkSpec A img.base).inImage img)) :
    subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1ReceivedSendEkChunkName)
      ((ct1ReceivedSendEkChunkSpec A F img.base).inImage img) := by
  simp only [Spec.inImage, ct1ReceivedSendEkChunkSpec]
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1ReceivedSendEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk" "memcpy")))
      sessionMemcpyRegionSpec := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk" "memcpy"))) (b := img.base) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x58e58 libsignalSessionCode_fnOff_memcpy (by decide)).symm
    hmemcpy
  have hnext_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1ReceivedSendEkChunkName + 49460#64)
      ((polyNextChunkSpec A img.base).inImage img) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 49460) (b := img.base) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x58e58 libsignalSessionCode_fnOff_0x64f8c (by decide)).symm
    hnextChunk
  code_fetches libsignalSessionCode spqrStatesLeavesBin img.base
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x58e58 364120 164
  dsimp only [leavesProgAtExt, ct1ReceivedSendEkChunkName,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hnext_raw ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt, chunk⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  obtain ⟨hnc_ok, hout_eq⟩ := ct1Received_send_ek_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 944#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 944#64 (by assumption) (by decide)
  apply of_sepWP_inImage (mid := entry + 49460#64) (by assumption) (by assumption)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 504) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 504#64) rfl rfl (by decide),
        stackAt_944_split s0.sp]
    unfold chunkedCt1ReceivedAt
  refine SepWP.fold (cells_13_unfold (s0.sp - 136#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_4_unfold (s0.sp - 32#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedEkSentCt1ReceivedAt_extract A
    (s0.readReg64 (Reg.gpr 0#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists
  rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 456#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 464#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 472#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 480#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 488#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 496#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList, authWordsList,
      vecWordsList, List.append]
    simp only [wordsAt_13, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 136#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.sp - 136#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 120#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.sp - 104#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.sp - 88#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.sp - 80#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.sp - 72#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.sp - 64#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.sp - 56#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.sp - 48#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.sp - 40#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList, authWordsList,
      vecWordsList, List.append]
    simp only [wordsAt_13, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_13, arm64_norm]
  wp_steps
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_polyEncoderAt A st.sending_ek)
    (s0.sp - 936#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := entry + 104#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_copy_recompose (k := 104) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 136#64)
    (ekSentCt1ReceivedWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps
  refine call_polyNextChunk hnext_raw (by assumption)
    (s0.readReg64 (Reg.gpr 8#5) + 504#64) (s0.sp - 936#64)
    st.sending_ek outSt.sending_ek chunk
    (ret_pc := entry + 116#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1])
    (by simp only [Reg.x8, arm64_norm, hx19_1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    hnc_ok
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_polyEncoderAt A outSt.sending_ek)
    (s0.sp - 536#64) (s0.sp - 936#64)
    (ret_pc := entry + 132#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr2])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2])
    (by simp only [Reg.x0, arm64_norm, hsp2])
    (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hregs3 htr3 => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  refine SepWP.fold (chunkedCt1ReceivedAt_recompose_sp A s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_chunkedCt1ReceivedAt A outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 536#64)
    (ret_pc := entry + 148#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun3)
    (by simp only [State.sp, arm64_norm, hsp3])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr3])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3])
    (by simp only [Reg.x0, arm64_norm, hx19_3])
    (by simp only [Reg.x1, arm64_norm, hsp3])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  wp_steps
  refine SepWP.fold (stackAt_944_rejoin s0.sp _ _ _ _) (by sep_focus) ?_
  wp_done

/-! ## 3. Proof 6: `<Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`, 41 insns) -/

theorem stackAt_1376_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 1376) =
      stackAt (sp - 1376#64) polyNextChunkStack ∗
      memRegion (sp - 1376#64) 8 ∗
      memRegion (sp - 1368#64) 392 ∗
      memRegion (sp - 976#64) 400 ∗
      memRegion (sp - 576#64) 128 ∗
      memRegion (sp - 448#64) 400 ∗
      memRegion (sp - 48#64) 48 := by
  change memRegion (sp - 19808#64) 19808 =
    memRegion (sp - 1376#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 1376#64 - 18432#64 = sp - 19808#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19808#64) (n := 18432) (k := 1376)
        (b' := sp - 1376#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1376#64) (n := 8) (k := 1368)
        (b' := sp - 1368#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1368#64) (n := 392) (k := 976)
        (b' := sp - 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 400) (k := 576)
        (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 128) (k := 448)
        (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 448#64) (n := 400) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide)]

theorem stackAt_1376_rejoin (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    stackAt (sp - 1376#64) polyNextChunkStack ∗
      memRegion (sp - 1376#64) 400 ∗
      memRegion (sp - 976#64) 928 ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
    stackAt sp (polyNextChunkStack + 1376) := by
  have h6 :
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 48#64) 48 := by
    have heq :
        (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
         ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) =
        wordsAt (sp - 48#64) [w0, w1, w2, w3, w4, w5] := by
      simp only [wordsAt_6, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp - 48#64) 48 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h6))) ?_
  rw [stackAt_1376_split sp,
      ProofLib.memRegion_split' (b := sp - 1376#64) (n := 8) (k := 392)
        (b' := sp - 1368#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 400) (k := 528)
        (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 128) (k := 400)
        (b' := sp - 448#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedCt1SampledAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ct1 := outSt.sending_ct1, receiving_ek := st.receiving_ek }) :
    polyEncoderAt A (sp - 976#64) outSt.sending_ct1 ∗
      unchunkedCt1SentAt A (sp - 576#64) st.uc ∗
      polyDecoderAt A (sp - 448#64) st.receiving_ek ⊢
    chunkedCt1SampledAt A (sp - 976#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hdec : st.receiving_ek = outSt.receiving_ek := by rw [hout]
  have hoff1 : (sp - 976#64) + 400#64 = sp - 576#64 := by bv_omega
  have hoff2 : (sp - 976#64) + 528#64 = sp - 448#64 := by bv_omega
  unfold chunkedCt1SampledAt
  rw [huc, hdec, hoff1, hoff2]
  exact Entails.refl _

theorem ct1_sampled_send_ct1_chunk_ok_ext {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hnextChunk : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr polyNextChunkName)
      ((polyNextChunkSpec A img.base).inImage img)) :
    subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1SampledSendCt1ChunkName)
      ((ct1SampledSendCt1ChunkSpec A F img.base).inImage img) := by
  simp only [Spec.inImage, ct1SampledSendCt1ChunkSpec]
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1SampledSendCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk" "memcpy")))
      sessionMemcpyRegionSpec := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk" "memcpy"))) (b := img.base) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x583c4 libsignalSessionCode_fnOff_memcpy (by decide)).symm
    hmemcpy
  have hnext_raw : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr ct1SampledSendCt1ChunkName + 52168#64)
      ((polyNextChunkSpec A img.base).inImage img) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 52168) (b := img.base) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x583c4 libsignalSessionCode_fnOff_0x64f8c (by decide)).symm
    hnextChunk
  code_fetches libsignalSessionCode spqrStatesLeavesBin img.base
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x583c4 361412 164
  dsimp only [leavesProgAtExt, ct1SampledSendCt1ChunkName,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hnext_raw ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt, chunk⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  obtain ⟨hnc_ok, hout_eq⟩ := ct1Sampled_send_ct1_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 1376#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1376#64 (by assumption) (by decide)
  apply of_sepWP_inImage (mid := entry + 52168#64) (by assumption) (by assumption)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 928) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 928#64) rfl rfl (by decide),
        stackAt_1376_split s0.sp]
    unfold chunkedCt1SampledAt
  refine SepWP.fold (cells_1_unfold (s0.sp - 1376#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_6_unfold (s0.sp - 48#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedCt1SentAt_extract A
    (s0.readReg64 (Reg.gpr 0#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists
  rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (fiveVecWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ g.rest.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 456#64) ↦₆₄ g.rest.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 464#64) ↦₆₄ g.rest.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 472#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 480#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 488#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 496#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 504#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 512#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 520#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList,
      authWordsList, vecWordsList, List.append]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 576#64) (fiveVecWordsList g st.uc.epoch) =
      (((s0.sp - 576#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 568#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 560#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 552#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.sp - 544#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.sp - 536#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.sp - 528#64) ↦₆₄ g.rest.rest.v1.w0) ∗
       ((s0.sp - 520#64) ↦₆₄ g.rest.rest.v1.w1) ∗
       ((s0.sp - 512#64) ↦₆₄ g.rest.rest.v1.w2) ∗
       ((s0.sp - 504#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
       ((s0.sp - 496#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
       ((s0.sp - 488#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
       ((s0.sp - 480#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
       ((s0.sp - 472#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
       ((s0.sp - 464#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
       ((s0.sp - 456#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList,
      authWordsList, vecWordsList, List.append]
    simp only [wordsAt_16, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_16, arm64_norm]
  wp_steps
  refine SepWP.fold (cell_0_rejoin_400 s0.sp 1376#64 1368#64 0#64 (by bv_omega)) (by sep_focus) ?_
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_polyEncoderAt A st.sending_ct1)
    (s0.sp - 1376#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := entry + 80#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_polyDecoderAt A st.receiving_ek)
    (s0.sp - 448#64) (s0.readReg64 (Reg.gpr 0#5) + 528#64)
    (ret_pc := entry + 100#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by simp only [Reg.x1, arm64_norm, hx19_1])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_dec_copy_recompose (k := 128) (by decide) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 576#64) (by bv_omega)
    (fiveVecWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps
  refine call_polyNextChunk hnext_raw (by assumption)
    (s0.readReg64 (Reg.gpr 8#5) + 928#64) (s0.sp - 1376#64)
    st.sending_ct1 outSt.sending_ct1 chunk
    (ret_pc := entry + 112#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr2])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2])
    (by simp only [Reg.x8, arm64_norm, hx20_2])
    (by simp only [Reg.x0, arm64_norm, hsp2])
    hnc_ok
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hregs3 htr3 => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_polyEncoderAt A outSt.sending_ct1)
    (s0.sp - 976#64) (s0.sp - 1376#64)
    (ret_pc := entry + 128#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun3)
    (by simp only [State.sp, arm64_norm, hsp3])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr3])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3])
    (by simp only [Reg.x0, arm64_norm, hsp3])
    (by simp only [Reg.x1, arm64_norm, hsp3])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  refine SepWP.fold (chunkedCt1SampledAt_recompose_sp A s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0) (Relocatable.of_chunkedCt1SampledAt A outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 976#64)
    (ret_pc := entry + 144#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun4)
    (by simp only [State.sp, arm64_norm, hsp4])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr4])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4])
    (by simp only [Reg.x0, arm64_norm, hx20_4])
    (by simp only [Reg.x1, arm64_norm, hsp4])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf5 hpc5 hrun5 hsp5 hregs5 htr5 => ?_)
  rcases hregs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hvregs_5⟩
  wp_steps
  refine SepWP.fold (stackAt_1376_rejoin s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  wp_done

end CryptoVerification.SpqrV1.States.Leaves
