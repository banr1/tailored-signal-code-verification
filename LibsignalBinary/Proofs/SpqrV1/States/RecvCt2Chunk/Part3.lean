/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Epilogue & `Err(MacVerifyFailed)` Branch

Verifies the shared `Some`-branch epilogue (`0x5f0d0 .. 0x5f108`), `Err(MacVerifyFailed)` write-out
(`0x5f0a0 .. 0x5f0d0`), and 9-buffer error deallocation chain (`0x5eff4 .. 0x5f0a0`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

set_option maxHeartbeats 800000 in
theorem recv_ct2_chunk_epilogue_wpp {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (cap_ct2 ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 1188#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx24 : st.readReg64 .x24 = cap_ct2) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (ct2DeallocAt A cap_ct2 ptr_ct2 ∗ polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        cells (s0.sp - 2496#64) 9 ∗ memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗ someBranchFrameAt (s0.sp - 2496#64) ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2ChunkRoAt img ∗
        ekSentCt1ReceivedRecvChunkResultAt A x.outA (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2ChunkPostQ img K F A x s0 R)
      (recvCt2ChunkPostQp K F A img.base x s0 R) := by
  have h_dealloc := dealloc_ok_at_recvCt2 hA
  have h_drop := dropSortedSetPt16_ok_at_recvCt2 (img := img) hdealloc
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  dsimp only [ct2DeallocAt]
  refine SepWPp.pure_left_focus (cap_ct2 ≠ 0#64 ∧ cap_ct2.toNat < 2 ^ 63 ∧ ptr_ct2 ≠ 0#64)
    (by sep_focus) fun ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ => ?_
  have hcap_ct2_pos : 0 < cap_ct2.toNat := by
    apply Nat.pos_of_ne_zero; intro h0; exact hcap_ct2_ne (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  unfold tripleRatchetProgAtExt at hpc h_dealloc h_drop ⊢
  recv_ct2_chunk_fetches_range img.base (Rust.withPanics ext) 1188 56
  clear hA hdealloc
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      recvCt2ChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hinv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_dealloc (ptr_ct2, cap_ct2.toNat, 1) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_sf :
      stackAt st.sp extHookStack ⊢
        memRegion (s0.sp - 18880#64) 12256 ∗ stackAt sf.sp dropGluePoly16Stack := by
    rw [hsp_sf, hsp, ← stackAt_extHook_eq_dropGluePoly16 s0.sp]; exact Entails.refl _
  refine SepWPp.fold hstack_sf (by sep_focus) ?_
  refine SepWPp.fold (polyDecoderAt_entails_vecs_tail A (s0.sp - 2424#64) receivingCt2) (by sep_focus) ?_
  sep_elim_exists; rename_i vecs
  refine SepWPp.pure_left_focus (vecs.length = NUM_POLYS) (by sep_focus) fun hvecs_len => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + (0x46920#64 - 0x59834#64)) hF_sf ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_inImage_recvCt2 h_drop (⟨s0.sp - 2424#64, vecs⟩ : DropGlueSortedSetPt16Ghost) hinv2
  refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
  have hstack_back :
      memRegion (s0.sp - 18880#64) 12256 ∗ stackAt sf.sp dropGluePoly16Stack ⊢
        stackAt (s0.sp - 2496#64) extHookStack := by
    rw [hsp_sf, hsp, ← stackAt_extHook_eq_dropGluePoly16 s0.sp]; exact Entails.refl _
  refine SepWPp.fold hstack_back (by sep_focus) ?_
  refine SepWPp.fold (polyDecoder_post_join (s0.sp - 2424#64)) (by sep_focus) ?_
  change SepWPp prog (s0.readReg64 .x30) sf_1 (memRegion (s0.sp - 2424#64) 400 ∗ _) _ _
  refine SepWPp.fold (rejoin_activeFrameRegionsAt_epilogue s0.sp) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_stack_polyDecodedMessage_from_extHook s0.sp) (by sep_focus) ?_
  apply SepWPp.of_sepWP_ret
  unfold savedRegsAt
  wp_steps
  have hfold_saved :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      savedRegsAt s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvCt2Chunk s0) (by sep_focus) ?_
  unfold recvCt2ChunkPostQ; dsimp only [recvCt2ChunkSpec]; wp_done

set_option maxHeartbeats 800000 in
theorem recv_ct2_chunk_err_write_out_wpp {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (cap_ct2 ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 1140#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx24 : st.readReg64 .x24 = cap_ct2) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (ct2DeallocAt A cap_ct2 ptr_ct2 ∗ memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1328#64) 48 ∗ memRegion (s0.sp - 1280#64) 24 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 152#64) 32 ∗ unusedFrameAt (s0.sp - 2496#64) ∗
        memRegion (s0.sp - 1856#64) 504 ∗ polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        cells (s0.sp - 2496#64) 9 ∗ memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2ChunkRoAt img ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2ChunkPostQ img K F A x s0 R)
      (recvCt2ChunkPostQp K F A img.base x s0 R) := by
  have hep := @recv_ct2_chunk_epilogue_wpp img K F A ext hA hdealloc x receivingCt2 cap_ct2 ptr_ct2 s0
  dsimp only [ct2DeallocAt]
  refine SepWPp.pure_left_focus (cap_ct2 ≠ 0#64 ∧ cap_ct2.toNat < 2 ^ 63 ∧ ptr_ct2 ≠ 0#64)
    (by sep_focus) fun ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ => ?_
  have hcap_ct2_beq : (cap_ct2 == 0#64) = false := beq_false_of_ne hcap_ct2_ne
  have hfold_ct2 :
      memRegion ptr_ct2 cap_ct2.toNat ∗ A.live ptr_ct2 cap_ct2.toNat 1 ⊢
        ct2DeallocAt A cap_ct2 ptr_ct2 := by
    dsimp only [ct2DeallocAt]
    exact Entails.pure_right ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ (Entails.refl _)
  refine SepWPp.fold hfold_ct2 (by sep_focus) ?_
  refine SepWPp.fold (memRegion_outA_err_split x.outA) (by sep_focus) ?_
  sep_elim_exists; rename_i o0 ob8 o9 o17 o25
  refine SepWPp.rw_pre (by rw [memRegion_144_x20_split s0.sp]) ?_
  refine SepWPp.fold (memRegion_24_split_23_1 (s0.sp - 2000#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i u0 u1 u2
  refine SepWPp.fold (memRegion_24_split_23_1 (s0.sp - 1968#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i v0 v1 v2
  have ha0 : (s0.sp - 2000#64) + 8#64 = s0.sp - 1992#64 := by bv_omega
  have ha1 : (s0.sp - 2000#64) + 16#64 = s0.sp - 1984#64 := by bv_omega
  have ha2 : (s0.sp - 2000#64) + 23#64 = s0.sp - 1977#64 := by bv_omega
  have hb0 : (s0.sp - 1968#64) + 8#64 = s0.sp - 1960#64 := by bv_omega
  have hb1 : (s0.sp - 1968#64) + 16#64 = s0.sp - 1952#64 := by bv_omega
  have hb2 : (s0.sp - 1968#64) + 23#64 = s0.sp - 1945#64 := by bv_omega
  refine SepWPp.rw_pre (by simp only [ha0, ha1, ha2, hb0, hb1, hb2]; rfl) ?_
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx24
  unfold tripleRatchetProgAtExt at hpc hep ⊢
  recv_ct2_chunk_fetches_range img.base (Rust.withPanics ext) 1140 48
  clear hA hdealloc
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      recvCt2ChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.of_sepWP_inImage (mid := entry + 1188#64) hinv ?_
  wp_step; wp_step
  have hshift_b :=
    left_and_low7_to_mid_at_7 (s0.sp - 1960#64) (s0.sp - 1953#64) (s0.sp - 1952#64)
      v1 v2 (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_b) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step
  have hshift_a1 :=
    left_and_low7_to_mid_at_7 (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64)
      v1 u2 (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_a1) (by sep_focus) ?_
  wp_step
  have hshift_a2 :=
    mid_at_7_to_left (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64)
      v1 (unshiftWord8 v1 v2) (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_a2) (by sep_focus) ?_
  wp_step; wp_step; wp_step
  have hshift_out :=
    left_and_low7_to_mid_at_7 (x.outA + 17#64) (x.outA + 24#64) (x.outA + 25#64)
      (setByte7 v1 (unshiftWord8 v1 v2)) o25 (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_out) (by sep_focus) ?_
  wp_step; wp_step
  have hrejoin_out := rejoin_outA_err A (F := F) x.outA
    v0 (setByte7 v1 (unshiftWord8 v1 v2)) (unshiftWord8 v1 v2)
  rw [← hres] at hrejoin_out
  refine SepWP.fold hrejoin_out (by sep_focus) ?_
  have hrejoin_a :
      ((s0.sp - 2000#64) ↦₆₄ v0) ∗ ((s0.sp - 1992#64) ↦₆₄ setByte7 v1 (unshiftWord8 v1 v2)) ∗
      mid7At (s0.sp - 1984#64) (unshiftWord8 v1 v2) ∗ ((s0.sp - 1977#64) ↦₈ b7 u2) ⊢
      memRegion (s0.sp - 2000#64) 24 := by
    have h := rejoin_memRegion_24_left (s0.sp - 2000#64) v0
      (setByte7 v1 (unshiftWord8 v1 v2)) (unshiftWord8 v1 v2) (b7 u2)
    rwa [ha0, ha1, ha2] at h
  have hrejoin_b :
      ((s0.sp - 1968#64) ↦₆₄ v0) ∗ low7At (s0.sp - 1960#64) v1 ∗
      ((s0.sp - 1953#64) ↦₆₄ unshiftWord8 v1 v2) ∗ ((s0.sp - 1945#64) ↦₈ b7 v2) ⊢
      memRegion (s0.sp - 1968#64) 24 := by
    have h := rejoin_memRegion_24_mid (s0.sp - 1968#64) v0 v1 (unshiftWord8 v1 v2) (b7 v2)
    have h15 : (s0.sp - 1968#64) + 15#64 = s0.sp - 1953#64 := by bv_omega
    rwa [hb0, h15, hb2] at h
  refine SepWP.fold hrejoin_a (by sep_focus) ?_
  refine SepWP.fold hrejoin_b (by sep_focus) ?_
  have hrejoin_144 :
      memRegion (s0.sp - 2000#64) 24 ∗ memRegion (s0.sp - 1976#64) 8 ∗
      memRegion (s0.sp - 1968#64) 24 ∗ memRegion (s0.sp - 1944#64) 88 ⊢
      memRegion (s0.sp - 2000#64) 144 :=
    Entails.of_eq (memRegion_144_x20_split s0.sp).symm
  refine SepWP.fold hrejoin_144 (by sep_focus) ?_
  refine SepWP.fold (rejoin_someBranchFrameAt s0.sp) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  refine SepWPp.rw_pre (by ac_rfl)
    (hep _ R (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *]) hsp_s0
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv1
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

/-! ## `Err(MacVerifyFailed)` Deallocation Chain (`0x5eff4 .. 0x5f0a0`) -/
set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_err_wpp {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (ct2Full ss_raw ss : Bytes)
    (auth' : Authenticator) (g_auth' : AuthenticatorGhost)
    (cap_ct2 ptr_ct2 cap_dk ptr_dk cap_ct1' ptr_ct1'
      cap_info ptr_info ptr_ss_raw ptr_ss ptr_mac ptr_ct2_128 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hgt128 : 128 < ct2Full.length) (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hss_raw_len : ss_raw.length = 32) (hss_len : ss.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hmk_cap_ne : g_auth'.macKey.cap ≠ 0#64)
    (hmk_le : 32 ≤ g_auth'.macKey.cap.toNat) (hmk_max : g_auth'.macKey.cap.toNat < 2 ^ 63)
    (hmk_ptr_ne : g_auth'.macKey.ptr ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 968#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_ss_raw) (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx27 : st.readReg64 .x27 = ptr_ss) (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      ((ptr_ss ↦ₛ ss) ∗ A.live ptr_ss 32 1 ∗ ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗ ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗ memRegion (s0.sp - 128#64) 8 ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗ A.live ptr_ss_raw 32 1 ∗
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗ ct2DeallocAt A cap_ct1' ptr_ct1' ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        vecU8At A (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗ ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗ (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗ A.live ptr_ct2_128 128 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗ ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗ ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗ ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗ ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗ memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗ memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗ memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2ChunkRoAt img ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2ChunkPostQ img K F A x s0 R)
      (recvCt2ChunkPostQp K F A img.base x s0 R) := by
  have h_dealloc := dealloc_ok_at_recvCt2 hA
  have h_write := @recv_ct2_chunk_err_write_out_wpp img K F A ext hA hdealloc x receivingCt2 cap_ct2 ptr_ct2 s0
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hss_mr : (ptr_ss ↦ₛ ss) ⊢ memRegion ptr_ss 32 := by
    rw [← hss_len]; exact pointsToBytes_entails_memRegion ptr_ss ss
  have hss_raw_mr : (ptr_ss_raw ↦ₛ ss_raw) ⊢ memRegion ptr_ss_raw 32 := by
    rw [← hss_raw_len]; exact pointsToBytes_entails_memRegion ptr_ss_raw ss_raw
  have hct2_128_mr : (ptr_ct2_128 ↦ₛ ct2Full.take 128) ⊢ memRegion ptr_ct2_128 128 := by
    have h := pointsToBytes_entails_memRegion ptr_ct2_128 (ct2Full.take 128)
    rwa [htake128_len] at h
  have hmk_dealloc :
      (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ⊢
      ct2DeallocAt A g_auth'.macKey.cap g_auth'.macKey.ptr := by
    have h := bytes_rem_entails_ct2DeallocAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey
      (by omega) hmk_max hmk_ptr_ne hmk_cap_ne
    rwa [hmk_len] at h
  have hmac_mr_live :
      vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ⊢
        memRegion ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat ∗
          A.live ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 := by
    have hlen : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
    rw [← hlen]; exact vecBufAt_entails_memRegion_live A ptr_mac (ct2Full.drop 128) (by omega) (by omega)
  have hmac_toNat : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = ct2Full.length - 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmac_pos : 0 < (BitVec.ofNat 64 (ct2Full.length - 128)).toNat := by omega
  have hmac_max : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat < 2 ^ 63 := by omega
  have hmac_beq : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = false := by
    apply beq_false_of_ne; intro h0
    have h1 := congrArg BitVec.toNat h0; change (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = 0 at h1; omega
  refine SepWPp.fold hss_mr (by sep_focus) ?_
  refine SepWPp.fold hss_raw_mr (by sep_focus) ?_
  refine SepWPp.fold hct2_128_mr (by sep_focus) ?_
  refine SepWPp.fold hmk_dealloc (by sep_focus) ?_
  refine SepWPp.fold hmac_mr_live (by sep_focus) ?_
  refine SepWPp.fold
    (vecU8At_expose_sp_1328 A s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey (by omega))
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus
    (auth'.rootKey.length ≤ g_auth'.rootKey.cap.toNat ∧ g_auth'.rootKey.cap.toNat < 2 ^ 63 ∧
      g_auth'.rootKey.ptr ≠ 0#64 ∧ g_auth'.rootKey.cap ≠ 0#64)
    (by sep_focus) fun _ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A cap_info ptr_info) (by sep_focus) ?_
  refine SepWPp.pure_left_focus (Ct2DeallocProp cap_info ptr_info) (by sep_focus)
    fun ⟨hinfo_beq, hinfo_pos, hinfo_max, hinfo_ptr⟩ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A cap_ct1' ptr_ct1') (by sep_focus) ?_
  refine SepWPp.pure_left_focus (Ct2DeallocProp cap_ct1' ptr_ct1') (by sep_focus)
    fun ⟨hct1_beq, hct1_pos, hct1_max, hct1_ptr⟩ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A cap_dk ptr_dk) (by sep_focus) ?_
  refine SepWPp.pure_left_focus (Ct2DeallocProp cap_dk ptr_dk) (by sep_focus)
    fun ⟨hdk_beq, hdk_pos, hdk_max, hdk_ptr⟩ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A g_auth'.rootKey.cap g_auth'.rootKey.ptr) (by sep_focus) ?_
  refine SepWPp.pure_left_focus (Ct2DeallocProp g_auth'.rootKey.cap g_auth'.rootKey.ptr) (by sep_focus)
    fun ⟨hrk_beq, hrk_pos, hrk_max, hrk_ptr⟩ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A g_auth'.macKey.cap g_auth'.macKey.ptr) (by sep_focus) ?_
  refine SepWPp.pure_left_focus (Ct2DeallocProp g_auth'.macKey.cap g_auth'.macKey.ptr) (by sep_focus)
    fun ⟨hmk_beq, hmk_pos, hmk_max, hmk_ptr⟩ => ?_
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx23 hx24 hx25 hx27 hx29
  unfold tripleRatchetProgAtExt at hpc h_dealloc h_write ⊢
  recv_ct2_chunk_fetches_range img.base (Rust.withPanics ext) 968 172
  clear hA hdealloc
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      recvCt2ChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hinv ?_
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1
  wpp_call_inImage_recvCt2 h_dealloc (ptr_ss, 32, 1) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf ?_
  wp_steps
  have hst1 : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by rw [hsp_sf]
  refine SepWP.fold (Entails.of_eq hst1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv2
  wpp_call_inImage_recvCt2 h_dealloc (ptr_info, cap_info.toNat, 1) hinv2
  refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_1 ?_
  wp_steps
  have hst2 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by rw [hsp_sf_1]
  refine SepWP.fold (Entails.of_eq hst2) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv3
  wpp_call_inImage_recvCt2 h_dealloc (ptr_ss_raw, 32, 1) hinv3
  refine SepWPp.pure_left_focus (sf_2.trace = sf_1.trace) (by sep_focus) fun htr3 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_2 ?_
  wp_steps
  have hst3 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by rw [hsp_sf_2]
  refine SepWP.fold (Entails.of_eq hst3) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv4
  wpp_call_inImage_recvCt2 h_dealloc (ptr_ct1', cap_ct1'.toNat, 1) hinv4
  refine SepWPp.pure_left_focus (sf_3.trace = sf_2.trace) (by sep_focus) fun htr4 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_3 ?_
  wp_steps
  have hst4 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by rw [hsp_sf_3]
  refine SepWP.fold (Entails.of_eq hst4) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv5
  wpp_call_inImage_recvCt2 h_dealloc (ptr_dk, cap_dk.toNat, 1) hinv5
  refine SepWPp.pure_left_focus (sf_4.trace = sf_3.trace) (by sep_focus) fun htr5 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_4 ?_
  wp_steps
  have hst5 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by rw [hsp_sf_4]
  refine SepWP.fold (Entails.of_eq hst5) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv6
  wpp_call_inImage_recvCt2 h_dealloc (g_auth'.rootKey.ptr, g_auth'.rootKey.cap.toNat, 1) hinv6
  refine SepWPp.pure_left_focus (sf_5.trace = sf_4.trace) (by sep_focus) fun htr6 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_5 ?_
  wp_steps
  have hst6 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by rw [hsp_sf_5]
  refine SepWP.fold (Entails.of_eq hst6) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv7
  wpp_call_inImage_recvCt2 h_dealloc (g_auth'.macKey.ptr, g_auth'.macKey.cap.toNat, 1) hinv7
  refine SepWPp.pure_left_focus (sf_6.trace = sf_5.trace) (by sep_focus) fun htr7 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_6 ?_
  wp_steps
  have hst7 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by rw [hsp_sf_6]
  refine SepWP.fold (Entails.of_eq hst7) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv8
  wpp_call_inImage_recvCt2 h_dealloc (ptr_mac, (BitVec.ofNat 64 (ct2Full.length - 128)).toNat, 1) hinv8
  refine SepWPp.pure_left_focus (sf_7.trace = sf_6.trace) (by sep_focus) fun htr8 => ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_7 ?_
  wp_steps
  have hst8 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by rw [hsp_sf_7]
  refine SepWP.fold (Entails.of_eq hst8) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv9
  wpp_call_inImage_recvCt2 h_dealloc (ptr_ct2_128, 128, 1) hinv9
  refine SepWPp.pure_left_focus (sf_8.trace = sf_7.trace) (by sep_focus) fun htr9 => ?_
  have hst9 : stackAt sf_7.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
    rw [hsp_sf_7, hsp_sf_6, hsp_sf_5, hsp_sf_4, hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  refine SepWPp.fold (Entails.of_eq hst9) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_memRegion_32_sp_152 s0.sp cap_info ptr_info 41#64) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_memRegion_24_sp_1280 s0.sp cap_ct1' ptr_ct1' 960#64) (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_48_sp_1328 s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
      (BitVec.ofNat 64 auth'.rootKey.length) g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)
    (by sep_focus) ?_
  refine SepWPp.fold
    (cells9_sp_2496_fold s0.sp g_auth'.macKey.ptr ptr_dk (BitVec.ofNat 64 ct2Full.length)
      ptr_info cap_ct2 cap_dk ptr_mac ptr_ct1' x.epoch)
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by dsimp only [recvCt2ChunkRoAt]; ac_rfl)
    (h_write sf_8 R hres
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *]) hsp_s0
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hF_sf_8
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
