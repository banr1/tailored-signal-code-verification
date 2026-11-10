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
# `<EkSentCt1Received>::recv_ct2_chunk`: `ct1.reserve(128)`, Append `ct2`, and `libcrux_hmac`

Verifies `ct1.reserve(128)` (`0x5eec4 .. 0x5eed8` + `0x5f3c0`), appending `ct2[..128]` to `ct1`,
`sliceConcat3`, `libcrux_hmac::hmac`, and temporary `mac_data` deallocation (`0x5eed8 .. 0x5ef88`).
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
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length replicate_32_zero_length ctLabel_length
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

/-! ## `ct1.reserve(128)` (`0x5eec4 .. 0x5eed8` + `0x5f3c0 .. 0x5f3e4`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_reserve_ct1_wpp {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hres7 : DoReserve7OkX img A ext)
    (x : RecvCt2ChunkGhost F)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hct1_len : x.self.uc.ct1.length = 960)
    (hcap_ct1_ne : cap_ct1 ≠ 0#64)
    (hct1_le : 960 ≤ cap_ct1.toNat)
    (hct1_lt : cap_ct1.toNat < 2 ^ 63)
    (hptr_ct1_ne : ptr_ct1 ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 664#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64),
      cap_ct1' ≠ 0#64 →
      1088 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 684#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      ImgCallInv img st' →
      st'.readReg64 .x8 = 960#64 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = st.readReg64 .x21 →
      st'.readReg64 .x22 = st.readReg64 .x22 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = st.readReg64 .x28 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st'
        (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
          (ptr_ct1' ↦ₛ x.self.uc.ct1) ∗
          memRegion (ptr_ct1' + 960#64) (cap_ct1'.toNat - 960) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
          A.pool ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2ChunkPostQ img K F A x s0 R)
        (recvCt2ChunkPostQp K F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (((s0.sp - 1280#64) ↦₆₄ cap_ct1) ∗
        ((s0.sp - 1272#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
        (ptr_ct1 ↦ₛ x.self.uc.ct1) ∗
        memRegion (ptr_ct1 + 960#64) (cap_ct1.toNat - 960) ∗
        A.live ptr_ct1 cap_ct1.toNat 1 ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
        A.pool ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2ChunkPostQ img K F A x s0 R)
      (recvCt2ChunkPostQp K F A img.base x s0 R) := by
  have h_res := doReserve7_ok_at_recvCt2 hres7
  simp only [doReserveSpecX] at h_res
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  unfold tripleRatchetProgAtExt at hpc h_res hcont ⊢
  recv_ct2_chunk_fetches_range img.base (Rust.withPanics ext) 664 20
  recv_ct2_chunk_fetches_range img.base (Rust.withPanics ext) 1940 40
  clear hres7
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      recvCt2ChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  by_cases hls : ¬ (cap_ct1 - 960#64).ule 127#64 = true
  · have hls_f : (cap_ct1 - 960#64).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge1088 : 1088 ≤ cap_ct1.toNat := le_of_not_ule_sub_960 hct1_le hls
    refine SepWPp.of_sepWP_inImage (mid := entry + 684#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 hcap_ct1_ne hge1088 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - 960#64).ule 127#64 = true := Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_960 hct1_le hls_t
    have hbound' : reserveCap cap_ct1.toNat x.self.uc.ct1.length 128 + 1 ≤ 2 ^ 63 := by
      rwa [hct1_len]
    refine SepWPp.of_sepWP_inImage (mid := entry + (0x4dca8#64 - 0x59834#64)) hinv ?_
    wp_steps
    have h1264 : ((s0.sp - 1264#64) ↦₆₄ 960#64) ⊢
        ((s0.sp - 1264#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.ct1.length) := by
      rw [hct1_len]; exact Entails.refl _
    refine SepWP.fold h1264 (by sep_focus) ?_
    have hmr_ct1 :
        memRegion (ptr_ct1 + 960#64) (cap_ct1.toNat - 960) ⊢
          memRegion (ptr_ct1 + BitVec.ofNat 64 x.self.uc.ct1.length) (cap_ct1.toNat - x.self.uc.ct1.length) := by
      rw [hct1_len]; exact Entails.refl _
    refine SepWP.fold hmr_ct1 (by sep_focus) ?_
    refine SepWP.fold
      (vecU8At_of_sp_1280 A s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1
        (by omega) hct1_lt hptr_ct1_ne hcap_ct1_ne)
      (by sep_focus) ?_
    have hstack_res :
        memRegion (s0.sp - 19552#64) 672 ∗ stackAt (s0.sp - 2496#64) extHookStack ⊢
          memRegion (s0.sp - 19552#64) 560 ∗ stackAt (s0.sp - 2496#64) doReserveStackX :=
      Entails.of_eq (stackAt_extHook_eq_doReserveX s0.sp)
    refine SepWP.fold hstack_res (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_inImage_recvCt2 h_res
      (⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩ : DoReserveCall)
      hinv1
    refine SepWPp.rw_pre (emp_sepConj _).symm ?_
    sep_elim_exists
    rename_i ptr_ct1'
    refine SepWPp.rw_pre (emp_sepConj _) ?_
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    refine SepWPp.fold
      (vecU8At_expose_sp_1280 A s0.sp
        (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128))
        ptr_ct1' x.self.uc.ct1 (by omega))
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, hmax_ct1', hptr_ct1'_ne, hcap_ct1'_ne⟩
    have hge1088' :
        1088 ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)).toNat := by
      rw [hct1_len]
      exact reserveCap_ge_1088 hbound
    refine SepWPp.rw_pre (by rw [hct1_len]) ?_
    refine SepWPp.of_sepWP_inImage (mid := entry + 684#64) hF_sf ?_
    wp_steps
    have hstack_back :
        memRegion (s0.sp - 19552#64) 560 ∗ stackAt st.sp doReserveStackX ⊢
          memRegion (s0.sp - 19552#64) 672 ∗ stackAt (s0.sp - 2496#64) extHookStack := by
      rw [hsp, ← stackAt_extHook_eq_doReserveX s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_back (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat 960 128)) ptr_ct1'
        (reserveCap_ne_zero hbound)
        (by simpa [hct1_len] using hge1088')
        (by simpa [hct1_len] using hmax_ct1')
        hptr_ct1'_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

/-! ## Append `ct2` to `ct1`, `sliceConcat3`, `libcrux_hmac`, and dealloc (`0x5eed8 .. 0x5ef88`) -/
set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_append_hmac_wpp {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A))
    (x : RecvCt2ChunkGhost F)
    (ct2Full : Bytes)
    (auth' : Authenticator)
    (g_auth' : AuthenticatorGhost)
    (cap_ct1' ptr_ct1' ptr_ct2_128 s_2496 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hct1_len : x.self.uc.ct1.length = 960)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hmk_len : auth'.macKey.length = 32)
    (hcap_ct1'_ne : cap_ct1' ≠ 0#64)
    (hge1088 : 1088 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hptr_ct1'_ne : ptr_ct1' ≠ 0#64)
    (halign : img.base &&& 4095#64 = 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 684#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx8 : st.readReg64 .x8 = 960#64)
    (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx28 : st.readReg64 .x28 = rev64 x.epoch)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      g_auth'.macKey.cap ≠ 0#64 →
      32 ≤ g_auth'.macKey.cap.toNat →
      g_auth'.macKey.cap.toNat < 2 ^ 63 →
      g_auth'.macKey.ptr ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + 860#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      ImgCallInv img st' →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x21 = st.readReg64 .x21 →
      st'.readReg64 .x22 = st.readReg64 .x22 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = ptr_ct2_128 →
      st'.readReg64 .x26 = g_auth'.macKey.ptr →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st'
        (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
          ct2DeallocAt A cap_ct1' ptr_ct1' ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          vecU8At A (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
          ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗
          ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
          ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗
          (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
          memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
          A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
          ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗
          vecU8 A (s0.sp - 1248#64) (auth'.macCtUnchecked F x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)) ∗
          memRegion (s0.sp - 1224#64) 24 ∗
          memRegion (s0.sp - 1200#64) 912 ∗
          memRegion (s0.sp - 288#64) 128 ∗
          memRegion (s0.sp - 2000#64) 144 ∗
          ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
          A.pool ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2ChunkPostQ img K F A x s0 R)
        (recvCt2ChunkPostQp K F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
        (ptr_ct1' ↦ₛ x.self.uc.ct1) ∗
        memRegion (ptr_ct1' + 960#64) (cap_ct1'.toNat - 960) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        authenticatorPinAt A g_auth' (s0.sp - 1328#64) auth' ∗
        ((s0.sp - 2496#64) ↦₆₄ s_2496) ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2ChunkPostQ img K F A x s0 R)
      (recvCt2ChunkPostQp K F A img.base x s0 R) := by
  have h_concat3 := sliceConcat3_ok_at_recvCt2 hconcat3
  have h_hmac := libcrux_hmac_safe_ok_at_recvCt2 (img := img) hhmac
  have h_dealloc := dealloc_ok_at_recvCt2 hA
  have hadrp_ct := adrp_ctLabel halign
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx8 hx25 hx28 hx29
  unfold tripleRatchetProgAtExt at hpc h_concat3 h_hmac h_dealloc hcont ⊢
  recv_ct2_chunk_fetches_range img.base (Rust.withPanics ext) 684 180
  have hfn_eq : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr recvCt2ChunkName =
      img.base + 0x59834#64 := by
    rw [Program.fnAddr_rebase, recvCt2Chunk_fnOff]
  rw [← hfn_eq] at hadrp_ct
  clear hA hconcat3 hhmac hfn_eq
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      recvCt2ChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hct2_eq⟩ :=
    exists_unpack64_of_length_128 htake128_len
  dsimp only [authenticatorPinAt]
  refine SepWPp.fold
    (vecU8At_expose_sp_1304 A s0.sp g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey (by omega))
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ptr_ne, hmk_cap_ne⟩
  refine SepWPp.rw_pre (by
    rw [hmk_len,
      memRegion_ct1_split_128 ptr_ct1' hge1088 hmax_ct1',
      memRegion_128_cells (ptr_ct1' + 960#64),
      hct2_eq ptr_ct2_128,
      memRegion_128_split_24_104 s0.sp,
      memRegion_960_split_48_912 s0.sp,
      memRegion_144_split_80_8_56 s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x5eab8 - 0x59834)) hinv ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (hct2_eq ptr_ct2_128).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hct2_eq (ptr_ct1' + 960#64)).symm) (by sep_focus) ?_
  refine SepWP.fold
    (pointsToBytes_append_960_128 ptr_ct1' x.self.uc.ct1 (ct2Full.take 128) hct1_len)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 1920#64) x.epoch))
    (by sep_focus) ?_
  have hct1_full_len :
      BitVec.ofNat 64 (x.self.uc.ct1 ++ ct2Full.take 128).length = 1088#64 := by
    rw [List.length_append, hct1_len, htake128_len]
  have hconcat3_bound :
      43 + (x.self.uc.ct1 ++ ct2Full.take 128).length < 9223372036854775808 := by
    rw [List.length_append, hct1_len, htake128_len]
    decide
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_concat3
    (⟨s0.sp - 288#64, s0.sp - 1248#64,
      true, img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext"), Authenticator.ctLabel,
      false, s0.sp - 1920#64, toBEBytes 8 x.epoch,
      false, ptr_ct1', x.self.uc.ct1 ++ ct2Full.take 128⟩ : SliceConcat3Ghost)
    hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  rw [← List.append_assoc Authenticator.ctLabel]
  have hdata_len :
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)).length = 1131 := by
    simp [List.length_append, ctLabel_length, hct1_len, htake128_len]
  have hdata_pos :
      0 < (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)).length := by
    omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_288 A s0.sp
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128))
      hdata_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_false_of_ne hcap_md_ne
  refine SepWPp.fold
    (fold_sp_1248_24_24 s0.sp
      (img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) 35#64
      (s0.sp - 1920#64) 8#64 ptr_ct1'
      (BitVec.ofNat 64 (x.self.uc.ct1 ++ ct2Full.take 128).length))
    (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_144_80_8_56 s0.sp (bs := toBEBytes 8 x.epoch) (by simp))
    (by sep_focus) ?_
  have hct1_1088 :
      BitVec.ofNat 64 (x.self.uc.ct1 ++ ct2Full.take 128).length = 1088#64 := hct1_full_len
  have hct1_len_nat : (x.self.uc.ct1 ++ ct2Full.take 128).length = 1088 := by
    rw [List.length_append, hct1_len, htake128_len]
  have hfold_ct1 :
      (ptr_ct1' ↦ₛ (x.self.uc.ct1 ++ ct2Full.take 128)) ∗
        memRegion (ptr_ct1' + 1088#64) (cap_ct1'.toNat - 1088) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ⊢
        ct2DeallocAt A cap_ct1' ptr_ct1' := by
    rw [← hct1_1088, ← hct1_len_nat]
    exact bytes_rem_entails_ct2DeallocAt A cap_ct1' ptr_ct1'
      (x.self.uc.ct1 ++ ct2Full.take 128) (by omega) hmax_ct1' hptr_ct1'_ne hcap_ct1'_ne
  refine SepWPp.fold hfold_ct1 (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac")) hF_sf ?_
  wp_steps
  have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
    rw [hsp_sf]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  have hmk_len_bv : BitVec.ofNat 64 auth'.macKey.length = 32#64 := by rw [hmk_len]
  have hmk_lt32 : auth'.macKey.length < 2 ^ 32 := by omega
  have hdata_lt32 :
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)).length < 2 ^ 32 := by
    omega
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_inImage_recvCt2 h_hmac
    (⟨s0.sp - 1248#64, g_auth'.macKey.ptr, auth'.macKey,
      ptr_md, Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)⟩ : LibcruxHmacCall)
    hinv2
  refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
  rw [← List.append_assoc Authenticator.ctLabel,
    ← macCtUnchecked_eq_hmacWith F auth' x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)]
  refine SepWPp.fold
    (bytes_rem_entails_memRegion ptr_md cap_md
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128))
      hle_md hmax_md)
    (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc")) hF_sf_1 ?_
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [hsp_sf_1]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_inImage_recvCt2 h_dealloc (ptr_md, cap_md.toNat, 1) hinv3
  refine SepWPp.pure_left_focus (sf_2.trace = sf_1.trace) (by sep_focus) fun htr3 => ?_
  have hstack_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
    rw [hsp_sf_1, hsp_sf, hsp]
  refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_128_24_104 s0.sp cap_md ptr_md
      (BitVec.ofNat 64 (Authenticator.ctLabel ++ (toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128))).length))
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by ac_rfl)
    (hcont sf_2 hmk_cap_ne (by omega) hmk_max hmk_ptr_ne
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf_2
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
