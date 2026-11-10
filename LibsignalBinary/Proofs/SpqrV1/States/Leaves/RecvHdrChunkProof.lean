/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Epilogues & Top-Level Proof

**Checked by Lean.** Verifies the `MacVerifyFailed` epilogue entry (`0x61574 .. 0x615ec`,
offsets `800 .. 920`), the `Ok(.done ...)` epilogue (`0x61678 .. 0x61700`, offsets `1060 .. 1196`),
and the top-level contract `noHeaderReceived_recv_hdr_chunk_okX`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

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
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option autoImplicit false
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
  noHeaderReceivedRecvHdrChunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff
  sliceConcat_fnOff shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff dropSortedSetPt16_fnOff
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  (ls_lemma% fnOff "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message")
  (ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")
  (ls_lemma% fnOff "spqr::util::is_non_zero")
  (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
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

/-! ## 1. `MacVerifyFailed` Epilogue Entry (`0x61574 .. 0x615ec`, offsets `800 .. 920`) -/

theorem authenticatorHeapAt_rootKey_eq0 (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator)
    (h0 : g.rootKey.cap = 0#64) :
    authenticatorHeapAt A g auth ⊢
      vecU8HeapAt A g.macKey.cap g.macKey.ptr auth.macKey := by
  have h1 : vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ⊢ emp :=
    vecU8HeapAt_eq0_emp A g.rootKey.cap g.rootKey.ptr auth.rootKey h0
  refine Entails.trans (authenticatorHeapAt_expose A g auth) ?_
  refine Entails.trans (sepConj_mono_left h1) ?_
  exact Entails.of_eq (emp_sepConj _)

theorem authenticatorHeapAt_rootKey_ne0 (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator)
    (hne : g.rootKey.cap ≠ 0#64) :
    authenticatorHeapAt A g auth ⊢
      ⌜g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0#64⌝ ∗
        memRegion g.rootKey.ptr g.rootKey.cap.toNat ∗
        A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗
        vecU8HeapAt A g.macKey.cap g.macKey.ptr auth.macKey := by
  have h1 := vecU8HeapAt_ne0_dealloc A g.rootKey.cap g.rootKey.ptr auth.rootKey hne
  refine Entails.trans (authenticatorHeapAt_expose A g auth) ?_
  refine Entails.trans (sepConj_mono_left h1) ?_
  unfold vecU8HeapAt
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_err_epilogue_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (v0 v3 v6 v8 v9 v10 v200 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (_hptr_hdr : ptr_hdr ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 800#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx25 : st.readReg64 .x25 = ptr_hdr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkRoAt img ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗
        ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
        ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
        ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗
        ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗
        polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗
        memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  refine SepWPp.fold (ptr_hdr_take64_entails_memRegion ptr_hdr hdrFull hge64) (by sep_focus) ?_
  have h_dealloc := dealloc_ok_at_recvHdr hA
  have h_err844 := @recv_hdr_chunk_err_844_wpp img F A ext hA x hdrFull cap_hdrFull ptr_hdrFull ptr_mac g_auth0 s0
  have h_err864 := @recv_hdr_chunk_err_864_wpp img F A ext hA hdealloc_ext x receivingHdr hdrFull
    cap_hdrFull ptr_hdrFull ptr_mac v0 g_auth0.macKey.ptr ptr_hdrFull v3
    g_auth0.rootKey.cap g_auth0.rootKey.ptr v6 g_auth0.macKey.cap v8 v9 v10 v200 s0
  have hpos64 : 0 < 64 := by decide
  have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hmax64 : 64 + 1 ≤ 2 ^ 63 := by decide
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  by_cases hcap : g_auth0.rootKey.cap = 0#64
  · refine SepWPp.fold
      (authenticatorHeapAt_rootKey_eq0 A g_auth0 x.self.uc.auth hcap)
      (by sep_focus) ?_
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx25
    unfold tripleRatchetProgAtExt at hpc h_dealloc h_err844 h_err864 ⊢
    recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 800 44
    clear hA hdealloc_ext
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        noHeaderReceivedRecvHdrChunkName = entry
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_dealloc")) hinv ?_
    wp_steps
    have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
      rw [hsp]
    refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_inImage_recvCt2 h_dealloc (ptr_hdr, 64, 1) hinv1
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    refine SepWPp.of_sepWP_inImage (mid := entry + 844#64) hF_sf ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by ac_rfl)
      (h_err844 _
        (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitAt img.base ∗
          reduceTableAt img.base ∗
          ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
          ((s0.sp - 1648#64) ↦₆₄ v0) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1624#64) ↦₆₄ v3) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ v6) ∗
          ((s0.sp - 1584#64) ↦₆₄ v8) ∗
          ((s0.sp - 1576#64) ↦₆₄ v9) ∗
          ((s0.sp - 1568#64) ↦₆₄ v10) ∗
          polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ v200) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          savedRegsAt s0 ∗
          memRegion (s0.sp - 18704#64) 672)
        R
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun st2 hpc2 hrun2 hsp2 htr2 hvregs2 hinv3 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 =>
          SepWPp.rw_pre (by ac_rfl)
            (h_err864 st2 R hres hge64 hmax_hdr
              hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv3
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2)))
  · have hcap_beq : (g_auth0.rootKey.cap == 0#64) = false := beq_false_of_ne hcap
    have hcap_pos : 0 < g_auth0.rootKey.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
    refine SepWPp.fold
      (authenticatorHeapAt_rootKey_ne0 A g_auth0 x.self.uc.auth hcap)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmax, hptr_ne⟩
    have hmax1 : g_auth0.rootKey.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx25
    unfold tripleRatchetProgAtExt at hpc h_dealloc h_err844 h_err864 ⊢
    recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 800 44
    clear hA hdealloc_ext
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        noHeaderReceivedRecvHdrChunkName = entry
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_dealloc")) hinv ?_
    wp_steps
    have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
      rw [hsp]
    refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_inImage_recvCt2 h_dealloc (ptr_hdr, 64, 1) hinv1
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_dealloc")) hF_sf ?_
    wp_steps
    have hstack_sf' : stackAt (s0.sp - 1648#64) extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf') (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_inImage_recvCt2 h_dealloc (g_auth0.rootKey.ptr, g_auth0.rootKey.cap.toNat, 1) hinv2
    refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    refine SepWPp.rw_pre (by ac_rfl)
      (h_err844 sf_1
        (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitAt img.base ∗
          reduceTableAt img.base ∗
          ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
          ((s0.sp - 1648#64) ↦₆₄ v0) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1624#64) ↦₆₄ v3) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ v6) ∗
          ((s0.sp - 1584#64) ↦₆₄ v8) ∗
          ((s0.sp - 1576#64) ↦₆₄ v9) ∗
          ((s0.sp - 1568#64) ↦₆₄ v10) ∗
          polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ v200) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          savedRegsAt s0 ∗
          memRegion (s0.sp - 18704#64) 672)
        R
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hF_sf_1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun st2 hpc2 hrun2 hsp2 htr3 hvregs2 hinv3 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 =>
          SepWPp.rw_pre (by ac_rfl)
            (h_err864 st2 R hres hge64 hmax_hdr
              hpc2 hrun2 hsp2 hsp_s0 htr3 hvregs2 hinv3
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2)))

/-! ## 2. `Ok(.done ...)` Epilogue (`0x61678 .. 0x61700`, offsets `1060 .. 1196`) -/

theorem sp_sub_1616_orr_9 (sp : BitVec 64) (halign : (sp &&& 15#64 == 0#64) = true) :
    (sp - 1616#64) ||| 9#64 = sp - 1607#64 := by
  have h : sp &&& 15#64 = 0#64 := of_decide_eq_true halign
  bv_kernel

def overlapWord1 (u0 u8 : BitVec 64) : BitVec 64 :=
  (u0 >>> 8) ||| (u8 <<< 56)

theorem hiBytes7_append_loByte_eq (u0 u8 : BitVec 64) :
    Poly.EncoderFromPb.hiBytes7 u0 ++ [Poly.EncoderFromPb.loByte u8] =
      unpack64 (overlapWord1 u0 u8) := by
  simp only [Poly.EncoderFromPb.hiBytes7, Poly.EncoderFromPb.loByte, unpack64, overlapWord1,
    List.drop, List.cons_append, List.nil_append, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem hiBytes7_pointsTo64_eq_overlap1 (p u0 u8 : BitVec 64) :
    (p ↦ₛ Poly.EncoderFromPb.hiBytes7 u0) ∗ ((p + 7#64) ↦₆₄ u8) =
      (p ↦₆₄ overlapWord1 u0 u8) ∗ ((p + 8#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u8) := by
  rw [FromPb.pointsTo64_split_1_7 (p + 7#64) u8]
  have ha : p + 7#64 + 1#64 = p + 8#64 := by bv_omega
  rw [ha, ← sepConj_assoc]
  congr 1
  rw [ProofLib.pointsTo64_eq_pointsToBytes p (overlapWord1 u0 u8),
      ← hiBytes7_append_loByte_eq u0 u8,
      ProofLib.pointsToBytes_append p (Poly.EncoderFromPb.hiBytes7 u0) [Poly.EncoderFromPb.loByte u8],
      Poly.EncoderFromPb.length_hiBytes7,
      ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]

theorem words3_eq_shift1 (b u0 u8 u16 : BitVec 64) :
    (b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16) =
      (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
      ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
      ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
      ((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) := by
  rw [FromPb.pointsTo64_split_1_7 b u0]
  have h1 := hiBytes7_pointsTo64_eq_overlap1 (b + 1#64) u0 u8
  have ha8 : b + 1#64 + 7#64 = b + 8#64 := by bv_omega
  have ha9 : b + 1#64 + 8#64 = b + 9#64 := by bv_omega
  rw [ha8, ha9] at h1
  have h2 := hiBytes7_pointsTo64_eq_overlap1 (b + 9#64) u8 u16
  have ha16 : b + 9#64 + 7#64 = b + 16#64 := by bv_omega
  have ha17 : b + 9#64 + 8#64 = b + 17#64 := by bv_omega
  rw [ha16, ha17] at h2
  calc ((b ↦₈ Poly.EncoderFromPb.loByte u0) ∗ ((b + 1#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u0)) ∗
        ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16)
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        (((b + 1#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u0) ∗ ((b + 8#64) ↦₆₄ u8)) ∗
        ((b + 16#64) ↦₆₄ u16) := by ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        (((b + 9#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u8) ∗ ((b + 16#64) ↦₆₄ u16)) := by
        rw [h1]; ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        ((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) := by
        rw [h2]

theorem words5_eq_shift1 (b u0 u8 u16 u24 u32 : BitVec 64) :
    (b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16) ∗
      ((b + 24#64) ↦₆₄ u24) ∗ ((b + 32#64) ↦₆₄ u32) =
      (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
      ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
      ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
      ((b + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
      ((b + 25#64) ↦₆₄ overlapWord1 u24 u32) ∗
      ((b + 33#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u32) := by
  have h12 := words3_eq_shift1 b u0 u8 u16
  have h3 := hiBytes7_pointsTo64_eq_overlap1 (b + 17#64) u16 u24
  have ha24 : b + 17#64 + 7#64 = b + 24#64 := by bv_omega
  have ha25 : b + 17#64 + 8#64 = b + 25#64 := by bv_omega
  rw [ha24, ha25] at h3
  have h4 := hiBytes7_pointsTo64_eq_overlap1 (b + 25#64) u24 u32
  have ha32 : b + 25#64 + 7#64 = b + 32#64 := by bv_omega
  have ha33 : b + 25#64 + 8#64 = b + 33#64 := by bv_omega
  rw [ha32, ha33] at h4
  calc (b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16) ∗
        ((b + 24#64) ↦₆₄ u24) ∗ ((b + 32#64) ↦₆₄ u32)
    _ = ((b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16)) ∗
        ((b + 24#64) ↦₆₄ u24) ∗ ((b + 32#64) ↦₆₄ u32) := by ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        (((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) ∗ ((b + 24#64) ↦₆₄ u24)) ∗
        ((b + 32#64) ↦₆₄ u32) := by rw [h12]; ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        ((b + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
        (((b + 25#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u24) ∗ ((b + 32#64) ↦₆₄ u32)) := by
        rw [h3]; ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        ((b + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
        ((b + 25#64) ↦₆₄ overlapWord1 u24 u32) ∗
        ((b + 33#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u32) := by
        rw [h4]

def merge17 (w16 u16 : BitVec 64) : BitVec 64 :=
  (w16 &&& 0xff#64) ||| (u16 &&& 0xffffffffffffff00#64)

theorem overlapWord1_merge17 (w8 w16 u16 : BitVec 64) :
    overlapWord1 w8 (merge17 w16 u16) = overlapWord1 w8 w16 := by
  simp only [overlapWord1, merge17]; bv_kernel

theorem hiBytes7_merge17 (w16 u16 : BitVec 64) :
    Poly.EncoderFromPb.hiBytes7 (merge17 w16 u16) = Poly.EncoderFromPb.hiBytes7 u16 := by
  simp only [Poly.EncoderFromPb.hiBytes7, unpack64, merge17, List.drop, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem words3_shift1_unmerge (b w0 w8 w16 u16 : BitVec 64) :
    (b ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((b + 1#64) ↦₆₄ overlapWord1 w0 w8) ∗
      ((b + 9#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) =
      (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w8) ∗ ((b + 16#64) ↦₆₄ merge17 w16 u16) := by
  have h := (words3_eq_shift1 b w0 w8 (merge17 w16 u16)).symm
  rw [overlapWord1_merge17, hiBytes7_merge17] at h
  exact h

def polyDecoderNew1152Tail391At (A : RustAlloc) (p : BitVec 64) : SepProp :=
  (p ↦ₛ Poly.EncoderFromPb.hiBytes7 2#64) ∗
    ((p + 7#64) ↦₆₄ 0#64) ∗
    sortedSetPtListOf A (p + 15#64) (List.replicate 15 SortedSetPt.new) ∗
    ((p + 375#64) ↦₆₄ 576#64) ∗
    ((p + 383#64) ↦₈ 0#8) ∗
    memRegion (p + 384#64) 7

theorem polyDecoderNew1152RawAt_eq_head9_tail391 (A : RustAlloc) (a : BitVec 64) :
    polyDecoderNew1152RawAt A a =
      (a ↦₆₄ 0#64) ∗
      ((a + 8#64) ↦₈ 2#8) ∗
      polyDecoderNew1152Tail391At A (a + 9#64) := by
  unfold polyDecoderNew1152RawAt polyDecoderNew1152Tail391At
  rw [FromPb.pointsTo64_split_1_7 (a + 8#64) 2#64]
  have hlo : Poly.EncoderFromPb.loByte 2#64 = 2#8 := rfl
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have ha16 : a + 9#64 + 7#64 = a + 16#64 := by bv_omega
  have ha24 : a + 9#64 + 15#64 = a + 24#64 := by bv_omega
  have ha384 : a + 9#64 + 375#64 = a + 384#64 := by bv_omega
  have ha392 : a + 9#64 + 383#64 = a + 392#64 := by bv_omega
  have ha393 : a + 9#64 + 384#64 = a + 393#64 := by bv_omega
  rw [hlo, ha9, ha16, ha24, ha384, ha392, ha393]
  ac_rfl

def polyDecoderNew1152Tail391Split (A : RustAlloc) :
    SplitBytes 391 (polyDecoderNew1152Tail391At A) :=
  have h : ∀ p,
      ((p ↦ₛ Poly.EncoderFromPb.hiBytes7 2#64) ∗
        (((p + BitVec.ofNat 64 7) ↦₆₄ 0#64) ∗
          (sortedSetPtListOf A ((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8)
              (List.replicate 15 SortedSetPt.new) ∗
            ((((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8) + BitVec.ofNat 64 360) ↦₆₄ 576#64 ∗
              (((((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8) + BitVec.ofNat 64 360) + BitVec.ofNat 64 8) ↦₈ 0#8 ∗
                memRegion (((((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8) + BitVec.ofNat 64 360) + BitVec.ofNat 64 8) + BitVec.ofNat 64 1) 7))))) =
      polyDecoderNew1152Tail391At A p := by
    intro p
    unfold polyDecoderNew1152Tail391At
    have h15 : (p + 7#64) + 8#64 = p + 15#64 := by bv_omega
    have h375 : (p + 15#64) + 360#64 = p + 375#64 := by bv_omega
    have h383 : (p + 375#64) + 8#64 = p + 383#64 := by bv_omega
    have h384 : (p + 383#64) + 1#64 = p + 384#64 := by bv_omega
    simp only [BitVec.ofNat_eq_ofNat, h15, h375, h383, h384, sepConj_assoc]
  have S_hi7 : SplitBytes 7 (fun p => p ↦ₛ Poly.EncoderFromPb.hiBytes7 2#64) :=
    SplitBytes.pointsToBytesFixed (Poly.EncoderFromPb.hiBytes7 2#64)
  have S_pts15 : SplitBytes 360 (fun p => sortedSetPtListOf A p (List.replicate 15 SortedSetPt.new)) :=
    SplitBytes.arrayAtSplit (SplitBytes.sortedSetPtSplit A) (List.replicate 15 SortedSetPt.new) (by decide)
  SplitBytes.congr h <|
    S_hi7.seq
      ((SplitBytes.pointsTo64 0#64).seq
        (S_pts15.seq
          ((SplitBytes.pointsTo64 576#64).seq
            ((SplitBytes.pointsTo8 0#8).seq (SplitBytes.region 7 (by decide)) (by decide))
            (by decide))
          (by decide))
        (by decide))
      (by decide)

theorem authenticatorHeapAt_rootKey_cap_max (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator) :
    authenticatorHeapAt A g auth ⊢ ⌜g.rootKey.cap.toNat < 2 ^ 63⌝ ∗ authenticatorHeapAt A g auth := by
  unfold authenticatorHeapAt
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  exact Entails.pure_right hmax (Entails.pure_right ⟨hle, hmax, hptr_ne⟩ (Entails.refl _))

theorem words2_eq_loBytes7_overlap7_hiByte (b w0 w8 : BitVec 64) :
    (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w8) =
      (b ↦ₛ Poly.EncoderFromPb.loBytes7 w0) ∗ ((b + 7#64) ↦₆₄ FromPb.overlapWord7 w0 w8) ∗
      ((b + 15#64) ↦₈ Poly.EncoderFromPb.hiByte w8) := by
  rw [FromPb.pointsTo64_split_7_1 (b + 8#64) w8, ← sepConj_assoc,
      FromPb.pointsTo64_loBytes7_eq_loBytes7_overlapWord7 b w0 w8]
  have ha15 : b + 8#64 + 7#64 = b + 15#64 := by bv_omega
  rw [ha15, sepConj_assoc]

theorem collapse_scratch_736 (sp w0 w8 w16 w24 w31 : BitVec 64) (b39 : BitVec 8) :
    memRegion (sp - 736#64) 32 ∗ ((sp - 704#64) ↦₆₄ w0) ∗ ((sp - 696#64) ↦₆₄ w8) ∗
      ((sp - 688#64) ↦₆₄ w16) ∗ ((sp - 680#64) ↦ₛ Poly.EncoderFromPb.loBytes7 w24) ∗
      ((sp - 673#64) ↦₆₄ w31) ∗ ((sp - 665#64) ↦₈ b39) ∗ memRegion (sp - 664#64) 8 ⊢
      memRegion (sp - 736#64) 80 := by
  have hm0 := ProofLib.pointsTo64_entails_memRegion (sp - 704#64) w0
  have hm8 := ProofLib.pointsTo64_entails_memRegion (sp - 696#64) w8
  have hm16 := ProofLib.pointsTo64_entails_memRegion (sp - 688#64) w16
  have hm24 := FromPb.loBytes7_entails_memRegion_7 (sp - 680#64) w24
  have hm31 := ProofLib.pointsTo64_entails_memRegion (sp - 673#64) w31
  have hm39 := pointsTo8_entails_memRegion (sp - 665#64) b39
  rw [ProofLib.memRegion_split' (b := sp - 736#64) (n := 32) (k := 48) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 8) (k := 40) (b' := sp - 696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 696#64) (n := 8) (k := 32) (b' := sp - 688#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 24) (b' := sp - 680#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 680#64) (n := 7) (k := 17) (b' := sp - 673#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 673#64) (n := 8) (k := 9) (b' := sp - 665#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 665#64) (n := 1) (k := 8) (b' := sp - 664#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono hm0 (sepConj_mono hm8 (sepConj_mono hm16
    (sepConj_mono hm24 (sepConj_mono hm31 (sepConj_mono_left hm39))))))

theorem collapse_poly_1136_head9_tail391 (sp : BitVec 64) :
    ((sp - 1136#64) ↦₆₄ 0#64) ∗ ((sp - 1128#64) ↦₈ 2#8) ∗ memRegion (sp - 1127#64) 391 ⊢
      memRegion (sp - 1136#64) 400 := by
  rw [ProofLib.memRegion_split' (b := sp - 1136#64) (n := 8) (k := 392) (b' := sp - 1128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1128#64) (n := 1) (k := 391) (b' := sp - 1127#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

theorem memRegion_out_480_split (out : BitVec 64) :
    memRegion out chunkedHeaderReceivedSize ⊢
      cells out 11 ∗ (∃∗ ub88 : BitVec 8, ((out + 88#64) ↦₈ ub88)) ∗ memRegion (out + 89#64) 391 := by
  unfold chunkedHeaderReceivedSize
  rw [ProofLib.memRegion_split out 88 392 (by decide), ProofLib.memRegion_cells out 11 (by decide),
      ProofLib.memRegion_split' (b := out + 88#64) (n := 1) (k := 391) (b' := out + 89#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (out + 88#64)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_736_80_split (sp : BitVec 64) :
    memRegion (sp - 736#64) 80 ⊢
      memRegion (sp - 736#64) 32 ∗ cells (sp - 704#64) 5 ∗ memRegion (sp - 664#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp - 736#64) (n := 32) (k := 48) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 40) (k := 8) (b' := sp - 664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 704#64) 5 (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem fold_out_ok_done {F : ShaCompress} (A : RustAlloc)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (hdrFull : Bytes) (ptr_hdr : BitVec 64)
    (hptr_hdr : ptr_hdr ≠ 0#64) (hge64 : 64 ≤ hdrFull.length)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk =
      .ok (.done { uc := { auth := x.self.uc.auth, hdr := hdrFull.take 64, epoch := x.epoch }
                   receiving_ek := polyDecoderNew1152 })) :
    (x.outA ↦₆₄ g_auth0.rootKey.cap) ∗ ((x.outA + 8#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
      ((x.outA + 16#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
      ((x.outA + 24#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((x.outA + 32#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      authenticatorHeapAt A g_auth0 x.self.uc.auth ∗ ((x.outA + 48#64) ↦₆₄ 64#64) ∗
      ((x.outA + 56#64) ↦₆₄ ptr_hdr) ∗ ((x.outA + 64#64) ↦₆₄ 64#64) ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ∗
      ((x.outA + 72#64) ↦₆₄ x.epoch) ∗ ((x.outA + 80#64) ↦₆₄ 0#64) ∗
      ((x.outA + 88#64) ↦₈ 2#8) ∗ polyDecoderNew1152Tail391At A (x.outA + 89#64) ⊢
      noHeaderReceivedRecvChunkResultAt A x.outA
        (x.self.recv_hdr_chunk x.epoch x.chunk) := by
  rw [hres]
  dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt,
    chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt]
  refine Entails.pure_right polyDecoderStrictSorted_new1152 ?_
  rw [show (authenticatorAt A x.outA x.self.uc.auth ∗
        vecU8 A (x.outA + 48#64) (hdrFull.take 64) ∗ ((x.outA + 72#64) ↦₆₄ x.epoch)) ∗
      polyDecoderAt A (x.outA + 80#64) polyDecoderNew1152 =
      authenticatorAt A x.outA x.self.uc.auth ∗ vecU8 A (x.outA + 48#64) (hdrFull.take 64) ∗
      ((x.outA + 72#64) ↦₆₄ x.epoch) ∗ polyDecoderAt A (x.outA + 80#64) polyDecoderNew1152 by ac_rfl]
  have hauth := authenticatorPinAt_entails_authenticatorAt A g_auth0 x.outA x.self.uc.auth
  rw [authenticatorPinAt_eq_cells_heap A g_auth0 x.outA x.self.uc.auth] at hauth
  have htake_len64 : (hdrFull.take 64).length = 64 := by rw [List.length_take, Nat.min_eq_left hge64]
  have htake_len : BitVec.ofNat 64 (hdrFull.take 64).length = 64#64 := by rw [htake_len64]
  have hbuf64 : (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ⊢
      vecU8HeapAt A 64#64 ptr_hdr (hdrFull.take 64) := by
    unfold vecU8HeapAt
    refine Entails.pure_right ⟨by rw [htake_len64]; decide, by decide, hptr_hdr⟩ ?_
    have h64_ne : (64#64 : BitVec 64) ≠ 0 := by decide
    simp only [h64_ne, ↓reduceIte, htake_len64, htake_len,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.of_eq (sepConj_comm _ _)
  have hvec_hdr : ((x.outA + 48#64) ↦₆₄ 64#64) ∗ ((x.outA + 56#64) ↦₆₄ ptr_hdr) ∗
      ((x.outA + 64#64) ↦₆₄ 64#64) ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ⊢
      vecU8 A (x.outA + 48#64) (hdrFull.take 64) := by
    dsimp only [vecU8]
    refine Entails.sepExists_right 64#64 (Entails.sepExists_right ptr_hdr ?_)
    rw [vecU8At_eq_cells_heap A (x.outA + 48#64) 64#64 ptr_hdr (hdrFull.take 64), htake_len]
    have ha56 : (x.outA + 48#64) + 8#64 = x.outA + 56#64 := by bv_omega
    have ha64 : (x.outA + 48#64) + 16#64 = x.outA + 64#64 := by bv_omega
    rw [ha56, ha64]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hbuf64))
  have hpoly : ((x.outA + 80#64) ↦₆₄ 0#64) ∗ ((x.outA + 88#64) ↦₈ 2#8) ∗
      polyDecoderNew1152Tail391At A (x.outA + 89#64) ⊢
      polyDecoderAt A (x.outA + 80#64) polyDecoderNew1152 := by
    have ha88 : (x.outA + 80#64) + 8#64 = x.outA + 88#64 := by bv_omega
    have ha89 : (x.outA + 80#64) + 9#64 = x.outA + 89#64 := by bv_omega
    rw [← ha88, ← ha89, ← polyDecoderNew1152RawAt_eq_head9_tail391 A (x.outA + 80#64)]
    exact polyDecoderNew1152RawAt_entails_polyDecoderAt A (x.outA + 80#64)
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((x.outA ↦₆₄ g_auth0.rootKey.cap) ∗ ((x.outA + 8#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((x.outA + 16#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((x.outA + 24#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((x.outA + 32#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        authenticatorHeapAt A g_auth0 x.self.uc.auth) ∗
      (((x.outA + 48#64) ↦₆₄ 64#64) ∗ ((x.outA + 56#64) ↦₆₄ ptr_hdr) ∗
        ((x.outA + 64#64) ↦₆₄ 64#64) ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1) ∗
      ((x.outA + 72#64) ↦₆₄ x.epoch) ∗
      (((x.outA + 80#64) ↦₆₄ 0#64) ∗ ((x.outA + 88#64) ↦₈ 2#8) ∗
        polyDecoderNew1152Tail391At A (x.outA + 89#64)) by ac_rfl)) ?_
  exact sepConj_mono hauth (sepConj_mono hvec_hdr (sepConj_mono_right hpoly))

@[local arm64_norm, local wp_norm]
theorem out_32_add_8 (out : BitVec 64) : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_48_add_8 (out : BitVec 64) : out + 48#64 + 8#64 = out + 56#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_64_add_8 (out : BitVec 64) : out + 64#64 + 8#64 = out + 72#64 := by bv_omega

theorem sp_1608_words5_shift1 (sp w0 w8 w16 w24 w32 : BitVec 64) :
    ((sp - 1608#64) ↦₆₄ w0) ∗ ((sp - 1600#64) ↦₆₄ w8) ∗ ((sp - 1592#64) ↦₆₄ w16) ∗
      ((sp - 1584#64) ↦₆₄ w24) ∗ ((sp - 1576#64) ↦₆₄ w32) =
      ((sp - 1608#64) ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((sp - 1607#64) ↦₆₄ overlapWord1 w0 w8) ∗ ((sp - 1599#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗ ((sp - 1583#64) ↦₆₄ overlapWord1 w24 w32) ∗
      ((sp - 1575#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w32) := by
  have h := words5_eq_shift1 (sp - 1608#64) w0 w8 w16 w24 w32
  have ha1 : sp - 1608#64 + 1#64 = sp - 1607#64 := by bv_omega
  have ha8 : sp - 1608#64 + 8#64 = sp - 1600#64 := by bv_omega
  have ha9 : sp - 1608#64 + 9#64 = sp - 1599#64 := by bv_omega
  have ha16 : sp - 1608#64 + 16#64 = sp - 1592#64 := by bv_omega
  have ha17 : sp - 1608#64 + 17#64 = sp - 1591#64 := by bv_omega
  have ha24 : sp - 1608#64 + 24#64 = sp - 1584#64 := by bv_omega
  have ha25 : sp - 1608#64 + 25#64 = sp - 1583#64 := by bv_omega
  have ha32 : sp - 1608#64 + 32#64 = sp - 1576#64 := by bv_omega
  have ha33 : sp - 1608#64 + 33#64 = sp - 1575#64 := by bv_omega
  rw [ha1, ha8, ha9, ha16, ha17, ha24, ha25, ha32, ha33] at h; exact h

theorem sp_1591_words2_unshift1 (sp w16 w24 w32 : BitVec 64) :
    ((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗ ((sp - 1583#64) ↦₆₄ overlapWord1 w24 w32) ∗
      ((sp - 1575#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w32) =
      ((sp - 1591#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w16) ∗
      ((sp - 1584#64) ↦₆₄ w24) ∗ ((sp - 1576#64) ↦₆₄ w32) := by
  have h3 := (hiBytes7_pointsTo64_eq_overlap1 (sp - 1591#64) w16 w24).symm
  have ha24 : sp - 1591#64 + 7#64 = sp - 1584#64 := by bv_omega
  have ha25 : sp - 1591#64 + 8#64 = sp - 1583#64 := by bv_omega
  rw [ha24, ha25] at h3
  have h4 := (hiBytes7_pointsTo64_eq_overlap1 (sp - 1583#64) w24 w32).symm
  have ha32 : sp - 1583#64 + 7#64 = sp - 1576#64 := by bv_omega
  have ha33 : sp - 1583#64 + 8#64 = sp - 1575#64 := by bv_omega
  rw [ha32, ha33] at h4
  calc ((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗
        ((sp - 1583#64) ↦₆₄ overlapWord1 w24 w32) ∗
        ((sp - 1575#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w32)
    _ = (((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗
         ((sp - 1583#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w24)) ∗
        ((sp - 1576#64) ↦₆₄ w32) := by rw [h4]; ac_rfl
    _ = ((sp - 1591#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w16) ∗
        ((sp - 1584#64) ↦₆₄ w24) ∗ ((sp - 1576#64) ↦₆₄ w32) := by rw [h3]; ac_rfl

theorem sp_1608_words3_unshift1 (sp w0 w8 w16 : BitVec 64) :
    ((sp - 1608#64) ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((sp - 1607#64) ↦₆₄ overlapWord1 w0 w8) ∗ ((sp - 1599#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((sp - 1591#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w16) =
      ((sp - 1608#64) ↦₆₄ w0) ∗ ((sp - 1600#64) ↦₆₄ w8) ∗ ((sp - 1592#64) ↦₆₄ w16) := by
  have h := (words3_eq_shift1 (sp - 1608#64) w0 w8 w16).symm
  have ha1 : sp - 1608#64 + 1#64 = sp - 1607#64 := by bv_omega
  have ha8 : sp - 1608#64 + 8#64 = sp - 1600#64 := by bv_omega
  have ha9 : sp - 1608#64 + 9#64 = sp - 1599#64 := by bv_omega
  have ha16 : sp - 1608#64 + 16#64 = sp - 1592#64 := by bv_omega
  have ha17 : sp - 1608#64 + 17#64 = sp - 1591#64 := by bv_omega
  rw [ha1, ha8, ha9, ha16, ha17] at h; exact h

theorem sp_680_words2_shift7 (sp w0 w8 : BitVec 64) :
    ((sp - 680#64) ↦₆₄ w0) ∗ ((sp - 672#64) ↦₆₄ w8) =
      ((sp - 680#64) ↦ₛ Poly.EncoderFromPb.loBytes7 w0) ∗
      ((sp - 673#64) ↦₆₄ FromPb.overlapWord7 w0 w8) ∗
      ((sp - 665#64) ↦₈ Poly.EncoderFromPb.hiByte w8) := by
  have h := words2_eq_loBytes7_overlap7_hiByte (sp - 680#64) w0 w8
  have ha7 : sp - 680#64 + 7#64 = sp - 673#64 := by bv_omega
  have ha8 : sp - 680#64 + 8#64 = sp - 672#64 := by bv_omega
  have ha15 : sp - 680#64 + 15#64 = sp - 665#64 := by bv_omega
  rw [ha7, ha8, ha15] at h; exact h

theorem out_8_words3_shift1 (out u8 u16 u24 : BitVec 64) :
    ((out + 8#64) ↦₆₄ u8) ∗ ((out + 16#64) ↦₆₄ u16) ∗ ((out + 24#64) ↦₆₄ u24) =
      ((out + 8#64) ↦₈ Poly.EncoderFromPb.loByte u8) ∗
      ((out + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗ ((out + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
      ((out + 25#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u24) := by
  have h := words3_eq_shift1 (out + 8#64) u8 u16 u24
  have ha9 : out + 8#64 + 1#64 = out + 9#64 := by bv_omega
  have ha16 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
  have ha17 : out + 8#64 + 9#64 = out + 17#64 := by bv_omega
  have ha24 : out + 8#64 + 16#64 = out + 24#64 := by bv_omega
  have ha25 : out + 8#64 + 17#64 = out + 25#64 := by bv_omega
  rw [ha9, ha16, ha17, ha24, ha25] at h; exact h

theorem out_8_words3_unmerge (out w0 w8 w16 u24 : BitVec 64) :
    ((out + 8#64) ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((out + 9#64) ↦₆₄ overlapWord1 w0 w8) ∗ ((out + 17#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((out + 25#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u24) =
      ((out + 8#64) ↦₆₄ w0) ∗ ((out + 16#64) ↦₆₄ w8) ∗ ((out + 24#64) ↦₆₄ merge17 w16 u24) := by
  have h := words3_shift1_unmerge (out + 8#64) w0 w8 w16 u24
  have ha9 : out + 8#64 + 1#64 = out + 9#64 := by bv_omega
  have ha16 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
  have ha17 : out + 8#64 + 9#64 = out + 17#64 := by bv_omega
  have ha24 : out + 8#64 + 16#64 = out + 24#64 := by bv_omega
  have ha25 : out + 8#64 + 17#64 = out + 25#64 := by bv_omega
  rw [ha9, ha16, ha17, ha24, ha25] at h; exact h

theorem poly_1136_split_head9_tail391 (A : RustAlloc) (sp : BitVec 64) :
    polyDecoderNew1152RawAt A (sp - 1136#64) =
      ((sp - 1136#64) ↦₆₄ 0#64) ∗ ((sp - 1128#64) ↦₈ 2#8) ∗
      polyDecoderNew1152Tail391At A (sp - 1127#64) := by
  have h := polyDecoderNew1152RawAt_eq_head9_tail391 A (sp - 1136#64)
  have ha8 : (sp - 1136#64) + 8#64 = sp - 1128#64 := by bv_omega
  have ha9 : (sp - 1136#64) + 9#64 = sp - 1127#64 := by bv_omega
  rw [ha8, ha9] at h; exact h

@[local arm64_norm, local wp_norm]
theorem zeroExtend32_truncate8_loByte (w : BitVec 64) :
    BitVec.truncate 8 (BitVec.truncate 32 (BitVec.zeroExtend 64 (Poly.EncoderFromPb.loByte w))) =
      Poly.EncoderFromPb.loByte w := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem bv391_toNat : (391#64 : BitVec 64).toNat = 391 := rfl

theorem collapse_tail_1160_1064 (sp v200 : BitVec 64) :
    memRegion (sp - 1160#64) 24 ∗ memRegion (sp - 1136#64) 400 ∗
      memRegion (sp - 736#64) 80 ∗ memRegion (sp - 656#64) 456 ∗
      ((sp - 200#64) ↦₆₄ v200) ∗ memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 168#64) 48 ∗ memRegion (sp - 120#64) 8 ∗
      memRegion (sp - 112#64) 16 ⊢ memRegion (sp - 1160#64) 1064 := by
  rw [ProofLib.memRegion_split' (b := sp - 1136#64) (n := 384) (k := 16)
        (b' := sp - 752#64) rfl (by bv_omega) (by decide), sepConj_assoc]
  exact rejoin_sp_1160_1064 sp v200

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_ok_epilogue_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc_ext : DeallocOkExt img.base A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk =
      .ok (.done { uc := { auth := x.self.uc.auth, hdr := hdrFull.take 64, epoch := x.epoch }
                   receiving_ek := polyDecoderNew1152 }))
    (hptr_hdr : ptr_hdr ≠ 0#64) (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 1060#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx19 : st.readReg64 .x19 = x.outA) (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx24 : st.readReg64 .x24 = x.epoch)
    (hx25 : st.readReg64 .x25 = ptr_hdr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (authenticatorHeapAt A g_auth0 x.self.uc.auth ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkRoAt img ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have horr := sp_sub_1616_orr_9 s0.sp hsp_s0
  have hmc_raw := hA.session_memcpy_region_ok_at noHeaderReceivedRecvHdrChunkName
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy")) extHookStack (by decide) (by decide)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, memcpy_fnOff])
  have h_memcpy := (polyDecoderNew1152Tail391Split A).memcpy_withStack_inImage_ok
    (by decide) extHookStack hmc_raw
  have h_tail940 := @recv_hdr_chunk_tail_940_wpp img F A ext hA hdealloc_ext
    x receivingHdr cap_hdrFull ptr_hdrFull s0
  have h_tail924 := @recv_hdr_chunk_tail_924_wpp img F A ext hA hdealloc_ext
    x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac s0
  refine SepWPp.fold (authenticatorHeapAt_rootKey_cap_max A g_auth0 x.self.uc.auth) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hmax_rk => ?_
  have hmax1 : g_auth0.rootKey.cap.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_cmn : (g_auth0.rootKey.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hmax_rk
  refine SepWPp.fold (memRegion_out_480_split x.outA) (by sep_focus) ?_
  refine SepWPp.fold (memRegion_736_80_split s0.sp) (by sep_focus) ?_
  dsimp only [cells]
  sep_elim_exists
  rename_i ub88 u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 sc0 sc8 sc16 sc24 sc32
  simp only [bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.fold (Entails.of_eq (poly_1136_split_head9_tail391 A s0.sp)) (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (sp_1608_words5_shift1 s0.sp
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
    g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)))
    (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (out_8_words3_shift1 x.outA u8 u16 u24)) (by sep_focus) ?_
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25
  unfold tripleRatchetProgAtExt at hpc h_memcpy h_tail940 h_tail924 ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 1060 140
  clear hA hdealloc_ext hmc_raw
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy")) hinv ?_
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (sp_1591_words2_unshift1 s0.sp
    g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (sp_680_words2_shift7 s0.sp
    (overlapWord1 g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)) sc32))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (sp_1608_words3_unshift1 s0.sp
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length) g_auth0.macKey.cap))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (out_8_words3_unmerge x.outA
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length) g_auth0.macKey.cap u24))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (collapse_scratch_736 s0.sp
    (overlapWord1 g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length))
    (overlapWord1 (BitVec.ofNat 64 x.self.uc.auth.rootKey.length) g_auth0.macKey.cap)
    (overlapWord1 g_auth0.macKey.cap g_auth0.macKey.ptr)
    (overlapWord1 g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length))
    (BitVec.ofNat 64 x.self.uc.auth.macKey.length)
    (Poly.EncoderFromPb.hiByte sc32)) (by sep_focus) ?_
  have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by rw [hsp]
  refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_memcpy (x.outA + 89#64, s0.sp - 1127#64) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace ∧ sf.readReg64 (Reg.gpr 0#5) = x.outA + 89#64)
    (by sep_focus) fun ⟨htr1, _⟩ => ?_
  have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by rw [hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWPp.fold (fold_out_ok_done A x g_auth0 hdrFull ptr_hdr hptr_hdr hge64 hres) (by sep_focus) ?_
  refine SepWPp.fold (collapse_poly_1136_head9_tail391 s0.sp) (by sep_focus) ?_
  refine SepWPp.fold
    (cells11_entails_memRegion_88 s0.sp v0 v1 ptr_hdrFull v3
      g_auth0.rootKey.cap g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
      g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length) v10)
    (by sep_focus) ?_
  refine SepWPp.fold (collapse_tail_1160_1064 s0.sp v200) (by sep_focus) ?_
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hx22_sf0 : sf.readReg64 (Reg.gpr 22#5) = 0#64 := by
      rw [h_3, hx22, hsub0]
    refine SepWPp.of_sepWP_inImage (mid := entry + 940#64) hF_sf ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.fold (vecBufAt_drop64_eq64_emp A ptr_mac hdrFull heq64) (by sep_focus) ?_
    refine SepWPp.rw_pre (by simp only [emp_sepConj, sepConj_emp]; ac_rfl)
      (h_tail940 _ R (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) hsp_s0
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hge65 : 65 ≤ hdrFull.length := by omega
    have hx22_ne : BitVec.ofNat 64 (hdrFull.length - 64) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      change hdrFull.length - 64 = 0 at h1; omega
    have hx22_beq : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false :=
      beq_false_of_ne hx22_ne
    have hx22_sf_ne : (sf.readReg64 (Reg.gpr 22#5) == 0#64) = false := by
      rw [h_3, hx22]
      exact hx22_beq
    refine SepWPp.of_sepWP_inImage (mid := entry + 924#64) hF_sf ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by ac_rfl)
      (h_tail924 _ R hge65 hmax_hdr (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) hsp_s0
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv2
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))

/-! ## 3. Top-Level Proof (`noHeaderReceived_recv_hdr_chunk_okX`) -/

theorem recv_hdr_chunk_eq_macVerifyFailed {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length) (hmk : self.uc.auth.macKey.length < 2 ^ 32)
    (hle32 : (hdrFull.drop 64).length ≤ 32)
    (hcmp : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F epoch (hdrFull.take 64)) != 0#8) = true) :
    self.recv_hdr_chunk epoch chunk = .error (.err .macVerifyFailed) := by
  have hd : (Authenticator.hdrLabel ++ toBEBytes 8 self.uc.epoch ++ hdrFull.take 64).length < 2 ^ 32 := by
    have htake : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake]; decide
  have hcmp' : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F self.uc.epoch (hdrFull.take 64)) != 0#8) = true := by rwa [← hepoch]
  rw [recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull hepoch hadd hdec (by omega),
      verifyHdrError_of_mac_le_32 F self.uc.auth self.uc.epoch (hdrFull.take 64) (hdrFull.drop 64)
        hmk hd hle32,
      hcmp']
  rfl

theorem recv_hdr_chunk_eq_ok_done {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length) (hmk : self.uc.auth.macKey.length < 2 ^ 32)
    (hle32 : (hdrFull.drop 64).length ≤ 32)
    (hcmp : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F epoch (hdrFull.take 64)) != 0#8) = false) :
    self.recv_hdr_chunk epoch chunk =
      .ok (.done { uc := { auth := self.uc.auth, hdr := hdrFull.take 64, epoch := epoch }
                   receiving_ek := polyDecoderNew1152 }) := by
  have hd : (Authenticator.hdrLabel ++ toBEBytes 8 self.uc.epoch ++ hdrFull.take 64).length < 2 ^ 32 := by
    have htake : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake]; decide
  have hcmp' : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F self.uc.epoch (hdrFull.take 64)) != 0#8) = false := by rwa [← hepoch]
  rw [recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull hepoch hadd hdec (by omega),
      verifyHdrError_of_mac_le_32 F self.uc.auth self.uc.epoch (hdrFull.take 64) (hdrFull.drop 64)
        hmk hd hle32,
      hcmp', ← hepoch]
  rfl

set_option maxHeartbeats 800000 in
theorem noHeaderReceived_recv_hdr_chunk_okX {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) (hdealloc_ext : DeallocOkExt img.base A ext)
    (hadd_ok : AddChunkOkX img A ext) (hdec_ok : PolyDecodedMessageOkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    NoHeaderReceivedRecvHdrChunkOkX img F A ext := by
  unfold NoHeaderReceivedRecvHdrChunkOkX
  refine subroutine_ok_inImage_rodata1_keep (rodata_hdrLabel himg) ?_
  dsimp only [noHeaderReceivedRecvHdrChunkSpec]
  wpp_init x s0
  have hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  replace hpc : s0.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName :=
    hpc.trans (by unfold tripleRatchetProgAtExt; rw [Program.fnAddr_rebase, noHeaderReceivedRecvHdrChunk_fnOff])
  change SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
    (recvHdrChunkRoAt img ∗
      memRegion x.outA chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt img.base ∗
      reduceTableAt img.base ∗
      A.pool ∗
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
    (recvHdrChunkPostQ img F A x s0 R)
    (recvHdrChunkPostQp F A img.base x s0 R)
  refine recv_hdr_chunk_part1_wpp hA hadd_ok hdec_ok x s0 R
    h hpc hrun hsp_s0 h_3 hinv0 h_4 h_5 h_6 h_7
    (fun st2 receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0
      hepoch hadd hsort hdec hge64 hlt_max hptr_hdr
      hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_)
  refine SepWPp.frame_call
    (recvHdrChunkRoAt img ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗
      authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
      ((s0.sp - 1640#64) ↦₆₄ c1) ∗
      ((s0.sp - 1632#64) ↦₆₄ c2) ∗
      ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      memRegion (s0.sp - 192#64) 24 ∗
      memRegion (s0.sp - 168#64) 48 ∗
      memRegion (s0.sp - 120#64) 8 ∗
      A.pool ∗
      stackAt (s0.sp - 1648#64) extHookStack)
    (by sep_focus) (by repeat rw [sepConj_assoc])
    (recv_hdr_chunk_hmac_wpp hA hconcat3 hhmac x receivingHdr hdrFull
      cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0 s0 st2 _ R
      hepoch hadd hdec hge64 h_3
      hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
      (fun st3 hmk_lt32 hpc3 hrun3 hsp3 htr3 hvregs3 hinv3
        hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  refine SepWPp.frame_call
    (vecU8 A (s0.sp - 168#64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
      memRegion (s0.sp - 144#64) 24 ∗
      vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
      A.pool ∗
      stackAt (s0.sp - 1648#64) extHookStack)
    (by sep_focus) (by repeat rw [sepConj_assoc])
    (recv_hdr_chunk_mac_compare_wpp hA x receivingHdr hdrFull ptr_mac s0 st3 _ R
      hepoch hadd hdec hge64 hlt_max hmk_lt32
      hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3 hinv3
      hx21_3 hx22_3 hx26_3 hx29_3
      (fun st4 hle32 hcmp hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx19_4 hx20_4 _ hx22_4 hx23_4 _ hx25_4 _ _ => ?_)
      (fun st4 hle32 hcmp_f hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx19_4 hx20_4 _ hx22_4 hx23_4 hx24_4 hx25_4 _ _ => ?_))
  · have hres_err := recv_hdr_chunk_eq_macVerifyFailed x.self x.epoch x.chunk
      receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hle32 hcmp
    refine SepWPp.rw_pre (by ac_rfl)
      (recv_hdr_chunk_err_epilogue_wpp hA hdealloc_ext x receivingHdr hdrFull
        cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr
        0#64 x.epoch (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
        g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)
        x.self.uc.epoch x.epoch g_auth0 s0 st4 R
        hres_err hge64 hlt_max hptr_hdr
        hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
        (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hx22_4 hx23_4 (hx25_4.trans hx25_3))
  · have hres_ok := recv_hdr_chunk_eq_ok_done x.self x.epoch x.chunk
      receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hle32 hcmp_f
    refine SepWPp.rw_pre (by ac_rfl)
      (recv_hdr_chunk_ok_epilogue_wpp hA hdealloc_ext x g_auth0 receivingHdr hdrFull
        cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac
        0#64 g_auth0.macKey.ptr x.epoch x.self.uc.epoch x.epoch s0 st4 R
        hres_ok hptr_hdr hge64 hlt_max
        hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
        (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hx22_4 hx23_4
        (hx24_4.trans hx24_3) (hx25_4.trans hx25_3))

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
