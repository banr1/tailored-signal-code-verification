/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 5: Shared & Error Epilogues

**Checked by Lean.** Stack-frame recomposition helpers, the shared epilogue tail
(`0x615ec .. 0x61638`, offsets `920 .. 996`) deallocating `mac`/`hdrFull` and dropping
`receivingHdr`, and the `MacVerifyFailed` epilogue body (`0x61574 .. 0x615ec`, offsets `800 .. 920`).
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

/-! ## 1. Stack Frame Recomposition & Drop Glue Helpers -/

theorem polyDecoderAt_entails_sortedSet16_tail (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢
      ⌜(dec.pts.map SortedSetPt.vec).length = NUM_POLYS⌝ ∗
        vecPtListOf A a (dec.pts.map SortedSetPt.vec) ∗
        memRegion (a + 384#64) 16 := by
  unfold polyDecoderAt
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  have hlen_map : (dec.pts.map SortedSetPt.vec).length = NUM_POLYS := by
    rw [List.length_map, hlen]
  refine Entails.pure_right hlen_map ?_
  dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, polyDecoderPadSize]
  rw [sortedSetPtListOf_eq_vecPtListOf A a dec.pts]
  have h1 : ((a + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ⊢ memRegion (a + 384#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (a + 384#64) _
  have h2 : ((a + 392#64) ↦₈ boolByte dec.isComplete) ⊢ memRegion (a + 392#64) 1 :=
    pointsTo8_entails_memRegion (a + 392#64) _
  have hsplit16 : memRegion (a + 384#64) 16 =
      memRegion (a + 384#64) 8 ∗ memRegion (a + 392#64) 1 ∗ memRegion (a + 393#64) 7 := by
    rw [ProofLib.memRegion_split' (b := a + 384#64) (n := 8) (k := 8)
          (b' := a + 392#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 392#64) (n := 1) (k := 7)
          (b' := a + 393#64) rfl (by bv_omega) (by decide)]
  rw [hsplit16]
  have hassoc :
      vecPtListOf A a (dec.pts.map SortedSetPt.vec) ∗
        ((a + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((a + 392#64) ↦₈ boolByte dec.isComplete) ∗
        memRegion (a + 393#64) 7 =
      vecPtListOf A a (dec.pts.map SortedSetPt.vec) ∗
        (((a + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((a + 392#64) ↦₈ boolByte dec.isComplete) ∗
          memRegion (a + 393#64) 7) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))

theorem memRegion_400_of_384_16 (a : BitVec 64) :
    memRegion a 384 ∗ memRegion (a + 384#64) 16 ⊢ memRegion a 400 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 384) (k := 16)
        (b' := a + 384#64) rfl rfl (by decide)]
  exact Entails.refl _

theorem memRegion_400_sp_1560 (sp : BitVec 64) :
    memRegion (sp - 1560#64) 384 ∗ memRegion (sp - 1176#64) 16 ⊢
      memRegion (sp - 1560#64) 400 := by
  rw [ProofLib.memRegion_split' (b := sp - 1560#64) (n := 384) (k := 16)
        (b' := sp - 1176#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_extHook_eq_dropStack32_hdr (sp : BitVec 64) :
    memRegion (sp - 18704#64) 672 ∗ stackAt (sp - 1648#64) extHookStack =
      memRegion (sp - 18704#64) 12928 ∗ stackAt (sp - 1648#64) dropStack32 := by
  have h1 := stackAt_polyDecodedMessage_eq_extHook (sp - 1648#64)
  have h2 := stackAt_polyDecodedMessage_eq_dropStack32 (sp - 1648#64)
  have hsub : (sp - 1648#64) - 17056#64 = sp - 18704#64 := by bv_kernel
  rw [hsub] at h1 h2
  exact h1.symm.trans h2

theorem stackAt_dropStack32_to_polyDecodedMessage_hdr (sp : BitVec 64) :
    memRegion (sp - 18704#64) 12928 ∗ stackAt (sp - 1648#64) dropStack32 ⊢
      stackAt (sp - 1648#64) polyDecodedMessageStackX := by
  have h2 := stackAt_polyDecodedMessage_eq_dropStack32 (sp - 1648#64)
  have hsub : (sp - 1648#64) - 17056#64 = sp - 18704#64 := by bv_kernel
  rw [hsub] at h2
  exact Entails.of_eq h2.symm

theorem vecBufAt_drop64_eq64_emp (A : RustAlloc) (ptr_mac : BitVec 64) (hdrFull : Bytes)
    (heq64 : hdrFull.length = 64) :
    vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ⊢ emp := by
  have hsub0 : hdrFull.length - 64 = 0 := by omega
  have hdrop_nil : hdrFull.drop 64 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hsub0, hdrop_nil, show BitVec.ofNat 64 0 = 0#64 from rfl]
  unfold vecBufAt
  simp only [pointsToBytes_nil, emp_sepConj, ↓reduceIte]
  exact Entails.refl _

theorem vecBufAt_drop64_ne64_dealloc (A : RustAlloc) (ptr_mac : BitVec 64) (hdrFull : Bytes)
    (hge65 : 65 ≤ hdrFull.length) (hmax : hdrFull.length < 2 ^ 63) :
    vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ⊢
      memRegion ptr_mac (hdrFull.length - 64) ∗ A.live ptr_mac (hdrFull.length - 64) 1 := by
  have hlen : (hdrFull.drop 64).length = hdrFull.length - 64 := List.length_drop
  have hne0 : (hdrFull.drop 64).length ≠ 0 := by omega
  have hlt : (hdrFull.drop 64).length < 2 ^ 63 := by omega
  have hexp := vecBufAt_expose_of_bytes_live A ptr_mac (hdrFull.drop 64) hne0 hlt
  rw [hlen] at hexp
  refine Entails.trans hexp ?_
  refine sepConj_mono_left ?_
  rw [← hlen]
  exact ProofLib.pointsToBytes_entails_memRegion ptr_mac (hdrFull.drop 64)

theorem ct2DeallocAt_expose (A : RustAlloc) (cap ptr : BitVec 64) :
    ct2DeallocAt A cap ptr ⊢
      ⌜cap ≠ 0#64 ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        memRegion ptr cap.toNat ∗ A.live ptr cap.toNat 1 := by
  unfold ct2DeallocAt
  exact Entails.refl _

theorem rejoin_stack_hdr_epilogue (s0 : State) :
    stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
      memRegion (s0.sp - 1648#64) 88 ∗
      memRegion (s0.sp - 1560#64) 400 ∗
      memRegion (s0.sp - 1160#64) 1064 ∗
      savedRegsAt s0 ⊢
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX := by
  have h1552 :
      memRegion (s0.sp - 1648#64) 88 ∗
        memRegion (s0.sp - 1560#64) 400 ∗
        memRegion (s0.sp - 1160#64) 1064 =
      hdrActiveFrameRegionsAt (s0.sp - 1648#64) := by
    rw [← memRegion_1552_eq_hdrActiveFrameRegionsAt (s0.sp - 1648#64),
        ProofLib.memRegion_split' (b := s0.sp - 1648#64) (n := 88) (k := 1464)
          (b' := s0.sp - 1560#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1560#64) (n := 400) (k := 1064)
          (b' := s0.sp - 1160#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
      (memRegion (s0.sp - 1648#64) 88 ∗
        memRegion (s0.sp - 1560#64) 400 ∗
        memRegion (s0.sp - 1160#64) 1064) ∗
      savedRegsAt s0 by ac_rfl)) ?_
  rw [h1552]
  exact rejoin_stack_recvHdrChunk s0

/-! ## 2. Shared Epilogue Tail (`0x615ec .. 0x61638`, offsets `920 .. 996`) -/

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_tail_940_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (cap_hdrFull ptr_hdrFull : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 940#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (recvHdrChunkRoAt img ∗
        noHeaderReceivedRecvChunkResultAt A x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  refine SepWPp.fold (ct2DeallocAt_expose A cap_hdrFull ptr_hdrFull) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_hdrFull_ne, hmax_hdrFull, hptr_hdrFull_ne⟩
  have hpos_hdrFull : 0 < cap_hdrFull.toNat := by
    have : cap_hdrFull.toNat ≠ 0 := fun h0 => hcap_hdrFull_ne (BitVec.eq_of_toNat_eq h0)
    omega
  have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hmax_hdrFull' : cap_hdrFull.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_hdrFull_beq : (cap_hdrFull == 0#64) = false := beq_false_of_ne hcap_hdrFull_ne
  have h_dealloc := dealloc_ok_at_recvHdr hA
  have h_drop16 := dropSortedSet16_ok_at_recvHdr (img := img) hdealloc_ext
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx20 hx21
  unfold tripleRatchetProgAtExt at hpc h_dealloc h_drop16 ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 940 60
  clear hA hdealloc_ext
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_dealloc")) hinv ?_
  wp_steps
  have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
    rw [hsp]
  refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_dealloc (ptr_hdrFull, cap_hdrFull.toNat, 1) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWPp.fold
    (polyDecoderAt_entails_sortedSet16_tail A (s0.sp - 1560#64) receivingHdr)
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen_pts => ?_
  have hstack_drop :
      memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack ⊢
        memRegion (s0.sp - 18704#64) 12928 ∗ stackAt sf.sp dropStack32 := by
    rw [hsp_sf, hsp, stackAt_extHook_eq_dropStack32_hdr s0.sp]
    exact Entails.refl _
  refine SepWPp.fold hstack_drop (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry +
      (bv% (ls_off% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>") -
       bv% (ls_off% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"))) hF_sf ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_inImage_recvCt2 h_drop16
    (⟨s0.sp - 1560#64, receivingHdr.pts.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost) hinv2
  refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
  refine SepWPp.fold (memRegion_400_sp_1560 s0.sp) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp dropStack32 = stackAt (s0.sp - 1648#64) dropStack32 := by
    rw [hsp_sf, hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  refine SepWPp.fold (stackAt_dropStack32_to_polyDecodedMessage_hdr s0.sp) (by sep_focus) ?_
  have hsp_sf1_norm : sf_1.readReg64 .sp = s0.sp - 1648#64 := hsp_sf_1.trans (hsp_sf.trans hsp)
  simp only [wp_norm, arm64_norm] at hsp_sf1_norm
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (Entails.of_eq (show
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
    savedRegsAt s0 from rfl)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_hdr_epilogue s0) (by sep_focus) ?_
  unfold recvHdrChunkPostQ
  dsimp only [noHeaderReceivedRecvHdrChunkSpec]
  wp_done

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_tail_924_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hge65 : 65 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 924#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkRoAt img ∗
        noHeaderReceivedRecvChunkResultAt A x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  refine SepWPp.fold (vecBufAt_drop64_ne64_dealloc A ptr_mac hdrFull hge65 hmax_hdr) (by sep_focus) ?_
  have h_dealloc := dealloc_ok_at_recvHdr hA
  have h_tail940 := @recv_hdr_chunk_tail_940_wpp img F A ext hA hdealloc_ext x receivingHdr cap_hdrFull ptr_hdrFull s0
  have hsub_pos : 0 < hdrFull.length - 64 := by omega
  have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsub_max : (hdrFull.length - 64) + 1 ≤ 2 ^ 63 := by omega
  have hsub_toNat : (BitVec.ofNat 64 (hdrFull.length - 64)).toNat = hdrFull.length - 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx20 hx21 hx22 hx23
  unfold tripleRatchetProgAtExt at hpc h_dealloc h_tail940 ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 924 20
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
  wpp_call_inImage_recvCt2 h_dealloc (ptr_mac, hdrFull.length - 64, 1) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWPp.rw_pre (by ac_rfl)
    (h_tail940 sf R
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_tail_920_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 920#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkRoAt img ∗
        noHeaderReceivedRecvChunkResultAt A x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have h_tail940 := @recv_hdr_chunk_tail_940_wpp img F A ext hA hdealloc_ext x receivingHdr cap_hdrFull ptr_hdrFull s0
  have h_tail924 := @recv_hdr_chunk_tail_924_wpp img F A ext hA hdealloc_ext x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac s0
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hx22_0 : st.readReg64 .x22 = 0#64 := by rw [hx22, hsub0]
    simp only [wp_norm, arm64_norm] at hx20 hx21 hx22_0
    refine SepWPp.fold (vecBufAt_drop64_eq64_emp A ptr_mac hdrFull heq64) (by sep_focus) ?_
    unfold tripleRatchetProgAtExt at hpc h_tail940 ⊢
    recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 920 8
    clear hA hdealloc_ext h_tail924
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        noHeaderReceivedRecvHdrChunkName = entry
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    refine SepWPp.of_sepWP_inImage (mid := entry + 940#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by simp only [emp_sepConj, sepConj_emp])
      (h_tail940 _ R
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hge65 : 65 ≤ hdrFull.length := by omega
    have hx22_ne : BitVec.ofNat 64 (hdrFull.length - 64) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      change hdrFull.length - 64 = 0 at h1
      omega
    have hx22_beq : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false :=
      beq_false_of_ne hx22_ne
    simp only [wp_norm, arm64_norm] at hx20 hx21 hx22 hx23
    unfold tripleRatchetProgAtExt at hpc h_tail924 ⊢
    recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 920 8
    clear hA hdealloc_ext h_tail940
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        noHeaderReceivedRecvHdrChunkName = entry
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    refine SepWPp.of_sepWP_inImage (mid := entry + 924#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by ac_rfl)
      (h_tail924 _ R hge65 hmax_hdr
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

/-! ## 3. `MacVerifyFailed` Epilogue (`0x61574 .. 0x615ec`, offsets `800 .. 920`) -/

theorem vecU8HeapAt_eq0_emp (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (h0 : cap = 0#64) :
    vecU8HeapAt A cap ptr bs ⊢ emp := by
  subst h0
  unfold vecU8HeapAt
  apply Entails.pure_left; rintro ⟨_, _, _⟩
  change emp ⊢ emp
  exact Entails.refl _

theorem vecU8HeapAt_ne0_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : cap ≠ 0#64) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      memRegion ptr cap.toNat ∗
      A.live ptr cap.toNat 1 := by
  unfold vecU8HeapAt
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hne' : cap ≠ 0 := hne
  simp only [hne', ↓reduceIte]
  refine Entails.pure_right ⟨hmax, hptr_ne⟩ ?_
  have h1 := pointsToBytes_entails_memRegion ptr bs
  have hsplit : memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      memRegion ptr cap.toNat :=
    (ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)).symm
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  rw [hsplit]
  exact Entails.of_eq (by ac_rfl)

theorem ptr_hdr_take64_entails_memRegion (ptr_hdr : BitVec 64) (hdrFull : Bytes)
    (hge64 : 64 ≤ hdrFull.length) :
    (ptr_hdr ↦ₛ hdrFull.take 64) ⊢ memRegion ptr_hdr 64 := by
  have hlen : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  simpa only [hlen] using pointsToBytes_entails_memRegion ptr_hdr (hdrFull.take 64)

theorem recv_hdr_chunk_err_844_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (s0 st : State) (F_frame R : SepProp)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 844#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx26 : st.readReg64 .x26 = s0.sp - 736#64)
    (hcont : ∀ (st2 : State),
      st2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 864#64 →
      st2.status = .Running →
      st2.sp = s0.sp - 1648#64 →
      st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 →
      ImgCallInv img st2 →
      st2.readReg64 .x19 = x.outA →
      st2.readReg64 .x20 = cap_hdrFull →
      st2.readReg64 .x21 = ptr_hdrFull →
      st2.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st2.readReg64 .x23 = ptr_mac →
      st2.readReg64 .x26 = s0.sp - 736#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st2
        (recvHdrChunkRoAt img ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          A.pool ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPostQ img F A x s0 R)
        (recvHdrChunkPostQp F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (vecU8HeapAt A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey ∗
        recvHdrChunkRoAt img ∗
        ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have h_dealloc := dealloc_ok_at_recvHdr hA
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  by_cases hcap : g_auth0.macKey.cap = 0#64
  · refine SepWPp.fold
      (vecU8HeapAt_eq0_emp A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey hcap)
      (by sep_focus) ?_
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
    unfold tripleRatchetProgAtExt at hpc hcont ⊢
    recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 844 20
    clear hA h_dealloc
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        noHeaderReceivedRecvHdrChunkName = entry
    generalize_entry
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    refine SepWPp.of_sepWP_inImage (mid := entry + 864#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by simp only [emp_sepConj, sepConj_emp])
      (hcont _
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
        (by simp only [wp_norm, arm64_norm, *]))
  · have hcap_beq : (g_auth0.macKey.cap == 0#64) = false := beq_false_of_ne hcap
    have hcap_pos : 0 < g_auth0.macKey.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
    have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    refine SepWPp.fold
      (vecU8HeapAt_ne0_dealloc A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey hcap)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmax, hptr_ne⟩
    have hmax1 : g_auth0.macKey.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
    unfold tripleRatchetProgAtExt at hpc h_dealloc hcont ⊢
    recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 844 20
    clear hA
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
    wpp_call_inImage_recvCt2 h_dealloc (g_auth0.macKey.ptr, g_auth0.macKey.cap.toNat, 1) hinv1
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont sf
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hF_sf
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

theorem memRegion_24_entails_two64_loBytes7 (a : BitVec 64) :
    memRegion a 24 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗
        ((a + 16#64) ↦ₛ EncoderFromPb.loBytes7 w16) ∗
        memRegion (a + 23#64) 1 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8 (Entails.sepExists_right w16 ?_))
  rw [FromPb.pointsTo64_split_7_1 (a + 16#64) w16]
  have ha23 : (a + 16#64) + 7#64 = a + 23#64 := by bv_omega
  rw [ha23]
  have hm1 := pointsTo8_entails_memRegion (a + 23#64) (EncoderFromPb.hiByte w16)
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm1))

theorem two64_loBytes7_entails_memRegion_23 (a w0 w8 : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 7) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦ₛ bs) ⊢
      memRegion a 23 := by
  have h0 := ProofLib.pointsTo64_entails_memRegion a w0
  have h8 := ProofLib.pointsTo64_entails_memRegion (a + 8#64) w8
  have h16 : ((a + 16#64) ↦ₛ bs) ⊢ memRegion (a + 16#64) 7 := by
    rw [← hlen]
    exact pointsToBytes_entails_memRegion (a + 16#64) bs
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 15) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 7) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h0 (sepConj_mono h8 h16)

theorem one64_loBytes7_one64_entails_memRegion_23 (a w0 : BitVec 64) (bs : List (BitVec 8)) (w15 : BitVec 64)
    (hlen : bs.length = 7) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ ((a + 15#64) ↦₆₄ w15) ⊢
      memRegion a 23 := by
  have h0 := ProofLib.pointsTo64_entails_memRegion a w0
  have h8 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 7 := by
    rw [← hlen]
    exact pointsToBytes_entails_memRegion (a + 8#64) bs
  have h15 := ProofLib.pointsTo64_entails_memRegion (a + 15#64) w15
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 15) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 7) (k := 8) (b' := a + 15#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h0 (sepConj_mono h8 h15)

theorem sp_736_80_expose (sp : BitVec 64) :
    memRegion (sp - 736#64) 80 ⊢
      ∃∗ w736 : BitVec 64, ∃∗ w728 : BitVec 64, ∃∗ w720 : BitVec 64,
      ∃∗ w704 : BitVec 64, ∃∗ w696 : BitVec 64, ∃∗ w688 : BitVec 64,
        ((sp - 736#64) ↦₆₄ w736) ∗ ((sp - 728#64) ↦₆₄ w728) ∗
        ((sp - 720#64) ↦ₛ EncoderFromPb.loBytes7 w720) ∗
        memRegion (sp - 713#64) 9 ∗
        ((sp - 704#64) ↦₆₄ w704) ∗ ((sp - 696#64) ↦₆₄ w696) ∗
        ((sp - 688#64) ↦ₛ EncoderFromPb.loBytes7 w688) ∗
        memRegion (sp - 681#64) 25 := by
  rw [ProofLib.memRegion_split' (b := sp - 736#64) (n := 24) (k := 56) (b' := sp - 712#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 712#64) (n := 8) (k := 48) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 24) (k := 24) (b' := sp - 680#64) rfl (by bv_omega) (by decide)]
  have h1 := memRegion_24_entails_two64_loBytes7 (sp - 736#64)
  have h2 := memRegion_24_entails_two64_loBytes7 (sp - 704#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_left h2))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, wp_norm, arm64_norm]
  apply Entails.sepExists_elim; intro w704
  apply Entails.sepExists_elim; intro w696
  apply Entails.sepExists_elim; intro w688
  apply Entails.sepExists_elim; intro w736
  apply Entails.sepExists_elim; intro w728
  apply Entails.sepExists_elim; intro w720
  refine Entails.sepExists_right w736 (Entails.sepExists_right w728 (Entails.sepExists_right w720
    (Entails.sepExists_right w704 (Entails.sepExists_right w696 (Entails.sepExists_right w688 ?_)))))
  rw [ProofLib.memRegion_split' (b := sp - 713#64) (n := 1) (k := 8) (b' := sp - 712#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 681#64) (n := 1) (k := 24) (b' := sp - 680#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem sp_736_80_collapse (sp w736 w728 w721 w704 w696 w689 : BitVec 64) :
    ((sp - 736#64) ↦₆₄ w736) ∗ ((sp - 728#64) ↦₆₄ w728) ∗
      ((sp - 720#64) ↦ₛ EncoderFromPb.hiBytes7 w721) ∗
      memRegion (sp - 713#64) 9 ∗
      ((sp - 704#64) ↦₆₄ w704) ∗ ((sp - 696#64) ↦ₛ EncoderFromPb.loBytes7 w696) ∗
      ((sp - 689#64) ↦₆₄ w689) ∗
      memRegion (sp - 681#64) 25 ⊢
      memRegion (sp - 736#64) 80 := by
  have h1 :
      ((sp - 736#64) ↦₆₄ w736) ∗ ((sp - 728#64) ↦₆₄ w728) ∗
        ((sp - 720#64) ↦ₛ EncoderFromPb.hiBytes7 w721) ⊢
        memRegion (sp - 736#64) 23 := by
    have h := two64_loBytes7_entails_memRegion_23 (sp - 736#64) w736 w728
      (EncoderFromPb.hiBytes7 w721) (EncoderFromPb.length_hiBytes7 w721)
    simpa only [wp_norm, arm64_norm] using h
  have h2 :
      ((sp - 704#64) ↦₆₄ w704) ∗ ((sp - 696#64) ↦ₛ EncoderFromPb.loBytes7 w696) ∗
        ((sp - 689#64) ↦₆₄ w689) ⊢
        memRegion (sp - 704#64) 23 := by
    have h := one64_loBytes7_one64_entails_memRegion_23 (sp - 704#64) w704
      (EncoderFromPb.loBytes7 w696) w689 (EncoderFromPb.length_loBytes7 w696)
    simpa only [wp_norm, arm64_norm] using h
  have hreassoc :
      ((sp - 736#64) ↦₆₄ w736) ∗ ((sp - 728#64) ↦₆₄ w728) ∗
        ((sp - 720#64) ↦ₛ EncoderFromPb.hiBytes7 w721) ∗
        memRegion (sp - 713#64) 9 ∗
        ((sp - 704#64) ↦₆₄ w704) ∗ ((sp - 696#64) ↦ₛ EncoderFromPb.loBytes7 w696) ∗
        ((sp - 689#64) ↦₆₄ w689) ∗
        memRegion (sp - 681#64) 25 =
      (((sp - 736#64) ↦₆₄ w736) ∗ ((sp - 728#64) ↦₆₄ w728) ∗
        ((sp - 720#64) ↦ₛ EncoderFromPb.hiBytes7 w721)) ∗
      (memRegion (sp - 713#64) 9 ∗
        (((sp - 704#64) ↦₆₄ w704) ∗ ((sp - 696#64) ↦ₛ EncoderFromPb.loBytes7 w696) ∗
          ((sp - 689#64) ↦₆₄ w689)) ∗
        memRegion (sp - 681#64) 25) := by ac_rfl
  rw [hreassoc,
      ProofLib.memRegion_split' (b := sp - 736#64) (n := 23) (k := 57) (b' := sp - 713#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 713#64) (n := 9) (k := 48) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 23) (k := 25) (b' := sp - 681#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 (sepConj_mono_right (sepConj_mono_left h2))

theorem out_480_err_expose (out : BitVec 64) :
    memRegion out chunkedHeaderReceivedSize ⊢
      ∃∗ u0 : BitVec 64, ∃∗ ub8 : BitVec 8, ∃∗ u9 : BitVec 64, ∃∗ u17 : BitVec 64, ∃∗ u25 : BitVec 64,
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₈ ub8) ∗
        ((out + 9#64) ↦₆₄ u9) ∗ ((out + 17#64) ↦₆₄ u17) ∗
        ((out + 25#64) ↦ₛ EncoderFromPb.loBytes7 u25) ∗
        memRegion (out + 32#64) 448 := by
  unfold chunkedHeaderReceivedSize
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 472) (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 471) (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 9#64) (n := 24) (k := 447) (b' := out + 33#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out]
  have hb8 := byte_1_entails_exists (out + 8#64)
  have h24 := memRegion_24_entails_two64_loBytes7 (out + 9#64)
  refine Entails.trans (sepConj_mono_right (sepConj_mono hb8 (sepConj_mono_left h24))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, wp_norm, arm64_norm]
  apply Entails.sepExists_elim; intro u9
  apply Entails.sepExists_elim; intro u17
  apply Entails.sepExists_elim; intro u25
  apply Entails.sepExists_elim; intro ub8
  apply Entails.sepExists_elim; intro u0
  refine Entails.sepExists_right u0 (Entails.sepExists_right ub8
    (Entails.sepExists_right u9 (Entails.sepExists_right u17 (Entails.sepExists_right u25 ?_))))
  rw [ProofLib.memRegion_split' (b := out + 32#64) (n := 1) (k := 447) (b' := out + 33#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem out_480_err_collapse {F : ShaCompress} (A : RustAlloc) (out w9 w17 w24 : BitVec 64)
    (res : StatesResult (Chunked.SendCt.NoHeaderReceivedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .error (.err .macVerifyFailed)) :
    (out ↦₆₄ 18446744073709551614#64) ∗ ((out + 8#64) ↦₈ 3#8) ∗
      ((out + 9#64) ↦₆₄ w9) ∗ ((out + 17#64) ↦ₛ EncoderFromPb.loBytes7 w17) ∗
      ((out + 24#64) ↦₆₄ w24) ∗
      memRegion (out + 32#64) 448 ⊢
      noHeaderReceivedRecvChunkResultAt A (F := F) out res := by
  subst hres
  change (out ↦₆₄ none2Cap) ∗ ((out + 8#64) ↦₈ 3#8) ∗
      ((out + 9#64) ↦₆₄ w9) ∗ ((out + 17#64) ↦ₛ EncoderFromPb.loBytes7 w17) ∗
      ((out + 24#64) ↦₆₄ w24) ∗
      memRegion (out + 32#64) 448 ⊢ _
  unfold noHeaderReceivedRecvChunkResultAt spqrErrorByte
  have h23 :
      ((out + 9#64) ↦₆₄ w9) ∗ ((out + 17#64) ↦ₛ EncoderFromPb.loBytes7 w17) ∗
        ((out + 24#64) ↦₆₄ w24) ⊢
        memRegion (out + 9#64) 23 := by
    have h := one64_loBytes7_one64_entails_memRegion_23 (out + 9#64) w9
      (EncoderFromPb.loBytes7 w17) w24 (EncoderFromPb.length_loBytes7 w17)
    simpa only [wp_norm, arm64_norm] using h
  have hreassoc :
      (out ↦₆₄ none2Cap) ∗ ((out + 8#64) ↦₈ 3#8) ∗
        ((out + 9#64) ↦₆₄ w9) ∗ ((out + 17#64) ↦ₛ EncoderFromPb.loBytes7 w17) ∗
        ((out + 24#64) ↦₆₄ w24) ∗
        memRegion (out + 32#64) 448 =
      (out ↦₆₄ none2Cap) ∗ ((out + 8#64) ↦₈ 3#8) ∗
        (((out + 9#64) ↦₆₄ w9) ∗ ((out + 17#64) ↦ₛ EncoderFromPb.loBytes7 w17) ∗
          ((out + 24#64) ↦₆₄ w24)) ∗
        memRegion (out + 32#64) 448 := by ac_rfl
  rw [hreassoc,
      ProofLib.memRegion_split' (b := out + 9#64) (n := 23) (k := 448) (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h23))

@[local arm64_norm, local wp_norm]
theorem out_9_add_8 (out : BitVec 64) : (out + 9#64) + 8#64 = out + 17#64 := by bv_omega

theorem sp_696_realign (sp w696 w688 : BitVec 64) :
    ((sp - 696#64) ↦₆₄ w696) ∗ ((sp - 688#64) ↦ₛ EncoderFromPb.loBytes7 w688) ⊢
      ((sp - 696#64) ↦ₛ EncoderFromPb.loBytes7 w696) ∗
      ((sp - 689#64) ↦₆₄ FromPb.overlapWord7 w696 w688) := by
  have h := FromPb.pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (sp - 696#64) w696 w688
  simpa only [wp_norm, arm64_norm] using Entails.of_eq h

theorem sp_728_realign (sp w728 w720 : BitVec 64) :
    ((sp - 728#64) ↦₆₄ w728) ∗ ((sp - 720#64) ↦ₛ EncoderFromPb.loBytes7 w720) ⊢
      ((sp - 728#64) ↦ₛ EncoderFromPb.loBytes7 w728) ∗
      ((sp - 721#64) ↦₆₄ FromPb.overlapWord7 w728 w720) := by
  have h := FromPb.pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (sp - 728#64) w728 w720
  simpa only [wp_norm, arm64_norm] using Entails.of_eq h

theorem sp_728_721_realign (sp w728 w721 : BitVec 64) :
    ((sp - 728#64) ↦ₛ EncoderFromPb.loBytes7 w728) ∗ ((sp - 721#64) ↦₆₄ w721) ⊢
      ((sp - 728#64) ↦₆₄ FromPb.overlapLow7 w728 w721) ∗
      ((sp - 720#64) ↦ₛ EncoderFromPb.hiBytes7 w721) := by
  have h := FromPb.loBytes7_pointsTo64_eq_overlap (sp - 728#64) w728 w721
  simpa only [wp_norm, arm64_norm] using Entails.of_eq h

theorem out_17_25_realign (out w17 u25 : BitVec 64) :
    ((out + 17#64) ↦₆₄ w17) ∗ ((out + 25#64) ↦ₛ EncoderFromPb.loBytes7 u25) ⊢
      ((out + 17#64) ↦ₛ EncoderFromPb.loBytes7 w17) ∗
      ((out + 24#64) ↦₆₄ FromPb.overlapWord7 w17 u25) := by
  have h := FromPb.pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (out + 17#64) w17 u25
  have ha25 : (out + 17#64) + 8#64 = out + 25#64 := by bv_omega
  have ha24 : (out + 17#64) + 7#64 = out + 24#64 := by bv_omega
  rw [ha25, ha24] at h
  exact Entails.of_eq h

theorem rejoin_sp_1160_1064 (sp v200 : BitVec 64) :
    memRegion (sp - 1160#64) 24 ∗
      memRegion (sp - 1136#64) 384 ∗
      memRegion (sp - 752#64) 16 ∗
      memRegion (sp - 736#64) 80 ∗
      memRegion (sp - 656#64) 456 ∗
      ((sp - 200#64) ↦₆₄ v200) ∗
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 168#64) 48 ∗
      memRegion (sp - 120#64) 8 ∗
      memRegion (sp - 112#64) 16 ⊢
      memRegion (sp - 1160#64) 1064 := by
  have hv200 := ProofLib.pointsTo64_entails_memRegion (sp - 200#64) v200
  rw [ProofLib.memRegion_split' (b := sp - 1160#64) (n := 24) (k := 1040) (b' := sp - 1136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1136#64) (n := 384) (k := 656) (b' := sp - 752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 752#64) (n := 16) (k := 640) (b' := sp - 736#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 736#64) (n := 80) (k := 560) (b' := sp - 656#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 656#64) (n := 456) (k := 104) (b' := sp - 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 200#64) (n := 8) (k := 96) (b' := sp - 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 192#64) (n := 24) (k := 72) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 48) (k := 24) (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 16) (b' := sp - 112#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left hv200)))))

theorem cells11_entails_memRegion_88 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : BitVec 64) :
    ((sp - 1648#64) ↦₆₄ v0) ∗
      ((sp - 1640#64) ↦₆₄ v1) ∗
      ((sp - 1632#64) ↦₆₄ v2) ∗
      ((sp - 1624#64) ↦₆₄ v3) ∗
      ((sp - 1616#64) ↦₆₄ v4) ∗
      ((sp - 1608#64) ↦₆₄ v5) ∗
      ((sp - 1600#64) ↦₆₄ v6) ∗
      ((sp - 1592#64) ↦₆₄ v7) ∗
      ((sp - 1584#64) ↦₆₄ v8) ∗
      ((sp - 1576#64) ↦₆₄ v9) ∗
      ((sp - 1568#64) ↦₆₄ v10) ⊢
      memRegion (sp - 1648#64) 88 := by
  rw [ProofLib.memRegion_cells (sp - 1648#64) 11 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    wp_norm, arm64_norm, emp_sepConj, sepConj_emp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.refl _)))))))))))

theorem authenticatorHeapAt_expose (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator) :
    authenticatorHeapAt A g auth ⊢
      vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        vecU8HeapAt A g.macKey.cap g.macKey.ptr auth.macKey := by
  unfold authenticatorHeapAt vecU8HeapAt
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_err_864_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 864#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx26 : st.readReg64 .x26 = s0.sp - 736#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkRoAt img ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗
        ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ v2) ∗
        ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ v4) ∗
        ((s0.sp - 1608#64) ↦₆₄ v5) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗
        ((s0.sp - 1592#64) ↦₆₄ v7) ∗
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
  have h_drop := dropSortedSet16_ok_at_recvHdr (img := img) hdealloc_ext
  have h_tail920 := @recv_hdr_chunk_tail_920_wpp img F A ext hA hdealloc_ext x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac s0
  refine SepWPp.fold (cells11_entails_memRegion_88 s0.sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) (by sep_focus) ?_
  refine SepWPp.fold (polyDecoderNew1152RawAt_entails_polyDecoderAt A (s0.sp - 1136#64)) (by sep_focus) ?_
  refine SepWPp.fold (polyDecoderAt_entails_sortedSet16_tail A (s0.sp - 1136#64) polyDecoderNew1152) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen16 => ?_
  refine SepWPp.fold (sp_736_80_expose s0.sp) (by sep_focus) ?_
  refine SepWPp.fold (out_480_err_expose x.outA) (by sep_focus) ?_
  sep_elim_exists
  rename_i w736 w728 w720 w704 w696 w688 u0 ub8 u9 u17 u25
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
  unfold tripleRatchetProgAtExt at hpc h_drop h_tail920 ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 864 56
  clear hA hdealloc_ext
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.of_sepWP_inImage (mid := entry +
      (bv% (ls_off% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>") -
       bv% (ls_off% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"))) hinv ?_
  wp_step; wp_step
  refine SepWP.fold (sp_696_realign s0.sp w696 w688) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (sp_728_realign s0.sp w696 w720) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold (sp_728_721_realign s0.sp w696 (FromPb.overlapWord7 w696 w688)) (by sep_focus) ?_
  wp_step; wp_step; wp_step
  refine SepWP.fold (out_17_25_realign x.outA (FromPb.overlapLow7 w696 (FromPb.overlapWord7 w696 w688)) u25) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold
    (sp_736_80_collapse s0.sp w704
      (FromPb.overlapLow7 w696 (FromPb.overlapWord7 w696 w688))
      (FromPb.overlapWord7 w696 w688)
      w704 w696 (FromPb.overlapWord7 w696 w688))
    (by sep_focus) ?_
  refine SepWP.fold
    (out_480_err_collapse A x.outA w704
      (FromPb.overlapLow7 w696 (FromPb.overlapWord7 w696 w688))
      (FromPb.overlapWord7 w696 w688)
      (x.self.recv_hdr_chunk x.epoch x.chunk) hres)
    (by sep_focus) ?_
  have hstack_drop :
      memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack ⊢
        memRegion (s0.sp - 18704#64) 12928 ∗ stackAt st.sp dropStack32 := by
    rw [hsp, stackAt_extHook_eq_dropStack32_hdr s0.sp]
    exact Entails.refl _
  refine SepWP.fold hstack_drop (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_drop
    (⟨s0.sp - 1136#64, polyDecoderNew1152.pts.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_back :
      memRegion (s0.sp - 18704#64) 12928 ∗ stackAt st.sp dropStack32 =
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp, ← stackAt_extHook_eq_dropStack32_hdr s0.sp]
  refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_sp_1160_1064 s0.sp v200) (by sep_focus) ?_
  refine SepWPp.rw_pre (by ac_rfl)
    (h_tail920 sf R hge64 hmax_hdr
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
