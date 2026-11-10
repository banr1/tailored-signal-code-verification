/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefs
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 1 (`0x61254 .. 0x61488`)

**Checked by Lean.** Callee `subroutine_ok` wrappers, panic helpers, the `None` (`StillReceiving`)
branch (`recv_hdr_chunk_none_wpp`), and `Some(hdrFull)` length check with `mac`/`hdr` heap
allocations (`recv_hdr_chunk_alloc_mac_hdr_wpp`).
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
  (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
  (ls_lemma% fnOff "spqr::util::is_non_zero")
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

/-! ## 1. Fetch Macro, Postcondition Abbreviations, and Callee Wrappers -/

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside `0x61254`. -/
macro "recv_hdr_chunk_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode recvHdrChunkBin $b $H noHeaderReceivedRecvHdrChunk_fnOff 0x5be5c $k0 $len)

abbrev recvHdrChunkRoAt (img : Obj.Image) : SepProp :=
  (img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader")) ↦ᵣ Authenticator.hdrLabel

abbrev recvHdrChunkPostQ (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader")) ↦ᵣ Authenticator.hdrLabel) ∗
          (noHeaderReceivedRecvHdrChunkSpec F A img.base).post x s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev recvHdrChunkPostQp (F : ShaCompress) (_A : RustAlloc) (_b : BitVec 64)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (⌜((x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∨ allocFailedIn s0 sf) ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem sub_ok_at_recvHdr {α : Type} {img : Obj.Image}
    {ext : String → Option (State → State)} {callee : String} {off : BitVec 64} {spec : Spec α}
    (hoff : BitVec.ofNat 64 (libsignalSessionCode.fnOff noHeaderReceivedRecvHdrChunkName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff callee))
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr callee) spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + off) spec := by
  have haddr :
      (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + off =
        (tripleRatchetProgAtExt img.base ext).fnAddr callee := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hoff]
  rwa [haddr]

theorem shim_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hA

theorem memcpy_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hA

theorem alloc_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hA

theorem dealloc_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hA

theorem addChunk_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"))
      ((addChunkSpecX A).inImage img) := by
  unfold AddChunkOkX at h
  exact sub_ok_at_recvHdr (callee := addChunkName)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, addChunk_fnOff]; rfl) h

theorem polyDecodedMessage_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : PolyDecodedMessageOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
      ((polyDecodedMessageSpec A img.base).inImage img) :=
  sub_ok_at_recvHdr (callee := polyDecodedMessageName)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, polyDecodedMessage_fnOff]; rfl) h

theorem sliceConcat3_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : SliceConcat3OkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"))
      ((sliceConcat3Spec A).inImage img) :=
  sub_ok_at_recvHdr (callee := sliceConcatName)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, sliceConcat_fnOff]; rfl) h

theorem libcrux_hmac_ok_at_recvHdr {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "libcrux_hmac::hmac"))
      ((libcruxHmacSpec F A).inImage img) :=
  Alloc.subroutine_ok_inImage img <|
    libcrux_hmac_ok_at_ext img.base F A ext hhmac noHeaderReceivedRecvHdrChunkName
      (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "libcrux_hmac::hmac"))
      (by simp only [arm64_norm])

theorem isNonZero_ok_at_recvHdr (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "spqr::util::is_non_zero"))
      (isNonZeroSpec.inImage img) :=
  sub_ok_at_recvHdr (callee := isNonZeroName)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, gf16IsNonZero_fnOff]; rfl)
    (Alloc.subroutine_ok_inImage img (isNonZero_ok img.base ext))

theorem dropSortedSet16_ok_at_recvHdr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        (bv% (ls_off% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>") -
         bv% (ls_off% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk")))
      ((dropGlueSortedSetPt16Spec A).inImage img) :=
  sub_ok_at_recvHdr (callee := dropSortedSetPt16Name)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, dropSortedSetPt16_fnOff]; rfl)
    (Alloc.subroutine_ok_inImage img (drop_glue_sorted_set_pt16_ok_ext hdealloc))

theorem panic_at_handle_error_recvHdr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext noHeaderReceivedRecvHdrChunkName
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
      "alloc::raw_vec::handle_error"))

theorem panic_at_assert_failed_u64_recvHdr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "core::panicking::assert_failed::<u64, u64>")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext noHeaderReceivedRecvHdrChunkName assertFailedU64Name
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
      "core::panicking::assert_failed::<u64, u64>"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

theorem panic_at_slice_index_fail_recvHdr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "core::slice::index::slice_index_fail")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext noHeaderReceivedRecvHdrChunkName sliceIndexFailName
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
      "core::slice::index::slice_index_fail"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

theorem panic_at_bounds_check_recvHdr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "core::panicking::panic_bounds_check")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext noHeaderReceivedRecvHdrChunkName panicBoundsCheckName
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
      "core::panicking::panic_bounds_check"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

/-! ## 2. Structural Expose and Fold Helpers for `NoHeaderReceived` -/

theorem noHeaderReceivedUcAt_expose_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)) :
    unchunkedNoHeaderReceivedAt A a uc ⊢
      ∃∗ g_auth : AuthenticatorGhost,
        (a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((a + 48#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth := by
  unfold unchunkedNoHeaderReceivedAt
  rw [authenticatorAt_eq_exists_pinned A a uc.auth]
  refine Entails.trans (sepConj_mono_left (Entails.sepExists_elim fun g_auth =>
    Entails.sepExists_right g_auth (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_auth a uc.auth)))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g_auth => Entails.sepExists_right g_auth ?_
  exact Entails.of_eq (by ac_rfl)

theorem noHeaderReceivedUcAt_fold_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F))
    (g_auth : AuthenticatorGhost) :
    (a ↦₆₄ g_auth.rootKey.cap) ∗
      ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
      ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
      ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
      ((a + 48#64) ↦₆₄ uc.epoch) ∗
      authenticatorHeapAt A g_auth uc.auth ⊢
      unchunkedNoHeaderReceivedAt A a uc := by
  unfold unchunkedNoHeaderReceivedAt
  have harrange :
      (a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((a + 48#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth =
      ((a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        authenticatorHeapAt A g_auth uc.auth) ∗
      ((a + 48#64) ↦₆₄ uc.epoch) := by ac_rfl
  rw [harrange, ← authenticatorPinAt_eq_cells_heap A g_auth a uc.auth]
  exact sepConj_mono_left (authenticatorPinAt_entails_authenticatorAt A g_auth a uc.auth)

theorem noHeaderReceivedCells_entails_memRegion_456
    (a c0 c1 c2 c3 c4 c5 c6 : BitVec 64) :
    (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
      ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
      ((a + 48#64) ↦₆₄ c6) ∗ memRegion (a + 56#64) 400 ⊢
      memRegion a chunkedNoHeaderReceivedSize := by
  change _ ⊢ memRegion a 456
  rw [ProofLib.memRegion_split' (b := a) (n := 56) (k := 400)
        (b' := a + 56#64) rfl rfl (by decide),
      ProofLib.memRegion_cells a 7 (by decide)]
  have hc7 :
      (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ⊢ cells a 7 := by
    dsimp only [cells]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      emp_sepConj, sepConj_emp]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.refl _)))))))
  have hgroup :
      (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ∗ memRegion (a + 56#64) 400 =
      ((a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6)) ∗ memRegion (a + 56#64) 400 := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left hc7

theorem memRegion_456_at_fsp_3e0_split (fsp : BitVec 64) :
    memRegion (fsp + 0x3e0#64) 456 =
      (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
       ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64,
        ((fsp + 0x3e0#64) ↦₆₄ d0) ∗ ((fsp + 0x3e8#64) ↦₆₄ d1) ∗
        ((fsp + 0x3f0#64) ↦₆₄ d2) ∗ ((fsp + 0x3f8#64) ↦₆₄ d3) ∗
        ((fsp + 0x400#64) ↦₆₄ d4) ∗ ((fsp + 0x408#64) ↦₆₄ d5) ∗
        ((fsp + 0x410#64) ↦₆₄ d6)) ∗
      memRegion (fsp + 0x418#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 0x3e0#64) (n := 56) (k := 400)
        (b' := fsp + 0x418#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (fsp + 0x3e0#64) 7 (by decide)]
  congr 1
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem chunkedNoHeaderReceivedAt_fsp_3e0_entails (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F))
    (receivingHdr : PolyDecoder) (g_auth : AuthenticatorGhost) :
    ((sp - 656#64) ↦₆₄ g_auth.rootKey.cap) ∗
      ((sp - 648#64) ↦₆₄ g_auth.rootKey.ptr) ∗
      ((sp - 640#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
      ((sp - 632#64) ↦₆₄ g_auth.macKey.cap) ∗
      ((sp - 624#64) ↦₆₄ g_auth.macKey.ptr) ∗
      ((sp - 616#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
      ((sp - 608#64) ↦₆₄ uc.epoch) ∗
      authenticatorHeapAt A g_auth uc.auth ∗
      polyDecoderAt A (sp - 600#64) receivingHdr ⊢
      chunkedNoHeaderReceivedAt A (sp - 656#64) { uc := uc, receiving_hdr := receivingHdr } := by
  unfold chunkedNoHeaderReceivedAt unchunkedNoHeaderReceivedAt
  have h56 : (sp - 656#64) + 56#64 = sp - 600#64 := by bv_omega
  have h8 : (sp - 656#64) + 8#64 = sp - 648#64 := by bv_omega
  have h16 : (sp - 656#64) + 16#64 = sp - 640#64 := by bv_omega
  have h24 : (sp - 656#64) + 24#64 = sp - 632#64 := by bv_omega
  have h32 : (sp - 656#64) + 32#64 = sp - 624#64 := by bv_omega
  have h40 : (sp - 656#64) + 40#64 = sp - 616#64 := by bv_omega
  have h48 : (sp - 656#64) + 48#64 = sp - 608#64 := by bv_omega
  rw [h56, h48]
  have hauth := authenticatorPinAt_entails_authenticatorAt A g_auth (sp - 656#64) uc.auth
  rw [authenticatorPinAt_eq_cells_heap A g_auth (sp - 656#64) uc.auth, h8, h16, h24, h32, h40] at hauth
  have hgroup :
      ((sp - 656#64) ↦₆₄ g_auth.rootKey.cap) ∗
        ((sp - 648#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((sp - 640#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((sp - 632#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((sp - 624#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((sp - 616#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((sp - 608#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth ∗
        polyDecoderAt A (sp - 600#64) receivingHdr =
      ((((sp - 656#64) ↦₆₄ g_auth.rootKey.cap) ∗
          ((sp - 648#64) ↦₆₄ g_auth.rootKey.ptr) ∗
          ((sp - 640#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
          ((sp - 632#64) ↦₆₄ g_auth.macKey.cap) ∗
          ((sp - 624#64) ↦₆₄ g_auth.macKey.ptr) ∗
          ((sp - 616#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
          authenticatorHeapAt A g_auth uc.auth) ∗
        ((sp - 608#64) ↦₆₄ uc.epoch)) ∗
      polyDecoderAt A (sp - 600#64) receivingHdr := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (sepConj_mono_left hauth)

theorem memRegion_480_outA_split (outA : BitVec 64) :
    memRegion outA chunkedHeaderReceivedSize =
      (∃∗ v0 : BitVec 64, outA ↦₆₄ v0) ∗
        memRegion (outA + 8#64) 456 ∗
        memRegion (outA + 464#64) 16 := by
  change memRegion outA 480 = _
  rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 472)
        (b' := outA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 16)
        (b' := outA + 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outA]

/-! ## 3. `None` (`StillReceiving`) Branch (`0x61308 .. 0x6134c` + `0x6161c .. 0x61638`) -/

set_option maxHeartbeats 800000 in
theorem recv_hdr_chunk_none_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (s0 st : State) (R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hsort : PolyDecoderStrictSorted receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok none)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 180#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx21 : st.readReg64 .x21 = x.selfA)
    (hx22 : st.readReg64 .x22 = s0.sp - 736#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (recvHdrChunkRoAt img ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        unchunkedNoHeaderReceivedAt A x.selfA x.self.uc ∗
        memRegion (x.selfA + 56#64) 400 ∗
        cells (s0.sp - 1648#64) 11 ∗
        polyDecoderAt A ((s0.sp - 1648#64) + 0x58#64) receivingHdr ∗
        optKeyBytesAt A ((s0.sp - 1648#64) + 0x1e8#64) none ∗
        memRegion ((s0.sp - 1648#64) + 0x3e0#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have hmc_raw := hA.session_memcpy_region_ok_at noHeaderReceivedRecvHdrChunkName
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy"))
    polyDecodedMessageStackX (by decide) (by decide)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, memcpy_fnOff])
  have h_mc_dec := (polyDecoderSplit A receivingHdr).memcpy_withStack_inImage_ok
    (by decide) polyDecodedMessageStackX hmc_raw
  have h_mc_st := (chunkedNoHeaderReceivedSplit A { uc := x.self.uc, receiving_hdr := receivingHdr }).memcpy_withStack_inImage_ok
    (by decide) polyDecodedMessageStackX hmc_raw
  unfold tripleRatchetProgAtExt at hpc h_mc_dec h_mc_st ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 180 72
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 968 32
  clear hA hmc_raw
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  refine SepWPp.rw_pre (by
    rw [memRegion_456_at_fsp_3e0_split (s0.sp - 1648#64),
        memRegion_480_outA_split x.outA]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy")) hinv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_mc_dec
    ((s0.sp - 1648#64) + 0x418#64, (s0.sp - 1648#64) + 0x58#64) hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
  rcases hpost1 with ⟨htr1, _⟩
  refine SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy")) hF_sf ?_
  refine SepWP.fold (noHeaderReceivedUcAt_expose_entails A x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold
    (chunkedNoHeaderReceivedAt_fsp_3e0_entails A s0.sp x.self.uc receivingHdr _)
    (by sep_focus) ?_
  refine SepWP.fold
    (noHeaderReceivedCells_entails_memRegion_456 x.selfA _ _ _ _ _ _ _)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_inImage_recvCt2 h_mc_st (x.outA + 8#64, s0.sp - 656#64) hinv2
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost2 => ?_
  rcases hpost2 with ⟨htr2, _⟩
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold
    (optKeyBytesAt_none_entails_memRegion_24 A (s0.sp - 1160#64))
    (by sep_focus) ?_
  unfold savedRegsAt
  wp_steps
  have hfold_saved :
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
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by sep_focus) ?_
  have hfold_active :
      cells (s0.sp - 1648#64) 11 ∗
        memRegion (s0.sp - 1560#64) 400 ∗
        memRegion (s0.sp - 1160#64) 24 ∗
        memRegion (s0.sp - 656#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ⊢
      hdrActiveFrameRegionsAt (s0.sp - 1648#64) := by
    unfold hdrActiveFrameRegionsAt
    have ha1 : (s0.sp - 1648#64) + 0x58#64 = s0.sp - 1560#64 := by bv_omega
    have ha2 : (s0.sp - 1648#64) + 0x1e8#64 = s0.sp - 1160#64 := by bv_omega
    have ha3 : (s0.sp - 1648#64) + 0x3e0#64 = s0.sp - 656#64 := by bv_omega
    rw [ha1, ha2, ha3]
    exact Entails.refl _
  refine SepWP.fold hfold_active (by sep_focus) ?_
  have hstack_eq : stackAt sf.sp polyDecodedMessageStackX ⊢ stackAt (s0.sp - 1648#64) polyDecodedMessageStackX := by
    rw [hsp_sf, hsp]; exact Entails.refl _
  refine SepWP.fold hstack_eq (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvHdrChunk s0) (by sep_focus) ?_
  have hres := recv_hdr_chunk_eq_stillReceiving x.self x.epoch x.chunk receivingHdr hepoch hadd hdec
  unfold recvHdrChunkPostQ
  dsimp only [noHeaderReceivedRecvHdrChunkSpec]
  rw [hres]
  dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt]
  wp_done

/-! ## 4. `Some(hdrFull)` Length Check & `mac` / `hdr` Allocations (`0x612ec .. 0x61394`) -/

theorem ofNat_ult_64_of_lt {n : Nat} (h : n < 64) :
    (BitVec.ofNat 64 n).ult 64#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 64 < 2 ^ 64), decide_eq_true_eq]
  exact h

theorem ofNat_ult_64_of_ge {n : Nat} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).ult 64#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 64 < 2 ^ 64), decide_eq_false_iff_not]
  omega

theorem ofNat_sub_64_eq {n : Nat} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    BitVec.ofNat 64 n - 64#64 = BitVec.ofNat 64 (n - 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n - 64 < 2 ^ 64)]
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    exact hge

theorem ofNat_sub_64_eq_zero_iff {n : Nat} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 (n - 64) == 0#64) = decide (n = 64) := by
  by_cases h : n = 64
  · subst h; decide
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change n - 64 = 0 at h1
    omega

theorem addWithCarry64_sub_64_n (a : BitVec 64) :
    (AddWithCarry64 a 18446744073709551551#64 true).2.n = (a - 64#64).getLsbD 63 := by
  dsimp [AddWithCarry64]
  have htrunc :
      BitVec.setWidth 64 (1#65 + (18446744073709551551#65 + BitVec.setWidth 65 a)) =
        a - 64#64 := by
    bv_kernel
  rw [htrunc, BitVec.msb_eq_getLsbD_last]

theorem vecU8HeapAt_split_64 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hge : 64 ≤ bs.length) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs.take 64) ∗
      ((ptr + 64#64) ↦ₛ bs.drop 64) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0
    have hle0 : bs.length ≤ 0 := hle
    omega
  simp only [hcap_ne, ↓reduceIte]
  have htake_len : (bs.take 64).length = 64 := by rw [List.length_take]; omega
  have happ : bs.take 64 ++ bs.drop 64 = bs := List.take_append_drop 64 bs
  conv_lhs => arg 2; arg 1; rw [← happ, pointsToBytes_append, htake_len]
  refine Entails.pure_right ⟨hle, hmax, hptr_ne, hcap_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

@[simp] theorem ofNat_64_eq : BitVec.ofNat 64 64 = 64#64 := rfl
@[simp] theorem ofNat_64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_alloc_mac_hdr_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hge64 : 64 ≤ hdrFull.length)
    (hlt_max : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 252#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_hdr : BitVec 64),
      ptr_hdr ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 320#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      ImgCallInv img st' →
      st'.readReg64 .x0 = ptr_hdr →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_hdrFull →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st'
        (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
          vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion ptr_hdr 64 ∗
          A.live ptr_hdr 64 1 ∗
          ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
          A.pool ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPostQ img F A x s0 R)
        (recvHdrChunkPostQp F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have h_shim := shim_ok_at_recvHdr hA
  have h_alloc := alloc_ok_at_recvHdr hA
  have h_mc := memcpy_ok_at_recvHdr hA
  have h_pan_oom := panic_at_handle_error_recvHdr img.base ext
  unfold tripleRatchetProgAtExt at hpc h_shim h_alloc h_mc h_pan_oom hcont ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 168 12
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 252 68
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 1000 36
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 1248 16
  clear hA
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hzero_iff := ofNat_sub_64_eq_zero_iff hge64 hlt_max
  have hlay64 : LayoutOk 64 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  by_cases hlen64 : hdrFull.length = 64
  · have hzero : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = true := by
      rw [hzero_iff, decide_eq_true hlen64]
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_inImage_recvCt2 h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "__rustc::__rust_alloc")) hF_sf ?_
    wp_steps
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_inImage_recvCt2 h_alloc (64, 1) hinv2
    by_cases hoom64 : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom64_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
      conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      refine SepWPp.of_sepWP_inImage (mid := entry + 320#64) hF_sf_1 ?_
      wp_steps
      have hdrop0 : (hdrFull.drop 64).length = 0 := by rw [List.length_drop, hlen64]
      have hsub0 : BitVec.ofNat 64 (hdrFull.length - 64) = 0#64 := by rw [hlen64]
      have hvb0 : ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ⊢
          ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
            vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) 1#64 (hdrFull.drop 64) := by
        rw [hsub0]
        refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
        exact sepConj_mono_right (vecBufAt_zero_one A (hdrFull.drop 64) hdrop0)
      refine SepWP.fold hvb0 (by sep_focus) ?_
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
        rw [← hstack_sf, hsp]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv_end
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ 1#64 (sf_1.readReg64 Reg.x0) hoom64
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv_end
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
  · have hzero : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false := by
      rw [hzero_iff, decide_eq_false hlen64]
    have hlay_mac : LayoutOk (hdrFull.length - 64) 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
    have hsub_toNat : (BitVec.ofNat 64 (hdrFull.length - 64)).toNat = hdrFull.length - 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hdrop_len : (hdrFull.drop 64).length = hdrFull.length - 64 := List.length_drop
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_inImage_recvCt2 h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "__rustc::__rust_alloc")) hF_sf ?_
    wp_steps
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_inImage_recvCt2 h_alloc (hdrFull.length - 64, 1) hinv2
    by_cases hoom_mac : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom_mac, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom_mac_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_mac
      conv => arg 4; simp only [hoom_mac, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      refine SepWPp.of_sepWP_inImage
        (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy")) hF_sf_1 ?_
      wp_steps
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
        rw [hsp_sf_1]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      wpp_call_inImage_recvCt2 h_mc (sf_1.readReg64 Reg.x0, ptr_hdrFull + 64#64, hdrFull.drop 64) hinv3
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr3⟩
      have hfold_mac :
          ((sf_1.readReg64 Reg.x0) ↦ₛ hdrFull.drop 64) ∗
            A.live (sf_1.readReg64 Reg.x0) (hdrFull.length - 64) 1 ⊢
          vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64))
            (sf_1.readReg64 Reg.x0) (hdrFull.drop 64) := by
        rw [← hdrop_len]
        exact vecBufAt_of_bytes_live A (sf_1.readReg64 Reg.x0) (hdrFull.drop 64)
          (by omega) (by omega)
      refine SepWPp.of_sepWP_inImage
        (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hF_sf_2 ?_
      refine SepWP.fold hfold_mac (by sep_focus) ?_
      wp_steps
      have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
        rw [hsp_sf_2]
      refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv4
      wpp_call_inImage_recvCt2 h_shim () hinv4
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr4 => ?_
      refine SepWPp.of_sepWP_inImage
        (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
          "__rustc::__rust_alloc")) hF_sf_3 ?_
      wp_steps
      have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
        rw [hsp_sf_3]
      refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv5
      wpp_call_inImage_recvCt2 h_alloc (64, 1) hinv5
      by_cases hoom64 : sf_4.readReg64 Reg.x0 = 0#64
      · conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) fun htr5 => ?_
        apply SepWPp.of_sepWP
          (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
            "alloc::raw_vec::handle_error"))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        exact allowPanic_oom_recvCt2
          (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · have hoom64_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
        conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨_, htr5⟩
        refine SepWPp.of_sepWP_inImage (mid := entry + 320#64) hF_sf_4 ?_
        wp_steps
        have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
          rw [← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf, hsp]
        refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv_end
        refine SepWPp.rw_pre (by ac_rfl)
          (hcont _ (sf_1.readReg64 Reg.x0) (sf_4.readReg64 Reg.x0) hoom64
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            hinv_end
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))

/-! ## 5. `polyDecoderNew1152` Initialization & `hdr` Copy (`0x61394 .. 0x61488`) -/

theorem savedRegsAt_of_cells12_hdr (s0 : State) :
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
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 :=
  Entails.refl _

theorem cells11_sp_1648_expand (sp : BitVec 64) :
    cells (sp - 1648#64) 11 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64,
        ((sp - 1648#64) ↦₆₄ c0) ∗ ((sp - 1640#64) ↦₆₄ c1) ∗
        ((sp - 1632#64) ↦₆₄ c2) ∗ ((sp - 1624#64) ↦₆₄ c3) ∗
        ((sp - 1616#64) ↦₆₄ c4) ∗ ((sp - 1608#64) ↦₆₄ c5) ∗
        ((sp - 1600#64) ↦₆₄ c6) ∗ ((sp - 1592#64) ↦₆₄ c7) ∗
        ((sp - 1584#64) ↦₆₄ c8) ∗ ((sp - 1576#64) ↦₆₄ c9) ∗
        ((sp - 1568#64) ↦₆₄ c10)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

theorem cells11_sp_1648_fold (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : BitVec 64) :
    ((sp - 1648#64) ↦₆₄ c0) ∗ ((sp - 1640#64) ↦₆₄ c1) ∗
      ((sp - 1632#64) ↦₆₄ c2) ∗ ((sp - 1624#64) ↦₆₄ c3) ∗
      ((sp - 1616#64) ↦₆₄ c4) ∗ ((sp - 1608#64) ↦₆₄ c5) ∗
      ((sp - 1600#64) ↦₆₄ c6) ∗ ((sp - 1592#64) ↦₆₄ c7) ∗
      ((sp - 1584#64) ↦₆₄ c8) ∗ ((sp - 1576#64) ↦₆₄ c9) ∗
      ((sp - 1568#64) ↦₆₄ c10) ⊢ cells (sp - 1648#64) 11 := by
  rw [cells11_sp_1648_expand sp]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
        (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.refl _)))))))))))

theorem optKeyBytesAt_none_sp_1160 (A : RustAlloc) (sp : BitVec 64) :
    optKeyBytesAt A (sp - 1160#64) none =
      ((sp - 1160#64) ↦₆₄ noneCap) ∗ memRegion (sp - 1152#64) 16 := by
  unfold optKeyBytesAt
  have h2 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  rw [h2]

theorem optKeyBytesAt_some_sp_1160 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    optKeyBytesAt A (sp - 1160#64) (some bs) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 1160#64) ↦₆₄ cap) ∗
        ((sp - 1152#64) ↦₆₄ ptr) ∗
        ((sp - 1144#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  have h2 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  have h3 : (sp - 1160#64) + 16#64 = sp - 1144#64 := by bv_omega
  have hexp := optKeyBytesAt_some_expose A (sp - 1160#64) bs
  rw [h2, h3] at hexp
  exact hexp

theorem memRegion_24_of_sp_1160 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 1160#64) ↦₆₄ v0) ∗ ((sp - 1152#64) ↦₆₄ v1) ∗ ((sp - 1144#64) ↦₆₄ v2) ⊢
      memRegion (sp - 1160#64) 24 := by
  have h2 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  have h3 : (sp - 1160#64) + 16#64 = sp - 1144#64 := by bv_omega
  rw [memRegion_24_cells (sp - 1160#64), h2, h3]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.refl _)))

theorem fold_none_addrs_sp_hdr (A : RustAlloc) (sp : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A (sp - 1560#64) dec ∗
      ((sp - 1160#64) ↦₆₄ noneCap) ∗ memRegion (sp - 1152#64) 16 ∗
      memRegion (sp - 656#64) 456 ⊢
    polyDecoderAt A ((sp - 1648#64) + 0x58#64) dec ∗
      optKeyBytesAt A ((sp - 1648#64) + 0x1e8#64) none ∗
      memRegion ((sp - 1648#64) + 0x3e0#64) 456 := by
  dsimp only [optKeyBytesAt]
  have h1 : (sp - 1648#64) + 0x58#64 = sp - 1560#64 := by bv_omega
  have h2 : (sp - 1648#64) + 0x1e8#64 = sp - 1160#64 := by bv_omega
  have h3 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  have h4 : (sp - 1648#64) + 0x3e0#64 = sp - 656#64 := by bv_omega
  rw [h1, h2, h3, h4]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
