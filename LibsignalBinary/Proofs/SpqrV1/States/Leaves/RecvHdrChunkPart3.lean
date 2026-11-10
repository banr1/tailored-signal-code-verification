/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 3 (`0x61488 .. 0x6150c`)

**Checked by Lean.** Verifies `recv_hdr_chunk_hmac_wpp` (offsets `564 .. 696`): `sliceConcat3`,
`libcrux_hmac`, and `ct_mac_data` deallocation.
-/

@[expose] public section

set_option autoImplicit false

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
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout
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
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length MacHdrFacts.hdrLabel_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  noHeaderReceivedRecvHdrChunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff
  sliceConcat_fnOff
  shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff
  assertFailedU64_fnOff sliceIndexFail_fnOff
  panicBoundsCheck_fnOff
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
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")

/-! ## 1. `sliceConcat3`, `libcrux_hmac`, and `ct_mac_data` Dealloc (`0x61488 .. 0x6150c`, offsets `564 .. 696`) -/

theorem bytes_rem_entails_memRegion_hdr (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat + 1 ≤ 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem page_align_mask_hdr {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    b &&& 18446744073709547520#64 = b := by
  have hb : (b &&& 18446744073709547520#64) + (b &&& 4095#64) = b := by bv_kernel
  rw [halign, BitVec.add_zero] at hb
  exact hb

theorem adrp_hdrLabel {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    (((b + bv% (ls_off% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk")) + 564#64 &&& 18446744073709547520#64) + bv% (ls_xref% 0x5c090 - 0x5c000)) + bv% ((ls_xref% 0x5c090 0x5c094) % 4096) =
      b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader") := by
  rw [← page_align_mask_hdr halign]; bv_kernel

/-- `adrp_hdrLabel` with the `adrp` page offset and `add` immediate folded. -/
theorem adrp_hdrLabel_folded {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    ((b + bv% (ls_off% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk")) + 564#64 &&& 18446744073709547520#64) + bv% (ls_xref% 0x5c090 - 0x5c000 + (ls_xref% 0x5c090 0x5c094) % 4096) =
      b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader") := by
  rw [← page_align_mask_hdr halign]; bv_kernel

theorem verifyHdrError_of_key_ge_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch)
    (hdr mac : Bytes) (hk : 2 ^ 32 ≤ auth.macKey.length) :
    auth.verifyHdrError F ep hdr mac = .error hmacU32UnwrapPanic := by
  have hnot : ¬ (auth.macKey.length < 2 ^ 32 ∧
      (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32) := by
    omega
  simp only [Authenticator.verifyHdrError, Authenticator.verifyHdr, Authenticator.macHdr, hnot,
    ↓reduceIte, Bind.bind, Except.bind, Except.map]

theorem recv_hdr_chunk_isPanic_of_macKey_ge_32 {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge : 64 ≤ hdrFull.length)
    (hk : 2 ^ 32 ≤ self.uc.auth.macKey.length) :
    (self.recv_hdr_chunk epoch chunk).isPanic = true := by
  have hafter := recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull
    hepoch hadd hdec (by omega)
  dsimp only at hafter
  have herr := verifyHdrError_of_key_ge_32 F self.uc.auth self.uc.epoch
    (hdrFull.take 64) (hdrFull.drop 64) hk
  rw [hafter, herr]
  rfl

/-- Call-site specialized `libcrux_hmac::hmac` specification for `recv_hdr_chunk` where
    `2 ^ 32 ≤ x.key.length` implies `P` (`isPanic = true`). -/
def libcruxHmacHdrSpec (s0_top : State) (P : Prop) (F : ShaCompress) (A : RustAlloc) :
    Spec LibcruxHmacCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      s.trace = s0_top.trace ∧
      (2 ^ 32 ≤ x.key.length → P) ∧ x.data.length < 2 ^ 32⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜x.key.length < 2 ^ 32 ∧ sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A x.ret (hmacWith F x.key x.data) ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf =>
    ⌜(P ∨ allocFailedIn s0_top sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem libcrux_hmac_hdr_ok_at_recvHdr {s0_top : State} {P : Prop} {img : Obj.Image}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "libcrux_hmac::hmac"))
      ((libcruxHmacHdrSpec s0_top P F A).inImage img) := by
  have hraw := libcrux_hmac_ok_at_recvHdr (img := img) hhmac
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, libcruxHmacHdrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, htr_eq, hk_imp, hd_lt⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((libcruxHmacSpec F A).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  refine (hraw.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, libcruxHmacSpec, libcruxHmacHdrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hpost.1.2.2⟩, hpost.2⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, libcruxHmacSpec, libcruxHmacHdrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨haf | hk_ge | hd_ge, hpref⟩, hmem'⟩
    · unfold allocFailedIn at haf ⊢
      rw [htr_eq] at haf
      exact ⟨⟨Or.inr haf, hpref⟩, hmem'⟩
    · exact ⟨⟨Or.inl (hk_imp hk_ge), hpref⟩, hmem'⟩
    · omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem onPanic_or_alloc_entails_recvHdr {Q : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜Q ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜Q ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem authenticatorHeapAt_expose_macKey (A : RustAlloc) (g : AuthenticatorGhost)
    (auth : Authenticator) :
    authenticatorHeapAt A g auth ⊢
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) := by
  unfold authenticatorHeapAt vecU8HeapAt
  rw [show ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
        (if g.rootKey.cap = 0 then emp
         else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
           memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
        ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) =
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        ((if g.macKey.cap = 0 then emp
          else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ∗
         (⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
           (if g.rootKey.cap = 0 then emp
            else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
              memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : g.macKey.cap = 0
  · have hle0 : auth.macKey.length ≤ (0 : BitVec 64).toNat := hcap ▸ hle
    have hbs : auth.macKey = [] := List.eq_nil_of_length_eq_zero (by change auth.macKey.length ≤ 0 at hle0; omega)
    rw [hbs]
    simp only [hcap, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem authenticatorHeapAt_unexpose_macKey (A : RustAlloc) (g : AuthenticatorGhost)
    (auth : Authenticator)
    (hle : auth.macKey.length ≤ g.macKey.cap.toNat)
    (hlt : g.macKey.cap.toNat < 2 ^ 63)
    (hptr : g.macKey.ptr ≠ 0) :
    (g.macKey.ptr ↦ₛ auth.macKey) ∗
      vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
      (if g.macKey.cap = 0 then emp
       else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
         memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ⊢
      authenticatorHeapAt A g auth := by
  unfold authenticatorHeapAt vecU8HeapAt
  rw [show ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
        (if g.rootKey.cap = 0 then emp
         else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
           memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
        ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) =
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        ((if g.macKey.cap = 0 then emp
          else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ∗
         (⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
           (if g.rootKey.cap = 0 then emp
            else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
              memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)))) by ac_rfl]
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : g.macKey.cap = 0
  · have hle0 : auth.macKey.length ≤ (0 : BitVec 64).toNat := hcap ▸ hle
    have hbs : auth.macKey = [] := List.eq_nil_of_length_eq_zero (by change auth.macKey.length ≤ 0 at hle0; omega)
    rw [hbs]
    simp only [hcap, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem memRegion_48_sp_168_cells (sp : BitVec 64) :
    memRegion (sp - 168#64) 48 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗
        ((sp - 152#64) ↦₆₄ s2) ∗ ((sp - 144#64) ↦₆₄ s3) ∗
        ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5)) := by
  change memRegion (sp - 168#64) (8 * 6) = _
  rw [ProofLib.memRegion_cells (sp - 168#64) 6 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

theorem fold_sp_168_24_24 (sp s0 s1 s2 s3 s4 s5 : BitVec 64) :
    ((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗ ((sp - 152#64) ↦₆₄ s2) ∗
      ((sp - 144#64) ↦₆₄ s3) ∗ ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5) ⊢
      memRegion (sp - 168#64) 24 ∗ memRegion (sp - 144#64) 24 := by
  have h1 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h2 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  have h3 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h4 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [memRegion_24_cells (sp - 168#64), memRegion_24_cells (sp - 144#64), h1, h2, h3, h4]
  have hassoc :
      ((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗ ((sp - 152#64) ↦₆₄ s2) ∗
        ((sp - 144#64) ↦₆₄ s3) ∗ ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5) =
      (((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗ ((sp - 152#64) ↦₆₄ s2)) ∗
        (((sp - 144#64) ↦₆₄ s3) ∗ ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5)) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono
    (Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.sepExists_right s2 (Entails.refl _))))
    (Entails.sepExists_right s3 (Entails.sepExists_right s4 (Entails.sepExists_right s5 (Entails.refl _))))

theorem vecU8_expose_nonempty_192 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 192#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 192#64) ↦₆₄ cap) ∗
          ((sp - 184#64) ↦₆₄ ptr) ∗
          ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 192#64) cap ptr bs]
  have h8 : (sp - 192#64) + 8#64 = sp - 184#64 := by bv_omega
  have h16 : (sp - 192#64) + 16#64 = sp - 176#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 192#64) ↦₆₄ cap) ∗ ((sp - 184#64) ↦₆₄ ptr) ∗
        ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 192#64) ↦₆₄ cap) ∗ ((sp - 184#64) ↦₆₄ ptr) ∗
        ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem memRegion_24_of_sp_192 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ⊢
      memRegion (sp - 192#64) 24 := by
  have h1 : (sp - 192#64) + 8#64 = sp - 184#64 := by bv_omega
  have h2 : (sp - 192#64) + 16#64 = sp - 176#64 := by bv_omega
  rw [memRegion_24_cells (sp - 192#64), h1, h2]
  exact Entails.sepExists_right v0
    (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))

theorem macHdrUnchecked_eq_hmacWith_hdr (F : ShaCompress)
    (auth : Authenticator) (ep : Epoch) (hdr : Bytes) :
    auth.macHdrUnchecked F ep hdr =
      hmacWith F auth.macKey (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr) := by
  unfold Authenticator.macHdrUnchecked
  exact hmacWith_take_macSize F _ _

attribute [local irreducible] Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_hmac_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A))
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (halign : img.base &&& 4095#64 = 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 564#64)
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
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx25 : st.readReg64 .x25 = ptr_hdr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      x.self.uc.auth.macKey.length < 2 ^ 32 →
      st'.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 696#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      ImgCallInv img st' →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = BitVec.ofNat 64 x.self.uc.auth.macKey.length →
      st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x25 = ptr_hdr →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st'.readReg64 .x27 = g_auth0.macKey.ptr →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st'
        (recvHdrChunkRoAt img ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          vecU8 A (s0.sp - 168#64) (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
          memRegion (s0.sp - 144#64) 24 ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          A.pool ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPostQ img F A x s0 R)
        (recvHdrChunkPostQp F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
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
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have h_concat3 := sliceConcat3_ok_at_recvHdr hconcat3
  have h_hmac := libcrux_hmac_hdr_ok_at_recvHdr (s0_top := s0)
    (P := (x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true) (img := img) hhmac
  have h_dealloc := dealloc_ok_at_recvHdr hA
  have hadrp_hdr := adrp_hdrLabel halign
  have hadrp_hdr' := adrp_hdrLabel_folded halign
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx29
  unfold tripleRatchetProgAtExt at hpc h_concat3 h_hmac h_dealloc hcont ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 564 132
  have hfn_eq : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = img.base + bv% (ls_off% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk") := by
    rw [Program.fnAddr_rebase, noHeaderReceivedRecvHdrChunk_fnOff]
  rw [← hfn_eq] at hadrp_hdr hadrp_hdr'
  clear hA hconcat3 hhmac hfn_eq
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have htake64_len : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  have htake64_bv : BitVec.ofNat 64 (hdrFull.take 64).length = 64#64 := by rw [htake64_len]
  have hconcat3_bound : 41 + (hdrFull.take 64).length < 9223372036854775808 := by
    rw [htake64_len]; decide
  refine SepWPp.fold
    (authenticatorHeapAt_expose_macKey A g_auth0 x.self.uc.auth)
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ptr_ne⟩
  have hmk_toNat : (BitVec.ofNat 64 x.self.uc.auth.macKey.length).toNat = x.self.uc.auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.rw_pre (by
    rw [memRegion_48_sp_168_cells s0.sp,
        ProofLib.memRegion_eight (s0.sp - 120#64)]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")) hinv ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq ((congrArg (fun e => (s0.sp - 120#64) ↦₆₄ rev64 e) hepoch.symm).trans
      (pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) x.epoch)))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_recvCt2 h_concat3
    (⟨s0.sp - 192#64, s0.sp - 168#64,
      true, img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader"), Authenticator.hdrLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.epoch,
      false, ptr_hdr, hdrFull.take 64⟩ : SliceConcat3Ghost)
    hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  rw [← List.append_assoc Authenticator.hdrLabel]
  have hdata_len :
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length = 105 := by
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake64_len]
  have hdata_pos :
      0 < (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length := by
    omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_192 A s0.sp
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)
      hdata_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_false_of_ne hcap_md_ne
  refine SepWPp.fold
    (fold_sp_168_24_24 s0.sp
      (img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader")) 33#64
      (s0.sp - 120#64) 8#64 ptr_hdr
      (BitVec.ofNat 64 (hdrFull.take 64).length))
    (by sep_focus) ?_
  have hbe_mr : ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.epoch) ⊢ memRegion (s0.sp - 120#64) 8 := by
    have hbe8 : (toBEBytes 8 x.epoch).length = 8 := toBEBytes_8_length x.epoch
    exact hbe8 ▸ pointsToBytes_entails_memRegion (s0.sp - 120#64) (toBEBytes 8 x.epoch)
  refine SepWPp.fold hbe_mr (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "libcrux_hmac::hmac")) hF_sf ?_
  wp_steps
  have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
    rw [hsp_sf]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  have hdata_lt32 :
      (Authenticator.hdrLabel ++ (toBEBytes 8 x.epoch ++ hdrFull.take 64)).length < 4294967296 := by
    rw [← List.append_assoc Authenticator.hdrLabel, hdata_len]
    decide
  have hmk_panic : 4294967296 ≤ x.self.uc.auth.macKey.length →
      (x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true :=
    recv_hdr_chunk_isPanic_of_macKey_ge_32 x.self x.epoch x.chunk receivingHdr hdrFull
      hepoch hadd hdec hge64
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  apply (MacHdrFacts.SepWPp.call_allowPanic_inImage_mid h_hmac
    (x := (⟨s0.sp - 168#64, g_auth0.macKey.ptr, x.self.uc.auth.macKey,
      ptr_md, Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64⟩ : LibcruxHmacCall))
    (F := recvHdrChunkRoAt img ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗
      vecU8HeapAt A g_auth0.rootKey.cap g_auth0.rootKey.ptr x.self.uc.auth.rootKey ∗
      (if g_auth0.macKey.cap = 0 then emp
       else A.live g_auth0.macKey.ptr g_auth0.macKey.cap.toNat 1 ∗
         memRegion (g_auth0.macKey.ptr + BitVec.ofNat 64 x.self.uc.auth.macKey.length)
           (g_auth0.macKey.cap.toNat - x.self.uc.auth.macKey.length)) ∗
      ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
      ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      memRegion (s0.sp - 144#64) 24 ∗
      ((s0.sp - 192#64) ↦₆₄ cap_md) ∗
      ((s0.sp - 184#64) ↦₆₄ ptr_md) ∗
      ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length) ∗
      A.live ptr_md cap_md.toNat 1 ∗
      memRegion (ptr_md + BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length)
        (cap_md.toNat - (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length) ∗
      memRegion (s0.sp - 120#64) 8 ∗
      F_frame)
    hinv2)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [libcruxHmacHdrSpec] at _hmR' ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by rw [← List.append_assoc Authenticator.hdrLabel, ← hepoch, hdata_len]; rfl,
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             hmk_panic,
             by rw [List.append_assoc Authenticator.hdrLabel]; exact hdata_lt32⟩, ?_⟩
    dsimp only [recvHdrChunkRoAt]
    simp only [wp_norm, arm64_norm]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) _hmR'
  · intro _
    dsimp only [libcruxHmacHdrSpec]
    exact onPanic_or_alloc_entails_recvHdr (by wp_norm_lhs)
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf_1 hpc_sf_1 hrun_sf_1 hsp_sf_1 hcs_sf_1 hF_sf_1
  dsimp only [libcruxHmacHdrSpec]
  simp only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hsp_sf_1 hcs_sf_1
  rcases hcs_sf_1 with ⟨hx19_sf_1, hx20_sf_1, hx21_sf_1, hx22_sf_1, hx23_sf_1,
    hx24_sf_1, hx25_sf_1, hx26_sf_1, hx27_sf_1, hx28_sf_1, hx29_sf_1, hvregs_sf_1⟩
  conv => arg 4; simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf_1]
  refine SepWPp.pure_left_focus
    (x.self.uc.auth.macKey.length < 2 ^ 32 ∧ sf_1.trace = sf.trace)
    (by sep_focus) ?_
  rintro ⟨hmk_lt32, htr2⟩
  rw [← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith_hdr F x.self.uc.auth x.epoch (hdrFull.take 64)]
  refine SepWPp.fold
    (authenticatorHeapAt_unexpose_macKey A g_auth0 x.self.uc.auth hmk_le hmk_max hmk_ptr_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (bytes_rem_entails_memRegion_hdr ptr_md cap_md
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)
      hle_md hmax_md)
    (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "__rustc::__rust_dealloc")) hF_sf_1 ?_
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [hsp_sf_1]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_inImage_recvCt2 h_dealloc (ptr_md, cap_md.toNat, 1) hinv3
  refine SepWPp.pure_left_focus (sf_2.trace = sf_1.trace) (by sep_focus) fun htr3 => ?_
  have hstack_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp_sf_1, hsp_sf, hsp]
  refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  refine SepWPp.fold
    (memRegion_24_of_sp_192 s0.sp cap_md ptr_md
      (BitVec.ofNat 64 (Authenticator.hdrLabel ++ (toBEBytes 8 x.epoch ++ hdrFull.take 64)).length))
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by dsimp only [recvHdrChunkRoAt]; ac_rfl)
    (hcont sf_2 hmk_lt32
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
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
