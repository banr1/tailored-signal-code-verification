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
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 2 (`0x61254 .. 0x61488`)

**Checked by Lean.** Verifies `polyDecoderNew1152` initialization and `hdr` copy
(`recv_hdr_chunk_init_dec_wpp`, offsets `320 .. 564`) and assembles the combined entry prefix
`recv_hdr_chunk_part1_wpp` (offsets `0 .. 564`).
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
  bytesAt_true bytesAt_false toBEBytes_8_length
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
  (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
  (ls_lemma% fnOff "spqr::util::is_non_zero")
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

/-! ## 1. `polyDecoderNew1152` Initialization & `hdr` Copy (`0x61394 .. 0x61488`) -/

theorem exists_unpack64_of_length_64_hdr {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) := by
  have h1 : (bs.take 32).length = 32 := by rw [List.length_take]; omega
  have h2 : (bs.drop 32).length = 32 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, _, ha1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w4, w5, w6, w7, _, ha2⟩ := exists_unpack64_of_length_32 h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  conv_lhs => rw [← List.take_append_drop 32 bs, pointsToBytes_append, h1]
  rw [ha1 a, ha2 (a + 32#64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion_64_cells_hdr (a : BitVec 64) :
    memRegion a 64 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7)) := by
  rw [ProofLib.memRegion_cells a 8 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem ct2DeallocAt_of_cells64_drop (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (hge : 64 ≤ bs.length) (hle : bs.length ≤ cap.toNat)
    (hmax : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
      ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3) ∗
      ((ptr + 32#64) ↦₆₄ w4) ∗ ((ptr + 40#64) ↦₆₄ w5) ∗
      ((ptr + 48#64) ↦₆₄ w6) ∗ ((ptr + 56#64) ↦₆₄ w7)) ∗
      ((ptr + 64#64) ↦ₛ bs.drop 64) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 ⊢
    ct2DeallocAt A cap ptr := by
  have h64 :
      ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
        ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3) ∗
        ((ptr + 32#64) ↦₆₄ w4) ∗ ((ptr + 40#64) ↦₆₄ w5) ∗
        ((ptr + 48#64) ↦₆₄ w6) ∗ ((ptr + 56#64) ↦₆₄ w7)) ⊢
      memRegion ptr 64 := by
    rw [memRegion_64_cells_hdr ptr]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
        (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.refl _))))))))
  have hdrop : ((ptr + 64#64) ↦ₛ bs.drop 64) ⊢ memRegion (ptr + 64#64) (bs.length - 64) := by
    have hlen : (bs.drop 64).length = bs.length - 64 := List.length_drop
    rw [← hlen]
    exact pointsToBytes_entails_memRegion (ptr + 64#64) (bs.drop 64)
  refine Entails.trans (sepConj_mono h64 (sepConj_mono_left hdrop)) ?_
  dsimp only [ct2DeallocAt]
  refine Entails.pure_right ⟨hcap, hmax, hptr⟩ ?_
  have hsplit1 : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)
  have hsplit2 : memRegion ptr bs.length =
      memRegion ptr 64 ∗ memRegion (ptr + 64#64) (bs.length - 64) :=
    ProofLib.memRegion_split' (b := ptr) (n := 64) (k := bs.length - 64)
      (b' := ptr + 64#64) (by omega) rfl (by omega)
  rw [hsplit1, hsplit2]
  exact Entails.of_eq (by ac_rfl)

theorem byte_1_entails_exists (a : BitVec 64) :
    memRegion a 1 ⊢ (∃∗ b0 : BitVec 8, a ↦₈ b0) := by
  rw [memRegion_eq_exists_bytes a 1 (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  rcases bs with _ | ⟨b0, _ | _⟩
  · simp at hlen
  · refine Entails.sepExists_right b0 ?_
    simp [pointsToBytes_cons, pointsToBytes_nil]
    exact Entails.refl _
  · simp at hlen

theorem three_words_entails_sortedSetPtOf_new (A : RustAlloc) (b : BitVec 64) :
    (b ↦₆₄ 0#64) ∗ ((b + 8#64) ↦₆₄ 2#64) ∗ ((b + 16#64) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A b SortedSetPt.new := by
  unfold sortedSetPtOf SortedSetPt.new vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl)), sepConj_emp]
  have hpure : ([] : List Pt).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * ptStride < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  refine Entails.trans (Entails.pure_right hpure (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem sortedSetPtOf_new_sp (A : RustAlloc) (sp off0 off1 off2 : BitVec 64)
    (h1 : (sp - off0) + 8#64 = sp - off1)
    (h2 : (sp - off0) + 16#64 = sp - off2) :
    ((sp - off0) ↦₆₄ 0#64) ∗ ((sp - off1) ↦₆₄ 2#64) ∗ ((sp - off2) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A (sp - off0) SortedSetPt.new := by
  rw [← h1, ← h2]
  exact three_words_entails_sortedSetPtOf_new A (sp - off0)

def polyDecoderNew1152RawAt (A : RustAlloc) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 2#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
    sortedSetPtListOf A (a + 24#64) (List.replicate 15 SortedSetPt.new) ∗
    ((a + 384#64) ↦₆₄ 576#64) ∗
    ((a + 392#64) ↦₈ 0#8) ∗
    memRegion (a + 393#64) 7

theorem polyDecoderNew1152RawAt_entails_polyDecoderAt (A : RustAlloc) (a : BitVec 64) :
    polyDecoderNew1152RawAt A a ⊢ polyDecoderAt A a polyDecoderNew1152 := by
  unfold polyDecoderNew1152RawAt polyDecoderAt polyDecoderNew1152
  have hpure : (List.replicate 16 SortedSetPt.new).length = NUM_POLYS ∧ 576 < 2 ^ 64 :=
    ⟨rfl, by decide⟩
  refine Entails.pure_right hpure ?_
  dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff,
    polyDecoderPadSize, boolByte, NUM_POLYS, CHUNK_SIZE, sortedSetPtListOf,
    Poly.vecHeaderBytes]
  rw [show (if false = true then (1#8 : BitVec 8) else 0#8) = 0#8 from rfl]
  have h16 : List.replicate 16 SortedSetPt.new = SortedSetPt.new :: List.replicate 15 SortedSetPt.new := rfl
  rw [h16]
  dsimp only [arrayAt]
  rw [← sepConj_assoc, ← sepConj_assoc]
  have hslot0 :
      ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 2#64)) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
        sortedSetPtOf A a SortedSetPt.new := by
    rw [sepConj_assoc]
    exact three_words_entails_sortedSetPtOf_new A a
  refine Entails.trans (sepConj_mono_left hslot0) ?_
  exact Entails.of_eq (by ac_rfl)

theorem polyDecoderNew1152Raw_of_slots (A : RustAlloc) (sp : BitVec 64) :
    ((sp - 1136#64) ↦₆₄ 0#64) ∗
      ((sp - 1128#64) ↦₆₄ 2#64) ∗
      ((sp - 1120#64) ↦₆₄ 0#64) ∗
      sortedSetPtOf A (sp - 1112#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1088#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1064#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1040#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1016#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 992#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 968#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 944#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 920#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 896#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 872#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 848#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 824#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 800#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 776#64) SortedSetPt.new ∗
      ((sp - 752#64) ↦₆₄ 576#64) ∗
      ((sp - 744#64) ↦₈ 0#8) ∗
      memRegion (sp - 743#64) 7 ⊢
    polyDecoderNew1152RawAt A (sp - 1136#64) := by
  unfold polyDecoderNew1152RawAt sortedSetPtListOf
  dsimp only [Poly.vecHeaderBytes]
  simp only [List.replicate, arrayAt, wp_norm, arm64_norm, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_128_sp_1136 (sp : BitVec 64) :
    memRegion (sp - 1136#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 1136#64) ↦₆₄ v0) ∗ ((sp - 1128#64) ↦₆₄ v1) ∗ ((sp - 1120#64) ↦₆₄ v2) ∗ ((sp - 1112#64) ↦₆₄ v3) ∗
        ((sp - 1104#64) ↦₆₄ v4) ∗ ((sp - 1096#64) ↦₆₄ v5) ∗ ((sp - 1088#64) ↦₆₄ v6) ∗ ((sp - 1080#64) ↦₆₄ v7) ∗
        ((sp - 1072#64) ↦₆₄ v8) ∗ ((sp - 1064#64) ↦₆₄ v9) ∗ ((sp - 1056#64) ↦₆₄ v10) ∗ ((sp - 1048#64) ↦₆₄ v11) ∗
        ((sp - 1040#64) ↦₆₄ v12) ∗ ((sp - 1032#64) ↦₆₄ v13) ∗ ((sp - 1024#64) ↦₆₄ v14) ∗ ((sp - 1016#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 1136#64)]
  simp only [wp_norm, arm64_norm]

theorem memRegion_128_sp_1008 (sp : BitVec 64) :
    memRegion (sp - 1008#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 1008#64) ↦₆₄ v0) ∗ ((sp - 1000#64) ↦₆₄ v1) ∗ ((sp - 992#64) ↦₆₄ v2) ∗ ((sp - 984#64) ↦₆₄ v3) ∗
        ((sp - 976#64) ↦₆₄ v4) ∗ ((sp - 968#64) ↦₆₄ v5) ∗ ((sp - 960#64) ↦₆₄ v6) ∗ ((sp - 952#64) ↦₆₄ v7) ∗
        ((sp - 944#64) ↦₆₄ v8) ∗ ((sp - 936#64) ↦₆₄ v9) ∗ ((sp - 928#64) ↦₆₄ v10) ∗ ((sp - 920#64) ↦₆₄ v11) ∗
        ((sp - 912#64) ↦₆₄ v12) ∗ ((sp - 904#64) ↦₆₄ v13) ∗ ((sp - 896#64) ↦₆₄ v14) ∗ ((sp - 888#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 1008#64)]
  simp only [wp_norm, arm64_norm]

theorem memRegion_128_sp_880 (sp : BitVec 64) :
    memRegion (sp - 880#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 880#64) ↦₆₄ v0) ∗ ((sp - 872#64) ↦₆₄ v1) ∗ ((sp - 864#64) ↦₆₄ v2) ∗ ((sp - 856#64) ↦₆₄ v3) ∗
        ((sp - 848#64) ↦₆₄ v4) ∗ ((sp - 840#64) ↦₆₄ v5) ∗ ((sp - 832#64) ↦₆₄ v6) ∗ ((sp - 824#64) ↦₆₄ v7) ∗
        ((sp - 816#64) ↦₆₄ v8) ∗ ((sp - 808#64) ↦₆₄ v9) ∗ ((sp - 800#64) ↦₆₄ v10) ∗ ((sp - 792#64) ↦₆₄ v11) ∗
        ((sp - 784#64) ↦₆₄ v12) ∗ ((sp - 776#64) ↦₆₄ v13) ∗ ((sp - 768#64) ↦₆₄ v14) ∗ ((sp - 760#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 880#64)]
  simp only [wp_norm, arm64_norm]

theorem hdrSomeBranchFrameAt_expose (sp : BitVec 64) :
    hdrSomeBranchFrameAt (sp - 1648#64) ⊢
      memRegion (sp - 1136#64) 128 ∗
      memRegion (sp - 1008#64) 128 ∗
      memRegion (sp - 880#64) 128 ∗
      (∃∗ v : BitVec 64, (sp - 752#64) ↦₆₄ v) ∗
      (∃∗ b744 : BitVec 8, (sp - 744#64) ↦₈ b744) ∗
      memRegion (sp - 743#64) 7 ∗
      memRegion (sp - 736#64) 80 ∗
      (∃∗ v : BitVec 64, (sp - 200#64) ↦₆₄ v) ∗
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 168#64) 48 ∗
      memRegion (sp - 120#64) 8 ∗
      memRegion (sp - 112#64) 16 := by
  unfold hdrSomeBranchFrameAt
  have h1 : (sp - 1648#64) + 0x200#64 = sp - 1136#64 := by bv_omega
  have h2 : (sp - 1648#64) + 0x390#64 = sp - 736#64 := by bv_omega
  have h3 : (sp - 1648#64) + 0x5a8#64 = sp - 200#64 := by bv_omega
  have h4 : (sp - 1648#64) + 0x5b0#64 = sp - 192#64 := by bv_omega
  have h5 : (sp - 1648#64) + 0x5c8#64 = sp - 168#64 := by bv_omega
  have h6 : (sp - 1648#64) + 0x5f8#64 = sp - 120#64 := by bv_omega
  have h7 : (sp - 1648#64) + 0x600#64 = sp - 112#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7,
      ProofLib.memRegion_split' (b := sp - 1136#64) (n := 128) (k := 272)
        (b' := sp - 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1008#64) (n := 128) (k := 144)
        (b' := sp - 880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 880#64) (n := 128) (k := 16)
        (b' := sp - 752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 752#64) (n := 8) (k := 8)
        (b' := sp - 744#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 744#64) (n := 1) (k := 7)
        (b' := sp - 743#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 752#64),
      ProofLib.memRegion_eight (sp - 200#64)]
  have hcomm :
      memRegion (sp - 1136#64) 128 ∗
        memRegion (sp - 1008#64) 128 ∗
        memRegion (sp - 880#64) 128 ∗
        (∃∗ v : BitVec 64, (sp - 752#64) ↦₆₄ v) ∗
        memRegion (sp - 744#64) 1 ∗
        memRegion (sp - 743#64) 7 ∗
        memRegion (sp - 736#64) 80 ∗
        (∃∗ v : BitVec 64, (sp - 200#64) ↦₆₄ v) ∗
        memRegion (sp - 192#64) 24 ∗
        memRegion (sp - 168#64) 48 ∗
        memRegion (sp - 120#64) 8 ∗
        memRegion (sp - 112#64) 16 =
      memRegion (sp - 744#64) 1 ∗
        (memRegion (sp - 1136#64) 128 ∗
          memRegion (sp - 1008#64) 128 ∗
          memRegion (sp - 880#64) 128 ∗
          (∃∗ v : BitVec 64, (sp - 752#64) ↦₆₄ v) ∗
          memRegion (sp - 743#64) 7 ∗
          memRegion (sp - 736#64) 80 ∗
          (∃∗ v : BitVec 64, (sp - 200#64) ↦₆₄ v) ∗
          memRegion (sp - 192#64) 24 ∗
          memRegion (sp - 168#64) 48 ∗
          memRegion (sp - 120#64) 8 ∗
          memRegion (sp - 112#64) 16) := by ac_rfl
  simp only [sepConj_assoc]
  rw [hcomm]
  refine Entails.trans (sepConj_mono_left (byte_1_entails_exists (sp - 744#64))) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_init_dec_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hge64 : 64 ≤ hdrFull.length)
    (hle_cap : hdrFull.length ≤ cap_hdrFull.toNat)
    (hmax_cap : cap_hdrFull.toNat < 2 ^ 63)
    (hptr_hdrFull : ptr_hdrFull ≠ 0#64)
    (hcap_hdrFull : cap_hdrFull ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 320#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : ImgCallInv img st)
    (hx0 : st.readReg64 .x0 = ptr_hdr)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State),
      st2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st2
        (ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          F_frame)
        (recvHdrChunkPostQ img F A x s0 R)
        (recvHdrChunkPostQp F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st
      ((ptr_hdrFull ↦ₛ hdrFull.take 64) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        memRegion (ptr_hdrFull + BitVec.ofNat 64 hdrFull.length) (cap_hdrFull.toNat - hdrFull.length) ∗
        A.live ptr_hdrFull cap_hdrFull.toNat 1 ∗
        memRegion ptr_hdr 64 ∗
        A.live ptr_hdr 64 1 ∗
        ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        F_frame)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx29
  unfold tripleRatchetProgAtExt at hpc hcont ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 320 244
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have htake64_len : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, ha_hdr⟩ :=
    exists_unpack64_of_length_64_hdr htake64_len
  have hepoch_bne : (x.epoch != x.self.uc.epoch) = false := by simp [hepoch]
  refine SepWPp.fold (hdrSomeBranchFrameAt_expose s0.sp) (by sep_focus) ?_
  refine SepWPp.of_sepWP_inImage (mid := entry + 564#64) hinv ?_
  wp_conv_pre =>
    rw [ha_hdr ptr_hdrFull, memRegion_64_cells_hdr ptr_hdr,
        memRegion_128_sp_1136 s0.sp,
        memRegion_128_sp_1008 s0.sp,
        memRegion_128_sp_880 s0.sp]
  wp_pull_exists
  wp_steps
  refine SepWP.fold
    (ct2DeallocAt_of_cells64_drop A cap_hdrFull ptr_hdrFull hdrFull
      w0 w1 w2 w3 w4 w5 w6 w7 hge64 hle_cap hmax_cap hptr_hdrFull hcap_hdrFull)
    (by sep_focus) ?_
  have hfold_hdr :
      (ptr_hdr ↦₆₄ w0) ∗ ((ptr_hdr + 8#64) ↦₆₄ w1) ∗
        ((ptr_hdr + 16#64) ↦₆₄ w2) ∗ ((ptr_hdr + 24#64) ↦₆₄ w3) ∗
        ((ptr_hdr + 32#64) ↦₆₄ w4) ∗ ((ptr_hdr + 40#64) ↦₆₄ w5) ∗
        ((ptr_hdr + 48#64) ↦₆₄ w6) ∗ ((ptr_hdr + 56#64) ↦₆₄ w7) ⊢
      (ptr_hdr ↦ₛ hdrFull.take 64) :=
    Entails.of_eq (ha_hdr ptr_hdr).symm
  refine SepWP.fold hfold_hdr (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 1112#64 1104#64 1096#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 1088#64 1080#64 1072#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 1064#64 1056#64 1048#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 1040#64 1032#64 1024#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 1016#64 1008#64 1000#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 992#64 984#64 976#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 968#64 960#64 952#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 944#64 936#64 928#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 920#64 912#64 904#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 896#64 888#64 880#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 872#64 864#64 856#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 848#64 840#64 832#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 824#64 816#64 808#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 800#64 792#64 784#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A s0.sp 776#64 768#64 760#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (polyDecoderNew1152Raw_of_slots A s0.sp) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv_end
  refine SepWPp.rw_pre (by rw [← hepoch]; ac_rfl)
    (hcont _
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

/-! ## 2. Combined Part 1 (`0x61254 .. 0x61488`, offsets `0 .. 564`) -/

theorem cells12_sp_96_expand_hdr (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
       ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64, ∃∗ r7 : BitVec 64,
       ∃∗ r8 : BitVec 64, ∃∗ r9 : BitVec 64, ∃∗ r10 : BitVec 64, ∃∗ r11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_part1_wpp {img : Obj.Image} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hadd_ok : AddChunkOkX img A ext)
    (hdec_ok : PolyDecodedMessageOkX img A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (s0 : State) (R : SepProp)
    (hsort_self : PolyDecoderStrictSorted x.self.receiving_hdr)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
    (hrun : s0.status = .Running)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (halign : img.base &&& 4095#64 = 0#64)
    (hinv : ImgCallInv img s0)
    (hx0 : s0.readReg64 .x0 = x.outA)
    (hx1 : s0.readReg64 .x1 = x.selfA)
    (hx2 : s0.readReg64 .x2 = x.epoch)
    (hx3 : s0.readReg64 .x3 = x.chunkA)
    (hcont : ∀ (st2 : State) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
        (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
        (c1 c2 : BitVec 64) (g_auth0 : AuthenticatorGhost)
        (_hepoch : x.epoch = x.self.uc.epoch)
        (_hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
        (_hsort : PolyDecoderStrictSorted receivingHdr)
        (_hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
        (_hge64 : 64 ≤ hdrFull.length)
        (_hlt_max : hdrFull.length < 2 ^ 63)
        (_hptr_hdr : ptr_hdr ≠ 0#64),
      st2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) st2
        (recvHdrChunkRoAt img ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1648#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 1640#64) ↦₆₄ c1) ∗
          ((s0.sp - 1632#64) ↦₆₄ c2) ∗
          ((s0.sp - 1624#64) ↦₆₄ x.epoch) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitAt img.base ∗
          reduceTableAt img.base ∗
          A.pool ∗
          memRegion (s0.sp - 18704#64) 672 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          savedRegsAt s0)
        (recvHdrChunkPostQ img F A x s0 R)
        (recvHdrChunkPostQp F A img.base x s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
      (recvHdrChunkRoAt img ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        chunkedNoHeaderReceivedAt A x.selfA x.self ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        A.pool ∗
        stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R) := by
  have hmc_raw := hA.session_memcpy_region_ok_at noHeaderReceivedRecvHdrChunkName
    (num% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy"))
    polyDecodedMessageStackX (by decide) (by decide)
    (by rw [noHeaderReceivedRecvHdrChunk_fnOff, memcpy_fnOff])
  have h_mc_dec := (polyDecoderSplit A x.self.receiving_hdr).memcpy_withStack_inImage_ok
    (by decide) polyDecodedMessageStackX hmc_raw
  have h_add := addChunk_ok_at_recvHdr hadd_ok
  have h_dec := polyDecodedMessage_ok_at_recvHdr hdec_ok
  have h_pan_epoch := panic_at_assert_failed_u64_recvHdr img.base ext
  have h_pan_slice := panic_at_slice_index_fail_recvHdr img.base ext
  have h_none := @recv_hdr_chunk_none_wpp img F A ext hA x
  have h_alloc_mac := @recv_hdr_chunk_alloc_mac_hdr_wpp img F A ext hA x
  have h_init_dec := @recv_hdr_chunk_init_dec_wpp img F A ext x
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx3
  unfold tripleRatchetProgAtExt at hpc h_mc_dec h_add h_dec h_pan_epoch h_pan_slice h_none h_alloc_mac h_init_dec hcont ⊢
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 0 164
  recv_hdr_chunk_fetches_range img.base (Rust.withPanics ext) 1200 52
  clear hmc_raw hadd_ok hdec_ok hA
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      noHeaderReceivedRecvHdrChunkName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  unfold chunkedNoHeaderReceivedAt
  refine SepWPp.rw_pre (by rw [stackAt_recvHdrChunk_split s0.sp]) ?_
  unfold hdrActiveFrameRegionsAt
  refine SepWPp.rw_pre (by rw [cells12_sp_96_expand_hdr s0.sp, cells11_sp_1648_expand s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  refine SepWPp.fold (noHeaderReceivedUcAt_expose_entails A x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  rename_i g_auth0
  by_cases hepoch : x.epoch = x.self.uc.epoch
  · have hepoch_bne : (x.epoch != x.self.uc.epoch) = false := by simp [hepoch]
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk" "memcpy")) hinv ?_
    wp_steps
    refine SepWP.fold (savedRegsAt_of_cells12_hdr s0) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_inImage_recvCt2 h_mc_dec
      (s0.sp - 1560#64, x.selfA + 56#64) hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost_mc => ?_
    rcases hpost_mc with ⟨htr1, _⟩
    refine SepWPp.fold
      (polyDecoderAt_pts_length A (s0.sp - 1560#64) x.self.receiving_hdr)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpts_len => ?_
    have hadd_eq : PolyDecoder.addChunk x.self.receiving_hdr x.chunk =
        .ok (addChunkTotal x.self.receiving_hdr x.chunk) :=
      addChunk_eq_ok x.self.receiving_hdr x.chunk hpts_len
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk")) hF_sf ?_
    wp_steps
    have hstack_add :
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX =
          memRegion ((s0.sp - 1648#64) - 17056#64) 576 ∗ stackAt sf.sp addChunkStackX := by
      rw [hsp_sf, stackAt_polyDecodedMessage_eq_addChunk (s0.sp - 1648#64)]
    refine SepWP.fold (Entails.of_eq hstack_add) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_inImage_recvCt2 h_add
      ⟨s0.sp - 1560#64, x.chunkA, x.self.receiving_hdr, x.chunk⟩ hinv2
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost_add => ?_
    rcases hpost_add with ⟨htr2, hsort_add⟩
    have hstack_add_back :
        memRegion ((s0.sp - 1648#64) - 17056#64) 576 ∗ stackAt sf.sp addChunkStackX ⊢
          stackAt sf_1.sp polyDecodedMessageStackX := by
      rw [hsp_sf_1, hsp_sf, ← stackAt_polyDecodedMessage_eq_addChunk (s0.sp - 1648#64)]
      exact Entails.refl _
    refine SepWPp.fold hstack_add_back (by sep_focus) ?_
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message")) hF_sf_1 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_inImage_recvCt2 h_dec
      ⟨s0.sp - 1160#64, s0.sp - 1560#64,
       addChunkTotal x.self.receiving_hdr x.chunk⟩ hinv3
    apply SepWPp.exists_elim
    intro optMsg
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost_dec => ?_
    rcases hpost_dec with ⟨hdec_eq, htr3⟩
    have hsp_sf2 : sf_2.sp = s0.sp - 1648#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf]
    have htr_sf2 : sf_2.trace = s0.trace := by rw [htr3, htr2, htr1]
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by rw [hcs_sf_2, hcs_sf_1, hcs_sf]
    have hstack_sf1 :
        stackAt sf_1.sp polyDecodedMessageStackX ⊢
          stackAt (s0.sp - 1648#64) polyDecodedMessageStackX := by
      rw [hsp_sf_1, hsp_sf]
      exact Entails.refl _
    refine SepWPp.fold hstack_sf1 (by sep_focus) ?_
    change SepWPp prog (s0.readReg64 .x30) sf_2 _
      (recvHdrChunkPostQ img F A x s0 R)
      (recvHdrChunkPostQp F A img.base x s0 R)
    cases optMsg with
    | none =>
      refine SepWPp.rw_pre (by rw [optKeyBytesAt_none_sp_1160 A s0.sp]) ?_
      refine SepWPp.of_sepWP_inImage (mid := entry + 180#64) hF_sf_2 ?_
      wp_steps
      refine SepWP.fold (noHeaderReceivedUcAt_fold_entails A x.selfA x.self.uc g_auth0) (by sep_focus) ?_
      refine SepWP.fold (cells11_sp_1648_fold s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold
        (fold_none_addrs_sp_hdr A s0.sp (addChunkTotal x.self.receiving_hdr x.chunk))
        (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv_none
      refine SepWPp.rw_pre (by unfold recvHdrChunkRoAt; ac_rfl)
        (h_none (addChunkTotal x.self.receiving_hdr x.chunk)
          s0 _ R hepoch hadd_eq hsort_add hdec_eq
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, hsp_sf2])
          hsp_s0
          (by simp only [wp_norm, arm64_norm, htr_sf2])
          hvregs_sf2
          hinv_none
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
    | some hdrFull =>
      refine SepWPp.fold (optKeyBytesAt_some_sp_1160 A s0.sp hdrFull) (by sep_focus) ?_
      sep_elim_exists
      rename_i cap_hdrFull ptr_hdrFull
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hle_cap, hmax_cap, hptr_hdrFull⟩
      have hlt_max : hdrFull.length < 2 ^ 63 := by omega
      have hcap_cmn : (cap_hdrFull + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hmax_cap
      by_cases hge64 : 64 ≤ hdrFull.length
      · have hult64 : (BitVec.ofNat 64 hdrFull.length).ult 64#64 = false :=
          ofNat_ult_64_of_ge hge64 hlt_max
        have hsub64 : BitVec.ofNat 64 hdrFull.length - 64#64 = BitVec.ofNat 64 (hdrFull.length - 64) :=
          ofNat_sub_64_eq hge64 hlt_max
        have hmsb64 : (BitVec.ofNat 64 (hdrFull.length - 64)).getLsbD 63 = false :=
          ofNat_getLsbD_63_false (by omega)
        have hmsb64' : (BitVec.ofNat 64 (hdrFull.length - 64))[63] = false :=
          ofNat_getElem_63_false (by omega)
        have hpl64 : ConditionHolds .PL (subsPState64 (BitVec.ofNat 64 hdrFull.length) 64#64) = true := by
          simp only [ConditionHolds, subsPState64, wp_norm, arm64_norm, addWithCarry64_sub_64_n, hsub64, hmsb64, hmsb64']
        refine SepWPp.fold (vecU8HeapAt_split_64 A cap_hdrFull ptr_hdrFull hdrFull hge64) (by sep_focus) ?_
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨_, _, _, hcap_hdrFull⟩
        refine SepWPp.fold
          (noHeaderReceivedCells_entails_memRegion_456 x.selfA _ _ _ _ _ _ _)
          (by sep_focus) ?_
        refine SepWPp.of_sepWP_inImage (mid := entry + 252#64) hF_sf_2 ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq (stackAt_polyDecodedMessage_eq_extHook (s0.sp - 1648#64))) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv_some
        refine SepWPp.frame_call
          (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
            ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
            A.pool ∗
            stackAt (s0.sp - 1648#64) extHookStack)
          (by sep_focus)
          (by repeat rw [sepConj_assoc])
          (h_alloc_mac hdrFull cap_hdrFull ptr_hdrFull s0 _ _ R hge64 hlt_max
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, hsp_sf2])
            hsp_s0
            (by simp only [wp_norm, arm64_norm, htr_sf2])
            hvregs_sf2
            hinv_some
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, hsub64, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (fun st' ptr_mac ptr_hdr hptr_hdr hpc' hrun' hsp' htr' hvregs' hinv'
              hx0' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx29' => ?_))
        refine SepWPp.fold
          (memRegion_24_of_sp_1160 s0.sp cap_hdrFull ptr_hdrFull (BitVec.ofNat 64 hdrFull.length))
          (by sep_focus) ?_
        refine SepWPp.frame_call
          ((ptr_hdrFull ↦ₛ hdrFull.take 64) ∗
            ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
            memRegion (ptr_hdrFull + BitVec.ofNat 64 hdrFull.length) (cap_hdrFull.toNat - hdrFull.length) ∗
            A.live ptr_hdrFull cap_hdrFull.toNat 1 ∗
            memRegion ptr_hdr 64 ∗
            A.live ptr_hdr 64 1 ∗
            ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
            hdrSomeBranchFrameAt (s0.sp - 1648#64))
          (by sep_focus)
          (by repeat rw [sepConj_assoc])
          (h_init_dec hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr s0 st' _ R
            hepoch hge64 hle_cap hmax_cap hptr_hdrFull hcap_hdrFull
            hpc' hrun' hsp' hsp_s0 htr' hvregs' hinv'
            hx0' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx29'
            (fun st2 hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
        refine SepWPp.rw_pre (by rw [← hepoch]; ac_rfl)
          (hcont st2 (addChunkTotal x.self.receiving_hdr x.chunk) hdrFull
            cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0
            hepoch hadd_eq hsort_add hdec_eq hge64 hlt_max hptr_hdr
            hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
            hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2)
      · have hlt64 : hdrFull.length < 64 := by omega
        have hult64 : (BitVec.ofNat 64 hdrFull.length).ult 64#64 = true :=
          ofNat_ult_64_of_lt hlt64
        have hpan_lt := recv_hdr_chunk_isPanic_of_lt_64 x.self x.epoch x.chunk
          (addChunkTotal x.self.receiving_hdr x.chunk) hdrFull hepoch hadd_eq hdec_eq hlt64
        apply SepWPp.of_sepWP
          (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
            "core::slice::index::slice_index_fail"))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        exact allowPanic_isPanic_recvCt2 hpan_lt
          (by simp only [wp_norm, arm64_norm, htr_sf2, List.prefix_refl]) hm
  · have hepoch_bne : (x.epoch != x.self.uc.epoch) = true := bne_iff_ne.mpr hepoch
    have hpan_ep := recv_hdr_chunk_isPanic_of_epoch_ne x.self x.epoch x.chunk hepoch
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"
        "core::panicking::assert_failed::<u64, u64>"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    exact allowPanic_isPanic_recvCt2 hpan_ep
      (by simp only [wp_norm, arm64_norm, List.prefix_refl]) hm

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

