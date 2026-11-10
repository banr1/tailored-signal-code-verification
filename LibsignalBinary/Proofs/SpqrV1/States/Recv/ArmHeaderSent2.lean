/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.headerSent` Arm, Part 2

**Checked by Lean.** Post-call `.done` / `.stillReceiving` writeback blocks, the
`<HeaderSent>::recv_ct1_chunk` (`eq_ct1`) branch, and the complete `.headerSent` arm
`states_recv_arm_headerSent` (`0x55760`, `+780`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
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
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  bv376_toNat_hs

@[local arm64_norm, local wp_norm]
theorem bv880_toNat_hs : (880#64 : BitVec 64).toNat = 880 := rfl

/-! ## 1. Stack, Relocation, and Tag-Extraction Helpers for `.headerSent` -/

theorem sendEkUnusedAt_split_f10 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qf10 : BitVec 128,
        ((fsp + 3856#64) ↦₁₂₈ qf10) ∗
        memRegion fsp 8 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2736#64) 1120 ∗
        memRegion (fsp + 3872#64) 272 := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 1120) (k := 288)
        (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 16) (k := 272)
        (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 3856#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro qf10
  refine Entails.sepExists_right qf10 ?_
  exact Entails.of_eq (by ac_rfl)

theorem sendEkUnusedAt_rejoin_f10 (fsp : BitVec 64) (qf10 : BitVec 128) :
    ((fsp + 3856#64) ↦₁₂₈ qf10) ∗
    memRegion fsp 8 ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2736#64) 1120 ∗
    memRegion (fsp + 3872#64) 272 ⊢
      sendEkUnusedAt fsp := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 1120) (k := 288)
        (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 16) (k := 272)
        (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
    (memRegion (fsp + 2736#64) 1120 ∗ (((fsp + 3856#64) ↦₁₂₈ qf10) ∗ memRegion (fsp + 3872#64) 272)) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 3856#64) qf10)))))

theorem done_976_entails_memRegion_880 (a : BitVec 64) (w : Words63) :
    (a ↦₆₄ 2#64) ∗ words63At (a + 8#64) w ∗ memRegion (a + 512#64) 368 ⊢
      memRegion a 880 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 872) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 504) (k := 368)
        (b' := a + 512#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a 2#64)
    (sepConj_mono_left (words63At_entails_memRegion (a + 8#64) w))

theorem Relocatable.of_chunkedHeaderSentAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    Relocatable 880 (fun a => chunkedHeaderSentAt A a st) := by
  intro src; dsimp only
  refine Entails.trans (chunkedHeaderSentAt_extract63_376 A src st) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.sepExists_elim; intro tailBytes
  apply Entails.pure_left; intro ⟨_, htail⟩
  let bs := wordsBytes (words63List w) ++ tailBytes
  have hlen : bs.length = 880 := by
    simp only [bs, List.length_append, length_wordsBytes, length_words63List, htail]
  have hbs : ∀ dst : BitVec 64,
      words63At dst w ∗ ((dst + 504#64) ↦ₛ tailBytes) = (dst ↦ₛ bs) := by
    intro dst
    rw [words63At_eq_wordsAt, wordsAt_eq_pointsToBytes,
        pointsToBytes_append dst (wordsBytes (words63List w)) tailBytes,
        length_wordsBytes, length_words63List]
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  rw [← sepConj_assoc, hbs src]
  exact Entails.refl _

def polyEncoderTag : EncoderState → BitVec 64
  | .points _ => 0#64
  | .polys _ => 1#64

theorem polyEncoderTag_bne_2 (s : EncoderState) : (polyEncoderTag s != 2#64) = true := by
  cases s <;> rfl

def polyEncoderTailAt (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) : SepProp :=
  (match enc.s with
   | .points pts =>
     ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
       pointListOf A a pts
   | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A a ps) ∗
  ((a + 384#64) ↦₃₂ enc.idx) ∗
  memRegion (a + 388#64) 4

theorem polyEncoderAt_eq_tag_tail (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc =
      (a ↦₆₄ polyEncoderTag enc.s) ∗ polyEncoderTailAt A (a + 8#64) enc := by
  unfold polyEncoderAt polyEncoderTailAt encoderStateAt polyEncoderTag
    polyEncoderPointsTag polyEncoderPolysTag polyEncoderVecsOff
    polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  have h1 : (a + 8#64) + 384#64 = a + 0x188#64 := by bv_omega
  have h2 : (a + 8#64) + 388#64 = a + 0x18c#64 := by bv_omega
  rw [h1, h2]
  cases enc.s <;> · dsimp only; ac_rfl

theorem Relocatable.of_polyEncoderTailAt (A : RustAlloc) (enc : PolyEncoder) :
    Relocatable 392 (fun a => polyEncoderTailAt A a enc) := by
  have hstate : Relocatable 384 (fun a =>
      match enc.s with
      | .points pts =>
        ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
          pointListOf A a pts
      | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A a ps) := by
    cases hs : enc.s with
    | points pts =>
      dsimp only
      refine Relocatable.pure_left
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555))
        fun ⟨hlen, _⟩ => ?_
      exact Relocatable.arrayAt (elem := fun pt addr => pointOf A addr pt)
        (fun pt => Relocatable.vecOf A gf16Stride gf16Align gf16At pt.value)
        pts 384 (by rw [hlen]; rfl)
    | polys ps =>
      dsimp only
      refine Relocatable.pure_left (ps.length = NUM_POLYS) fun hlen => ?_
      exact Relocatable.arrayAt (elem := fun p addr => polyOf A addr p)
        (fun p => Relocatable.vecOf A gf16Stride gf16Align gf16At p.coefficients)
        ps 384 (by rw [hlen]; rfl)
  have hfull := Relocatable.sepConj (off := 384#64) (m := 392) rfl rfl hstate
    (Relocatable.sepConj (off := 4#64) (m := 8) rfl rfl
      (Relocatable.pointsTo32 enc.idx) (Relocatable.of_memRegion 4))
  refine Relocatable.congr rfl (fun a => ?_) hfull
  unfold polyEncoderTailAt
  have h2 : (a + 384#64) + 4#64 = a + 388#64 := by bv_omega
  rw [h2]

theorem exists_words5x10_cons_of_length_392 (w0 : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 392) :
    ∃ p : Words5x10, p.b0.w0 = w0 ∧ unpack64 w0 ++ bs = wordsBytes (words5x10List p) := by
  obtain ⟨w1, r2, hr2, h1⟩ := exists_word_cons_of_length_add_8 (k := 384) bs h
  obtain ⟨w2, r3, hr3, h2⟩ := exists_word_cons_of_length_add_8 (k := 376) r2 hr2
  obtain ⟨w3, r4, hr4, h3⟩ := exists_word_cons_of_length_add_8 (k := 368) r3 hr3
  obtain ⟨w4, r5, hr5, h4⟩ := exists_word_cons_of_length_add_8 (k := 360) r4 hr4
  obtain ⟨w5, r6, hr6, h5⟩ := exists_word_cons_of_length_add_8 (k := 352) r5 hr5
  obtain ⟨w6, r7, hr7, h6⟩ := exists_word_cons_of_length_add_8 (k := 344) r6 hr6
  obtain ⟨w7, r8, hr8, h7⟩ := exists_word_cons_of_length_add_8 (k := 336) r7 hr7
  obtain ⟨w8, r9, hr9, h8⟩ := exists_word_cons_of_length_add_8 (k := 328) r8 hr8
  obtain ⟨w9, r10, hr10, h9⟩ := exists_word_cons_of_length_add_8 (k := 320) r9 hr9
  obtain ⟨b1, r20, hr20, hb1⟩ := exists_words10_of_length_add_80 (k := 240) r10 hr10
  obtain ⟨b2, r30, hr30, hb2⟩ := exists_words10_of_length_add_80 (k := 160) r20 hr20
  obtain ⟨b3, r40, hr40, hb3⟩ := exists_words10_of_length_add_80 (k := 80) r30 hr30
  obtain ⟨b4, r50, hr50, hb4⟩ := exists_words10_of_length_add_80 (k := 0) r40 hr40
  have hr50_nil : r50 = [] := List.length_eq_zero_iff.mp hr50
  refine ⟨⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩, b1, b2, b3, b4⟩, rfl, ?_⟩
  simp only [words5x10List, words10List, wordsBytes_append, wordsBytes_cons, wordsBytes_nil,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, hb1, hb2, hb3, hb4, hr50_nil,
    List.append_assoc, List.append_nil, List.nil_append]

theorem polyEncoderAt_extract_words5x10_tag (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc ⊢
      ∃∗ p : Words5x10,
        ⌜(p.b0.w0 != 2#64) = true⌝ ∗
        wordsAt a (words5x10List p) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst enc) (wordsBytes (words5x10List p)) := by
  let w0 := polyEncoderTag enc.s
  have h1 : polyEncoderAt A a enc ⊢
      (a ↦₆₄ w0) ∗ (∃∗ bs : List (BitVec 8),
        ⌜bs.length = 392⌝ ∗ ((a + 8#64) ↦ₛ bs) ∗
        relocatedHeap (fun dst => polyEncoderTailAt A dst enc) bs) := by
    rw [polyEncoderAt_eq_tag_tail A a enc]
    exact sepConj_mono_right (Relocatable.of_polyEncoderTailAt A enc (a + 8#64))
  refine Entails.trans h1 ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm (a ↦₆₄ w0)]
  apply Entails.pure_left; intro hlen
  obtain ⟨p, hp0, hbs⟩ := exists_words5x10_cons_of_length_392 w0 bs hlen
  refine Entails.sepExists_right p ?_
  have htag : (p.b0.w0 != 2#64) = true := hp0 ▸ polyEncoderTag_bne_2 enc.s
  refine Entails.pure_right htag ?_
  have hslice : ∀ dst : BitVec 64,
      (dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦ₛ bs) = wordsAt dst (words5x10List p) := by
    intro dst
    rw [wordsAt_eq_pointsToBytes, ← hbs, pointsToBytes_append dst (unpack64 w0) bs,
        unpack64_length, ← pointsTo64_eq_pointsToBytes dst w0]
  rw [← sepConj_assoc, hslice a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  rw [← wordsAt_eq_pointsToBytes, ← hslice dst, polyEncoderAt_eq_tag_tail A dst enc, sepConj_assoc]
  exact sepConj_mono_right (relocatedHeap_recompose (fun d => polyEncoderTailAt A d enc) bs (dst + 8#64))

theorem chunkedHeaderSentAt_extract63_376_tag (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderSentAt A a st ⊢
      ∃∗ w : Words63, ∃∗ tailBytes : List (BitVec 8),
        ⌜(w.b0.w0 != 2#64) = true ∧ w.b5.w9 = st.uc.epoch ∧ tailBytes.length = 376⌝ ∗
        words63At a w ∗
        ((a + 504#64) ↦ₛ tailBytes) ∗
        relocatedHeap (fun dst => chunkedHeaderSentAt A dst st)
          (wordsBytes (words63List w) ++ tailBytes) := by
  unfold chunkedHeaderSentAt
  have h12 : polyEncoderAt A a st.sending_ek ∗ unchunkedEkSentAt A (a + 400#64) st.uc ⊢
      ∃∗ p : Words5x10, ∃∗ g : ThreeVecWords,
        ⌜(p.b0.w0 != 2#64) = true⌝ ∗
        wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) := by
    refine Entails.trans (sepConj_mono
      (polyEncoderAt_extract_words5x10_tag A a st.sending_ek)
      (unchunkedEkSentAt_extract A (a + 400#64) st.uc)) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
    rw [sepConj_assoc (⌜(p.b0.w0 != 2#64) = true⌝)]
    apply Entails.pure_left; intro htag
    exact Entails.sepExists_right p (Entails.sepExists_right g
      (Entails.pure_right htag (wordsExtract_sepConj rfl (fun _ => rfl))))
  refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm) ?_
  refine Entails.trans (sepConj_mono h12
    (relocatable_400_extract_words3_376 (Relocatable.of_polyDecoderAt A st.receiving_ct1) (a + 480#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro v
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro tailBytes
  rw [sepConj_assoc (⌜(p.b0.w0 != 2#64) = true⌝)]
  apply Entails.pure_left; intro htag
  rw [sepConj_left_comm (wordsAt a _ ∗ _)]
  apply Entails.pure_left; intro htail
  let w := mkWords63_50_10_3 p g st.uc.epoch v
  refine Entails.sepExists_right w (Entails.sepExists_right tailBytes ?_)
  refine Entails.pure_right ⟨htag, rfl, htail⟩ ?_
  have hw_eq := words63List_mkWords63_50_10_3 p g st.uc.epoch v
  have hwords_a :
      wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗ wordsAt (a + 480#64) (vecWordsList v) =
      words63At a w := by
    rw [words63At_eq_wordsAt a w, ← hw_eq,
        wordsAt_append (words5x10List p ++ ekSentWordsList g st.uc.epoch) (vecWordsList v)]
    simp only [List.length_append, length_words5x10List, length_ekSentWordsList]
  have ha504 : (a + 480#64) + 24#64 = a + 504#64 := by bv_omega
  rw [ha504]
  have hreord :
      (wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))) ∗
      wordsAt (a + 480#64) (vecWordsList v) ∗
      ((a + 504#64) ↦ₛ tailBytes) ∗
      relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
        (wordsBytes (vecWordsList v) ++ tailBytes) =
      (wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗ wordsAt (a + 480#64) (vecWordsList v)) ∗
      ((a + 504#64) ↦ₛ tailBytes) ∗
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
          (wordsBytes (vecWordsList v) ++ tailBytes)) := by ac_rfl
  rw [hreord, hwords_a]
  refine sepConj_mono_right (sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_))
  have hsplit_dst :
      (dst ↦ₛ (wordsBytes (words63List w) ++ tailBytes)) =
      (dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
      ((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes)) := by
    rw [← hw_eq, wordsBytes_append, List.append_assoc,
        pointsToBytes_append dst (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))
          (wordsBytes (vecWordsList v) ++ tailBytes)]
    simp only [length_wordsBytes, List.length_append, length_words5x10List, length_ekSentWordsList]
  have hreord_dst :
      ((dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
        ((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes))) ∗
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
          (wordsBytes (vecWordsList v) ++ tailBytes)) =
      ((dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))) ∗
      (((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes)) ∗
        relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
          (wordsBytes (vecWordsList v) ++ tailBytes)) := by ac_rfl
  rw [hsplit_dst, hreord_dst, ← sepConj_assoc (polyEncoderAt A dst st.sending_ek)]
  exact sepConj_mono (relocatedHeap_recompose _ _ dst) (relocatedHeap_recompose _ _ (dst + 480#64))

/-! ## 2. Post-Call Writeback Blocks (`0x56848..0x56ad4` and `0x58cac..0x58ecc`) -/

theorem fnAddr_adrp_569c0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 5484#64) &&&
      0xfffffffffffff000#64) = b + 0x51000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

set_option maxHeartbeats 1200000 in
/-- Post-call writeback block `0x56848..0x569e8 -> 0x56aa4..0x56ad4 -> 0x58e80..0x58ecc -> 0x59e88..0x59ff0`
    (`+5108 -> s0.x30`) when `<HeaderSent>::recv_ct1_chunk` returns `.done outSt` at `fsp + 976#64`. -/
theorem headerSent_post_call_done_56848 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
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
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hadrp := fnAddr_adrp_569c0 (b := b) (H := Rust.withPanics ext) hb
  have hwb := @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range b (Rust.withPanics ext) 5108 420
  states_recv_fetches_range b (Rust.withPanics ext) 5712 52
  states_recv_fetches_range b (Rust.withPanics ext) 14892 80
  dsimp only [tripleRatchetProgAtExt, statesRecvName, headerSentRecvChunkAt,
    BitVec.ofNat_eq_ofNat] at hpc hadrp hwb ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
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
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
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
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
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
/-- Post-call writeback block `0x56848..0x56850 -> 0x58cac..0x58ecc -> 0x59e88..0x59ff0`
    (`+5108 -> s0.x30`) when `<HeaderSent>::recv_ct1_chunk` returns `.stillReceiving outSt` at `fsp + 976#64`. -/
theorem headerSent_post_call_still_56848 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  states_recv_fetches_range b (Rust.withPanics ext) 5108 12
  states_recv_fetches_range b (Rust.withPanics ext) 14424 548
  dsimp only [tripleRatchetProgAtExt, statesRecvName, headerSentRecvChunkAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376_tag A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out tailBytes
  refine SepWP.pure_elim fun ⟨hw0, hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => a ↦ₛ tailBytes)
    hrel_tail s0
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hwb
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
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
  refine call_memcpy_relocate_cs (ret_pc := entry + 14836#64)
    hmemcpy_raw hrel_tail (sp0 - 3664#64) (sp0 - 2760#64)
    rfl hrun hsp hfsp_align rfl htr rfl
    (by simp only [Reg.x1, arm64_norm, hx21])
    rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
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
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes))
        rfl hrun1 hsp1 hsp_align
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

/-! ## 3. Call Rule and `.headerSent` `eq_ct1` Arm -/

theorem fnAddr_fwd_headerSentRecvCt1 {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr statesRecvName + 33960#64 := by
  dsimp only [tripleRatchetProgAtExt, statesRecvName, headerSentRecvCt1ChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x5005c,
      CryptoVerification.libsignalSessionCode_fnOff_0x58504]
  bv_omega

theorem stackAt_statesRecvCallee_split_headerSentRecvCt1 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 928 ∗ stackAt fsp headerSentRecvCt1ChunkStack :=
  stackAt_split_bottom fsp headerSentRecvCt1ChunkStack 928 (by decide)

/-- Framed call rule for `headerSentRecvCt1ChunkSpec A F b` (`0x5d8fc`). -/
theorem call_headerSentRecvCt1Chunk {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry (headerSentRecvCt1ChunkSpec A F b))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
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
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, chunkA, st, chunk, outRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [headerSentRecvCt1ChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hsort, hrecv⟩, hm⟩
  · dsimp only [headerSentRecvCt1ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [headerSentRecvCt1ChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame =
        (headerSentRecvChunkAt A outA outRes ∗
          (memRegion stA chunkedHeaderSentSize ∗
            (chunkAt chunkA chunk ∗ (tokenInitAt b ∗ (reduceTableAt b ∗
              (A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option maxHeartbeats 1600000 in
/-- `.headerSent` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct1 chunk`
    (`+780 -> s0.x30`, `0x55760..0x558c0 -> 0x56814..0x56844 -> 0x56848..0x59ff0`). -/
theorem headerSent_arm_eq_ct1
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F b))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
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
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt b ∗ reduceTableAt b ∗
        A.pool ∗
        stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      sf.trace = s0.trace →
      Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt b ∗ reduceTableAt b ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sm Pm =>
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm Q_post Q_panic) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  have hpost_done := @headerSent_post_call_done_56848 A F b ext hb hmemcpy s0
  have hpost_still := @headerSent_post_call_still_56848 A F b ext hmemcpy s0
  rw [fnAddr_fwd_headerSentRecvCt1] at hcall ⊢
  states_recv_fetches_range b (Rust.withPanics ext) 780 356
  states_recv_fetches_range b (Rust.withPanics ext) 5056 52
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
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
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
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
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
  · refine call_memcpy_relocate_cs (ret_pc := entry + 5084#64)
      hmemcpy_raw (Relocatable.of_chunkedHeaderSentAt A st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
      rfl hrun hsp hfsp_align rfl htr
      (by simp only [Reg.x0, arm64_norm, hsp])
      (by simp only [Reg.x1, arm64_norm, hx1])
      rfl (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
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
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_headerSentRecvCt1 (s0.sp - 4240#64)))
      (by sep_focus) ?_
    refine call_headerSentRecvCt1Chunk hb hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk outRes hsort hrecv
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := entry + 5108#64)
      (R := R)
      (Frame :=
        P_rest ∗
        memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) - 19552#64) 928 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      rfl hrun1 hsp1 hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      htr1
      (by simp only [Reg.x0, arm64_norm, hsp1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm, hx25_1])
      (by simp only [Reg.x3, arm64_norm, hx24_1])
      (by
        dsimp only [chunkedHeaderSentSize, statesRecvCalleeStackX, headerSentRecvCt1ChunkStack,
          polyDecoderDecodedMessageStack, extHookStack, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]
        ac_rfl)
      hpanic
      ?_
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_headerSentRecvCt1 (s0.sp - 4240#64)).symm)
      (by sep_focus) ?_
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
             memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             tokenInitAt b ∗ reduceTableAt b ∗
             A.pool)
            hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
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
             memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
             tokenInitAt b ∗ reduceTableAt b ∗
             A.pool)
            hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]
      ac_rfl

/-! ## 4. Complete `.headerSent` Arm (`+780 -> s0.x30`, `0x55760 -> 0x59ff0`) -/

/-- Complete `.headerSent` arm of `<States>::recv` (`+780 -> s0.x30`, `0x55760 -> 0x59ff0`):
    handles all `msg` cases (`msg.epoch > st.uc.epoch`, `msg.epoch < st.uc.epoch`,
    `msg.epoch = st.uc.epoch` with `msg.payload ≠ .ct1 _`, and `msg.epoch = st.uc.epoch` with
    `msg.payload = .ct1 chunk`). -/
theorem states_recv_arm_headerSent
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F b))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hinv : statesRecvPreInv (.headerSent st))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoAt b ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpec A F K b (.headerSent st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpec A F K b (.headerSent st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.headerSent st) msg _ R ?_
    rw [states_recv_headerSent_gt K st msg hgt]
    rw [show memRegion outA v1RecvSize ∗
          chunkedStatesAt A selfA (.headerSent st) ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 =
        statesRecvRoAt b ∗
          memRegion outA v1RecvSize ∗
          chunkedStatesAt A selfA (.headerSent st) ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (headerSent_arm_gt hdealloc s0 s outA selfA msgA st msg (statesRecvRoAt b)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.headerSent st) msg _ R ?_
      rw [states_recv_headerSent_lt K st msg hlt]
      rw [show memRegion outA v1RecvSize ∗
            chunkedStatesAt A selfA (.headerSent st) ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoAt b ∗
            A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 =
          statesRecvRoAt b ∗
            memRegion outA v1RecvSize ∗
            chunkedStatesAt A selfA (.headerSent st) ∗
            messageAt spqrPolyApi msgA msg ∗
            A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 by ac_rfl]
      refine SepWP.mono
        (headerSent_arm_lt hmemcpy s0 s outA selfA msgA st msg (statesRecvRoAt b)
          hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct1 chunk =>
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt b ∗
                (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt b ∗ reduceTableAt b) ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 =
            (statesRecvJumpTableAt b ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
              memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              tokenInitAt b ∗ reduceTableAt b ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 by ac_rfl]
        refine SepWPp.of_sepWP
          (headerSent_arm_eq_ct1 (K := K) hb hcall hmemcpy s0 s outA selfA msgA st msg chunk
            (statesRecvJumpTableAt b ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) R
            hinv heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpec, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨Or.inr hpan'.1.1, hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
        have hct1 : ∀ c, msg.payload ≠ .ct1 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.headerSent st) msg _ R ?_
        rw [states_recv_headerSent_eq_other K st msg heq hct1]
        rw [show memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              statesRecvRoAt b ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 =
            statesRecvRoAt b ∗
              memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 by ac_rfl]
        refine SepWP.mono
          (headerSent_arm_eq_other hmemcpy s0 s outA selfA msgA st msg (statesRecvRoAt b)
            heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

end CryptoVerification.SpqrV1.States.Recv
