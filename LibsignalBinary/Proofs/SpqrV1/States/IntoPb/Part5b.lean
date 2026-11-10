/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5b: Arm 9 (`States.ct1Acknowledged`) Step Lemmas

**Checked by Lean.**

Representation exposure, scratch-cell layout, and step lemmas for Arm 9 (`States.ct1Acknowledged`,
tag `11`, `+0 -> +60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544 -> ret`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Representation Exposure & Scratch Helpers for Arm 9 (`Ct1Acknowledged`) -/

/-- `Relocatable 32` for 4 consecutive 64-bit words starting at `a`. -/
theorem Relocatable.words4 (w0 w1 w2 w3 : BitVec 64) :
    Relocatable 32 (fun a =>
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
  have h := Relocatable.sepConj (off := 24#64) (m := 32) rfl rfl
    (Relocatable.words3 w0 w1 w2) (Relocatable.pointsTo64 w3)
  refine Relocatable.congr rfl (fun a => ?_) h
  ac_rfl

/-- `Relocatable 432` for 4 words `(w0, w1, w2, w3)` followed by `polyDecoderAt A (a + 32#64) dec`. -/
theorem Relocatable.words4_polyDecoderAt (A : RustAlloc)
    (w0 w1 w2 w3 : BitVec 64) (dec : PolyDecoder) :
    Relocatable 432 (fun a =>
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ polyDecoderAt A (a + 32#64) dec) := by
  have h := Relocatable.sepConj (off := 32#64) (m := 432) rfl rfl
    (Relocatable.words4 w0 w1 w2 w3) (Relocatable.of_polyDecoderAt A dec)
  refine Relocatable.congr rfl (fun a => ?_) h
  ac_rfl

/-- Expose `unchunkedCt1SentAt A a st` for cloning `st.ct1` while moving `st.auth`, `st.hdr`, `st.es`. -/
theorem unchunkedCt1Sent_expose_clone (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A a st ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ hdr0 : BitVec 64, ∃∗ hdr1 : BitVec 64, ∃∗ hdr2 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜st.ct1.length < 2 ^ 63⌝ ∗
        (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
        ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
        ((a + 48#64) ↦₆₄ hdr0) ∗ ((a + 56#64) ↦₆₄ hdr1) ∗ ((a + 64#64) ↦₆₄ hdr2) ∗
        ((a + 72#64) ↦₆₄ es0) ∗ ((a + 80#64) ↦₆₄ es1) ∗ ((a + 88#64) ↦₆₄ es2) ∗
        ((a + 96#64) ↦₆₄ cap_ct1) ∗ ((a + 104#64) ↦₆₄ ptr_ct1) ∗
        ((a + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((a + 120#64) ↦₆₄ st.epoch) ∗
        (ptr_ct1 ↦ₛ st.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 st.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 st.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 st.hdr ∗
        vecU8Heap A es0 es1 es2 st.es :=
  unchunkedCt1SentEkReceived_expose_clone A a
    { auth := st.auth, es := st.hdr, ek := st.es, ct1 := st.ct1, epoch := st.epoch }

/-- Expose `chunkedStatesAt A stA (.ct1Acknowledged s)` into tag `11#64`,
    the 12 kept words (`auth`, `hdr`, `es`) at `stA + 8..stA + 96`,
    the 432-byte relocated block (`ct1`, `epoch`, `receiving_ek`) at `stA + 104..stA + 536`,
    and trailing padding `memRegion (stA + 536#64) 392`. -/
theorem chunkedCt1Acknowledged_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ct1Acknowledged s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ hdr0 : BitVec 64, ∃∗ hdr1 : BitVec 64, ∃∗ hdr2 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
        (stA ↦₆₄ 11#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
         ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
         ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
        (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
         ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
         ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗
        memRegion (stA + 536#64) 392 := by
  dsimp only [chunkedStatesAt, chunkedCt1AcknowledgedAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (unchunkedCt1Sent_expose_clone A (stA + 8#64) s.uc)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  apply Entails.sepExists_elim; intro hdr0
  apply Entails.sepExists_elim; intro hdr1
  apply Entails.sepExists_elim; intro hdr2
  apply Entails.sepExists_elim; intro es0
  apply Entails.sepExists_elim; intro es1
  apply Entails.sepExists_elim; intro es2
  apply Entails.sepExists_elim; intro cap_ct1
  apply Entails.sepExists_elim; intro ptr_ct1
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right hdr0 (Entails.sepExists_right hdr1
          (Entails.sepExists_right hdr2 (Entails.sepExists_right es0
            (Entails.sepExists_right es1 (Entails.sepExists_right es2
              (Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 ?_)))))))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Recombine `stA` after Arm 9 (`ct1Acknowledged`) into `memRegion stA 928`. -/
theorem stA_ct1Acknowledged_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64) :
    (stA ↦₆₄ 11#64) ∗
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
     ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
     ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
    memRegion (stA + 104#64) 432 ∗
    memRegion (stA + 536#64) 392 ⊢
    memRegion stA chunkedStatesSize := by
  have h104 :
      (stA ↦₆₄ 11#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ⊢
      memRegion stA 104 := by
    rw [ProofLib.memRegion_cells stA 13 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right 11#64 (Entails.sepExists_right a0
      (Entails.sepExists_right a1 (Entails.sepExists_right a2
        (Entails.sepExists_right a3 (Entails.sepExists_right a4
          (Entails.sepExists_right a5 (Entails.sepExists_right hdr0
            (Entails.sepExists_right hdr1 (Entails.sepExists_right hdr2
              (Entails.sepExists_right es0 (Entails.sepExists_right es1
                (Entails.sepExists_right es2 ?_))))))))))))
    exact Entails.of_eq (by ac_rfl)
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 104) (k := 824)
        (b' := stA + 104#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 104#64) (n := 432) (k := 392)
        (b' := stA + 536#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    ((stA ↦₆₄ 11#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2))) ∗
    (memRegion (stA + 104#64) 432 ∗ memRegion (stA + 536#64) 392) by ac_rfl)) ?_
  exact sepConj_mono h104 (Entails.refl _)

/-- Scratch cells in `s0.sp - 480..s0.sp - 304` and `s0.sp - 256..s0.sp - 96` used by Arm 9 (`27` words):
    - `u0..u5` (`6` words at `s0.sp - 480..s0.sp - 432`, `[sp, #0x410..#0x440)`)
    - `v0..v8` (`9` words at `s0.sp - 424..s0.sp - 352`, `[sp, #0x448..#0x490)`)
    - `w0..w5` (`6` words at `s0.sp - 256..s0.sp - 208`, `[x29, #-0xa0..#-0x70)`)
    - `y0..y5` (`6` words at `s0.sp - 160..s0.sp - 112`, `[x29, #-0x40..#-0x10)`). -/
def ct1AcknowledgedScratchCells (sp : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64) : SepProp :=
  ((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗ ((sp - 464#64) ↦₆₄ u2) ∗
  ((sp - 456#64) ↦₆₄ u3) ∗ ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5) ∗
  ((sp - 424#64) ↦₆₄ v0) ∗ ((sp - 416#64) ↦₆₄ v1) ∗ ((sp - 408#64) ↦₆₄ v2) ∗
  ((sp - 400#64) ↦₆₄ v3) ∗ ((sp - 392#64) ↦₆₄ v4) ∗ ((sp - 384#64) ↦₆₄ v5) ∗
  ((sp - 376#64) ↦₆₄ v6) ∗ ((sp - 368#64) ↦₆₄ v7) ∗ ((sp - 360#64) ↦₆₄ v8) ∗
  ((sp - 256#64) ↦₆₄ w0) ∗ ((sp - 248#64) ↦₆₄ w1) ∗ ((sp - 240#64) ↦₆₄ w2) ∗
  ((sp - 232#64) ↦₆₄ w3) ∗ ((sp - 224#64) ↦₆₄ w4) ∗ ((sp - 216#64) ↦₆₄ w5) ∗
  ((sp - 160#64) ↦₆₄ y0) ∗ ((sp - 152#64) ↦₆₄ y1) ∗ ((sp - 144#64) ↦₆₄ y2) ∗
  ((sp - 136#64) ↦₆₄ y3) ∗ ((sp - 128#64) ↦₆₄ y4) ∗ ((sp - 120#64) ↦₆₄ y5)

theorem memRegion_ct1Acknowledged_scratch_split (sp : BitVec 64) :
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 ⊢
    ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
    ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
    ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
    ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
    ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v8 : BitVec 64,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ y0 : BitVec 64, ∃∗ y1 : BitVec 64, ∃∗ y2 : BitVec 64,
    ∃∗ y3 : BitVec 64, ∃∗ y4 : BitVec 64, ∃∗ y5 : BitVec 64,
      ct1AcknowledgedScratchCells sp
        u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
      memRegion (sp - 1360#64) 528 ∗
      memRegion (sp - 832#64) 352 ∗
      memRegion (sp - 432#64) 8 ∗
      memRegion (sp - 352#64) 40 ∗
      memRegion (sp - 312#64) 8 ∗
      memRegion (sp - 208#64) 48 ∗
      memRegion (sp - 112#64) 16 := by
  have h880 : memRegion (sp - 1360#64) 880 =
      memRegion (sp - 1360#64) 528 ∗ memRegion (sp - 832#64) 352 :=
    ProofLib.memRegion_split' (b := sp - 1360#64) (n := 528) (k := 352)
      (b' := sp - 832#64) rfl (by bv_omega) (by decide)
  have h176 : memRegion (sp - 480#64) 176 =
      cells (sp - 480#64) 6 ∗ memRegion (sp - 432#64) 8 ∗
      cells (sp - 424#64) 9 ∗ memRegion (sp - 352#64) 40 ∗
      memRegion (sp - 312#64) 8 := by
    rw [ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 128)
          (b' := sp - 432#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 432#64) (n := 8) (k := 120)
          (b' := sp - 424#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 424#64) (n := 72) (k := 48)
          (b' := sp - 352#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 352#64) (n := 40) (k := 8)
          (b' := sp - 312#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 480#64) 6 (by decide),
        ProofLib.memRegion_cells (sp - 424#64) 9 (by decide)]
  have h160 : memRegion (sp - 256#64) 160 =
      cells (sp - 256#64) 6 ∗ memRegion (sp - 208#64) 48 ∗
      cells (sp - 160#64) 6 ∗ memRegion (sp - 112#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 256#64) (n := 48) (k := 112)
          (b' := sp - 208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 208#64) (n := 48) (k := 64)
          (b' := sp - 160#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 160#64) (n := 48) (k := 16)
          (b' := sp - 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 256#64) 6 (by decide),
        ProofLib.memRegion_cells (sp - 160#64) 6 (by decide)]
  rw [h880, h176, h160]
  unfold ct1AcknowledgedScratchCells
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  apply Entails.sepExists_elim; intro y0
  apply Entails.sepExists_elim; intro y1
  apply Entails.sepExists_elim; intro y2
  apply Entails.sepExists_elim; intro y3
  apply Entails.sepExists_elim; intro y4
  apply Entails.sepExists_elim; intro y5
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro v0
  apply Entails.sepExists_elim; intro v1
  apply Entails.sepExists_elim; intro v2
  apply Entails.sepExists_elim; intro v3
  apply Entails.sepExists_elim; intro v4
  apply Entails.sepExists_elim; intro v5
  apply Entails.sepExists_elim; intro v6
  apply Entails.sepExists_elim; intro v7
  apply Entails.sepExists_elim; intro v8
  apply Entails.sepExists_elim; intro u0
  apply Entails.sepExists_elim; intro u1
  apply Entails.sepExists_elim; intro u2
  apply Entails.sepExists_elim; intro u3
  apply Entails.sepExists_elim; intro u4
  apply Entails.sepExists_elim; intro u5
  refine Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5
        (Entails.sepExists_right v0 (Entails.sepExists_right v1
          (Entails.sepExists_right v2 (Entails.sepExists_right v3
            (Entails.sepExists_right v4 (Entails.sepExists_right v5
              (Entails.sepExists_right v6 (Entails.sepExists_right v7
                (Entails.sepExists_right v8 (Entails.sepExists_right w0
                  (Entails.sepExists_right w1 (Entails.sepExists_right w2
                    (Entails.sepExists_right w3 (Entails.sepExists_right w4
                      (Entails.sepExists_right w5 (Entails.sepExists_right y0
                        (Entails.sepExists_right y1 (Entails.sepExists_right y2
                          (Entails.sepExists_right y3 (Entails.sepExists_right y4
                            (Entails.sepExists_right y5 ?_))))))))))))))))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem ct1AcknowledgedScratchCells_entails_memRegions (sp : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (c0 c1 c2 c3 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64) :
    ct1AcknowledgedScratchCells sp
      u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
      w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
    (((sp - 1264#64) ↦₆₄ c0) ∗ ((sp - 1256#64) ↦₆₄ c1) ∗
     ((sp - 1248#64) ↦₆₄ c2) ∗ ((sp - 1240#64) ↦₆₄ c3)) ∗
    (((sp - 352#64) ↦₆₄ d0) ∗ ((sp - 344#64) ↦₆₄ d1) ∗
     ((sp - 336#64) ↦₆₄ d2) ∗ ((sp - 328#64) ↦₆₄ d3) ∗
     ((sp - 320#64) ↦₆₄ d4)) ∗
    memRegion (sp - 1360#64) 96 ∗
    memRegion (sp - 1232#64) 400 ∗
    memRegion (sp - 832#64) 352 ∗
    memRegion (sp - 432#64) 8 ∗
    memRegion (sp - 312#64) 8 ∗
    memRegion (sp - 208#64) 48 ∗
    memRegion (sp - 112#64) 16 ⊢
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 := by
  have hc4 :
      ((sp - 1264#64) ↦₆₄ c0) ∗ ((sp - 1256#64) ↦₆₄ c1) ∗
      ((sp - 1248#64) ↦₆₄ c2) ∗ ((sp - 1240#64) ↦₆₄ c3) ⊢
      memRegion (sp - 1264#64) 32 := by
    rw [ProofLib.memRegion_cells (sp - 1264#64) 4 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right c3 (Entails.of_eq (by ac_rfl)))))
  have hd5 :
      ((sp - 352#64) ↦₆₄ d0) ∗ ((sp - 344#64) ↦₆₄ d1) ∗
      ((sp - 336#64) ↦₆₄ d2) ∗ ((sp - 328#64) ↦₆₄ d3) ∗
      ((sp - 320#64) ↦₆₄ d4) ⊢
      memRegion (sp - 352#64) 40 := by
    rw [ProofLib.memRegion_cells (sp - 352#64) 5 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d4 (Entails.of_eq (by ac_rfl))))))
  have hu6 :
      ((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗ ((sp - 464#64) ↦₆₄ u2) ∗
      ((sp - 456#64) ↦₆₄ u3) ∗ ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5) ⊢
      memRegion (sp - 480#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 480#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
        (Entails.sepExists_right u4 (Entails.sepExists_right u5 (Entails.of_eq (by ac_rfl)))))))
  have hv9 :
      ((sp - 424#64) ↦₆₄ v0) ∗ ((sp - 416#64) ↦₆₄ v1) ∗ ((sp - 408#64) ↦₆₄ v2) ∗
      ((sp - 400#64) ↦₆₄ v3) ∗ ((sp - 392#64) ↦₆₄ v4) ∗ ((sp - 384#64) ↦₆₄ v5) ∗
      ((sp - 376#64) ↦₆₄ v6) ∗ ((sp - 368#64) ↦₆₄ v7) ∗ ((sp - 360#64) ↦₆₄ v8) ⊢
      memRegion (sp - 424#64) 72 := by
    rw [ProofLib.memRegion_cells (sp - 424#64) 9 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1
      (Entails.sepExists_right v2 (Entails.sepExists_right v3
        (Entails.sepExists_right v4 (Entails.sepExists_right v5
          (Entails.sepExists_right v6 (Entails.sepExists_right v7
            (Entails.sepExists_right v8 (Entails.of_eq (by ac_rfl))))))))))
  have hw6 :
      ((sp - 256#64) ↦₆₄ w0) ∗ ((sp - 248#64) ↦₆₄ w1) ∗ ((sp - 240#64) ↦₆₄ w2) ∗
      ((sp - 232#64) ↦₆₄ w3) ∗ ((sp - 224#64) ↦₆₄ w4) ∗ ((sp - 216#64) ↦₆₄ w5) ⊢
      memRegion (sp - 256#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 256#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.of_eq (by ac_rfl)))))))
  have hy6 :
      ((sp - 160#64) ↦₆₄ y0) ∗ ((sp - 152#64) ↦₆₄ y1) ∗ ((sp - 144#64) ↦₆₄ y2) ∗
      ((sp - 136#64) ↦₆₄ y3) ∗ ((sp - 128#64) ↦₆₄ y4) ∗ ((sp - 120#64) ↦₆₄ y5) ⊢
      memRegion (sp - 160#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 160#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right y0 (Entails.sepExists_right y1
      (Entails.sepExists_right y2 (Entails.sepExists_right y3
        (Entails.sepExists_right y4 (Entails.sepExists_right y5 (Entails.of_eq (by ac_rfl)))))))
  rw [ProofLib.memRegion_split' (b := sp - 1360#64) (n := 96) (k := 784)
        (b' := sp - 1264#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1264#64) (n := 32) (k := 752)
        (b' := sp - 1232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1232#64) (n := 400) (k := 352)
        (b' := sp - 832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 128)
        (b' := sp - 432#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 432#64) (n := 8) (k := 120)
        (b' := sp - 424#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 424#64) (n := 72) (k := 48)
        (b' := sp - 352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 352#64) (n := 40) (k := 8)
        (b' := sp - 312#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 256#64) (n := 48) (k := 112)
        (b' := sp - 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 208#64) (n := 48) (k := 64)
        (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 48) (k := 16)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide)]
  unfold ct1AcknowledgedScratchCells
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp - 1264#64) ↦₆₄ c0) ∗ ((sp - 1256#64) ↦₆₄ c1) ∗
     ((sp - 1248#64) ↦₆₄ c2) ∗ ((sp - 1240#64) ↦₆₄ c3)) ∗
    (((sp - 352#64) ↦₆₄ d0) ∗ ((sp - 344#64) ↦₆₄ d1) ∗
     ((sp - 336#64) ↦₆₄ d2) ∗ ((sp - 328#64) ↦₆₄ d3) ∗
     ((sp - 320#64) ↦₆₄ d4)) ∗
    (((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗ ((sp - 464#64) ↦₆₄ u2) ∗
     ((sp - 456#64) ↦₆₄ u3) ∗ ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5)) ∗
    (((sp - 424#64) ↦₆₄ v0) ∗ ((sp - 416#64) ↦₆₄ v1) ∗ ((sp - 408#64) ↦₆₄ v2) ∗
     ((sp - 400#64) ↦₆₄ v3) ∗ ((sp - 392#64) ↦₆₄ v4) ∗ ((sp - 384#64) ↦₆₄ v5) ∗
     ((sp - 376#64) ↦₆₄ v6) ∗ ((sp - 368#64) ↦₆₄ v7) ∗ ((sp - 360#64) ↦₆₄ v8)) ∗
    (((sp - 256#64) ↦₆₄ w0) ∗ ((sp - 248#64) ↦₆₄ w1) ∗ ((sp - 240#64) ↦₆₄ w2) ∗
     ((sp - 232#64) ↦₆₄ w3) ∗ ((sp - 224#64) ↦₆₄ w4) ∗ ((sp - 216#64) ↦₆₄ w5)) ∗
    (((sp - 160#64) ↦₆₄ y0) ∗ ((sp - 152#64) ↦₆₄ y1) ∗ ((sp - 144#64) ↦₆₄ y2) ∗
     ((sp - 136#64) ↦₆₄ y3) ∗ ((sp - 128#64) ↦₆₄ y4) ∗ ((sp - 120#64) ↦₆₄ y5)) ∗
    (memRegion (sp - 1360#64) 96 ∗
     memRegion (sp - 1232#64) 400 ∗
     memRegion (sp - 832#64) 352 ∗
     memRegion (sp - 432#64) 8 ∗
     memRegion (sp - 312#64) 8 ∗
     memRegion (sp - 208#64) 48 ∗
     memRegion (sp - 112#64) 16) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hc4 (sepConj_mono hd5 (sepConj_mono hu6
      (sepConj_mono hv9 (sepConj_mono hw6 (sepConj_mono hy6 (Entails.refl _))))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Reassemble the 28 output words of `out` for Arm 9 (`States.ct1Acknowledged`) into
    `optProtoInnerStateAt A out (States.ct1Acknowledged s).into_pb.innerState`. -/
theorem outWords28_entails_ct1Acknowledged (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (hdr0 hdr1 hdr2 es0 es1 es2 ct1_0 ct1_1 ct1_2 a0 a1 a2 a3 a4 a5 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000009#64
      hdr0 hdr1 hdr2 es0 es1 es2 ct1_0
      ct1_1 ct1_2 a0 a1 a2 a3 a4 a5
      s.uc.epoch d0 d1 d2 d3 d4 w176 w184
      w192 w200 w208 w216 ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
    vecU8Heap A es0 es1 es2 s.uc.es ∗
    vecU8Heap A ct1_0 ct1_1 ct1_2 s.uc.ct1 ⊢
    optProtoInnerStateAt A out (States.ct1Acknowledged s).into_pb.innerState := by
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 136#64)
    d0 d1 d2 d3 d4 s.receiving_ek.intoPb
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdec
  have hauth := authenticatorAt_of_words_heap A (out + 80#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hauth
  have hhdr := vecU8_of_words_heap A (out + 8#64) hdr0 hdr1 hdr2 s.uc.hdr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr
  have hes := vecU8_of_words_heap A (out + 32#64) es0 es1 es2 s.uc.es
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hes
  have hct1 := vecU8_of_words_heap A (out + 56#64) ct1_0 ct1_1 ct1_2 s.uc.ct1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hct1
  have h48 :
      ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 176#64) 48 := by
    rw [ProofLib.memRegion_cells (out + 176#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w176 (Entails.sepExists_right w184
      (Entails.sepExists_right w192 (Entails.sepExists_right w200
        (Entails.sepExists_right w208 (Entails.sepExists_right w216 (Entails.of_eq (by ac_rfl)))))))
  dsimp only [States.into_pb, Chunked.SendCt.Ct1Acknowledged.into_pb,
    Unchunked.SendCt.Ct1Sent.into_pb,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt,
    optProtoUnchunkedCt1SentAt, protoUnchunkedCt1SentAt,
    optProtoPolynomialDecoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000009#64) ∗
    (((out + 8#64) ↦₆₄ hdr0) ∗ ((out + 16#64) ↦₆₄ hdr1) ∗ ((out + 24#64) ↦₆₄ hdr2) ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr) ∗
    (((out + 32#64) ↦₆₄ es0) ∗ ((out + 40#64) ↦₆₄ es1) ∗ ((out + 48#64) ↦₆₄ es2) ∗
     vecU8Heap A es0 es1 es2 s.uc.es) ∗
    (((out + 56#64) ↦₆₄ ct1_0) ∗ ((out + 64#64) ↦₆₄ ct1_1) ∗ ((out + 72#64) ↦₆₄ ct1_2) ∗
     vecU8Heap A ct1_0 ct1_1 ct1_2 s.uc.ct1) ∗
    (((out + 80#64) ↦₆₄ a0) ∗ ((out + 88#64) ↦₆₄ a1) ∗
     ((out + 96#64) ↦₆₄ a2) ∗ ((out + 104#64) ↦₆₄ a3) ∗
     ((out + 112#64) ↦₆₄ a4) ∗ ((out + 120#64) ↦₆₄ a5) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((out + 128#64) ↦₆₄ s.uc.epoch) ∗
    (((out + 136#64) ↦₆₄ d0) ∗ ((out + 144#64) ↦₆₄ d1) ∗
     ((out + 152#64) ↦₆₄ d2) ∗ ((out + 160#64) ↦₆₄ d3) ∗
     ((out + 168#64) ↦₆₄ d4) ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb) ∗
    (((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
     ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
     ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hhdr (sepConj_mono hes (sepConj_mono hct1
      (sepConj_mono hauth (sepConj_mono_right (sepConj_mono hdec h48))))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Step Lemmas for Arm 9 (`+60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544`) -/

/-- Step 1b (`+60 -> +372`): jump-table dispatch for tag `11#64` (index `9` -> `+360`) and setup
    for `memcpy(s0.sp - 1360, stA + 8, 528)` at `+372`. -/
theorem ct1Acknowledged_step_60_to_372 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (Rest : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (hx8 : s.readReg64 .x8 = 11#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy")) s
      (statesIntoPbJumpTableAt b ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ statesIntoPbJumpTableAt b ∗ Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 376#64 ∧
        sm.readReg64 .x0 = s0.sp - 1360#64 ∧
        sm.readReg64 .x1 = stA + 8#64 ∧
        (sm.readReg64 .x2).toNat = 528 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hadrp := fnAddr_adrp_5ce6c (H := Rust.withPanics ext) hb
  states_into_pb_fetches_range b (Rust.withPanics ext) 60 40
  states_into_pb_fetches_range b (Rust.withPanics ext) 360 16
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hadrp hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Step 2 (`+376 -> +424`): load `cap_ct1`, `ptr_ct1`, `len_ct1`, `epoch` from `s0.sp - 1264..1240`,
    copy `a0..a5` from `stA + 8..48` to `s0.sp - 480..440` (`u0..u5`), and take fallthrough of
    `tbnz x21, #0x3f, +1696`. -/
theorem ct1Acknowledged_step_376_to_424 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 epoch : BitVec 64)
    (len_ct1 : Nat)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : len_ct1 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 376#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 424#64) s
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
        ((s0.sp - 1240#64) ↦₆₄ epoch)) ∗
       ct1AcknowledgedScratchCells s0.sp
         u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
           ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 len_ct1) ∗
           ((s0.sp - 1240#64) ↦₆₄ epoch)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 len_ct1 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hmsb := ofNat_lt_2pow63_msb_zero hlen
  have hand := ofNat_lt_2pow63_and_highBit_zero hlen
  have hlsr := ofNat_lt_2pow63_lsr63_zero hlen
  states_into_pb_fetches_range b (Rust.withPanics ext) 376 48
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    ct1AcknowledgedScratchCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

/-- Step 3 (`+424 -> +1812`): clone `s.uc.ct1`. -/
theorem ct1Acknowledged_step_424_to_1812
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 epoch : BitVec 64)
    (ct1 : List (BitVec 8))
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : ct1.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (ptr_new : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1812#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x28 = s0.sp - 256#64 →
      sm.readReg64 .x27 = epoch →
      sm.readReg64 .x26 = s0.sp - 480#64 →
      sm.readReg64 .x24 = ptr_ct1 →
      sm.readReg64 .x23 = cap_ct1 →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x19 = out →
      TraceCalleeSaved sm s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        (vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_new (BitVec.ofNat 64 ct1.length) ct1 ∗
         vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      ((ptr_ct1 ↦ₛ ct1) ∗
       vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  by_cases hlen_zero : ct1.length = 0
  · have hnil : ct1 = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx21 hlen hnext ⊢
    refine DecoderPb.SepWPp.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1812#64)
      (P_mid :=
        vecU8Heap A 0#64 1#64 0#64 [] ∗
        vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x28 = s0.sp - 256#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x22 = 1#64 ∧
        sm.readReg64 .x21 = 0#64 ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_into_pb_fetches_range b (Rust.withPanics ext) 424 4
      states_into_pb_fetches_range b (Rust.withPanics ext) 1808 4
      dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::into_pb" = entry
      examples_hide_fetches
      wp_steps
      have hdealloc := vecU8CloneTail_entails_dealloc A cap_ct1 ptr_ct1 []
      have hnil := vecU8Heap_nil_intro A
        (vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hnil
      have hent :
          (ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 [] ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame ⊢
          vecU8Heap A 0#64 1#64 0#64 [] ∗
          vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
        rw [show (ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 [] ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame =
            ((ptr_ct1 ↦ₛ []) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 []) ∗
            (A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by ac_rfl]
        exact Entails.trans (sepConj_mono_left hdealloc) hnil
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx28m, hx27m, hx26m, hx24m, hx23m,
        hx22m, hx21m, hx20m, hx19m, htrm⟩
      exact hnext sm 1#64 hpcm hrunm hspm hx29m hx28m hx27m hx26m hx24m hx23m
        hx22m hx21m hx20m hx19m htrm
  · have hpos : 0 < ct1.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 ct1.length == 0#64) = false :=
      ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 ct1.length != 0#64) = true :=
      ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 ct1.length).toNat = ct1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk ct1.length 1 := ⟨hpos, hpow2, by omega⟩
    have hshim := shim_ok_at2_ext hA (name := statesIntoPbName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := alloc_ok_at_norm_ext hA (name := statesIntoPbName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_alloc"))
    have hmemcpy := memcpy_ok_at2_ext hA (name := statesIntoPbName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1700#64 →
        sm.status = .Running →
        sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm P_mid Q
          (StatesIntoPbPanic s0 R) := by
      intro sm P_mid hpcm hrunm htrm
      have heq : (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) =
          StatesIntoPbPanic s0 R := by
        funext sf P_f
        simp only [StatesIntoPbPanic, statesIntoPbOnPanic, sepConj_assoc]
      rw [← heq]
      exact states_into_pb_panic_1700 s0 sm P_mid R hpcm hrunm htrm
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    states_into_pb_fetches_range b (Rust.withPanics ext) 424 48
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpanic ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 448#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine DecoderPb.SepWPp.seq_clean (mid := entry + 1700#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          (ptr_ct1 ↦ₛ ct1) ∗
          vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true :=
        bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine DecoderPb.SepWPp.seq_clean (mid := entry + 1812#64)
        (P_mid :=
          vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_c
            (BitVec.ofNat 64 ct1.length) ct1 ∗
          vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x28 = s0.sp - 256#64 ∧
          sm.readReg64 .x27 = epoch ∧
          sm.readReg64 .x26 = s0.sp - 480#64 ∧
          sm.readReg64 .x24 = ptr_ct1 ∧
          sm.readReg64 .x23 = cap_ct1 ∧
          sm.readReg64 .x22 = ptr_c ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 ct1.length ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · wp_steps
        wp_apply
        wp_steps
        have hbuf := vecU8Heap_of_exact_alloc A ptr_c ct1 hpos hlen hoom
        have hdealloc := vecU8CloneTail_entails_dealloc A cap_ct1 ptr_ct1 ct1
        have hent :
            (ptr_c ↦ₛ ct1) ∗ (ptr_ct1 ↦ₛ ct1) ∗
            A.pool ∗ stackAt sf.sp allocHookStack ∗
            A.live ptr_c ct1.length 1 ∗
            vecU8CloneTail A cap_ct1 ptr_ct1 ct1 ∗ Frame ⊢
            vecU8Heap A (BitVec.ofNat 64 ct1.length) ptr_c
              (BitVec.ofNat 64 ct1.length) ct1 ∗
            vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame := by
          rw [‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            ((ptr_c ↦ₛ ct1) ∗ A.live ptr_c ct1.length 1) ∗
            ((ptr_ct1 ↦ₛ ct1) ∗ vecU8CloneTail A cap_ct1 ptr_ct1 ct1) ∗
            (A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) by ac_rfl)) ?_
          exact sepConj_mono hbuf (sepConj_mono hdealloc (Entails.refl _))
        exact SepWP.weaken_pre hent (by wp_done)
      · intro sm hpcm hrunm ⟨hspm, hx29m, hx28m, hx27m, hx26m, hx24m, hx23m,
          hx22m, hx21m, hx20m, hx19m, htrm⟩
        exact hnext sm ptr_c hpcm hrunm hspm hx29m hx28m hx27m hx26m hx24m hx23m
          hx22m hx21m hx20m hx19m htrm

/-- Step 4 (`+1812 -> +1900`): move `a0..a5` from `s0.sp - 480..440` (`u0..u5`) to
    `s0.sp - 160..120` (`y0..y5`), copy `hdr0..hdr2, es0..es2` from `stA + 56..96` to
    `s0.sp - 256..216` (`w0..w5`), deallocate `(cap_ct1, ptr_ct1)` via `__rust_dealloc`,
    and set up `<PolyDecoder>::into_pb(s0.sp - 352, s0.sp - 1232)` at `+1900` (`+25104`). -/
theorem ct1Acknowledged_step_1812_to_1900
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (out stA cap_ct1 ptr_ct1 ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1812#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s.readReg64 .x24 = ptr_ct1)
    (hx23 : s.readReg64 .x23 = cap_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx20 : s.readReg64 .x20 = stA)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64) s
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
       vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
           ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
           ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
          ct1AcknowledgedScratchCells s0.sp
            a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1904#64 ∧
        sm.readReg64 .x0 = s0.sp - 352#64 ∧
        sm.readReg64 .x1 = s0.sp - 1232#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x27 = epoch ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hdealloc := dealloc_ok_at_norm_ext hA (name := statesIntoPbName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "__rustc::__rust_dealloc"))
  simp only [rustDeallocSpec] at hdealloc
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_into_pb_fetches_range b (Rust.withPanics ext) 1812 92
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, ct1AcknowledgedScratchCells,
    vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  by_cases hc : (cap_ct1 == 0#64) = true
  · have hc_bne : (cap_ct1 != 0#64) = false := by
      rcases eq_or_ne cap_ct1 0#64 with rfl | hne
      · rfl
      · exact False.elim (hne (beq_iff_eq.mp hc))
    simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]
    wp_steps
    refine DropGlueFacts.align_pre (by ac_rfl) ?_
    wp_done
  · have hc_beq : (cap_ct1 == 0#64) = false := Bool.eq_false_iff.mpr hc
    have hc_bne : (cap_ct1 != 0#64) = true := by
      rw [bne_iff_ne]; intro h; exact hc (beq_iff_eq.mpr h)
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    wp_apply
    wp_steps
    refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
    wp_done

/-- Step 5 (`+1904 -> +1544`): pack `hdr`, `es`, `ct1`, `auth`, `epoch`, and `receiving_ek.intoPb`
    into `epilogueStagingCells` and branch to `+1544`. -/
theorem ct1Acknowledged_step_1904_to_1544 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out ptr_new len_ct1 epoch : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : s.readReg64 .x27 = epoch)
    (hx26 : s.readReg64 .x26 = s0.sp - 480#64)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) s
      (ct1AcknowledgedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
        ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
        ((s0.sp - 320#64) ↦₆₄ d4)) ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       Rest)
      (fun sm Pm =>
        (Pm ⊢
          ct1AcknowledgedScratchCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5 epoch
            hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
          (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
           ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
           ((s0.sp - 320#64) ↦₆₄ d4)) ∗
          epilogueStagingCells s0.sp
            hdr0 hdr1 hdr2 es0 es1 es2
            ptr_new len_ct1 a0 a1 a2 a3 a4 a5
            epoch d0 d1 d2 d3 d4 w176 w184
            w192 w200 w208 w216 ∗
          Rest) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = len_ct1 ∧
        sm.readReg64 .x22 = 0x8000000000000009#64 ∧
        TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_into_pb_fetches_range b (Rust.withPanics ext) 1904 120
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    ct1AcknowledgedScratchCells, epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  refine DropGlueFacts.align_pre (by ac_rfl) ?_
  wp_done

end CryptoVerification.SpqrV1.States.IntoPb

