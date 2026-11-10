/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Specifications.AsmConstants

/-!
# Exact `SignalProtocolError` Result Layouts and Copy Lemmas for `PreKeySignalMessage::try_from`

Defines the 248-byte `Err(e)` layout `pksmErrE` at `sret`, bridges it to `RunCompose.pksmResAt`,
and proves cell-packing and 48-byte word-for-word `speAt` copy lemmas (`pksm0c_speAt_detach`,
`errCopy48_entails_pksmErrE`) across all error exits.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.SignalSession.Cli

/-! ## 1. Exact Err Result at `sret` (`pksmErrE`) and `pksmResAt` Bridge -/

/-- Exact 248-byte `Err(e)` result layout at `r` for `PreKeySignalMessage::try_from`:
niche `errTag` at `r`, 48-byte `speAt A fn (r + 8) e`, and 192 unspecified trailing bytes at
`r + 56`. -/
def pksmErrE (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (r ↦₆₄ errTag) ∗ speAt A fn (r + 8#64) e ∗ memRegion (r + 56#64) 192

/-- `pksmErrE A fn r e ∗ anyHeap` entails `RunCompose.pksmResAt A r none` by witnessing `fn`
and `e`. -/
theorem pksmErrE_entails_resAt_none (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (e : SignalProtocolError) :
    pksmErrE A fn r e ∗ anyHeap ⊢ RunCompose.pksmResAt A r none := by
  unfold pksmErrE RunCompose.pksmResAt
  have hex : speAt A fn (r + 8#64) e ⊢
      ∃∗ fn' : List (BitVec 8), ∃∗ e' : SignalProtocolError, speAt A fn' (r + 8#64) e' :=
    Entails.sepExists_right fn (Entails.sepExists_right e (Entails.refl _))
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_left hex)

/-- Any residual heap/rodata frame `R` alongside `pksmErrE A fn r e` absorbs into `anyHeap` to
produce `RunCompose.pksmResAt A r none`. -/
theorem pksm0c_pksmErrE_frame_entails_resAt_none (A : RustAlloc) (fn : List (BitVec 8))
    (r : BitVec 64) (e : SignalProtocolError) (R : SepProp) :
    pksmErrE A fn r e ∗ R ⊢ RunCompose.pksmResAt A r none :=
  Entails.trans (sepConj_mono_right (entails_anyHeap R))
    (pksmErrE_entails_resAt_none A fn r e)

/-! ## 2. Private Byte/Word/Region Splitting & Merging Helpers -/

private theorem pksm0c_sepConj_pure_of_true {φ : Prop} (h : φ) (P : SepProp) :
    (P ∗ ⌜φ⌝) = P := by
  rw [sepConj_comm, pure_sepConj_of_true h P]

private theorem pksm0c_pure_intro_emp {φ : Prop} (h : φ) : emp ⊢ (⌜φ⌝ : SepProp) := by
  have heq := pure_sepConj_of_true h emp
  rw [sepConj_emp] at heq
  exact Entails.of_eq heq.symm

private theorem pksm0c_false_entails {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q :=
  Entails.trans (Entails.of_eq (sepConj_emp (⌜False⌝ : SepProp)).symm)
    (Entails.pure_left False.elim)

private theorem pksm0c_pointsTo64_to_truncate8_memRegion7 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.truncate 8) ∗ memRegion (a + 1#64) 7 := by
  have hw : w = w.extractLsb' 8 56 ++ w.truncate 8 := by bv_bits
  conv => lhs; rw [hw]
  exact pointsTo64_to_8_memRegion7 a (w.extractLsb' 8 56) (w.truncate 8)

private theorem pksm0c_pointsTo64_to_byte_memRegion7 (a w : BitVec 64) (b : BitVec 8)
    (hb : w.truncate 8 = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  subst hb
  exact pksm0c_pointsTo64_to_truncate8_memRegion7 a w

private theorem pksm0c_word_exact (a x : BitVec 64) :
    (a ↦₆₄ x) ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜w = x⌝ :=
  Entails.sepExists_right x (Entails.of_eq (pksm0c_sepConj_pure_of_true rfl (a ↦₆₄ x)).symm)

private theorem pksm0c_word_any (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜True⌝ := by
  rw [ProofLib.memRegion_eight a]
  exact Entails.sepExists_elim fun w =>
    Entails.sepExists_right w (Entails.of_eq (sepConj_pure_true (a ↦₆₄ w)).symm)

private theorem pksm0c_word_byte (a : BitVec 64) (b : BitVec 8) :
    ((a ↦₈ b) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜w.truncate 8 = b⌝ := by
  refine Entails.trans (pointsTo8_memRegion7_to_64 a b) ?_
  refine Entails.sepExists_elim fun hi => ?_
  have htr : (hi ++ b).truncate 8 = b := by bv_bits
  exact Entails.sepExists_right (hi ++ b)
    (Entails.of_eq (pksm0c_sepConj_pure_of_true htr (a ↦₆₄ (hi ++ b))).symm)

private theorem pksm0c_word_pair32 (a : BitVec 64) (i c : BitVec 32) :
    ((a ↦₃₂ i) ∗ ((a + 4#64) ↦₃₂ c)) ⊢
      ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜w = c ++ i⌝ := by
  rw [pointsTo32_merge64 a i c]
  exact pksm0c_word_exact a (c ++ i)

private theorem pksm0c_zext8_truncate8 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 8 = b := by bv_bits

private theorem pksm0c_memRegion_words2 (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ⊢ memRegion a 16 := by
  rw [ProofLib.memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (pointsTo64_entails_memRegion (a + 8#64) w1)

private theorem pksm0c_memRegion_words3 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split a 8 16 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pksm0c_memRegion_words2 (a + 8#64) w1 w2)

private theorem pksm0c_memRegion_words4 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split a 8 24 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pksm0c_memRegion_words3 (a + 8#64) w1 w2 w3)

private theorem pksm0c_memRegion_words5 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pksm0c_memRegion_words4 (a + 8#64) w1 w2 w3 w4)

private theorem pksm0c_memRegion24_split8 (a : BitVec 64) :
    memRegion a 24 = memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem pksm0c_memRegion32_split8 (a : BitVec 64) :
    memRegion a 32 =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗
        memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8 := by
  rw [ProofLib.memRegion_split a 8 24 (by decide), pksm0c_memRegion24_split8 (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem pksm0c_memRegion40_split8 (a : BitVec 64) :
    memRegion a 40 =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗
        memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 8 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide), pksm0c_memRegion32_split8 (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 3. Cell-to-`pksmErrE` Packing Lemmas (–) -/

/-- `speWord 2` (`InvalidProtobufEncoding`) at `r + 8` and `232` plain trailing
bytes at `r + 16` pack into `pksmErrE A fn r .invalidProtobufEncoding`. -/
theorem errCells_invalidProtobufEncoding (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 2) ∗ memRegion (r + 16#64) 232 ⊢
      pksmErrE A fn r .invalidProtobufEncoding := by
  unfold pksmErrE speAt
  rw [show (232 : Nat) = 40 + 192 by decide,
    ProofLib.memRegion_split (r + 16#64) 40 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 3` at `r + 8` and `BitVec.ofNat 64 n` at `r + 16` (`0#64` when `n = 0`)
pack into `pksmErrE A fn r (.ciphertextMessageTooShort n)`. -/
theorem errCells_tooShort (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64) (n : Nat) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 3) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (r + 24#64) 224 ⊢
      pksmErrE A fn r (.ciphertextMessageTooShort n) := by
  unfold pksmErrE speAt
  rw [show (224 : Nat) = 32 + 192 by decide,
    ProofLib.memRegion_split (r + 24#64) 32 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 4` at `r + 8` and version byte `v` at `r + 16` (`strb`) pack into
`pksmErrE A fn r (.legacyCiphertextVersion v)`. -/
theorem errCells_legacyVersion (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (v : BitVec 8) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 4) ∗ ((r + 16#64) ↦₈ v) ∗
      memRegion (r + 17#64) 231 ⊢
      pksmErrE A fn r (.legacyCiphertextVersion v) := by
  unfold pksmErrE speAt
  rw [show (231 : Nat) = 39 + 192 by decide,
    ProofLib.memRegion_split (r + 17#64) 39 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- Word-form companion of `errCells_legacyVersion` when `r + 16` holds a 64-bit word `w` with low
byte `v`. -/
theorem pksm0c_errCells_legacyVersion_word (A : RustAlloc) (fn : List (BitVec 8))
    (r w : BitVec 64) (v : BitVec 8) (hv : w.truncate 8 = v) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 4) ∗ ((r + 16#64) ↦₆₄ w) ∗
      memRegion (r + 24#64) 224 ⊢
      pksmErrE A fn r (.legacyCiphertextVersion v) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pksm0c_pointsTo64_to_byte_memRegion7 (r + 16#64) w v hv)))) ?_
  refine Entails.trans ?_ (errCells_legacyVersion A fn r v)
  rw [show (231 : Nat) = 7 + 224 by decide,
    ProofLib.memRegion_split (r + 17#64) 7 224 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 5` at `r + 8` and version byte `v` at `r + 16` (`strb`) pack into
`pksmErrE A fn r (.unrecognizedCiphertextVersion v)`. -/
theorem errCells_unrecognizedVersion (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (v : BitVec 8) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 5) ∗ ((r + 16#64) ↦₈ v) ∗
      memRegion (r + 17#64) 231 ⊢
      pksmErrE A fn r (.unrecognizedCiphertextVersion v) := by
  unfold pksmErrE speAt
  rw [show (231 : Nat) = 39 + 192 by decide,
    ProofLib.memRegion_split (r + 17#64) 39 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- Word-form companion of `errCells_unrecognizedVersion` when `r + 16` holds a 64-bit word `w`
with low byte `v`. -/
theorem pksm0c_errCells_unrecognizedVersion_word (A : RustAlloc) (fn : List (BitVec 8))
    (r w : BitVec 64) (v : BitVec 8) (hv : w.truncate 8 = v) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 5) ∗ ((r + 16#64) ↦₆₄ w) ∗
      memRegion (r + 24#64) 224 ⊢
      pksmErrE A fn r (.unrecognizedCiphertextVersion v) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pksm0c_pointsTo64_to_byte_memRegion7 (r + 16#64) w v hv)))) ?_
  refine Entails.trans ?_ (errCells_unrecognizedVersion A fn r v)
  rw [show (231 : Nat) = 7 + 224 by decide,
    ProofLib.memRegion_split (r + 17#64) 7 224 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 7` (`NoKeyTypeIdentifier`) at `r + 8` and `232` plain trailing bytes at
`r + 16` pack into `pksmErrE A fn r .noKeyTypeIdentifier`. -/
theorem errCells_noKeyType (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 7) ∗ memRegion (r + 16#64) 232 ⊢
      pksmErrE A fn r .noKeyTypeIdentifier := by
  unfold pksmErrE speAt
  rw [show (232 : Nat) = 40 + 192 by decide,
    ProofLib.memRegion_split (r + 16#64) 40 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- Byte-form companion of `errCells_badKeyType` when `r + 16` holds `(r + 16) ↦₈ t`. -/
theorem pksm0c_errCells_badKeyType_byte (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (t : BitVec 8) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₈ t) ∗
      memRegion (r + 17#64) 231 ⊢
      pksmErrE A fn r (.badKeyType t) := by
  unfold pksmErrE speAt
  rw [show (231 : Nat) = 39 + 192 by decide,
    ProofLib.memRegion_split (r + 17#64) 39 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- General word-form companion of `errCells_badKeyType` for any 64-bit word `w` at `r + 16` with
`w.truncate 8 = t` (including both `t.zeroExtend 64` and `bfxil`/`orr`-merged words). -/
theorem pksm0c_errCells_badKeyType_word (A : RustAlloc) (fn : List (BitVec 8)) (r w : BitVec 64)
    (t : BitVec 8) (ht : w.truncate 8 = t) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₆₄ w) ∗
      memRegion (r + 24#64) 224 ⊢
      pksmErrE A fn r (.badKeyType t) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pksm0c_pointsTo64_to_byte_memRegion7 (r + 16#64) w t ht)))) ?_
  refine Entails.trans ?_ (pksm0c_errCells_badKeyType_byte A fn r t)
  rw [show (231 : Nat) = 7 + 224 by decide,
    ProofLib.memRegion_split (r + 17#64) 7 224 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 8` at `r + 8` and `t.zeroExtend 64` at `r + 16` pack into
`pksmErrE A fn r (.badKeyType t)`. -/
theorem errCells_badKeyType (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (t : BitVec 8) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₆₄ t.zeroExtend 64) ∗
      memRegion (r + 24#64) 224 ⊢
      pksmErrE A fn r (.badKeyType t) :=
  pksm0c_errCells_badKeyType_word A fn r (t.zeroExtend 64) t (pksm0c_zext8_truncate8 t)

/-- `speWord 9` at `r + 8` and `BitVec.ofNat 64 n` at `r + 16` pack into
`pksmErrE A fn r (.badKeyLength n)`. -/
theorem errCells_badKeyLength (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64) (n : Nat) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 9) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (r + 24#64) 224 ⊢
      pksmErrE A fn r (.badKeyLength n) := by
  unfold pksmErrE speAt
  rw [show (224 : Nat) = 32 + 192 by decide,
    ProofLib.memRegion_split (r + 24#64) 32 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 10` (`InvalidKeyAgreement`) at `r + 8` and `232` plain trailing bytes at
`r + 16` pack into `pksmErrE A fn r .invalidKeyAgreement`. -/
theorem errCells_invalidKeyAgreement (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 10) ∗ memRegion (r + 16#64) 232 ⊢
      pksmErrE A fn r .invalidKeyAgreement := by
  unfold pksmErrE speAt
  rw [show (232 : Nat) = 40 + 192 by decide,
    ProofLib.memRegion_split (r + 16#64) 40 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- `speWord 24` at `r + 8`, owned `String` `vecU8 A (r + 16) str` at `r + 16..40`,
and pre-key message-type byte `3#8` at `r + 40` pack into
`pksmErrE A fn r (.invalidMessage .preKey .badCiphertext)`. -/
theorem errCells_invalidMessage_preKey (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (str : List (BitVec 8)) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 24) ∗ vecU8 A (r + 16#64) str ∗
      ((r + 40#64) ↦₈ 3#8) ∗ memRegion (r + 41#64) 207 ⊢
      pksmErrE A fn r (.invalidMessage .preKey .badCiphertext) := by
  unfold pksmErrE speAt invalidMessageStrAt
  have hstr : vecU8 A (r + 16#64) str ⊢ ∃∗ bs : List (BitVec 8), vecU8 A (r + 16#64) bs :=
    Entails.sepExists_right str (Entails.refl _)
  rw [show (207 : Nat) = 15 + 192 by decide,
    ProofLib.memRegion_split (r + 41#64) 15 192 (by decide)]
  simp only [msgTypeByte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstr))

/-- Word-form companion of `errCells_invalidMessage_preKey` when `r + 40` and `r + 48` hold 64-bit
words `w5`, `w6` with `w5.truncate 8 = 3#8` (matching `W5bKyberb`'s bitfield insert on `r + 40`). -/
theorem pksm0c_errCells_invalidMessage_preKey_words (A : RustAlloc) (fn : List (BitVec 8))
    (r w5 w6 : BitVec 64) (str : List (BitVec 8)) (hw5 : w5.truncate 8 = 3#8) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 24) ∗ vecU8 A (r + 16#64) str ∗
      ((r + 40#64) ↦₆₄ w5) ∗ ((r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 ⊢
      pksmErrE A fn r (.invalidMessage .preKey .badCiphertext) := by
  have hw : ((r + 40#64) ↦₆₄ w5) ∗ ((r + 48#64) ↦₆₄ w6) ⊢
      ((r + 40#64) ↦₈ 3#8) ∗ memRegion (r + 41#64) 15 := by
    refine Entails.trans
      (sepConj_mono (pksm0c_pointsTo64_to_byte_memRegion7 (r + 40#64) w5 3#8 hw5)
        (pointsTo64_entails_memRegion (r + 48#64) w6)) ?_
    rw [show (15 : Nat) = 7 + 8 by decide, ProofLib.memRegion_split (r + 41#64) 7 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  refine Entails.trans ?_ (errCells_invalidMessage_preKey A fn r str)
  rw [show (207 : Nat) = 15 + 192 by decide,
    ProofLib.memRegion_split (r + 41#64) 15 192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (Q := ((r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₆₄ speWord 24) ∗ vecU8 A (r + 16#64) str ∗
        memRegion (r + 56#64) 192) ∗ (((r + 40#64) ↦₆₄ w5) ∗ ((r + 48#64) ↦₆₄ w6)))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_right hw) ?_
  apply Entails.of_eq; ac_rfl

/-! ## 4. General 48-Byte `speAt` Word-for-Word Copy Helpers () -/

def pksm0c_vecTail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- The 6 contiguous 64-bit words of a 48-byte `SignalProtocolError` slot at `a`. -/
def pksm0c_speWords6At (a w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
    ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

/-- Address-independent heap/rodata/pure invariant of `speAt A fn a e` once its 6 inline words
`(w0 .. w5)` at `a .. a + 40` are detached. Covers all 13 `SignalProtocolError` constructors. -/
def pksm0c_speDetached (A : RustAlloc) (fn : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) : SignalProtocolError → SepProp
  | .invalidState =>
    ∃∗ bs : List (BitVec 8),
      ⌜w0 = speWord 1 ∧ w3 = BitVec.ofNat 64 bs.length ∧ w5 = BitVec.ofNat 64 fn.length⌝ ∗
        pksm0c_vecTail A w1 w2 bs ∗ (w4 ↦ᵣ fn)
  | .ciphertextMessageTooShort n =>
    ⌜w0 = speWord 3 ∧ w1 = BitVec.ofNat 64 n⌝
  | .legacyCiphertextVersion v =>
    ⌜w0 = speWord 4 ∧ w1.truncate 8 = v⌝
  | .unrecognizedCiphertextVersion v =>
    ⌜w0 = speWord 5 ∧ w1.truncate 8 = v⌝
  | .invalidProtobufEncoding =>
    ⌜w0 = speWord 2⌝
  | .noKeyTypeIdentifier =>
    ⌜w0 = speWord 7⌝
  | .badKeyType t =>
    ⌜w0 = speWord 8 ∧ w1.truncate 8 = t⌝
  | .badKeyLength n =>
    ⌜w0 = speWord 9 ∧ w1 = BitVec.ofNat 64 n⌝
  | .invalidKeyAgreement =>
    ⌜w0 = speWord 10⌝
  | .invalidSessionStructure r =>
    ⌜w0 = speWord 20 ∧ w2 = BitVec.ofNat 64 (invalidSessionStructureStr r).length⌝ ∗ (w1 ↦ᵣ invalidSessionStructureStr r)
  | .duplicatedMessage i c =>
    ⌜w0 = speWord 23 ∧ w1 = c ++ i⌝
  | .invalidMessage t .tooFarInFuture =>
    ⌜w0 = speWord 24 ∧ w3 = BitVec.ofNat 64 tooFarInFutureStr.length ∧
      w4.truncate 8 = msgTypeByte t⌝ ∗
      pksm0c_vecTail A w1 w2 tooFarInFutureStr
  | .invalidMessage t .macFailed =>
    ⌜w0 = speWord 24 ∧ w3 = BitVec.ofNat 64 macFailedStr.length ∧
      w4.truncate 8 = msgTypeByte t⌝ ∗
      pksm0c_vecTail A w1 w2 macFailedStr
  | .invalidMessage t .pqRatchet =>
    ∃∗ bs : List (BitVec 8),
      ⌜w0 = speWord 24 ∧ w3 = BitVec.ofNat 64 bs.length ∧ w4.truncate 8 = msgTypeByte t⌝ ∗
        pksm0c_vecTail A w1 w2 bs
  | .invalidMessage t .badCiphertext =>
    ∃∗ bs : List (BitVec 8),
      ⌜w0 = speWord 24 ∧ w3 = BitVec.ofNat 64 bs.length ∧ w4.truncate 8 = msgTypeByte t⌝ ∗
        pksm0c_vecTail A w1 w2 bs
  | .invalidMessage _ .decryptionFailed => ⌜False⌝
  | .panic => ⌜False⌝

/-- Any 6 inline words `pksm0c_speWords6At src w0..w5` pack back into `memRegion src 48`. -/
theorem pksm0c_words6_entails_memRegion48 (src w0 w1 w2 w3 w4 w5 : BitVec 64) :
    pksm0c_speWords6At src w0 w1 w2 w3 w4 w5 ⊢ memRegion src 48 := by
  unfold pksm0c_speWords6At
  rw [ProofLib.memRegion_split src 8 40 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion src w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pksm0c_memRegion_words5 (src + 8#64) w1 w2 w3 w4 w5)

private theorem pksm0c_word_pure_step {a : BitVec 64} {v : BitVec 64 → Prop} {Q R : SepProp}
    (h : ∀ w : BitVec 64, v w → Q ∗ (a ↦₆₄ w) ⊢ R) :
    (∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜v w⌝) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w => ?_
  rw [sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun hw => ?_
  rw [sepConj_comm]
  exact h w hw

private theorem pksm0c_words6_intro {a : BitVec 64}
    {D : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {P0 P1 P2 P3 P4 P5 Q : SepProp}
    {v0 v1 v2 v3 v4 v5 : BitVec 64 → Prop}
    (h0 : P0 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜v0 w⌝)
    (h1 : P1 ⊢ ∃∗ w : BitVec 64, ((a + 8#64) ↦₆₄ w) ∗ ⌜v1 w⌝)
    (h2 : P2 ⊢ ∃∗ w : BitVec 64, ((a + 16#64) ↦₆₄ w) ∗ ⌜v2 w⌝)
    (h3 : P3 ⊢ ∃∗ w : BitVec 64, ((a + 24#64) ↦₆₄ w) ∗ ⌜v3 w⌝)
    (h4 : P4 ⊢ ∃∗ w : BitVec 64, ((a + 32#64) ↦₆₄ w) ∗ ⌜v4 w⌝)
    (h5 : P5 ⊢ ∃∗ w : BitVec 64, ((a + 40#64) ↦₆₄ w) ∗ ⌜v5 w⌝)
    (hQ : ∀ w0 w1 w2 w3 w4 w5, v0 w0 → v1 w1 → v2 w2 → v3 w3 → v4 w4 → v5 w5 →
      Q ⊢ D w0 w1 w2 w3 w4 w5) :
    P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ Q ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        pksm0c_speWords6At a w0 w1 w2 w3 w4 w5 ∗
          D w0 w1 w2 w3 w4 w5 := by
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2
    (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono_left h5)))))) ?_
  refine pksm0c_word_pure_step fun w0 hv0 => ?_
  rw [sepConj_assoc]
  refine pksm0c_word_pure_step fun w1 hv1 => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine pksm0c_word_pure_step fun w2 hv2 => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine pksm0c_word_pure_step fun w3 hv3 => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine pksm0c_word_pure_step fun w4 hv4 => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine pksm0c_word_pure_step fun w5 hv5 => ?_
  refine Entails.trans (Q := pksm0c_speWords6At a w0 w1 w2 w3 w4 w5 ∗ Q)
    (by unfold pksm0c_speWords6At; apply Entails.of_eq; ac_rfl) ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 ?_)))))
  exact sepConj_mono_right (hQ w0 w1 w2 w3 w4 w5 hv0 hv1 hv2 hv3 hv4 hv5)

private theorem pksm0c_words6_emp {A : RustAlloc} {fn : List (BitVec 8)} {a : BitVec 64}
    {e : SignalProtocolError} {P0 P1 P2 P3 P4 P5 : SepProp}
    {v0 v1 v2 v3 v4 v5 : BitVec 64 → Prop}
    (h0 : P0 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ⌜v0 w⌝)
    (h1 : P1 ⊢ ∃∗ w : BitVec 64, ((a + 8#64) ↦₆₄ w) ∗ ⌜v1 w⌝)
    (h2 : P2 ⊢ ∃∗ w : BitVec 64, ((a + 16#64) ↦₆₄ w) ∗ ⌜v2 w⌝)
    (h3 : P3 ⊢ ∃∗ w : BitVec 64, ((a + 24#64) ↦₆₄ w) ∗ ⌜v3 w⌝)
    (h4 : P4 ⊢ ∃∗ w : BitVec 64, ((a + 32#64) ↦₆₄ w) ∗ ⌜v4 w⌝)
    (h5 : P5 ⊢ ∃∗ w : BitVec 64, ((a + 40#64) ↦₆₄ w) ∗ ⌜v5 w⌝)
    (hQ : ∀ w0 w1 w2 w3 w4 w5, v0 w0 → v1 w1 → v2 w2 → v3 w3 → v4 w4 → v5 w5 →
      emp ⊢ pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e) :
    P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        pksm0c_speWords6At a w0 w1 w2 w3 w4 w5 ∗
          pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e := by
  refine Entails.trans ?_ (pksm0c_words6_intro h0 h1 h2 h3 h4 h5 hQ)
  apply Entails.of_eq; simp only [sepConj_emp, sepConj_assoc]

private theorem pksm0c_vecU8_repack (A : RustAlloc) (b w1 w2 : BitVec 64) (bs : List (BitVec 8)) :
    (b ↦₆₄ w1) ∗ ((b + 8#64) ↦₆₄ w2) ∗ ((b + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      pksm0c_vecTail A w1 w2 bs ⊢ vecU8 A b bs :=
  Entails.sepExists_right w1 (Entails.sepExists_right w2 (by
    unfold vecU8At vecHeader pksm0c_vecTail
    apply Entails.of_eq; simp only [sepConj_assoc]))

private theorem pksm0c_detach_invalidMessage_str (A : RustAlloc) (_fn : List (BitVec 8))
    (src : BitVec 64) (t : MessageType) (bs : List (BitVec 8)) :
    (src ↦₆₄ speWord 24) ∗ vecU8 A (src + 8#64) bs ∗
      ((src + 32#64) ↦₈ msgTypeByte t) ∗ memRegion (src + 33#64) 15 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        pksm0c_speWords6At src w0 w1 w2 w3 w4 w5 ∗
          (⌜w0 = speWord 24 ∧ w3 = BitVec.ofNat 64 bs.length ∧
            w4.truncate 8 = msgTypeByte t⌝ ∗
            pksm0c_vecTail A w1 w2 bs) := by
  unfold vecU8 vecU8At vecHeader
  rw [show (15 : Nat) = 7 + 8 by decide, ProofLib.memRegion_split (src + 33#64) 7 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  have hbyte := pksm0c_word_byte (src + 32#64) (msgTypeByte t)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbyte
  refine Entails.trans
    (Q := (src ↦₆₄ speWord 24) ∗ ((src + 8#64) ↦₆₄ cap) ∗ ((src + 16#64) ↦₆₄ ptr) ∗
      ((src + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (((src + 32#64) ↦₈ msgTypeByte t) ∗ memRegion (src + 33#64) 7) ∗
      memRegion (src + 40#64) 8 ∗
      pksm0c_vecTail A cap ptr bs)
    (by unfold pksm0c_vecTail; apply Entails.of_eq; ac_rfl) ?_
  refine pksm0c_words6_intro (pksm0c_word_exact src (speWord 24))
    (pksm0c_word_exact (src + 8#64) cap)
    (pksm0c_word_exact (src + 16#64) ptr)
    (pksm0c_word_exact (src + 24#64) (BitVec.ofNat 64 bs.length))
    hbyte (pksm0c_word_any (src + 40#64)) ?_
  intro w0 w1 w2 w3 w4 _ hw0 hw1 hw2 hw3 hw4 _
  subst hw1 hw2
  rw [pure_sepConj_of_true ⟨hw0, hw3, hw4⟩]
  exact Entails.refl _

/-- Detaches any 48-byte `speAt A fn src e` into its 6 inline words `w0..w5` at `src` plus the
address-independent predicate `pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e`. -/
theorem pksm0c_speAt_detach (A : RustAlloc) (fn : List (BitVec 8)) (src : BitVec 64)
    (e : SignalProtocolError) :
    speAt A fn src e ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        pksm0c_speWords6At src w0 w1 w2 w3 w4 w5 ∗
          pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e := by
  cases e with
  | invalidState =>
    unfold speAt
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    unfold vecU8 vecU8At vecHeader
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    unfold strRefAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right, sepConj_assoc]
    refine Entails.sepExists_elim fun p => ?_
    refine Entails.trans
      (Q := (src ↦₆₄ speWord 1) ∗ ((src + 8#64) ↦₆₄ cap) ∗ ((src + 16#64) ↦₆₄ ptr) ∗
        ((src + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((src + 32#64) ↦₆₄ p) ∗
        ((src + 40#64) ↦₆₄ BitVec.ofNat 64 fn.length) ∗
        (pksm0c_vecTail A cap ptr bs ∗ (p ↦ᵣ fn)))
      (by unfold pksm0c_vecTail; apply Entails.of_eq; ac_rfl) ?_
    refine pksm0c_words6_intro (pksm0c_word_exact src (speWord 1))
      (pksm0c_word_exact (src + 8#64) cap)
      (pksm0c_word_exact (src + 16#64) ptr)
      (pksm0c_word_exact (src + 24#64) (BitVec.ofNat 64 bs.length))
      (pksm0c_word_exact (src + 32#64) p)
      (pksm0c_word_exact (src + 40#64) (BitVec.ofNat 64 fn.length)) ?_
    rintro _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    dsimp only [pksm0c_speDetached]
    refine Entails.sepExists_right bs ?_
    rw [pure_sepConj_of_true ⟨rfl, rfl, rfl⟩]
    exact Entails.refl _
  | ciphertextMessageTooShort n =>
    unfold speAt
    rw [pksm0c_memRegion32_split8 (src + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine pksm0c_words6_emp (pksm0c_word_exact src (speWord 3))
      (pksm0c_word_exact (src + 8#64) (BitVec.ofNat 64 n))
      (pksm0c_word_any (src + 16#64)) (pksm0c_word_any (src + 24#64))
      (pksm0c_word_any (src + 32#64)) (pksm0c_word_any (src + 40#64)) ?_
    intro _ _ _ _ _ _ h0 h1 _ _ _ _
    exact pksm0c_pure_intro_emp ⟨h0, h1⟩
  | legacyCiphertextVersion v =>
    unfold speAt
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (src + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pksm0c_memRegion32_split8 (src + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hbyte := pksm0c_word_byte (src + 8#64) v
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbyte
    refine Entails.trans (by apply Entails.of_eq; ac_rfl)
      (pksm0c_words6_emp (pksm0c_word_exact src (speWord 4)) hbyte
        (pksm0c_word_any (src + 16#64)) (pksm0c_word_any (src + 24#64))
        (pksm0c_word_any (src + 32#64)) (pksm0c_word_any (src + 40#64)) ?_)
    intro _ _ _ _ _ _ h0 h1 _ _ _ _
    exact pksm0c_pure_intro_emp ⟨h0, h1⟩
  | unrecognizedCiphertextVersion v =>
    unfold speAt
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (src + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pksm0c_memRegion32_split8 (src + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hbyte := pksm0c_word_byte (src + 8#64) v
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbyte
    refine Entails.trans (by apply Entails.of_eq; ac_rfl)
      (pksm0c_words6_emp (pksm0c_word_exact src (speWord 5)) hbyte
        (pksm0c_word_any (src + 16#64)) (pksm0c_word_any (src + 24#64))
        (pksm0c_word_any (src + 32#64)) (pksm0c_word_any (src + 40#64)) ?_)
    intro _ _ _ _ _ _ h0 h1 _ _ _ _
    exact pksm0c_pure_intro_emp ⟨h0, h1⟩
  | invalidProtobufEncoding =>
    unfold speAt
    rw [pksm0c_memRegion40_split8 (src + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine pksm0c_words6_emp (pksm0c_word_exact src (speWord 2))
      (pksm0c_word_any (src + 8#64)) (pksm0c_word_any (src + 16#64))
      (pksm0c_word_any (src + 24#64)) (pksm0c_word_any (src + 32#64))
      (pksm0c_word_any (src + 40#64)) ?_
    intro _ _ _ _ _ _ h0 _ _ _ _ _
    exact pksm0c_pure_intro_emp h0
  | noKeyTypeIdentifier =>
    unfold speAt
    rw [pksm0c_memRegion40_split8 (src + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine pksm0c_words6_emp (pksm0c_word_exact src (speWord 7))
      (pksm0c_word_any (src + 8#64)) (pksm0c_word_any (src + 16#64))
      (pksm0c_word_any (src + 24#64)) (pksm0c_word_any (src + 32#64))
      (pksm0c_word_any (src + 40#64)) ?_
    intro _ _ _ _ _ _ h0 _ _ _ _ _
    exact pksm0c_pure_intro_emp h0
  | badKeyType t =>
    unfold speAt
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (src + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pksm0c_memRegion32_split8 (src + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hbyte := pksm0c_word_byte (src + 8#64) t
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbyte
    refine Entails.trans (by apply Entails.of_eq; ac_rfl)
      (pksm0c_words6_emp (pksm0c_word_exact src (speWord 8)) hbyte
        (pksm0c_word_any (src + 16#64)) (pksm0c_word_any (src + 24#64))
        (pksm0c_word_any (src + 32#64)) (pksm0c_word_any (src + 40#64)) ?_)
    intro _ _ _ _ _ _ h0 h1 _ _ _ _
    exact pksm0c_pure_intro_emp ⟨h0, h1⟩
  | badKeyLength n =>
    unfold speAt
    rw [pksm0c_memRegion32_split8 (src + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine pksm0c_words6_emp (pksm0c_word_exact src (speWord 9))
      (pksm0c_word_exact (src + 8#64) (BitVec.ofNat 64 n))
      (pksm0c_word_any (src + 16#64)) (pksm0c_word_any (src + 24#64))
      (pksm0c_word_any (src + 32#64)) (pksm0c_word_any (src + 40#64)) ?_
    intro _ _ _ _ _ _ h0 h1 _ _ _ _
    exact pksm0c_pure_intro_emp ⟨h0, h1⟩
  | invalidKeyAgreement =>
    unfold speAt
    rw [pksm0c_memRegion40_split8 (src + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine pksm0c_words6_emp (pksm0c_word_exact src (speWord 10))
      (pksm0c_word_any (src + 8#64)) (pksm0c_word_any (src + 16#64))
      (pksm0c_word_any (src + 24#64)) (pksm0c_word_any (src + 32#64))
      (pksm0c_word_any (src + 40#64)) ?_
    intro _ _ _ _ _ _ h0 _ _ _ _ _
    exact pksm0c_pure_intro_emp h0
  | invalidSessionStructure r =>
    unfold speAt strRefAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine Entails.sepExists_elim fun p => ?_
    rw [pksm0c_memRegion24_split8 (src + 24#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (Q := (src ↦₆₄ speWord 20) ∗ ((src + 8#64) ↦₆₄ p) ∗
        ((src + 16#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr r).length) ∗
        memRegion (src + 24#64) 8 ∗ memRegion (src + 32#64) 8 ∗ memRegion (src + 40#64) 8 ∗
        (p ↦ᵣ invalidSessionStructureStr r))
      (by apply Entails.of_eq; ac_rfl) ?_
    refine pksm0c_words6_intro (pksm0c_word_exact src (speWord 20))
      (pksm0c_word_exact (src + 8#64) p)
      (pksm0c_word_exact (src + 16#64) (BitVec.ofNat 64 (invalidSessionStructureStr r).length))
      (pksm0c_word_any (src + 24#64)) (pksm0c_word_any (src + 32#64))
      (pksm0c_word_any (src + 40#64)) ?_
    rintro _ _ _ _ _ _ rfl rfl rfl _ _ _
    dsimp only [pksm0c_speDetached]
    rw [pure_sepConj_of_true ⟨rfl, rfl⟩]
    exact Entails.refl _
  | duplicatedMessage i c =>
    unfold speAt
    rw [pksm0c_memRegion32_split8 (src + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hpair := pksm0c_word_pair32 (src + 8#64) i c
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpair
    refine Entails.trans (by apply Entails.of_eq; ac_rfl)
      (pksm0c_words6_emp (pksm0c_word_exact src (speWord 23)) hpair
        (pksm0c_word_any (src + 16#64)) (pksm0c_word_any (src + 24#64))
        (pksm0c_word_any (src + 32#64)) (pksm0c_word_any (src + 40#64)) ?_)
    intro _ _ _ _ _ _ h0 h1 _ _ _ _
    exact pksm0c_pure_intro_emp ⟨h0, h1⟩
  | invalidMessage t r =>
    cases r with
    | tooFarInFuture =>
      unfold speAt invalidMessageStrAt pksm0c_speDetached
      exact pksm0c_detach_invalidMessage_str A fn src t tooFarInFutureStr
    | macFailed =>
      unfold speAt invalidMessageStrAt pksm0c_speDetached
      exact pksm0c_detach_invalidMessage_str A fn src t macFailedStr
    | pqRatchet =>
      unfold speAt invalidMessageStrAt pksm0c_speDetached
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun bs => ?_
      refine Entails.trans (pksm0c_detach_invalidMessage_str A fn src t bs) ?_
      refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
        Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
        Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 => ?_
      refine Entails.sepExists_right w0 (Entails.sepExists_right w1
        (Entails.sepExists_right w2 (Entails.sepExists_right w3
          (Entails.sepExists_right w4 (Entails.sepExists_right w5 ?_)))))
      exact Entails.sepExists_right bs (Entails.refl _)
    | badCiphertext =>
      unfold speAt invalidMessageStrAt pksm0c_speDetached
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun bs => ?_
      refine Entails.trans (pksm0c_detach_invalidMessage_str A fn src t bs) ?_
      refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
        Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
        Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 => ?_
      refine Entails.sepExists_right w0 (Entails.sepExists_right w1
        (Entails.sepExists_right w2 (Entails.sepExists_right w3
          (Entails.sepExists_right w4 (Entails.sepExists_right w5 ?_)))))
      exact Entails.sepExists_right bs (Entails.refl _)
    | decryptionFailed =>
      unfold speAt invalidMessageStrAt
      simp only [sepConj_pure_left_comm]
      exact Entails.pure_left False.elim
  | panic =>
    unfold speAt
    exact pksm0c_false_entails

/-- Reattaches the 6 copied words `pksm0c_speWords6At dst w0..w5` at any destination `dst`
together with `pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e` to obtain `speAt A fn dst e`. -/
theorem pksm0c_speDetached_entails_speAt (A : RustAlloc) (fn : List (BitVec 8))
    (dst w0 w1 w2 w3 w4 w5 : BitVec 64) (e : SignalProtocolError) :
    pksm0c_speWords6At dst w0 w1 w2 w3 w4 w5 ∗
      pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e ⊢
      speAt A fn dst e := by
  refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
  cases e with
  | invalidState =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt strRefAt
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun bs => ?_
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.pure_left fun ⟨hw0, hw3, hw5⟩ => ?_
    subst hw0 hw3 hw5
    have hv := pksm0c_vecU8_repack A (dst + 8#64) w1 w2 bs
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
    refine Entails.trans
      (Q := (dst ↦₆₄ speWord 1) ∗
        (((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
          ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ pksm0c_vecTail A w1 w2 bs) ∗
        (((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 fn.length) ∗ (w4 ↦ᵣ fn)))
      (by apply Entails.of_eq; ac_rfl) ?_
    exact sepConj_mono_right (sepConj_mono
      (Entails.sepExists_right bs hv)
      (Entails.sepExists_right w4 (Entails.refl _)))
  | ciphertextMessageTooShort n =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun ⟨hw0, hw1⟩ => ?_
    subst hw0 hw1
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words4 (dst + 16#64) w2 w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | legacyCiphertextVersion v =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun ⟨hw0, hv⟩ => ?_
    subst hw0
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (dst + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_pointsTo64_to_byte_memRegion7 (dst + 8#64) w1 v hv)
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words4 (dst + 16#64) w2 w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | unrecognizedCiphertextVersion v =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun ⟨hw0, hv⟩ => ?_
    subst hw0
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (dst + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_pointsTo64_to_byte_memRegion7 (dst + 8#64) w1 v hv)
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words4 (dst + 16#64) w2 w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | invalidProtobufEncoding =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun hw0 => ?_
    subst hw0
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words5 (dst + 8#64) w1 w2 w3 w4 w5))
      (by apply Entails.of_eq; ac_rfl)
  | noKeyTypeIdentifier =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun hw0 => ?_
    subst hw0
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words5 (dst + 8#64) w1 w2 w3 w4 w5))
      (by apply Entails.of_eq; ac_rfl)
  | badKeyType t =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun ⟨hw0, ht⟩ => ?_
    subst hw0
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (dst + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_pointsTo64_to_byte_memRegion7 (dst + 8#64) w1 t ht)
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words4 (dst + 16#64) w2 w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | badKeyLength n =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun ⟨hw0, hw1⟩ => ?_
    subst hw0 hw1
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words4 (dst + 16#64) w2 w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | invalidKeyAgreement =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun hw0 => ?_
    subst hw0
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words5 (dst + 8#64) w1 w2 w3 w4 w5))
      (by apply Entails.of_eq; ac_rfl)
  | invalidSessionStructure r =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt strRefAt
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.pure_left fun ⟨hw0, hw2⟩ => ?_
    subst hw0 hw2
    refine Entails.trans
      (Q := (dst ↦₆₄ speWord 20) ∗
        (((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr r).length) ∗
          (w1 ↦ᵣ invalidSessionStructureStr r)) ∗
        (((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5)))
      (by apply Entails.of_eq; ac_rfl) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono
        (Entails.sepExists_right w1 (Entails.refl _))
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words3 (dst + 24#64) w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | duplicatedMessage i c =>
    unfold pksm0c_speWords6At pksm0c_speDetached speAt
    refine Entails.pure_left fun ⟨hw0, hw1⟩ => ?_
    subst hw0 hw1
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    have hmerge : ((dst + 8#64) ↦₃₂ i) ∗ ((dst + 12#64) ↦₃₂ c) = ((dst + 8#64) ↦₆₄ (c ++ i)) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_merge64 (dst + 8#64) i c
    rw [← hmerge]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          pksm0c_memRegion_words4 (dst + 16#64) w2 w3 w4 w5)))
      (by apply Entails.of_eq; ac_rfl)
  | invalidMessage t r =>
    cases r with
    | tooFarInFuture =>
      unfold pksm0c_speWords6At pksm0c_speDetached speAt invalidMessageStrAt
      simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.pure_left fun ⟨hw0, hw3, hw4⟩ => ?_
      subst hw0 hw3
      have hv := pksm0c_vecU8_repack A (dst + 8#64) w1 w2 tooFarInFutureStr
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
      rw [show (15 : Nat) = 7 + 8 by decide,
        ProofLib.memRegion_split (dst + asm64% (speInvalidMessageTypeOff + 1)) 7 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine Entails.trans
        (Q := (dst ↦₆₄ speWord 24) ∗
          (((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
            ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 tooFarInFutureStr.length) ∗
            pksm0c_vecTail A w1 w2 tooFarInFutureStr) ∗
          ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5))
        (by apply Entails.of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono hv (sepConj_mono
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            pksm0c_pointsTo64_to_byte_memRegion7 (dst + 32#64) w4 (msgTypeByte t) hw4)
          (pointsTo64_entails_memRegion (dst + 40#64) w5))))
        (by apply Entails.of_eq; ac_rfl)
    | macFailed =>
      unfold pksm0c_speWords6At pksm0c_speDetached speAt invalidMessageStrAt
      simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.pure_left fun ⟨hw0, hw3, hw4⟩ => ?_
      subst hw0 hw3
      have hv := pksm0c_vecU8_repack A (dst + 8#64) w1 w2 macFailedStr
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
      rw [show (15 : Nat) = 7 + 8 by decide,
        ProofLib.memRegion_split (dst + asm64% (speInvalidMessageTypeOff + 1)) 7 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine Entails.trans
        (Q := (dst ↦₆₄ speWord 24) ∗
          (((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
            ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 macFailedStr.length) ∗
            pksm0c_vecTail A w1 w2 macFailedStr) ∗
          ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5))
        (by apply Entails.of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono hv (sepConj_mono
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            pksm0c_pointsTo64_to_byte_memRegion7 (dst + 32#64) w4 (msgTypeByte t) hw4)
          (pointsTo64_entails_memRegion (dst + 40#64) w5))))
        (by apply Entails.of_eq; ac_rfl)
    | pqRatchet =>
      unfold pksm0c_speWords6At pksm0c_speDetached speAt invalidMessageStrAt
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun bs => ?_
      simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.pure_left fun ⟨hw0, hw3, hw4⟩ => ?_
      subst hw0 hw3
      have hv := pksm0c_vecU8_repack A (dst + 8#64) w1 w2 bs
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
      rw [show (15 : Nat) = 7 + 8 by decide,
        ProofLib.memRegion_split (dst + asm64% (speInvalidMessageTypeOff + 1)) 7 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine Entails.trans
        (Q := (dst ↦₆₄ speWord 24) ∗
          (((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
            ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ pksm0c_vecTail A w1 w2 bs) ∗
          ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5))
        (by apply Entails.of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono
          (Entails.sepExists_right bs hv)
          (sepConj_mono
            (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              pksm0c_pointsTo64_to_byte_memRegion7 (dst + 32#64) w4 (msgTypeByte t) hw4)
            (pointsTo64_entails_memRegion (dst + 40#64) w5))))
        (by apply Entails.of_eq; ac_rfl)
    | badCiphertext =>
      unfold pksm0c_speWords6At pksm0c_speDetached speAt invalidMessageStrAt
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun bs => ?_
      simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.pure_left fun ⟨hw0, hw3, hw4⟩ => ?_
      subst hw0 hw3
      have hv := pksm0c_vecU8_repack A (dst + 8#64) w1 w2 bs
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
      rw [show (15 : Nat) = 7 + 8 by decide,
        ProofLib.memRegion_split (dst + asm64% (speInvalidMessageTypeOff + 1)) 7 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine Entails.trans
        (Q := (dst ↦₆₄ speWord 24) ∗
          (((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
            ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ pksm0c_vecTail A w1 w2 bs) ∗
          ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5))
        (by apply Entails.of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono
          (Entails.sepExists_right bs hv)
          (sepConj_mono
            (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              pksm0c_pointsTo64_to_byte_memRegion7 (dst + 32#64) w4 (msgTypeByte t) hw4)
            (pointsTo64_entails_memRegion (dst + 40#64) w5))))
        (by apply Entails.of_eq; ac_rfl)
    | decryptionFailed =>
      unfold pksm0c_speDetached
      exact Entails.pure_left False.elim
  | panic =>
    unfold pksm0c_speDetached
    exact Entails.pure_left False.elim

/-- General 48-byte error copy (`errCopy48_entails_pksmErrE`):
once the 6 inline words `w0..w5` detached from `speAt A fn src e` (`pksm0c_speAt_detach`) have
been copied to `r + 8 .. r + 48`, combining them with `r ↦₆₄ errTag`, `memRegion (r + 56) 192`,
and `pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e` yields `pksmErrE A fn r e` for **every**
`e : SignalProtocolError`. -/
theorem errCopy48_entails_pksmErrE (A : RustAlloc) (fn : List (BitVec 8))
    (r w0 w1 w2 w3 w4 w5 : BitVec 64) (e : SignalProtocolError) :
    (r ↦₆₄ errTag) ∗
      ((r + 8#64) ↦₆₄ w0) ∗ ((r + 16#64) ↦₆₄ w1) ∗ ((r + 24#64) ↦₆₄ w2) ∗
      ((r + 32#64) ↦₆₄ w3) ∗ ((r + 40#64) ↦₆₄ w4) ∗ ((r + 48#64) ↦₆₄ w5) ∗
      memRegion (r + 56#64) 192 ∗
      pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e ⊢
      pksmErrE A fn r e := by
  unfold pksmErrE
  have hre := pksm0c_speDetached_entails_speAt A fn (r + 8#64) w0 w1 w2 w3 w4 w5 e
  unfold pksm0c_speWords6At at hre
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hre
  refine Entails.trans
    (Q := (r ↦₆₄ errTag) ∗
      ((((r + 8#64) ↦₆₄ w0) ∗ ((r + 16#64) ↦₆₄ w1) ∗ ((r + 24#64) ↦₆₄ w2) ∗
        ((r + 32#64) ↦₆₄ w3) ∗ ((r + 40#64) ↦₆₄ w4) ∗ ((r + 48#64) ↦₆₄ w5)) ∗
        pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e) ∗
      memRegion (r + 56#64) 192)
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono_right (sepConj_mono_left hre)

/-- When `∀ b, (b ↦₆₄ ew0) ∗ ((b + 8) ↦₆₄ ew1) ∗ memRegion (b + 16) 32 ⊢ speAt A fn b e`,
the 6 copied words at `r + 8 .. r + 48` directly entail `pksmErrE A fn r e`. -/
theorem pksm0c_errCopy48_words2_entails_pksmErrE (A : RustAlloc) (fn : List (BitVec 8))
    (r ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64) (e : SignalProtocolError)
    (hpack : ∀ b : BitVec 64,
      (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢ speAt A fn b e) :
    (r ↦₆₄ errTag) ∗
      ((r + 8#64) ↦₆₄ ew0) ∗ ((r + 16#64) ↦₆₄ ew1) ∗ ((r + 24#64) ↦₆₄ ew2) ∗
      ((r + 32#64) ↦₆₄ ew3) ∗ ((r + 40#64) ↦₆₄ ew4) ∗ ((r + 48#64) ↦₆₄ ew5) ∗
      memRegion (r + 56#64) 192 ⊢
      pksmErrE A fn r e := by
  unfold pksmErrE
  have hm32 :
      ((r + 24#64) ↦₆₄ ew2) ∗ ((r + 32#64) ↦₆₄ ew3) ∗
      ((r + 40#64) ↦₆₄ ew4) ∗ ((r + 48#64) ↦₆₄ ew5) ⊢
      memRegion (r + 24#64) 32 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pksm0c_memRegion_words4 (r + 24#64) ew2 ew3 ew4 ew5
  have hspe :
      ((r + 8#64) ↦₆₄ ew0) ∗ ((r + 16#64) ↦₆₄ ew1) ∗ ((r + 24#64) ↦₆₄ ew2) ∗
      ((r + 32#64) ↦₆₄ ew3) ∗ ((r + 40#64) ↦₆₄ ew4) ∗ ((r + 48#64) ↦₆₄ ew5) ⊢
      speAt A fn (r + 8#64) e := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right hm32)) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hpack (r + 8#64)
  refine Entails.trans
    (Q := (r ↦₆₄ errTag) ∗
      (((r + 8#64) ↦₆₄ ew0) ∗ ((r + 16#64) ↦₆₄ ew1) ∗ ((r + 24#64) ↦₆₄ ew2) ∗
        ((r + 32#64) ↦₆₄ ew3) ∗ ((r + 40#64) ↦₆₄ ew4) ∗ ((r + 48#64) ↦₆₄ ew5)) ∗
      memRegion (r + 56#64) 192)
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono_right (sepConj_mono_left hspe)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
