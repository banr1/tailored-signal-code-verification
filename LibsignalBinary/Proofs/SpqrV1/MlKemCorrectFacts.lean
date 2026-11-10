/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire

/-!
# Properties and Non-Vacuity of `MlKem.CorrectWith`

Establishes triviality at `δ = 1`, monotonicity in `δ`, and non-vacuity at `δ = 0` (witnessed by
`MlKem.ideal`) for the ML-KEM correctness hypothesis `MlKem.CorrectWith` (`DEV-SPQR6`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSpqrV1

open OracleComp ENNReal
/-- `CorrectWith K 1` holds for every `K`: a probability is at most `1`. -/
theorem MlKem.correctWith_one (K : MlKem) : K.CorrectWith 1 := by
  unfold MlKem.CorrectWith
  exact ((evalDist _).mono (Set.subset_univ _)).trans (EvalDistSemantics.apply_univ_le_one _)

/-- `CorrectWith` is monotone in `δ`. -/
theorem MlKem.CorrectWith.mono {K : MlKem} {δ δ' : ℝ≥0∞} (h : K.CorrectWith δ) (hδ : δ ≤ δ') :
    K.CorrectWith δ' :=
  h.trans hδ

/-- An idealized ML-KEM: all keys, ciphertexts and secrets are zero, so decapsulation always
returns the encapsulated secret. Used only to show that `CorrectWith K 0` is satisfiable. -/
def MlKem.ideal : MlKem where
  keyPair _ := List.Vector.replicate 2400 0
  encaps1 _ _ := some (List.Vector.replicate 960 0, List.Vector.replicate 2080 0,
    List.Vector.replicate 32 0)
  encaps2 _ _ := List.Vector.replicate 128 0
  decaps _ _ _ := List.Vector.replicate 32 0
  validPk _ _ := true

private theorem vector_toList_replicate {α : Type} (n : Nat) (a : α) :
    (List.Vector.replicate n a).toList = List.replicate n a := rfl

/-- `MlKem.ideal.fromSeed` returns all-zero key pairs. -/
theorem MlKem.ideal_fromSeed :
    MlKem.ideal.fromSeed = fun _ => (List.Vector.replicate 64 0, List.Vector.replicate 1152 0,
      List.Vector.replicate 2400 0) := by
  funext seed
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply List.Vector.eq
    rw [MlKem.fromSeed_hdr]
    dsimp only [MlKem.ideal]
    rw [vector_toList_replicate, vector_toList_replicate, List.drop_replicate, List.take_replicate]
    exact congrArg (List.replicate · 0) (by unfold pk1Off; omega)
  · apply List.Vector.eq
    rw [MlKem.fromSeed_ek]
    dsimp only [MlKem.ideal]
    rw [vector_toList_replicate, vector_toList_replicate, List.drop_replicate, List.take_replicate]
    exact congrArg (List.replicate · 0) (by unfold pk2Off; omega)
  · exact MlKem.fromSeed_dk MlKem.ideal seed

/-- The issue-1275 scan never asks for a flip on all-zero bytes. -/
theorem issue1275NeedsFlip_replicate_zero (n : ℕ) :
    issue1275NeedsFlip (List.replicate n 0) = false := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      change issue1275NeedsFlip (0 :: 0 :: List.replicate m 0) = false
      unfold issue1275NeedsFlip
      exact ih m (by omega)

private theorem bytesToVector?_toList {n : Nat} (v : List.Vector (BitVec 8) n) :
    bytesToVector? n v.toList = some v := by
  unfold bytesToVector?
  simp only [v.toList_length, ↓reduceDIte]
  exact congrArg some (List.Vector.eq _ _ rfl)

private theorem take_toList_self {n : Nat} (v : List.Vector (BitVec 8) n) :
    v.toList.take n = v.toList :=
  List.take_of_length_le (Nat.le_of_eq v.toList_length)

private theorem ideal_generate (seed : List.Vector (BitVec 8) 64) :
    LibsignalSpqrV1.generate MlKem.ideal seed.toList =
      .ok ({ ek := (List.Vector.replicate 1152 0).toList,
             dk := (List.Vector.replicate 2400 0).toList,
             hdr := (List.Vector.replicate 64 0).toList },
           seed.toList.drop 64) := by
  unfold LibsignalSpqrV1.generate KEY_GENERATION_SEED_SIZE
  rw [take_toList_self seed, bytesToVector?_toList seed, MlKem.ideal_fromSeed]

private theorem ideal_encaps1 (hdr : Bytes) (m : List.Vector (BitVec 8) 32) :
    LibsignalSpqrV1.encaps1 MlKem.ideal hdr m.toList =
      .ok (((List.Vector.replicate 960 0).toList,
            (List.Vector.replicate 2080 0).toList,
            (List.Vector.replicate 32 0).toList),
           m.toList.drop 32) := by
  unfold LibsignalSpqrV1.encaps1 SHARED_SECRET_SIZE
  rw [take_toList_self m, bytesToVector?_toList m]
  rfl

private theorem ideal_ek_matches :
    LibsignalSpqrV1.ek_matches_header MlKem.ideal (List.Vector.replicate 1152 0).toList
      (List.Vector.replicate 64 0).toList = true := by
  unfold LibsignalSpqrV1.ek_matches_header MlKem.validPkBytes
  rw [vector_toList_replicate, vector_toList_replicate, List.length_replicate,
    List.length_replicate]
  rfl

private theorem ideal_encaps2 :
    LibsignalSpqrV1.encaps2 MlKem.ideal (List.Vector.replicate 1152 0).toList
      (List.Vector.replicate 2080 0).toList = .ok (List.Vector.replicate 128 0).toList := by
  have hfix : potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
      (List.Vector.replicate 2080 0).toList = .ok none := by
    unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 ENCAPSULATION_STATE_SIZE
    rw [vector_toList_replicate, List.length_replicate, bne_self_eq_false]
    simp only [Bool.false_eq_true, ↓reduceIte, List.drop_replicate, List.take_replicate,
      issue1275NeedsFlip_replicate_zero]
  unfold LibsignalSpqrV1.encaps2 ENCAPSULATION_STATE_SIZE ENCAPSULATION_KEY_SIZE
  rw [hfix]
  simp only [Bind.bind, Except.bind, Option.getD_none, bytesToVector?_toList]
  rfl

private theorem ideal_decaps :
    LibsignalSpqrV1.decaps MlKem.ideal (List.Vector.replicate 2400 0).toList
      (List.Vector.replicate 960 0).toList (List.Vector.replicate 128 0).toList =
      .ok (List.Vector.replicate 32 0).toList := by
  unfold LibsignalSpqrV1.decaps CIPHERTEXT1_SIZE CIPHERTEXT2_SIZE DECAPSULATION_KEY_SIZE
  rw [bytesToVector?_toList, bytesToVector?_toList, bytesToVector?_toList]
  rfl

/-- The idealized ML-KEM never fails an honest exchange. -/
theorem MlKem.ideal_honestFail (seed : List.Vector (BitVec 8) 64)
    (m : List.Vector (BitVec 8) 32) : MlKem.ideal.honestExchangeFails seed m = false := by
  unfold MlKem.honestExchangeFails
  simp only [ideal_generate, ideal_encaps1, ideal_ek_matches, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, ideal_encaps2, ideal_decaps, ne_eq, not_true_eq_false, decide_false]

/-- Non-vacuity: `CorrectWith` is satisfiable with `δ = 0`. -/
theorem MlKem.correctWith_ideal : MlKem.ideal.CorrectWith 0 := by
  unfold MlKem.CorrectWith
  simp only [MlKem.ideal_honestFail]
  rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const]
  rw [LawfulPureEvalDistSemantics.denote_pure]
  simp

end CryptoVerification.LibsignalSpqrV1
