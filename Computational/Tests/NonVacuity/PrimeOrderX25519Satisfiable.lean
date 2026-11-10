/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.NonVacuity.PqHeadlineSatisfiable
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
public import Computational.Tests.XeddsaRomNonVac
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import Computational.Tests.NonVacuity.KeyInd1KeyRoNonVac
import LibsignalBinary.Proofs.SignalSession.PqModelRun
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Prime-Order X25519 Joint Hypothesis Satisfiability

**Checked by Lean.**

Joint satisfiability witness for `SessionSecure`, `LibsignalCliPqSecure`, and the excused-abort
specialization of `CliPqxdhSecurityFor` over the Curve25519 subgroup of prime order
`l25519 = 2 ^ 252 + 27742317777372353535851937790883648493`. The carrier
`Pt25519 := Fin (halfL25519 + 1)` of size `(l25519 + 1) / 2 > 2 ^ 251` represents `0` together
with the `(l25519 - 1) / 2` x-only `{±P}` pairs, with basepoint `base25519 = 9`. RFC 7748 clamped
scalars act injectively on `Pt25519` via `absZMod (c * Q)`, which gives `DhKerUniform dh25519` and
the point-fiber bound `δ = (1 : ℝ≥0∞) / 2 ^ 250`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession CKA SM
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SignalSession CryptoGames.LibsignalSM.Proofs.Correctness
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
open Computational.Tests.XeddsaRomNonVac
open SpecTests.SignalPqxdh (cwfC cwfC_clamp cwfC_word_eq uniform256_map_bool_le
  cwfPrimitives cwfPrimitives_kem_coll_bound fitBytes_length)
open _root_.SignalPqxdh (fitBytes word256ToBytes clampScalar25519 sampleScalar32 sampleBytes32
  sampleKemKeyGen isCanonicalRef xeddsaVerifyRef isValidDhTripleRef)

/-- Prime-order x-only subgroup carrier for Curve25519 (`0` for the identity and `1 .. halfL25519`
for the `(l25519 - 1) / 2` non-identity `{±P}` pairs in `ZMod l25519`). -/
abbrev Pt25519 : Type := Fin (halfL25519 + 1)

theorem two_pow_251_lt_card_pt25519 : 2 ^ 251 < Fintype.card Pt25519 := by
  rw [Fintype.card_fin]
  unfold halfL25519 l25519
  decide

/-- Curve25519 Montgomery basepoint `u = 9` in `Pt25519`. -/
def base25519 : Pt25519 :=
  ⟨9, by unfold halfL25519 l25519; decide⟩

private theorem pt25519_val_le_half (Q : Pt25519) : Q.val ≤ halfL25519 :=
  Nat.lt_succ_iff.mp Q.isLt

private theorem pt25519_val_lt_two_pow_252 (Q : Pt25519) : Q.val < 2 ^ 252 :=
  lt_of_le_of_lt (pt25519_val_le_half Q) halfL25519_lt_two_pow_252

private theorem pt25519_val_lt_l25519 (Q : Pt25519) : Q.val < l25519 :=
  lt_trans (pt25519_val_lt_two_pow_252 Q) two_pow_252_lt_l25519

private theorem absZMod_pt25519_cast (Q : Pt25519) :
    absZMod (Q.val : ZMod l25519) = Q.val := by
  unfold absZMod
  simp [ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q), pt25519_val_le_half Q]

private theorem pt25519_cast_ne_zero {Q : Pt25519} (hQ : Q ≠ 0) :
    (Q.val : ZMod l25519) ≠ 0 := by
  intro h0
  have hval := congrArg ZMod.val h0
  rw [ZMod.val_natCast_of_lt (pt25519_val_lt_l25519 Q), ZMod.val_zero] at hval
  exact hQ (Fin.ext (by simpa using hval))

/-- 32-byte little-endian encoding of `Q : Pt25519`. -/
def encPt25519 (Q : Pt25519) : List (BitVec 8) :=
  ofU8 (bytesOfNatLE 32 Q.val)

def encT25519 (Q : Pt25519) : PublicKey := ⟨vec32 (encPt25519 Q)⟩

/-- Partial inverse of `encT25519` accepting encodings below `halfL25519 + 1`. -/
def decT25519 (pk : PublicKey) : Option Pt25519 :=
  let n := natOfBytesLE (vecU8 pk.1)
  if h : n < halfL25519 + 1 then some ⟨n, h⟩ else none

/-- Clamped x-only prime-subgroup DH action on `Pt25519` over `ZMod l25519`. -/
def dh25519 : DHFun (BitVec 256) Pt25519 where
  base := base25519
  dh k Q :=
    ⟨absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)),
     Nat.lt_succ_of_le (absZMod_le_half _)⟩

private theorem toU8_encPt25519_eq_encodeMontZMod (Q : Pt25519) :
    toU8 (encPt25519 Q) = encodeMontZMod (Q.val : ZMod l25519) := by
  rw [encPt25519, toU8_ofU8, encodeMontZMod, absZMod_pt25519_cast]

private theorem encPt25519_length (Q : Pt25519) : (encPt25519 Q).length = 32 := by
  simp [encPt25519, bytesOfNatLE_length]

private theorem encPt25519_zero : encPt25519 0 = List.replicate 32 0#8 := by
  unfold encPt25519
  rw [Fin.val_zero, bytesOfNatLE_zero]
  rfl

private theorem encPt25519_base : encPt25519 dh25519.base = x25519Base := by
  change ofU8 (bytesOfNatLE 32 9) = x25519Base
  decide

private theorem base25519_ne_zero : dh25519.base ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_zero] at hv
  exact absurd hv (by decide : (9 : ℕ) ≠ 0)

private theorem baseZMod_ne_zero : (dh25519.base.val : ZMod l25519) ≠ 0 :=
  pt25519_cast_ne_zero base25519_ne_zero

private theorem toU8_x25519Base_eq_encodeMontZMod_base :
    toU8 x25519Base = encodeMontZMod (dh25519.base.val : ZMod l25519) := by
  rw [← encPt25519_base, toU8_encPt25519_eq_encodeMontZMod]

private theorem vecU8_encT25519 (Q : Pt25519) :
    vecU8 (encT25519 Q).1 = bytesOfNatLE 32 Q.val := by
  simp [encT25519, vecU8, vec32, encPt25519, toU8_ofU8]

private theorem natOfBytesLE_vecU8_encT25519 (Q : Pt25519) :
    natOfBytesLE (vecU8 (encT25519 Q).1) = Q.val := by
  rw [vecU8_encT25519, natOfBytesLE_bytesOfNatLE]
  exact Nat.mod_eq_of_lt (lt_trans (pt25519_val_lt_two_pow_252 Q) (by decide))

theorem decT25519_encT25519 (Q : Pt25519) : decT25519 (encT25519 Q) = some Q := by
  unfold decT25519
  dsimp only
  simp [natOfBytesLE_vecU8_encT25519, Q.isLt]

theorem encT25519_inj : Function.Injective encT25519 := by
  intro a b h
  exact Option.some.inj ((decT25519_encT25519 a).symm.trans (by rw [h, decT25519_encT25519]))

theorem encPt25519_inj : Function.Injective encPt25519 := by
  intro a b h
  exact encT25519_inj (by simp only [encT25519, h])

theorem encT25519_ne_dummyKey (Q : Pt25519) : encT25519 Q ≠ dummyKey := by
  intro h
  have h1 := congrArg (fun pk : PublicKey => decide (natOfBytesLE (vecU8 pk.1) < 2 ^ 252)) h
  rw [natOfBytesLE_vecU8_encT25519, decide_eq_true (pt25519_val_lt_two_pow_252 Q)] at h1
  have h2 : decide (natOfBytesLE (vecU8 dummyKey.1) < 2 ^ 252) = false := by decide
  rw [h2] at h1
  exact Bool.noConfusion h1

private theorem x25519ZMod_len (a u : List UInt8) : (x25519ZMod a u).length = 32 :=
  encodeMontZMod_len _

private theorem toU8_encPt25519_dh25519 (k : BitVec 256) (Q : Pt25519) :
    toU8 (encPt25519 (dh25519.dh k Q)) =
      x25519ZMod (word256ToBytes k) (toU8 (encPt25519 Q)) := by
  rw [toU8_encPt25519_eq_encodeMontZMod Q, x25519ZMod_encodeMontZMod]
  simp only [encPt25519, dh25519, toU8_ofU8, encodeMontZMod]

private theorem encPt25519_dh25519 (k : BitVec 256) (Q : Pt25519) :
    encPt25519 (dh25519.dh k Q) =
      ofU8 (x25519ZMod (word256ToBytes k) (toU8 (encPt25519 Q))) := by
  rw [← ofU8_toU8 (encPt25519 (dh25519.dh k Q)), toU8_encPt25519_dh25519]

private theorem dh25519_dh_val (k : BitVec 256) (Q : Pt25519) :
    (dh25519.dh k Q).val =
      absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)) := by
  unfold dh25519
  rfl

theorem dh25519_zero (x : BitVec 256) : dh25519.dh x 0 = 0 := by
  apply Fin.ext
  rw [Fin.val_zero]
  change absZMod (clampedScalarZMod (word256ToBytes x) * (((0 : Pt25519).val : ℕ) : ZMod l25519)) = 0
  rw [Fin.val_zero]
  simp [absZMod]

theorem dh25519_ne_zero (k : BitVec 256) (Q : Pt25519) (hQ : Q ≠ 0) :
    dh25519.dh k Q ≠ 0 := by
  intro h0
  have hval : absZMod (clampedScalarZMod (word256ToBytes k) * (Q.val : ZMod l25519)) = 0 := by
    simpa [dh25519] using congrArg Fin.val h0
  have hmul := (absZMod_eq_zero_iff _).mp hval
  exact mul_ne_zero (clampedScalarZMod_ne_zero (word256ToBytes k)) (pt25519_cast_ne_zero hQ) hmul

theorem dh25519_commutes : dh25519.Commutes := by
  intro a b
  have h : toU8 (encPt25519 (dh25519.dh a (dh25519.dh b dh25519.base))) =
      toU8 (encPt25519 (dh25519.dh b (dh25519.dh a dh25519.base))) := by
    rw [toU8_encPt25519_dh25519, toU8_encPt25519_dh25519,
        toU8_encPt25519_dh25519, toU8_encPt25519_dh25519,
        toU8_encPt25519_eq_encodeMontZMod,
        x25519ZMod_encodeMontZMod, x25519ZMod_encodeMontZMod,
        x25519ZMod_encodeMontZMod, x25519ZMod_encodeMontZMod,
        mul_left_comm]
  apply encPt25519_inj
  have h1 := congrArg ofU8 h
  rwa [ofU8_toU8, ofU8_toU8] at h1

theorem dh25519_dh_inj (a : BitVec 256) : Function.Injective (dh25519.dh a) := by
  intro Q Q' h
  have habs : absZMod (clampedScalarZMod (word256ToBytes a) * (Q.val : ZMod l25519)) =
      absZMod (clampedScalarZMod (word256ToBytes a) * (Q'.val : ZMod l25519)) :=
    congrArg Fin.val h
  have hpm : (Q.val : ZMod l25519) = (Q'.val : ZMod l25519) ∨
      (Q.val : ZMod l25519) = -(Q'.val : ZMod l25519) := by
    rcases (absZMod_eq_iff _ _).mp habs with hm | hm
    · exact Or.inl (mul_left_cancel₀ (clampedScalarZMod_ne_zero (word256ToBytes a)) hm)
    · rw [← mul_neg] at hm
      exact Or.inr (mul_left_cancel₀ (clampedScalarZMod_ne_zero (word256ToBytes a)) hm)
  have hval : absZMod (Q.val : ZMod l25519) = absZMod (Q'.val : ZMod l25519) :=
    (absZMod_eq_iff _ _).mpr hpm
  rw [absZMod_pt25519_cast, absZMod_pt25519_cast] at hval
  exact Fin.ext hval

theorem dh25519_kerUniform : DhKerUniform dh25519 := by
  intro s x Q Q'
  rw [(dh25519_dh_inj x).eq_iff, (dh25519_dh_inj s).eq_iff]

/-- Each point `Q : Pt25519` has at most `64` preimages under `w ↦ dh25519.dh w dh25519.base`
(`≤ 2` clamped scalars `±c₀` times `2^5 = 32` clamped-away bits of `w : BitVec 256`). -/
theorem dh25519_base_fiber_card (Q : Pt25519) :
    (Finset.univ.filter (fun w : BitVec 256 => dh25519.dh w dh25519.base = Q)).card ≤ 64 := by
  set S := Finset.univ.filter (fun w : BitVec 256 => dh25519.dh w dh25519.base = Q)
  by_cases hne : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hne
    have hw0_eq : dh25519.dh w0 dh25519.base = Q := (Finset.mem_filter.mp hw0).2
    set c0 := clampedScalarZMod (word256ToBytes w0)
    let b0 : ZMod l25519 := (dh25519.base.val : ZMod l25519)
    have hb0_ne : b0 ≠ 0 := baseZMod_ne_zero
    have hc0_ne_neg : c0 ≠ -c0 := by
      intro h2c0
      have hc0_ne : c0 ≠ 0 := clampedScalarZMod_ne_zero (word256ToBytes w0)
      have hs := edSignZMod_neg c0 hc0_ne
      rw [← h2c0] at hs
      rcases edSignZMod_bool c0 with hb | hb <;> rw [hb] at hs <;>
        exact (by revert hs; decide)
    let tag : BitVec 256 → Bool × Fin 8 × Fin 4 := fun w =>
      (@decide (clampedScalarZMod (word256ToBytes w) = c0) (Classical.propDecidable _),
       ⟨w.toNat % 8, Nat.mod_lt _ (by decide)⟩,
       ⟨w.toNat / 2 ^ 254, Nat.div_lt_of_lt_mul (by have := w.isLt; omega)⟩)
    have hinj : Set.InjOn tag (S : Set (BitVec 256)) := by
      intro w1 hw1 w2 hw2 htag
      have hw1_eq : dh25519.dh w1 dh25519.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).2
      have hw2_eq : dh25519.dh w2 dh25519.base = Q :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hw2)).2
      have hw1_abs : absZMod (clampedScalarZMod (word256ToBytes w1) * b0) = absZMod (c0 * b0) := by
        have h := congrArg Fin.val (hw1_eq.trans hw0_eq.symm)
        rwa [dh25519_dh_val, dh25519_dh_val] at h
      have hw2_abs : absZMod (clampedScalarZMod (word256ToBytes w2) * b0) = absZMod (c0 * b0) := by
        have h := congrArg Fin.val (hw2_eq.trans hw0_eq.symm)
        rwa [dh25519_dh_val, dh25519_dh_val] at h
      have hpm1 : clampedScalarZMod (word256ToBytes w1) = c0 ∨
          clampedScalarZMod (word256ToBytes w1) = -c0 := by
        rcases (absZMod_eq_iff _ _).mp hw1_abs with hm | hm
        · exact Or.inl (mul_right_cancel₀ hb0_ne hm)
        · rw [← neg_mul] at hm
          exact Or.inr (mul_right_cancel₀ hb0_ne hm)
      have hpm2 : clampedScalarZMod (word256ToBytes w2) = c0 ∨
          clampedScalarZMod (word256ToBytes w2) = -c0 := by
        rcases (absZMod_eq_iff _ _).mp hw2_abs with hm | hm
        · exact Or.inl (mul_right_cancel₀ hb0_ne hm)
        · rw [← neg_mul] at hm
          exact Or.inr (mul_right_cancel₀ hb0_ne hm)
      have htag_iff : (clampedScalarZMod (word256ToBytes w1) = c0) ↔
          (clampedScalarZMod (word256ToBytes w2) = c0) :=
        @decide_eq_decide _ _ (Classical.propDecidable _) (Classical.propDecidable _) |>.mp
          (congrArg Prod.fst htag)
      have hlo : w1.toNat % 8 = w2.toNat % 8 := congrArg (fun p => p.2.1.val) htag
      have hhi : w1.toNat / 2 ^ 254 = w2.toNat / 2 ^ 254 := congrArg (fun p => p.2.2.val) htag
      have hc_eq :
          clampedScalarZMod (word256ToBytes w1) = clampedScalarZMod (word256ToBytes w2) := by
        rcases hpm1 with hc1 | hc1 <;> rcases hpm2 with hc2 | hc2
        · exact hc1.trans hc2.symm
        · exfalso
          exact hc0_ne_neg (hc2.symm.trans (htag_iff.mp hc1)).symm
        · exfalso
          exact hc0_ne_neg (hc1.symm.trans (htag_iff.mpr hc2)).symm
        · exact hc1.trans hc2.symm
      have hcl_eq := clampScalar25519_eq_of_clampedScalarZMod_eq hc_eq
      have hcwf : cwfC (word256ToBytes w1) = cwfC (word256ToBytes w2) := by
        rw [← cwfC_clamp (word256ToBytes w1), ← cwfC_clamp (word256ToBytes w2), hcl_eq]
      exact cwfC_word_eq w1 w2 hcwf hlo hhi
    have hcard_le : S.card ≤ Fintype.card (Bool × Fin 8 × Fin 4) :=
      Finset.card_le_card_of_injOn tag (fun _ _ => Finset.mem_univ _) hinj
    have hcard64 : Fintype.card (Bool × Fin 8 × Fin 4) = 64 := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    exact hcard_le.trans_eq hcard64
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le 64

/-- Point-fiber probability bound `64 / 2 ^ 256 = 1 / 2 ^ 250` on `Pt25519`. -/
theorem dh25519_base_fiber_prob_le (Q : Pt25519) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | dh25519.dh x dh25519.base = Q} ≤
      (1 : ℝ≥0∞) / 2 ^ 250 := by
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample,
      Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_of_le_mul
  calc ((Finset.univ.filter (fun x : BitVec 256 => dh25519.dh x dh25519.base = Q)).card : ℝ≥0∞)
      ≤ ((64 : ℕ) : ℝ≥0∞) := by exact_mod_cast dh25519_base_fiber_card Q
    _ = (2 : ℝ≥0∞) ^ 6 := by norm_num
    _ = ((1 : ℝ≥0∞) / 2 ^ 250) * (2 : ℝ≥0∞) ^ 256 := by
      rw [one_div, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 250 * 2 ^ 6 by rw [← pow_add],
          ENNReal.inv_mul_cancel_left (by simp) (by simp)]

/-- `Crypto` hooks backed by `x25519ZMod` over `ZMod l25519`. -/
def c25519 : Crypto where
  F := fun st _ => st
  E := fun _ b => b
  D := fun _ b => b
  X := fun s u => u8Vec 32 (x25519ZMod (vecU8 s) (vecU8 u))
  pubKey := fun s => u8Vec 32 (x25519ZMod (vecU8 s) (toU8 x25519Base))

/-- `PqxdhPrims` witness over `ZMod l25519` with canonical Montgomery check `isCanonMont32`. -/
def Q25519 : PqxdhPrims :=
  { Q255 with
    montToEd := fun u s =>
      if s == 0#8 && isCanonMont32 (vecU8 u) then
        some (List.Vector.replicate 160 0#8)
      else none }

def W25519 : PEParams := ⟨c25519, Q25519⟩

/-- Pre-DDH `UnreachedPqxdhPrimitives` witness over `ZMod l25519` (`pow8 = pow8ZMod`). -/
def X25519_pre : UnreachedPqxdhPrimitives :=
  { X255_pre with
    sigPkGen := fun a => vecU8 (c25519.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
    pow8 := pow8ZMod }

/-- `UnreachedPqxdhPrimitives` witness with `isValidDhTriple` pinned to `isValidDhTripleRef`. -/
noncomputable def X25519 : UnreachedPqxdhPrimitives :=
  { X25519_pre with
    isValidDhTriple := fun A B Z =>
      @decide (isValidDhTripleRef (modelPrims X25519_pre W25519) A B Z)
        (Classical.propDecidable _) }

private theorem fitBytesRef32_of_len {pk : List UInt8} (hpk : pk.length = 32) :
    _root_.SignalPqxdh.fitBytesRef 32 pk = pk := by
  simp [_root_.SignalPqxdh.fitBytesRef, hpk]

private theorem vecU8_vec32_of_len (bs : List (BitVec 8)) (h : bs.length = 32) :
    vecU8 (vec32 bs) = toU8 bs := by
  simp [vecU8, vec32, h]

private theorem vecU8_vec32_keyToBytes32_25519 (k : BitVec 256) :
    vecU8 (vec32 (HMAC.keyToBytes32 k)) = word256ToBytes k := by
  rw [vecU8_vec32_of_len _ (length_keyToBytes32 k), ← word256ToBytes_eq_toU8_keyToBytes32]

private theorem word256ToBytes_clamp256_25519 (k : BitVec 256) :
    word256ToBytes (clamp256 k) = clampScalar25519 (word256ToBytes k) := by
  have h1 : u8Vec 32 (word256ToBytes (clamp256 k)) =
      u8Vec 32 (clampScalar25519 (word256ToBytes k)) := by
    rw [u8Vec_word256ToBytes, ← clampScalar_keyVec,
        ← u8Vec_word256ToBytes, u8Vec_clampScalar25519]
  have h2 := congrArg vecU8 h1
  rwa [vecU8_u8Vec_of_length _ (length_word256ToBytes _),
       vecU8_u8Vec_of_length _ (_root_.SignalPqxdh.clampScalar25519_length _)] at h2

theorem libX25519Rel_c25519 : X25519RealizesDh c25519 dh25519 encPt25519 encT25519 := by
  refine ⟨?_, fun _ => rfl⟩
  refine
    { enc_injective := encPt25519_inj
      enc_length := encPt25519_length
      enc_zero := encPt25519_zero
      enc_base := encPt25519_base
      base_ne_zero := base25519_ne_zero
      hook := fun k Q => ?_
      pubKey_hook := fun k => ?_
      dh_clamp := fun k Q => ?_
      dh_ne_zero := dh25519_ne_zero }
  · dsimp only [c25519]
    rw [vecU8_vec32_keyToBytes32_25519, vecU8_vec32_of_len _ (encPt25519_length Q),
        ← ofU8_fitBytesRef_eq_u8Vec_toList, fitBytesRef32_of_len (x25519ZMod_len _ _),
        encPt25519_dh25519]
  · dsimp only [c25519]
    rw [vecU8_vec32_keyToBytes32_25519, ← ofU8_fitBytesRef_eq_u8Vec_toList,
        fitBytesRef32_of_len (x25519ZMod_len _ _), encPt25519_dh25519, encPt25519_base]
  · apply Fin.ext
    dsimp only [dh25519]
    rw [word256ToBytes_clamp256_25519, clampedScalarZMod_clamp]

private theorem vecU8_clampScalar_u8Vec_25519 (a : List UInt8) :
    vecU8 (Ratchet.clampScalar (u8Vec 32 a)) = clampScalar25519 a := by
  rw [← u8Vec_clampScalar25519,
      vecU8_u8Vec_of_length _ (_root_.SignalPqxdh.clampScalar25519_length a)]

private theorem modelPrims_X25519_x25519Base (a : List UInt8) :
    (modelPrims X25519 W25519).x25519Base a =
      encodeMontZMod (clampedScalarZMod a * (dh25519.base.val : ZMod l25519)) := by
  dsimp only [modelPrims, blockLevelPrims, W25519, c25519]
  rw [vecU8_u8Vec_of_length _ (x25519ZMod_len _ _), vecU8_clampScalar_u8Vec_25519,
      toU8_x25519Base_eq_encodeMontZMod_base, x25519ZMod_encodeMontZMod, clampedScalarZMod_clamp]

private theorem modelPrims_X25519_x25519 (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X25519 W25519).x25519 a pk =
      encodeMontZMod (clampedScalarZMod a * decodeMont32 pk) := by
  dsimp only [modelPrims, blockLevelPrims, W25519, c25519]
  rw [vecU8_u8Vec_of_length _ (x25519ZMod_len _ _), vecU8_clampScalar_u8Vec_25519,
      vecU8_u8Vec_of_length pk hpk]
  unfold x25519ZMod
  rw [fitBytesRef32_of_len hpk, clampedScalarZMod_clamp]

private theorem modelPrims_X25519_isCanonical (pk : List UInt8) :
    (modelPrims X25519 W25519).isCanonical pk = isCanonMont32 pk := by
  dsimp only [modelPrims, blockLevelPrims, W25519, Q25519, Q255, isCanonicalRef]
  by_cases hc : isCanonMont32 pk = true
  · obtain ⟨hlen, _, hle⟩ := isCanonMont32_spec.mp hc
    have hlt252 : natOfBytesLE pk < 2 ^ 252 := lt_of_le_of_lt hle halfL25519_lt_two_pow_252
    obtain ⟨h80, hr⟩ := scalarIsInRange_of_lt_two_pow_252 hlt252
    rw [hc, hlen, h80, hr, vecU8_u8Vec_of_length pk hlen, hc]
    rfl
  · have hfalse : isCanonMont32 pk = false := Bool.eq_false_iff.mpr hc
    by_cases hlen : pk.length = 32
    · rw [hfalse, vecU8_u8Vec_of_length pk hlen, hfalse]
      split <;> rfl
    · have hlenB : (pk.length == 32) = false := beq_eq_false_iff_ne.mpr hlen
      simp [hfalse, hlenB]

theorem modelPrims_X25519_sig_corr (sk msg r : List UInt8) :
    (modelPrims X25519 W25519).sigVerify (X25519.sigPkGen sk) msg (X25519.sigSign sk msg r) =
      true := by
  have hpk : X25519.sigPkGen sk =
      encodeMontZMod (clampedScalarZMod sk * (dh25519.base.val : ZMod l25519)) :=
    modelPrims_X25519_x25519Base sk
  have hcan : isCanonMont32 (X25519.sigPkGen sk) = true := by
    rw [hpk, isCanonMont32_encodeMontZMod_iff]
    exact mul_ne_zero (clampedScalarZMod_ne_zero sk) baseZMod_ne_zero
  have hlen : (X25519.sigPkGen sk).length = 32 := (isCanonMont32_spec.mp hcan).1
  rw [modelPrims_sigVerify_eq_ref]
  have hsig : X25519.sigSign sk msg r = List.replicate 64 0 := rfl
  rw [hsig]
  unfold xeddsaVerifyRef
  have hcond : ((X25519.sigPkGen sk).length == 32 &&
      (List.replicate 64 (0 : UInt8)).length == 64 &&
      (((List.replicate 64 (0 : UInt8)).getD 63 0 &&& 0x60) == 0)) = true := by
    rw [hlen]; decide
  rw [hcond]
  dsimp only [modelPrims, blockLevelPrims, W25519, Q25519, Q255]
  have hs0 : (((List.replicate 64 (0 : UInt8)).getD 63 0 &&& 0x80) >>> 7).toBitVec == 0#8 := by
    decide
  rw [vecU8_u8Vec_of_length _ hlen, hcan, hs0]
  decide

private theorem modelPrims_X25519_ec_coll_bound (targetPk : List UInt8) :
    (𝒟[do
        let sk ← sampleScalar32
        pure (X25519.pow8 ((modelPrims X25519 W25519).x25519Base sk) ==
          X25519.pow8 targetPk)] {true}).toReal
      ≤ 1 / (2 : ℝ) ^ 250 := by
  have hy : ∃ y : ZMod l25519, pow8ZMod targetPk = encodeMontZMod y := by
    unfold pow8ZMod
    by_cases hlen : targetPk.length == 32
    · exact ⟨decodeMont32 targetPk, by simp [hlen]⟩
    · exact ⟨0, by simp [hlen, encodeMontZMod_zero]⟩
  obtain ⟨y, hy_eq⟩ := hy
  let Qt : Pt25519 := ⟨absZMod y, Nat.lt_succ_of_le (absZMod_le_half y)⟩
  have hQt : pow8ZMod targetPk = encodeMontZMod (Qt.val : ZMod l25519) := by
    rw [hy_eq, encodeMontZMod, encodeMontZMod, absZMod_pt25519_cast]
  have hc : ∀ sk, X25519.pow8 ((modelPrims X25519 W25519).x25519Base sk) =
      encodeMontZMod (clampedScalarZMod sk * (dh25519.base.val : ZMod l25519)) := fun sk => by
    change pow8ZMod ((modelPrims X25519 W25519).x25519Base sk) = _
    rw [modelPrims_X25519_x25519Base, pow8ZMod_encodeMontZMod]
  have hp8 : X25519.pow8 targetPk = pow8ZMod targetPk := rfl
  let f : BitVec 256 → Bool := fun w =>
    encodeMontZMod (clampedScalarZMod (word256ToBytes w) * (dh25519.base.val : ZMod l25519)) ==
      pow8ZMod targetPk
  have hexpr :
      (do
        let sk ← sampleScalar32
        pure (X25519.pow8 ((modelPrims X25519 W25519).x25519Base sk) ==
          X25519.pow8 targetPk)) =
      (f <$> ($ᵗ BitVec 256)) := by
    simp only [hc, hp8, sampleScalar32, sampleBytes32, bind_pure_comp, Functor.map_map]
    rfl
  rw [hexpr]
  refine le_trans (uniform256_map_bool_le f 64 ?_) (by norm_num)
  refine le_trans (Finset.card_le_card ?_) (dh25519_base_fiber_card Qt)
  intro w hw
  have hw_eq :
      encodeMontZMod (clampedScalarZMod (word256ToBytes w) * (dh25519.base.val : ZMod l25519)) =
        encodeMontZMod (Qt.val : ZMod l25519) := by
    have hb : f w = true := (Finset.mem_filter.mp hw).2
    dsimp only [f] at hb
    rw [hQt] at hb
    exact beq_iff_eq.mp hb
  have habs :
      absZMod (clampedScalarZMod (word256ToBytes w) * (dh25519.base.val : ZMod l25519)) =
        Qt.val := by
    have hnat := congrArg natOfBytesLE hw_eq
    rwa [natOfBytesLE_encodeMontZMod, natOfBytesLE_encodeMontZMod, absZMod_pt25519_cast] at hnat
  have hdh : dh25519.dh w dh25519.base = Qt := by
    apply Fin.ext
    rw [dh25519_dh_val]
    exact habs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hdh⟩

theorem modelPrims_X25519_cryptoAssumptions : ModelPrimsCryptoAssumptions X25519 W25519 where
  x25519_zero_iff := fun a1 a2 pk _ _ hpk => by
    rw [modelPrims_X25519_x25519 a1 pk hpk, modelPrims_X25519_x25519 a2 pk hpk,
        encodeMontZMod_eq_zero_iff, encodeMontZMod_eq_zero_iff,
        mul_eq_zero_iff_left (clampedScalarZMod_ne_zero a1),
        mul_eq_zero_iff_left (clampedScalarZMod_ne_zero a2)]
  canon_base := fun e _ => by
    rw [modelPrims_X25519_isCanonical, modelPrims_X25519_x25519Base,
        isCanonMont32_encodeMontZMod_iff]
    exact mul_ne_zero (clampedScalarZMod_ne_zero e) baseZMod_ne_zero
  canon_x25519 := fun a pk _ hcan => by
    rw [modelPrims_X25519_isCanonical] at hcan ⊢
    obtain ⟨hpk, hpos, hle⟩ := isCanonMont32_spec.mp hcan
    have hdec_ne : decodeMont32 pk ≠ 0 := by
      unfold decodeMont32
      simp only [hcan, ↓reduceIte]
      intro h0
      have hv := congrArg ZMod.val h0
      have hlt_l : natOfBytesLE pk < l25519 :=
        lt_trans (lt_of_le_of_lt hle halfL25519_lt_two_pow_252) two_pow_252_lt_l25519
      rw [ZMod.val_natCast_of_lt hlt_l, ZMod.val_zero] at hv
      omega
    rw [modelPrims_X25519_x25519 a pk hpk, isCanonMont32_encodeMontZMod_iff]
    exact mul_ne_zero (clampedScalarZMod_ne_zero a) hdec_ne
  pow8_idemp := pow8ZMod_idemp
  isValidDhTriple_eq_ref := fun A B Z => by
    dsimp only [X25519]
    exact @decide_eq_true_iff _ (Classical.propDecidable _)
  x25519_pow8_congr := fun a pk1 pk2 _ h1 h2 hpow => by
    rw [modelPrims_X25519_x25519 a pk1 h1, modelPrims_X25519_x25519 a pk2 h2]
    change pow8ZMod pk1 = pow8ZMod pk2 at hpow
    unfold pow8ZMod at hpow
    simp only [h1, h2, beq_self_eq_true, ↓reduceIte] at hpow
    rcases (encodeMontZMod_eq_iff _ _).mp hpow with hd | hd
    · rw [hd]
    · rw [hd, mul_neg, encodeMontZMod_neg]
  x25519_congr_of_base_eq := fun a1 a2 pk _ _ hcan hbase => by
    rw [modelPrims_X25519_isCanonical] at hcan
    have hpk := (isCanonMont32_spec.mp hcan).1
    rw [modelPrims_X25519_x25519Base, modelPrims_X25519_x25519Base] at hbase
    rw [modelPrims_X25519_x25519 a1 pk hpk, modelPrims_X25519_x25519 a2 pk hpk]
    rcases (encodeMontZMod_eq_iff _ _).mp hbase with hm | hm
    · rw [mul_right_cancel₀ baseZMod_ne_zero hm]
    · rw [← neg_mul] at hm
      rw [mul_right_cancel₀ baseZMod_ne_zero hm, neg_mul, encodeMontZMod_neg]
  canon_pow8_inj := fun pk1 pk2 h1 h2 hpow => by
    rw [modelPrims_X25519_isCanonical] at h1 h2
    change pow8ZMod pk1 = pow8ZMod pk2 at hpow
    rwa [pow8ZMod_of_isCanonMont32 h1, pow8ZMod_of_isCanonMont32 h2] at hpow
  pow8_len := fun p => by
    change (pow8ZMod p).length = 32
    unfold pow8ZMod
    split
    · exact encodeMontZMod_len _
    · simp
  ec_coll_bound := modelPrims_X25519_ec_coll_bound
  x25519_inj_pow8 := fun a pk1 pk2 _ h1 h2 hx => by
    rw [modelPrims_X25519_x25519 a pk1 h1, modelPrims_X25519_x25519 a pk2 h2] at hx
    change pow8ZMod pk1 = pow8ZMod pk2
    unfold pow8ZMod
    simp only [h1, h2, beq_self_eq_true, ↓reduceIte]
    apply (encodeMontZMod_eq_iff _ _).mpr
    rcases (encodeMontZMod_eq_iff _ _).mp hx with hm | hm
    · exact Or.inl (mul_left_cancel₀ (clampedScalarZMod_ne_zero a) hm)
    · rw [← mul_neg] at hm
      exact Or.inr (mul_left_cancel₀ (clampedScalarZMod_ne_zero a) hm)
  pow8_base_len := fun p e _ hpow => by
    change pow8ZMod p = pow8ZMod ((modelPrims X25519 W25519).x25519Base e) at hpow
    rw [modelPrims_X25519_x25519Base, pow8ZMod_encodeMontZMod] at hpow
    by_contra hne
    have hp : pow8ZMod p = List.replicate 32 0 := by simp [pow8ZMod, hne]
    rw [hp] at hpow
    exact mul_ne_zero (clampedScalarZMod_ne_zero e) baseZMod_ne_zero
      ((encodeMontZMod_eq_zero_iff _).mp hpow.symm)
  sigPkGen_eq_x25519Base := rfl
  scalarMul_len := fun _ _ => by simp [X25519, X25519_pre, X255_pre]
  scalarAdd_len := fun _ _ => by simp [X25519, X25519_pre, X255_pre]
  kemKeyGen_len := fun seed => ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  sig_corr := modelPrims_X25519_sig_corr
  kem_coll_bound := cwfPrimitives_kem_coll_bound

private theorem c25519_D_E (k : BitVec 256) (x : BitVec 128) : c25519.D k (c25519.E k x) = x :=
  rfl

private theorem encaps1Total_K255 : Encaps1Total K255 :=
  fun _ _ _ => rfl

private theorem bhEncaps1Total_W25519 : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W25519.Q.K :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem modelPrims_X25519_kemCorrectWith_zero :
    SignalPqxdh.KemDeltaCorrect (modelPrims X25519 W25519) 0 := by
  unfold SignalPqxdh.KemDeltaCorrect
  have hCorr : ∀ seed r ss ct,
      (modelPrims X25519 W25519).kemEncaps ((modelPrims X25519 W25519).kemKeyGen seed).1 r =
        some (ss, ct) →
      (modelPrims X25519 W25519).kemDecaps ((modelPrims X25519 W25519).kemKeyGen seed).2 ct =
        some ss :=
    modelPrims_kem_corr_of_decaps X25519 W25519 (fun _ _ => rfl)
  simp [SignalPqxdh.kemHonestFail_eq_false_of_kem_corr hCorr]

theorem modelPrims_X25519_cwfδ :
    SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X25519 W25519) :=
  cryptoWellFormedPrimitivesδ_modelPrims X25519 W25519 modelPrims_X25519_cryptoAssumptions
    dh25519_commutes libX25519Rel_c25519 c25519_D_E

abbrev sessionNoopAdv (ℓ : ℕ) :
    SM.Adversary (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
      (BitVec 512) CryptoVerification.E2E.Bytes :=
  (pure false :
    SM.AdversaryComp (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
      (BitVec 512) CryptoVerification.E2E.Bytes Bool)

/-- Joint satisfiability of all hypotheses of `SessionSecure` on a carrier `Pt` of cardinality
`> 2 ^ 251` with point-fiber bound `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem session_hypotheses_satisfiable_prime_order (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (C : Crypto) (K : LibsignalSpqrV1.MlKem) (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep q : ℕ)
      (oa : ProbComp Unit) (_ida _idb : Unit → IdentityKey) (_s : Unit → BitVec 256)
      (A : Unit → SM.Adversary (GhostState CryptoVerification.E2E.Bytes) (CBC.Plain ℓ)
        (BitVec 512) CryptoVerification.E2E.Bytes),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      2 ^ 251 < Fintype.card Pt ∧
      0 < q ∧
      Encaps1Total K ∧
      (∀ k x, C.D k (C.E k x) = x) ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      DhKerUniform Dh ∧
      2 * (q + 1) + 25002 < 2 ^ 32 ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      (∀ o ∈ support oa, SM.MakesAtMostQueries (A o) q) := by
  refine ⟨Pt25519, inferInstance, inferInstance, inferInstance, inferInstance,
    c25519, K255, dh25519, encPt25519, encT25519, decT25519, 1, 1,
    pure (), (fun _ => bhIdKeyOf []), (fun _ => bhIdKeyOf []), (fun _ => 0),
    (fun _ => sessionNoopAdv ℓ), ?_⟩
  exact ⟨two_pow_251_lt_card_pt25519, by decide, encaps1Total_K255, c25519_D_E, hℓ,
    dh25519_commutes, libX25519Rel_c25519, decT25519_encT25519, encT25519_inj,
    encT25519_ne_dummyKey, dh25519_zero, dh25519_kerUniform,
    show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dh25519_base_fiber_prob_le, fun _ _ => trivial⟩

/-- Instantiates `SessionSecure (Pt := Pt25519) ℓ` with the prime-order witness at
`δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem sessionSecure_prime_order_instantiable (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : SessionSecure (Pt := Pt25519) ℓ) :
    ∃ D : SessionCostedReductionFamily Pt25519 ℓ,
      SessionCostedReductionFamilyBounded ℓ D ∧
      𝒟[(pure () : ProbComp Unit) >>= fun o =>
          SM.gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr c25519 (LibsignalSpqrV1.spqrV1SessionUniformCoins c25519.F K255)
                (bhIdKeyOf []) (bhIdKeyOf []))
              ℓ (0 : BitVec 256))
            3 1 (configRefuseEarlyBobCorr decT25519 encT25519)
            ((fun _ : Unit => sessionNoopAdv ℓ) o)].boolBias ≤
        sessionAdvantageBound ℓ D c25519 K255 dh25519 encPt25519 encT25519 decT25519 1 1
          ((1 : ℝ≥0∞) / 2 ^ 250) (pure ()) (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf [])
          (fun _ => 0) (fun _ => sessionNoopAdv ℓ)
          + 2 * sessionKemFailProb c25519 K255 ℓ decT25519 encT25519 1 (pure ())
            (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf []) (fun _ => 0)
            (fun _ => sessionNoopAdv ℓ) := by
  rcases hSec with ⟨D, hD, hMain⟩
  exact ⟨D, hD, hMain c25519 K255 dh25519 encPt25519 encT25519 decT25519
    encaps1Total_K255 c25519_D_E hℓ dh25519_commutes libX25519Rel_c25519
    decT25519_encT25519 encT25519_ne_dummyKey dh25519_zero dh25519_kerUniform
    1 1 (by decide) ((1 : ℝ≥0∞) / 2 ^ 250) dh25519_base_fiber_prob_le
    (pure ()) (fun _ => bhIdKeyOf []) (fun _ => bhIdKeyOf []) (fun _ => 0)
    (fun _ => sessionNoopAdv ℓ) (fun _ _ => trivial)⟩

/-- Joint satisfiability of the hypotheses of `LibsignalCliPqSecure` with
`2 ^ 251 < Fintype.card Pt`, `δ_kem = 0`, and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem cli_pq_headline_hypotheses_satisfiable_prime_order
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 0, 1, 0⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := cliRoCoinDrAdv S ℓ (BitVec 512)
  refine ⟨Pt25519, inferInstance, inferInstance, inferInstance, inferInstance,
    pqModelRun X25519 W25519, X25519, W25519, dh25519, encPt25519, encT25519, decT25519,
    1, b1, 1, fun _ => 1, A0, ?_⟩
  exact ⟨two_pow_251_lt_card_pt25519, by decide, by decide,
    cliSpecPq_pqModelRun X25519 W25519, bhEncaps1Total_W25519,
    modelPrims_X25519_cwfδ, modelPrims_X25519_kemCorrectWith_zero, hℓ,
    dh25519_commutes, libX25519Rel_c25519, decT25519_encT25519, encT25519_inj,
    encT25519_ne_dummyKey, dh25519_zero, c25519_D_E, dh25519_kerUniform,
    fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide,
    dh25519_base_fiber_prob_le,
    cliRoCoinDrAdv_bounded S ℓ (BitVec 512)⟩

/-- Closed specialization of `cli_pq_headline_hypotheses_satisfiable_prime_order` at `N_id = 2`
and `ℓ = 32`. -/
theorem cli_pq_headline_hypotheses_satisfiable_prime_order_concrete :
    ∃ (S : SignalPqxdh.Setup) (ℓ : ℕ)
      (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt)
      (_qep : ℕ) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      2 ≤ S.N_id ∧ 0 < S.N_send_tot ∧ 0 < S.N_recv_tot ∧ 0 < ℓ ∧
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdh run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  let S0 : SignalPqxdh.Setup := ⟨2, 1, 1, 1, 1, 1⟩
  obtain ⟨Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
      b, qStart, qs, A, hRest⟩ :=
    cli_pq_headline_hypotheses_satisfiable_prime_order S0 32 (by decide)
  exact ⟨S0, 32, Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
    b, qStart, qs, A, by decide, by decide, by decide, by decide, hRest⟩

/-- Instantiates both advantage bounds of `LibsignalCliPqSecure (Pt := Pt25519) S ℓ` with the
prime-order witness at `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem libsignalCliPqSecure_prime_order_instantiable
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hSec : LibsignalCliPqSecure (Pt := Pt25519) S ℓ) :
    ∃ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
      (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
      (b_ki : SignalPqxdh.QueryBudget)
      (A : CliGameAdversary S ℓ (BitVec 512))
      (advK : SignalPqxdh.KeyIndAdversary S)
      (hK : SignalPqxdh.QueryBounded advK b_ki)
      (prefixSum : ℝ≥0∞),
      CliPqxdhAdvantage S run X W ℓ qep decT25519 encT25519 A ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X W) advK +
          prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0 +
          2 * CliKemFailProb S run X W ℓ qep decT25519 encT25519 A ∧
      CliPqxdhAdvantage S run X W ℓ qep decT25519 encT25519 A ≤
        2 * (let R := RK.eval
             let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
             SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on 0
               (SignalPqxdh.GapSigEufCma (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (R.sig _ Ab))
               (SignalPqxdh.KemShCr (modelPrims X W) (R.shcr _ Ab))
               (SignalPqxdh.GapDhWithSign (modelPrims X W) (modelPrims X W).isValidDhTriple
                 (modelPrims X W).pow8 (R.gdh _ Ab)) + 1)
          + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S 0
          + 2 * CliKemFailProb S run X W ℓ qep decT25519 encT25519 A := by
  rcases hSec with ⟨L_cli, RK, D, R_e2e, _, _, _, _, hMain⟩
  let b1 : SignalPqxdh.QueryBudget := ⟨1, 1, 1, 1⟩
  let A0 : CliGameAdversary S ℓ (BitVec 512) := ⟨pure false⟩
  have hA0 : CliGameAdversaryPerInstanceBounded A0 b1 1 (fun _ => 1) :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, fun _ _ => trivial⟩
  rcases hMain (pqModelRun X25519 W25519) X25519 W25519 (cliSpecPq_pqModelRun X25519 W25519)
      bhEncaps1Total_W25519 modelPrims_X25519_cwfδ 0 modelPrims_X25519_kemCorrectWith_zero
      dh25519 encPt25519 encT25519 decT25519 1 hℓ
      dh25519_commutes libX25519Rel_c25519 decT25519_encT25519 encT25519_ne_dummyKey
      dh25519_zero c25519_D_E dh25519_kerUniform
      b1 1 (fun _ => 1) (fun _ _ => show 2 * (1 + 1) + 25002 < 2 ^ 32 by decide)
      ((1 : ℝ≥0∞) / 2 ^ 250) dh25519_base_fiber_prob_le A0 hA0
    with ⟨hK, _, hBound1, hBound2⟩
  exact ⟨pqModelRun X25519 W25519, X25519, W25519, 1, RK, keyIndReductionBudget S 1 b1, A0, _, hK, _,
    hBound1, hBound2 1 (SignalPqxdh.keyIndRoGap_one S (modelPrims X25519 W25519) _)⟩

/-- Joint satisfiability for the `CliSpecPqxdhOrExcusedAbort` specialization of
`CliPqxdhSecurityFor` with `2 ^ 251 < Fintype.card Pt` and `δ = (1 : ℝ≥0∞) / 2 ^ 250`. -/
theorem pqOom_hypotheses_satisfiable_prime_order
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    ∃ (Pt : Type) (_ : DecidableEq Pt) (zPt : Zero Pt) (fPt : Fintype Pt) (sPt : SampleableType Pt)
      (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (Dh : DHFun (BitVec 256) Pt)
      (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (_qep : ℕ)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      letI : Zero Pt := zPt; letI : Fintype Pt := fPt; letI : SampleableType Pt := sPt
      2 ^ 251 < Fintype.card Pt ∧
      0 < qStart ∧
      0 < qs 0 ∧
      CliSpecPqxdhOrExcusedAbort exc run X W ∧
      MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K ∧
      SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W) ∧
      SignalPqxdh.KemDeltaCorrect (modelPrims X W) 0 ∧
      ℓ < 10 ^ 6 ∧
      Dh.Commutes ∧
      X25519RealizesDh W.C Dh encPt encT ∧
      (∀ T, decT (encT T) = some T) ∧
      Function.Injective encT ∧
      (∀ T, encT T ≠ dummyKey) ∧
      (∀ x, Dh.dh x 0 = 0) ∧
      (∀ k x, W.C.D k (W.C.E k x) = x) ∧
      DhKerUniform Dh ∧
      (∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) ∧
      (∀ Q : Pt,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤
          (1 : ℝ≥0∞) / 2 ^ 250) ∧
      CliGameAdversaryPerInstanceBounded A b qStart qs := by
  obtain ⟨Pt, dPt, zPt, fPt, sPt, run, X, W, Dh, encPt, encT, decT, qep,
      b, qStart, qs, A, hCard, hqStart, hqs0, hCli, hRest⟩ :=
    cli_pq_headline_hypotheses_satisfiable_prime_order S ℓ hℓ
  have someIte : ∀ {α : Type} (p : Prop) [Decidable p] (a b : α),
      (if p then some a else some b) = some (if p then a else b) := by
    intro α p _ a b; by_cases hp : p <;> simp [hp]
  have someIte2 : ∀ {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b c : α),
      (if p then some a else if q then some b else some c) =
        some (if p then a else if q then b else c) := by
    intro α p q _ _ a b c; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  have hCliOom : CliSpecPqxdhOrExcusedAbort (⊥ : Inputs → Prop) run X W := by
    intro st hst
    obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hCli st hst
    exact ⟨fun b t hnone => Or.inl ⟨_, hInit b t hnone, rfl⟩,
      fun m r hm => Or.inl ⟨_, (hSend m r hm).trans (someIte2 _ _ _ _ _), rfl⟩,
      fun c rc hc => Or.inl ⟨_, (hWhisper c rc hc).trans (someIte _ _ _), rfl⟩,
      fun m rc h1 h2 => Or.inl ⟨_, (hPrekey m rc h1 h2).trans (someIte _ _ _), rfl⟩,
      fun c rc h1 h2 h3 => Or.inl ⟨_, (hBad c rc h1 h2 h3).trans (someIte _ _ _), rfl⟩⟩
  exact ⟨Pt, dPt, zPt, fPt, sPt, ⊥, run, X, W, Dh, encPt, encT, decT, qep,
    b, qStart, qs, A, hCard, hqStart, hqs0, hCliOom, hRest⟩

/--
info: 'CryptoVerification.E2E.session_hypotheses_satisfiable_prime_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms session_hypotheses_satisfiable_prime_order

/--
info: 'CryptoVerification.E2E.cli_pq_headline_hypotheses_satisfiable_prime_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cli_pq_headline_hypotheses_satisfiable_prime_order

/--
info: 'CryptoVerification.E2E.pqOom_hypotheses_satisfiable_prime_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pqOom_hypotheses_satisfiable_prime_order

end CryptoVerification.E2E
