/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimShallow
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.CreateChainProofDefs
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Clamping and chain-creation helpers for the refinement

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Pure X25519 clamping lemmas, honest `createChain` evaluation, and the `simNoneWinEvent` wrapper
used in `libsignal_refines`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

abbrev LibAdv (PQ PQC : Type) (ℓ : ℕ) :=
  SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))

theorem getLsbD_clamp256 (x : BitVec 256) (m : ℕ) (hm : m < 256) :
    (CKA.clamp256 x).getLsbD m =
      (decide (m = 254) || (x.getLsbD m && !decide (m < 3) && !decide (m = 255))) := by
  have h7 : ∀ i, (7 : BitVec 256).getLsbD i = (decide (i < 256) && decide (i < 3)) := fun i => by
    rw [show (7 : BitVec 256) = BitVec.ofNat 256 7 from rfl, BitVec.getLsbD_ofNat,
      show (7 : ℕ) = 2 ^ 3 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have h1 : ∀ i, (1 : BitVec 256).getLsbD i = (decide (i < 256) && decide (i = 0)) := fun i => by
    rw [show (1 : BitVec 256) = BitVec.ofNat 256 1 from rfl, BitVec.getLsbD_ofNat,
      show (1 : ℕ) = 2 ^ 1 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp
  simp only [CKA.clamp256, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, h7, h1]
  by_cases h254 : m = 254
  · subst h254; simp
  · by_cases h255 : m = 255
    · subst h255; simp
    · have e1 : decide (m - 254 = 0) = decide (m < 254) := by
        by_cases h : m < 254 <;> simp [h] <;> omega
      have e2 : (decide (m < 255) = false) → False := by intro h; simp at h; omega
      by_cases h3 : m < 3 <;> by_cases h2 : m < 254 <;> simp_all

theorem get_keyVec (y : BitVec 256) (j : Fin 32) :
    (keyToBytesVec32 y).get j = y.extractLsb' (8 * j.val) 8 := by
  unfold keyToBytesVec32 keyToBytes32 List.Vector.get
  rw [List.get_ofFn]
  rfl

theorem clampScalar_keyVec (x : BitVec 256) :
    clampScalar (keyToBytesVec32 x) = keyToBytesVec32 (CKA.clamp256 x) := by
  apply List.Vector.ext
  intro j
  rw [get_keyVec]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', getLsbD_clamp256 x _ (by omega)]
  by_cases h31 : j = 31
  · subst h31
    simp only [clampScalar, List.Vector.get_set_same, get_keyVec]
    interval_cases k <;> simp
  · by_cases h0 : j = 0
    · subst h0
      simp only [clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_same, get_keyVec]
      interval_cases k <;> simp
    · simp only [clampScalar]
      rw [List.Vector.get_set_of_ne (Ne.symm h31), List.Vector.get_set_of_ne (Ne.symm h0),
        get_keyVec, BitVec.getLsbD_extractLsb']
      have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hj31 : j.val ≠ 31 := fun h => h31 (Fin.ext h)
      have := j.isLt
      have a1 : 8 * j.val + k ≠ 254 := by omega
      have a2 : 8 * j.val + k ≠ 255 := by omega
      have a3 : ¬ 8 * j.val + k < 3 := by omega
      simp [hk, a1, a2, a3]

theorem toListFn_vec (X : X25519Fn) (k u : List.Vector (BitVec 8) 32) :
    X.toListFn k.toList u.toList = (X k u).toList := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨u, hu⟩ := u
  simp [X25519Fn.toListFn, hk, hu]

/-- Under `X25519Model`, `createChain` on a private key `keyToBytesVec32 x` and non-zero point `T`
performs one `rootPRNG` step on `D.dh x T`. -/
theorem createChain_honest {D : CKA.DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} (F : ShaState → List (BitVec 8) → ShaState) (X : X25519Fn)
    {pubKey : List (BitVec 8) → List (BitVec 8)}
    (hM : CKA.X25519Model D encPt X.toListFn pubKey) (rk : Ratchet.RootKey)
    (x : BitVec 256) (T : Pt) (hT : T ≠ 0) (pub : List.Vector (BitVec 8) 32)
    (hpub : pub.toList = encPt T) :
    createChain F X rk pub (keyToBytesVec32 x) = some ((rootPRNG F encPt).up rk (D.dh x T)) := by
  have hss : (X (clampScalar (keyToBytesVec32 x)) pub).toList = encPt (D.dh x T) := by
    rw [clampScalar_keyVec, ← hM.dh_clamp x T, ← hM.hook (CKA.clamp256 x) T, ← hpub,
      ← toListFn_vec]
    rfl
  have hne : encPt (D.dh x T) ≠ List.replicate 32 0#8 := fun he =>
    hM.dh_ne_zero x T hT (hM.enc_injective (he.trans hM.enc_zero.symm))
  simp only [createChain, hss, hne, ite_false]
  rfl

theorem createChain_honest_clamped {D : CKA.DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} (F : ShaState → List (BitVec 8) → ShaState) (X : X25519Fn)
    {pubKey : List (BitVec 8) → List (BitVec 8)}
    (hM : CKA.X25519Model D encPt X.toListFn pubKey) (rk : Ratchet.RootKey)
    (x : BitVec 256) (T : Pt) (hT : T ≠ 0) (pub : List.Vector (BitVec 8) 32)
    (hpub : pub.toList = encPt T) :
    createChain F X rk pub (keyToBytesVec32 (CKA.clamp256 x)) =
      some ((rootPRNG F encPt).up rk (D.dh x T)) := by
  have h := createChain_honest F X hM rk (CKA.clamp256 x) T hT pub hpub
  rwa [hM.dh_clamp x T] at h

/-- Experiment running `LibsignalSim.simRun` with `k = none` inside `lFig8` (`Config.h1`) and
returning `s.win`. -/
def simNoneWinEvent (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b (LibsignalSim.simRun P Dh encT decT qep none A)
  return s.win

end CryptoGames.LibsignalSM.Proofs.Refinement

