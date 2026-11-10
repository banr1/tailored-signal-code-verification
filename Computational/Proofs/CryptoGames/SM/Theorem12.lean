/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
public import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14
public import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma15

/-!
# Theorem 12: privacy of the Fig. 8 SM scheme

**Checked by Lean.** Proves `theorem12` (ACD19 §5.3.3, Lemmas 13–15), bounding the privacy
advantage of the Fig. 8 SM scheme via the concrete reductions `redCKAPriv`, `redPRNGPriv`,
`redFSPriv`, and `redFSPrivCoin` (`SM/Reductions.lean`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

/-- Lemma 13: privacy bias bounded by the real CKA world of `redCKAPriv`. -/
theorem lemma13 (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[privGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A].boolBias ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAPriv cka prng fs lam Δcka qep tL t A)].boolBias := by
  let _ := (inferInstance : DecidableEq I)
  let _ := (inferInstance : SampleableType K)
  exact PrivL13.lemma13_proof cka prng fs lam Δcka qep hc tL t A

/-- Lemma 14: ideal CKA world bounded by the real PRF-PRNG world of `redPRNGPriv` (DEV-SM24). -/
theorem lemma14 (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAPriv cka prng fs lam Δcka qep tL t A)].boolBias ≤
      𝒟[PRFPRNG.branch prng false (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolBias :=
  PrivL14.lemma14_proof cka prng fs lam Δcka qep hc tL t A

/-- **DEV-SM25 (paper fix): Lemma 15's bound.** Privacy attacks a single challenge session (no
factor `q`), while discarding FS-AEAD challenge-session forgery wins adds `2 * Adv(redFSPrivCoin)`. -/
theorem lemma15 (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolBias ≤
      FSAEAD.advantage fs (redFSPriv cka prng fs lam Δcka qep tL t A)
        + 2 * FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A) :=
  PrivL15.lemma15_proof cka prng fs lam Δcka qep tL t A

/-- Privacy bound for the ACD19 Fig. 8 SM scheme with `Δ_SM = 2 + Δ_CKA` (DEV-SM20, DEV-SM24,
DEV-SM25, DEV-SM27). -/
theorem theorem12 (hc : cka.Correct) :
    Theorem12 cka prng fs lam Δcka qep (redCKAPriv cka prng fs lam Δcka qep)
      (redPRNGPriv cka prng fs lam Δcka qep) (redFSPriv cka prng fs lam Δcka qep)
      (redFSPrivCoin cka prng fs lam Δcka qep) := by
  intro tL t A
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CKA.branch cka Δcka (healEpoch tL) true (redCKAPriv cka prng fs lam Δcka qep tL t A)]
  set cF := 𝒟[CKA.branch cka Δcka (healEpoch tL) false
    (redCKAPriv cka prng fs lam Δcka qep tL t A)]
  set pT := 𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)]
  set pF := 𝒟[PRFPRNG.branch prng false (redPRNGPriv cka prng fs lam Δcka qep tL t A)]
  have h13 := lemma13 cka prng fs lam Δcka qep hc tL t A
  have h14 := lemma14 cka prng fs lam Δcka qep hc tL t A
  have h15 := lemma15 cka prng fs lam Δcka qep tL t A
  have hc' : cF.boolBias ≤ cT.boolBias + 2 * cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact boolBias_le_add_two_mul_boolDist _ _
  have hp' : pF.boolBias ≤ pT.boolBias + 2 * pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact boolBias_le_add_two_mul_boolDist _ _
  unfold privAdvantage
  calc 𝒟[privGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A].boolBias
      ≤ cF.boolBias := h13
    _ ≤ cT.boolBias + 2 * cT.boolDist cF := hc'
    _ ≤ (pT.boolBias + 2 * pT.boolDist pF) + 2 * cT.boolDist cF :=
        add_le_add (h14.trans hp') le_rfl
    _ ≤ ((FSAEAD.advantage fs (redFSPriv cka prng fs lam Δcka qep tL t A)
          + 2 * FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A))
          + 2 * pT.boolDist pF) + 2 * cT.boolDist cF :=
        add_le_add (add_le_add h15 le_rfl) le_rfl
    _ = _ := by ring

end CryptoGames.SM.Construction
