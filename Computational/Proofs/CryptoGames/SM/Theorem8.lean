/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11

/-!
# Theorem 8: authenticity of the Fig. 8 SM scheme

**Checked by Lean.**

Proves ACD19 §5.3.2 Theorem 8 (`theorem8`, matching `Theorem8` in `SM/Theorem8And12Statements.lean`)
for the concrete reductions `redCKAAuth`, `redPRNGAuth`, and `redFSAuth` by combining Lemmas 9–11.
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

/-- Lemma 9 (`H0 →` CKA real world): bounds the authenticity game by the real world of
`redCKAAuth` up to doomed runs. -/
theorem lemma9 (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    authAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] {true} := by
  exact AuthL9.lemma9_proof cka prng fs lam Δcka qep hc tL t A

/-- Lemma 10 (`H1 →` PRF-PRNG real world): couples `redCKAAuth` under a uniform epoch-`t_heal`
CKA key with `redPRNGAuth` under the real root RNG. -/
theorem lemma10 (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} := by
  exact AuthL10.lemma10_proof cka prng fs lam Δcka qep hc tL t A

/-- Lemma 11 (`H2 →` FS-AEAD): bounds a win in the ideal world of `redPRNGAuth` by a sum over at
most `q` epoch-`t*` FS-AEAD sessions. -/
theorem lemma11 (tL : Option ℕ) (t q : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueries A q) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      ∑ j ∈ Finset.range q, FSAEAD.advantage fs (redFSAuth cka prng fs lam Δcka qep j tL t A) := by
  exact AuthL11.lemma11_proof cka prng fs lam Δcka qep tL t q A hq

/-- Authenticity of the Fig. 8 SM scheme (`Δ_SM = 2 + Δ_CKA`, ACD19 Theorem 8; DEV-SM2,
DEV-SM27). -/
theorem theorem8 (hc : cka.Correct) :
    Theorem8 cka prng fs lam Δcka qep (redCKAAuth cka prng fs lam Δcka qep)
      (redPRNGAuth cka prng fs lam Δcka qep) (redFSAuth cka prng fs lam Δcka qep) := by
  intro tL t q A hq
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CKA.branch cka Δcka (healEpoch tL) true (redCKAAuth cka prng fs lam Δcka qep tL t A)]
  set cF := 𝒟[CKA.branch cka Δcka (healEpoch tL) false
    (redCKAAuth cka prng fs lam Δcka qep tL t A)]
  set pT := 𝒟[PRFPRNG.branch prng true (redPRNGAuth cka prng fs lam Δcka qep tL t A)]
  set pF := 𝒟[PRFPRNG.branch prng false (redPRNGAuth cka prng fs lam Δcka qep tL t A)]
  have h9 := lemma9 cka prng fs lam Δcka qep hc tL t A
  have h10 := lemma10 cka prng fs lam Δcka qep hc tL t A
  have h11 := lemma11 cka prng fs lam Δcka qep tL t q A hq
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  calc authAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A
      ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ ((∑ j ∈ Finset.range q, FSAEAD.advantage fs
          (redFSAuth cka prng fs lam Δcka qep j tL t A)) + pT.boolDist pF) + cT.boolDist cF :=
        add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ring

end CryptoGames.SM.Construction
