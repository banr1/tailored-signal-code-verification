/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.SM.Theorem8And12Statements
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# ACD19 Theorem 8 and Theorem 12 statement predicates

**Checked by Lean.**

Defines the reduction-parameterized authenticity (`Theorem8`) and privacy (`Theorem12`) statement
predicates for ACD19's Fig. 8 secure-messaging construction, along with a boolean bias triangle
inequality.
-/

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

abbrev SchemeAdversary (Γ T Sig SS RS M CCoins E : Type) :=
  Adversary (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

section Statements

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

/-- Authenticity bound for the Fig. 8 scheme with healing window `2 + Δcka` (ACD19 Theorem 8). -/
def Theorem8
    (R₁ : Option ℕ → ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E → CKA.Adversary Γ CCoins T I)
    (R₂ : Option ℕ → ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E → PRFPRNG.Adversary Sig I K)
    (R₃ : ℕ → Option ℕ → ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E →
      FSAEAD.Adversary SS RS (Header T) M E) : Prop :=
  ∀ (tL : Option ℕ) (t q : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E),
    MakesAtMostQueries A q →
    authAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A ≤
      CKA.advantage cka Δcka (healEpoch tL) (R₁ tL t A) + PRFPRNG.advantage prng (R₂ tL t A)
        + ∑ j ∈ Finset.range q, FSAEAD.advantage fs (R₃ j tL t A)

/-- Privacy bound for the Fig. 8 scheme with healing window `2 + Δcka` (ACD19 Theorem 12). -/
def Theorem12
    (R₁ : Option ℕ → ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E → CKA.Adversary Γ CCoins T I)
    (R₂ : Option ℕ → ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E → PRFPRNG.Adversary Sig I K)
    (R₃ R₃' : Option ℕ → ℕ → SchemeAdversary Γ T Sig SS RS M CCoins E →
      FSAEAD.Adversary SS RS (Header T) M E) : Prop :=
  ∀ (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E),
    privAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A ≤
      2 * CKA.advantage cka Δcka (healEpoch tL) (R₁ tL t A)
        + 2 * PRFPRNG.advantage prng (R₂ tL t A)
        + FSAEAD.advantage fs (R₃ tL t A) + 2 * FSAEAD.advantage fs (R₃' tL t A)

end Statements

theorem boolBias_le_add_two_mul_boolDist (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : μ.boolBias ≤ ν.boolBias + 2 * μ.boolDist ν := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν, Measure.boolDist]
  calc 2 * ENNReal.absDiff (μ {true}) (1 / 2)
      ≤ 2 * (ENNReal.absDiff (μ {true}) (ν {true}) + ENNReal.absDiff (ν {true}) (1 / 2)) := by
        gcongr
        exact ENNReal.absDiff_triangle _ _ _
    _ = _ := by ring

end CryptoGames.SM.Construction
