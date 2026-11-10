/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedPrims
public import Computational.Proofs.CryptoGames.SM.Reductions
import Computational.Proofs.CryptoGames.SM.Theorem8
import Computational.Proofs.E2E.SignedSession

/-!
# ACD19 Theorem 8 on mixtures

Bounds the winning probability of a prefix-indexed mixture of SM authenticity games
(`theorem8_mix`) using single averaged CKA and PRF-PRNG reductions and expected FS-AEAD
advantages.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Construction

theorem evalDist_bind_apply_mono {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool) (v : Bool)
    (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v}) : 𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} := by
  let _ : MeasurableSpace α := ⊤
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  exact lintegral_mono H

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

/-- ACD19 Theorem 8 authenticity bound for a prefix-indexed mixture with uniform CKA and PRF-PRNG reductions. -/
theorem theorem8_mix {α : Type} (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : α → FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (hc : cka.Correct)
    (tL : Option ℕ) (t q : ℕ) (oa : ProbComp α) (A : α → SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= fun o => authGame (scheme cka prng (fs o) lam) (2 + Δcka) qep tL t (A o)] {true} ≤
      CKA.advantage cka Δcka (healEpoch tL)
          (advAvg oa fun o => redCKAAuth cka prng (fs o) lam Δcka qep tL t (A o))
        + PRFPRNG.advantage prng
          (advAvg oa fun o => redPRNGAuth cka prng (fs o) lam Δcka qep tL t (A o))
        + ∫⁻ o, ∑ j ∈ Finset.range q, FSAEAD.advantage (fs o)
            (redFSAuth cka prng (fs o) lam Δcka qep j tL t (A o)) ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  set cT := 𝒟[CKA.branch cka Δcka (healEpoch tL) true
    (advAvg oa fun o => redCKAAuth cka prng (fs o) lam Δcka qep tL t (A o))]
  set cF := 𝒟[CKA.branch cka Δcka (healEpoch tL) false
    (advAvg oa fun o => redCKAAuth cka prng (fs o) lam Δcka qep tL t (A o))]
  set pT := 𝒟[PRFPRNG.branch prng true
    (advAvg oa fun o => redPRNGAuth cka prng (fs o) lam Δcka qep tL t (A o))]
  set pF := 𝒟[PRFPRNG.branch prng false
    (advAvg oa fun o => redPRNGAuth cka prng (fs o) lam Δcka qep tL t (A o))]
  have h9 : 𝒟[oa >>= fun o => authGame (scheme cka prng (fs o) lam) (2 + Δcka) qep tL t (A o)]
      {true} ≤ cF {true} := by
    simp only [cF, ckaBranch_avg]
    exact evalDist_bind_apply_mono _ _ _ true fun o =>
      lemma9 cka prng (fs o) lam Δcka qep hc tL t (A o)
  have h10 : cT {true} ≤ pF {true} := by
    simp only [cT, pF, ckaBranch_avg, prngBranch_avg]
    exact evalDist_bind_apply_mono _ _ _ true fun o =>
      lemma10 cka prng (fs o) lam Δcka qep hc tL t (A o)
  have h11 : pT {true} ≤ ∫⁻ o, ∑ j ∈ Finset.range q, FSAEAD.advantage (fs o)
      (redFSAuth cka prng (fs o) lam Δcka qep j tL t (A o)) ∂𝒟[oa] := by
    simp only [pT, prngBranch_avg]
    rw [evalDist_bind_apply_lintegral]
    exact lintegral_mono fun o => lemma11 cka prng (fs o) lam Δcka qep tL t q (A o) (hq o)
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist]
  calc _ ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ (∫⁻ o, ∑ j ∈ Finset.range q, FSAEAD.advantage (fs o)
            (redFSAuth cka prng (fs o) lam Δcka qep j tL t (A o)) ∂𝒟[oa] + pT.boolDist pF)
          + cT.boolDist cF := add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ring

end CryptoVerification.E2E.Signed
