/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.E2E.SignedPrims
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma15
import Computational.Proofs.E2E.SignedRefine
import Computational.Proofs.E2E.SignedSession

/-!
# ACD19 Theorem 12 on mixtures

Bounds the bias of a prefix-indexed mixture of SM privacy games (`theorem12_mix`) using single
averaged CKA and PRF-PRNG reductions and FS-AEAD mixture terms.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Construction

theorem boolDist_bind_le_lintegral {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f].boolDist 𝒟[oa >>= g] ≤ ∫⁻ a, 𝒟[f a].boolDist 𝒟[g a] ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  refine Measure.boolDist_le_of_apply_le _ _ fun v => ?_
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono fun a => apply_le_add_boolDist _ _ v

theorem evalDist_privGame_of_not_valid {Key St Msg Coins C : Type} [DecidableEq Msg]
    [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : Adversary St Msg Coins C) (hvalid : lastLeakGuessAdmissible Δ tL t = false) :
    𝒟[privGame sm Δ qep tL t A] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  unfold privGame
  simp only [hvalid, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [evalDist_bind_congr _ _ (fun _ => ($ᵗ Bool : ProbComp Bool))
    fun b => OracleComp.evalDist_bind_const _ _]
  exact OracleComp.evalDist_bind_const _ _

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

theorem boolDist_branch_redPRNGPriv_game_le (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true) :
    𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolDist
        𝒟[FSAEAD.game fs (redFSPriv cka prng fs lam Δcka qep tL t A)] ≤
      FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A) := by
  rw [PrivL15.branch_true_eq_eager]
  simp only [PrivL15.simulateQ_redPRNGPriv]
  rw [PrivL15.evalDist_swap_three, PrivL15.evalDist_game_redFSPriv,
    PrivL15.advantage_redFSPrivCoin]
  refine PrivL15.boolDist_le_of_closeBy ?_
  refine PrivL15.closeBy_bind ($ᵗ Bool) fun b => ?_
  refine PrivL15.closeBy_bind ($ᵗ K) fun k_fs => ?_
  simp only [PrivL15.runHM_initPRNG_eq, PrivL15.runHM_initFS_eq, bind_assoc]
  refine PrivL15.closeBy_bind ($ᵗ KR) fun kr => ?_
  refine PrivL15.closeBy_bind ($ᵗ KC) fun kc => ?_
  exact PrivL15.closeBy_init_after_keys cka prng fs lam Δcka qep tL t A hvalid b k_fs kr kc

/-- ACD19 Theorem 12 privacy bound for a prefix-indexed mixture with uniform CKA and PRF-PRNG reductions. -/
theorem theorem12_mix {α : Type} (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : α → FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (hc : cka.Correct)
    (tL : Option ℕ) (t : ℕ) (oa : ProbComp α)
    (A : α → SchemeAdversary Γ T Sig SS RS M CCoins E) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= fun o => privGame (scheme cka prng (fs o) lam) (2 + Δcka) qep tL t (A o)].boolBias ≤
      2 * CKA.advantage cka Δcka (healEpoch tL)
          (advAvg oa fun o => redCKAPriv cka prng (fs o) lam Δcka qep tL t (A o))
        + 2 * PRFPRNG.advantage prng
          (advAvg oa fun o => redPRNGPriv cka prng (fs o) lam Δcka qep tL t (A o))
        + 𝒟[oa >>= fun o => FSAEAD.game (fs o)
            (redFSPriv cka prng (fs o) lam Δcka qep tL t (A o))].boolBias
        + 2 * ∫⁻ o, FSAEAD.advantage (fs o)
            (redFSPrivCoin cka prng (fs o) lam Δcka qep tL t (A o)) ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  cases hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t
  · have h0 : 𝒟[oa >>= fun o => privGame (scheme cka prng (fs o) lam) (2 + Δcka) qep tL t (A o)] =
        𝒟[($ᵗ Bool : ProbComp Bool)] := by
      rw [evalDist_bind_congr _ _ (fun _ => ($ᵗ Bool : ProbComp Bool))
        fun o => evalDist_privGame_of_not_valid _ _ qep tL t (A o) hvalid]
      exact OracleComp.evalDist_bind_const _ _
    rw [h0, PrivL13.boolBias_uniformBool]
    exact zero_le
  set cT := 𝒟[CKA.branch cka Δcka (healEpoch tL) true
    (advAvg oa fun o => redCKAPriv cka prng (fs o) lam Δcka qep tL t (A o))]
  set cF := 𝒟[CKA.branch cka Δcka (healEpoch tL) false
    (advAvg oa fun o => redCKAPriv cka prng (fs o) lam Δcka qep tL t (A o))]
  set pT := 𝒟[PRFPRNG.branch prng true
    (advAvg oa fun o => redPRNGPriv cka prng (fs o) lam Δcka qep tL t (A o))]
  set pF := 𝒟[PRFPRNG.branch prng false
    (advAvg oa fun o => redPRNGPriv cka prng (fs o) lam Δcka qep tL t (A o))]
  set G := 𝒟[oa >>= fun o => FSAEAD.game (fs o) (redFSPriv cka prng (fs o) lam Δcka qep tL t (A o))]
  have h13 : 𝒟[oa >>= fun o => privGame (scheme cka prng (fs o) lam) (2 + Δcka) qep tL t (A o)] =
      cF := by
    simp only [cF, ckaBranch_avg]
    exact evalDist_bind_congr _ _ _ fun o =>
      (PrivL13.privGame_dEq_redCKAPriv cka prng (fs o) lam Δcka qep tL t hc (A o)).evalDist_eq
  have h14 : cT = pF := by
    simp only [cT, pF, ckaBranch_avg, prngBranch_avg]
    exact evalDist_bind_congr _ _ _ fun o =>
      (PrivL14.branch_redCKAPriv_dEq_redPRNGPriv cka prng (fs o) lam Δcka qep tL t (A
      o)).evalDist_eq
  have h15 : pT.boolDist G ≤ ∫⁻ o, FSAEAD.advantage (fs o)
      (redFSPrivCoin cka prng (fs o) lam Δcka qep tL t (A o)) ∂𝒟[oa] := by
    simp only [pT, G, prngBranch_avg]
    exact (boolDist_bind_le_lintegral _ _ _).trans (lintegral_mono fun o =>
      boolDist_branch_redPRNGPriv_game_le cka prng (fs o) lam Δcka qep tL t (A o) hvalid)
  have hc' : cF.boolBias ≤ cT.boolBias + 2 * cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact boolBias_le_add_two_mul_boolDist _ _
  have hp' : pF.boolBias ≤ pT.boolBias + 2 * pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact boolBias_le_add_two_mul_boolDist _ _
  have hg : pT.boolBias ≤ G.boolBias + 2 * pT.boolDist G := boolBias_le_add_two_mul_boolDist _ _
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist, h13]
  calc cF.boolBias ≤ cT.boolBias + 2 * cT.boolDist cF := hc'
    _ ≤ (pT.boolBias + 2 * pT.boolDist pF) + 2 * cT.boolDist cF := by
        rw [h14]; exact add_le_add hp' le_rfl
    _ ≤ ((G.boolBias + 2 * ∫⁻ o, FSAEAD.advantage (fs o)
            (redFSPrivCoin cka prng (fs o) lam Δcka qep tL t (A o)) ∂𝒟[oa])
          + 2 * pT.boolDist pF) + 2 * cT.boolDist cF := by
        gcongr
        exact hg.trans (add_le_add le_rfl (mul_le_mul_right h15 2))
    _ = _ := by ring

end CryptoVerification.E2E.Signed
