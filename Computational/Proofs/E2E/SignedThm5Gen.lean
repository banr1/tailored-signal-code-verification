/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
public import Computational.Proofs.E2E.SignedAdv
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Final
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Generic ACD19 Theorem 5 on mixtures

Bounds the bias of a prefix-indexed mixture of `fromAEADPRG` FS-AEAD games (`theorem5_mix_multi`)
by single averaged chain-PRG reductions per hop plus `multiOtBranch` mixture distances.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal CryptoGames CryptoGames.Lazy
open CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5 CryptoGames.FSAEAD.Thm5.Ends

namespace CryptoVerification.E2E.Signed.Thm5Mix

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  {α : Type} (oa : ProbComp α) (ae : α → AEADScheme MK (ℕ × AD) M C)
  (A : α → RatchetAdversary CK MK AD M C)

theorem evalDist_mix_congr {f g : α → ProbComp Bool} (h : ∀ o, 𝒟[f o] = 𝒟[g o]) :
    𝒟[oa >>= f] = 𝒟[oa >>= g] :=
  evalDist_bind_congr oa f g h

theorem evalDist_mix_true_const {f : α → ProbComp Bool} {p : ℝ≥0∞}
    (h : ∀ o, 𝒟[f o] {true} = p) : 𝒟[oa >>= f] {true} = p := by
  rw [evalDist_bind_apply_lintegral]
  simp only [h, lintegral_const, measure_univ, mul_one]

theorem closeBy_start (ok : AD → Bool) (o : α) (hae : (ae o).CorrectOn fun ia => ok ia.2)
    (hA : EncADsOk ok (A o)) :
    CloseBy (game (fromAEADPRG (ae o) G maxSkip) (A o))
      (hybridA ideal (ae o) G maxSkip 0 false (A o))
      (hybridA ideal (ae o) G maxSkip 0 true (A o)) := by
  have hclose : CloseBy
      (($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implR (ae o) G maxSkip) (A o)).run
          (initState (fromAEADPRG (ae o) G maxSkip) k b) >>=
          fun z => pure ((z.2.b == z.1) || z.2.win))
      (($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implH ideal (ae o) G maxSkip false) (A o)).run (hInit b (.seed k)) >>=
          fun z => pure (hOut false z))
      (($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implH ideal (ae o) G maxSkip true) (A o)).run (hInit b (.seed k)) >>=
          fun z => pure (hOut true z)) := by
    refine closeBy_bind ($ᵗ Bool) fun b => closeBy_bind ($ᵗ CK) fun k => ?_
    refine Thm5On.closeBy_simulateQ_of_syncRML_on ideal (ae o) G maxSkip hae (A o) hA _ _ _ ?_ ?_
      (syncRML_init (ae o) G maxSkip k b) (Thm5On.inTransitOk_hInit ok b (.seed k))
    · intro a stR sM hsync
      rw [hsync.stR_eq]
      rfl
    · intro z hlf
      simp [hOut, hlf]
  intro s
  have h := hclose s
  rwa [← game_evalDist_eq (ae o) G maxSkip (A o),
    ← hybA_zero_evalDist ideal (ae o) G maxSkip false (A o),
    ← hybA_zero_evalDist ideal (ae o) G maxSkip true (A o)] at h

theorem start_mix (ok : AD → Bool) (hae : ∀ o, (ae o).CorrectOn fun ia => ok ia.2)
    (hA : ∀ o, EncADsOk ok (A o)) :
    𝒟[oa >>= fun o => game (fromAEADPRG (ae o) G maxSkip) (A o)].boolBias ≤
      2 * ENNReal.absDiff
          (𝒟[oa >>= fun o => hybridA ideal (ae o) G maxSkip 0 false (A o)] {true}) (1 / 2) +
        2 * 𝒟[oa >>= fun o => hybridA ideal (ae o) G maxSkip 0 true (A o)] {true} := by
  have hcb := closeBy_bind oa (fun o => closeBy_start ideal G maxSkip ae A ok o (hae o) (hA o))
    {true}
  set g := 𝒟[oa >>= fun o => game (fromAEADPRG (ae o) G maxSkip) (A o)] {true}
  set x := 𝒟[oa >>= fun o => hybridA ideal (ae o) G maxSkip 0 false (A o)] {true}
  set y := 𝒟[oa >>= fun o => hybridA ideal (ae o) G maxSkip 0 true (A o)] {true}
  have hdiff : ENNReal.absDiff g x ≤ y := ENNReal.absDiff_le_iff.mpr hcb
  have htri : ENNReal.absDiff g (1 / 2) ≤ ENNReal.absDiff x (1 / 2) + y :=
    calc ENNReal.absDiff g (1 / 2) ≤ ENNReal.absDiff g x + ENNReal.absDiff x (1 / 2) :=
          ENNReal.absDiff_triangle _ _ _
      _ ≤ y + ENNReal.absDiff x (1 / 2) := by gcongr
      _ = _ := add_comm _ _
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, ← mul_add]
  gcongr

theorem hop_mix_eq (la : Bool) (k : ℕ) :
    𝒟[oa >>= fun o => hRunWith ideal (ae o) G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (A o) .unknown].boolDist
      𝒟[oa >>= fun o => hRunWith ideal (ae o) G maxSkip (hp (k + 1) 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (A o) .unknown] =
      (G ((2 * k + la.toNat) / 2)).prgAdvantage
        (prgAvg oa fun o => cumulativeChainPrgReduction ideal (ae o) G maxSkip (2 * k + la.toNat) (A o)) := by
  have h1 : (2 * k + la.toNat) / 2 = k := by
    cases la <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have h2 : isLookaheadHop (2 * k + la.toNat) = la := by
    cases la <;> simp [isLookaheadHop, Nat.add_mod]
  have hR : ∀ o, 𝒟[hRunWith ideal (ae o) G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (A o) .unknown] =
      𝒟[(G k).prgRealExperiment
        (cumulativeChainPrgReduction ideal (ae o) G maxSkip (2 * k + la.toNat) (A o))] := by
    intro o
    have := hybZero_eq_prgReal ideal (ae o) G maxSkip (A o) (2 * k + la.toNat)
    rw [h1, h2] at this
    exact this
  have hI : ∀ o, 𝒟[hRunWith ideal (ae o) G maxSkip (hp (k + 1) 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (A o) .unknown] =
      𝒟[PRGScheme.prgIdealExperiment
        (cumulativeChainPrgReduction ideal (ae o) G maxSkip (2 * k + la.toNat) (A o))] := by
    intro o
    have := prgIdeal_eq_hybZero_succ ideal (ae o) G maxSkip (A o) (2 * k + la.toNat)
    rw [h1, h2] at this
    exact this.symm
  rw [h1, evalDist_mix_congr oa hR, evalDist_mix_congr oa hI, PRGScheme.prgAdvantage,
    prgReal_avg, prgIdeal_avg]

theorem chain_mix (la : Bool) (N : ℕ) :
    𝒟[oa >>= fun o => hybridA ideal (ae o) G maxSkip 0 la (A o)].boolDist
      𝒟[oa >>= fun o => hybridA ideal (ae o) G maxSkip N la (A o)] ≤
    (∑ k ∈ Finset.range N,
      (G ((2 * k + la.toNat) / 2)).prgAdvantage
        (prgAvg oa fun o => cumulativeChainPrgReduction ideal (ae o) G maxSkip (2 * k + la.toNat) (A o))) +
      𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true N
          (multiSlotOtccaReduction ideal (ae o) G maxSkip N la (A o))].boolDist
        𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false N
          (multiSlotOtccaReduction ideal (ae o) G maxSkip N la (A o))] := by
  refine (Measure.boolDist_triangle _
    𝒟[oa >>= fun o => hRunWith ideal (ae o) G maxSkip (hp N 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (A o) .unknown] _).trans ?_
  refine add_le_add ?_ (le_of_eq ?_)
  · unfold hybridA
    refine (Measure.boolDist_le_sum_range
      (fun k => 𝒟[oa >>= fun o => hRunWith ideal (ae o) G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (A o) .unknown]) N).trans ?_
    exact le_of_eq (Finset.sum_congr rfl fun k _ => hop_mix_eq ideal G maxSkip oa ae A la k)
  · rw [evalDist_mix_congr oa (fun o => (multiOtBranch_false_eq_hRunWith ideal (ae o) G maxSkip
        N la (A o)).symm),
      evalDist_mix_congr oa (fun o => (multiOtBranch_true_eq_hybAWith ideal (ae o) G maxSkip
        N la (A o)).symm),
      Measure.boolDist_comm]

/-- Two-stage ACD19 Theorem 5 bound for a prefix-indexed mixture of `fromAEADPRG` games. -/
theorem theorem5_mix_multi (ok : AD → Bool) (hae : ∀ o, (ae o).CorrectOn fun ia => ok ia.2)
    (q : ℕ) (hq : ∀ o, MakesAtMostQueries (A o) q) (hA : ∀ o, EncADsOk ok (A o)) :
    𝒟[oa >>= fun o => game (fromAEADPRG (ae o) G maxSkip) (A o)].boolBias ≤
      2 * ∑ j ∈ Finset.range (slotCount maxSkip q),
        (G (slotToHybridHopIndex q j / 2)).prgAdvantage
          (prgAvg oa fun o => cumulativeChainPrgReduction ideal (ae o) G maxSkip (slotToHybridHopIndex q j) (A o)) +
      2 * (𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true q
            (multiSlotOtccaReduction ideal (ae o) G maxSkip q false (A o))].boolDist
          𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false q
            (multiSlotOtccaReduction ideal (ae o) G maxSkip q false (A o))] +
        𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true (q + (maxSkip + 1))
            (multiSlotOtccaReduction ideal (ae o) G maxSkip (q + (maxSkip + 1)) true (A o))].boolDist
          𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false (q + (maxSkip + 1))
            (multiSlotOtccaReduction ideal (ae o) G maxSkip (q + (maxSkip + 1)) true (A o))]) := by
  set fP : ℕ → ℝ≥0∞ := fun j =>
    (G (j / 2)).prgAdvantage (prgAvg oa fun o => cumulativeChainPrgReduction ideal (ae o) G maxSkip j (A o))
  have hmain := chain_mix ideal G maxSkip oa ae A false q
  have hla := chain_mix ideal G maxSkip oa ae A true (q + (maxSkip + 1))
  simp only [Bool.toNat_false, add_zero, Bool.toNat_true] at hmain hla
  rw [Measure.boolDist, evalDist_mix_true_const oa
    (fun o => final_main_idx ideal (ae o) G maxSkip (A o) q (hq o))] at hmain
  rw [Measure.boolDist, evalDist_mix_true_const oa
    (fun o => final_la_idx ideal (ae o) G maxSkip (A o) q (hq o)),
    ENNReal.absDiff_zero_right] at hla
  calc _ ≤ _ := start_mix ideal G maxSkip oa ae A ok hae hA
    _ ≤ 2 * ((∑ k ∈ Finset.range q, fP (2 * k)) +
          𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true q
              (multiSlotOtccaReduction ideal (ae o) G maxSkip q false (A o))].boolDist
            𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false q
              (multiSlotOtccaReduction ideal (ae o) G maxSkip q false (A o))]) +
        2 * ((∑ k ∈ Finset.range (q + (maxSkip + 1)), fP (2 * k + 1)) +
          𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true (q + (maxSkip + 1))
              (multiSlotOtccaReduction ideal (ae o) G maxSkip (q + (maxSkip + 1)) true (A o))].boolDist
            𝒟[oa >>= fun o => multiOtBranch ideal (ae o) false (q + (maxSkip + 1))
              (multiSlotOtccaReduction ideal (ae o) G maxSkip (q + (maxSkip + 1)) true (A o))]) := by
        gcongr
    _ = _ := by
        rw [sum_range_hopIdx fP maxSkip q]
        ring

end CryptoVerification.E2E.Signed.Thm5Mix
