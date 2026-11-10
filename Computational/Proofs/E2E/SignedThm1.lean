/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.CryptoGames.SM.SessionProofs.BlankLemma18
public import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17
public import Computational.Proofs.E2E.SignedPrims
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.SignedThm12
import Computational.Proofs.E2E.SignedThm8

/-!
# Blanked ACD19 Theorems 1 and 6 at `H1` on mixtures

Lifts the blanked `H1` security bounds (`theorem1_h1_blank_mix` and `theorem6_h1_blank_mix`) to
prefix-indexed mixtures, with single averaged CKA and PRF-PRNG reductions.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
  CryptoGames.SM.Thm1.L18 CryptoGames.LibsignalSM.Proofs.BlankLemma18

section Generic

variable {Key St Msg Coins C Pub : Type} [DecidableEq Msg] [DecidableEq C]
  [SampleableType Key] [SampleableType Coins]

theorem boolBias_mix_eq_zero {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (h : ∀ a, 𝒟[f a].boolBias = 0) : 𝒟[oa >>= f].boolBias = 0 := by
  let _ : MeasurableSpace α := ⊤
  have h' : ∀ a, 𝒟[f a] {true} = 𝒟[f a] {false} := fun a =>
    ENNReal.absDiff_eq_zero.mp (h a)
  change ENNReal.absDiff _ _ = 0
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  simp only [h', ENNReal.absDiff_self]

theorem closeBySum_h1_h2 (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (A : Adversary St Msg Coins C) :
    CloseBySum Δ qep (game sm Δ qep Config.h1 A) (game sm Δ qep Config.h2 A)
      (fun t tL => authGame sm Δ qep tL t (challSim Δ qep A)) := by
  let f (b : Bool) : Bool × GameState St Msg C → ProbComp Bool :=
    fun z => pure (b == z.1 || z.2.win)
  let fAuth (t : ℕ) (tL : Option ℕ) :
      (Bool × Mirror Msg C) × GameState St Msg C → ProbComp Bool :=
    fun z => pure (z.2.win && authLosingConditionsAvoided Δ tL t z.2)
  have hclose : CloseBySum Δ qep
      (game sm Δ qep Config.h1 A)
      (game sm Δ qep Config.h2 A)
      (fun t tL =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (fullImpl sm Δ qep (Config.auth t))
            ((simulateQ (simImpl Δ qep (fun _ => none) none) A).run
              (toMirror (initState sm k b)))).run (toAuth (initState sm k b)) >>=
            fAuth t tL) := by
    unfold game run
    simp only [bind_assoc]
    refine closeBySum_bind Δ qep ($ᵗ Bool : ProbComp Bool) fun b =>
      closeBySum_bind Δ qep ($ᵗ Key : ProbComp Key) fun k => ?_
    exact closeBySum_simulateQ sm Δ qep hΔ A (f b) (f b) fAuth
      (fun _ _ _ => rfl)
      (fun t tL z hwin hok => by simp [fAuth, hwin, hok])
      (wfState_init sm Δ k b) rfl
  intro ev
  have htr := hclose ev
  dsimp only [fAuth] at htr
  simp_rw [← authGame_challSim_evalDist sm Δ qep _ _ A] at htr
  exact htr

theorem lemma17_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (oa : ProbComp α) (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => game (sm o) Δ qep Config.h1 (A o)].boolBias ≤
      𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)].boolBias +
        2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
          𝒟[oa >>= fun o => authGame (sm o) Δ qep tL t (challSim Δ qep (A o))] {true} := by
  have hclose := closeBySum_bind Δ qep oa
    (f1 := fun o => game (sm o) Δ qep Config.h1 (A o))
    (f2 := fun o => game (sm o) Δ qep Config.h2 (A o))
    (fAuth := fun t tL o => authGame (sm o) Δ qep tL t (challSim Δ qep (A o)))
    fun o => closeBySum_h1_h2 (sm o) Δ qep hΔ (A o)
  set S := ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
    𝒟[oa >>= fun o => authGame (sm o) Δ qep tL t (challSim Δ qep (A o))] {true}
  set μ1 := 𝒟[oa >>= fun o => game (sm o) Δ qep Config.h1 (A o)]
  set μ2 := 𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)]
  have hdiff : ENNReal.absDiff (μ1 {true}) (μ2 {true}) ≤ S :=
    ENNReal.absDiff_le_iff.mpr (hclose {true})
  have htri : ENNReal.absDiff (μ1 {true}) (1 / 2) ≤ ENNReal.absDiff (μ2 {true}) (1 / 2) + S := by
    calc ENNReal.absDiff (μ1 {true}) (1 / 2)
        ≤ ENNReal.absDiff (μ1 {true}) (μ2 {true}) + ENNReal.absDiff (μ2 {true}) (1 / 2) :=
          ENNReal.absDiff_triangle _ _ _
      _ ≤ S + ENNReal.absDiff (μ2 {true}) (1 / 2) := by gcongr
      _ = _ := add_comm _ _
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
      Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, ← mul_add]
  gcongr

theorem evalDist_select_mix {α : Type} (oa : ProbComp α) (x y : α → ProbComp Bool) :
    𝒟[do let sel ← $ᵗ Bool; if sel then oa >>= x else oa >>= y] =
      𝒟[oa >>= fun o => do let sel ← $ᵗ Bool; if sel then x o else y o] := by
  have h : (do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then oa >>= x else oa >>= y) =
      (($ᵗ Bool : ProbComp Bool) >>= fun sel => oa >>= fun o => if sel then x o else y o) := by
    refine bind_congr fun sel => ?_
    cases sel <;> rfl
  rw [h, OracleComp.evalDist_bind_bind_swap]

theorem evalDist_mix_uniformBool {α : Type} (oa : ProbComp α) :
    𝒟[oa >>= fun _ => ($ᵗ Bool : ProbComp Bool)] = 𝒟[($ᵗ Bool : ProbComp Bool)] :=
  OracleComp.evalDist_bind_const _ _

theorem evalDist_select_gameKillB_insert_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (S : Finset (Option ℕ)) (tL : Option ℕ) (htL_not : tL ∉ S)
    (hval : lastLeakGuessAdmissible Δ tL i = true) (challMsg : ℕ → Option (Msg → Msg)) (oa : ProbComp α)
    (A : α → Adversary St Msg Coins C) :
    𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i S challMsg (A o) else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i (insert tL S) challMsg (A o)
        else oa >>= fun o => hybBranchB (sm o) Δ qep tL i challMsg (A o)] := by
  have h0 : 𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i S challMsg (A o) else $ᵗ Bool] =
      𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i S challMsg (A o)
        else oa >>= fun _ => ($ᵗ Bool : ProbComp Bool)] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · exact (evalDist_mix_uniformBool oa).symm
    · rfl
  rw [h0, evalDist_select_mix, evalDist_select_mix]
  exact evalDist_bind_congr oa _ _ fun o =>
    evalDist_select_gameKillB_insert (sm o) Δ qep i S tL htL_not hval challMsg (A o)

theorem boolBias_mix_privGame_privRedB {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (tL : Option ℕ) (i : ℕ) (blank : Msg → Msg) (oa : ProbComp α)
    (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias =
      𝒟[oa >>= fun o => hybBranchB (sm o) Δ qep tL i (challMsgB i blank) (A o)].boolDist
        𝒟[oa >>= fun o => hybBranchB (sm o) Δ qep tL i (challMsgB (i + 1) blank) (A o)] := by
  rw [← evalDist_boolBias_bind_uniformBool]
  congr 1
  unfold privGame
  rw [OracleComp.evalDist_bind_bind_swap]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  rw [evalDist_bind_congr oa _
    (fun o => do
      let z ← hybBranchB (sm o) Δ qep tL i (challMsgHybB i blank b) (A o)
      return (b == z))
    fun o => evalDist_privRedB_run (sm o) Δ qep tL i blank b (A o)]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    rfl
  · simp only [↓reduceIte, bind_assoc]
    rfl

theorem gameKillB_mix_union_le {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (blank : Msg → Msg) (oa : ProbComp α) (A : α → Adversary St Msg Coins C)
    (T : Finset (Option ℕ)) (hval : ∀ tL ∈ T, lastLeakGuessAdmissible Δ tL i = true) :
    ∀ S : Finset (Option ℕ), Disjoint S T →
      𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB i blank) (A o)].boolDist
          𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB (i + 1) blank) (A o)] ≤
        𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (S ∪ T) (challMsgB i blank) (A o)].boolDist
            𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (S ∪ T) (challMsgB (i + 1) blank) (A o)] +
          ∑ tL ∈ T, 𝒟[oa >>= fun o =>
            privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  induction T using Finset.induction_on with
  | empty =>
    intro S _
    simp
  | @insert tL T htL_not_T ih =>
    intro S hdisj
    have htL_not_S : tL ∉ S := Finset.disjoint_insert_right.mp hdisj |>.1
    have hdisj' : Disjoint (insert tL S) T := by
      rw [Finset.disjoint_insert_left]
      exact ⟨htL_not_T, Finset.disjoint_insert_right.mp hdisj |>.2⟩
    have hvtL := hval tL (Finset.mem_insert_self tL T)
    have hstep :
        𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB i blank) (A o)].boolDist
            𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB (i + 1) blank) (A o)] ≤
          𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (insert tL S) (challMsgB i blank)
              (A o)].boolDist
            𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (insert tL S) (challMsgB (i + 1) blank)
              (A o)] +
          𝒟[oa >>= fun o =>
            privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
      rw [boolBias_mix_privGame_privRedB]
      exact boolDist_le_of_select_eq _ _ _ _ _ _
        (evalDist_select_gameKillB_insert_mix sm Δ qep i S tL htL_not_S hvtL
          (challMsgB i blank) oa A)
        (evalDist_select_gameKillB_insert_mix sm Δ qep i S tL htL_not_S hvtL
          (challMsgB (i + 1) blank) oa A)
    have hih := ih (fun x hx => hval x (Finset.mem_insert_of_mem hx)) (insert tL S) hdisj'
    have hunion : insert tL S ∪ T = S ∪ insert tL T := by
      ext x; simp
    rw [hunion] at hih
    rw [Finset.sum_insert htL_not_T]
    calc _ ≤ _ := hstep
      _ ≤ _ := add_le_add hih le_rfl
      _ = _ := by ring

theorem lemma18B_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (blank : Msg → Msg) (i : ℕ) (oa : ProbComp α) (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB i blank) (A o)].boolBias ≤
      𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (i + 1) blank) (A o)].boolBias +
        2 * ∑ tL ∈ admissibleLastLeakGuesses Δ i, 𝒟[oa >>= fun o =>
          privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  refine (boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB i blank) (A o)]
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (i + 1) blank) (A o)]).trans ?_
  gcongr
  have hunion := gameKillB_mix_union_le sm Δ qep i blank oa A (admissibleLastLeakGuesses Δ i)
    (fun tL htL => validGuess_of_mem_targetsL Δ hΔ htL) ∅ (Finset.disjoint_empty_left _)
  simp only [Finset.empty_union, gameKillB_empty] at hunion
  rw [evalDist_bind_congr oa
      (fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i) (challMsgB i blank) (A o))
      (fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i) (challMsgB (i + 1) blank) (A o))
      fun o => evalDist_gameKillB_targetsL_eq (sm o) Δ qep hΔ i blank (A o),
    Measure.boolDist_self, zero_add] at hunion
  exact hunion

/-- Blanked ACD19 Theorem 1 at `H1` for a prefix-indexed mixture of SM games. -/
theorem theorem1_h1_blank_mix [DecidableEq Pub] {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (hΔ : 0 < Δ) (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁) (oa : ProbComp α)
    (A : α → Adversary St Msg Coins C) (heq : ∀ o, EqualPubChalls pubOf (A o)) :
    𝒟[oa >>= fun o => game (sm o) Δ qep Config.h1 (A o)].boolBias ≤
      2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
            𝒟[oa >>= fun o => authGame (sm o) Δ qep tL t (challSim Δ qep (A o))] {true}
        + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses Δ i,
            𝒟[oa >>= fun o =>
              privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  have h17 := lemma17_mix sm Δ qep hΔ oa A
  have htel : ∀ n : ℕ,
      𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)].boolBias ≤
        𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB n blank) (A o)].boolBias +
          2 * ∑ i ∈ Finset.range n, ∑ tL ∈ admissibleLastLeakGuesses Δ i, 𝒟[oa >>= fun o =>
            privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
    intro n
    induction n with
    | zero =>
      simp only [challMsgB_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      exact le_rfl
    | succ n ih =>
      refine ih.trans ?_
      have h := lemma18B_mix sm Δ qep hΔ blank n oa A
      rw [Finset.sum_range_succ, mul_add]
      calc _ ≤ _ := add_le_add h le_rfl
        _ = _ := by ring
  have hfin : 𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (qep + 1) blank) (A o)].boolBias =
      0 :=
    boolBias_mix_eq_zero oa _ fun o => h3B_final_proof (sm o) Δ qep pubOf blank hblank (A o) (heq o)
  have h18 := htel (qep + 1)
  rw [hfin, zero_add] at h18
  calc _ ≤ _ := h17
    _ ≤ _ + _ := add_le_add h18 le_rfl
    _ = _ := by ring

end Generic

section Scheme

open CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] [DecidableEq Pub]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

/-- Blanked ACD19 Theorem 6 at `H1` for a prefix-indexed mixture with uniform CKA and PRF-PRNG reductions. -/
theorem theorem6_h1_blank_mix {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : α → FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (hc : cka.Correct) (pubOf : M → Pub) (blank : M → M)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁) (oa : ProbComp α)
    (A : α → SchemeAdversary Γ T Sig SS RS M CCoins E) (heq : ∀ o, EqualPubChalls pubOf (A o))
    (q : ℕ) (hq : ∀ o, MakesAtMostQueries (A o) q) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= fun o => game (scheme cka prng (fs o) lam) (2 + Δcka) qep Config.h1 (A o)].boolBias ≤
      2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
          (CKA.advantage cka Δcka (healEpoch tL)
              (advAvg oa fun o => redCKAAuth cka prng (fs o) lam Δcka qep tL t
                (challSim (2 + Δcka) qep (A o)))
            + PRFPRNG.advantage prng
              (advAvg oa fun o => redPRNGAuth cka prng (fs o) lam Δcka qep tL t
                (challSim (2 + Δcka) qep (A o)))
            + ∫⁻ o, ∑ j ∈ Finset.range q, FSAEAD.advantage (fs o)
                (redFSAuth cka prng (fs o) lam Δcka qep j tL t
                  (challSim (2 + Δcka) qep (A o))) ∂𝒟[oa])
        + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) i,
          (2 * CKA.advantage cka Δcka (healEpoch tL)
              (advAvg oa fun o => redCKAPriv cka prng (fs o) lam Δcka qep tL i
                (ThmB.privRedB (2 + Δcka) qep i blank (A o)))
            + 2 * PRFPRNG.advantage prng
              (advAvg oa fun o => redPRNGPriv cka prng (fs o) lam Δcka qep tL i
                (ThmB.privRedB (2 + Δcka) qep i blank (A o)))
            + 𝒟[oa >>= fun o => FSAEAD.game (fs o)
                (redFSPriv cka prng (fs o) lam Δcka qep tL i
                  (ThmB.privRedB (2 + Δcka) qep i blank (A o)))].boolBias
            + 2 * ∫⁻ o, FSAEAD.advantage (fs o)
                (redFSPrivCoin cka prng (fs o) lam Δcka qep tL i
                  (ThmB.privRedB (2 + Δcka) qep i blank (A o))) ∂𝒟[oa]) := by
  refine (theorem1_h1_blank_mix (fun o => scheme cka prng (fs o) lam) (2 + Δcka) qep (by omega)
    pubOf blank hblank oa A heq).trans ?_
  gcongr with t _ tL _ i _ tL _
  · exact theorem8_mix cka prng fs lam Δcka qep hc tL t q oa _
      fun o => Thm1.challSim_queries _ _ (A o) q (hq o)
  · exact theorem12_mix cka prng fs lam Δcka qep hc tL i oa _

end Scheme

end CryptoVerification.E2E.Signed
