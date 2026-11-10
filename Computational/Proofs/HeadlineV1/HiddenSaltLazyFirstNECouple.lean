/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERel
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS
import ProofLib.SepLogic.WP.StateNorm

/-!
# `firstNESimImpl` Paper-Engine Coupling

Defines the shifted paper games and advantages, the per-cell parameters `cellDelta`, `cellShift`,
and `cellWinPred`, and the pre-divergence leak-shift relation `ShiftedLeakRel` with its step lemmas.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSM.Proofs.Refinement

/-- Authenticity predicate for the `Δ = 2` shifted paper game requiring
`SM.authLosingConditionsAvoided 2 tL tStar s` and `(Party.senderOf tStar, tStar) ∉ s.corrs`. -/
def authOKDir2 {St Msg C : Type} (tL : Option ℕ) (tStar : ℕ)
    (s : SM.GameState St Msg C) : Bool :=
  SM.authLosingConditionsAvoided 2 tL tStar s &&
    !(s.corrs.any (fun pe => pe.1 == Party.senderOf tStar && pe.2 == tStar))

export CryptoGames.SM.Construction.DeliverForge (
  trivB1 injectImplB1 deliverForgeBaseImplB1
  corrImplShiftedPaper oracleImplShiftedPaper oracleImplShiftedDir2Paper
  oracleImplBaseDFShiftedPaper oracleImplBaseDFShiftedDir2Paper
  fullImplBaseDFShiftedPaper fullImplBaseDFShiftedDir2Paper
  runBaseDFShiftedPaper runBaseDFShiftedDir2Paper
)

/-- Shifted paper `DeliverForge` game at `Δ = 2` and shift boundary `l = tStar - 1`. -/
def forgeGameGuessedShiftedDir2Paper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let (_, s') ←
    DeliverForge.runBaseDFShiftedDir2Paper sm l qep tStar sameHdr (SM.Config.auth tStar) false B
  return s'.win && authOKDir2 (some (l - 1)) tStar s'

noncomputable def forgeGuessedAdvantageShiftedDir2Paper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGameGuessedShiftedDir2Paper sm qep sameHdr l tStar B] {true}

/-- `Δ`-parametric shifted paper `DeliverForge` game at shift boundary `l = tStar - 2`. -/
def forgeGameGuessedShiftedPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp Bool := do
  let (_, s') ← runBaseDFShiftedPaper sm Δ l qep sameHdr (SM.Config.auth tStar) false B
  return s'.win && SM.authLosingConditionsAvoided Δ (some (l - 1)) tStar s'

noncomputable def forgeGuessedAdvantageShiftedPaper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool)
    (l tStar : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  𝒟[forgeGameGuessedShiftedPaper sm Δ qep sameHdr l tStar B] {true}

/-- Per-cell paper `DeliverForge` advantage (3-way dispatch). -/
noncomputable def forgeGuessedAdvantageCellPaper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    forgeGuessedAdvantageShiftedDir2Paper sm qep sameHdr (t - 1) t B
  else if 3 ≤ t ∧ tL = some (t - 3) then
    forgeGuessedAdvantageShiftedPaper sm (2 + 1) qep sameHdr (t - 2) t B
  else
    DeliverForge.forgeGuessedAdvantagePaper sm (2 + 1) qep sameHdr tL t B

def cellDelta (tL : Option ℕ) (t : ℕ) : ℕ :=
  if 2 ≤ t ∧ tL = some (t - 2) then 2 else 2 + 1

def cellShift (tL : Option ℕ) (t : ℕ) : ℕ :=
  if 2 ≤ t ∧ tL = some (t - 2) then t - 1 else if 3 ≤ t ∧ tL = some (t - 3) then t - 2 else 0

def cellWinPred {St Msg C : Type} (tL : Option ℕ) (t : ℕ) (s : SM.GameState St Msg C) : Bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then s.win && authOKDir2 (some (t - 2)) t s
  else s.win && SM.authLosingConditionsAvoided (2 + 1) tL t s

/-- Pre-divergence structural and leak-shift relation between unshifted `s_unsh` and shifted
`s_sh` at boundary `l`. -/
structure ShiftedLeakRel {St Msg C : Type} (l : ℕ)
    (s_unsh s_sh : SM.GameState St Msg C) : Prop where
  st_eq : s_sh.st = s_unsh.st
  b_eq : s_sh.b = s_unsh.b
  epoch_eq : s_sh.epoch = s_unsh.epoch
  idx_eq : s_sh.idx = s_unsh.idx
  maxAcc_eq : s_sh.maxAcc = s_unsh.maxAcc
  trans_eq : s_sh.trans = s_unsh.trans
  chall_eq : s_sh.chall = s_unsh.chall
  corrs_eq : s_sh.corrs = s_unsh.corrs
  leaks_sh_to_unsh : ∀ e_sh ∈ s_sh.leaks,
    ∃ m ∈ s_unsh.leaks, e_sh ≤ m ∧ m ≤ e_sh + 1 ∧ (m = e_sh + 1 → m = l)
  leaks_unsh_to_sh : ∀ m ∈ s_unsh.leaks,
    (m ≠ l → m ∈ s_sh.leaks) ∧ (m = l → l ∈ s_sh.leaks ∨ l - 1 ∈ s_sh.leaks)
  leak_corr_unsh : DeliverForge.LeakCorrInv s_unsh
  tL_sh_none : s_sh.tL = none → s_sh.leaks = []
  tL_sh_some : ∀ k, s_sh.tL = some k → k ∈ s_sh.leaks ∧ ∀ x ∈ s_sh.leaks, x ≤ k
  leaks_sh_ge_l : 1 ≤ l → ∀ x ∈ s_sh.leaks, l ≤ x → ∃ P e, (P, e) ∈ s_unsh.corrs ∧ l ≤ e

theorem cellDelta_le_three (tL : Option ℕ) (t : ℕ) : cellDelta tL t ≤ 2 + 1 := by
  unfold cellDelta
  split_ifs <;> omega

theorem two_le_cellDelta (tL : Option ℕ) (t : ℕ) : 2 ≤ cellDelta tL t := by
  unfold cellDelta
  split_ifs <;> omega

theorem pos_cellDelta (tL : Option ℕ) (t : ℕ) : 0 < cellDelta tL t := by
  have := two_le_cellDelta tL t
  omega

theorem shiftedLeakRel_init {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (l : ℕ) (k : Key) (b : Bool) :
    ShiftedLeakRel l (SM.initState sm k b) (SM.initState sm k b) where
  st_eq := rfl
  b_eq := rfl
  epoch_eq := rfl
  idx_eq := rfl
  maxAcc_eq := rfl
  trans_eq := rfl
  chall_eq := rfl
  corrs_eq := rfl
  leaks_sh_to_unsh := by intro _ h; nomatch h
  leaks_unsh_to_sh := by intro _ h; nomatch h
  leak_corr_unsh := DeliverForge.LeakCorrInv.init sm k b
  tL_sh_none := fun _ => rfl
  tL_sh_some := by intro _ h; nomatch h
  leaks_sh_ge_l := by intro _ _ h; nomatch h

theorem ShiftedLeakRel.transmit_step {St Msg C : Type} (l Δ_unsh Δ_sh qep : ℕ)
    (P : Party) (st' : St) (rec_r : SM.Record Msg C)
    {s_unsh s_unsh₁ s_sh s_sh₁ : SM.GameState St Msg C}
    (hrel : ShiftedLeakRel l s_unsh s_sh)
    (hep_unsh : s_unsh.epMgmt Δ_unsh qep P false = some s_unsh₁)
    (hep_sh : s_sh.epMgmt Δ_sh qep P false = some s_sh₁) :
    ShiftedLeakRel l (s_unsh₁.record Δ_unsh P st' rec_r false)
      (s_sh₁.record Δ_sh P st' rec_r false) := by
  unfold SM.GameState.epMgmt at hep_unsh hep_sh
  rw [hrel.epoch_eq] at hep_sh
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep_unsh hep_sh
  split_ifs at hep_unsh hep_sh with h1 h2
  · injection hep_unsh with hu
    injection hep_sh with hs
    subst hu hs
    refine
      { st_eq := by simp [SM.GameState.record, hrel.st_eq]
        b_eq := by simp [SM.GameState.record, hrel.b_eq]
        epoch_eq := by simp [SM.GameState.record, hrel.epoch_eq]
        idx_eq := by simp [SM.GameState.record, hrel.idx_eq]
        maxAcc_eq := by simp [SM.GameState.record, hrel.maxAcc_eq]
        trans_eq := by simp [SM.GameState.record, hrel.trans_eq]
        chall_eq := by simp [SM.GameState.record, hrel.chall_eq]
        corrs_eq := by simp [SM.GameState.record, hrel.corrs_eq]
        leaks_sh_to_unsh := by simpa [SM.GameState.record] using hrel.leaks_sh_to_unsh
        leaks_unsh_to_sh := by simpa [SM.GameState.record] using hrel.leaks_unsh_to_sh
        leak_corr_unsh := hrel.leak_corr_unsh
        tL_sh_none := by simpa [SM.GameState.record] using hrel.tL_sh_none
        tL_sh_some := by simpa [SM.GameState.record] using hrel.tL_sh_some
        leaks_sh_ge_l := by simpa [SM.GameState.record] using hrel.leaks_sh_ge_l }
  · injection hep_unsh with hu
    injection hep_sh with hs
    subst hu hs
    refine
      { st_eq := by simp [SM.GameState.record, hrel.st_eq]
        b_eq := by simp [SM.GameState.record, hrel.b_eq]
        epoch_eq := by simp [SM.GameState.record, hrel.epoch_eq]
        idx_eq := by simp [SM.GameState.record, hrel.idx_eq]
        maxAcc_eq := by simp [SM.GameState.record, hrel.maxAcc_eq]
        trans_eq := by simp [SM.GameState.record, hrel.trans_eq]
        chall_eq := by simp [SM.GameState.record, hrel.chall_eq]
        corrs_eq := by simp [SM.GameState.record, hrel.corrs_eq]
        leaks_sh_to_unsh := by simpa [SM.GameState.record] using hrel.leaks_sh_to_unsh
        leaks_unsh_to_sh := by simpa [SM.GameState.record] using hrel.leaks_unsh_to_sh
        leak_corr_unsh := hrel.leak_corr_unsh
        tL_sh_none := by simpa [SM.GameState.record] using hrel.tL_sh_none
        tL_sh_some := by simpa [SM.GameState.record] using hrel.tL_sh_some
        leaks_sh_ge_l := by simpa [SM.GameState.record] using hrel.leaks_sh_ge_l }

theorem ShiftedLeakRel.accept_step {St Msg C : Type} [DecidableEq C] (l : ℕ)
    (Q : Party) (st' : St) (pos : SM.Pos)
    {s_unsh s_sh : SM.GameState St Msg C} (hrel : ShiftedLeakRel l s_unsh s_sh) :
    ShiftedLeakRel l (s_unsh.accept Q st' pos) (s_sh.accept Q st' pos) where
  st_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.st_eq]
  b_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.b_eq]
  epoch_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.epoch_eq]
  idx_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.idx_eq]
  maxAcc_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.maxAcc_eq]
  trans_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.trans_eq]
  chall_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.chall_eq]
  corrs_eq := by simp [SM.GameState.accept, SM.GameState.delete, hrel.corrs_eq]
  leaks_sh_to_unsh := by
    simpa [SM.GameState.accept, SM.GameState.delete] using hrel.leaks_sh_to_unsh
  leaks_unsh_to_sh := by
    simpa [SM.GameState.accept, SM.GameState.delete] using hrel.leaks_unsh_to_sh
  leak_corr_unsh := hrel.leak_corr_unsh
  tL_sh_none := by simpa [SM.GameState.accept, SM.GameState.delete] using hrel.tL_sh_none
  tL_sh_some := by simpa [SM.GameState.accept, SM.GameState.delete] using hrel.tL_sh_some
  leaks_sh_ge_l := by simpa [SM.GameState.accept, SM.GameState.delete] using hrel.leaks_sh_ge_l

theorem ShiftedLeakRel.corr_step {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (l : ℕ) (P : Party)
    {s_unsh s_sh : SM.GameState St Msg C} (hrel : ShiftedLeakRel l s_unsh s_sh)
    (hwf_unsh : SM.Thm1L17.WFState (2 + 1) s_unsh)
    (htL_unsh : ∀ l₀, s_unsh.tL = some l₀ → l₀ ≤ max (s_unsh.epoch .A) (s_unsh.epoch .B))
    (htL_sh : ∀ l₀, s_sh.tL = some l₀ → l₀ ≤ max (s_sh.epoch .A) (s_sh.epoch .B)) :
    ShiftedLeakRel l (s_unsh.afterCorr P) (DeliverForge.afterCorrShifted l s_sh P) := by
  have hmax_unsh : SM.maxOpt s_unsh.tL (max (s_unsh.epoch .A) (s_unsh.epoch .B)) =
      max (s_unsh.epoch .A) (s_unsh.epoch .B) := by
    cases htl : s_unsh.tL with
    | none => rfl
    | some l₀ => exact Nat.max_eq_right (htL_unsh l₀ htl)
  have hmax_sh : SM.maxOpt s_sh.tL (max (s_unsh.epoch .A) (s_unsh.epoch .B)) =
      max (s_unsh.epoch .A) (s_unsh.epoch .B) := by
    cases htl : s_sh.tL with
    | none => rfl
    | some l₀ =>
      have := htL_sh l₀ htl
      rw [hrel.epoch_eq] at this
      exact Nat.max_eq_right this
  have hsh_sub : max (s_unsh.epoch .A) (s_unsh.epoch .B) = l →
      SM.maxOpt s_sh.tL (l - 1) = l - 1 ∨ SM.maxOpt s_sh.tL (l - 1) = l := by
    intro hmax_eq
    cases htl : s_sh.tL with
    | none => exact Or.inl rfl
    | some l₀ =>
      have hl₀ := htL_sh l₀ htl
      rw [hrel.epoch_eq, hmax_eq] at hl₀
      simp only [SM.maxOpt]
      omega
  refine
    { st_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak, hrel.st_eq]
      b_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak, hrel.b_eq]
      epoch_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak,
          hrel.epoch_eq]
      idx_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak, hrel.idx_eq]
      maxAcc_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak,
          hrel.maxAcc_eq]
      trans_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak,
          hrel.trans_eq]
      chall_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak,
          hrel.chall_eq]
      corrs_eq := by
        simp [SM.GameState.afterCorr, DeliverForge.afterCorrShifted, SM.GameState.leak,
          hrel.corrs_eq, hrel.epoch_eq]
      leaks_sh_to_unsh := ?_
      leaks_unsh_to_sh := ?_
      leak_corr_unsh := DeliverForge.LeakCorrInv.afterCorr_of_wfState hwf_unsh hrel.leak_corr_unsh P
      tL_sh_none := by
        intro h
        unfold DeliverForge.afterCorrShifted SM.GameState.leak at h
        nomatch h
      tL_sh_some := ?_
      leaks_sh_ge_l := ?_ }
  · intro e_sh he_sh
    unfold DeliverForge.afterCorrShifted SM.GameState.leak at he_sh
    dsimp only at he_sh
    rw [hrel.epoch_eq] at he_sh
    unfold SM.GameState.afterCorr SM.GameState.leak
    dsimp only
    rw [hmax_unsh]
    simp only [List.mem_cons] at he_sh ⊢
    rcases he_sh with rfl | he_old
    · refine ⟨max (s_unsh.epoch .A) (s_unsh.epoch .B), Or.inl rfl, ?_⟩
      split_ifs with hcond
      · rcases hcond with ⟨hmax_eq, hep⟩
        rcases hsh_sub hmax_eq with h1 | h2 <;> omega
      · rw [hmax_sh]
        omega
    · rcases hrel.leaks_sh_to_unsh e_sh he_old with ⟨m, hm, h1, h2, h3⟩
      exact ⟨m, Or.inr hm, h1, h2, h3⟩
  · intro m hm
    unfold SM.GameState.afterCorr SM.GameState.leak at hm
    dsimp only at hm
    rw [hmax_unsh] at hm
    unfold DeliverForge.afterCorrShifted SM.GameState.leak
    dsimp only
    rw [hrel.epoch_eq]
    simp only [List.mem_cons] at hm ⊢
    rcases hm with rfl | hm_old
    · constructor
      · intro hne
        left
        split_ifs with hcond
        · exact False.elim (hne hcond.1)
        · exact hmax_sh.symm
      · intro heq
        split_ifs with hcond
        · rcases hsh_sub heq with h1 | h2
          · exact Or.inr (Or.inl h1.symm)
          · exact Or.inl (Or.inl h2.symm)
        · left
          left
          rw [hmax_sh, heq]
    · rcases hrel.leaks_unsh_to_sh m hm_old with ⟨h1, h2⟩
      refine ⟨fun hne => Or.inr (h1 hne), fun heq => ?_⟩
      rcases h2 heq with hl | hlm1
      · exact Or.inl (Or.inr hl)
      · exact Or.inr (Or.inr hlm1)
  · intro k hk
    unfold DeliverForge.afterCorrShifted SM.GameState.leak at hk ⊢
    dsimp only at hk ⊢
    injection hk with hk
    subst hk
    refine ⟨List.mem_cons_self, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx_old
    · exact le_refl _
    · cases htl : s_sh.tL with
      | none =>
        rw [hrel.tL_sh_none htl] at hx_old
        nomatch hx_old
      | some k₀ =>
        have hxk₀ := (hrel.tL_sh_some k₀ htl).2 x hx_old
        simp only [SM.maxOpt]
        omega
  · intro hl1 x hx hx_ge
    unfold DeliverForge.afterCorrShifted SM.GameState.leak at hx
    dsimp only at hx
    rw [hrel.epoch_eq] at hx
    unfold SM.GameState.afterCorr SM.GameState.leak
    dsimp only
    rcases List.mem_cons.mp hx with rfl | hx_old
    · split_ifs at hx_ge with hcond
      · cases htl : s_sh.tL with
        | none =>
          simp only [htl, SM.maxOpt] at hx_ge
          omega
        | some k₀ =>
          simp only [htl, SM.maxOpt] at hx_ge
          have hk₀_mem := (hrel.tL_sh_some k₀ htl).1
          rcases hrel.leaks_sh_ge_l hl1 k₀ hk₀_mem (by omega) with ⟨P₀, e₀, hmem₀, hle₀⟩
          exact ⟨P₀, e₀, List.mem_cons_of_mem _ hmem₀, hle₀⟩
      · rw [hmax_sh] at hx_ge
        have hstep : max (s_unsh.epoch .A) (s_unsh.epoch .B) ≤ s_unsh.epoch P + 1 :=
          max_le (hwf_unsh.epoch_le_any_add_one .A P) (hwf_unsh.epoch_le_any_add_one .B P)
        exact ⟨P, s_unsh.epoch P, List.mem_cons_self, by omega⟩
    · rcases hrel.leaks_sh_ge_l hl1 x hx_old hx_ge with ⟨P₀, e₀, hmem₀, hle₀⟩
      exact ⟨P₀, e₀, List.mem_cons_of_mem _ hmem₀, hle₀⟩

theorem s_win_of_cellWinPred {St Msg C : Type} {tL : Option ℕ} {t : ℕ}
    {s : SM.GameState St Msg C} (h : cellWinPred tL t s = true) : s.win = true := by
  unfold cellWinPred at h
  split_ifs at h <;> simp only [Bool.and_eq_true] at h <;> exact h.1

theorem PPrimePaperRel.of_mirror {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} (m₁' : Mirror Msg C)
    {g : SM.GameState St Msg C} (h : PPrimePaperRel s_df m' g) :
    PPrimePaperRel s_df m₁' g :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15⟩

theorem PPrimePaperRelShifted.of_mirror {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} (m₁' : Mirror Msg C)
    {g : SM.GameState St Msg C} (h : PPrimePaperRelShifted s_df m' g) :
    PPrimePaperRelShifted s_df m₁' g :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14⟩

theorem cellWinPred_win_of_authOK_and_k4Free {St Msg C : Type}
    (tL : Option ℕ) (t : ℕ) (s : SM.GameState St Msg C)
    (hauth : SM.authLosingConditionsAvoided (cellDelta tL t) tL t s = true)
    (hk4 : (Party.senderOf t, t) ∉ s.corrs) :
    cellWinPred tL t { s with win := true } = true := by
  unfold cellWinPred
  split_ifs with hB1
  · rcases hB1 with ⟨ht2, rfl⟩
    have hdelta : cellDelta (some (t - 2)) t = 2 := by
      unfold cellDelta
      simp [ht2]
    rw [hdelta] at hauth
    simp only [Bool.true_and, authOKDir2, Bool.and_eq_true]
    refine ⟨hauth, ?_⟩
    rw [Bool.not_eq_true', List.any_eq_false]
    rintro ⟨p1, p2⟩ hpe
    simp only [Bool.and_eq_true, beq_iff_eq]
    rintro ⟨rfl, rfl⟩
    exact hk4 hpe
  · have hdelta : cellDelta tL t = 2 + 1 := by
      unfold cellDelta
      simp [hB1]
    rw [hdelta] at hauth
    simp only [Bool.true_and]
    exact hauth

theorem ShiftedLeakRel.tL_sh_eq_some_of_mem_and_le {St Msg C : Type} {l : ℕ}
    {s_unsh s_sh : SM.GameState St Msg C} (hrel : ShiftedLeakRel l s_unsh s_sh)
    {m : ℕ} (hm : m ∈ s_sh.leaks) (hle : ∀ x ∈ s_sh.leaks, x ≤ m) :
    s_sh.tL = some m := by
  cases htl : s_sh.tL with
  | none =>
    rw [hrel.tL_sh_none htl] at hm
    nomatch hm
  | some k =>
    rcases hrel.tL_sh_some k htl with ⟨hk_mem, hk_le⟩
    exact congrArg some (Nat.le_antisymm (hk_le m hm) (hle k hk_mem)).symm

theorem exists_cell_healed_of_corrs_bound {St Msg C : Type}
    {t' : ℕ} {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hcorrs : ∀ P e, (P, e) ∈ (s_cell t' none).corrs → e + 2 ≤ t')
    (hleak_corr : DeliverForge.LeakCorrInv (s_cell t' none))
    (hcell : ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t',
      ShiftedLeakRel (cellShift tL t') (s_cell t' none) (s_cell t' tL)) :
    ∃ tLStar ∈ SM.admissibleLastLeakGuesses 2 t',
      (s_cell t' tLStar).tL = tLStar ∧
      SM.healedBy tLStar (cellDelta tLStar t') t' = true := by
  cases htl : (s_cell t' none).tL with
  | none =>
    exact ⟨none, Finset.mem_insert_self none _, htl, rfl⟩
  | some m =>
    rcases hleak_corr.2.1 m htl with ⟨hm_mem, hm_max⟩
    rcases hleak_corr.2.2 m hm_mem with ⟨R, e, hRe, he_le, hm_le, _⟩
    have he_bound : e + 2 ≤ t' := hcorrs R e hRe
    by_cases hm3 : m + 3 ≤ t'
    · have htL_mem : some m ∈ SM.admissibleLastLeakGuesses 2 t' :=
        Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩)
      have hleak := hcell (some m) htL_mem
      have hdelta : cellDelta (some m) t' = 2 + 1 := by
        unfold cellDelta
        split_ifs with hB1
        · rcases hB1 with ⟨_, h⟩
          injection h
          omega
        · rfl
      have hm_sh : m ∈ (s_cell t' (some m)).leaks := by
        rcases hleak.leaks_unsh_to_sh m hm_mem with ⟨h1, h2⟩
        by_cases hml : m = cellShift (some m) t'
        · have hl0 : cellShift (some m) t' = 0 := by
            unfold cellShift at hml ⊢
            split_ifs at hml ⊢ with hB1 hB2
            · rcases hB1 with ⟨_, h⟩
              injection h
              omega
            · rcases hB2 with ⟨_, h⟩
              injection h
              omega
            · rfl
          rcases h2 hml with h_in | h_in
          · rwa [← hml] at h_in
          · rw [hl0] at h_in hml
            simpa [hml] using h_in
        · exact h1 hml
      have hmax_sh : ∀ x ∈ (s_cell t' (some m)).leaks, x ≤ m := by
        intro x hx
        rcases hleak.leaks_sh_to_unsh x hx with ⟨u, hu, hxu, _⟩
        exact le_trans hxu (hm_max u hu)
      refine ⟨some m, htL_mem, hleak.tL_sh_eq_some_of_mem_and_le hm_sh hmax_sh, ?_⟩
      rw [hdelta]
      simp only [SM.healedBy, decide_eq_true_eq]
      omega
    · have ht2 : 2 ≤ t' := by omega
      have htL_mem : some (t' - 2) ∈ SM.admissibleLastLeakGuesses 2 t' :=
        Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t' - 2, Finset.mem_range.mpr (by omega), rfl⟩)
      have hleak := hcell (some (t' - 2)) htL_mem
      have hdelta : cellDelta (some (t' - 2)) t' = 2 := by
        unfold cellDelta
        simp [ht2]
      have hshift : cellShift (some (t' - 2)) t' = t' - 1 := by
        unfold cellShift
        simp [ht2]
      rw [hshift] at hleak
      have hmax_sh : ∀ x ∈ (s_cell t' (some (t' - 2))).leaks, x ≤ t' - 2 := by
        intro x hx
        by_contra hgt
        rcases hleak.leaks_sh_ge_l (by omega) x hx (by omega) with ⟨P₀, e₀, hmem₀, hle₀⟩
        have := hcorrs P₀ e₀ hmem₀
        omega
      have hm_sh : t' - 2 ∈ (s_cell t' (some (t' - 2))).leaks := by
        rcases hleak.leaks_unsh_to_sh m hm_mem with ⟨h1, h2⟩
        by_cases hml : m = t' - 1
        · rcases h2 hml with h_in | h_in
          · have := hmax_sh (t' - 1) h_in
            omega
          · simpa [Nat.sub_sub] using h_in
        · have hmeq : m = t' - 2 := by omega
          have hm_in := h1 hml
          rwa [hmeq] at hm_in
      refine ⟨some (t' - 2), htL_mem, hleak.tL_sh_eq_some_of_mem_and_le hm_sh hmax_sh, ?_⟩
      rw [hdelta]
      simp only [SM.healedBy, decide_eq_true_eq]
      omega

end CryptoVerification.LibsignalSession.HeadlineV1

end
