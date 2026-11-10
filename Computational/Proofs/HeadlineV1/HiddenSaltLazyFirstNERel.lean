/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
public import Computational.Proofs.HeadlineV1.DeliverForgeShifted
import ProofLib.SepLogic.WP.StateNorm

/-!
# Pre-Divergence Relations for the Paper `DeliverForge` Engine

Defines the pre-divergence relations `PPrimePaperRel` and `PPrimePaperRelShifted` between the
`DeliverForge` paper engine, its mirror, and `firstNESimImpl`, together with their step lemmas and
`CompUnhealed` invariants.
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
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

/-! ## Pre-divergence relations -/

/-- Shifted pre-divergence relation for `B1` and `B2` cells under `DeliverForge.afterCorrShifted`. -/
structure PPrimePaperRelShifted {St Msg C : Type}
    (s_df : SM.GameState St Msg C) (_m' : Mirror Msg C) (g : SM.GameState St Msg C) : Prop where
  win_df_false : s_df.win = false
  win_mir_false : g.win = false
  st_eq : s_df.st = g.st
  b_eq : s_df.b = g.b
  epoch_eq : s_df.epoch = g.epoch
  idx_eq : s_df.idx = g.idx
  maxAcc_eq : s_df.maxAcc = g.maxAcc
  trans_eq : s_df.trans = g.trans
  chall_df_nil : s_df.chall = []
  corrs_eq : s_df.corrs = g.corrs
  tL_df_le_max : ∀ l_df, s_df.tL = some l_df → l_df ≤ max (s_df.epoch .A) (s_df.epoch .B)
  tL_g_le_max : ∀ l_g, g.tL = some l_g → l_g ≤ max (g.epoch .A) (g.epoch .B)
  tL_le : ∀ l_df, s_df.tL = some l_df → ∃ l_g, g.tL = some l_g ∧ l_df ≤ l_g
  comp_sub : ∀ pos ∈ s_df.comp, pos ∈ g.comp

/-- Pre-divergence relation `PPrimePaperRel` between `s_df` (`DeliverForge.fullImplBaseDFPaper`),
`m'` (`DeliverForge.challSimDF'Paper (2 + 1)`), and `g` (`firstNESimImpl`). -/
structure PPrimePaperRel {St Msg C : Type}
    (s_df : SM.GameState St Msg C) (_m' : Mirror Msg C) (g : SM.GameState St Msg C) : Prop where
  win_df_false : s_df.win = false
  win_mir_false : g.win = false
  st_eq : s_df.st = g.st
  b_eq : s_df.b = g.b
  epoch_eq : s_df.epoch = g.epoch
  idx_eq : s_df.idx = g.idx
  maxAcc_eq : s_df.maxAcc = g.maxAcc
  trans_eq : s_df.trans = g.trans
  chall_df_nil : s_df.chall = []
  corrs_eq : s_df.corrs = g.corrs
  tL_df_le_max : ∀ l_df, s_df.tL = some l_df → l_df ≤ max (s_df.epoch .A) (s_df.epoch .B)
  tL_g_le_max : ∀ l_g, g.tL = some l_g → l_g ≤ max (g.epoch .A) (g.epoch .B)
  leaks_sub : ∀ e ∈ s_df.leaks, e ∈ g.leaks
  tL_le : ∀ l_df, s_df.tL = some l_df → ∃ l_g, g.tL = some l_g ∧ l_df ≤ l_g
  comp_sub : ∀ pos ∈ s_df.comp, pos ∈ g.comp

theorem PPrimePaperRel.toShifted {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) : PPrimePaperRelShifted s_df m' g :=
  ⟨hrel.win_df_false, hrel.win_mir_false, hrel.st_eq, hrel.b_eq, hrel.epoch_eq, hrel.idx_eq,
    hrel.maxAcc_eq, hrel.trans_eq, hrel.chall_df_nil, hrel.corrs_eq, hrel.tL_df_le_max,
    hrel.tL_g_le_max, hrel.tL_le, hrel.comp_sub⟩

theorem PPrimePaperRelShifted.inTransit_eq {St Msg C : Type} [DecidableEq C]
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) (P : Party) (c : C) :
    s_df.inTransit P c = g.inTransit P c := by unfold SM.GameState.inTransit; rw [hrel.trans_eq]

theorem PPrimePaperRel.inTransit_eq {St Msg C : Type} [DecidableEq C]
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) (P : Party) (c : C) :
    s_df.inTransit P c = g.inTransit P c := hrel.toShifted.inTransit_eq P c

theorem PPrimePaperRelShifted.comp_contains_false_of_mir {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) {pos : SM.Pos} (hnot : g.comp.contains pos = false) :
    s_df.comp.contains pos = false := by
  rw [List.contains_eq_mem] at hnot ⊢; simp only [decide_eq_false_iff_not] at hnot ⊢
  exact fun h => hnot (hrel.comp_sub pos h)

theorem PPrimePaperRelShifted.corrAllowedPaper_df {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) (P : Party) :
    s_df.corrAllowedPaper P = true := by simp [SM.GameState.corrAllowedPaper, hrel.chall_df_nil]

theorem PPrimePaperRel.corrAllowedPaper_df {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) (P : Party) :
    s_df.corrAllowedPaper P = true := hrel.toShifted.corrAllowedPaper_df P

theorem corrAllowedPaper_of_corrAllowed {St Msg C : Type}
    {g : SM.GameState St Msg C} {m' : Mirror Msg C} {P : Party}
    (hallow : g.corrAllowed P = true) :
    g.corrAllowedPaper P = true ∧
      ((∀ pos ∈ m'.chall, pos ∈ g.chall) → m'.corrAllowedPaper P = true) := by
  unfold SM.GameState.corrAllowed at hallow; simp only [Bool.and_eq_true] at hallow
  refine ⟨hallow.1, fun hsub => ?_⟩; unfold SM.GameState.corrAllowedPaper
  have h1 : g.chall.any (fun pos => pos.sender == P.other) = false := by simpa using hallow.1
  rw [List.any_eq_false] at h1; simp only [Bool.not_eq_true', List.any_eq_false]
  exact fun pos hpos => h1 pos (hsub pos hpos)

theorem PPrimePaperRelShifted.healedBy_df_of_healedBy_mir {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) {Δ e : ℕ} (hΔ : Δ ≤ 2 + 1)
    (hheal : SM.healedBy g.tL (2 + 1) e = true) : SM.healedBy s_df.tL Δ e = true := by
  cases htl : s_df.tL with
  | none => rfl
  | some l_df =>
    obtain ⟨l_g, hlg, hle⟩ := hrel.tL_le l_df htl
    rw [hlg] at hheal; simp only [SM.healedBy, decide_eq_true_eq] at hheal ⊢; omega

theorem PPrimePaperRelShifted.safeCh_df_of_safeCh_mir {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) {P : Party}
    (hsafe : g.safeCh (2 + 1) P = true) : s_df.safeCh Δ P = true := by
  unfold SM.GameState.safeCh at hsafe ⊢; rw [hrel.epoch_eq]
  exact hrel.healedBy_df_of_healedBy_mir hΔ hsafe

theorem PPrimePaperRel.safeCh_df_of_safeCh_mir {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) {P : Party}
    (hsafe : g.safeCh (2 + 1) P = true) : s_df.safeCh Δ P = true :=
  hrel.toShifted.safeCh_df_of_safeCh_mir hΔ hsafe

theorem PPrimePaperRelShifted.safeCh_mir_false_of_safeCh_df_false {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) {P : Party}
    (hnsafe : s_df.safeCh Δ P = false) : g.safeCh (2 + 1) P = false := by
  by_contra h; have htrue : g.safeCh (2 + 1) P = true := Bool.eq_true_of_not_eq_false h
  have hdf := hrel.safeCh_df_of_safeCh_mir hΔ htrue; rw [hdf] at hnsafe; cases hnsafe

theorem PPrimePaperRelShifted.safeInj_df_of_safeInj_mir {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1)
    (hsafe : g.safeInj (2 + 1) = true) : s_df.safeInj Δ = true := by
  unfold SM.GameState.safeInj at hsafe ⊢; rw [hrel.epoch_eq]
  exact hrel.healedBy_df_of_healedBy_mir hΔ hsafe

theorem PPrimePaperRel.safeInj_df_of_safeInj_mir {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1)
    (hsafe : g.safeInj (2 + 1) = true) : s_df.safeInj Δ = true :=
  hrel.toShifted.safeInj_df_of_safeInj_mir hΔ hsafe

theorem PPrimePaperRelShifted.trivial_df_false_of_trivial_mir_false {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) {pos : SM.Pos}
    (htriv_g : g.trivial (2 + 1) pos = false) : s_df.trivial Δ pos = false := by
  unfold SM.GameState.trivial at htriv_g ⊢
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at htriv_g ⊢
  refine ⟨hrel.comp_contains_false_of_mir htriv_g.1, ?_⟩; rw [hrel.trans_eq]
  exact htriv_g.2.imp id (hrel.healedBy_df_of_healedBy_mir hΔ)

theorem PPrimePaperRel.trivial_df_false_of_trivial_mir_false {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) {pos : SM.Pos}
    (htriv_g : g.trivial (2 + 1) pos = false) : s_df.trivial Δ pos = false :=
  hrel.toShifted.trivial_df_false_of_trivial_mir_false hΔ htriv_g

/-! ## Step lemmas -/

theorem PPrimePaperRelShifted.toPaperRel {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) (hleaks : ∀ e ∈ s_df.leaks, e ∈ g.leaks) :
    PPrimePaperRel s_df m' g :=
  ⟨hrel.win_df_false, hrel.win_mir_false, hrel.st_eq, hrel.b_eq, hrel.epoch_eq, hrel.idx_eq,
    hrel.maxAcc_eq, hrel.trans_eq, hrel.chall_df_nil, hrel.corrs_eq, hrel.tL_df_le_max,
    hrel.tL_g_le_max, hleaks, hrel.tL_le, hrel.comp_sub⟩

private theorem tL_le_of_mir_leak_shifted {St Msg C : Type}
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) (e : ℕ) :
    ∀ l_df, s_df.tL = some l_df → ∃ l_g, (g.leak e).tL = some l_g ∧ l_df ≤ l_g := by
  intro l_df hldf; obtain ⟨l_g, hlg, hle⟩ := hrel.tL_le l_df hldf
  simp only [SM.GameState.leak, SM.maxOpt, hlg, Option.some.injEq]
  exact ⟨max l_g e, rfl, hle.trans (Nat.le_max_left l_g e)⟩

private theorem max_epoch_le_update_add_one {St Msg C : Type} (s : SM.GameState St Msg C)
    (P : Party) :
    max (s.epoch .A) (s.epoch .B) ≤
      max (Function.update s.epoch P (s.epoch P + 1) .A)
          (Function.update s.epoch P (s.epoch P + 1) .B) := by cases P <;> simp <;> omega

theorem PPrimePaperRelShifted.epMgmt_step {St Msg C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {s_df : SM.GameState St Msg C} {m' m₁' : Mirror Msg C} {g g₁ : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁) :
    ∃ s_df₁, s_df.epMgmt Δ (qep + 1) P false = some s_df₁ ∧ s_df₁.leaks = s_df.leaks ∧
      (∀ e ∈ g.leaks, e ∈ g₁.leaks) ∧ PPrimePaperRelShifted s_df₁ m₁' g₁ := by
  unfold SM.GameState.epMgmt at hep_g ⊢; rw [hrel.epoch_eq]
  by_cases hsends : P.sendsIn (g.epoch P + 1) = true
  · simp only [hsends, ↓reduceIte] at hep_g ⊢
    by_cases hq : qep + 1 < g.epoch P + 1
    · simp [hq] at hep_g
    · simp only [hq, ↓reduceIte, Bool.false_and, Bool.false_eq_true, Option.some.injEq] at hep_g ⊢
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · subst hep_g
        by_cases hcond : (bad && !(g.safeCh (2 + 1) P)) = true
        · simp only [hcond, ↓reduceIte, SM.GameState.leak]
          exact fun e he => List.mem_cons_of_mem _ he
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact fun _ h => h
      · subst hep_g
        have hdf_max : ∀ l_df, s_df.tL = some l_df →
            l_df ≤ max (Function.update s_df.epoch P (s_df.epoch P + 1) .A)
                       (Function.update s_df.epoch P (s_df.epoch P + 1) .B) :=
          fun l_df hldf => (hrel.tL_df_le_max l_df hldf).trans (max_epoch_le_update_add_one s_df P)
        by_cases hcond : (bad && !(g.safeCh (2 + 1) P)) = true
        · simp only [hcond, ↓reduceIte]
          refine ⟨hrel.win_df_false, hrel.win_mir_false, hrel.st_eq, hrel.b_eq,
            by simp [SM.GameState.leak, hrel.epoch_eq], by simp [SM.GameState.leak, hrel.idx_eq],
            hrel.maxAcc_eq, hrel.trans_eq, hrel.chall_df_nil, hrel.corrs_eq, hdf_max, ?_,
            tL_le_of_mir_leak_shifted hrel (g.epoch P + 1), hrel.comp_sub⟩
          intro l_g hlg; simp only [SM.GameState.leak, Option.some.injEq] at hlg; subst hlg
          have hP_le : g.epoch P + 1 ≤
              max (Function.update g.epoch P (g.epoch P + 1) .A)
                  (Function.update g.epoch P (g.epoch P + 1) .B) := by cases P <;> simp
          cases htl : g.tL with
          | none => exact hP_le
          | some l₀ =>
            simp only [SM.maxOpt]
            exact max_le ((hrel.tL_g_le_max l₀ htl).trans (max_epoch_le_update_add_one g P)) hP_le
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hrel.win_df_false, hrel.win_mir_false, hrel.st_eq, hrel.b_eq,
            by simp [hrel.epoch_eq], by simp [hrel.idx_eq], hrel.maxAcc_eq, hrel.trans_eq,
            hrel.chall_df_nil, hrel.corrs_eq, hdf_max,
            fun l_g hlg => (hrel.tL_g_le_max l_g hlg).trans (max_epoch_le_update_add_one g P),
            hrel.tL_le, hrel.comp_sub⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hep_g ⊢
    by_cases hq : qep + 1 < g.epoch P
    · simp [hq] at hep_g
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep_g ⊢; subst hep_g
      exact ⟨s_df, rfl, rfl, fun _ h => h, ⟨hrel.win_df_false, hrel.win_mir_false, hrel.st_eq,
        hrel.b_eq, hrel.epoch_eq, hrel.idx_eq, hrel.maxAcc_eq, hrel.trans_eq, hrel.chall_df_nil,
        hrel.corrs_eq, hrel.tL_df_le_max, hrel.tL_g_le_max, hrel.tL_le, hrel.comp_sub⟩⟩

theorem PPrimePaperRel.epMgmt_step {St Msg C : Type} {Δ qep : ℕ} {P : Party} {bad : Bool}
    {s_df : SM.GameState St Msg C} {m' m₁' : Mirror Msg C} {g g₁ : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁) :
    ∃ s_df₁, s_df.epMgmt Δ (qep + 1) P false = some s_df₁ ∧ PPrimePaperRel s_df₁ m₁' g₁ := by
  obtain ⟨s_df₁, hep_df, hldf, hlg, hrel₁⟩ := hrel.toShifted.epMgmt_step (m₁' := m₁') hep_g
  exact ⟨s_df₁, hep_df, hrel₁.toPaperRel (fun e he => hlg e (hrel.leaks_sub e (hldf ▸ he)))⟩

theorem PPrimePaperRelShifted.record_step {St Msg C : Type}
    {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) (P : Party) (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    {s_df₁ : SM.GameState St Msg C} {m' m₁' : Mirror Msg C} {g₁ : SM.GameState St Msg C}
    (hrel₁ : PPrimePaperRelShifted s_df₁ m' g₁) :
    PPrimePaperRelShifted (s_df₁.record Δ P st' rec_r false) m₁'
      (g₁.record (2 + 1) P st' rec_r isChall) := by
  refine ⟨hrel₁.win_df_false, hrel₁.win_mir_false,
    by simp [SM.GameState.record, hrel₁.st_eq], hrel₁.b_eq, hrel₁.epoch_eq,
    by simp [SM.GameState.record, hrel₁.idx_eq], hrel₁.maxAcc_eq,
    by simp [SM.GameState.record, hrel₁.trans_eq],
    by simp [SM.GameState.record, hrel₁.chall_df_nil], hrel₁.corrs_eq,
    hrel₁.tL_df_le_max, hrel₁.tL_g_le_max, hrel₁.tL_le, ?_⟩
  intro pos hpos; unfold SM.GameState.record at hpos ⊢; dsimp only at hpos ⊢
  by_cases hsdf : s_df₁.safeCh Δ P = true
  · simp only [hsdf, ↓reduceIte] at hpos; have hmem : pos ∈ g₁.comp := hrel₁.comp_sub pos hpos
    split <;> [exact hmem; exact List.mem_cons_of_mem _ hmem]
  · have hsdfF : s_df₁.safeCh Δ P = false := Bool.eq_false_iff.mpr hsdf
    have hsgF := hrel₁.safeCh_mir_false_of_safeCh_df_false hΔ hsdfF
    simp only [hsdfF, hsgF, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
    rcases List.mem_cons.mp hpos with rfl | hpos
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hrel₁.comp_sub pos hpos)

theorem PPrimePaperRel.record_step {St Msg C : Type}
    {Δ : ℕ} (hΔ : Δ ≤ 2 + 1) (P : Party) (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    {s_df₁ : SM.GameState St Msg C} {m' m₁' : Mirror Msg C} {g₁ : SM.GameState St Msg C}
    (hrel₁ : PPrimePaperRel s_df₁ m' g₁) :
    PPrimePaperRel (s_df₁.record Δ P st' rec_r false) m₁'
      (g₁.record (2 + 1) P st' rec_r isChall) :=
  (hrel₁.toShifted.record_step hΔ P st' rec_r isChall).toPaperRel hrel₁.leaks_sub

private theorem max_epoch_le_accept {St Msg C : Type}
    (s : SM.GameState St Msg C) (Q : Party) (st' : St) (pos : SM.Pos) :
    max (s.epoch .A) (s.epoch .B) ≤
      max ((s.accept Q st' pos).epoch .A) ((s.accept Q st' pos).epoch .B) := by
  cases Q <;> simp [SM.GameState.accept, SM.GameState.delete] <;> omega

theorem pprimePaperRelShifted_inject_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (Δ : ℕ) (Q : Party) (st' : St) (pos : SM.Pos)
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) :
    PPrimePaperRelShifted (s_df.accept Q st' pos) m' (g.accept Q st' pos) := by
  let _ := Δ
  refine ⟨hrel.win_df_false, hrel.win_mir_false,
    by simp [SM.GameState.accept, SM.GameState.delete, hrel.st_eq], hrel.b_eq,
    by simp [SM.GameState.accept, SM.GameState.delete, hrel.epoch_eq], hrel.idx_eq,
    by simp [SM.GameState.accept, SM.GameState.delete, hrel.maxAcc_eq],
    by simp [SM.GameState.accept, SM.GameState.delete, hrel.trans_eq],
    by simp [SM.GameState.accept, SM.GameState.delete, hrel.chall_df_nil], hrel.corrs_eq,
    fun l_df hldf => (hrel.tL_df_le_max l_df hldf).trans (max_epoch_le_accept s_df Q st' pos),
    fun l_g hlg => (hrel.tL_g_le_max l_g hlg).trans (max_epoch_le_accept g Q st' pos),
    hrel.tL_le, ?_⟩
  intro pos' hpos'
  simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hpos' ⊢
  exact ⟨hrel.comp_sub pos' hpos'.1, hpos'.2⟩

theorem pprimePaperRel_inject_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (Δ : ℕ) (Q : Party) (st' : St) (pos : SM.Pos)
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRel s_df m' g) :
    PPrimePaperRel (s_df.accept Q st' pos) m' (g.accept Q st' pos) :=
  (pprimePaperRelShifted_inject_step (Key := Key) (Coins := Coins) Δ Q st' pos
    hrel.toShifted).toPaperRel hrel.leaks_sub

private theorem maxOpt_eq_right_of_le_max {tL : Option ℕ} {l₀ : ℕ}
    (h : ∀ l, tL = some l → l ≤ l₀) : SM.maxOpt tL l₀ = l₀ := by
  cases tL with
  | none => rfl
  | some l => exact Nat.max_eq_right (h l rfl)

theorem PPrimePaperRelShifted.afterCorrShifted_step {St Msg C : Type} (l : ℕ) (P : Party)
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) :
    PPrimePaperRelShifted (DeliverForge.afterCorrShifted l s_df P)
      (m'.afterCorr P) (g.afterCorr P) := by
  let e_leak :=
    if max (s_df.epoch .A) (s_df.epoch .B) = l ∧ s_df.epoch P + 1 ≤ l then l - 1
    else max (s_df.epoch .A) (s_df.epoch .B)
  have he_le : e_leak ≤ max (s_df.epoch .A) (s_df.epoch .B) := by
    dsimp only [e_leak]; split_ifs <;> omega
  have hmax_df : SM.maxOpt s_df.tL e_leak ≤ max (s_df.epoch .A) (s_df.epoch .B) := by
    cases htl : s_df.tL with
    | none => exact he_le
    | some l₀ => exact max_le (hrel.tL_df_le_max l₀ htl) he_le
  have hmax_g : SM.maxOpt g.tL (max (g.epoch .A) (g.epoch .B)) =
      max (g.epoch .A) (g.epoch .B) := maxOpt_eq_right_of_le_max hrel.tL_g_le_max
  refine ⟨hrel.win_df_false, hrel.win_mir_false, hrel.st_eq, hrel.b_eq, hrel.epoch_eq,
    hrel.idx_eq, hrel.maxAcc_eq, hrel.trans_eq, hrel.chall_df_nil,
    by simp [DeliverForge.afterCorrShifted, SM.GameState.afterCorr, SM.GameState.leak,
         hrel.epoch_eq, hrel.corrs_eq], ?_, ?_, ?_, ?_⟩
  · intro l_df hldf
    simp only [DeliverForge.afterCorrShifted, SM.GameState.leak, Option.some.injEq] at hldf ⊢
    exact hldf ▸ hmax_df
  · intro l_g hlg
    simp only [SM.GameState.afterCorr, SM.GameState.leak, hmax_g, Option.some.injEq] at hlg ⊢
    rw [← hlg]
  · intro l_df hldf
    simp only [DeliverForge.afterCorrShifted, SM.GameState.afterCorr, SM.GameState.leak,
      hmax_g, Option.some.injEq] at hldf ⊢
    exact ⟨_, rfl, by rw [← hldf, ← hrel.epoch_eq]; exact hmax_df⟩
  · intro pos hpos
    simp only [DeliverForge.afterCorrShifted, SM.GameState.afterCorr, SM.GameState.leak,
      List.mem_append, List.mem_map, List.mem_filter, hrel.trans_eq] at hpos ⊢
    exact hpos.imp id (hrel.comp_sub pos)

theorem afterCorrShifted_zero_eq_afterCorr {St Msg C : Type}
    (s : SM.GameState St Msg C) (P : Party) :
    DeliverForge.afterCorrShifted 0 s P = s.afterCorr P := by
  unfold DeliverForge.afterCorrShifted SM.GameState.afterCorr; simp

theorem PPrimePaperRelShifted.afterCorr_step {St Msg C : Type} (P : Party)
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) :
    PPrimePaperRelShifted (s_df.afterCorr P) (m'.afterCorr P) (g.afterCorr P) := by
  rw [← afterCorrShifted_zero_eq_afterCorr s_df P]; exact hrel.afterCorrShifted_step 0 P

theorem pprimePaperRelShifted_corr_step {St Msg C : Type} (l : ℕ) (P : Party)
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g) (hallow_g : g.corrAllowed P = true) :
    s_df.win = false ∧ s_df.corrAllowedPaper P = true ∧ s_df.st P = g.st P ∧
    PPrimePaperRelShifted (DeliverForge.afterCorrShifted l s_df P)
      (m'.afterCorr P) (g.afterCorr P) := by
  let _ := hallow_g
  exact ⟨hrel.win_df_false, hrel.corrAllowedPaper_df P, congrFun hrel.st_eq P,
    hrel.afterCorrShifted_step l P⟩

/-! ## `CompUnhealed` and `WFState` invariants -/

structure CompUnhealed {St Msg C : Type} (Δ : ℕ) (s : SM.GameState St Msg C) : Prop where
  trans_epoch_le : ∀ r ∈ s.trans, r.pos.epoch ≤ s.epoch r.pos.sender
  comp_unhealed : ∀ pos ∈ s.comp, SM.healedBy s.tL Δ pos.epoch = false

theorem CompUnhealed.of_wfState {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {Δ : ℕ} {s : SM.GameState St Msg C} (hwf : SM.Thm1L17.WFState Δ s) : CompUnhealed Δ s :=
  ⟨hwf.trans_epoch_le, hwf.comp_not_healed⟩

theorem CompUnhealed.comp_contains_false_of_healedBy {St Msg C : Type}
    {Δ : ℕ} {s : SM.GameState St Msg C} (hc : CompUnhealed Δ s)
    {pos : SM.Pos} (hheal : SM.healedBy s.tL Δ pos.epoch = true) :
    s.comp.contains pos = false := by
  rw [List.contains_eq_mem, decide_eq_false_iff_not]; intro hmem
  have hfalse := hc.comp_unhealed pos hmem; rw [hheal] at hfalse; cases hfalse

theorem CompUnhealed.afterCorrShifted {St Msg C : Type} {Δ : ℕ} (hΔ : 2 ≤ Δ) (l : ℕ)
    {s : SM.GameState St Msg C} (hc : CompUnhealed Δ s) (P : Party) :
    CompUnhealed Δ (DeliverForge.afterCorrShifted l s P) where
  trans_epoch_le := hc.trans_epoch_le
  comp_unhealed := by
    let e_leak :=
      if max (s.epoch .A) (s.epoch .B) = l ∧ s.epoch P + 1 ≤ l then l - 1
      else max (s.epoch .A) (s.epoch .B)
    intro pos hpos
    simp only [DeliverForge.afterCorrShifted, SM.GameState.leak, List.mem_append, List.mem_map,
      List.mem_filter] at hpos ⊢
    rcases hpos with ⟨r, ⟨hr_mem, _⟩, rfl⟩ | hpos
    · have hle := hc.trans_epoch_le r hr_mem
      have hmax : s.epoch r.pos.sender ≤ max (s.epoch .A) (s.epoch .B) := by
        cases r.pos.sender <;> simp
      have hopt := SM.Thm1L17.le_maxOpt_right s.tL e_leak
      dsimp only [e_leak] at hopt; simp only [SM.healedBy, decide_eq_false_iff_not]
      split_ifs at hopt ⊢ <;> omega
    · exact SM.Thm1L17.not_healedBy_leak (hc.comp_unhealed pos hpos)

theorem wfState_afterCorrShifted {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (l : ℕ) {s : SM.GameState St Msg C} {P : Party}
    (hwf : SM.Thm1L17.WFState Δ s) (hallow : s.corrAllowedPaper P = true) :
    SM.Thm1L17.WFState Δ (DeliverForge.afterCorrShifted l s P) := by
  let s₁ : SM.GameState St Msg C :=
    { s with comp := (s.trans.filter (fun r : SM.Record Msg C => r.pos.sender == P.other)).map
                       (fun r : SM.Record Msg C => r.pos) ++ s.comp }
  let e_leak :=
    if max (s.epoch .A) (s.epoch .B) = l ∧ s.epoch P + 1 ≤ l then l - 1
    else max (s.epoch .A) (s.epoch .B)
  have hepP_le : s.epoch P ≤ e_leak := by
    have hmaxP := hwf.epoch_le_max P; dsimp only [e_leak]; split_ifs <;> omega
  have hc_after : CompUnhealed Δ (DeliverForge.afterCorrShifted l s P) :=
    (CompUnhealed.of_wfState hwf).afterCorrShifted hΔ l P
  refine ⟨hwf.tL_leak_eq e_leak, hwf.epoch_bound, ?_, hc_after.comp_unhealed, ?_,
    hwf.trans_sender, hwf.trans_epoch_idx, ?_⟩
  · intro pe hpe; rcases List.mem_cons.mp hpe with rfl | hpe
    · exact ⟨SM.maxOpt s.tL e_leak, List.mem_cons_self,
        hepP_le.trans (SM.Thm1L17.le_maxOpt_right s.tL e_leak)⟩
    · rcases hwf.corrs_le_leaks pe hpe with ⟨l', hl', hle⟩
      exact ⟨l', List.mem_cons_of_mem _ hl', hle⟩
  · intro pos hpos; dsimp only [DeliverForge.afterCorrShifted, s₁, SM.GameState.leak] at hpos ⊢
    rcases hwf.chall_in_trans pos hpos with ⟨r, hr, rfl, huncomp⟩
    unfold SM.GameState.corrAllowedPaper at hallow
    simp only [Bool.not_eq_true', List.any_eq_false] at hallow
    have hne_other : r.pos.sender ≠ P.other :=
      fun heq => hallow r.pos hpos (beq_iff_eq.mpr heq)
    refine ⟨r, hr, rfl, fun hmem => ?_⟩; rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_map.mp hmem with ⟨r', hr', heq⟩
      rw [List.mem_filter, beq_iff_eq] at hr'; exact hne_other (heq ▸ hr'.2)
    · exact huncomp hmem
  · intro r hr huncomp; dsimp only [DeliverForge.afterCorrShifted] at hr huncomp ⊢
    have huncomp0 : r.pos ∉ s.comp := fun hmem => huncomp (List.mem_append_right _ hmem)
    have hne_other : r.pos.sender ≠ P.other := fun heq =>
      huncomp (List.mem_append_left _
        (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, beq_iff_eq.mpr heq⟩, rfl⟩))
    have hsendP : r.pos.sender = P := by
      cases h1 : r.pos.sender <;> cases P <;> simp_all [Party.other]
    have hr_le : r.pos.epoch ≤ e_leak := (hsendP ▸ hwf.trans_epoch_le r hr).trans hepP_le
    have hcanon : SM.canon r.pos.epoch { s₁.leak e_leak with corrs := (P, s.epoch P) :: s.corrs } =
        SM.canon r.pos.epoch s := SM.Thm1L17.canon_leak_of_le hr_le
    rw [hcanon]; have htc := hwf.trans_uncomp r hr huncomp0
    refine ⟨htc.1, fun pe hpe hrec => ?_⟩; rcases List.mem_cons.mp hpe with rfl | hpe
    · have hrec_eq : Party.receiverOf r.pos.epoch = r.pos.sender.other :=
        SM.Thm1L17.receiverOf_eq_other_of_sendsIn (hwf.trans_sender r hr)
      rw [hrec_eq] at hrec; dsimp only at hrec
      exact absurd (by rw [hrec, Party.other_other]) hne_other
    · exact htc.2 pe hpe hrec

end CryptoVerification.LibsignalSession.HeadlineV1
