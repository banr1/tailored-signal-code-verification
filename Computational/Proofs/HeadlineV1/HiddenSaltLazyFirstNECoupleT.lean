/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple2
import ProofLib.SepLogic.WP.StateNorm

/-!
# K4-Doomed Cell Disjunct and `T⁻` Cell Triviality Coupling

**Checked by Lean.** Defines the K4-doomed frozen-cell predicate `CellK4Doomed`, the `T⁻`
triviality predicate `cellTrivialT`, the compromised-set relation `CellCompRel`, and the
cell-family invariant `FirstNECellFamilyInvT` with its step preservation lemmas.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open CryptoGames CryptoGames.SM.Engine
open CryptoGames.SM.Thm1
open CryptoGames.SM.Thm1L17
open CryptoGames.SM.Construction
open CryptoGames.LibsignalSM.Proofs.Refinement

noncomputable section

namespace CryptoVerification.LibsignalSession.HeadlineV1

/-- Predicate for a `B1(t)` cell (`2 ≤ t ∧ tL = some (t - 2)`) whose target sender is corrupted at
`t` and which has already set `s.win = true`. -/
def CellK4Doomed {St Msg C : Type} (tL : Option ℕ) (t : ℕ)
    (g s : SM.GameState St Msg C) : Prop :=
  2 ≤ t ∧ tL = some (t - 2) ∧
    ((Party.senderOf t, t) ∈ g.corrs ∧ (Party.senderOf t, t) ∈ s.corrs) ∧ s.win = true

theorem CellK4Doomed.not_of_not_B1 {St Msg C : Type} {tL : Option ℕ} {t : ℕ}
    {g s : SM.GameState St Msg C} (hnot : ¬(2 ≤ t ∧ tL = some (t - 2))) :
    ¬CellK4Doomed tL t g s := by
  rintro ⟨ht2, htL, _, _⟩
  exact hnot ⟨ht2, htL⟩

theorem CellK4Doomed.not_of_k4Free {St Msg C : Type} {tL : Option ℕ} {t : ℕ}
    {g s : SM.GameState St Msg C} (hk4 : (Party.senderOf t, t) ∉ g.corrs) :
    ¬CellK4Doomed tL t g s := by
  rintro ⟨_, _, ⟨hmem, _⟩, _⟩
  exact hk4 hmem

theorem CellK4Doomed.of_corrs_sub {St Msg C : Type} {tL : Option ℕ} {t : ℕ}
    {g g' s : SM.GameState St Msg C} (h : CellK4Doomed tL t g s)
    (hsub : ∀ pe ∈ g.corrs, pe ∈ g'.corrs) :
    CellK4Doomed tL t g' s :=
  ⟨h.1, h.2.1, ⟨hsub _ h.2.2.1.1, h.2.2.1.2⟩, h.2.2.2⟩

/-! ## Cell triviality and runner -/

/-- Cell triviality predicate treating off-target positions below `min (s.epoch .A) (s.epoch .B)` as
trivial in `B1(t)` and using `s.trivial 3` elsewhere. -/
def cellTrivialT {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (tL : Option ℕ) (t : ℕ) (s : SM.GameState St Msg C) (pos : SM.Pos) : Bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    s.trivial 2 pos ||
      (pos.epoch != t && decide (pos.epoch < min (s.epoch .A) (s.epoch .B)))
  else
    s.trivial (2 + 1) pos

@[simp] theorem cellTrivialT_none {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (t : ℕ) (s : SM.GameState St Msg C) (pos : SM.Pos) :
    cellTrivialT none t s pos = s.trivial (2 + 1) pos := by
  unfold cellTrivialT
  simp

theorem cellTrivialT_of_not_B1 {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {tL : Option ℕ} {t : ℕ} (hnot : ¬(2 ≤ t ∧ tL = some (t - 2)))
    (s : SM.GameState St Msg C) (pos : SM.Pos) :
    cellTrivialT tL t s pos = s.trivial (2 + 1) pos := by
  unfold cellTrivialT
  simp [hnot]

theorem cellTrivialT_at_target {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (tL : Option ℕ) (t : ℕ) (s : SM.GameState St Msg C) (pos : SM.Pos) (hep : pos.epoch = t) :
    cellTrivialT tL t s pos = s.trivial (cellDelta tL t) pos := by
  unfold cellTrivialT cellDelta
  split_ifs <;> simp [hep]

theorem cellTrivialT_eq_trivB1 {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {t : ℕ} (ht2 : 2 ≤ t) (s : SM.GameState St Msg C) :
    cellTrivialT (some (t - 2)) t s = trivB1 t s := by
  funext pos; unfold cellTrivialT trivB1; simp [ht2]

def injectImplCell {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg) :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) ProbComp) := fun ⟨P, c⟩ => do
  let s ← get
  if s.win || (s.inTransit P.other c).isSome || !(s.safeInj (cellDelta tL t)) then return none
  match sm.receive (s.st P) c with
  | none => return some .rejected
  | some (st', t', i', m') =>
    if qep + 1 < t' then return some .rejected
    let pos : SM.Pos := ⟨P.other, t', i'⟩
    if cellTrivialT tL t s pos then
      set (s.accept P st' pos); return some (.accepted t' i' (some m'))
    else
      if cfg.injectFull t' then set { s with win := true }
      return some .rejected

def deliverForgeBaseImplCell {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (t : ℕ) (sameHdr : C → C → Bool)
    (cfg : SM.Config Msg) :
    QueryImpl ((Party × C × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) ProbComp) := fun ⟨P, c, c'⟩ => do
  let s ← get
  if s.win then return none
  match s.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.inTransit P.other c').isSome || s.comp.contains r.pos || !(sameHdr c c') then return none
    match sm.receive (s.st P) c' with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if cellTrivialT tL t s pos then
        set (s.accept P st' pos); return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then set { s with win := true }
        return some .rejected

def oracleImplCellPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (cfg : SM.Config Msg) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  SM.transmitImpl sm (cellDelta tL t) qep + SM.challImpl sm (cellDelta tL t) qep cfg +
    SM.deliverImpl sm cfg + injectImplCell sm qep tL t cfg +
    corrImplShiftedPaper (St := St) (Msg := Msg) (C := C) (cellShift tL t)

def oracleImplBaseDFCellPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg) :
    QueryImpl (DeliverForge.specDF St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  oracleImplCellPaper sm qep tL t cfg + deliverForgeBaseImplCell sm qep tL t sameHdr cfg

abbrev fullImplBaseDFCellPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg) :
    QueryImpl (unifSpec + DeliverForge.specDF St Msg Coins C)
      (StateT (SM.GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (SM.GameState St Msg C) ProbComp) +
    oracleImplBaseDFCellPaper sm qep sameHdr tL t cfg

/-- Per-cell paper `DeliverForge` runner using `cellDelta`, `cellTrivialT`, and `cellShift`. -/
def runBaseDFCellPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) : ProbComp (Bool × SM.GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplBaseDFCellPaper sm qep sameHdr tL t cfg) B).run (SM.initState sm k b)

theorem injectImplCell_eq_injectImplB1 {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {t : ℕ} (ht2 : 2 ≤ t) (cfg : SM.Config Msg) :
    injectImplCell sm qep (some (t - 2)) t cfg = injectImplB1 sm qep t cfg := by
  have hD : cellDelta (some (t - 2)) t = 2 := by unfold cellDelta; simp [ht2]
  funext ⟨P, c⟩; apply StateT.ext; intro s
  simp only [injectImplCell, injectImplB1, StateT.run_bind, StateT.run_get, pure_bind, hD]
  split_ifs
  · rfl
  · cases sm.receive (s.st P) c with
    | none => rfl
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      simp [cellTrivialT_eq_trivB1 ht2]

theorem deliverForgeBaseImplCell_eq_deliverForgeBaseImplB1 {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {t : ℕ} (ht2 : 2 ≤ t) (sameHdr : C → C → Bool)
    (cfg : SM.Config Msg) :
    deliverForgeBaseImplCell sm qep (some (t - 2)) t sameHdr cfg =
      deliverForgeBaseImplB1 sm qep t sameHdr cfg := by
  funext ⟨P, c, c'⟩; apply StateT.ext; intro s
  simp only [deliverForgeBaseImplCell, deliverForgeBaseImplB1,
    StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · rfl
  · cases s.inTransit P.other c with
    | none => rfl
    | some r =>
      dsimp only
      split_ifs
      · rfl
      · cases sm.receive (s.st P) c' with
        | none => rfl
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          simp [cellTrivialT_eq_trivB1 ht2]

theorem fullImplBaseDFCellPaper_eq_shiftedDir2 {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    {t : ℕ} (ht2 : 2 ≤ t) (cfg : SM.Config Msg) :
    fullImplBaseDFCellPaper sm qep sameHdr (some (t - 2)) t cfg =
      fullImplBaseDFShiftedDir2Paper sm (t - 1) qep t sameHdr cfg := by
  have hD : cellDelta (some (t - 2)) t = 2 := by unfold cellDelta; simp [ht2]
  have hS : cellShift (some (t - 2)) t = t - 1 := by unfold cellShift; simp [ht2]
  simp only [fullImplBaseDFCellPaper, fullImplBaseDFShiftedDir2Paper,
    oracleImplBaseDFCellPaper, oracleImplBaseDFShiftedDir2Paper,
    oracleImplCellPaper, oracleImplShiftedDir2Paper, hD, hS,
    injectImplCell_eq_injectImplB1 sm qep ht2 cfg,
    deliverForgeBaseImplCell_eq_deliverForgeBaseImplB1 sm qep ht2 sameHdr cfg]

theorem injectImplCell_eq_injectImpl {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {tL : Option ℕ} {t : ℕ}
    (hnot : ¬(2 ≤ t ∧ tL = some (t - 2))) (cfg : SM.Config Msg) :
    injectImplCell sm qep tL t cfg = SM.injectImpl sm (cellDelta tL t) qep cfg := by
  have hD : cellDelta tL t = 2 + 1 := by unfold cellDelta; simp [hnot]
  funext ⟨P, c⟩; apply StateT.ext; intro s
  simp only [injectImplCell, SM.injectImpl, StateT.run_bind, StateT.run_get, pure_bind, hD]
  split_ifs
  · rfl
  · cases sm.receive (s.st P) c with
    | none => rfl
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      simp [cellTrivialT_of_not_B1 hnot]

theorem deliverForgeBaseImplCell_eq_deliverForgeBaseImpl {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {tL : Option ℕ} {t : ℕ}
    (hnot : ¬(2 ≤ t ∧ tL = some (t - 2))) (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    deliverForgeBaseImplCell sm qep tL t sameHdr cfg =
      DeliverForge.deliverForgeBaseImpl sm (cellDelta tL t) qep sameHdr cfg := by
  have hD : cellDelta tL t = 2 + 1 := by unfold cellDelta; simp [hnot]
  funext ⟨P, c, c'⟩; apply StateT.ext; intro s
  simp only [deliverForgeBaseImplCell, DeliverForge.deliverForgeBaseImpl,
    StateT.run_bind, StateT.run_get, pure_bind, hD]
  split_ifs
  · rfl
  · cases s.inTransit P.other c with
    | none => rfl
    | some r =>
      dsimp only
      split_ifs
      · rfl
      · cases sm.receive (s.st P) c' with
        | none => rfl
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          simp [cellTrivialT_of_not_B1 hnot]

theorem fullImplBaseDFCellPaper_eq_shifted {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    {tL : Option ℕ} {t : ℕ} (hnot : ¬(2 ≤ t ∧ tL = some (t - 2))) (cfg : SM.Config Msg) :
    fullImplBaseDFCellPaper sm qep sameHdr tL t cfg =
      fullImplBaseDFShiftedPaper sm (cellDelta tL t) (cellShift tL t) qep sameHdr cfg := by
  simp only [fullImplBaseDFCellPaper, fullImplBaseDFShiftedPaper,
    oracleImplBaseDFCellPaper, oracleImplBaseDFShiftedPaper,
    oracleImplCellPaper, oracleImplShiftedPaper,
    injectImplCell_eq_injectImpl sm qep hnot cfg,
    deliverForgeBaseImplCell_eq_deliverForgeBaseImpl sm qep hnot sameHdr cfg]

theorem accept_wf_of_cellTrivialT {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {tL : Option ℕ} {t : ℕ} {s : SM.GameState St Msg C} {Q : Party} {st' : St} {pos : SM.Pos}
    (hwf : SM.Thm1L17.WFState (cellDelta tL t) s)
    (hsafe : s.safeInj (cellDelta tL t) = true)
    (htriv : cellTrivialT tL t s pos = true) :
    SM.Thm1L17.WFState (cellDelta tL t) (s.accept Q st' pos) := by
  refine SM.Thm1L17.accept_wf hwf ?_
  unfold cellTrivialT at htriv
  split_ifs at htriv with hB1
  · have hdelta : cellDelta tL t = 2 := by
      unfold cellDelta
      simp [hB1]
    rcases Bool.or_eq_true_iff.mp htriv with htriv2 | hoff
    · exact SM.Thm1L17.pos_epoch_le_of_trivial hwf hsafe (hdelta.symm ▸ htriv2)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hoff
      have hlt := hoff.2
      cases Q <;> simp at hlt ⊢ <;> omega
  · have hdelta : cellDelta tL t = 2 + 1 := by
      unfold cellDelta
      simp [hB1]
    exact SM.Thm1L17.pos_epoch_le_of_trivial hwf hsafe (hdelta.symm ▸ htriv)

/-! ## Compromised-set relation -/

/-- Invariant relating compromised positions of the unshifted cell `s_unsh` and shifted cell `s_sh`
at `(t, tL)`. -/
structure CellCompRel {St Msg C : Type} (tL : Option ℕ) (t : ℕ)
    (s_unsh s_sh : SM.GameState St Msg C) : Prop where
  comp_in_trans : ∀ p ∈ s_unsh.comp, ∃ r₀ ∈ s_unsh.trans, r₀.pos = p
  comp_sh_sub_unsh : ∀ p ∈ s_sh.comp, p ∈ s_unsh.comp
  comp_diff_epoch_eq : ¬(2 ≤ t ∧ tL = some (t - 2)) →
    ∀ r ∈ s_unsh.trans, r.pos ∈ s_unsh.comp → r.pos ∉ s_sh.comp → r.pos.epoch = t
  comp_diff_canon_eq :
    ∀ r ∈ s_unsh.trans, r.pos.epoch = t → r.pos ∈ s_unsh.comp → r.pos ∉ s_sh.comp →
      SM.canon t s_sh = tL

theorem cellCompRel_init {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (tL : Option ℕ) (t : ℕ) (k : Key) (b : Bool) :
    CellCompRel tL t (SM.initState sm k b) (SM.initState sm k b) := by
  refine ⟨fun _ hp => ?_, fun _ hp => hp, fun _ _ hr => ?_, fun _ hr => ?_⟩
  · simp [SM.initState] at hp
  · simp [SM.initState] at hr
  · simp [SM.initState] at hr

theorem CellCompRel.accept_step {St Msg C : Type} {tL : Option ℕ} {t : ℕ}
    {s_unsh s_sh : SM.GameState St Msg C} (hrel : CellCompRel tL t s_unsh s_sh)
    (Q : Party) (st' : St) (pos : SM.Pos) :
    CellCompRel tL t (s_unsh.accept Q st' pos) (s_sh.accept Q st' pos) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    unfold SM.GameState.accept SM.GameState.delete at hp ⊢
    dsimp only at hp ⊢
    rw [List.mem_filter] at hp
    rcases hrel.comp_in_trans p hp.1 with ⟨r₀, hr₀, rfl⟩
    exact ⟨r₀, List.mem_filter.mpr ⟨hr₀, hp.2⟩, rfl⟩
  · intro p hp
    unfold SM.GameState.accept SM.GameState.delete at hp ⊢
    dsimp only at hp ⊢
    rw [List.mem_filter] at hp ⊢
    exact ⟨hrel.comp_sh_sub_unsh p hp.1, hp.2⟩
  · intro hnotB1 r hr hcomp_u hncomp_s
    unfold SM.GameState.accept SM.GameState.delete at hr hcomp_u hncomp_s
    dsimp only at hr hcomp_u hncomp_s
    rw [List.mem_filter] at hr hcomp_u
    refine hrel.comp_diff_epoch_eq hnotB1 r hr.1 hcomp_u.1 (fun hs => hncomp_s ?_)
    rw [List.mem_filter]
    exact ⟨hs, hcomp_u.2⟩
  · intro r hr hep hcomp_u hncomp_s
    unfold SM.GameState.accept SM.GameState.delete at hr hcomp_u hncomp_s
    dsimp only at hr hcomp_u hncomp_s
    rw [List.mem_filter] at hr hcomp_u
    have hcanon : SM.canon t (s_sh.accept Q st' pos) = SM.canon t s_sh := rfl
    rw [hcanon]
    refine hrel.comp_diff_canon_eq r hr.1 hep hcomp_u.1 (fun hs => hncomp_s ?_)
    rw [List.mem_filter]
    exact ⟨hs, hcomp_u.2⟩

theorem CellCompRel.corr_step {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {tL : Option ℕ} {t : ℕ}
    {s_unsh s_sh : SM.GameState St Msg C} (hrel : CellCompRel tL t s_unsh s_sh)
    (hleak : ShiftedLeakRel (cellShift tL t) s_unsh s_sh)
    (hwf_sh : SM.Thm1L17.WFState (cellDelta tL t) s_sh) (P : Party) :
    CellCompRel tL t (s_unsh.afterCorr P)
      (DeliverForge.afterCorrShifted (cellShift tL t) s_sh P) := by
  have hshift_lt : cellShift tL t = 0 ∨ cellShift tL t < t := by
    unfold cellShift
    split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    unfold SM.GameState.afterCorr SM.GameState.leak at hp ⊢
    dsimp only at hp ⊢
    rcases List.mem_append.mp hp with hp_new | hp_old
    · rcases List.mem_map.mp hp_new with ⟨r₀, hr₀, rfl⟩
      exact ⟨r₀, (List.mem_filter.mp hr₀).1, rfl⟩
    · exact hrel.comp_in_trans p hp_old
  · intro p hp
    unfold DeliverForge.afterCorrShifted SM.GameState.leak at hp
    unfold SM.GameState.afterCorr SM.GameState.leak
    dsimp only at hp ⊢
    rw [hleak.trans_eq] at hp
    rcases List.mem_append.mp hp with hp_new | hp_old
    · exact List.mem_append_left _ hp_new
    · exact List.mem_append_right _ (hrel.comp_sh_sub_unsh p hp_old)
  · intro hnotB1 r hr hcomp_u hncomp_s
    unfold SM.GameState.afterCorr SM.GameState.leak at hr hcomp_u
    unfold DeliverForge.afterCorrShifted SM.GameState.leak at hncomp_s
    dsimp only at hr hcomp_u hncomp_s
    rw [hleak.trans_eq] at hncomp_s
    rcases List.mem_append.mp hcomp_u with hnew | hold
    · exact False.elim (hncomp_s (List.mem_append_left _ hnew))
    · exact hrel.comp_diff_epoch_eq hnotB1 r hr hold
        (fun hs => hncomp_s (List.mem_append_right _ hs))
  · intro r hr hep hcomp_u hncomp_s
    have hr_sh : r ∈ s_sh.trans := hleak.trans_eq.symm ▸ hr
    have ht_le_max : t ≤ max (s_sh.epoch .A) (s_sh.epoch .B) := by
      rw [← hep]
      exact (hwf_sh.trans_epoch_le r hr_sh).trans (hwf_sh.epoch_le_max r.pos.sender)
    have ht_le_l0 : t ≤ (if max (s_sh.epoch .A) (s_sh.epoch .B) = cellShift tL t ∧
        s_sh.epoch P + 1 ≤ cellShift tL t then cellShift tL t - 1
        else max (s_sh.epoch .A) (s_sh.epoch .B)) := by
      split_ifs with hcond
      · rcases hshift_lt with h0 | hlt <;> omega
      · exact ht_le_max
    have hcanon : SM.canon t (DeliverForge.afterCorrShifted (cellShift tL t) s_sh P) =
        SM.canon t (s_sh.leak (if max (s_sh.epoch .A) (s_sh.epoch .B) = cellShift tL t ∧
          s_sh.epoch P + 1 ≤ cellShift tL t then cellShift tL t - 1
          else max (s_sh.epoch .A) (s_sh.epoch .B))) := rfl
    rw [hcanon, SM.Thm1L17.canon_leak_of_le ht_le_l0]
    unfold SM.GameState.afterCorr SM.GameState.leak at hr hcomp_u
    unfold DeliverForge.afterCorrShifted SM.GameState.leak at hncomp_s
    dsimp only at hr hcomp_u hncomp_s
    rw [hleak.trans_eq] at hncomp_s
    rcases List.mem_append.mp hcomp_u with hnew | hold
    · exact False.elim (hncomp_s (List.mem_append_left _ hnew))
    · exact hrel.comp_diff_canon_eq r hr hep hold (fun hs => hncomp_s (List.mem_append_right _ hs))

theorem ShiftedLeakRel.healedBy_sh_of_healedBy_unsh {St Msg C : Type}
    {tL : Option ℕ} {t e : ℕ} {s_unsh s_sh : SM.GameState St Msg C}
    (hleak : ShiftedLeakRel (cellShift tL t) s_unsh s_sh)
    (hunsh : SM.healedBy s_unsh.tL (2 + 1) e = true) :
    SM.healedBy s_sh.tL (cellDelta tL t) e = true := by
  cases htl_sh : s_sh.tL with
  | none => rfl
  | some k =>
    have hk_mem := (hleak.tL_sh_some k htl_sh).1
    rcases hleak.leaks_sh_to_unsh k hk_mem with ⟨m, hm_mem, hk_le_m, _⟩
    cases htl_u : s_unsh.tL with
    | none =>
      rw [hleak.leak_corr_unsh.1 htl_u] at hm_mem
      nomatch hm_mem
    | some m₀ =>
      have hm_le_m₀ := (hleak.leak_corr_unsh.2.1 m₀ htl_u).2 m hm_mem
      have hdelta := cellDelta_le_three tL t
      rw [htl_u] at hunsh
      simp only [SM.healedBy, decide_eq_true_eq] at hunsh ⊢
      omega

theorem ShiftedLeakRel.healedBy_diff_epoch_and_canon {St Msg C : Type}
    {tL : Option ℕ} {t e : ℕ} {s_unsh s_sh : SM.GameState St Msg C}
    (hleak : ShiftedLeakRel (cellShift tL t) s_unsh s_sh)
    (hunsh : SM.healedBy s_unsh.tL (2 + 1) e = false)
    (hsh : SM.healedBy s_sh.tL (cellDelta tL t) e = true) :
    (¬(2 ≤ t ∧ tL = some (t - 2)) → e = t) ∧
    (e = t → SM.canon t s_sh = tL) := by
  cases htl_u : s_unsh.tL with
  | none =>
    rw [htl_u] at hunsh
    nomatch hunsh
  | some m₀ =>
    rcases hleak.leak_corr_unsh.2.1 m₀ htl_u with ⟨hm₀_mem, hm₀_max⟩
    rw [htl_u] at hunsh
    simp only [SM.healedBy, decide_eq_false_iff_not] at hunsh
    have hx_le_m₀ : ∀ x ∈ s_sh.leaks, x ≤ m₀ := by
      intro x hx
      rcases hleak.leaks_sh_to_unsh x hx with ⟨u, hu_mem, hx_le_u, _⟩
      exact le_trans hx_le_u (hm₀_max u hu_mem)
    by_cases hm₀_sh : m₀ ∈ s_sh.leaks
    · cases htl_sh : s_sh.tL with
      | none =>
        rw [hleak.tL_sh_none htl_sh] at hm₀_sh
        nomatch hm₀_sh
      | some k =>
        have hk_ge := (hleak.tL_sh_some k htl_sh).2 m₀ hm₀_sh
        have hk_le := hx_le_m₀ k (hleak.tL_sh_some k htl_sh).1
        rw [htl_sh] at hsh
        simp only [SM.healedBy, decide_eq_true_eq] at hsh
        have hB1 : 2 ≤ t ∧ tL = some (t - 2) := by
          by_contra hnotB1
          have hdelta : cellDelta tL t = 2 + 1 := by unfold cellDelta; simp [hnotB1]
          omega
        refine ⟨fun hnotB1 => False.elim (hnotB1 hB1), fun hep => ?_⟩
        rcases hB1 with ⟨ht2, rfl⟩
        have hdelta : cellDelta (some (t - 2)) t = 2 := by unfold cellDelta; simp [ht2]
        have hm₀_eq : m₀ = t - 2 := by omega
        subst hm₀_eq
        exact canon_eq_some_of_mem_and_le hm₀_sh (by omega) (fun m hm _ => hx_le_m₀ m hm)
    · rcases hleak.leaks_unsh_to_sh m₀ hm₀_mem with ⟨h1, h2⟩
      have hm₀_shift : m₀ = cellShift tL t := by
        by_contra hne
        exact hm₀_sh (h1 hne)
      have hm₀_sub_sh : m₀ - 1 ∈ s_sh.leaks := by
        rcases h2 hm₀_shift with h_in | h_in
        · exact False.elim (hm₀_sh (hm₀_shift ▸ h_in))
        · exact hm₀_shift ▸ h_in
      have hm₀_pos : 1 ≤ m₀ := by
        by_contra h0
        have hm₀_zero : m₀ = 0 := by omega
        exact hm₀_sh (hm₀_zero ▸ hm₀_sub_sh)
      have hx_le_sub : ∀ x ∈ s_sh.leaks, x ≤ m₀ - 1 := by
        intro x hx
        have hle := hx_le_m₀ x hx
        have hne : x ≠ m₀ := fun heq => hm₀_sh (heq ▸ hx)
        omega
      cases htl_sh : s_sh.tL with
      | none =>
        rw [hleak.tL_sh_none htl_sh] at hm₀_sub_sh
        nomatch hm₀_sub_sh
      | some k =>
        have hk_ge := (hleak.tL_sh_some k htl_sh).2 (m₀ - 1) hm₀_sub_sh
        have hk_le := hx_le_sub k (hleak.tL_sh_some k htl_sh).1
        rw [htl_sh] at hsh
        simp only [SM.healedBy, decide_eq_true_eq] at hsh
        refine ⟨fun hnotB1 => ?_, fun hep => ?_⟩
        · have hdelta : cellDelta tL t = 2 + 1 := by unfold cellDelta; simp [hnotB1]
          unfold cellShift at hm₀_shift
          split_ifs at hm₀_shift <;> omega
        · subst e
          unfold cellShift at hm₀_shift
          split_ifs at hm₀_shift with hB1 hB2
          · rcases hB1 with ⟨ht2, rfl⟩
            have hsub : m₀ - 1 = t - 2 := by omega
            exact canon_eq_some_of_mem_and_le (hsub ▸ hm₀_sub_sh) (by omega)
              (fun m hm _ => hsub ▸ hx_le_sub m hm)
          · rcases hB2 with ⟨ht3, rfl⟩
            have hsub : m₀ - 1 = t - 3 := by omega
            exact canon_eq_some_of_mem_and_le (hsub ▸ hm₀_sub_sh) (by omega)
              (fun m hm _ => hsub ▸ hx_le_sub m hm)
          · omega

theorem CellCompRel.record_step {St Msg C : Type} {tL : Option ℕ} {t : ℕ}
    {s_unsh₁ s_sh₁ : SM.GameState St Msg C} (hrel : CellCompRel tL t s_unsh₁ s_sh₁)
    (hleak : ShiftedLeakRel (cellShift tL t) s_unsh₁ s_sh₁)
    (P : Party) (st' : St) (rec_r : SM.Record Msg C)
    (hep_r : rec_r.pos.epoch = s_unsh₁.epoch P) :
    CellCompRel tL t (s_unsh₁.record (2 + 1) P st' rec_r false)
      (s_sh₁.record (cellDelta tL t) P st' rec_r false) := by
  have hsafe_imp : s_unsh₁.safeCh (2 + 1) P = true →
      s_sh₁.safeCh (cellDelta tL t) P = true := by
    intro hu
    unfold SM.GameState.safeCh at hu ⊢
    rw [hleak.epoch_eq]
    exact hleak.healedBy_sh_of_healedBy_unsh hu
  have hsub_sh : ∀ p ∈ s_sh₁.comp,
      p ∈ (s_sh₁.record (cellDelta tL t) P st' rec_r false).comp := by
    intro p hp
    unfold SM.GameState.record; dsimp only
    split_ifs <;> [exact hp; exact List.mem_cons_of_mem _ hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    unfold SM.GameState.record at hp ⊢; dsimp only at hp ⊢
    split_ifs at hp with hsafe
    · rcases hrel.comp_in_trans p hp with ⟨r₀, hr₀, rfl⟩
      exact ⟨r₀, List.mem_cons_of_mem _ hr₀, rfl⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨rec_r, List.mem_cons_self, rfl⟩
      · rcases hrel.comp_in_trans p hp with ⟨r₀, hr₀, rfl⟩
        exact ⟨r₀, List.mem_cons_of_mem _ hr₀, rfl⟩
  · intro p hp
    unfold SM.GameState.record at hp ⊢; dsimp only at hp ⊢
    by_cases hu : s_unsh₁.safeCh (2 + 1) P = true
    · simp only [hu, hsafe_imp hu, ↓reduceIte] at hp ⊢
      exact hrel.comp_sh_sub_unsh p hp
    · simp only [hu, Bool.false_eq_true, ↓reduceIte]
      split_ifs at hp with hs
      · exact List.mem_cons_of_mem _ (hrel.comp_sh_sub_unsh p hp)
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hrel.comp_sh_sub_unsh p hp)
  · intro hnotB1 r _ hcomp_u hncomp_s
    have hn_sh : r.pos ∉ s_sh₁.comp := fun hs => hncomp_s (hsub_sh r.pos hs)
    by_cases hmem_u : r.pos ∈ s_unsh₁.comp
    · rcases hrel.comp_in_trans r.pos hmem_u with ⟨r₀, hr₀, hr₀_pos⟩
      rw [← hr₀_pos]
      exact hrel.comp_diff_epoch_eq hnotB1 r₀ hr₀ (hr₀_pos ▸ hmem_u) (hr₀_pos ▸ hn_sh)
    · unfold SM.GameState.record at hcomp_u hncomp_s; dsimp only at hcomp_u hncomp_s
      have hu_false : s_unsh₁.safeCh (2 + 1) P = false := by
        by_contra hu_true
        simp only [Bool.not_eq_false] at hu_true
        simp only [hu_true, ↓reduceIte] at hcomp_u
        exact hmem_u hcomp_u
      simp only [hu_false, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hcomp_u
      have hr_eq : r.pos = rec_r.pos := hcomp_u.resolve_right hmem_u
      have hs_true : s_sh₁.safeCh (cellDelta tL t) P = true := by
        by_contra hs_false
        simp only [hs_false, ↓reduceIte] at hncomp_s
        exact hncomp_s (hr_eq ▸ List.mem_cons_self)
      unfold SM.GameState.safeCh at hu_false hs_true
      rw [hleak.epoch_eq] at hs_true
      rw [hr_eq, hep_r]
      exact (hleak.healedBy_diff_epoch_and_canon hu_false hs_true).1 hnotB1
  · intro r _ hep hcomp_u hncomp_s
    have hn_sh : r.pos ∉ s_sh₁.comp := fun hs => hncomp_s (hsub_sh r.pos hs)
    have hcanon : SM.canon t (s_sh₁.record (cellDelta tL t) P st' rec_r false) =
        SM.canon t s_sh₁ := rfl
    rw [hcanon]
    by_cases hmem_u : r.pos ∈ s_unsh₁.comp
    · rcases hrel.comp_in_trans r.pos hmem_u with ⟨r₀, hr₀, hr₀_pos⟩
      exact hrel.comp_diff_canon_eq r₀ hr₀ (by rw [hr₀_pos, hep])
        (hr₀_pos ▸ hmem_u) (hr₀_pos ▸ hn_sh)
    · unfold SM.GameState.record at hcomp_u hncomp_s; dsimp only at hcomp_u hncomp_s
      have hu_false : s_unsh₁.safeCh (2 + 1) P = false := by
        by_contra hu_true
        simp only [Bool.not_eq_false] at hu_true
        simp only [hu_true, ↓reduceIte] at hcomp_u
        exact hmem_u hcomp_u
      simp only [hu_false, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hcomp_u
      have hr_eq : r.pos = rec_r.pos := hcomp_u.resolve_right hmem_u
      have hs_true : s_sh₁.safeCh (cellDelta tL t) P = true := by
        by_contra hs_false
        simp only [hs_false, ↓reduceIte] at hncomp_s
        exact hncomp_s (hr_eq ▸ List.mem_cons_self)
      unfold SM.GameState.safeCh at hu_false hs_true
      rw [hleak.epoch_eq] at hs_true
      have hep_P : s_unsh₁.epoch P = t := by rw [← hep_r, ← hr_eq, hep]
      exact (hleak.healedBy_diff_epoch_and_canon hu_false hs_true).2 hep_P

theorem CellCompRel.transmit_step {St Msg C : Type} {tL : Option ℕ} {t qep : ℕ}
    (P : Party) (st' : St) (rec_r : SM.Record Msg C)
    {s_unsh s_unsh₁ s_sh s_sh₁ : SM.GameState St Msg C}
    (hrel : CellCompRel tL t s_unsh s_sh)
    (hleak : ShiftedLeakRel (cellShift tL t) s_unsh s_sh)
    (hep_unsh : s_unsh.epMgmt (2 + 1) qep P false = some s_unsh₁)
    (hep_sh : s_sh.epMgmt (cellDelta tL t) qep P false = some s_sh₁)
    (hep_r : rec_r.pos.epoch = s_unsh₁.epoch P) :
    CellCompRel tL t (s_unsh₁.record (2 + 1) P st' rec_r false)
      (s_sh₁.record (cellDelta tL t) P st' rec_r false) := by
  have ⟨hrel₁, hleak₁⟩ :
      CellCompRel tL t s_unsh₁ s_sh₁ ∧ ShiftedLeakRel (cellShift tL t) s_unsh₁ s_sh₁ := by
    unfold SM.GameState.epMgmt at hep_unsh hep_sh
    rw [hleak.epoch_eq] at hep_sh
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep_unsh hep_sh
    split_ifs at hep_unsh hep_sh with h1 h2
    · injection hep_unsh with hu; injection hep_sh with hs; subst hu hs
      exact ⟨⟨hrel.1, hrel.2, hrel.3, hrel.4⟩,
        ⟨hleak.1, hleak.2, by simp [hleak.3], by simp [hleak.4], hleak.5, hleak.6, hleak.7,
          hleak.8, hleak.9, hleak.10, hleak.11, hleak.12, hleak.13, hleak.14⟩⟩
    · injection hep_unsh with hu; injection hep_sh with hs; subst hu hs
      exact ⟨hrel, hleak⟩
  exact hrel₁.record_step hleak₁ P st' rec_r hep_r

/-! ## Cell-family invariant -/

def FirstNECellFamilyInvT {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (fl : Bool) (g : SM.GameState St Msg C) (m' : Mirror Msg C)
    (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  (∃ t ∈ Finset.range ((qep + 1) + 2), ∃ tL ∈ SM.admissibleLastLeakGuesses 2 t,
    cellWinPred tL t (s_cell t tL) = true) ∨
  (fl = false ∧
    (∀ t₁ ∈ Finset.range ((qep + 1) + 2), ∀ t₂ ∈ Finset.range ((qep + 1) + 2),
      s_cell t₁ none = s_cell t₂ none) ∧
    ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))

theorem firstNECellFamilyInvT_deliver_noProbe_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (qep : ℕ) (Q : Party) (st' : St) (pos : SM.Pos)
    {fl : Bool} {m' m₁' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hinv : FirstNECellFamilyInvT qep fl g m' s_cell)
    (hpos : pos.epoch ≤ max (g.epoch Q) (g.epoch Q.other)) :
    FirstNECellFamilyInvT qep fl (g.accept Q st' pos) m₁'
      (fun t tL => if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' pos) := by
  rcases hinv with ⟨t, ht, tL, htL, hwin⟩ | ⟨hfl, hcol, hrel_all⟩
  · refine Or.inl ⟨t, ht, tL, htL, ?_⟩
    have hswin : (s_cell t tL).win = true := s_win_of_cellWinPred hwin
    dsimp only; simp only [hswin, ↓reduceIte]; exact hwin
  · refine Or.inr ⟨hfl, ?_, ?_⟩
    · intro t₁ ht₁ t₂ ht₂; dsimp only; rw [hcol t₁ ht₁ t₂ ht₂]
    · intro t ht
      rcases hrel_all t ht with ⟨hrel_none, hwf_none, hcell_t⟩
      dsimp only
      simp only [hrel_none.win_df_false, Bool.false_eq_true, ↓reduceIte]
      have hrel_none' : PPrimePaperRel ((s_cell t none).accept Q st' pos) m₁'
          (g.accept Q st' pos) :=
        (pprimePaperRel_inject_step (Key := Key) (Coins := Coins) (2 + 1) Q st' pos
          hrel_none).of_mirror m₁'
      have hwf_none' : SM.Thm1L17.WFState (2 + 1) ((s_cell t none).accept Q st' pos) := by
        refine SM.Thm1L17.accept_wf hwf_none ?_
        rw [hrel_none.epoch_eq]; exact hpos
      refine ⟨hrel_none', hwf_none', fun tL htL => ?_⟩
      rcases hcell_t tL htL with hdoomed | ⟨hrel_sh, hwf_sh, hleak_sh, hcomp_sh⟩
      · simp only [hdoomed.2.2.2, ↓reduceIte]
        exact Or.inl (hdoomed.of_corrs_sub (fun _ h => h))
      · simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
        have hrel_sh' : PPrimePaperRelShifted ((s_cell t tL).accept Q st' pos) m₁'
            (g.accept Q st' pos) :=
          (pprimePaperRelShifted_inject_step (Key := Key) (Coins := Coins) (cellDelta tL t)
            Q st' pos hrel_sh).of_mirror m₁'
        have hwf_sh' : SM.Thm1L17.WFState (cellDelta tL t)
            ((s_cell t tL).accept Q st' pos) := by
          refine SM.Thm1L17.accept_wf hwf_sh ?_
          rw [hrel_sh.epoch_eq]; exact hpos
        exact Or.inr ⟨hrel_sh', hwf_sh', hleak_sh.accept_step (cellShift tL t) Q st' pos,
          hcomp_sh.accept_step Q st' pos⟩

theorem firstNECellFamilyInvT_corr_step {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (P : Party) {fl : Bool} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hinv : FirstNECellFamilyInvT qep fl g m' s_cell) (hallow_g : g.corrAllowed P = true) :
    FirstNECellFamilyInvT qep fl (g.afterCorr P) (m'.afterCorr P)
      (fun t tL => if (s_cell t tL).win then s_cell t tL
        else DeliverForge.afterCorrShifted (cellShift tL t) (s_cell t tL) P) := by
  rcases hinv with ⟨t, ht, tL, htL, hwin⟩ | ⟨hfl, hcol, hrel_all⟩
  · refine Or.inl ⟨t, ht, tL, htL, ?_⟩
    have hswin : (s_cell t tL).win = true := s_win_of_cellWinPred hwin
    dsimp only; simp only [hswin, ↓reduceIte]; exact hwin
  · refine Or.inr ⟨hfl, ?_, ?_⟩
    · intro t₁ ht₁ t₂ ht₂
      have heq : s_cell t₁ none = s_cell t₂ none := hcol t₁ ht₁ t₂ ht₂
      have hsh₁ : cellShift none t₁ = 0 := by simp [cellShift]
      have hsh₂ : cellShift none t₂ = 0 := by simp [cellShift]
      dsimp only; rw [heq, hsh₁, hsh₂]
    · intro t ht
      rcases hrel_all t ht with ⟨hrel_none, hwf_none, hcell_t⟩
      dsimp only
      have hsh_none : cellShift none t = 0 := by simp [cellShift]
      simp only [hrel_none.win_df_false, Bool.false_eq_true, ↓reduceIte, hsh_none,
        afterCorrShifted_zero_eq_afterCorr]
      have hallow_none : (s_cell t none).corrAllowedPaper P = true :=
        hrel_none.corrAllowedPaper_df P
      have hmax_df : SM.maxOpt (s_cell t none).tL
          (max ((s_cell t none).epoch .A) ((s_cell t none).epoch .B)) =
          max (g.epoch .A) (g.epoch .B) := by
        rw [← hrel_none.epoch_eq]
        cases htl : (s_cell t none).tL with
        | none => rfl
        | some l₀ => exact Nat.max_eq_right (hrel_none.tL_df_le_max l₀ htl)
      have hmax_g : SM.maxOpt g.tL (max (g.epoch .A) (g.epoch .B)) =
          max (g.epoch .A) (g.epoch .B) := by
        cases htl : g.tL with
        | none => rfl
        | some l₀ => exact Nat.max_eq_right (hrel_none.tL_g_le_max l₀ htl)
      have hrel_none' : PPrimePaperRel ((s_cell t none).afterCorr P) (m'.afterCorr P)
          (g.afterCorr P) := by
        refine (hrel_none.toShifted.afterCorr_step P).toPaperRel ?_
        intro e he
        simp only [SM.GameState.afterCorr, SM.GameState.leak, hmax_df, hmax_g,
          List.mem_cons] at he ⊢
        exact he.imp id (hrel_none.leaks_sub e)
      have hwf_none' : SM.Thm1L17.WFState (2 + 1) ((s_cell t none).afterCorr P) := by
        rw [← afterCorrShifted_zero_eq_afterCorr (s_cell t none) P]
        exact wfState_afterCorrShifted (by omega) 0 hwf_none hallow_none
      refine ⟨hrel_none', hwf_none', fun tL htL => ?_⟩
      rcases hcell_t tL htL with hdoomed | ⟨hrel_sh, hwf_sh, hleak_sh, hcomp_sh⟩
      · simp only [hdoomed.2.2.2, ↓reduceIte]
        exact Or.inl (hdoomed.of_corrs_sub (fun _ h => List.mem_cons_of_mem _ h))
      · simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
        rcases pprimePaperRelShifted_corr_step (cellShift tL t) P hrel_sh hallow_g with
          ⟨_, hallow_sh, _, hrel_sh'⟩
        exact Or.inr ⟨hrel_sh',
          wfState_afterCorrShifted (two_le_cellDelta tL t) (cellShift tL t) hwf_sh hallow_sh,
          hleak_sh.corr_step (cellShift tL t) P hwf_none hrel_none.tL_df_le_max
            hrel_sh.tL_df_le_max,
          hcomp_sh.corr_step hleak_sh hwf_sh P⟩

theorem firstNECellFamilyInvT_send_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (P : Party) (m_msg : Msg) (coins : Coins)
    (bad isChall : Bool) {fl : Bool} {m' m₁' : Mirror Msg C} {g g₁ : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hinv : FirstNECellFamilyInvT qep fl g m' s_cell)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁) :
    let c := (sm.send (g₁.st P) m_msg coins).2
    let st' := (sm.send (g₁.st P) m_msg coins).1
    let rec_r : SM.Record Msg C := ⟨⟨P, g₁.epoch P, g₁.idx P + 1⟩, m_msg, c⟩
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL
      else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) P false with
        | some s₁ => s₁.record (cellDelta tL t) P st' rec_r false
        | none => s_cell t tL
    FirstNECellFamilyInvT qep fl (g₁.record (2 + 1) P st' rec_r isChall) m₁' s_cell' := by
  intro c st' rec_r s_cell'
  rcases hinv with ⟨t, ht, tL, htL, hwin⟩ | ⟨hfl, hcol, hrel_all⟩
  · refine Or.inl ⟨t, ht, tL, htL, ?_⟩
    have hswin : (s_cell t tL).win = true := s_win_of_cellWinPred hwin
    dsimp only [s_cell']; simp only [hswin, ↓reduceIte]; exact hwin
  · refine Or.inr ⟨hfl, ?_, ?_⟩
    · intro t₁ ht₁ t₂ ht₂
      have heq : s_cell t₁ none = s_cell t₂ none := hcol t₁ ht₁ t₂ ht₂
      have hdelta₁ : cellDelta none t₁ = 2 + 1 := by simp [cellDelta]
      have hdelta₂ : cellDelta none t₂ = 2 + 1 := by simp [cellDelta]
      dsimp only [s_cell']; rw [heq, hdelta₁, hdelta₂]
    · intro t ht
      rcases hrel_all t ht with ⟨hrel_none, hwf_none, hcell_t⟩
      have hdelta_none : cellDelta none t = 2 + 1 := by simp [cellDelta]
      rcases hrel_none.epMgmt_step (Δ := 2 + 1) (m₁' := m₁') hep_g with
        ⟨s_unsh₁, hep_unsh, hrel_u₁⟩
      have hrel_none' : PPrimePaperRel (s_unsh₁.record (2 + 1) P st' rec_r false) m₁'
          (g₁.record (2 + 1) P st' rec_r isChall) :=
        hrel_u₁.record_step (le_refl _) P st' rec_r isChall
      have hcell_none_eq : s_cell' t none = s_unsh₁.record (2 + 1) P st' rec_r false := by
        dsimp only [s_cell']
        simp only [hrel_none.win_df_false, Bool.false_eq_true, ↓reduceIte, hdelta_none, hep_unsh]
      have hepoch_u : g₁.epoch P = s_unsh₁.epoch P := (congrFun hrel_u₁.epoch_eq P).symm
      have hidx_u : g₁.idx P = s_unsh₁.idx P := (congrFun hrel_u₁.idx_eq P).symm
      have hwf_none' : SM.Thm1L17.WFState (2 + 1) (s_cell' t none) := by
        rw [hcell_none_eq]
        obtain ⟨hwf₁, hsends₁⟩ := SM.Thm1L17.epMgmt_wf hwf_none hep_unsh
        exact SM.Thm1L17.record_wf (by omega) hwf₁ rfl hepoch_u (by simp [rec_r, hidx_u])
          hsends₁ (by intro h; nomatch h)
      have hcorrs_g : g.corrs = (g₁.record (2 + 1) P st' rec_r isChall).corrs := by
        have h1 : (s_cell t none).corrs = s_unsh₁.corrs := by
          unfold SM.GameState.epMgmt at hep_unsh
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep_unsh
          split_ifs at hep_unsh <;> { injection hep_unsh with hu; subst hu; rfl }
        rw [← hrel_none.corrs_eq, h1, ← hrel_none'.corrs_eq]; rfl
      refine ⟨hcell_none_eq ▸ hrel_none', hwf_none', fun tL htL => ?_⟩
      rcases hcell_t tL htL with hdoomed | ⟨hrel_sh, hwf_sh, hleak_sh, hcomp_sh⟩
      · have hcell_eq : s_cell' t tL = s_cell t tL := by
          dsimp only [s_cell']; simp only [hdoomed.2.2.2, ↓reduceIte]
        rw [hcell_eq]
        exact Or.inl (hdoomed.of_corrs_sub (fun _ h => hcorrs_g ▸ h))
      · rcases hrel_sh.epMgmt_step (Δ := cellDelta tL t) (m₁' := m₁') hep_g with
          ⟨s_sh₁, hep_sh, _, _, hrel_s₁⟩
        have hrel_sh' : PPrimePaperRelShifted
            (s_sh₁.record (cellDelta tL t) P st' rec_r false) m₁'
            (g₁.record (2 + 1) P st' rec_r isChall) :=
          hrel_s₁.record_step (cellDelta_le_three tL t) P st' rec_r isChall
        have hcell_sh_eq : s_cell' t tL = s_sh₁.record (cellDelta tL t) P st' rec_r false := by
          dsimp only [s_cell']
          simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte, hep_sh]
        have hepoch_s : g₁.epoch P = s_sh₁.epoch P := (congrFun hrel_s₁.epoch_eq P).symm
        have hidx_s : g₁.idx P = s_sh₁.idx P := (congrFun hrel_s₁.idx_eq P).symm
        have hwf_sh' : SM.Thm1L17.WFState (cellDelta tL t) (s_cell' t tL) := by
          rw [hcell_sh_eq]
          obtain ⟨hwf₁, hsends₁⟩ := SM.Thm1L17.epMgmt_wf hwf_sh hep_sh
          exact SM.Thm1L17.record_wf (pos_cellDelta tL t) hwf₁ rfl hepoch_s
            (by simp [rec_r, hidx_s]) hsends₁ (by intro h; nomatch h)
        refine Or.inr ⟨hcell_sh_eq ▸ hrel_sh', hwf_sh', ?_, ?_⟩
        · rw [hcell_none_eq, hcell_sh_eq]
          exact hleak_sh.transmit_step (cellShift tL t) (2 + 1) (cellDelta tL t) (qep + 1) P st'
            rec_r hep_unsh hep_sh
        · rw [hcell_none_eq, hcell_sh_eq]
          exact hcomp_sh.transmit_step P st' rec_r hleak_sh hep_unsh hep_sh hepoch_u

theorem firstNECellFamilyInvT_transmit_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (P : Party) (m_msg : Msg) (coins : Coins)
    (bad : Bool) {fl : Bool} {m' m₁' : Mirror Msg C} {g g₁ : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hinv : FirstNECellFamilyInvT qep fl g m' s_cell)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁) :
    let c := (sm.send (g₁.st P) m_msg coins).2
    let st' := (sm.send (g₁.st P) m_msg coins).1
    let rec_r : SM.Record Msg C := ⟨⟨P, g₁.epoch P, g₁.idx P + 1⟩, m_msg, c⟩
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL
      else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) P false with
        | some s₁ => s₁.record (cellDelta tL t) P st' rec_r false
        | none => s_cell t tL
    FirstNECellFamilyInvT qep fl (g₁.record (2 + 1) P st' rec_r false) m₁' s_cell' :=
  firstNECellFamilyInvT_send_step sm qep P m_msg coins bad false hinv hep_g

theorem firstNECellFamilyInvT_chall_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (P : Party) (m_msg : Msg) (coins : Coins)
    (bad : Bool) {fl : Bool} {m' m₁' : Mirror Msg C} {g g₁ : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hinv : FirstNECellFamilyInvT qep fl g m' s_cell)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁)
    (_hsafe_g : g₁.safeCh (2 + 1) P = true) :
    let c := (sm.send (g₁.st P) m_msg coins).2
    let st' := (sm.send (g₁.st P) m_msg coins).1
    let rec_r : SM.Record Msg C := ⟨⟨P, g₁.epoch P, g₁.idx P + 1⟩, m_msg, c⟩
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL
      else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) P false with
        | some s₁ => s₁.record (cellDelta tL t) P st' rec_r false
        | none => s_cell t tL
    FirstNECellFamilyInvT qep fl (g₁.record (2 + 1) P st' rec_r true) m₁' s_cell' :=
  firstNECellFamilyInvT_send_step sm qep P m_msg coins bad true hinv hep_g

theorem cellTrivialT_true_of_unsh_trivial_true_of_ne {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    {tL : Option ℕ} {t : ℕ} {s_unsh s_sh : SM.GameState St Msg C} {pos : SM.Pos}
    (hwf_unsh : SM.Thm1L17.WFState (2 + 1) s_unsh)
    (hsafe_unsh : s_unsh.safeInj (2 + 1) = true)
    (hleak : ShiftedLeakRel (cellShift tL t) s_unsh s_sh)
    (hcomp : CellCompRel tL t s_unsh s_sh)
    (htriv_u : s_unsh.trivial (2 + 1) pos = true)
    (hne : pos.epoch ≠ t) :
    cellTrivialT tL t s_sh pos = true := by
  have hunh : SM.healedBy s_unsh.tL (2 + 1) pos.epoch = false := by
    unfold SM.GameState.trivial at htriv_u
    rcases Bool.or_eq_true_iff.mp htriv_u with hcomp_u | hnot_in
    · exact hwf_unsh.comp_not_healed pos (List.contains_iff_mem.mp hcomp_u)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnot_in
      exact hnot_in.2
  unfold SM.GameState.safeInj at hsafe_unsh
  have hlt_min : pos.epoch < min (s_sh.epoch .A) (s_sh.epoch .B) := by
    rw [hleak.epoch_eq]
    cases htl : s_unsh.tL with
    | none => rw [htl] at hunh; nomatch hunh
    | some m₀ =>
      rw [htl] at hunh hsafe_unsh
      simp only [SM.healedBy, decide_eq_false_iff_not, decide_eq_true_eq] at hunh hsafe_unsh
      omega
  unfold cellTrivialT
  split_ifs with hB1
  · rw [Bool.or_eq_true_iff]
    refine Or.inr ?_
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨hne, hlt_min⟩
  · unfold SM.GameState.trivial at htriv_u ⊢
    rcases Bool.or_eq_true_iff.mp htriv_u with hcomp_u | hnot_in
    · have hmem_u : pos ∈ s_unsh.comp := List.contains_iff_mem.mp hcomp_u
      rcases hcomp.comp_in_trans pos hmem_u with ⟨r₀, hr₀, hr₀_pos⟩
      have hmem_sh : pos ∈ s_sh.comp := by
        by_contra hn_sh
        exact hne (hr₀_pos ▸ hcomp.comp_diff_epoch_eq hB1 r₀ hr₀ (hr₀_pos.symm ▸ hmem_u)
          (hr₀_pos.symm ▸ hn_sh))
      rw [List.contains_iff_mem.mpr hmem_sh, Bool.true_or]
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnot_in
      have hunh_sh : SM.healedBy s_sh.tL (2 + 1) pos.epoch = false := by
        by_contra hheal_sh
        simp only [Bool.not_eq_false] at hheal_sh
        have hdelta : cellDelta tL t = 2 + 1 := by unfold cellDelta; simp [hB1]
        exact hne ((hleak.healedBy_diff_epoch_and_canon hunh (hdelta.symm ▸ hheal_sh)).1 hB1)
      rw [hleak.trans_eq, hnot_in.1, hunh_sh]
      simp

theorem canon_eq_and_authOK_of_unsh_trivial_true_of_cellTrivialT_false
    {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {tL : Option ℕ} {t' i' : ℕ} {Q : Party} {s_unsh s_sh : SM.GameState St Msg C}
    (hwf_sh : SM.Thm1L17.WFState (cellDelta tL t') s_sh)
    (hleak : ShiftedLeakRel (cellShift tL t') s_unsh s_sh)
    (hcomp : CellCompRel tL t' s_unsh s_sh)
    (htriv_u : s_unsh.trivial (2 + 1) ⟨Q.other, t', i'⟩ = true)
    (htriv_sh : cellTrivialT tL t' s_sh ⟨Q.other, t', i'⟩ = false) :
    SM.canon t' s_sh = tL ∧ SM.authLosingConditionsAvoided (cellDelta tL t') tL t' s_sh = true := by
  let pos : SM.Pos := ⟨Q.other, t', i'⟩
  have htriv_std : s_sh.trivial (cellDelta tL t') pos = false := by
    rwa [← cellTrivialT_at_target tL t' s_sh pos rfl]
  have hcanon : SM.canon t' s_sh = tL := by
    unfold SM.GameState.trivial at htriv_u
    rcases Bool.or_eq_true_iff.mp htriv_u with hcomp_u | hnot_in
    · have hmem_u : pos ∈ s_unsh.comp := List.contains_iff_mem.mp hcomp_u
      have hn_sh : pos ∉ s_sh.comp := by
        intro hm
        have hc : s_sh.comp.contains pos = true := List.contains_iff_mem.mpr hm
        unfold SM.GameState.trivial at htriv_std
        rw [hc, Bool.true_or] at htriv_std
        nomatch htriv_std
      rcases hcomp.comp_in_trans pos hmem_u with ⟨r₀, hr₀, hr₀_pos⟩
      exact hcomp.comp_diff_canon_eq r₀ hr₀ (by rw [hr₀_pos]) (hr₀_pos.symm ▸ hmem_u)
        (hr₀_pos.symm ▸ hn_sh)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnot_in
      have hheal_sh : SM.healedBy s_sh.tL (cellDelta tL t') pos.epoch = true := by
        by_contra hunh_sh
        simp only [Bool.not_eq_true] at hunh_sh
        unfold SM.GameState.trivial at htriv_std
        rw [hleak.trans_eq, hnot_in.1, hunh_sh] at htriv_std
        simp at htriv_std
      exact (hleak.healedBy_diff_epoch_and_canon hnot_in.2 hheal_sh).2 rfl
  obtain ⟨hauth, _⟩ :=
    SM.Thm1L17.authOK_of_nontrivial_inject (pos_cellDelta tL t') hwf_sh htriv_std
  rw [hcanon] at hauth
  exact ⟨hcanon, hauth⟩

theorem firstNECellFamilyInvT_inject_step_of_unsh_trivial_false {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (Q : Party) (st' : St) (t' i' : ℕ)
    {fl : Bool} {m' m₁' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hrel_all : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (htriv_u : (s_cell t' none).trivial (2 + 1) ⟨Q.other, t', i'⟩ = false) :
    let pos : SM.Pos := ⟨Q.other, t', i'⟩
    let g' := if g.trivial (2 + 1) pos then g.accept Q st' pos else { g with win := true }
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL
      else if cellTrivialT tL t (s_cell t tL) pos then
        (s_cell t tL).accept Q st' pos
      else if t' == t then { s_cell t tL with win := true }
      else s_cell t tL
    FirstNECellFamilyInvT qep fl g' m₁' s_cell' := by
  intro pos g' s_cell'
  have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  rcases hrel_all t' ht'_mem with ⟨_, hwf_unsh, hcell_t'⟩
  obtain ⟨_, hmem3⟩ :=
    SM.Thm1L17.authOK_of_nontrivial_inject (by omega : 0 < 2 + 1) hwf_unsh htriv_u
  rcases targetsL_three_subset_targetsL_two hmem3 with ⟨htLStar, hnot_B1⟩
  set tLStar := SM.canon t' (s_cell t' none)
  rcases (hcell_t' tLStar htLStar).resolve_left (CellK4Doomed.not_of_not_B1 hnot_B1) with
    ⟨hrel_star, hwf_star, hleak_star, hcomp_star⟩
  have htriv_star_std : (s_cell t' tLStar).trivial (cellDelta tLStar t') pos = false := by
    unfold SM.GameState.trivial at htriv_u ⊢
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at htriv_u ⊢
    have hcomp_f : (s_cell t' tLStar).comp.contains pos = false := by
      rw [List.contains_eq_mem, decide_eq_false_iff_not]
      intro hm
      have hu_mem : pos ∈ (s_cell t' none).comp := hcomp_star.comp_sh_sub_unsh pos hm
      have hu_c : (s_cell t' none).comp.contains pos = true := List.contains_iff_mem.mpr hu_mem
      rw [htriv_u.1] at hu_c
      nomatch hu_c
    refine ⟨hcomp_f, ?_⟩
    rw [hleak_star.trans_eq]
    rcases htriv_u.2 with hin | hheal_u
    · exact Or.inl hin
    · exact Or.inr (hleak_star.healedBy_sh_of_healedBy_unsh hheal_u)
  have htriv_star : cellTrivialT tLStar t' (s_cell t' tLStar) pos = false := by
    rw [cellTrivialT_at_target tLStar t' (s_cell t' tLStar) pos rfl]
    exact htriv_star_std
  obtain ⟨hauth_canon, _⟩ :=
    SM.Thm1L17.authOK_of_nontrivial_inject (pos_cellDelta tLStar t') hwf_star htriv_star_std
  have hcanon_eq : SM.canon t' (s_cell t' tLStar) = tLStar :=
    canon_eq_of_shiftedLeakRel_of_mem_targetsL_three hleak_star rfl hmem3
  rw [hcanon_eq] at hauth_canon
  refine Or.inl ⟨t', ht'_mem, tLStar, htLStar, ?_⟩
  dsimp only [s_cell']
  simp only [hrel_star.win_df_false, htriv_star, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  unfold cellWinPred
  have hdelta : cellDelta tLStar t' = 2 + 1 := by unfold cellDelta; simp [hnot_B1]
  rw [hdelta] at hauth_canon
  simp only [hnot_B1, ↓reduceIte, Bool.true_and]
  exact hauth_canon

theorem firstNECellFamilyInvT_inject_step {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (Q : Party) (c : C) (st' : St) (t' i' : ℕ) (m_out : Msg)
    {fl : Bool} {m' m₁' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hinv : FirstNECellFamilyInvT qep fl g m' s_cell)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (_hnone_g : (g.inTransit Q.other c).isSome = false)
    (hsafe_g : g.safeInj (2 + 1) = true)
    (_hrcv_g : sm.receive (g.st Q) c = some (st', t', i', m_out)) :
    let pos : SM.Pos := ⟨Q.other, t', i'⟩
    let g' := if g.trivial (2 + 1) pos then g.accept Q st' pos else { g with win := true }
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL
      else if cellTrivialT tL t (s_cell t tL) pos then
        (s_cell t tL).accept Q st' pos
      else if t' == t then { s_cell t tL with win := true }
      else s_cell t tL
    FirstNECellFamilyInvT qep fl g' m₁' s_cell' := by
  let _ := sm; let _ := c; let _ := m_out
  intro pos g' s_cell'
  rcases hinv with ⟨t, ht, tL, htL, hwin⟩ | ⟨hfl, hcol, hrel_all⟩
  · refine Or.inl ⟨t, ht, tL, htL, ?_⟩
    have hswin : (s_cell t tL).win = true := s_win_of_cellWinPred hwin
    dsimp only [s_cell']; simp only [hswin, ↓reduceIte]; exact hwin
  · have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    cases htriv_u : (s_cell t' none).trivial (2 + 1) pos with
    | false =>
      exact firstNECellFamilyInvT_inject_step_of_unsh_trivial_false qep Q st' t' i'
        ht'_le hrel_all htriv_u
    | true =>
      rcases hrel_all t' ht'_mem with ⟨hrel_unsh, hwf_unsh, hcell_t'⟩
      by_cases hex : ∃ tLStar ∈ SM.admissibleLastLeakGuesses 2 t',
          ¬CellK4Doomed tLStar t' g (s_cell t' tLStar) ∧
          cellTrivialT tLStar t' (s_cell t' tLStar) pos = false ∧
          ¬(2 ≤ t' ∧ tLStar = some (t' - 2) ∧ (Party.senderOf t', t') ∈ g.corrs)
      · rcases hex with ⟨tLStar, htLStar, hnot_doomed, htriv_star, hnot_k4⟩
        rcases (hcell_t' tLStar htLStar).resolve_left hnot_doomed with
          ⟨hrel_star, hwf_star, hleak_star, hcomp_star⟩
        obtain ⟨_, hauth⟩ := canon_eq_and_authOK_of_unsh_trivial_true_of_cellTrivialT_false
          hwf_star hleak_star hcomp_star htriv_u htriv_star
        refine Or.inl ⟨t', ht'_mem, tLStar, htLStar, ?_⟩
        dsimp only [s_cell']
        simp only [hrel_star.win_df_false, htriv_star, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true]
        have hk4 : ¬(2 ≤ t' ∧ tLStar = some (t' - 2)) ∨
            (Party.senderOf t', t') ∉ (s_cell t' tLStar).corrs := by
          by_cases hB1 : 2 ≤ t' ∧ tLStar = some (t' - 2)
          · right
            rw [hrel_star.corrs_eq]
            exact fun hm => hnot_k4 ⟨hB1.1, hB1.2, hm⟩
          · exact Or.inl hB1
        unfold cellWinPred
        split_ifs with hB1
        · rcases hk4 with hnot | hk4_free
          · exact False.elim (hnot hB1)
          · have hwin :=
              cellWinPred_win_of_authOK_and_k4Free tLStar t' (s_cell t' tLStar) hauth hk4_free
            rcases hB1 with ⟨ht2, rfl⟩
            simpa [cellWinPred, ht2] using hwin
        · have hdelta : cellDelta tLStar t' = 2 + 1 := by unfold cellDelta; simp [hB1]
          rw [hdelta] at hauth
          simp only [Bool.true_and]; exact hauth
      · have htriv_g : g.trivial (2 + 1) pos = true := by
          by_contra htg
          simp only [Bool.not_eq_true] at htg
          have hdf_f := hrel_unsh.trivial_df_false_of_trivial_mir_false (Δ := 2 + 1) le_rfl htg
          rw [htriv_u] at hdf_f; nomatch hdf_f
        have hg'_eq : g' = g.accept Q st' pos := by
          dsimp only [g']; simp only [htriv_g, ↓reduceIte]
        rw [hg'_eq]
        refine Or.inr ⟨hfl, ?_, ?_⟩
        · intro t₁ ht₁ t₂ ht₂
          have heq₁ : s_cell t₁ none = s_cell t' none := hcol t₁ ht₁ t' ht'_mem
          have heq₂ : s_cell t₂ none = s_cell t' none := hcol t₂ ht₂ t' ht'_mem
          dsimp only [s_cell']
          rw [heq₁, heq₂]
          simp only [cellTrivialT_none, htriv_u, ↓reduceIte]
        · intro t ht
          rcases hrel_all t ht with ⟨hrel_none, hwf_none, hcell_t⟩
          have heq_u : s_cell t none = s_cell t' none := hcol t ht t' ht'_mem
          have htriv_ut : (s_cell t none).trivial (2 + 1) pos = true := heq_u ▸ htriv_u
          have hsafe_ut : (s_cell t none).safeInj (2 + 1) = true :=
            hrel_none.safeInj_df_of_safeInj_mir le_rfl hsafe_g
          have hs_none_eq : s_cell' t none = (s_cell t none).accept Q st' pos := by
            dsimp only [s_cell']
            simp only [hrel_none.win_df_false, Bool.false_eq_true, ↓reduceIte, cellTrivialT_none,
              htriv_ut]
          rw [hs_none_eq]
          refine ⟨(pprimePaperRel_inject_step (Key := Key) (Coins := Coins) (2 + 1) Q st' pos
              hrel_none).of_mirror m₁',
            SM.Thm1L17.accept_wf hwf_none
              (SM.Thm1L17.pos_epoch_le_of_trivial hwf_none hsafe_ut htriv_ut),
            fun tL htL => ?_⟩
          rcases hcell_t tL htL with hdoomed | ⟨hrel_sh, hwf_sh, hleak_sh, hcomp_sh⟩
          · have hw_true : (s_cell t tL).win = true := hdoomed.2.2.2
            dsimp only [s_cell']
            simp only [hw_true, ↓reduceIte]
            exact Or.inl (hdoomed.of_corrs_sub (fun _ h => h))
          · cases htriv_sh : cellTrivialT tL t (s_cell t tL) pos with
            | true =>
              have hs_sh_eq : s_cell' t tL = (s_cell t tL).accept Q st' pos := by
                dsimp only [s_cell']
                simp only [hrel_sh.win_df_false, Bool.false_eq_true, htriv_sh, ↓reduceIte]
              rw [hs_sh_eq]
              have hsafe_sh : (s_cell t tL).safeInj (cellDelta tL t) = true :=
                hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
              exact Or.inr ⟨(pprimePaperRelShifted_inject_step (Key := Key) (Coins := Coins)
                  (cellDelta tL t) Q st' pos hrel_sh).of_mirror m₁',
                accept_wf_of_cellTrivialT hwf_sh hsafe_sh htriv_sh,
                hleak_sh.accept_step (cellShift tL t) Q st' pos,
                hcomp_sh.accept_step Q st' pos⟩
            | false =>
              have ht_eq : t' = t := by
                by_contra hne
                have ht_true := cellTrivialT_true_of_unsh_trivial_true_of_ne hwf_none hsafe_ut
                  hleak_sh hcomp_sh htriv_ut hne
                rw [htriv_sh] at ht_true; nomatch ht_true
              subst ht_eq
              have hk4_cond : 2 ≤ t' ∧ tL = some (t' - 2) ∧ (Party.senderOf t', t') ∈ g.corrs := by
                by_contra hnot_k4
                refine hex ⟨tL, htL, ?_, htriv_sh, hnot_k4⟩
                intro hd
                have hw := hd.2.2.2
                rw [hrel_sh.win_df_false] at hw
                nomatch hw
              dsimp only [s_cell']
              simp only [hrel_sh.win_df_false, htriv_sh, Bool.false_eq_true, ↓reduceIte,
                beq_self_eq_true]
              exact Or.inl ⟨hk4_cond.1, hk4_cond.2.1,
                ⟨hk4_cond.2.2, hrel_sh.corrs_eq.symm ▸ hk4_cond.2.2⟩, rfl⟩

end CryptoVerification.LibsignalSession.HeadlineV1

end
