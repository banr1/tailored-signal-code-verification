/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import Computational.Proofs.GameHop.StateSim
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance

/-!
# Game-State Coupling Under Relabelling

State coupling between `sm₂` against `A` in `configR1OnCurve` (restricted by `keep`) and `sm₁`
against `A.relabel φ keep` in `configR1OnCurve`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Relabel.GameEq

open OracleComp OracleSpec CryptoGames CryptoGames.SM CryptoGames.Ratchet.LibsignalInst

set_option linter.unusedSectionVars false

variable {Key St₁ St₂ Msg Coins RCoins C : Type}

/-- Map party states in a `GameState` through `φ`, leaving all other fields unchanged. -/
def mapSt (φ : St₁ → St₂) (s : GameState St₁ Msg C) : GameState St₂ Msg C :=
  { st := fun P => φ (s.st P)
    epoch := s.epoch
    idx := s.idx
    tL := s.tL
    trans := s.trans
    chall := s.chall
    comp := s.comp
    maxAcc := s.maxAcc
    b := s.b
    win := s.win
    leaks := s.leaks
    corrs := s.corrs }

@[simp] theorem mapSt_st (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) :
    (mapSt φ s).st P = φ (s.st P) := rfl
@[simp] theorem mapSt_epoch (φ : St₁ → St₂) (s : GameState St₁ Msg C) :
    (mapSt φ s).epoch = s.epoch := rfl
@[simp] theorem mapSt_idx (φ : St₁ → St₂) (s : GameState St₁ Msg C) :
    (mapSt φ s).idx = s.idx := rfl
@[simp] theorem mapSt_chall (φ : St₁ → St₂) (s : GameState St₁ Msg C) :
    (mapSt φ s).chall = s.chall := rfl
@[simp] theorem mapSt_b (φ : St₁ → St₂) (s : GameState St₁ Msg C) :
    (mapSt φ s).b = s.b := rfl
@[simp] theorem mapSt_win (φ : St₁ → St₂) (s : GameState St₁ Msg C) :
    (mapSt φ s).win = s.win := rfl

@[simp] theorem mapSt_safeCh (φ : St₁ → St₂) (s : GameState St₁ Msg C) (Δ : ℕ) (P : Party) :
    (mapSt φ s).safeCh Δ P = s.safeCh Δ P := rfl
@[simp] theorem mapSt_safeInj (φ : St₁ → St₂) (s : GameState St₁ Msg C) (Δ : ℕ) :
    (mapSt φ s).safeInj Δ = s.safeInj Δ := rfl
@[simp] theorem mapSt_inTransit [DecidableEq C] (φ : St₁ → St₂) (s : GameState St₁ Msg C)
    (Q : Party) (c : C) : (mapSt φ s).inTransit Q c = s.inTransit Q c := rfl
@[simp] theorem mapSt_trivial (φ : St₁ → St₂) (s : GameState St₁ Msg C) (Δ : ℕ) (pos : Pos) :
    (mapSt φ s).trivial Δ pos = s.trivial Δ pos := rfl
@[simp] theorem mapSt_corrAllowed (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) :
    (mapSt φ s).corrAllowed P = s.corrAllowed P := rfl
@[simp] theorem mapSt_inWindow (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) :
    inWindow (mapSt φ s) P = inWindow s P := rfl
@[simp] theorem mapSt_noBobEpoch0 (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) :
    noBobSendInEpoch0 (mapSt φ s) P = noBobSendInEpoch0 s P := rfl
@[simp] theorem mapSt_noSpkCorr (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) :
    noAliceCorrWhileAliceBelowEpoch10 (mapSt φ s) P = noAliceCorrWhileAliceBelowEpoch10 s P := rfl

theorem update_comp_phi (φ : St₁ → St₂) (st : Party → St₁) (P : Party) (st' : St₁) :
    Function.update (fun Q => φ (st Q)) P (φ st') = fun Q => φ (Function.update st P st' Q) := by
  funext Q
  by_cases h : Q = P
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem mapSt_epMgmt (φ : St₁ → St₂) (s : GameState St₁ Msg C) (Δ qep : ℕ) (P : Party)
    (bad : Bool) :
    (mapSt φ s).epMgmt Δ qep P bad = (s.epMgmt Δ qep P bad).map (mapSt φ) := by
  unfold GameState.epMgmt GameState.leak GameState.safeCh mapSt
  dsimp only
  cases P.sendsIn (s.epoch P + 1) <;>
    by_cases h1 : qep < s.epoch P + 1 <;>
    by_cases h2 : qep < s.epoch P <;>
    cases bad <;>
    cases healedBy s.tL Δ (s.epoch P) <;>
    simp [h1, h2]

theorem mapSt_record (φ : St₁ → St₂) (s : GameState St₁ Msg C) (Δ : ℕ) (P : Party)
    (st' : St₁) (r : Record Msg C) (isChall : Bool) :
    (mapSt φ s).record Δ P (φ st') r isChall = mapSt φ (s.record Δ P st' r isChall) := by
  unfold GameState.record
  rw [mapSt_safeCh]
  unfold mapSt
  dsimp only
  rw [update_comp_phi]

theorem mapSt_accept (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) (st' : St₁)
    (pos : Pos) :
    (mapSt φ s).accept P (φ st') pos = mapSt φ (s.accept P st' pos) := by
  simp [GameState.accept, GameState.delete, mapSt, update_comp_phi]

theorem mapSt_afterCorr (φ : St₁ → St₂) (s : GameState St₁ Msg C) (P : Party) :
    (mapSt φ s).afterCorr P = mapSt φ (s.afterCorr P) := rfl

theorem epMgmt_st_trans {s s₁ : GameState St₁ Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : s.epMgmt Δ qep P bad = some s₁) : s₁.st = s.st ∧ s₁.trans = s.trans := by
  unfold GameState.epMgmt at hep
  split at hep
  · split at hep
    · contradiction
    · injection hep with hep
      subst hep
      split <;> exact ⟨rfl, rfl⟩
  · split at hep
    · contradiction
    · injection hep with hep
      subst hep
      exact ⟨rfl, rfl⟩

@[simp] theorem simulateQ_oracleSpec_query {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ospec m) (t : ospec.Domain) :
    simulateQ impl (query (spec := ospec) t : OracleComp ospec (ospec.Range t)) = impl t := by
  change simulateQ impl (liftM (ospec.query t)) = impl t
  simp [simulateQ_query]

theorem bind_congr_of_support {ι : Type} {ospec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp ospec α) (f g : α → OracleComp ospec β)
    (h : ∀ x ∈ support mx, f x = g x) :
    mx >>= f = mx >>= g :=
  bind_congr_of_forall_mem_support mx h

section Oracles

variable [DecidableEq Msg] [SampleableType Coins] [SampleableType RCoins]

abbrev fullImpl {St : Type} (sm : SMSchemeR Key St Msg Coins RCoins (List (BitVec 8)))
    (Δ qep : ℕ) (cfg : ConfigR St Msg (List (BitVec 8))) :
    QueryImpl (unifSpec + spec St Msg Coins (List (BitVec 8)))
      (StateT (GameState St Msg (List (BitVec 8))) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg (List (BitVec 8))) ProbComp) +
    oracleImplR sm Δ qep cfg

end Oracles

end CryptoVerification.E2E.Relabel.GameEq
