/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Query bounds for Theorem 1 reductions

**Checked by Lean.** Proves that `simRun` and `challSim` make no more SM oracle queries than the
underlying adversary, along with `b`-erasure lemmas for the final hybrid `H3,qep+1`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Thm1.L18

abbrev Comp (St Msg Coins C : Type) := AdversaryComp St Msg Coins C

section Queries

variable {St Msg Coins C : Type}

lemma isQueryBoundP_liftComp_unif {α : Type} (mx : ProbComp α) :
    IsQueryBoundP (liftM mx : Comp St Msg Coins C α) (· matches Sum.inr _) 0 := by
  change IsQueryBoundP (liftComp mx (unifSpec + spec St Msg Coins C)) (· matches Sum.inr _) 0
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    change IsQueryBoundP (liftM ((unifSpec + spec St Msg Coins C).query (.inl t)) >>=
      fun u => liftComp (mx u) (unifSpec + spec St Msg Coins C)) (· matches Sum.inr _) 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by rintro ⟨⟩), fun u => ih u⟩

lemma query_eq_liftM (t : (unifSpec + spec St Msg Coins C).Domain) :
    (query (spec := unifSpec + spec St Msg Coins C) t : Comp St Msg Coins C _) =
      liftM ((unifSpec + spec St Msg Coins C).query t) := rfl

lemma isQueryBoundP_simSend (challMsg : ℕ → Option Msg) (real : Option (ℕ × Msg))
    (P : Party) (t : ℕ) (mb : Msg) (r : Option Coins) {α : Type}
    (f : Option C → Comp St Msg Coins C α)
    (hf : ∀ u, IsQueryBoundP (f u) (· matches Sum.inr _) 0) :
    IsQueryBoundP (simSend (St := St) challMsg real P t mb r >>= f)
      (· matches Sum.inr _) 1 := by
  unfold simSend transmitQuery challQuery
  cases real with
  | none =>
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.zero_lt_one, fun u => (hf u).mono (Nat.zero_le _)⟩
  | some p =>
    rcases p with ⟨i, mbar⟩
    dsimp only
    split_ifs <;>
    · rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr Nat.zero_lt_one, fun u => (hf u).mono (Nat.zero_le _)⟩

lemma stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

lemma isQueryBoundP_simOracles [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (real : Option (ℕ × Msg)) (o : (spec St Msg Coins C).Domain) (s : Mirror Msg C) :
    IsQueryBoundP ((simOracles (St := St) (Coins := Coins) Δ qep challMsg real o).run s)
      (· matches Sum.inr _) 1 := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change IsQueryBoundP ((simTransmit (St := St) Δ qep (P, m, r)).run s)
      (· matches Sum.inr _) 1
    unfold simTransmit transmitQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> cases s.epMgmt Δ qep P r.isSome <;> simp
  · change IsQueryBoundP ((simChall (St := St) Δ qep challMsg real (P, m₀, m₁, r)).run s)
      (· matches Sum.inr _) 1
    unfold simChall
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases s.epMgmt Δ qep P r.isSome with
    | none => trivial
    | some s₁ =>
      dsimp only
      cases hsafe : s₁.safeCh Δ P
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
        trivial
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          stateT_lift_run, bind_assoc, pure_bind]
        refine isQueryBoundP_simSend challMsg real P (s₁.epoch P) (if s.b then m₁ else m₀) r _
          fun res => ?_
        cases res <;> simp
  · change IsQueryBoundP ((simDeliver (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold simDeliver deliverQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr =>
      cases rr <;> cases s.inTransit P.other c <;> simp
  · change IsQueryBoundP ((simInject (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold simInject injectQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp
  · change IsQueryBoundP ((simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run s)
      (· matches Sum.inr _) 1
    unfold simCorr corrQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> simp

theorem simRun_queries [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (real : Option (ℕ × Msg)) (A : Adversary St Msg Coins C) (q : ℕ) (hq : MakesAtMostQueries A q) :
    IsQueryBoundP (simRun Δ qep challMsg real A) (· matches Sum.inr _) q := by
  unfold simRun
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind
    (isQueryBoundP_liftComp_unif (St := St) (Msg := Msg) (Coins := Coins) (C := C)
      ($ᵗ Bool : ProbComp Bool))
    fun b _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simImpl (St := St) (Coins := Coins) Δ qep challMsg real) A).run
        ({ st := fun _ => (), b } : Mirror Msg C))
      (· matches Sum.inr _) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp s
      · cases hp
      · exact isQueryBoundP_simOracles Δ qep challMsg real o s
    · rintro (n | o) hnp s
      · change IsQueryBoundP ((simCoins (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run s)
          (· matches Sum.inr _) 0
        unfold simCoins
        simp only [stateT_lift_run]
        rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by rintro ⟨⟩), fun u => by simp⟩
      · exact absurd rfl hnp
  rw [StateT.run'_eq, ← Nat.add_zero q]
  have hmap : IsQueryBoundP
      (Prod.fst <$> (simulateQ (simImpl (St := St) (Coins := Coins) Δ qep challMsg real) A).run
        ({ st := fun _ => (), b } : Mirror Msg C))
      (· matches Sum.inr _) q := (isQueryBoundP_map_iff _ _ _).mpr hsim
  exact isQueryBoundP_bind hmap fun _ _ => trivial

theorem challSim_queries_proof [DecidableEq C] (Δ qep : ℕ) (A : Adversary St Msg Coins C) (q : ℕ)
    (hq : MakesAtMostQueries A q) :
    MakesAtMostQueries (challSim Δ qep A) q := by
  unfold MakesAtMostQueries challSim
  rw [← Nat.add_zero q]
  exact isQueryBoundP_bind (simRun_queries Δ qep (fun _ => none) none A q hq) fun _ _ => trivial

end Queries

section H3Final

variable {Key St Msg Coins C : Type}

def withBFalse (s : GameState St Msg C) : GameState St Msg C :=
  { s with b := false }

lemma withBFalse_st (s : GameState St Msg C) : (withBFalse s).st = s.st := rfl
lemma withBFalse_epoch (s : GameState St Msg C) : (withBFalse s).epoch = s.epoch := rfl
lemma withBFalse_idx (s : GameState St Msg C) : (withBFalse s).idx = s.idx := rfl
lemma withBFalse_chall (s : GameState St Msg C) : (withBFalse s).chall = s.chall := rfl
lemma withBFalse_win (s : GameState St Msg C) : (withBFalse s).win = s.win := rfl

lemma withBFalse_safeCh (Δ : ℕ) (s : GameState St Msg C) (P : Party) :
    (withBFalse s).safeCh Δ P = s.safeCh Δ P := rfl

lemma withBFalse_safeInj (Δ : ℕ) (s : GameState St Msg C) :
    (withBFalse s).safeInj Δ = s.safeInj Δ := rfl

lemma withBFalse_inTransit [DecidableEq C] (s : GameState St Msg C) (Q : Party) (c : C) :
    (withBFalse s).inTransit Q c = s.inTransit Q c := rfl

lemma withBFalse_trivial (Δ : ℕ) (s : GameState St Msg C) (pos : Pos) :
    (withBFalse s).trivial Δ pos = s.trivial Δ pos := rfl

lemma withBFalse_corrAllowed (s : GameState St Msg C) (P : Party) :
    (withBFalse s).corrAllowed P = s.corrAllowed P := rfl

lemma withBFalse_record (Δ : ℕ) (s : GameState St Msg C) (P : Party) (st' : St)
    (r : Record Msg C) (isChall : Bool) :
    (withBFalse s).record Δ P st' r isChall = withBFalse (s.record Δ P st' r isChall) := rfl

lemma withBFalse_accept (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    (withBFalse s).accept P st' pos = withBFalse (s.accept P st' pos) := rfl

lemma withBFalse_afterCorr (s : GameState St Msg C) (P : Party) :
    (withBFalse s).afterCorr P = withBFalse (s.afterCorr P) := rfl

lemma epMgmt_withBFalse (Δ qep : ℕ) (s : GameState St Msg C) (P : Party) (bad : Bool) :
    (withBFalse s).epMgmt Δ qep P bad = (s.epMgmt Δ qep P bad).map withBFalse := by
  dsimp only [GameState.epMgmt, GameState.safeCh]
  by_cases h1 : P.sendsIn (s.epoch P + 1) = true <;>
    by_cases h2 : qep < s.epoch P + 1 <;>
    by_cases h3 : healedBy s.tL Δ (s.epoch P) = true <;>
    by_cases h4 : qep < s.epoch P <;>
    cases bad <;>
    simp [h1, h2, h3, h4, withBFalse, GameState.leak]

lemma epMgmt_epoch_le (Δ qep : ℕ) {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) : s₁.epoch P ≤ qep := by
  dsimp only [GameState.epMgmt, GameState.leak] at h
  split_ifs at h <;> cases h
  all_goals try simp only [Function.update_self]
  all_goals omega

lemma epMgmt_win (Δ qep : ℕ) {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) : s₁.win = s.win := by
  unfold GameState.epMgmt GameState.leak at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

abbrev runImpl [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg) :
    QueryImpl (unifSpec + spec St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (GameState St Msg C) ProbComp) + oracleImpl sm Δ qep cfg

variable [DecidableEq Msg] [DecidableEq C] (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [SampleableType Coins]

end H3Final

end CryptoGames.SM.Thm1.L18

