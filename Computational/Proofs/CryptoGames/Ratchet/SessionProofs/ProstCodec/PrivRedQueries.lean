/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Query bound for `privRedB`

**Checked by Lean.**

Proves `privRedB_queries`, showing that the blanked privacy reduction `ThmB.privRedB` makes at most
as many SM oracle queries as the underlying adversary.
-/

@[expose] public section

open OracleComp OracleSpec

namespace CryptoGames.LibsignalSM.Proofs.PrivRedQueries

open SM SM.Thm1.L18

set_option linter.unusedSectionVars false

variable {St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

theorem isQueryBoundP_simSendB (challMsg : ℕ → Option (Msg → Msg))
    (real : Option (ℕ × (Msg → Msg))) (P : Party) (t : ℕ) (mb : Msg) (r : Option Coins) {α : Type}
    (f : Option C → Comp St Msg Coins C α)
    (hf : ∀ u, IsQueryBoundP (f u) (· matches Sum.inr _) 0) :
    IsQueryBoundP (ThmB.simSend (St := St) challMsg real P t mb r >>= f)
      (· matches Sum.inr _) 1 := by
  unfold ThmB.simSend transmitQuery challQuery
  cases real with
  | none =>
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.zero_lt_one, fun u => (hf u).mono (Nat.zero_le _)⟩
  | some p =>
    rcases p with ⟨i, blank⟩
    dsimp only
    split_ifs <;>
    · rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr Nat.zero_lt_one, fun u => (hf u).mono (Nat.zero_le _)⟩

theorem isQueryBoundP_simOraclesB (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (real : Option (ℕ × (Msg → Msg))) (o : (spec St Msg Coins C).Domain) (s : Thm1.Mirror Msg C) :
    IsQueryBoundP ((ThmB.simOracles (St := St) (Coins := Coins) Δ qep challMsg real o).run s)
      (· matches Sum.inr _) 1 := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change IsQueryBoundP ((ThmB.simTransmit (St := St) Δ qep (P, m, r)).run s)
      (· matches Sum.inr _) 1
    unfold ThmB.simTransmit transmitQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> cases s.epMgmt Δ qep P r.isSome <;> simp
  · change IsQueryBoundP ((ThmB.simChall (St := St) Δ qep challMsg real (P, m₀, m₁, r)).run s)
      (· matches Sum.inr _) 1
    unfold ThmB.simChall
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
        refine isQueryBoundP_simSendB challMsg real P (s₁.epoch P) (if s.b then m₁ else m₀) r _
          fun res => ?_
        cases res <;> simp
  · change IsQueryBoundP ((ThmB.simDeliver (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold ThmB.simDeliver deliverQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr =>
      cases rr <;> cases s.inTransit P.other c <;> simp
  · change IsQueryBoundP ((ThmB.simInject (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold ThmB.simInject injectQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp
  · change IsQueryBoundP ((ThmB.simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run s)
      (· matches Sum.inr _) 1
    unfold ThmB.simCorr corrQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_run, bind_assoc]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> simp

theorem simRunB_queries (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (real : Option (ℕ × (Msg → Msg))) (A : Adversary St Msg Coins C) (q : ℕ)
    (hq : MakesAtMostQueries A q) :
    IsQueryBoundP (ThmB.simRun Δ qep challMsg real A) (· matches Sum.inr _) q := by
  unfold ThmB.simRun
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind
    (isQueryBoundP_liftComp_unif (St := St) (Msg := Msg) (Coins := Coins) (C := C)
      ($ᵗ Bool : ProbComp Bool))
    fun b _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (ThmB.simImpl (St := St) (Coins := Coins) Δ qep challMsg real) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg C))
      (· matches Sum.inr _) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp s
      · cases hp
      · exact isQueryBoundP_simOraclesB Δ qep challMsg real o s
    · rintro (n | o) hnp s
      · change IsQueryBoundP ((ThmB.simCoins (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run s)
          (· matches Sum.inr _) 0
        unfold ThmB.simCoins
        simp only [stateT_lift_run]
        rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by rintro ⟨⟩), fun u => by simp⟩
      · exact absurd rfl hnp
  rw [StateT.run'_eq, ← Nat.add_zero q]
  have hmap : IsQueryBoundP
      (Prod.fst <$> (simulateQ (ThmB.simImpl (St := St) (Coins := Coins) Δ qep challMsg real) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg C))
      (· matches Sum.inr _) q := (isQueryBoundP_map_iff _ _ _).mpr hsim
  exact isQueryBoundP_bind hmap fun _ _ => trivial

/-- `privRedB i blank A` makes at most `q` SM oracle queries when `A` makes at most `q`. -/
theorem privRedB_queries (Δ qep i : ℕ) (blank : Msg → Msg) (A : Adversary St Msg Coins C) (q : ℕ)
    (hq : MakesAtMostQueries A q) : MakesAtMostQueries (ThmB.privRedB Δ qep i blank A) q := by
  unfold MakesAtMostQueries ThmB.privRedB
  rw [← Nat.add_zero q]
  exact isQueryBoundP_bind
    (simRunB_queries Δ qep (fun t => if t < i then some blank else none) (some (i, blank)) A q hq)
    fun _ _ => trivial

end CryptoGames.LibsignalSM.Proofs.PrivRedQueries
