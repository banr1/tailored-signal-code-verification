/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.LibsignalCorrNoInj

/-!
# Sanity Checks for the Injection-Free Correctness Game

**Checked by Lean.**

Sanity checks for `HonestCoins` and `configCorrNoInj` from
`Computational/Proofs/CryptoGames/SM/LibsignalCorrNoInj.lean`. Verifies that `HonestCoins` is
inhabited (`honestCoins_pure`), permits `transmit` and `chall` queries iff coins are `none`, leaves
`deliver`, `inject`, and `corr` unconstrained, and that `configCorrNoInj` refuses every `inject`
query without modifying game state.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM

variable {Key St Msg Coins RCoins C : Type}

theorem honestCoins_pure (b : Bool) : HonestCoins (pure b : AdversaryComp St Msg Coins C Bool) :=
  isQueryBoundP_pure _ _ _

private theorem query_eq_liftM (t : (unifSpec + spec St Msg Coins C).Domain) :
    (query (spec := unifSpec + spec St Msg Coins C) t : AdversaryComp St Msg Coins C _) =
      liftM ((unifSpec + spec St Msg Coins C).query t) := rfl

theorem honestCoins_transmitQuery_none (P : Party) (m : Msg) :
    HonestCoins ((transmitQuery (St := St) (C := C) (Coins := Coins) P m none >>= fun _ =>
      pure true : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins transmitQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [choosesCoins]), fun _ => isQueryBoundP_pure _ _ _⟩

theorem not_honestCoins_transmitQuery_some (P : Party) (m : Msg) (r : Coins)
    (k : Option C → Adversary St Msg Coins C) :
    ¬ HonestCoins ((transmitQuery (St := St) P m (some r) >>= k : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins transmitQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  simp [choosesCoins]

theorem honestCoins_challQuery_none (P : Party) (m₀ m₁ : Msg) :
    HonestCoins ((challQuery (St := St) (C := C) (Coins := Coins) P m₀ m₁ none >>= fun _ =>
      pure true : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins challQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [choosesCoins]), fun _ => isQueryBoundP_pure _ _ _⟩

theorem not_honestCoins_challQuery_some (P : Party) (m₀ m₁ : Msg) (r : Coins)
    (k : Option C → Adversary St Msg Coins C) :
    ¬ HonestCoins ((challQuery (St := St) P m₀ m₁ (some r) >>= k : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins challQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  simp [choosesCoins]

theorem honestCoins_deliverQuery (P : Party) (c : C)
    (k : Option (RecvResult Msg) → Adversary St Msg Coins C) (hk : ∀ u, HonestCoins (k u)) :
    HonestCoins ((deliverQuery (St := St) (Coins := Coins) P c >>= k : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins deliverQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [choosesCoins]), fun u => hk u⟩

/-- `HonestCoins` does not restrict `injectQuery`; `configCorrNoInj` refuses `inject` at the game
level. -/
theorem honestCoins_injectQuery (P : Party) (c : C)
    (k : Option (RecvResult Msg) → Adversary St Msg Coins C) (hk : ∀ u, HonestCoins (k u)) :
    HonestCoins ((injectQuery (St := St) (Coins := Coins) P c >>= k : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins injectQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [choosesCoins]), fun u => hk u⟩

theorem honestCoins_corrQuery (P : Party) (k : Option St → Adversary St Msg Coins C)
    (hk : ∀ u, HonestCoins (k u)) :
    HonestCoins ((corrQuery (Msg := Msg) (Coins := Coins) (C := C) P >>= k : AdversaryComp St Msg Coins C Bool)) := by
  unfold HonestCoins corrQuery
  rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [choosesCoins]), fun u => hk u⟩

/-- Under `configCorrNoInj`, `injectR` always returns `none` without modifying the game state. -/
theorem injectR_configCorrNoInj [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    [SampleableType RCoins] (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (must : GameState St Msg C → Party → Record Msg C → Bool) (P : Party) (c : C)
    (s : GameState St Msg C) :
    (injectR sm Δ qep (configCorrNoInj must) (P, c)).run s = pure (none, s) := by
  simp only [injectR, configCorrNoInj, StateT.run_bind, StateT.run_get, pure_bind, Bool.not_false,
    Bool.or_true, ↓reduceIte, StateT.run_pure]

end CryptoGames.SM
