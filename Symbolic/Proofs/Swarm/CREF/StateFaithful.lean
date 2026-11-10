/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces

/-!
# Linear Session-State Snapshot Faithfulness

Proves append and single-step preservation lemmas (`stateFaithful_append` and
`stateFaithful_snoc`) for `StateFaithful`, establishing that a composed run stays
state-faithful when no appended move reloads a snapshot already consumed by a
successful state-storing move.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement

/-- `ms ++ δ` is state-faithful if `ms` is state-faithful, `δ` is state-faithful from the
post-`ms` trace, and no move in `δ` loads a snapshot already consumed by `ms`. -/
theorem stateFaithful_append {r : ProtocolSetup} {ms δ : List Move}
    (h : StateFaithful r ms)
    (hδ : ∀ (i j : Nat) (mi mj : Move) (p : Participant) (k : Nat) (b : Bool), i < j →
      δ[i]? = some mi → δ[j]? = some mj →
      mi.stateLoad? = some (p, k, true) →
      (mi.act.run (runTraceMoves r (ms ++ δ.take i))).1.isSome = true →
      mj.stateLoad? = some (p, k, b) → False)
    (hnew : ∀ (i j : Nat) (mi mj : Move) (p : Participant) (k : Nat) (b : Bool),
      ms[i]? = some mi → δ[j]? = some mj →
      mi.stateLoad? = some (p, k, true) →
      (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true →
      mj.stateLoad? = some (p, k, b) → False) :
    StateFaithful r (ms ++ δ) := by
  intro i j mi mj p k b hij hi hj hl hs hl'
  by_cases hjm : j < ms.length
  · have him : i < ms.length := Nat.lt_trans hij hjm
    rw [List.getElem?_append_left him] at hi
    rw [List.getElem?_append_left hjm] at hj
    rw [List.take_append_of_le_length (Nat.le_of_lt him)] at hs
    exact h i j mi mj p k b hij hi hj hl hs hl'
  · have hj' : (ms ++ δ)[j]? = δ[j - ms.length]? :=
      List.getElem?_append_right (Nat.le_of_not_lt hjm)
    rw [hj'] at hj
    by_cases him : i < ms.length
    · rw [List.getElem?_append_left him] at hi
      rw [List.take_append_of_le_length (Nat.le_of_lt him)] at hs
      exact hnew i (j - ms.length) mi mj p k b hi hj hl hs hl'
    · have hle : ms.length ≤ i := Nat.le_of_not_lt him
      rw [List.getElem?_append_right hle] at hi
      have htake : (ms ++ δ).take i = ms ++ δ.take (i - ms.length) := by
        rw [List.take_append, List.take_of_length_le hle]
      rw [htake] at hs
      exact hδ (i - ms.length) (j - ms.length) mi mj p k b (by omega) hi hj hl hs hl'

/-- Appending a move that does not reload any snapshot already consumed by a successful
state-storing move preserves `StateFaithful`. -/
theorem stateFaithful_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (h : StateFaithful r ms)
    (hm : ∀ (i : Nat) (mi : Move) (p : Participant) (k : Nat) (b : Bool),
      ms[i]? = some mi → mi.stateLoad? = some (p, k, true) →
      (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true →
      m.stateLoad? = some (p, k, b) → False) :
    StateFaithful r (ms ++ [m]) := by
  refine stateFaithful_append h ?_ ?_
  · intro _ j _ _ _ _ _ hij _ hj _ _ _
    have hj1 : j < 1 := (List.getElem?_eq_some_iff.mp hj).1
    omega
  · intro i j mi mj p k b hi hj hl hs hl'
    have hj1 : j < 1 := (List.getElem?_eq_some_iff.mp hj).1
    obtain rfl : j = 0 := by omega
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    exact hm i mi p k b hi hl hs hl'

end Symbolic.Swarm.CREF
