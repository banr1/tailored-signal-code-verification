/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Mathlib.Data.List.Forall2
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge

/-!
# Model-Run Trace Monotonicity and Event-Match Splitting

Proves that extending a `Move` list extends `runTraceMoves` and preserves attacker knowledge and
earlier trace entries, and splits `Forall₂ (EventMatchesEntry ...)` across `runVis r (ms₀ ++ ms₁)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement

theorem move_next_le (m : Move) (tr : ExecTrace) : tr ≤ m.next tr :=
  (m.act.run tr).2.property

theorem runMoves_le : ∀ (ms : List Move) (tr : ExecTrace), tr ≤ (runMoves ms tr).1
  | [], tr => Trace.le_refl tr
  | m :: ms, tr => by
    rw [runMoves_cons_fst]
    exact Trace.le_trans _ _ _ (move_next_le m tr) (runMoves_le ms (m.next tr))

theorem runTrace_le_append (r : ProtocolSetup) (ms ms' : List Move) :
    runTraceMoves r ms ≤ runTraceMoves r (ms ++ ms') := by
  rw [runTrace_append]; exact runMoves_le ms' _

theorem attackerKnows_append {r : ProtocolSetup} {ms : List Move} (ms' : List Move) {b : DY.Bytes}
    (h : b.AttackerKnows (runTraceMoves r ms)) : b.AttackerKnows (runTraceMoves r (ms ++ ms')) :=
  Bytes.AttackerKnows_le b _ _ (runTrace_le_append r ms ms') h

theorem at?_of_le {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (h : tr ≤ tr') {i : Nat}
    (hi : i < tr.length) : (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le tr tr' h)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr tr' i hi h]

theorem forall₂_append_split {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys zs : List β}, List.Forall₂ R xs (ys ++ zs) →
      List.Forall₂ R (xs.take ys.length) ys ∧ List.Forall₂ R (xs.drop ys.length) zs
  | xs, [], zs, h => by simpa using h
  | x :: xs, y :: ys, zs, h => by
    rw [List.cons_append] at h
    cases h with
    | cons hxy hrest =>
      obtain ⟨h1, h2⟩ := forall₂_append_split hrest
      exact ⟨by simpa using List.Forall₂.cons hxy h1, by simpa using h2⟩

/-- Splits machine events matching `runVis r (ms₀ ++ ms₁)` into the prefix matching `ms₀` and the
suffix matching `ms₁`. -/
theorem eventsMatch_append_split {interpretation : CryptoProofLib.Refinement.ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ ms₁ : List Move}
    {τ : List DY.Libsignal.HwEvents.MachineEvent}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) τ (runVis r (ms₀ ++ ms₁))) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) (τ.take (runVis r ms₀).length)
        (runVis r ms₀) ∧
      List.Forall₂ (EventMatchesEntry interpretation r S g) (τ.drop (runVis r ms₀).length)
        (runMoves ms₁ (runTraceMoves r ms₀)).2 := by
  rw [runVis_append] at h
  exact forall₂_append_split h

end Symbolic.Swarm.CREF
