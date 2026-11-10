/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.Proofs.SpecLemmas.LeakableSecretProofDefs
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Actions.PersistentGlobalState

/-!
# Composed Refinement Step and Leak-Guard Lemmas

Proves list-append composition for `runSteps` (`runSteps_append`) and the equivalence between
`Cli.KeyInDirs` and `∃ p, Cli.KeyInDir` (`keyInDirs_iff_exists_keyInDir`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY

theorem runSteps_append : ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
    runSteps (ss₁ ++ ss₂) tr = runSteps ss₂ (runSteps ss₁ tr)
  | [], _, _ => rfl
  | s :: ss₁, ss₂, tr => runSteps_append ss₁ ss₂ (s.next tr)

private def Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private theorem Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} {b : β}
    (h1 : Runs x tr a tr1) (h2 : Runs (f a) tr1 b tr2) :
    Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, _⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', _⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem Runs.pure {α : Type} (a : α) (tr : ExecTrace) :
    Runs (Pure.pure a : Traceful α) tr a tr := ⟨rfl, rfl⟩

private theorem Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : Runs (DY.getEntry i : Traceful E) tr e tr := ⟨h, rfl⟩

private theorem Runs.requireTracePredicate {p : ExecTrace → Bool} {tr : ExecTrace} (h : p tr = true) :
    Runs (PQXDH.guardTrace p) tr () tr := by
  unfold Runs PQXDH.guardTrace
  simp only [Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

private def RunsOk {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) : Prop :=
  (x.run tr).1 = some a

private theorem RunsOk.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 : ExecTrace} {a : α} {b : β}
    (h1 : Runs x tr a tr1) (h2 : RunsOk (f a) tr1 b) :
    RunsOk (x >>= f) tr b := by
  obtain ⟨h1a, h1b⟩ := h1
  unfold RunsOk at h2 ⊢
  rw [Traceful.run_bind]
  rcases hx : x.run tr with ⟨o, t, _⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  exact h2

/-- `Cli.KeyInDirs` is equivalent to `Cli.KeyInDir` for some participant. -/
theorem keyInDirs_iff_exists_keyInDir (r : ProtocolSetup) (hne : r.alice ≠ r.bob)
    (t : Cli.CliTurn) (k : HwBytes) :
    Cli.KeyInDirs r t k ↔ ∃ p, Cli.KeyInDir r t p k := by
  have _ := hne
  unfold Cli.KeyInDirs LeakableSecret Cli.KeyInDir Cli.SetupDHSecret Cli.BobSetupDHSecret
  constructor
  · rintro (hk | (h0 | h1 | h2 | hopk) | ⟨p, rec, hrec, hkey⟩)
    · exact ⟨r.bob, Or.inr (Or.inl ⟨rfl, Or.inl hk⟩)⟩
    · exact ⟨r.alice, Or.inl ⟨rfl, h0⟩⟩
    · exact ⟨r.bob, Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl h1)⟩)⟩
    · exact ⟨r.bob, Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl h2))⟩)⟩
    · exact ⟨r.bob, Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr hopk))⟩)⟩
    · exact ⟨p, Or.inr (Or.inr ⟨rec, hrec, hkey⟩)⟩
  · rintro ⟨p, ⟨_, h0⟩ | ⟨_, hk | h1 | h2 | hopk⟩ | ⟨rec, hrec, hkey⟩⟩
    · exact Or.inr (Or.inl (Or.inl h0))
    · exact Or.inl hk
    · exact Or.inr (Or.inl (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h2))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr hopk))))
    · exact Or.inr (Or.inr ⟨p, rec, hrec, hkey⟩)

end DY.Libsignal.Composed.Refinement
