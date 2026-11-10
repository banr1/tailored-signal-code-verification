/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Process.Core

/-!
# Partial-Correctness Process Judgment Tests

Regression tests for `ProcessPartialRunsTo`, `ProcessTerminates`, `ElfPartialRunsTo`, and the
`ProofLib.Process.Core` weakening and invariant rules (`toPartial`, `of_invariant`, `mono`).
-/

set_option autoImplicit false

@[expose] public section

namespace Testing.ProcessPartial

open Arm64 Arm64.Process

/-! ## Total equals termination and partial -/

example (prog : Program) (s0 : State) (post : ProcessOutcome → Prop) (oom : State → Prop) :
    ProcessRunsTo prog s0 post oom ↔
      ProcessTerminates prog s0 post oom ∧ ProcessPartialRunsTo prog s0 post oom :=
  Iff.rfl

example (prog : Program) (s0 : State) (post : ProcessOutcome → Prop) (oom : State → Prop)
    (h : ProcessRunsTo prog s0 post oom) : ProcessPartialRunsTo prog s0 post oom :=
  h.toPartial

example (elfBytes : List (BitVec 8)) (pre : ProcessInputs → Prop)
    (post : ProcessInputs → ProcessOutcome → Prop)
    (h : ElfRunsTo elfBytes pre post (prog := Program.stdioCli)) :
    ElfPartialRunsTo elfBytes pre post (prog := Program.stdioCli) :=
  h.toPartial

/-! ## Divergence -/

theorem partial_of_forever_running {prog : Program} {s0 : State}
    (h : ∀ s, Steps prog s0 s → s.status = .Running ∧ ∃ s', Step prog s s') :
    ProcessPartialRunsTo prog s0 (fun _ => False) :=
  ProcessPartialRunsTo.of_invariant (Steps prog s0) (Steps.refl s0)
    (fun _ _ hs h1 => Steps.trans hs (Steps.step h1 (Steps.refl _)))
    (fun s hs => Or.inr (Or.inr (h s hs)))

theorem not_total_of_forever_running {prog : Program} {s0 : State}
    (h : ∀ s, Steps prog s0 s → s.status = .Running ∧ ∃ s', Step prog s s') :
    ¬ ProcessRunsTo prog s0 (fun _ => False) := by
  rintro ⟨⟨_, _, hf⟩ | ⟨sf, hs, hoom, _⟩, _⟩
  · exact hf
  · have := (h sf hs).1
    rw [hoom] at this
    cases this

/-! ## Stuck and exited initial states -/

theorem not_partial_of_halted {prog : Program} {s0 : State} {post : ProcessOutcome → Prop}
    {oom : State → Prop} (hst : s0.status = .Halted) :
    ¬ ProcessPartialRunsTo prog s0 post oom := by
  intro h
  rcases h s0 (Steps.refl s0) with ⟨_, ⟨_, hc, _⟩ | ⟨_, hc, _⟩, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩ <;>
    rw [hst] at hc <;> cases hc

theorem partial_of_exited {prog : Program} {s0 : State} {code : BitVec 64}
    (hst : s0.status = .Exited code) :
    ProcessPartialRunsTo prog s0 (· = ProcessOutcome.ofState code s0) := by
  refine ProcessPartialRunsTo.of_invariant (· = s0) rfl ?_ ?_
  · rintro s _ rfl h1
    have := Arm64.Step.status_running h1
    rw [hst] at this
    cases this
  · rintro s rfl
    exact Or.inl ⟨_, Or.inl ⟨code, hst, rfl⟩, rfl⟩

/-! ## Partial does not typecheck as total -/

/--
error: Type mismatch
  h
has type
  ElfPartialRunsTo elfBytes pre post
but is expected to have type
  ElfRunsTo elfBytes pre post
-/
#guard_msgs (error, substring := true) in
example (elfBytes : List (BitVec 8)) (pre : ProcessInputs → Prop)
    (post : ProcessInputs → ProcessOutcome → Prop) (h : ElfPartialRunsTo elfBytes pre post) :
    ElfRunsTo elfBytes pre post := h

end Testing.ProcessPartial
