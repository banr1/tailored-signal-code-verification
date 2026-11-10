/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Process
public import Arm64.Trusted.Process.Semantics
public import Arm64.Trusted.Spec.Hoare
import ProofLib.CoreLemmas
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ProcessProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Process Execution Determinism and `outcomeOf` Lemmas

**Checked by Lean.**

Establishes uniqueness and introduction rules for `ProcessRunsTo`, `ElfRunsTo`, and
`outcomeOf` from `Step` determinism: reaching a terminal `ProcessResult` implies
`ProcessSafe` (`processSafe_of_reaches`), so a single execution suffices to determine
`outcomeOf` (`outcomeOf_eq_some`, `outcomeOf_of_exits_with`). Also characterizes
`FsState.files` lookups and `setFile` updates at normalized path keys.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process

/-! ## Determinism of `Steps` -/

/-- Every `Step` starts from a `.Running` state. -/
theorem Step.status_running' {prog : Program} {s s' : State}
    (h : Step prog s s') : s.status = .Running := by
  cases h <;> assumption

/-- A state that is not `.Running` reaches only itself. -/
theorem Steps.from_not_running' {prog : Program} {s s' : State}
    (h : Steps prog s s') (hnr : s.status ≠ .Running) : s' = s := by
  cases h with
  | refl => rfl
  | step h1 _ => exact absurd (Step.status_running' h1) hnr

/-- Two runs from the same state lie on one path: one end is reachable from the other. -/
theorem Steps.deterministic_prefix' {prog : Program} {s s1 s2 : State}
    (h1 : Steps prog s s1) (h2 : Steps prog s s2) :
    Steps prog s1 s2 ∨ Steps prog s2 s1 := by
  induction h1 with
  | refl => exact Or.inl h2
  | step hs1 _ ih =>
    cases h2 with
    | refl => exact Or.inr (Steps.step hs1 ‹_›)
    | step hs2 hrest2 =>
      have heq := Step.deterministic hs1 hs2
      subst heq
      exact ih hrest2

/-! ## `ProcessResult.ofState?` -/

/-- A state with a result is not running. -/
theorem ProcessResult.ofState?_not_running {s : State} {r : ProcessResult}
    (h : ProcessResult.ofState? s = some r) : s.status ≠ .Running := by
  intro hrun
  simp [ProcessResult.ofState?, hrun] at h

/-- The result of an `.Exited code` state. -/
theorem ProcessResult.ofState?_exited {s : State} {code : BitVec 64}
    (h : s.status = .Exited code) :
    ProcessResult.ofState? s =
      some (.exited code (ProcessOutcome.traceStreamBytes .stdout s.trace) s.fs) := by
  simp [ProcessResult.ofState?, h]

/-- The result of a `.Panicked` state. -/
theorem ProcessResult.ofState?_panicked {s : State} (h : s.status = .Panicked) :
    ProcessResult.ofState? s = some .aborted := by
  simp [ProcessResult.ofState?, h]

/-! ## Uniqueness and Safety from Termination -/

/-- Two states with a result that are reachable from the same state are equal. -/
theorem Steps.eq_of_results {prog : Program} {s0 s1 s2 : State} {r1 r2 : ProcessResult}
    (h1 : Steps prog s0 s1) (hr1 : ProcessResult.ofState? s1 = some r1)
    (h2 : Steps prog s0 s2) (hr2 : ProcessResult.ofState? s2 = some r2) : s1 = s2 := by
  rcases Steps.deterministic_prefix' h1 h2 with h12 | h21
  · exact (Steps.from_not_running' h12 (ProcessResult.ofState?_not_running hr1)).symm
  · exact Steps.from_not_running' h21 (ProcessResult.ofState?_not_running hr2)

/-- Reaching a state with a `ProcessResult` implies `ProcessSafe` by `Step` determinism. -/
theorem processSafe_of_reaches {prog : Program} {s0 sf : State} {r : ProcessResult}
    (h_steps : Steps prog s0 sf) (h_res : ProcessResult.ofState? sf = some r) :
    ProcessSafe prog s0 := by
  intro s' h'
  rcases Steps.deterministic_prefix' h' h_steps with h_to | h_from
  · cases h_to with
    | refl => exact Or.inl (by rw [h_res]; rfl)
    | step hs _ => exact Or.inr ⟨Step.status_running' hs, _, hs⟩
  · have heq := Steps.from_not_running' h_from (ProcessResult.ofState?_not_running h_res)
    subst heq
    exact Or.inl (by rw [h_res]; rfl)

/-- `ProcessRunsTo` follows from a single terminating run via `processSafe_of_reaches`. -/
theorem ProcessRunsTo.of_steps {prog : Program} {s0 sf : State} {r : ProcessResult}
    (h_steps : Steps prog s0 sf) (h_res : ProcessResult.ofState? sf = some r) :
    ProcessRunsTo prog s0 r :=
  ⟨processSafe_of_reaches h_steps h_res, sf, h_steps, h_res⟩

/-- `ProcessRunsTo` has at most one result. -/
theorem ProcessRunsTo.unique {prog : Program} {s0 : State} {r1 r2 : ProcessResult}
    (h1 : ProcessRunsTo prog s0 r1) (h2 : ProcessRunsTo prog s0 r2) : r1 = r2 := by
  obtain ⟨_, s1, hs1, hr1⟩ := h1
  obtain ⟨_, s2, hs2, hr2⟩ := h2
  have heq := Steps.eq_of_results hs1 hr1 hs2 hr2
  subst heq
  rw [hr1] at hr2
  exact Option.some.inj hr2

/-- `ElfRunsTo` has at most one result. -/
theorem ElfRunsTo.unique {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {r1 r2 : ProcessResult}
    (h1 : ElfRunsTo img prog inputs r1) (h2 : ElfRunsTo img prog inputs r2) : r1 = r2 := by
  obtain ⟨s1, hl1, hp1⟩ := h1
  obtain ⟨s2, hl2, hp2⟩ := h2
  rw [hl1] at hl2
  cases hl2
  exact ProcessRunsTo.unique hp1 hp2

/-! ## `outcomeOf` Characterizations -/

/-- `outcomeOf` is `some r` exactly when the run reaches `r` safely. -/
theorem outcomeOf_eq_some_iff {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {r : ProcessResult} :
    outcomeOf img prog inputs = some r ↔ ElfRunsTo img prog inputs r := by
  unfold outcomeOf
  split
  · rename_i h
    constructor
    · intro hr
      have hc := Classical.choose_spec h
      rw [Option.some.inj hr] at hc
      exact hc
    · intro hr
      exact congrArg some (ElfRunsTo.unique (Classical.choose_spec h) hr)
  · rename_i h
    constructor
    · intro hr; cases hr
    · intro hr; exact absurd ⟨r, hr⟩ h

/-- `outcomeOf` is `none` exactly when no result is reached safely. -/
theorem outcomeOf_eq_none_iff {img : ElfImage} {prog : Program} {inputs : ProcessInputs} :
    outcomeOf img prog inputs = none ↔ ¬ ∃ r, ElfRunsTo img prog inputs r := by
  unfold outcomeOf
  split
  · rename_i h
    exact ⟨(fun hr => by cases hr), fun hn => absurd h hn⟩
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- If `loadState` succeeds and `Steps` reaches a state with result `r`, then `outcomeOf` is `some r`. -/
theorem outcomeOf_eq_some {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {s0 sf : State} {r : ProcessResult}
    (h_load : img.loadState inputs = .ok s0)
    (h_steps : Steps prog s0 sf)
    (h_res : ProcessResult.ofState? sf = some r) :
    outcomeOf img prog inputs = some r :=
  outcomeOf_eq_some_iff.mpr ⟨s0, h_load, ProcessRunsTo.of_steps h_steps h_res⟩

/-- `outcomeOf_eq_some` for a run that exits with `code`. -/
theorem outcomeOf_eq_exited {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {s0 sf : State} {code : BitVec 64}
    (h_load : img.loadState inputs = .ok s0)
    (h_steps : Steps prog s0 sf)
    (h_status : sf.status = .Exited code) :
    outcomeOf img prog inputs =
      some (.exited code (ProcessOutcome.traceStreamBytes .stdout sf.trace) sf.fs) :=
  outcomeOf_eq_some h_load h_steps (ProcessResult.ofState?_exited h_status)

/-- `outcomeOf_eq_some` for a run that panics. -/
theorem outcomeOf_eq_aborted {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {s0 sf : State}
    (h_load : img.loadState inputs = .ok s0)
    (h_steps : Steps prog s0 sf)
    (h_status : sf.status = .Panicked) :
    outcomeOf img prog inputs = some .aborted :=
  outcomeOf_eq_some h_load h_steps (ProcessResult.ofState?_panicked h_status)

/-- A run that reaches a state with no result that is not running (`.Halted`, `.OutOfMemory`,
    `.Exception`) has no outcome. -/
theorem outcomeOf_eq_none_of_stuck {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {s0 sf : State}
    (h_load : img.loadState inputs = .ok s0)
    (h_steps : Steps prog s0 sf)
    (h_none : ProcessResult.ofState? sf = none)
    (h_stop : sf.status ≠ .Running) :
    outcomeOf img prog inputs = none := by
  refine outcomeOf_eq_none_iff.mpr ?_
  rintro ⟨r, s0', h_load', h_safe, _⟩
  rw [h_load] at h_load'
  cases h_load'
  rcases h_safe sf h_steps with h | ⟨h, _⟩
  · rw [h_none] at h; cases h
  · exact h_stop h

/-- Loading failure gives no outcome. -/
theorem outcomeOf_eq_none_of_load_error {img : ElfImage} {prog : Program}
    {inputs : ProcessInputs} {e : String}
    (h_load : img.loadState inputs = .error e) :
    outcomeOf img prog inputs = none := by
  refine outcomeOf_eq_none_iff.mpr ?_
  rintro ⟨r, s0, h_load', _⟩
  rw [h_load] at h_load'
  cases h_load'

/-- From a Hoare `exits_with` contract (no out-of-memory case) on the loaded state: the outcome
    is `exited code` with the stdout and file system of some final state satisfying `post`. -/
theorem outcomeOf_of_exits_with {img : ElfImage} {prog : Program} {inputs : ProcessInputs}
    {s0 : State} {code : BitVec 64} {post : State → Prop}
    (h_load : img.loadState inputs = .ok s0)
    (h_code_loaded : prog.CodeLoaded s0.mem)
    (h_exits : exits_with prog code s0 post) :
    ∃ sf, post sf ∧ outcomeOf img prog inputs =
      some (.exited code (ProcessOutcome.traceStreamBytes .stdout sf.trace) sf.fs) := by
  obtain ⟨sf, h_steps, h⟩ := h_exits h_code_loaded
  rcases h with ⟨h_status, h_post⟩ | ⟨_, h_oom⟩
  · exact ⟨sf, h_post, outcomeOf_eq_exited h_load h_steps h_status⟩
  · exact h_oom.elim

/-! ## `ProcessExitsWith` and `loadState` Helpers -/

/-- Every state loaded by `ElfImage.loadState` starts in `.Running` status. -/
theorem loadState_status_running {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : elf.loadState inputs = .ok s0) : s0.status = .Running := by
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  cases hw : elf.WellFormed
  · rw [hw] at h; cases h
  · rw [hw] at h
    cases hd : (inputs.dirs.any fun d => hasLeadingSlash d || hasDotDot d)
    · rw [hd] at h
      cases hf : (inputs.files.any fun (p, bs) => hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE))
      · rw [hf] at h
        cases hb : buildInitialStack elf inputs <;> rw [hb] at h <;> cases h
        rfl
      · rw [hf] at h; cases h
    · rw [hd] at h; cases h

/-- Construct `ProcessExitsWith` from a reachable `.Exited code` state. -/
theorem processExitsWith_of_exited {prog : Program} {s0 sf : State} {code : BitVec 64}
    (h_steps : Steps prog s0 sf) (h_status : sf.status = .Exited code) :
    ProcessExitsWith prog s0 (ProcessOutcome.ofState code sf) :=
  ⟨sf, h_steps, Or.inl ⟨code, h_status, rfl⟩⟩

/-- Construct `ProcessExitsWith` from a reachable `.Signaled sig` state. -/
theorem processExitsWith_of_signaled {prog : Program} {s0 sf : State} {sig : BitVec 7}
    (h_steps : Steps prog s0 sf) (h_status : sf.status = .Signaled sig) :
    ProcessExitsWith prog s0 (ProcessOutcome.ofSignal sig sf) :=
  ⟨sf, h_steps, Or.inr ⟨sig, h_status, rfl⟩⟩

/-! ## File-System Lookups -/

/-- `FsState.files` reads the canonical key: the working directory (`[]`) is always a directory,
    any other key is the entry stored there. -/
theorem files_eq_entries (fs : FsState) (q : String) :
    fs.files q = if (normalizePath q).isEmpty then some .dir else fs.entries (normalizePath q) := rfl

/-- `setFile p e` updates `files q` iff `normalizePath q = normalizePath p` and `normalizePath q` is nonempty. -/
theorem files_setFile (fs : FsState) (p : String) (e : Option FsEntry) (q : String) :
    (fs.setFile p e).files q =
      if (normalizePath q).isEmpty then some .dir
      else if normalizePath q = normalizePath p then e else fs.files q := by
  simp only [FsState.files, FsState.setFile, FsState.getEntry, FsState.setEntry]
  split <;> simp_all

end CryptoVerification.SignalSession
