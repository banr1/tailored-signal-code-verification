/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process.Assumptions
public import ProofLib.Process.ByteArray
public import ProofLib.Exec
public import ProofLib.Simulation
public import ProofLib.Invariant
public import ProofLib.SepLogic.Defs
public import ProofLib.Hoare.SubroutineOk
import Arm64.Trusted.Spec.SepLogic
import Arm64.Trusted.Spec.Hoare

/-!
# Whole-Binary ELF Process Execution, Determinism, and Loader Bridges

Provides fuel-bounded ELF64 process runners (`runSteps`, `runElfImage`, `runStepsPure`,
`runElfImagePure`), determinism-based constructors for `ProcessRunsTo`, `ElfRunsTo`,
`ElfCorrect`, and `ElfSafe`, segment-to-memory ownership bridges for `ElfImage.loadState`,
and fail-closed syscall-handler monotonicity (`SvcRefines`, `ElfRunsTo.mono_svc`).
-/

@[expose] public section

namespace Arm64.Process

open ProofLib

/-! ## Executable Process Runners -/

/-- Execute up to `fuel` small-step transitions of `prog` from `s`, stopping as soon as
    `s.status != .Running`. -/
def runSteps : Nat → Program → State → State
  | 0, _, s => s
  | n + 1, prog, s =>
    if s.status != .Running then
      s
    else
      match stepState prog s with
      | some s' => runSteps n prog s'
      | none    => s

/-- `runSteps n Program.pureMem` specialised to executable evaluation (`runStepsPure_eq`): steps
    with `execInst` instead of `Program.pureMem.evalInst`. `evalSvc` rebuilds `mem` after every
    `SVC #0` as a closure reading both the pre- and post-syscall memory, so each syscall doubles
    the cost of every later read of an older byte under `runSteps`; `execInst` (equal by
    `evalInst_pureMem`) adds no such layer. Use this in executable reference runs. -/
def runStepsPure : Nat → State → State
  | 0, s => s
  | n + 1, s =>
    if s.status != .Running then
      s
    else
      match Program.pureMem.fetchMem s.mem s.pc with
      | some inst => runStepsPure n (execInst inst s)
      | none      => runStepsPure n { s with status := .Halted }

/-- Load `img` with `inputs` and execute up to `fuel` steps under `prog`, returning the final
    `State` and, if it terminated via `.Exited` or `.Signaled`, its `ProcessOutcome`. -/
def runElfImage (fuel : Nat) (img : ElfImage) (inputs : ProcessInputs := {})
    (prog : Program := Program.pureMem) : Except String (State × Option ProcessOutcome) := do
  let s0 ← img.loadState inputs
  let sf := runSteps fuel prog s0
  pure (sf, ProcessOutcome.ofTerminated? sf)

/-- Parse `elfBytes` (`List (BitVec 8)`), load with `inputs`, and execute up to `fuel` steps. -/
def runElf (fuel : Nat) (elfBytes : List (BitVec 8)) (inputs : ProcessInputs := {})
    (prog : Program := Program.pureMem) : Except String (State × Option ProcessOutcome) := do
  let img ← ElfImage.parse elfBytes
  runElfImage fuel img inputs prog

/-- Parse `elfBytes` (`ByteArray`), load with `inputs`, and execute up to `fuel` steps. -/
def runElfByteArray (fuel : Nat) (elfBytes : ByteArray) (inputs : ProcessInputs := {})
    (prog : Program := Program.pureMem) : Except String (State × Option ProcessOutcome) := do
  let img ← ElfImage.parseByteArray elfBytes
  runElfImage fuel img inputs prog

/-- `runElfImage fuel img inputs Program.pureMem` via `runStepsPure` (`runElfImagePure_eq`):
    the executable reference runner for tests. -/
def runElfImagePure (fuel : Nat) (img : ElfImage) (inputs : ProcessInputs := {}) :
    Except String (State × Option ProcessOutcome) := do
  let s0 ← img.loadState inputs
  let sf := runStepsPure fuel s0
  pure (sf, ProcessOutcome.ofTerminated? sf)

/-- `runElfByteArray fuel elfBytes inputs Program.pureMem` via `runStepsPure`. -/
def runElfByteArrayPure (fuel : Nat) (elfBytes : ByteArray) (inputs : ProcessInputs := {}) :
    Except String (State × Option ProcessOutcome) := do
  let img ← ElfImage.parseByteArray elfBytes
  runElfImagePure fuel img inputs

/-! ## Soundness of `runSteps` and Determinism of `Step` and `Steps` -/

/-- `Program.pureMem` has no extern or override hooks, so `HooksKeepFrozen` holds trivially. -/
theorem pureMem_hooksKeepFrozen : Program.pureMem.HooksKeepFrozen := by
  intro _ _ _ h_ext
  nomatch h_ext

/-- Every `runSteps` execution is a valid `Steps` trace when `prog.HooksKeepFrozen` holds. -/
theorem runSteps_steps {prog : Program} (h_hooks : prog.HooksKeepFrozen)
    (n : Nat) (s : State) :
    Steps prog s (runSteps n prog s) := by
  induction n generalizing s with
  | zero => exact Steps.refl s
  | succ n ih =>
    unfold runSteps
    split
    · exact Steps.refl s
    · split
      · rename_i s' h_step
        exact Steps.step (stepState_sound h_hooks h_step) (ih s')
      · exact Steps.refl s

/-- The executable `runStepsPure` agrees with `runSteps · Program.pureMem`. -/
theorem runStepsPure_eq (n : Nat) (s : State) :
    runStepsPure n s = runSteps n Program.pureMem s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold runStepsPure runSteps
    split
    · rfl
    · rename_i hrun
      have hext : Program.pureMem.externAt? s.pc = none := by
        simp [Program.externAt?, Program.hookAtOff?, Program.pureWithSvc, Program.ofSvc]
      revert hrun
      cases hst : s.status <;> intro hrun <;> try exact absurd rfl hrun
      split <;> rename_i h <;>
        simp [stepState, hst, hext, h, evalInst_pureMem, ih]

/-- `runElfImagePure` agrees with `runElfImage · · · Program.pureMem`. -/
theorem runElfImagePure_eq (fuel : Nat) (img : ElfImage) (inputs : ProcessInputs) :
    runElfImagePure fuel img inputs = runElfImage fuel img inputs Program.pureMem := by
  simp only [runElfImagePure, runElfImage, runStepsPure_eq]

/-- `runElfByteArrayPure` agrees with `runElfByteArray · · · Program.pureMem`. -/
theorem runElfByteArrayPure_eq (fuel : Nat) (elfBytes : ByteArray) (inputs : ProcessInputs) :
    runElfByteArrayPure fuel elfBytes inputs = runElfByteArray fuel elfBytes inputs Program.pureMem := by
  simp only [runElfByteArrayPure, runElfByteArray, runElfImagePure_eq]

/-- A state whose status is not `.Running` has no non-trivial outgoing `Steps`. -/
theorem _root_.Arm64.Steps.from_not_running {prog : Program} {s s' : State}
    (h : Steps prog s s') (hnr : s.status ≠ .Running) : s' = s := by
  cases h with
  | refl => rfl
  | step h1 _ => exact absurd h1.status_running hnr

/-- Because `Step` is deterministic (`Step.deterministic`), any two `Steps` traces from the same
    start state `s` lie on a single linear path: one endpoint is reachable from the other. -/
theorem _root_.Arm64.Steps.deterministic_prefix {prog : Program} {s s1 s2 : State}
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

/-! ## Per-Image Judgments and Process Safety from Deterministic Termination -/

/-- Per-image judgment for `ElfRunsTo`: loading the parsed image `img` with `inputs` succeeds
    and the run of `prog` satisfies `ProcessRunsTo` (`ElfRunsTo.intro`, `ElfRunsTo.image`). -/
def ElfImageRunsTo (img : ElfImage) (inputs : ProcessInputs)
    (post : ProcessOutcome → Prop)
    (oom : State → Prop := fun _ => False)
    (prog : Program := Program.pureMem) : Prop :=
  ∃ s0, img.loadState inputs = .ok s0 ∧ ProcessRunsTo prog s0 post oom

/-- Per-image judgment for `ElfCorrect`: `ElfImageRunsTo` with exit status `0`, no signal,
    `post`, and no OOM. -/
abbrev ElfImageCorrect (img : ElfImage) (inputs : ProcessInputs)
    (post : ProcessOutcome → Prop)
    (prog : Program := Program.pureMem) : Prop :=
  ElfImageRunsTo img inputs (fun out => out.exitCode = 0#64 ∧ out.signal = none ∧ post out)
    (fun _ => False) prog

/-- Per-image judgment for `ElfSafe`: `ElfImageCorrect` with a trivial postcondition. -/
abbrev ElfImageSafe (img : ElfImage) (inputs : ProcessInputs := {})
    (prog : Program := Program.pureMem) : Prop :=
  ElfImageCorrect img inputs (fun _ => True) prog

/-- A signal-terminated `ProcessOutcome.ofSignal sig sf` reports status `128 + sig.toNat` with
    `sig : BitVec 7` (`0 ≤ sig.toNat < 128`), so its `exitCode` never wraps to `0#64`. -/
theorem ProcessOutcome.ofSignal_exitCode_ne_zero (sig : BitVec 7) (sf : State) :
    (ProcessOutcome.ofSignal sig sf).exitCode ≠ 0#64 := by
  intro h
  have h1 := congrArg BitVec.toNat h
  have hlt : sig.toNat < 128 := sig.isLt
  simp [ProcessOutcome.ofSignal] at h1
  omega

/-- Every `ProcessTerminatedOutcome sf out` implies `sf.status ≠ .Running`. -/
theorem ProcessTerminatedOutcome.not_running {sf : State} {out : ProcessOutcome}
    (h : ProcessTerminatedOutcome sf out) : sf.status ≠ .Running := by
  rcases h with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] <;> intro hr <;> cases hr

/-- A terminated outcome with `exitCode = 0#64` is a normal exit (`signal = none`). -/
theorem ProcessExitsWith.signal_eq_none_of_code {prog : Program} {s0 : State}
    {out : ProcessOutcome} (h_exit : ProcessExitsWith prog s0 out) (h_code : out.exitCode = 0#64) :
    out.signal = none := by
  obtain ⟨sf, _, h_term⟩ := h_exit
  rcases h_term with ⟨_, _, rfl⟩ | ⟨sig, _, rfl⟩
  · rfl
  · exact absurd h_code (ProcessOutcome.ofSignal_exitCode_ne_zero sig sf)

/-- If `s0` terminates cleanly or by fatal signal with `ProcessExitsWith prog s0 out` and
    `post out`, then by determinism of `Step` `ProcessRunsTo prog s0 post oom` holds. -/
theorem ProcessRunsTo.of_exitsWith {prog : Program} {s0 : State} {out : ProcessOutcome}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    (h_exit : ProcessExitsWith prog s0 out)
    (h_post : post out) :
    ProcessRunsTo prog s0 post oom := by
  refine ⟨Or.inl ⟨out, h_exit, h_post⟩, ?_⟩
  obtain ⟨sf, h_steps_sf, h_term⟩ := h_exit
  intro s' h_steps_s'
  have h_not_run : sf.status ≠ .Running := h_term.not_running
  rcases Steps.deterministic_prefix h_steps_s' h_steps_sf with h_to_sf | h_from_sf
  · cases h_to_sf with
    | refl =>
      exact Or.inl ⟨out, h_term, h_post⟩
    | step hs _ =>
      exact Or.inr (Or.inr ⟨hs.status_running, _, hs⟩)
  · have heq := Steps.from_not_running h_from_sf h_not_run
    subst heq
    exact Or.inl ⟨out, h_term, h_post⟩

/-- If `s0` stops in `.OutOfMemory` at `sf` with `oom sf`, then by determinism of `Step`
    `ProcessRunsTo prog s0 post oom` holds. -/
theorem ProcessRunsTo.of_oom {prog : Program} {s0 sf : State}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    (h_steps_sf : Steps prog s0 sf)
    (h_oom_status : sf.status = .OutOfMemory)
    (h_oom : oom sf) :
    ProcessRunsTo prog s0 post oom := by
  refine ⟨Or.inr ⟨sf, h_steps_sf, h_oom_status, h_oom⟩, ?_⟩
  intro s' h_steps_s'
  have h_not_run : sf.status ≠ .Running := by
    rw [h_oom_status]
    intro h; cases h
  rcases Steps.deterministic_prefix h_steps_s' h_steps_sf with h_to_sf | h_from_sf
  · cases h_to_sf with
    | refl =>
      right; left
      exact ⟨h_oom_status, h_oom⟩
    | step hs _ =>
      right; right
      exact ⟨hs.status_running, _, hs⟩
  · have heq := Steps.from_not_running h_from_sf h_not_run
    subst heq
    right; left
    exact ⟨h_oom_status, h_oom⟩

/-- Prove `ElfImageRunsTo` from a clean `ProcessExitsWith` termination witness. -/
theorem ElfImageRunsTo.of_exitsWith {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    {prog : Program} {s0 : State} {out : ProcessOutcome}
    (h_load : img.loadState inputs = .ok s0)
    (h_exit : ProcessExitsWith prog s0 out)
    (h_post : post out) :
    ElfImageRunsTo img inputs post oom prog :=
  ⟨s0, h_load, ProcessRunsTo.of_exitsWith h_exit h_post⟩

/-- Prove `ElfImageRunsTo` from an `.OutOfMemory` stop witness. -/
theorem ElfImageRunsTo.of_oom {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    {prog : Program} {s0 sf : State}
    (h_load : img.loadState inputs = .ok s0)
    (h_steps : Steps prog s0 sf)
    (h_oom_status : sf.status = .OutOfMemory)
    (h_oom : oom sf) :
    ElfImageRunsTo img inputs post oom prog :=
  ⟨s0, h_load, ProcessRunsTo.of_oom h_steps h_oom_status h_oom⟩

/-- Prove `ElfImageCorrect` from `img.loadState inputs = .ok s0` and `ProcessExitsWith prog s0 out`
    with `out.exitCode = 0#64` and `post out`. -/
theorem ElfImageCorrect.of_exitsWith {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {prog : Program} {s0 : State} {out : ProcessOutcome}
    (h_load : img.loadState inputs = .ok s0)
    (h_exit : ProcessExitsWith prog s0 out)
    (h_code : out.exitCode = 0#64)
    (h_post : post out) :
    ElfImageCorrect img inputs post prog :=
  ElfImageRunsTo.of_exitsWith h_load h_exit
    ⟨h_code, h_exit.signal_eq_none_of_code h_code, h_post⟩

/-- Prove `ElfImageSafe` from `img.loadState inputs = .ok s0` and `ProcessExitsWith prog s0 out`
    with `out.exitCode = 0#64`. -/
theorem ElfImageSafe.of_exitsWith {img : ElfImage} {inputs : ProcessInputs}
    {prog : Program} {s0 : State} {out : ProcessOutcome}
    (h_load : img.loadState inputs = .ok s0)
    (h_exit : ProcessExitsWith prog s0 out)
    (h_code : out.exitCode = 0#64) :
    ElfImageSafe img inputs prog :=
  ElfImageCorrect.of_exitsWith h_load h_exit h_code trivial

/-- Prove `ElfImageRunsTo` for any exit code `code` by bounded execution (`runSteps`). -/
theorem ElfImageRunsTo.of_runSteps {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    {s0 : State} (fuel : Nat) (code : BitVec 64)
    (h_load : img.loadState inputs = .ok s0)
    (h_exit : (runSteps fuel Program.pureMem s0).status = .Exited code)
    (h_post : post (ProcessOutcome.ofState code (runSteps fuel Program.pureMem s0))) :
    ElfImageRunsTo img inputs post oom Program.pureMem := by
  let sf := runSteps fuel Program.pureMem s0
  let out := ProcessOutcome.ofState code sf
  have h_steps : Steps Program.pureMem s0 sf := runSteps_steps pureMem_hooksKeepFrozen fuel s0
  have h_pe : ProcessExitsWith Program.pureMem s0 out := ⟨sf, h_steps, Or.inl ⟨code, h_exit, rfl⟩⟩
  exact ElfImageRunsTo.of_exitsWith h_load h_pe h_post

/-- Prove `ElfImageRunsTo` for a fatal signal `sig` (such as `SIGABRT = 6#7` -> exit status `134`)
    by bounded execution (`runSteps`). -/
theorem ElfImageRunsTo.of_runSteps_signaled {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    {s0 : State} (fuel : Nat) (sig : BitVec 7)
    (h_load : img.loadState inputs = .ok s0)
    (h_sig : (runSteps fuel Program.pureMem s0).status = .Signaled sig)
    (h_post : post (ProcessOutcome.ofSignal sig (runSteps fuel Program.pureMem s0))) :
    ElfImageRunsTo img inputs post oom Program.pureMem := by
  let sf := runSteps fuel Program.pureMem s0
  let out := ProcessOutcome.ofSignal sig sf
  have h_steps : Steps Program.pureMem s0 sf := runSteps_steps pureMem_hooksKeepFrozen fuel s0
  have h_pe : ProcessExitsWith Program.pureMem s0 out := ⟨sf, h_steps, Or.inr ⟨sig, h_sig, rfl⟩⟩
  exact ElfImageRunsTo.of_exitsWith h_load h_pe h_post

/-- Prove `ElfImageCorrect` by bounded execution (`runSteps fuel Program.pureMem s0`). -/
theorem ElfImageCorrect.of_runSteps {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {s0 : State} (fuel : Nat)
    (h_load : img.loadState inputs = .ok s0)
    (h_exit : (runSteps fuel Program.pureMem s0).status = .Exited 0#64)
    (h_post : post (ProcessOutcome.ofState 0#64 (runSteps fuel Program.pureMem s0))) :
    ElfImageCorrect img inputs post Program.pureMem :=
  ElfImageRunsTo.of_runSteps fuel 0#64 h_load h_exit ⟨rfl, rfl, h_post⟩

/-- Prove `ElfImageSafe` by bounded execution (`runSteps fuel Program.pureMem s0`). -/
theorem ElfImageSafe.of_runSteps {img : ElfImage} {inputs : ProcessInputs}
    {s0 : State} (fuel : Nat)
    (h_load : img.loadState inputs = .ok s0)
    (h_exit : (runSteps fuel Program.pureMem s0).status = .Exited 0#64) :
    ElfImageSafe img inputs Program.pureMem :=
  ElfImageCorrect.of_runSteps fuel h_load h_exit trivial

/-- Lift `Arm64.exits_with` (with arbitrary `code` and `oom`) directly to `ElfImageRunsTo`. -/
theorem ElfImageRunsTo.of_hoare_exits_with {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    {prog : Program} {s0 : State} {code : BitVec 64}
    (h_load : img.loadState inputs = .ok s0)
    (h_code_loaded : prog.CodeLoaded s0.mem)
    (h_exits : exits_with prog code s0
      (fun sf => post (ProcessOutcome.ofState code sf)) oom) :
    ElfImageRunsTo img inputs post oom prog := by
  obtain ⟨sf, h_steps, h_out⟩ := h_exits h_code_loaded
  rcases h_out with ⟨h_status, h_post⟩ | ⟨h_oom_status, h_oom⟩
  · have h_pe : ProcessExitsWith prog s0 (ProcessOutcome.ofState code sf) :=
      ⟨sf, h_steps, Or.inl ⟨code, h_status, rfl⟩⟩
    exact ElfImageRunsTo.of_exitsWith h_load h_pe h_post
  · exact ElfImageRunsTo.of_oom h_load h_steps h_oom_status h_oom

/-- Lift `Arm64.exits_with` (without OOM, `oom := fun _ => False`) to `ElfImageCorrect`. -/
theorem ElfImageCorrect.of_hoare_exits_with {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {prog : Program} {s0 : State}
    (h_load : img.loadState inputs = .ok s0)
    (h_code_loaded : prog.CodeLoaded s0.mem)
    (h_exits : exits_with prog 0#64 s0 (fun sf => post (ProcessOutcome.ofState 0#64 sf))) :
    ElfImageCorrect img inputs post prog := by
  obtain ⟨sf, h_steps, h_out⟩ := h_exits h_code_loaded
  rcases h_out with ⟨h_status, h_post⟩ | ⟨_, h_oom⟩
  · have h_pe : ProcessExitsWith prog s0 (ProcessOutcome.ofState 0#64 sf) :=
      ⟨sf, h_steps, Or.inl ⟨0#64, h_status, rfl⟩⟩
    exact ElfImageCorrect.of_exitsWith h_load h_pe rfl h_post
  · exact False.elim h_oom

/-- Lift `Arm64.exits_with` (without OOM) to `ElfImageSafe`. -/
theorem ElfImageSafe.of_hoare_exits_with {img : ElfImage} {inputs : ProcessInputs}
    {prog : Program} {s0 : State}
    (h_load : img.loadState inputs = .ok s0)
    (h_code_loaded : prog.CodeLoaded s0.mem)
    (h_exits : exits_with prog 0#64 s0 (fun _ => True)) :
    ElfImageSafe img inputs prog :=
  ElfImageCorrect.of_hoare_exits_with (post := fun _ => True) h_load h_code_loaded h_exits

/-- Rewrite `loadElf elfBytes inputs` to `img.loadState inputs` using `ElfImage.parse elfBytes = .ok img`. -/
theorem loadElf_eq_of_parse {elfBytes : List (BitVec 8)} {img : ElfImage} {inputs : ProcessInputs}
    (h_parse : ElfImage.parse elfBytes = .ok img) :
    loadElf elfBytes inputs = img.loadState inputs := by
  unfold loadElf
  rw [h_parse]
  rfl

/-! ## Whole-Binary Constructors and Eliminators -/

/-- Prove `ElfRunsTo` from the parse result and a per-input `ElfImageRunsTo` proof. -/
theorem ElfRunsTo.intro {elfBytes : List (BitVec 8)} {img : ElfImage}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {oom : ProcessInputs → State → Prop} {prog : Program}
    (h_parse : ElfImage.parse elfBytes = .ok img)
    (h : ∀ inputs, pre inputs → ElfImageRunsTo img inputs (post inputs) (oom inputs) prog) :
    ElfRunsTo elfBytes pre post oom prog :=
  ⟨img, h_parse, h⟩

/-- Prove `ElfCorrect` from the parse result and a per-input `ElfImageCorrect` proof. -/
theorem ElfCorrect.intro {elfBytes : List (BitVec 8)} {img : ElfImage}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {prog : Program} {minPhysMem : ProcessInputs → Nat}
    (h_parse : ElfImage.parse elfBytes = .ok img)
    (h : ∀ inputs, inputs.init.physMemAvail ≥ minPhysMem inputs → pre inputs →
      ElfImageCorrect img inputs (post inputs) prog) :
    ElfCorrect elfBytes pre post prog minPhysMem :=
  ElfRunsTo.intro h_parse (fun inputs ⟨hphys, hpre⟩ => h inputs hphys hpre)

/-- Prove `ElfSafe` from the parse result and a per-input `ElfImageSafe` proof. -/
theorem ElfSafe.intro {elfBytes : List (BitVec 8)} {img : ElfImage}
    {pre : ProcessInputs → Prop} {prog : Program} {minPhysMem : ProcessInputs → Nat}
    (h_parse : ElfImage.parse elfBytes = .ok img)
    (h : ∀ inputs, inputs.init.physMemAvail ≥ minPhysMem inputs → pre inputs →
      ElfImageSafe img inputs prog) :
    ElfSafe elfBytes pre prog minPhysMem :=
  ElfRunsTo.intro h_parse (fun inputs ⟨hphys, hpre⟩ => h inputs hphys hpre)

/-- Instantiate `ElfRunsTo` at one input satisfying `pre`, given the parse result. -/
theorem ElfRunsTo.image {elfBytes : List (BitVec 8)} {img : ElfImage}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {oom : ProcessInputs → State → Prop} {prog : Program} {inputs : ProcessInputs}
    (h : ElfRunsTo elfBytes pre post oom prog)
    (h_parse : ElfImage.parse elfBytes = .ok img) (h_pre : pre inputs) :
    ElfImageRunsTo img inputs (post inputs) (oom inputs) prog := by
  obtain ⟨img', h_parse', h⟩ := h
  rw [h_parse] at h_parse'
  cases h_parse'
  exact h inputs h_pre

/-- `ProcessRunsTo` is monotone in the postcondition and OOM predicate. -/
theorem ProcessRunsTo.mono {prog : Program} {s0 : State}
    {post post' : ProcessOutcome → Prop} {oom oom' : State → Prop}
    (h : ProcessRunsTo prog s0 post oom)
    (h_post : ∀ out, post out → post' out) (h_oom : ∀ s, oom s → oom' s) :
    ProcessRunsTo prog s0 post' oom' := by
  obtain ⟨h_term, h_safe⟩ := h
  refine ⟨?_, fun s' hs' => ?_⟩
  · rcases h_term with ⟨out, he, hp⟩ | ⟨sf, hs, hst, ho⟩
    · exact Or.inl ⟨out, he, h_post out hp⟩
    · exact Or.inr ⟨sf, hs, hst, h_oom sf ho⟩
  · rcases h_safe s' hs' with ⟨out, ht, hp⟩ | ⟨hst, ho⟩ | hr
    · exact Or.inl ⟨out, ht, h_post out hp⟩
    · exact Or.inr (Or.inl ⟨hst, h_oom s' ho⟩)
    · exact Or.inr (Or.inr hr)

/-- `ElfRunsTo` is monotone in the precondition, postcondition, and OOM predicate. -/
theorem ElfRunsTo.mono {elfBytes : List (BitVec 8)}
    {pre pre' : ProcessInputs → Prop} {post post' : ProcessInputs → ProcessOutcome → Prop}
    {oom oom' : ProcessInputs → State → Prop} {prog : Program}
    (h : ElfRunsTo elfBytes pre post oom prog)
    (h_pre : ∀ inputs, pre' inputs → pre inputs)
    (h_post : ∀ inputs out, pre' inputs → post inputs out → post' inputs out)
    (h_oom : ∀ inputs s, pre' inputs → oom inputs s → oom' inputs s) :
    ElfRunsTo elfBytes pre' post' oom' prog := by
  obtain ⟨img, h_parse, h⟩ := h
  refine ⟨img, h_parse, fun inputs hi => ?_⟩
  obtain ⟨s0, h_load, h_run⟩ := h inputs (h_pre inputs hi)
  exact ⟨s0, h_load, h_run.mono (fun out => h_post inputs out hi) (fun s => h_oom inputs s hi)⟩

/-- Functional correctness implies safety (`ElfCorrect` implies `ElfSafe`). -/
theorem ElfCorrect.safe {elfBytes : List (BitVec 8)} {pre : ProcessInputs → Prop}
    {post : ProcessInputs → ProcessOutcome → Prop} {prog : Program}
    {minPhysMem : ProcessInputs → Nat}
    (h : ElfCorrect elfBytes pre post prog minPhysMem) :
    ElfSafe elfBytes pre prog minPhysMem :=
  ElfRunsTo.mono h (fun _ h => h) (fun _ _ _ ⟨h1, h2, _⟩ => ⟨h1, h2, trivial⟩)
    (fun _ _ _ h => h)

/-! ## Partial Correctness -/

/-- Total correctness implies partial correctness (`ProcessRunsTo` implies `ProcessPartialRunsTo`). -/
theorem ProcessRunsTo.toPartial {prog : Program} {s0 : State}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    (h : ProcessRunsTo prog s0 post oom) :
    ProcessPartialRunsTo prog s0 post oom :=
  h.2

/-- Prove `ProcessPartialRunsTo` from an invariant `inv` that holds initially, is preserved by
    every `Step prog`, and implies the per-state safety disjunction. -/
theorem ProcessPartialRunsTo.of_invariant {prog : Program} {s0 : State}
    {post : ProcessOutcome → Prop} {oom : State → Prop} (inv : State → Prop)
    (h_init : inv s0)
    (h_step : ∀ s s', inv s → Step prog s s' → inv s')
    (h_safe : ∀ s, inv s →
      (∃ out, ProcessTerminatedOutcome s out ∧ post out) ∨
      (s.status = .OutOfMemory ∧ oom s) ∨
      (s.status = .Running ∧ ∃ s'', Step prog s s'')) :
    ProcessPartialRunsTo prog s0 post oom := by
  intro s' hs
  induction hs with
  | refl s => exact h_safe s h_init
  | step h1 _ ih => exact ih (h_step _ _ h_init h1)

/-- Whole-binary total correctness implies partial correctness (`ElfRunsTo` implies
    `ElfPartialRunsTo`). -/
theorem ElfRunsTo.toPartial {elfBytes : List (BitVec 8)}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {oom : ProcessInputs → State → Prop} {prog : Program}
    (h : ElfRunsTo elfBytes pre post oom prog) :
    ElfPartialRunsTo elfBytes pre post oom prog := by
  obtain ⟨img, h_parse, h⟩ := h
  refine ⟨img, h_parse, fun inputs hi => ?_⟩
  obtain ⟨s0, h_load, h_run⟩ := h inputs hi
  exact ⟨s0, h_load, h_run.toPartial⟩

/-- `ProcessPartialRunsTo` is monotone in the postcondition and OOM predicate. -/
theorem ProcessPartialRunsTo.mono {prog : Program} {s0 : State}
    {post post' : ProcessOutcome → Prop} {oom oom' : State → Prop}
    (h : ProcessPartialRunsTo prog s0 post oom)
    (h_post : ∀ out, post out → post' out) (h_oom : ∀ s, oom s → oom' s) :
    ProcessPartialRunsTo prog s0 post' oom' := fun s' hs' => by
  rcases h s' hs' with ⟨out, ht, hp⟩ | ⟨hst, ho⟩ | hr
  · exact Or.inl ⟨out, ht, h_post out hp⟩
  · exact Or.inr (Or.inl ⟨hst, h_oom s' ho⟩)
  · exact Or.inr (Or.inr hr)

/-- `ElfPartialRunsTo` is monotone in the precondition, postcondition, and OOM predicate. -/
theorem ElfPartialRunsTo.mono {elfBytes : List (BitVec 8)}
    {pre pre' : ProcessInputs → Prop} {post post' : ProcessInputs → ProcessOutcome → Prop}
    {oom oom' : ProcessInputs → State → Prop} {prog : Program}
    (h : ElfPartialRunsTo elfBytes pre post oom prog)
    (h_pre : ∀ inputs, pre' inputs → pre inputs)
    (h_post : ∀ inputs out, pre' inputs → post inputs out → post' inputs out)
    (h_oom : ∀ inputs s, pre' inputs → oom inputs s → oom' inputs s) :
    ElfPartialRunsTo elfBytes pre' post' oom' prog := by
  obtain ⟨img, h_parse, h⟩ := h
  refine ⟨img, h_parse, fun inputs hi => ?_⟩
  obtain ⟨s0, h_load, h_run⟩ := h inputs (h_pre inputs hi)
  exact ⟨s0, h_load, h_run.mono (fun out => h_post inputs out hi) (fun s => h_oom inputs s hi)⟩

/-! ## Segment and `Obj.Image` Memory Bridge for `ElfImage.loadState` -/

end Arm64.Process

namespace Arm64.Snapshot

/-- Region `q` lies entirely at or below address `a` (and does not wrap past `2 ^ 64`). -/
def Below (a : BitVec 64) (q : Region) : Bool :=
  decide (q.start.toNat + q.bytes.length ≤ a.toNat)

/-- A region below `r.start` has no cell at `r.start + j` for `j` inside `r`. -/
theorem cellAt_below_none {q r : Region} {j : Nat} (hq : Below r.start q = true)
    (hj : j < r.bytes.length) (hwrap : r.start.toNat + r.bytes.length ≤ 2 ^ 64) :
    cellAt [q] (r.start + BitVec.ofNat 64 j) = none := by
  simp only [Below, decide_eq_true_eq] at hq
  simp only [cellAt, List.findSome?_cons, List.findSome?_nil]
  have hlt : ¬ (r.start + BitVec.ofNat 64 j - q.start).toNat < q.bytes.length := by
    have : (r.start + BitVec.ofNat 64 j - q.start).toNat = r.start.toNat + j - q.start.toNat := by
      bv_omega
    omega
  simp only [hlt, ↓reduceDIte]

/-- The cell at `r.start + j` of a region list `pre ++ r :: post` comes from `r`, when every
    region of `pre` is below `r.start`. -/
theorem cellAt_of_split {pre post : List Region} {r : Region} {j : Nat}
    (hpre : pre.all (Below r.start) = true) (hj : j < r.bytes.length)
    (hwrap : r.start.toNat + r.bytes.length ≤ 2 ^ 64) :
    cellAt (pre ++ r :: post) (r.start + BitVec.ofNat 64 j) = some (some r.perm, r.bytes[j]) := by
  have hnone : cellAt pre (r.start + BitVec.ofNat 64 j) = none := by
    induction pre with
    | nil => rfl
    | cons q qs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hpre
      have h1 := cellAt_below_none (j := j) hpre.1 hj hwrap
      have h2 := ih hpre.2
      unfold cellAt at h1 h2 ⊢
      rw [show q :: qs = [q] ++ qs from rfl, List.findSome?_append, h1, Option.none_or, h2]
  have hsub : (r.start + BitVec.ofNat 64 j - r.start).toNat = j := by
    have : r.start + BitVec.ofNat 64 j - r.start = BitVec.ofNat 64 j := by bv_omega
    rw [this, BitVec.toNat_ofNat]; omega
  simp only [cellAt, List.findSome?_append] at hnone ⊢
  rw [hnone, Option.none_or, List.findSome?_cons]
  simp [hsub, hj]

@[simp]
theorem read8_loadCellAt (regions : List Region) (a : BitVec 64) :
    (⟨loadCellAt regions⟩ : Memory).read8 a = (⟨cellAt regions⟩ : Memory).read8 a := by
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    by_cases hi : (a - r.start).toNat < r.bytes.length
    · simp only [Memory.read8, loadCellAt, cellAt, List.findSome?_cons, hi, ↓reduceDIte]
    · simpa only [Memory.read8, loadCellAt, cellAt, List.findSome?_cons, hi, ↓reduceDIte] using ih

@[simp]
theorem perm_loadCellAt (regions : List Region) (a : BitVec 64) :
    (⟨loadCellAt regions⟩ : Memory).perm a = (⟨cellAt regions⟩ : Memory).perm a := by
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    by_cases hi : (a - r.start).toNat < r.bytes.length
    · simp only [Memory.perm, loadCellAt, cellAt, List.findSome?_cons, hi, ↓reduceDIte]
      rfl
    · simpa only [Memory.perm, loadCellAt, cellAt, List.findSome?_cons, hi, ↓reduceDIte] using ih

@[simp]
theorem isLazyFree_loadCellAt (regions : List Region) (a : BitVec 64) :
    (⟨loadCellAt regions⟩ : Memory).isLazyFree a = false := by
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    by_cases hi : (a - r.start).toNat < r.bytes.length
    · simp only [Memory.isLazyFree, loadCellAt, List.findSome?_cons, hi, ↓reduceDIte]
    · simpa only [Memory.isLazyFree, loadCellAt, List.findSome?_cons, hi, ↓reduceDIte] using ih

/-- A slice `[off, off + bs.length)` of `regions[k]` that equals `bs` is held by `⟨cellAt regions⟩`
    with `regions[k]`'s normalized permission when `regions[k].perm.lazyFree = false`. -/
theorem holdsBytes_of_region_slice (regions : List Region) (k : Nat) (hk : k < regions.length)
    (hpre : (regions.take k).all (Below regions[k].start) = true)
    (hwrap : regions[k].start.toNat + regions[k].bytes.length ≤ 2 ^ 64)
    (off : Nat) (bs : List (BitVec 8))
    (hbs : (regions[k].bytes.drop off).take bs.length = bs)
    (hlf : regions[k].perm.lazyFree = false := by rfl) :
    Obj.HoldsBytes ⟨cellAt regions⟩ (regions[k].start + BitVec.ofNat 64 off) bs
      (fun _ => regions[k].perm.rwx) := by
  intro i hi
  have hsplit : regions = regions.take k ++ regions[k] :: regions.drop (k + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  generalize hr : regions[k] = r at hpre hwrap hbs hlf hsplit ⊢
  have hlen : off + bs.length ≤ r.bytes.length := by
    have := congrArg List.length hbs
    simp only [List.length_take, List.length_drop] at this
    omega
  have hj : off + i < r.bytes.length := by omega
  have haddr : r.start + BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      r.start + BitVec.ofNat 64 (off + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hcell : cellAt regions (r.start + BitVec.ofNat 64 (off + i)) =
      some (some r.perm, r.bytes[off + i]) := by
    rw [hsplit]
    exact cellAt_of_split hpre hj hwrap
  have hbyte : r.bytes[off + i] = bs[i] := by
    have : bs[i] = ((r.bytes.drop off).take bs.length)[i]'(by simp; omega) := by
      simp only [hbs]
    rw [this, List.getElem_take, List.getElem_drop]
  refine ⟨?_, ?_, ?_⟩
  · unfold Memory.read8; rw [haddr]; dsimp only []; rw [hcell, hbyte]
  · unfold Memory.perm; rw [haddr]; dsimp only []; rw [hcell]
  · unfold Memory.isLazyFree; rw [haddr]; dsimp only []; rw [hcell]; simp [hlf]

/-- A slice `[off, off + bs.length)` of `regions[k]` that equals `bs` is held by
    `⟨loadCellAt regions⟩` with `regions[k]`'s normalized permission. -/
theorem holdsBytes_of_loadRegion_slice (regions : List Region) (k : Nat) (hk : k < regions.length)
    (hpre : (regions.take k).all (Below regions[k].start) = true)
    (hwrap : regions[k].start.toNat + regions[k].bytes.length ≤ 2 ^ 64)
    (off : Nat) (bs : List (BitVec 8))
    (hbs : (regions[k].bytes.drop off).take bs.length = bs) :
    Obj.HoldsBytes ⟨loadCellAt regions⟩ (regions[k].start + BitVec.ofNat 64 off) bs
      (fun _ => regions[k].perm.rwx) := by
  intro i hi
  have hsplit : regions = regions.take k ++ regions[k] :: regions.drop (k + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  generalize hr : regions[k] = r at hpre hwrap hbs hsplit ⊢
  have hlen : off + bs.length ≤ r.bytes.length := by
    have := congrArg List.length hbs
    simp only [List.length_take, List.length_drop] at this
    omega
  have hj : off + i < r.bytes.length := by omega
  have haddr : r.start + BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      r.start + BitVec.ofNat 64 (off + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hcell : cellAt regions (r.start + BitVec.ofNat 64 (off + i)) =
      some (some r.perm, r.bytes[off + i]) := by
    rw [hsplit]
    exact cellAt_of_split hpre hj hwrap
  have hbyte : r.bytes[off + i] = bs[i] := by
    have : bs[i] = ((r.bytes.drop off).take bs.length)[i]'(by simp; omega) := by
      simp only [hbs]
    rw [this, List.getElem_take, List.getElem_drop]
  refine ⟨?_, ?_, isLazyFree_loadCellAt regions _⟩
  · rw [read8_loadCellAt]; unfold Memory.read8; rw [haddr]; dsimp only []; rw [hcell, hbyte]
  · rw [perm_loadCellAt]; unfold Memory.perm; rw [haddr]; dsimp only []; rw [hcell]

end Arm64.Snapshot

namespace Arm64.Process

open ProofLib

/-- `Memory.mapZero` preserves any `Obj.HoldsBytes` region. -/
theorem holdsBytes_mapZero {m : Memory} {base addr : BitVec 64} {len : Nat}
    {bs : List (BitVec 8)} {p : BitVec 64 → Perm}
    (h : Obj.HoldsBytes m addr bs p) :
    Obj.HoldsBytes (m.mapZero base len) addr bs p := by
  intro i hi
  obtain ⟨hr, hp, hlf⟩ := h i hi
  have hcell :
      (m.mapZero base len).cells (addr + BitVec.ofNat 64 i) =
        m.cells (addr + BitVec.ofNat 64 i) := by
    simp [Memory.mapZero, hp]
  refine ⟨?_, ?_, ?_⟩
  · unfold Memory.read8; rw [hcell]; exact hr
  · unfold Memory.perm; rw [hcell]; exact hp
  · unfold Memory.isLazyFree; rw [hcell]; exact hlf

/-- Deconstruct `img.loadState inputs = .ok s0` into its initial `sp`, `stackRegion`, and `s0.mem`. -/
theorem ElfImage.loadState_eq_ok {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h_load : img.loadState inputs = .ok s0) :
    ∃ sp stackRegion,
      buildInitialStack img inputs = .ok (sp, stackRegion) ∧
      s0.mem = (⟨Snapshot.loadCellAt (img.segments ++ [stackRegion])⟩ : Memory).mapZero
        (BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)) inputs.init.stackSize ∧
      s0.pc = img.entry ∧
      s0.sp = sp ∧
      s0.brkStart = img.brkStart ∧
      s0.brk = img.brkStart ∧
      s0.status = .Running := by
  unfold ElfImage.loadState at h_load
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_load
  split at h_load
  · contradiction
  · split at h_load
    · contradiction
    · split at h_load
      · contradiction
      · generalize hb : buildInitialStack img inputs = r at h_load
        cases r with
        | error _ => contradiction
        | ok pair =>
          rcases pair with ⟨sp, stackRegion⟩
          injection h_load with hs0
          subst hs0
          exact ⟨sp, stackRegion, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No byte in an initial ELF process state `s0` (`img.loadState inputs = .ok s0`) is marked
    `lazyFree`. -/
theorem ElfImage.loadState_isLazyFree {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h_load : img.loadState inputs = .ok s0) (a : BitVec 64) :
    s0.mem.isLazyFree a = false := by
  obtain ⟨_, stackRegion, _, hmem, _, _, _, _, _⟩ := ElfImage.loadState_eq_ok h_load
  rw [hmem, Memory.isLazyFree_mapZero]
  exact Snapshot.isLazyFree_loadCellAt _ a

/-- Any byte slice `[off, off + bs.length)` of `img.segments[k]` is held in `s0.mem` for every
    `inputs` and `s0` with `img.loadState inputs = .ok s0`. Because `img.segments` precede
    `stackRegion` in `Snapshot.loadCellAt (img.segments ++ [stackRegion])` and `Memory.mapZero`
    preserves mapped cells, all side conditions depend only on `img` and `bs`, not on `inputs`. -/
theorem ElfImage.holdsBytes_of_segment_slice (img : ElfImage) {inputs : ProcessInputs} {s0 : State}
    (h_load : img.loadState inputs = .ok s0)
    (k : Nat) (hk : k < img.segments.length)
    (hpre : (img.segments.take k).all (Snapshot.Below img.segments[k].start) = true)
    (hwrap : img.segments[k].start.toNat + img.segments[k].bytes.length ≤ 2 ^ 64)
    (off : Nat) (bs : List (BitVec 8))
    (hbs : (img.segments[k].bytes.drop off).take bs.length = bs) :
    Obj.HoldsBytes s0.mem (img.segments[k].start + BitVec.ofNat 64 off) bs
      (fun _ => img.segments[k].perm.rwx) := by
  obtain ⟨_, stackRegion, _, hmem, _, _, _, _, _⟩ := ElfImage.loadState_eq_ok h_load
  rw [hmem]
  have hk' : k < (img.segments ++ [stackRegion]).length := by
    simp only [List.length_append]; omega
  have h_elem : (img.segments ++ [stackRegion])[k] = img.segments[k] :=
    List.getElem_append_left hk
  have h_take : (img.segments ++ [stackRegion]).take k = img.segments.take k :=
    List.take_append_of_le_length (Nat.le_of_lt hk)
  have hpre' : ((img.segments ++ [stackRegion]).take k).all
      (Snapshot.Below (img.segments ++ [stackRegion])[k].start) = true := by
    rw [h_take, h_elem]; exact hpre
  have hwrap' : (img.segments ++ [stackRegion])[k].start.toNat +
      (img.segments ++ [stackRegion])[k].bytes.length ≤ 2 ^ 64 := by
    rw [h_elem]; exact hwrap
  have hbs' : ((img.segments ++ [stackRegion])[k].bytes.drop off).take bs.length = bs := by
    rw [h_elem]; exact hbs
  have h_reg := Snapshot.holdsBytes_of_loadRegion_slice (img.segments ++ [stackRegion])
    k hk' hpre' hwrap' off bs hbs'
  rw [h_elem] at h_reg
  exact holdsBytes_mapZero h_reg

/-! ## Total Initial-State Constructor for Kernel Evaluation -/

/-- Total initial-state constructor from `img` and `inputs` (omitting the one-time
    `img.WellFormed` check so repeated memory lookups in the kernel do not re-evaluate
    `img.WellFormed`). -/
def ElfImage.rawState (img : ElfImage) (inputs : ProcessInputs := {}) : State :=
  match buildInitialStack img inputs with
  | .error _ => {}
  | .ok (sp, stackRegion) =>
    let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
    let baseMem : Memory := ⟨Snapshot.loadCellAt (img.segments ++ [stackRegion])⟩
    let mem := baseMem.mapZero stackBase inputs.init.stackSize
    let symtab : String → String → Option (BitVec 64) :=
      fun _ name => (img.symbols.find? (·.1 == name)).map (·.2)
    { regs      := RegFile.empty
      vregs     := VRegFile.empty
      sp        := sp
      pc        := img.entry
      pstate    := PState.zero
      mem       := mem
      tpidrEl0  := 0#64
      brkStart  := img.brkStart
      brk       := img.brkStart
      fs        := initFsState inputs
      oracle    := inputs.init.oracle
      oracleIdx := 0
      exclFails    := inputs.init.oracle.exclFails
      trace        := []
      status       := .Running
      symtab       := symtab
      physMemAvail := inputs.init.physMemAvail }

/-- When `(img.loadState inputs).toOption.isSome = true`, `img.loadState inputs` equals
    `.ok (img.rawState inputs)`. -/
theorem ElfImage.loadState_eq_rawState {img : ElfImage} {inputs : ProcessInputs}
    (h : (img.loadState inputs).toOption.isSome = true) :
    img.loadState inputs = .ok (img.rawState inputs) := by
  generalize hL : img.loadState inputs = res at h ⊢
  cases res with
  | error _ => contradiction
  | ok s0 =>
    unfold ElfImage.loadState at hL
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hL
    split at hL
    · contradiction
    · split at hL
      · contradiction
      · split at hL
        · contradiction
        · unfold ElfImage.rawState
          generalize hb : buildInitialStack img inputs = r at hL ⊢
          cases r with
          | error _ => contradiction
          | ok pair =>
            rcases pair with ⟨sp, stackRegion⟩
            exact hL.symm

/-! ## Hookless `Program` Bridge and Syscall Bundle Monotonicity -/

/-- A `Program` with no active `externs` or `overrides` hooks (`∀ pc, prog.externAt? pc = none`). -/
def _root_.Arm64.Program.NoHooks (prog : Program) : Prop :=
  ∀ pc : BitVec 64, prog.externAt? pc = none

theorem _root_.Arm64.Program.noHooks_pureWithSvc (svc : State → State) :
    (Program.pureWithSvc svc).NoHooks := by
  intro _
  rfl

theorem _root_.Arm64.Program.noHooks_pureMem : Program.pureMem.NoHooks :=
  Program.noHooks_pureWithSvc Syscall.standard

theorem _root_.Arm64.Program.NoHooks.of_eq_none {prog : Program}
    (h_ext : prog.externs = fun _ => none)
    (h_ovr : prog.overrides = fun _ => none) :
    prog.NoHooks := by
  intro pc
  unfold Program.externAt? Program.hookAtOff?
  rw [h_ext, h_ovr]
  have hfn : (fun (x : String × Nat) => if x.2 == (pc - prog.base).toNat then (none : Option (State → State)) else none) = fun _ => none := by
    funext x; split <;> rfl
  have h_none : ∀ l : List (String × Nat), List.findSome? (fun _ => (none : Option (State → State))) l = none := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => exact ih
  rw [hfn, h_none prog.stubs, h_none prog.symbols]
  rfl

theorem _root_.Arm64.Program.NoHooks.hooksKeepFrozen {prog : Program}
    (h : prog.NoHooks) : prog.HooksKeepFrozen := by
  intro pc _ _ h_at
  rw [h pc] at h_at
  nomatch h_at

theorem _root_.Arm64.Program.NoHooks.fetchMem_eq_pureWithSvc {prog : Program}
    (h : prog.NoHooks) (svc : State → State) (m : Memory) (pc : BitVec 64) :
    prog.fetchMem m pc = (Program.pureWithSvc svc).fetchMem m pc := by
  unfold Program.fetchMem
  rw [h pc, Program.noHooks_pureWithSvc svc pc]

theorem _root_.Arm64.Program.NoHooks.fetchMem_eq_pureMem {prog : Program}
    (h : prog.NoHooks) (m : Memory) (pc : BitVec 64) :
    prog.fetchMem m pc = Program.pureMem.fetchMem m pc :=
  h.fetchMem_eq_pureWithSvc Syscall.standard m pc

theorem _root_.Arm64.Step.to_pureWithSvc {prog : Program} {svc : State → State} {s s' : State}
    (h_no : prog.NoHooks) (h : Step prog s s')
    (h_svc : prog.svc = svc := by rfl) : Step (Program.pureWithSvc svc) s s' := by
  have hev : ∀ inst, prog.evalInst inst s = (Program.pureWithSvc svc).evalInst inst s :=
    fun inst => by simp only [Program.evalInst, Program.pureWithSvc, Program.ofSvc, h_svc]
  cases h with
  | @exec inst h_run h_fetch =>
    rw [h_no.fetchMem_eq_pureWithSvc svc] at h_fetch
    rw [hev inst]
    exact Step.exec h_run h_fetch
  | halt_unmapped h_run h_fetch _ =>
    rw [h_no.fetchMem_eq_pureWithSvc svc] at h_fetch
    exact Step.halt_unmapped h_run h_fetch (Program.noHooks_pureWithSvc svc s.pc)
  | extern _ h_ext _ _ =>
    rw [h_no s.pc] at h_ext
    nomatch h_ext
  | extern_fault _ h_ext _ =>
    rw [h_no s.pc] at h_ext
    nomatch h_ext

theorem _root_.Arm64.Steps.to_pureWithSvc {prog : Program} {svc : State → State} {s s' : State}
    (h_no : prog.NoHooks) (h : Steps prog s s')
    (h_svc : prog.svc = svc := by rfl) : Steps (Program.pureWithSvc svc) s s' := by
  induction h with
  | refl s => exact Steps.refl s
  | step h1 _ ih => exact Steps.step (h1.to_pureWithSvc h_no h_svc) ih

theorem _root_.Arm64.Step.to_pureMem {prog : Program} {s s' : State}
    (h_no : prog.NoHooks) (h : Step prog s s')
    (h_svc : prog.svc = Syscall.standard := by rfl) : Step Program.pureMem s s' :=
  h.to_pureWithSvc h_no h_svc

theorem _root_.Arm64.Steps.to_pureMem {prog : Program} {s s' : State}
    (h_no : prog.NoHooks) (h : Steps prog s s')
    (h_svc : prog.svc = Syscall.standard := by rfl) : Steps Program.pureMem s s' :=
  h.to_pureWithSvc h_no h_svc

/-- Supervisor-call bundle `svc₁` refines into `svc₂` fail-closed: on every state `s`, `svc₁ s`
    either agrees identically with `svc₂ s` or traps with `.Exception _`. -/
def SvcRefines (svc₁ svc₂ : State → State) : Prop :=
  ∀ s : State, svc₁ s = svc₂ s ∨ ∃ msg, (svc₁ s).status = .Exception msg

theorem SvcRefines.refl (svc : State → State) : SvcRefines svc svc :=
  fun _ => Or.inl rfl

theorem SvcRefines.trans {svc₁ svc₂ svc₃ : State → State}
    (h12 : SvcRefines svc₁ svc₂) (h23 : SvcRefines svc₂ svc₃) :
    SvcRefines svc₁ svc₃ := by
  intro s
  rcases h12 s with heq | hex
  · rw [heq]; exact h23 s
  · exact Or.inr hex

theorem SvcRefines.noSyscalls (svc : State → State) : SvcRefines Arm64.noSyscalls svc :=
  fun _ => Or.inr ⟨_, rfl⟩

theorem SvcRefines.prefix {t₁ rest : List (BitVec 64 × (State → State))} :
    SvcRefines (Syscall.dispatch t₁) (Syscall.dispatch (t₁ ++ rest)) := by
  intro s
  unfold Syscall.dispatch
  induction t₁ with
  | nil => exact Or.inr ⟨_, rfl⟩
  | cons hd tl ih =>
    dsimp only [List.cons_append, List.find?]
    cases hd.1 == s.readReg64 Reg.x8
    · exact ih
    · exact Or.inl rfl

theorem SvcRefines.cons_right (hd : BitVec 64 × (State → State))
    {t : List (BitVec 64 × (State → State))}
    (hdisj : ∀ e ∈ t, e.1 ≠ hd.1) :
    SvcRefines (Syscall.dispatch t) (Syscall.dispatch (hd :: t)) := by
  intro s
  unfold Syscall.dispatch
  dsimp only [List.find?]
  cases h : (hd.1 == s.readReg64 Reg.x8)
  · exact Or.inl rfl
  · have heq : hd.1 = s.readReg64 Reg.x8 := of_decide_eq_true h
    have hnone : t.find? (·.1 == s.readReg64 Reg.x8) = none := by
      induction t with
      | nil => rfl
      | cons e tl ih =>
        have hne : (e.1 == s.readReg64 Reg.x8) = false :=
          beq_false_of_ne fun he => hdisj e (.head _) (he.trans heq.symm)
        simp only [List.find?, hne]
        exact ih fun e' hm => hdisj e' (.tail _ hm)
    rw [hnone]
    exact Or.inr ⟨_, rfl⟩

theorem SvcRefines.stdioWrite_stdioCli : SvcRefines Syscall.stdioWrite Syscall.stdioCli :=
  (SvcRefines.prefix (t₁ := Syscall.stdioWriteTable)
      (rest := [(SYS_READV, execReadv), (SYS_WRITEV, execWritev), (SYS_EXIT, execExit),
        (SYS_EXIT_GROUP, execExit)])).trans
    (SvcRefines.cons_right (SYS_READ, execRead)
      (by simp [Syscall.stdioWriteTable, SYS_WRITE, SYS_READ, SYS_READV, SYS_WRITEV, SYS_EXIT,
        SYS_EXIT_GROUP]))

theorem SvcRefines.stdioCli_fileIo : SvcRefines Syscall.stdioCli Syscall.fileIo :=
  SvcRefines.prefix

theorem SvcRefines.fileIo_standard : SvcRefines Syscall.fileIo Syscall.standard := by
  have heq : Syscall.standardTable = Syscall.fileIoTable ++
      (Syscall.pollTable ++ Syscall.allocTable ++ Syscall.signalsTable ++ Syscall.timeTable ++
       Syscall.randomTable ++ Syscall.miscTable) := by
    simp only [Syscall.standardTable, Syscall.fileIoTable, List.append_assoc]
  unfold Syscall.standard
  rw [heq]
  exact SvcRefines.prefix

theorem SvcRefines.stdioCli_standard : SvcRefines Syscall.stdioCli Syscall.standard :=
  SvcRefines.stdioCli_fileIo.trans SvcRefines.fileIo_standard

/-- Any `Steps (Program.pureWithSvc svc₁) s sf` trace whose final status is not `.Exception _`
    is also a `Steps (Program.pureWithSvc svc₂) s sf` trace when `SvcRefines svc₁ svc₂`. -/
theorem _root_.Arm64.Steps.mono_pureWithSvc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {s sf : State}
    (h : Steps (Program.pureWithSvc svc₁) s sf)
    (hnoexc : ∀ msg, sf.status ≠ .Exception msg) :
    Steps (Program.pureWithSvc svc₂) s sf := by
  induction h with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    cases h1 with
    | @exec inst hr hf =>
      have hf' : (Program.pureWithSvc svc₂).fetchMem s1.mem s1.pc = some inst := hf
      have hev : (Program.pureWithSvc svc₁).evalInst inst s1 =
          (Program.pureWithSvc svc₂).evalInst inst s1 ∨
          ∃ msg, ((Program.pureWithSvc svc₁).evalInst inst s1).status = .Exception msg := by
        cases inst with
        | system isHalt imm =>
          cases isHalt
          · by_cases himm : imm == 0#16
            · have heq : imm = 0#16 := of_decide_eq_true himm
              subst heq
              simp only [Program.evalInst, Program.pureWithSvc, Program.ofSvc,
                execInstWithSvc, BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
              rcases href s1 with hs | ⟨msg, hm⟩
              · exact Or.inl (by simp only [evalSvc, hs])
              · exact Or.inr ⟨msg, by simp only [evalSvc, hm]⟩
            · exact Or.inl (by simp [Program.evalInst, execInstWithSvc, himm])
          · exact Or.inl rfl
        | _ => exact Or.inl rfl
      rcases hev with heq | ⟨msg, hm⟩
      · have ih' := ih hnoexc
        rw [heq] at ih'
        exact Steps.step (Step.exec hr hf') ih'
      · have h23 := Steps.from_not_running h2 (by rw [hm]; simp)
        subst h23
        exact absurd hm (hnoexc msg)
    | halt_unmapped hr hf he =>
      exact Steps.step (Step.halt_unmapped hr hf he) (ih hnoexc)
    | extern _ he _ _ => nomatch he
    | extern_fault _ he _ => nomatch he

theorem ProcessExitsWith.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {s0 : State} {out : ProcessOutcome}
    (h : ProcessExitsWith (Program.pureWithSvc svc₁) s0 out) :
    ProcessExitsWith (Program.pureWithSvc svc₂) s0 out := by
  obtain ⟨sf, hs, hout⟩ := h
  refine ⟨sf, hs.mono_pureWithSvc href fun msg hm => ?_, hout⟩
  rcases hout with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hm] at hst <;> nomatch hst

theorem ElfImageRunsTo.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {oom : State → Prop}
    (h : ElfImageRunsTo img inputs post oom (Program.pureWithSvc svc₁)) :
    ElfImageRunsTo img inputs post oom (Program.pureWithSvc svc₂) := by
  obtain ⟨s0, hload, ⟨out, hpe, hpost⟩ | ⟨sf, hs, hoom, hoom_p⟩, _⟩ := h
  · exact ElfImageRunsTo.of_exitsWith hload (hpe.mono_svc href) hpost
  · refine ElfImageRunsTo.of_oom hload (hs.mono_pureWithSvc href fun _ hm => ?_) hoom hoom_p
    rw [hm] at hoom; nomatch hoom

/-- `ElfRunsTo` (and hence `ElfCorrect` / `ElfSafe`) is monotone in the syscall bundle. -/
theorem ElfRunsTo.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {elfBytes : List (BitVec 8)} {pre : ProcessInputs → Prop}
    {post : ProcessInputs → ProcessOutcome → Prop} {oom : ProcessInputs → State → Prop}
    (h : ElfRunsTo elfBytes pre post oom (Program.pureWithSvc svc₁)) :
    ElfRunsTo elfBytes pre post oom (Program.pureWithSvc svc₂) := by
  obtain ⟨img, hparse, hruns⟩ := h
  exact ⟨img, hparse, fun inputs hi => ElfImageRunsTo.mono_svc href (hruns inputs hi)⟩

theorem ElfImageCorrect.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop}
    (h : ElfImageCorrect img inputs post (Program.pureWithSvc svc₁)) :
    ElfImageCorrect img inputs post (Program.pureWithSvc svc₂) :=
  ElfImageRunsTo.mono_svc href h

theorem ElfImageSafe.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {img : ElfImage} {inputs : ProcessInputs}
    (h : ElfImageSafe img inputs (Program.pureWithSvc svc₁)) :
    ElfImageSafe img inputs (Program.pureWithSvc svc₂) :=
  ElfImageRunsTo.mono_svc href h

theorem ElfCorrect.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {elfBytes : List (BitVec 8)} {pre : ProcessInputs → Prop}
    {post : ProcessInputs → ProcessOutcome → Prop} {minPhysMem : ProcessInputs → Nat}
    (h : ElfCorrect elfBytes pre post (Program.pureWithSvc svc₁) minPhysMem) :
    ElfCorrect elfBytes pre post (Program.pureWithSvc svc₂) minPhysMem :=
  ElfRunsTo.mono_svc href h

theorem ElfSafe.mono_svc {svc₁ svc₂ : State → State}
    (href : SvcRefines svc₁ svc₂) {elfBytes : List (BitVec 8)} {pre : ProcessInputs → Prop}
    {minPhysMem : ProcessInputs → Nat}
    (h : ElfSafe elfBytes pre (Program.pureWithSvc svc₁) minPhysMem) :
    ElfSafe elfBytes pre (Program.pureWithSvc svc₂) minPhysMem :=
  ElfRunsTo.mono_svc href h

/-- Lift `exits_with prog 0#64 s0` on any hookless `prog` to `ElfImageCorrect` (with default
    `Program.pureMem`). -/
theorem ElfImageCorrect.of_noHooks_exits_with {img : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {prog : Program} {s0 : State}
    (h_no : prog.NoHooks)
    (h_load : img.loadState inputs = .ok s0)
    (h_code_loaded : prog.CodeLoaded s0.mem)
    (h_exits : exits_with prog 0#64 s0 (fun sf => post (ProcessOutcome.ofState 0#64 sf)))
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    ElfImageCorrect img inputs post Program.pureMem := by
  obtain ⟨sf, h_steps, h_out⟩ := h_exits h_code_loaded
  rcases h_out with ⟨h_status, h_post⟩ | ⟨_, h_oom⟩
  · have h_pe : ProcessExitsWith Program.pureMem s0 (ProcessOutcome.ofState 0#64 sf) :=
      ⟨sf, h_steps.to_pureMem h_no h_svc, Or.inl ⟨0#64, h_status, rfl⟩⟩
    exact ElfImageCorrect.of_exitsWith h_load h_pe rfl h_post
  · exact False.elim h_oom

/-- Lift `exits_with prog 0#64 s0` on any hookless `prog` to `ElfImageSafe` (with default
    `Program.pureMem`). -/
theorem ElfImageSafe.of_noHooks_exits_with {img : ElfImage} {inputs : ProcessInputs}
    {prog : Program} {s0 : State}
    (h_no : prog.NoHooks)
    (h_load : img.loadState inputs = .ok s0)
    (h_code_loaded : prog.CodeLoaded s0.mem)
    (h_exits : exits_with prog 0#64 s0 (fun _ => True))
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    ElfImageSafe img inputs Program.pureMem :=
  ElfImageCorrect.of_noHooks_exits_with (post := fun _ => True) h_no h_load h_code_loaded
    h_exits h_svc

end Arm64.Process
