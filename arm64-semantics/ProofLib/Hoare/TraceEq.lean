/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
import Arm64.Trusted.Spec.Hoare

/-!
# Trace-Equality Specifications

Hoare combinators for augmenting `Arm64.Spec` return postconditions with `⌜sf.trace = s0.trace⌝`
(`Spec.withTraceEq`), lifting hook contracts under `HooksPreserveTrace`, and weakening traced
subroutine contracts back to untraced ones (`of_withTraceEq`).

Note that an untraced `subroutine_ok P e spec` cannot soundly be lifted to `Spec.withTraceEq spec`
merely by checking that code reachable from `e` contains no `SVC #0` (with trace-inert indirect
targets): `subroutine_ok` requires only *some* execution reaching *some* `SubroutineOutcome` state,
not the first return. A run from `F: ret` may return to caller code at `L: svc #0; b L` (with
`write` arguments in `x0, x2, x8`), emit a trace event, and re-enter `pc = L` with `sp` and
callee-saved registers intact, satisfying a postcondition `⌜sf.trace ≠ s0.trace⌝`. Prove the
traced contract directly and derive the untraced contract via `of_withTraceEq`.
-/

@[expose] public section

namespace Arm64

open ProofLib

/-- `spec` with `⌜sf.trace = s0.trace⌝` added to its return postcondition. The panic, exit, and
    OOM postconditions are unchanged. -/
def Spec.withTraceEq {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜sf.trace = s0.trace⌝ ∗ spec.post x s0 sf }

/-- Every installed hook in `hooks` preserves `State.trace`. -/
def HooksPreserveTrace (hooks : String → Option (State → State)) : Prop :=
  ∀ (name : String) (f : State → State), hooks name = some f → ∀ s, (f s).trace = s.trace

/-- Under `HooksPreserveTrace hooks`, a hook meeting `spec` also meets `Spec.withTraceEq spec`. -/
theorem HookSat.with_trace_eq {α : Type} {hooks : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (h : HookSat hooks name spec) (htr : HooksPreserveTrace hooks) :
    HookSat hooks name (Spec.withTraceEq spec) := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [Spec.withTraceEq]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr name f hf s0, hpost⟩
  · right; exact hrest

/-- Drop the trace conjunct: a traced contract implies the untraced one. -/
theorem subroutine_ok.of_withTraceEq {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry_pc (Spec.withTraceEq spec)) :
    subroutine_ok prog entry_pc spec :=
  subroutine_ok_mono h (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [Spec.withTraceEq] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)

/-- `Program.subroutineOk` form of `subroutine_ok.of_withTraceEq`. -/
theorem Program.subroutineOk.of_withTraceEq {α : Type} {prog : Program} {fnName : String}
    {spec : Spec α} (h : prog.subroutineOk fnName (Spec.withTraceEq spec)) :
    prog.subroutineOk fnName spec :=
  subroutine_ok.of_withTraceEq h

/-- `Program.relocSubroutineOk` form of `subroutine_ok.of_withTraceEq`. -/
theorem Program.relocSubroutineOk.of_withTraceEq {α : Type} {prog : Program} {fnName : String}
    {spec : Spec α} {externs overrides : String → Option (State → State)}
    (h : prog.relocSubroutineOk fnName (Spec.withTraceEq spec) externs overrides) :
    prog.relocSubroutineOk fnName spec externs overrides :=
  fun base => subroutine_ok.of_withTraceEq (h base)

end Arm64
