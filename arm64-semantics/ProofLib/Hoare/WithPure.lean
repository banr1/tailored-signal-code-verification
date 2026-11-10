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
# Pure-Postcondition Strengthening

`Arm64.Spec.withPure spec R` conjoins a pure state-preservation relation `⌜R s0 sf⌝` onto the
return postcondition of `spec`, and `subroutine_ok.of_withPure` (together with its
`Program.subroutineOk` and `Program.relocSubroutineOk` counterparts) weakens the strengthened
contract back to `spec`. Proving `Spec.withPure spec R` once suffices for both callers that
transport state-indexed invariants across the call and callers that only use `spec`; as noted in
`ProofLib.Hoare.TraceEq`, such preservation conjuncts cannot be derived post hoc from `spec` alone.
`Spec.withTraceEq spec` is definitionally `Spec.withPure spec (fun s0 sf => sf.trace = s0.trace)`.
-/

@[expose] public section

namespace Arm64

open ProofLib

/-- `spec` with `⌜R s0 sf⌝` added to its return postcondition. The panic, exit, and OOM
    postconditions are unchanged. -/
def Spec.withPure {α : Type} (spec : Spec α) (R : State → State → Prop) : Spec α :=
  { spec with post := fun x s0 sf => ⌜R s0 sf⌝ ∗ spec.post x s0 sf }

/-- Drop the extra pure conjunct: a `Spec.withPure` contract implies the plain one. -/
theorem subroutine_ok.of_withPure {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} {R : State → State → Prop}
    (h : subroutine_ok prog entry_pc (Spec.withPure spec R)) :
    subroutine_ok prog entry_pc spec :=
  subroutine_ok_mono h (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [Spec.withPure] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)

/-- `Program.subroutineOk` form of `subroutine_ok.of_withPure`. -/
theorem Program.subroutineOk.of_withPure {α : Type} {prog : Program} {fnName : String}
    {spec : Spec α} {R : State → State → Prop}
    (h : prog.subroutineOk fnName (Spec.withPure spec R)) :
    prog.subroutineOk fnName spec :=
  subroutine_ok.of_withPure h

/-- `Program.relocSubroutineOk` form of `subroutine_ok.of_withPure`. -/
theorem Program.relocSubroutineOk.of_withPure {α : Type} {prog : Program} {fnName : String}
    {spec : Spec α} {R : State → State → Prop} {externs overrides : String → Option (State → State)}
    (h : prog.relocSubroutineOk fnName (Spec.withPure spec R) externs overrides) :
    prog.relocSubroutineOk fnName spec externs overrides :=
  fun base => subroutine_ok.of_withPure (h base)

end Arm64
