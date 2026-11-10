/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToDual
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces -- shake: keep
public import Symbolic.Specifications.Refinement.TraceExplanation -- shake: keep

/-!
# Composed-Refinement Environment Prelude

Defines `cref_hide_foreign_instances`, which removes standalone Triple Ratchet and PQXDH typeclass
instances that clash with `DY.Libsignal.Composed`, and `cref_open`, which opens the standard
composed-refinement namespaces.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open Lean Elab Command

/-- Standalone Triple Ratchet and PQXDH instance names that clash with `DY.Libsignal.Composed`. -/
meta def foreignInstanceNames : List Name :=
  let models := [`DY.Libsignal.TripleRatchet, `DY.Libsignal.PQXDH]
  let insts := [`instBytesFunctor_symbolic, `instBytesLength_symbolic,
    `instAttackerKnowledge_symbolic, `instHasExecBytes, `instExecTraceTypes_symbolic,
    `instBaseAttackerKnowledge_symbolic, `instHasExecTrace]
  models.flatMap fun m => insts.map fun i => m ++ i

/-- Removes each instance in `foreignInstanceNames` present in the environment. -/
syntax (name := crefHideForeignInstances) "cref_hide_foreign_instances" : command

@[command_elab crefHideForeignInstances]
meta def elabCrefHideForeignInstances : CommandElab := fun _ => do
  let env ← getEnv
  for n in foreignInstanceNames do
    if env.contains n then
      let id := mkCIdent n
      elabCommand (← `(attribute [-instance] $id:ident))

set_option hygiene false in
/-- Opens the standard namespaces for composed-refinement proof files. -/
macro "cref_open" : command => `(
  open DY DY.Comparse DY.Libsignal ByteSpecs
  open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
  open DY.Libsignal.HwEvents DY.Libsignal.Rust)

end Symbolic.Swarm.CREF
