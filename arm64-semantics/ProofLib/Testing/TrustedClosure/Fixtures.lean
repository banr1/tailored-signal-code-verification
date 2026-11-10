/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Process

/-!
# Negative Fixtures for Trusted Closure Audits

Fixtures imported by `ProofLib.Testing.TrustedClosure` to verify that `#trusted_closure!` rejects
allocator-contaminated `Program.stdioCli` statements and non-`Spec` statement dependencies,
including on `_`-prefixed theorem names.
-/

@[expose] public section

namespace ProofLib.Testing.TrustedClosure.Fixtures

open Arm64

def leakyCliProp (s : State) : Prop :=
  PAGE_SIZE = 4096 ∧ Steps Program.stdioCli s s

theorem bad_stdioCli_reaches_alloc (s : State) : leakyCliProp s :=
  ⟨rfl, Steps.refl s⟩

def untrustedProofStmt : Prop := True

theorem bad_theorems_stmt_uses_proof_def : untrustedProofStmt :=
  trivial

/-- Exercises module-level statement audits on `_`-prefixed theorem names. -/
theorem _bad_underscore_theorems_stmt : untrustedProofStmt :=
  trivial

end ProofLib.Testing.TrustedClosure.Fixtures
