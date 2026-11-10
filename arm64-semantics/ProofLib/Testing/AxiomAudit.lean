/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Testing.AxiomAudit.Core
public import ProofLib.Testing.AxiomAudit.Fixtures
import all ProofLib.Testing.AxiomAudit.Fixtures
public import ProofLib.TrustedClosure
public import ProofLib.VCGen

/-!
# Regression Tests for `#axiom_audit`

Tests `#axiom_audit`, `#axiom_audit_module`, `#axiom_audit_modules`, and
`#trusted_closure_modules_batch!`. Verifies that kernel-only proofs (including `reduceDecode`) pass
cleanly, and that `sorry`, custom `axiom`, `native_decide`, and `bv_decide` fixtures in
`ProofLib.Testing.AxiomAudit.Fixtures` are flagged with blame attributed to the introducing lemma.
-/

@[expose] public section

namespace Testing.AxiomAudit.Tests

/-- info: [axiom_audit] scope=explicit theorems=1 clean=1 dirty=0 culprits=0 -/
#guard_msgs in #axiom_audit Testing.AxiomAudit.Tests.clean_thm

#guard_msgs(drop info) in #axiom_audit! Testing.AxiomAudit.Tests.clean_thm

/--
info: [axiom_audit] scope=explicit theorems=5 clean=0 dirty=5 culprits=4
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_bv_decide kind=bv_decide dependents=2
[axiom_audit] blame Testing.AxiomAudit.Tests.custom_ax kind=axiom dependents=1
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_native kind=native dependents=1
[axiom_audit] blame sorryAx kind=sorry dependents=1
[axiom_audit] dirty Testing.AxiomAudit.Tests.downstream <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.sorry_thm <- [sorryAx]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_bv_decide <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_custom <- [Testing.AxiomAudit.Tests.custom_ax]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_native <- [Testing.AxiomAudit.Tests.uses_native]
-/
#guard_msgs in
#axiom_audit Testing.AxiomAudit.Tests.sorry_thm Testing.AxiomAudit.Tests.uses_custom
  Testing.AxiomAudit.Tests.uses_native Testing.AxiomAudit.Tests.uses_bv_decide
  Testing.AxiomAudit.Tests.downstream

/-- error: [axiom_audit] scope=explicit theorems=1 clean=0 dirty=1 culprits=1
[axiom_audit] blame sorryAx kind=sorry dependents=1
[axiom_audit] dirty Testing.AxiomAudit.Tests.sorry_thm <- [sorryAx]
-/
#guard_msgs in #axiom_audit! Testing.AxiomAudit.Tests.sorry_thm

/-- `ProofLib.reduceDecode` emits a kernel-checked `decide` proof with no native-evaluation axioms. -/
theorem reduceDecode_kernel :
    (Arm64.decode (BitVec.ofNat 32 0xd65f03c0)).isSome = true := by
  simp only [ProofLib.reduceDecode, Option.isSome_some]

/-- info: [axiom_audit] scope=explicit theorems=1 clean=1 dirty=0 culprits=0 -/
#guard_msgs in #axiom_audit Testing.AxiomAudit.Tests.reduceDecode_kernel

/--
info: [axiom_audit] scope=ProofLib.Testing.AxiomAudit.Fixtures theorems=7 clean=1 dirty=6 culprits=4
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_bv_decide kind=bv_decide dependents=2
[axiom_audit] blame sorryAx kind=sorry dependents=2
[axiom_audit] blame Testing.AxiomAudit.Tests.custom_ax kind=axiom dependents=1
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_native kind=native dependents=1
[axiom_audit] dirty Testing.AxiomAudit.Tests.downstream <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.sorry_thm <- [sorryAx]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_bv_decide <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_custom <- [Testing.AxiomAudit.Tests.custom_ax]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_native <- [Testing.AxiomAudit.Tests.uses_native]
[axiom_audit] dirty _private.ProofLib.Testing.AxiomAudit.Fixtures.0.Testing.AxiomAudit.Tests.priv_sorry <- [sorryAx]
-/
#guard_msgs in #axiom_audit_modules ProofLib.Testing.AxiomAudit.Fixtures

/-! `#axiom_audit_module M` audits exactly module `M`: the same fixtures as the prefix form above. -/
#guard_msgs (drop info) in #axiom_audit_module ProofLib.Testing.AxiomAudit.Fixtures

/--
error: [axiom_audit] scope=module ProofLib.Testing.AxiomAudit.Fixtures theorems=7 clean=1 dirty=6 culprits=4
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_bv_decide kind=bv_decide dependents=2
[axiom_audit] blame sorryAx kind=sorry dependents=2
[axiom_audit] blame Testing.AxiomAudit.Tests.custom_ax kind=axiom dependents=1
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_native kind=native dependents=1
[axiom_audit] dirty Testing.AxiomAudit.Tests.downstream <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.sorry_thm <- [sorryAx]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_bv_decide <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_custom <- [Testing.AxiomAudit.Tests.custom_ax]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_native <- [Testing.AxiomAudit.Tests.uses_native]
[axiom_audit] dirty _private.ProofLib.Testing.AxiomAudit.Fixtures.0.Testing.AxiomAudit.Tests.priv_sorry <- [sorryAx]
-/
#guard_msgs in #axiom_audit_module! ProofLib.Testing.AxiomAudit.Fixtures

/-! Exact match does not include submodules: the `Init` barrel declares no theorems itself. -/
/--
info: [axiom_audit] scope=module Init theorems=0 clean=0 dirty=0 culprits=0
-/
#guard_msgs in #axiom_audit_module Init

/-! Several modules in one pass: `Init` adds nothing, so the result matches `Fixtures` alone. -/
/--
error: [axiom_audit] scope=modules(2) theorems=7 clean=1 dirty=6 culprits=4
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_bv_decide kind=bv_decide dependents=2
[axiom_audit] blame sorryAx kind=sorry dependents=2
[axiom_audit] blame Testing.AxiomAudit.Tests.custom_ax kind=axiom dependents=1
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_native kind=native dependents=1
[axiom_audit] dirty Testing.AxiomAudit.Tests.downstream <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.sorry_thm <- [sorryAx]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_bv_decide <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_custom <- [Testing.AxiomAudit.Tests.custom_ax]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_native <- [Testing.AxiomAudit.Tests.uses_native]
[axiom_audit] dirty _private.ProofLib.Testing.AxiomAudit.Fixtures.0.Testing.AxiomAudit.Tests.priv_sorry <- [sorryAx]
-/
#guard_msgs in #axiom_audit_module! Init ProofLib.Testing.AxiomAudit.Fixtures

/-! A module that is not imported is an error, not a silent empty audit. -/
/--
error: #axiom_audit_module: module ProofLib.Testing.NoSuchModule is not imported
-/
#guard_msgs in #axiom_audit_module ProofLib.Testing.NoSuchModule

/-! `#axiom_audit_modules P1 P2 ...` audits multiple module prefixes in one shared `AuditM` pass. -/
/--
error: [axiom_audit] scope=prefixes(2) theorems=7 clean=1 dirty=6 culprits=4
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_bv_decide kind=bv_decide dependents=2
[axiom_audit] blame sorryAx kind=sorry dependents=2
[axiom_audit] blame Testing.AxiomAudit.Tests.custom_ax kind=axiom dependents=1
[axiom_audit] blame Testing.AxiomAudit.Tests.uses_native kind=native dependents=1
[axiom_audit] dirty Testing.AxiomAudit.Tests.downstream <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.sorry_thm <- [sorryAx]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_bv_decide <- [Testing.AxiomAudit.Tests.uses_bv_decide]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_custom <- [Testing.AxiomAudit.Tests.custom_ax]
[axiom_audit] dirty Testing.AxiomAudit.Tests.uses_native <- [Testing.AxiomAudit.Tests.uses_native]
[axiom_audit] dirty _private.ProofLib.Testing.AxiomAudit.Fixtures.0.Testing.AxiomAudit.Tests.priv_sorry <- [sorryAx]
-/
#guard_msgs in #axiom_audit_modules! ProofLib.Testing.AxiomAudit.Core ProofLib.Testing.AxiomAudit.Fixtures

/-! `#trusted_closure_modules_batch P1 P2 ...` audits multiple module prefixes in one shared `FastClosureM` pass. -/
/--
info: [trusted_closure] scope=prefixes(2) theorems=7 without_alloc=7 with_alloc=0 violations=0
-/
#guard_msgs in #trusted_closure_modules_batch! ProofLib.Testing.AxiomAudit.Core ProofLib.Testing.AxiomAudit.Fixtures

end Testing.AxiomAudit.Tests
