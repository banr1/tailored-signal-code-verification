/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Process
public import ProofLib
public import ProofLib.TrustedClosure
public import ProofLib.Testing.AxiomAudit.Core
public import ProofLib.Testing.TrustedClosure.Fixtures
import all ProofLib.Testing.TrustedClosure.Fixtures

/-!
# Trusted Closure Regression Tests

Positive and negative regression tests for `#trusted_closure!`, `#trusted_closure_theorems!`,
module role classification, and compiler-auxiliary detection in `ProofLib.TrustedClosure`.
-/

@[expose] public section

namespace ProofLib.Testing.TrustedClosure

open Arm64

theorem sample_noSyscalls_refl (s : State) :
    Steps Program.noSyscalls s s :=
  Steps.refl s

theorem sample_stdioWrite_refl (s : State) :
    Steps Program.stdioWrite s s :=
  Steps.refl s

theorem sample_stdioCli_refl (s : State) :
    Steps Program.stdioCli s s :=
  Steps.refl s

theorem sample_fileIo_refl (s : State) :
    Steps Program.fileIo s s :=
  Steps.refl s

theorem sample_library_noSyscalls (L : LibrarySpec) :
    library_ok_withSvc noSyscalls L → True :=
  fun _ => trivial

theorem sample_elf_stdioCli (elfBytes : List (BitVec 8)) (pre : Process.ProcessInputs → Prop)
    (post : Process.ProcessInputs → Process.ProcessOutcome → Prop) :
    Process.ElfRunsTo elfBytes pre post (prog := Program.stdioCli) → True :=
  fun _ => trivial

theorem sample_alloc_refl (s : State) :
    Steps Program.alloc s s :=
  Steps.refl s

-- Non-alloc theorems exclude `Arm64.Trusted.Syscalls.Alloc`; `sample_alloc_refl` includes `Alloc`.
/--
info: [trusted_closure] scope=explicit theorems=7 without_alloc=6 with_alloc=1 violations=0
-/
#guard_msgs (substring := true) in
#trusted_closure! sample_noSyscalls_refl sample_stdioWrite_refl sample_stdioCli_refl
  sample_fileIo_refl sample_library_noSyscalls sample_elf_stdioCli sample_alloc_refl

-- Rejects a theorem over a non-alloc bundle (`Program.stdioCli`) whose statement reaches `Alloc`.
/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures.bad_stdioCli_reaches_alloc uses non-alloc bundle [Arm64.Program.stdioCli] but its statement closure reaches Arm64.Trusted.Syscalls.Alloc ([Arm64.PAGE_SIZE]) via ProofLib.Testing.TrustedClosure.Fixtures.bad_stdioCli_reaches_alloc -> ProofLib.Testing.TrustedClosure.Fixtures.leakyCliProp -> Arm64.PAGE_SIZE
-/
#guard_msgs (error, substring := true) in
#trusted_closure! ProofLib.Testing.TrustedClosure.Fixtures.bad_stdioCli_reaches_alloc

-- Accepts a `Theorems` statement whose constants all live in `Init`/`Std`/`Arm64`.
/--
info: [trusted_closure] scope=theorems theorems=1 without_alloc=1 with_alloc=0 violations=0
-/
#guard_msgs (substring := true) in
#trusted_closure_theorems! sample_noSyscalls_refl

-- Rejects a `Theorems` statement referencing a non-spec constant.
/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures.bad_theorems_stmt_uses_proof_def (in ProofLib.Testing.TrustedClosure.Fixtures) references non-Spec constant ProofLib.Testing.TrustedClosure.Fixtures.untrustedProofStmt (from ProofLib.Testing.TrustedClosure.Fixtures) in its statement type
-/
#guard_msgs (error, substring := true) in
#trusted_closure_theorems! ProofLib.Testing.TrustedClosure.Fixtures.bad_theorems_stmt_uses_proof_def

-- Rejects `_`-prefixed impure `Theorems` statements as well.
/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt (in ProofLib.Testing.TrustedClosure.Fixtures) references non-Spec constant ProofLib.Testing.TrustedClosure.Fixtures.untrustedProofStmt (from ProofLib.Testing.TrustedClosure.Fixtures) in its statement type
-/
#guard_msgs (error, substring := true) in
#trusted_closure_theorems! ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt

-- Classifies `CaseStudies.<Lib>.Theorems.Testing.*` as a `Theorems` module.
/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt (in CaseStudies.Alpha.Theorems.Testing.Foo) references non-Spec constant ProofLib.Testing.TrustedClosure.Fixtures.untrustedProofStmt
-/
#guard_msgs (error, substring := true) in
#test_theorems_module_remap!
  ProofLib.Testing.TrustedClosure.Fixtures
  CaseStudies.Alpha.Theorems.Testing.Foo
  ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt

-- Does not exempt `CaseStudies.<Lib>.Theorems.Fixtures` via `.Fixtures` filtering.
/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt (in CaseStudies.Alpha.Theorems.Fixtures) references non-Spec constant ProofLib.Testing.TrustedClosure.Fixtures.untrustedProofStmt
-/
#guard_msgs (error, substring := true) in
#test_theorems_module_remap!
  ProofLib.Testing.TrustedClosure.Fixtures
  CaseStudies.Alpha.Theorems.Fixtures
  ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt

-- Same checks for `VerifiedLibraries.<Lib>.Theorems.Testing.*` and `.Fixtures`.
/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt (in VerifiedLibraries.Alpha.Theorems.Testing.Foo) references non-Spec constant ProofLib.Testing.TrustedClosure.Fixtures.untrustedProofStmt
-/
#guard_msgs (error, substring := true) in
#test_theorems_module_remap!
  ProofLib.Testing.TrustedClosure.Fixtures
  VerifiedLibraries.Alpha.Theorems.Testing.Foo
  ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt

/--
[trusted_closure] ERROR: theorem ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt (in VerifiedLibraries.Alpha.Theorems.Fixtures) references non-Spec constant ProofLib.Testing.TrustedClosure.Fixtures.untrustedProofStmt
-/
#guard_msgs (error, substring := true) in
#test_theorems_module_remap!
  ProofLib.Testing.TrustedClosure.Fixtures
  VerifiedLibraries.Alpha.Theorems.Fixtures
  ProofLib.Testing.TrustedClosure.Fixtures._bad_underscore_theorems_stmt

-- Unit checks for `isTheoremsModule` and `isAllowedTheoremsStmtModule` classification.
#guard ProofLib.TrustedClosure.isTheoremsModule `CaseStudies.Alpha.Theorems == true
#guard ProofLib.TrustedClosure.isTheoremsModule `CaseStudies.Alpha.Theorems.Top == true
#guard ProofLib.TrustedClosure.isTheoremsModule `CaseStudies.Alpha.Theorems.Testing.Foo == true
#guard ProofLib.TrustedClosure.isTheoremsModule `CaseStudies.Alpha.Theorems.Fixtures == true
#guard ProofLib.TrustedClosure.isTheoremsModule `CaseStudies.Alpha.Testing.Theorems == false
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Alpha.Theorems == true
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Alpha.Theorems.Top == true
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Alpha.Theorems.Fixtures == true
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Common.Theorems == true
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Alpha.Testing.Theorems == false
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Testing.Theorems == false
#guard ProofLib.TrustedClosure.isTheoremsModule `ProofLib.Testing.Theorems == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Arm64.Trusted.ISA.State == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Common.Spec.AlphaAlloc == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Common.AlphaAlloc == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Spec.Top == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Generated.AlphaPlacedObj == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Generated.AlphaPlacedWitness == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Theorems.Top == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Theorems.Spec == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha.Spec.Top == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Equivalence.Spec.Basic == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Equivalence.Proofs.Basic == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Equivalence.Proofs.Spec.Basic == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Equivalence.Testing.Spec == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Equivalence.Alpha.Spec.Top == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha.Generated.AlphaPlacedObj == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha.Generated.AlphaCode == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha.Theorems.Top == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha.Proofs.Top == false
#guard ProofLib.TrustedClosure.isTheoremsModule `FormalRfcs.Alpha.Widget.Theorems.Top == true
#guard ProofLib.TrustedClosure.isTheoremsModule `FormalRfcs.Alpha.Spec.Top == false
#guard ProofLib.TrustedClosure.isTheoremsModule `FormalRfcs.Alpha.Proofs.Theorems == false
#guard ProofLib.TrustedClosure.isTheoremsModule `FormalRfcs.Common.Widget.Theorems == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Common.Spec.Cli == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Spec.Model == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Widget.Spec.Top == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Proofs.Spec.X == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Proofs.Spec.X == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Generated.Spec.X == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Testing.Spec.X == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Widget.Generated.WidgetObj == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Testing.Spec == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Widget.Proofs.Top == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `FormalRfcs.Alpha.Widget.Theorems.Spec == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `Specs.Foo == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `ProofLib.Spec == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Proofs.Top == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `ProofLib.TrustedClosure == false
-- Positional `Spec` / `Generated` matching (aligned with `tcb_map::discovery::classify`): proof
-- modules that merely contain a `Spec` / `Generated` component never supply statement vocabulary.
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Proofs.Spec.Helper == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Proofs.Generated.BetaObj == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Alpha.Proofs.Spec.Helper == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Spec.Helper == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Generated == false
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `CaseStudies.Alpha.Spec == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Common.Spec == true
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Theorems == true
#guard ProofLib.TrustedClosure.isTheoremsModule `VerifiedLibraries.Theorems.Top == true
#guard ProofLib.TrustedClosure.isAllowedTheoremsStmtModule `VerifiedLibraries.Theorems.Spec == false

-- Unit checks for the formal RFC CLI statement helpers (end-to-end tests of
-- `formalRfcCliStmtCheck` / `formalRfcPackageViolations` live in the formal RFC package's
-- `Common/Testing/CliShapeAudit.lean`).
#guard ProofLib.TrustedClosure.formalRfcImplModule? `FormalRfcs.Alpha.Widget.Spec.Top ==
  some ("Alpha", "Widget", "Spec")
#guard ProofLib.TrustedClosure.formalRfcImplModule? `FormalRfcs.Alpha.Widget.Theorems ==
  some ("Alpha", "Widget", "Theorems")
#guard ProofLib.TrustedClosure.formalRfcImplModule? `FormalRfcs.Alpha.Spec.Top == none
#guard ProofLib.TrustedClosure.formalRfcImplModule? `FormalRfcs.Common.Spec.Cli == none
#guard ProofLib.TrustedClosure.formalRfcImplModule? `FormalRfcs.Alpha.Widget == none
#guard ProofLib.TrustedClosure.formalRfcImplModule? `CaseStudies.Alpha.Widget.Spec == none
#guard ProofLib.TrustedClosure.isFormalRfcByteListType
  (.app (.const ``List [.zero]) (.app (.const ``BitVec []) (Lean.mkNatLit 8))) == true
#guard ProofLib.TrustedClosure.isFormalRfcByteListType
  (.app (.const ``List [.zero]) (.app (.const ``BitVec []) (Lean.mkRawNatLit 8))) == true
#guard ProofLib.TrustedClosure.isFormalRfcByteListType
  (.app (.const ``List [.zero]) (.app (.const ``BitVec []) (Lean.mkNatLit 16))) == false
#guard ProofLib.TrustedClosure.isFormalRfcByteListType
  (.app (.const ``List [.zero]) (.const ``Nat [])) == false
#guard ProofLib.TrustedClosure.isFormalRfcByteListType
  (.app (.const ``Array [.zero]) (.app (.const ``BitVec []) (Lean.mkNatLit 8))) == false

/-- A definition with compiler-generated equation lemmas, for `isCompilerAuxTheorem`. -/
def sampleAuxDef (n : Nat) : Nat := n + 1

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let aux := ProofLib.TrustedClosure.isCompilerAuxTheorem env
  unless aux `ProofLib.Testing.TrustedClosure.sample_noSyscalls_refl._proof_1 do
    throwError "_proof_1 is a compiler auxiliary"
  unless aux `ProofLib.Testing.TrustedClosure.sampleAuxDef.match_1 do
    throwError "match_1 is a compiler auxiliary"
  unless aux `ProofLib.Testing.TrustedClosure.sampleAuxDef.eq_1 do
    throwError "eq_1 is a compiler auxiliary"
  unless aux `ProofLib.Testing.TrustedClosure.sampleAuxDef.eq_def do
    throwError "eq_def is a compiler auxiliary"
  if aux `ProofLib.Testing.TrustedClosure.sample_noSyscalls_refl then
    throwError "a user theorem is not a compiler auxiliary"
  if aux `ProofLib.Testing.TrustedClosure.sample_eq_1_like then
    throwError "a user name ending in `_1` is not a compiler auxiliary"
  -- Named like an auxiliary, but with no parent constant, or a parent from another module.
  if aux `ProofLib.Testing.TrustedClosure._foo then
    throwError "`_foo` without a parent constant is not a compiler auxiliary"
  if aux `ProofLib.Testing.TrustedClosure.match_1 then
    throwError "`match_1` without a parent constant is not a compiler auxiliary"
  if aux `Nat.succ._proof_1 then
    throwError "an auxiliary-like name whose parent is in another module is not a compiler auxiliary"
  unless aux ((`ProofLib.Testing.TrustedClosure).str "_auxLemma" |>.num 3) do
    throwError "`<module>._auxLemma.N` is a compiler auxiliary"

end ProofLib.Testing.TrustedClosure
