/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SpecAudit
public meta import ProofLib.SpecShape

/-!
# `#spec_audit_env` Spec-Shape Regression Tests

Regression suite for `ProofLib.SpecShape` (`constArity`, `isFullApp?`, `namedArg?`, and wrong-arity
rejection) and the theorem classifier of `#spec_audit_env` (`SepWP` with explicit `oom`,
`subroutine_ok` with `oom_when`, `Program.subroutineOk`, and fail-closed rejection of unrecognized
shapes such as `subroutine_ok ... ∧ True`). Kept in a standalone module because `#spec_audit_env`
inspects every theorem in the current module.
-/

@[expose] public section

namespace Testing.SpecAuditEnv

open Arm64 ProofLib

/-! ## `SpecShape` Full-Application Matchers -/

/-- info: SepWP arity = 6, P is binder 3 -/
#guard_msgs in
open Lean Meta in
run_meta do
  let n ← SpecShape.constArity ``ProofLib.SepWP
  let names ← SpecShape.constBinderNames ``ProofLib.SepWP
  logInfo m!"SepWP arity = {n}, P is binder {(names.idxOf? `P).getD 99}"

/-- info: full: true, P = Q -/
#guard_msgs in
open Lean Meta in
run_meta do
  let args := #[mkConst `p, mkConst `t, mkConst `s, mkConst `Q, mkConst `post, mkConst `oom]
  let e := mkAppN (mkConst ``ProofLib.SepWP) args
  let full ← SpecShape.isFullApp? e ``ProofLib.SepWP
  let some P ← SpecShape.namedArg? e ``ProofLib.SepWP `P | throwError "no P"
  logInfo m!"full: {full}, P = {P}"

-- A `SepWP` application missing its trailing `oom` argument must be an error, not a silent mismatch.
/--
error: SpecShape: unrecognized spec shape: `ProofLib.SepWP` applied to 5 arguments, but its declared type has 6 binders
  @SepWP p t s Q post
-/
#guard_msgs in
open Lean Meta in
run_meta do
  let args := #[mkConst `p, mkConst `t, mkConst `s, mkConst `Q, mkConst `post]
  discard <| SpecShape.isFullApp? (mkAppN (mkConst ``ProofLib.SepWP) args) ``ProofLib.SepWP

/-- info: not SepWP: false -/
#guard_msgs in
open Lean Meta in
run_meta do
  let r ← SpecShape.isFullApp? (mkConst ``True) ``ProofLib.SepWP
  logInfo m!"not SepWP: {r}"

/-! ## Recognized Statements (`SepWP` with `oom`, `subroutine_ok` with `oom_when`) -/

@[simp, arm64_norm] def env_audit_addr : BitVec 64 := 0x71000#64

/-- `env_audit_fn` (1 instruction): `ret`. -/
def envAuditCode : FnCode :=
  .atAddr "env_audit_fn" env_audit_addr "d65f03c0"

/-- Spec with an `oom_when` clause, so its `subroutine_ok` statement has a non-default `onOom`. -/
c_spec envAuditOomSpec (p : ptr) : u64
  requires memRegion p 8
  ensures  memRegion p 8
  returns  0#64
  oom_when True

/-- `SepWP` statement with an explicit (non-default) `oom` branch. -/
theorem envAudit_sepWP_oom (prog : Program) (s : State) (P : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWP prog env_audit_addr s P post oom) :
    SepWP prog env_audit_addr s P post oom := h

/-- `subroutine_ok` statement for a spec with `oom_when`. -/
theorem envAudit_oom_ok (prog : Program) (_h_code : envAuditCode.holds prog)
    (h : subroutine_ok prog env_audit_addr envAuditOomSpec) :
    subroutine_ok prog env_audit_addr envAuditOomSpec := h

/-- `Program.subroutineOk` wrapper (by symbol name): peeled to `subroutine_ok` before classifying. -/
theorem envAudit_fn_ok (prog : Program)
    (h : prog.subroutineOk "env_audit_fn" envAuditOomSpec) :
    prog.subroutineOk "env_audit_fn" envAuditOomSpec := h

/-! ## Unrecognized Statement Shape -/

/-- Conclusion mentions `subroutine_ok` but is a conjunction: the classifier cannot attribute it to
    a function, so `#spec_audit_env` must report it instead of silently dropping it. -/
theorem envAudit_conj_bad (prog : Program)
    (h : subroutine_ok prog env_audit_addr envAuditOomSpec) :
    subroutine_ok prog env_audit_addr envAuditOomSpec ∧ True := ⟨h, trivial⟩

-- `envAudit_sepWP_oom` (`SepWP` with `oom`), `envAudit_oom_ok` and `envAudit_fn_ok` are classified;
-- `envAudit_conj_bad` is reported in `unrecognized` and as an error.
/--
info: SPEC_AUDIT_ENV_JSON|{"addr_defs":[{"addr":462848,"full_name":"Testing.SpecAuditEnv.env_audit_addr","name":"env_audit_addr"}],"fncodes":[{"base_addr":462848,"code_offset":null,"const":"Testing.SpecAuditEnv.envAuditCode","name":"env_audit_fn","total_insns":1}],"lint_warnings":[],"theorems":[{"decl":"Testing.SpecAuditEnv.envAudit_oom_ok","fn":"env_audit_fn","short_decl":"envAudit_oom_ok","spec":"Testing.SpecAuditEnv.envAuditOomSpec"},{"decl":"Testing.SpecAuditEnv.envAudit_fn_ok","fn":"env_audit_fn","short_decl":"envAudit_fn_ok","spec":"Testing.SpecAuditEnv.envAuditOomSpec"},{"decl":"Testing.SpecAuditEnv.envAudit_sepWP_oom","fn":null,"short_decl":"envAudit_sepWP_oom","spec":null}],"unrecognized":[{"decl":"Testing.SpecAuditEnv.envAudit_conj_bad","reason":"unrecognized spec shape: conjunction with non-spec conjunct\n  Arm64.subroutine_ok prog Testing.SpecAuditEnv.env_audit_addr Testing.SpecAuditEnv.envAuditOomSpec ∧ True"}]}
---
error: [spec_audit_env] Testing.SpecAuditEnv.envAudit_conj_bad: unrecognized spec shape: conjunction with non-spec conjunct
  Arm64.subroutine_ok prog Testing.SpecAuditEnv.env_audit_addr Testing.SpecAuditEnv.envAuditOomSpec ∧ True
-/
#guard_msgs in
#spec_audit_env

end Testing.SpecAuditEnv
