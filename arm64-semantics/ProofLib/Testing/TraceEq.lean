/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import ProofLib

/-!
# Traced-Primary Contract Regression Tests

Regression tests for proving a subroutine against `Spec.withTraceEq`, deriving untraced and
relocatable contracts via `of_withTraceEq`, lifting `HookSat` via `HookSat.with_trace_eq`, and
re-exporting trace-preservation combinators with `export`.
-/

namespace Examples.Testing.ProofLib.TraceEq

open Arm64 _root_.ProofLib ProofLib.SepLogic

def alphaCode : FnCode :=
  .atAddr "alpha" 0x10000#64
    [ 0x91000400#32  -- add x0, x0, #1
    , 0xd65f03c0#32  -- ret
    ]

def alphaProg : Program :=
  Program.ofWords 0x10000#64 alphaCode.hex [("alpha", 0x10000#64)]

def alphaSpec : Spec (BitVec 64) where
  pre x s0 := ⌜s0.readReg64 .x0 = x⌝
  post x _ sf := ⌜sf.readReg64 .x0 = x + 1#64⌝

theorem alpha_trace_ok : alphaProg.subroutineOk "alpha" (Spec.withTraceEq alphaSpec) := by
  have h_code : alphaCode.holds alphaProg := by decide
  wp_init x s0
  wp_steps
  wp_done

theorem alpha_ok : alphaProg.subroutineOk "alpha" alphaSpec :=
  alpha_trace_ok.of_withTraceEq

example : subroutine_ok alphaProg (alphaProg.fnAddr "alpha") alphaSpec :=
  subroutine_ok.of_withTraceEq alpha_trace_ok

example (traced : alphaProg.relocSubroutineOk "alpha" (Spec.withTraceEq alphaSpec)) :
    alphaProg.relocSubroutineOk "alpha" alphaSpec :=
  traced.of_withTraceEq

theorem empty_hooks_traceInert : HooksPreserveTrace (fun _ => none) := by
  intro _ _ h
  cases h

example (name : String) (h : HookSat (fun _ => none) name alphaSpec) :
    HookSat (fun _ => none) name (Spec.withTraceEq alphaSpec) :=
  h.with_trace_eq empty_hooks_traceInert

namespace ReExport
export Arm64 (HooksPreserveTrace Spec.withTraceEq HookSat.with_trace_eq)
end ReExport

open ReExport

example : ReExport.Spec.withTraceEq alphaSpec = Arm64.Spec.withTraceEq alphaSpec := rfl
example : ReExport.HooksPreserveTrace (fun _ => none) := empty_hooks_traceInert
example : Spec.withTraceEq alphaSpec = Spec.withTraceEq alphaSpec := rfl

example : (ReExport.Spec.withTraceEq alphaSpec).pre = alphaSpec.pre := by
  dsimp only [ReExport.Spec.withTraceEq]

end Examples.Testing.ProofLib.TraceEq
