/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import ProofLib

/-!
# `Spec.withPure` Regression Tests

Tests proving a subroutine once against `Spec.withPure spec R` and deriving the plain and
relocatable contracts via `of_withPure`, `Spec.withTraceEq` unfolding, and rejection of
non-`Spec.withPure` contracts.
-/

namespace Examples.Testing.ProofLib.WithPure

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

abbrev WidgetKeep (s s' : State) : Prop := s'.brk = s.brk ∧ s'.tpidrEl0 = s.tpidrEl0

theorem alpha_keep_ok : alphaProg.subroutineOk "alpha" (Spec.withPure alphaSpec WidgetKeep) := by
  have h_code : alphaCode.holds alphaProg := by decide
  wp_init x s0
  wp_steps
  wp_done

theorem alpha_ok : alphaProg.subroutineOk "alpha" alphaSpec :=
  alpha_keep_ok.of_withPure

example : subroutine_ok alphaProg (alphaProg.fnAddr "alpha") alphaSpec :=
  subroutine_ok.of_withPure alpha_keep_ok

example (h : alphaProg.relocSubroutineOk "alpha" (Spec.withPure alphaSpec WidgetKeep)) :
    alphaProg.relocSubroutineOk "alpha" alphaSpec :=
  h.of_withPure

example : Spec.withTraceEq alphaSpec = Spec.withPure alphaSpec (fun s0 sf => sf.trace = s0.trace) :=
  rfl

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
example (h : alphaProg.subroutineOk "alpha" alphaSpec) :
    alphaProg.subroutineOk "alpha" (Spec.withPure alphaSpec WidgetKeep) :=
  subroutine_ok.of_withPure h

end Examples.Testing.ProofLib.WithPure
