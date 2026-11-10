/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs

/-!
Bridges between the trace inputs and expected outputs in `Cheval26WeakStateIdx1.ImplTrace` and
their pre-elaborated counterparts in `WeakState.FastInputs`, together with `ValidStepFiles` for the
post-step directory states.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.Files

open ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
  (ValidStepFiles wsInp0 wsInp1 wsInp2 wsInp3 wsInp4 wsInp5 wsInp6
   c1Out c2Out pt3Out c5Out pt6Out)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs
  (wsFiles0 wsFiles1 wsFiles2 wsFiles3 wsFiles4 wsFiles5 wsFiles6
   wsFastInp0 wsFastInp1 wsFastInp2 wsFastInp3 wsFastInp4 wsFastInp5 wsFastInp6
   wsFastOut1 wsFastOut2 wsFastOut3 wsFastOut5 wsFastOut6)

export Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs
  (wsFiles0 wsFiles1 wsFiles2 wsFiles3 wsFiles4 wsFiles5 wsFiles6
   wsFastInp0 wsFastInp1 wsFastInp2 wsFastInp3 wsFastInp4 wsFastInp5 wsFastInp6
   wsFastOut1 wsFastOut2 wsFastOut3 wsFastOut5 wsFastOut6)

set_option maxRecDepth 4000000 in
theorem wsInp0_eq : wsInp0 = wsFastInp0 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem wsInp1_eq : wsInp1 wsFiles0 = wsFastInp1 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem wsInp2_eq : wsInp2 wsFiles1 = wsFastInp2 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem wsInp3_eq : wsInp3 = wsFastInp3 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem wsInp4_eq : wsInp4 wsFiles2 = wsFastInp4 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem wsInp5_eq : wsInp5 wsFiles4 = wsFastInp5 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem wsInp6_eq : wsInp6 wsFiles3 = wsFastInp6 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem c1Out_eq : c1Out = wsFastOut1 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem c2Out_eq : c2Out = wsFastOut2 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem pt3Out_eq : pt3Out = wsFastOut3 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem c5Out_eq : c5Out = wsFastOut5 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem pt6Out_eq : pt6Out = wsFastOut6 := by rfl_kernel

theorem wsFiles_valid :
    ValidStepFiles wsFiles0 wsFiles1 wsFiles2 wsFiles3 wsFiles4 wsFiles5 wsFiles6 = true := by
  decide +kernel

end Symbolic.BugInjection.Disproofs.Impl.WeakState.Files
