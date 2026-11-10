/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs

/-!
Equality bridges and exit-file validity lemmas between the symbolic `ImplTrace` definitions for
`Cheval26SmallSubgroupHighBitCli` and the pre-elaborated byte lists in `FastInputs`. Also
re-exports the `FastInputs` definitions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Files

open ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace
  (ValidCall0Files ValidCall1Files hbInp0 hbInp1 hbInp2 ssC1Out ssC2Out)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs
  (ssFiles0 ssFiles1 hbFiles2 ssFiles2 ssFastInp0 ssFastInp1 hbFastInp2 ssFastInp2
   ssFastOut1 ssFastOut2)

export Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs
  (ssFiles0 ssFiles1 hbFiles2 ssFiles2 ssFastInp0 ssFastInp1 hbFastInp2 ssFastInp2
   ssFastOut1 ssFastOut2)

set_option maxRecDepth 4000000 in
theorem hbInp0_eq : hbInp0 = ssFastInp0 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem hbInp1_eq : hbInp1 ssFiles0 = ssFastInp1 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem hbInp2_eq : hbInp2 = hbFastInp2 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem ssC1Out_eq : ssC1Out = ssFastOut1 := by rfl_kernel

set_option maxRecDepth 4000000 in
theorem ssC2Out_eq : ssC2Out = ssFastOut2 := by rfl_kernel

theorem ssFiles0_valid : ValidCall0Files ssFiles0 = true := by decide +kernel
theorem ssFiles1_valid : ValidCall1Files ssFiles1 = true := by decide +kernel

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Files
