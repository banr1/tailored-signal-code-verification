/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
public import Symbolic.BugInjection.Proofs.Common443.CompRI0OnTable

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRWs81UntaggedShape
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRI0Census Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRI0OnTable
variable {S : Sem} {g : Ghost}
theorem shapeAgree_dhPk_dh (s p s' : DY.Bytes) : ShapeAgree S g (DY.DiffieHellman.dhPk s) (({ pk := p, sk := s' } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := shapeAgree_of_gamma_ne (gamma_dhPk_ne_dh_pack S g s p s')
end Symbolic.BugInjection.Proofs.Common443.CompRWs81UntaggedShape
