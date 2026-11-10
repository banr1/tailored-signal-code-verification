/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRI0Census
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupHighBitComp
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRI0OnTable
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.Refinement (x25519PublicKeySymbol x25519AgreementSymbol)
open DY.X25519 (isLowOrderKey)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRI0Census
theorem compPubOfIdx_not_lowOrder : ∀ i : Fin 12, isLowOrderKey ((compPubOfIdx i).map BitVec.toNat) = false := by decide +kernel
end Symbolic.BugInjection.Proofs.Common443.CompRI0OnTable
