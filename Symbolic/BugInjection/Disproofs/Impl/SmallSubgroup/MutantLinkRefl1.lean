/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import GeneratedLean.BugInjectionMutant
public meta import GeneratedLean.BugInjectionMutant
public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkInterned
import GeneratedLean.LibsignalSessionObj

/-!
Proves that `libsignalSessionLib` equals `lsInternedMultiLib.toMultiPlacedLibFast lsSharedExterns`
for the `cheval26-small-subgroup` mutant binary.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"

theorem ls_fast_eq :
    CryptoVerification.SignalSession.libsignalSessionLib =
      lsInternedMultiLib.toMultiPlacedLibFast lsSharedExterns := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
