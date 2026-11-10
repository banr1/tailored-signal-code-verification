/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import GeneratedLean.BugInjectionMutant
public meta import GeneratedLean.BugInjectionMutantImage
public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public meta import Symbolic.BugInjection.Disproofs.Impl.WeakState.F3LayoutData
public meta import Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenPlacement
public import Arm64
public import ProofLib.Placed.Multi
public import GeneratedLean.BugInjectionMutant
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.F3LayoutData

/-!
Computable `MultiPlacement` witnesses (`mutantMpl` and `mutantMmpl`) for `libsignalSessionLib`
and `VerifiedLibraries.mallocngLib` in the `cheval26-weak-state` mutant ELF.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

gen_mutant_ls_placement

/-- Interned `MultiLayout` for `libsignalSessionLib` in the `cheval26-weak-state` mutant ELF. -/
def mutantLsLayout : Arm64.Obj.Interned.MultiLayout where
  bases := f3LsBlockBases
  addrs := f3LsSymAddrs

/-- `MultiPlacement` witness for `libsignalSessionLib` in the `cheval26-weak-state` mutant ELF. -/
def mutantMpl : Arm64.Obj.MultiPlacement :=
  mutantLsLayout.toMultiPlacement lsNames

/-- `MultiPlacement` witness for `VerifiedLibraries.mallocngLib` in the `cheval26-weak-state` mutant ELF. -/
def mutantMmpl : Arm64.Obj.MultiPlacement :=
  Symbolic.BugInjection.Disproofs.Impl.WeakState.F3LayoutData.f3MallocngMpl

example :
    mutantMmpl =
      Symbolic.BugInjection.Disproofs.Impl.WeakState.F3LayoutData.f3MallocngMly.toMultiPlacement
        VerifiedLibraries.Mallocng.Proofs.mallocngMultiL.names :=
  rfl

#guard mutantBlocksLen == 624
#guard mutantBlocksLen == f3LsBlockBases.length
#guard (mutantMpl.base 0).toNat == 4201180
#guard mutantMmpl.base 0 == 0x49e2b0#64

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
