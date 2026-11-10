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
public meta import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData
public meta import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public meta import Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenPlacement
public import Arm64
public import ProofLib.Placed.Multi
public import GeneratedLean.BugInjectionMutant
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData

/-!
Computable `MultiPlacement` witnesses `mutantMpl` and `mutantMmpl` for `libsignalSessionLib` and
`VerifiedLibraries.mallocngLib` in the `cheval26-small-subgroup` mutant binary. Placement tables
are reflected at elaboration time from `libsignalSessionMultiLib` and `mutantCliElfImage`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"
#guard CryptoVerification.BugInjection.mutantCliElfSha256 ==
  Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData.f3TrialElfSha256

gen_mutant_ls_placement

/-- Interned `MultiLayout` for `libsignalSessionLib` in the `cheval26-small-subgroup` mutant ELF. -/
def mutantLsLayout : Arm64.Obj.Interned.MultiLayout where
  bases := f3LsBlockBases
  addrs := f3LsSymAddrs

/-- `MultiPlacement` for `libsignalSessionLib` in the `cheval26-small-subgroup` mutant ELF. -/
def mutantMpl : Arm64.Obj.MultiPlacement :=
  mutantLsLayout.toMultiPlacement lsNames

/-- `MultiPlacement` for `VerifiedLibraries.mallocngLib` in the `cheval26-small-subgroup` mutant ELF. -/
def mutantMmpl : Arm64.Obj.MultiPlacement :=
  Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData.f3MallocngMly.toMultiPlacement
    VerifiedLibraries.Mallocng.Proofs.mallocngMultiL.names

example : mutantMmpl = Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData.f3MallocngMpl :=
  rfl

#guard mutantBlocksLen > 0
#guard mutantBlocksLen == f3LsBlockBases.length
#guard (mutantMpl.base 0).toNat > 0x400000
#guard (mutantMmpl.base 0).toNat > 0x400000

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
