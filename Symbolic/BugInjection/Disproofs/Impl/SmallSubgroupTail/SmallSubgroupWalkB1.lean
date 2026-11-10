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
public import GeneratedLean.BugInjectionMutantImage
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkInterned

/-!
# `cheval26-small-subgroup` Text-Walk Slices `05..09`

Checks text-walk slices covering blocks `200..400` of `lsInternedMultiLib` against
`mutantCliElfImage`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfImage)

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"

theorem f3Ls_textWalk_05 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 200 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_06 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 240 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_07 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 280 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_08 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 320 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_09 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 360 40 = true := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
