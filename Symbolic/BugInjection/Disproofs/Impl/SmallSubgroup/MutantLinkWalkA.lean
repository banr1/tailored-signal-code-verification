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
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkInterned

/-!
Text-walk slice lemmas for blocks `0..200` of `lsInternedMultiLib` against `mutantCliElfImage` in
the `cheval26-small-subgroup` mutant binary.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfImage)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec (SlicesTextVarOk)

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"

theorem f3Ls_textWalk_00 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 0 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_01 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 40 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_02 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 80 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_03 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 120 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_04 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 160 40 = true := by
  rfl_kernel

theorem f3Ls_slicesTextVarOk_04 :
    SlicesTextVarOk lsInternedMultiLib mutantLsLayout mutantCliElfImage 200 :=
  (((((SlicesTextVarOk.zero.step
    f3Ls_textWalk_00).step
    f3Ls_textWalk_01).step
    f3Ls_textWalk_02).step
    f3Ls_textWalk_03).step
    f3Ls_textWalk_04)

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
