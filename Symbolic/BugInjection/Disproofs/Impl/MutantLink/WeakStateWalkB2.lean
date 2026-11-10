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
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkInterned

/-!
# `cheval26-weak-state` Text-Walk Slices `10..15c`

Checks text-walk slices covering blocks `400..mutantBlocksLen` of `lsInternedMultiLib` against
`mutantCliElfImage`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfImage)

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

theorem f3Ls_textWalk_10 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 400 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_11 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 440 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_12 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 480 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_13 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 520 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_14 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 560 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_15a :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 600 16 = true := by
  rfl_kernel

theorem f3Ls_textWalk_15b :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 616 2 = true := by
  rfl_kernel

theorem f3Ls_textWalk_15c :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib mutantLsLayout
      mutantCliElfImage 618 (mutantBlocksLen - 618) = true := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
