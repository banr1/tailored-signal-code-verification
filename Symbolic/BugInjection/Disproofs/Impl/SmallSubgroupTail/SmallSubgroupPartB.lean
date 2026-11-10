/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import GeneratedLean.BugInjectionMutant
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec
public meta import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroupTail.SmallSubgroupWalkB1
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroupTail.SmallSubgroupWalkB2
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroupTail.SmallSubgroupMallocng

/-!
# `cheval26-small-subgroup` Tail Text-Walk Combiner and `mallocngLib` Link

Re-exports text-walk slices `05..15c` (`200..mutantBlocksLen`) and `mutant_linkedAt_mg`, and
combines those slices with blocks `0..200` in `f3Ls_slicesTextVarOk_of_partA`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

open CryptoVerification.BugInjection (mutantCliElfImage)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec (SlicesTextVarOk)

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"
#guard CryptoVerification.BugInjection.mutantCliElfSha256 ==
  Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData.f3TrialElfSha256

/-- Extends `SlicesTextVarOk` from blocks `0..200` to `0..mutantBlocksLen` using slices `05..15c`. -/
theorem f3Ls_slicesTextVarOk_of_partA
    (h04 : SlicesTextVarOk lsInternedMultiLib mutantLsLayout mutantCliElfImage 200) :
    SlicesTextVarOk lsInternedMultiLib mutantLsLayout mutantCliElfImage mutantBlocksLen :=
  (((((((((((((h04.step
    f3Ls_textWalk_05).step
    f3Ls_textWalk_06).step
    f3Ls_textWalk_07).step
    f3Ls_textWalk_08).step
    f3Ls_textWalk_09).step
    f3Ls_textWalk_10).step
    f3Ls_textWalk_11).step
    f3Ls_textWalk_12).step
    f3Ls_textWalk_13).step
    f3Ls_textWalk_14).step
    f3Ls_textWalk_15a).step
    f3Ls_textWalk_15b).step
    f3Ls_textWalk_15c)

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
