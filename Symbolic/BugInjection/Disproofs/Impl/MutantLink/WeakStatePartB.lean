/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.BugInjectionMutant
public meta import GeneratedLean.BugInjectionMutant
public import GeneratedLean.BugInjectionMutantImage
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WeakStateWalkB1
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WeakStateWalkB2
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WeakStateMallocng
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkInterned

/-!
# Tail Text-Walk Combiner for `cheval26-weak-state`

Re-exports `WeakStateWalkB1` (blocks `200..400`), `WeakStateWalkB2` (blocks `400..mutantBlocksLen`),
and `WeakStateMallocng` (`mutant_linkedAt_mg`), and combines slices `05..15c` in
`f3Ls_slicesTextVarOk_of_partA`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

open CryptoVerification.BugInjection (mutantCliElfImage)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec (SlicesTextVarOk)

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

/-- Extends `SlicesTextVarOk` from block `200` to `mutantBlocksLen` using text-walk slices `05..15c`. -/
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

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
