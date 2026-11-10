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
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import Symbolic.BugInjection.Disproofs.Impl.MutantParse
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkPartA
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroupTail.SmallSubgroupPartB
public import VerifiedLibraries.Mallocng.Spec

/-!
Assembles `MutantLinkPartA` and `SmallSubgroupPartB` to prove `LinkedAt` witnesses for
`libsignalSessionLib` and `VerifiedLibraries.mallocngLib` against `mutantCliElfBytes` in the
`cheval26-small-subgroup` mutant binary.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"
#guard CryptoVerification.BugInjection.mutantCliElfSha256 ==
  Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.F3LayoutData.f3TrialElfSha256

open CryptoVerification.BugInjection (mutantCliElfBytes mutantCliElfImage)
open CryptoVerification.SignalSession (libsignalSessionLib)
open Symbolic.BugInjection.Disproofs.Impl.MutantParse (mutantCliElf_parse)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars (mutantCliElf_symbols_eq)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec (
  SlicesTextVarOk checkMultiVarSliced_spec
)

theorem f3Ls_slicesTextVarOk :
    SlicesTextVarOk lsInternedMultiLib mutantLsLayout mutantCliElfImage mutantBlocksLen :=
  f3Ls_slicesTextVarOk_of_partA f3Ls_slicesTextVarOk_04

/-- Placement, ELF residency, and data disjointness for `libsignalSessionLib` at `mutantMpl`. -/
theorem mutant_ls_placed :
    libsignalSessionLib.Placeable mutantMpl ∧
    libsignalSessionLib.InElf mutantCliElfImage mutantMpl ∧
    libsignalSessionLib.DataDisjoint mutantMpl :=
  checkMultiVarSliced_spec ls_toMultiPlacedLib_eq ls_names_eq
    mutantCliElf_symbols_eq f3Ls_meta_ok f3Ls_dataWalk_ok
    f3Ls_blocks_bound f3Ls_slicesTextVarOk

/-- `libsignalSessionLib` is linked into `mutantCliElfBytes` at `mutantMpl`. -/
theorem mutant_linkedAt_ls :
    CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt mutantCliElfBytes mutantMpl :=
  ⟨mutantCliElfImage, mutantCliElf_parse,
    mutant_ls_placed.1, mutant_ls_placed.2.1⟩

-- `mutant_linkedAt_mg` and `mutantMmpl_linkedIn` are re-exported via `SmallSubgroupPartB`.
#check (mutant_linkedAt_ls :
  CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt mutantCliElfBytes mutantMpl)
#check (mutant_linkedAt_mg :
  VerifiedLibraries.mallocngLib.LinkedAt mutantCliElfBytes mutantMmpl)
#check (mutantMmpl_linkedIn :
  VerifiedLibraries.mallocngLib.Placeable mutantMmpl ∧
    VerifiedLibraries.mallocngLib.InElf mutantCliElfImage mutantMmpl)

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
