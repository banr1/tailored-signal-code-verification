/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.BugInjectionMutant
public meta import GeneratedLean.BugInjectionMutant
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkRefl1
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkRefl2
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkWalkA

/-!
Aggregates `MutantLinkRefl1`, `MutantLinkRefl2`, and `MutantLinkWalkA` for the
`cheval26-small-subgroup` mutant binary and derives `ls_toMultiPlacedLib_eq`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink

open Arm64

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"

theorem ls_toMultiPlacedLib_eq :
    CryptoVerification.SignalSession.libsignalSessionLib =
      lsInternedMultiLib.toMultiPlacedLib :=
  Obj.Interned.toMultiPlacedLib_of_fast ls_fast_eq ls_ids_ok ls_names_len ls_ext_ok

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
