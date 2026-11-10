/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenInterned
public import Arm64
public import GeneratedLean.BugInjectionMutant
public meta import GeneratedLean.BugInjectionMutant
public import GeneratedLean.LibsignalSessionPlacedObj
public import ProofLib.Placed.Multi
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkData

/-!
Interned `MultiLib` reflection (`lsSharedExterns` and `lsInternedMultiLib` over `lsNames`) for
`libsignalSessionLib` in the `cheval26-weak-state` mutant, shared by `MutantLinkPartA` and
`WeakStatePartB`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

gen_mutant_ls_interned lsNames

example : lsInternedMultiLib.names = lsNames := rfl

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
