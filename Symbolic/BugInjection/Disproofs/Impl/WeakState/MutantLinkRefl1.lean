/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkInterned
import GeneratedLean.LibsignalSessionObj

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

open Arm64 Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection
open CryptoVerification.SignalSession (libsignalSessionLib)

theorem ls_fast_eq :
    libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLibFast lsSharedExterns := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
