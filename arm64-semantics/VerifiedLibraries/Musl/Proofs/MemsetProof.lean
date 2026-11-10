/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.Musl.Proofs.Code
public import VerifiedLibraries.Musl.Proofs.Common
public import VerifiedLibraries.Musl.Proofs.MemsetSym

/-!
# Verification of `musl` AArch64 `memset`

Connects the symbolic execution of `memsetWords` (`MemsetSym`) to `memsetSpec` and any valid
placement of `VerifiedLibraries.muslStringLib`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

theorem memset_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memsetWords) :
    subroutine_ok prog a memsetSpec :=
  memset_codeAt_ok_sym prog a hc

private theorem memset_image_hasWords (pl : Obj.Placement)
    (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    (muslStringProg pl hooks).hasWords ((muslStringProg pl hooks).fnAddr "memset") memsetWords :=
  muslStringProg_hasWords_relocFree hP rfl (by decide +kernel)

theorem memset_image_ok (pl : Obj.Placement) (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    (muslStringProg pl hooks).subroutineOk "memset" memsetSpec :=
  memset_codeAt_ok _ _ (memset_image_hasWords pl hooks hP)

end VerifiedLibraries.Musl
