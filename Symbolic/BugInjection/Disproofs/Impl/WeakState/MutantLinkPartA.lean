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
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkInterned
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkRefl1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkWalk04

/-!
Interned-library reflection (`ls_toMultiPlacedLib_eq`), metadata and data-section checks
(`f3Ls_meta_ok`, `f3Ls_dataWalk_ok`, `f3Ls_blocks_bound`), and text-walk slices `00..04`
(re-exported from `MutantLinkWalk04`) for `libsignalSessionLib` in the `cheval26-weak-state`
mutant ELF.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

open Arm64 Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfImage)
open CryptoVerification.SignalSession (libsignalSessionLib)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars (mutantCliElfSymChars)

theorem ls_names_eq : lsInternedMultiLib.names = lsNameChars.map String.ofList := by
  rfl_kernel

theorem ls_ids_ok : Obj.Interned.multiIdsOkFast lsInternedMultiLib = true := by
  rfl_kernel

theorem ls_names_len : Nat.blt lsInternedMultiLib.names.length 1048576 = true := by
  rfl_kernel

theorem ls_ext_ok :
    Obj.Interned.blocksSharedExternsOk lsInternedMultiLib lsSharedExterns = true := by
  rfl_kernel

theorem ls_toMultiPlacedLib_eq :
    libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLib :=
  Obj.Interned.toMultiPlacedLib_of_fast ls_fast_eq ls_ids_ok ls_names_len ls_ext_ok

theorem f3Ls_metaCore_ok :
    Obj.Interned.checkMultiMetaCoreFastB lsInternedMultiLib mutantLsLayout lsNameChars = true := by
  rfl_kernel

theorem f3Ls_metaData_ok :
    Obj.Interned.checkMultiMetaDataFastB lsInternedMultiLib mutantLsLayout = true := by
  rfl_kernel

theorem f3Ls_metaExports_ok :
    Obj.Interned.checkMultiMetaExportsFastB lsInternedMultiLib mutantLsLayout
      lsNameChars mutantCliElfSymChars = true := by
  rfl_kernel

theorem f3Ls_meta_ok :
    Obj.Interned.checkMultiMetaFastB lsInternedMultiLib mutantLsLayout
      lsNameChars mutantCliElfSymChars = true :=
  Obj.Interned.checkMultiMetaFastB_of_parts
    f3Ls_metaCore_ok f3Ls_metaData_ok f3Ls_metaExports_ok

theorem f3Ls_dataWalk_ok :
    Obj.Interned.checkMultiDataWalkFastB lsInternedMultiLib mutantLsLayout mutantCliElfImage = true := by
  rfl_kernel

theorem f3Ls_blocks_bound :
    Nat.ble lsInternedMultiLib.blocks.length mutantBlocksLen = true := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
