/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataGen
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl1
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Interned `MultiLayout` and Symbol-ID Reflection Shard 2

Defines `f3LsLayout` and `f3LsMpl` and proves symbol-name, ID-bound, and relocation-inversion
step checks for `lsInternedMultiLib`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData

open Arm64 Arm64.Obj Arm64.Obj.Interned

noncomputable section ReflectionLemmas

open ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.SignalSession
  (cliDehookedSymsPlaced libsignalSessionLib lsRustNoAllocShimSymCli)
open LibsignalBinary.Heap.Fine
  (f3MallocngMpl f3StdLayout f3StubNoShimAddr)
open VerifiedLibraries.Mallocng.Proofs
  (mallocngMultiL mallocngNameChars)


/-- Interned `MultiLayout` for `lsInternedMultiLib` matching `f3TrialElf`. -/
def f3LsLayout : Obj.Interned.MultiLayout where
  bases := f3LsBlockBases
  addrs := f3LsSymAddrs

/-- Concrete `MultiPlacement` witness for `libsignalSessionLib` in `f3TrialElf`. -/
noncomputable def f3LsMpl : Obj.MultiPlacement :=
  f3LsLayout.toMultiPlacement lsInternedMultiLib.names

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
    Obj.Interned.checkMultiMetaCoreFastB lsInternedMultiLib f3LsLayout lsNameChars = true := by
  rfl_kernel

theorem f3Ls_metaData_ok :
    Obj.Interned.checkMultiMetaDataFastB lsInternedMultiLib f3LsLayout = true := by
  rfl_kernel

end ReflectionLemmas

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
