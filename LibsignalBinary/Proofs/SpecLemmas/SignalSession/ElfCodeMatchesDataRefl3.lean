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
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

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


theorem ls_relocInv_ok :
    Obj.Interned.checkRelocInvStepsB lsInternedMultiLib lsNameChars lsRelocInvSteps = true := by
  rfl_kernel

theorem f3LsMpl_relax_false (i o : Nat) : f3LsMpl.relax i o = false := by
  cases i <;> rfl

theorem ls_namesNodup_ok : Obj.Interned.namesNodup lsNameChars = true := by
  rfl_kernel

theorem ls_names_nodup : lsInternedMultiLib.names.Nodup :=
  Obj.Interned.nodup_of_namesNodup ls_names_eq ls_namesNodup_ok

theorem ls_idsOk : lsInternedMultiLib.idsOk = true :=
  (Obj.Interned.multiIdsOkFast_eq lsInternedMultiLib).symm.trans ls_ids_ok

theorem ls_blockSymsMatch_ok :
    Obj.Interned.blockSymsMatchB lsInternedMultiLib f3LsLayout = true := by
  rfl_kernel

theorem ls_names_len_exact : lsInternedMultiLib.names.length = f3LsNamesLen := by
  rfl_kernel

theorem f3LsBlocksLen_ge_600 :
    Nat.ble 600 f3LsBlocksLen = true := by
  rfl_kernel

theorem f3LsBlockBases_len :
    Nat.beq f3LsBlockBases.length f3LsBlocksLen = true := by
  rfl_kernel

theorem lsInternedBlocks_len :
    Nat.beq lsInternedMultiLib.blocks.length f3LsBlocksLen = true := by
  rfl_kernel

theorem libsignalBlocks_len :
    Nat.beq libsignalSessionLib.blocks.length f3LsBlocksLen = true := by
  rw [ls_toMultiPlacedLib_eq, Obj.Interned.MultiLib.toMultiPlacedLib_blocks, List.length_map]
  exact lsInternedBlocks_len

theorem f3LsBlockBases_pos :
    (f3LsBlockBases.all fun b => Nat.blt 0 b.toNat) = true := by
  rfl_kernel

end ReflectionLemmas

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
