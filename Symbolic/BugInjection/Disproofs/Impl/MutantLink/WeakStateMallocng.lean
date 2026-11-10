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
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.F3LayoutData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public import Symbolic.BugInjection.Disproofs.Impl.MutantParse
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars
public import Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkData
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned

/-!
# `mallocngLib.LinkedAt` Proof for `cheval26-weak-state`

Proves `VerifiedLibraries.mallocngLib.LinkedAt mutantCliElfBytes mutantMmpl` for the
`cheval26-weak-state` mutant ELF via `checkMultiVarSliced_spec` and kernel-reduced slice checks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfBytes mutantCliElfImage)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.F3LayoutData (f3MallocngMly)
open Symbolic.BugInjection.Disproofs.Impl.MutantParse (mutantCliElf_parse)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.MutantSymChars (
  mutantCliElfSymChars mutantCliElf_symbols_eq
)
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec (
  SlicesTextVarOk checkMultiVarSliced_spec
)
open VerifiedLibraries.Mallocng.Proofs (
  mallocngMultiL mallocngMultiL_names mallocngMultiL_toMultiPlacedLib mallocngNameChars
)

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

theorem mutant_mallocng_metaCore_ok :
    Obj.Interned.checkMultiMetaCoreFastB mallocngMultiL f3MallocngMly
      mallocngNameChars = true := by
  rfl_kernel

theorem mutant_mallocng_metaData_ok :
    Obj.Interned.checkMultiMetaDataFastB mallocngMultiL f3MallocngMly = true := by
  rfl_kernel

theorem mutant_mallocng_metaExports_ok :
    Obj.Interned.checkMultiMetaExportsFastB mallocngMultiL f3MallocngMly
      mallocngNameChars mutantCliElfSymChars = true := by
  rfl_kernel

theorem mutant_mallocng_meta_ok :
    Obj.Interned.checkMultiMetaFastB mallocngMultiL f3MallocngMly
      mallocngNameChars mutantCliElfSymChars = true :=
  Obj.Interned.checkMultiMetaFastB_of_parts
    mutant_mallocng_metaCore_ok mutant_mallocng_metaData_ok mutant_mallocng_metaExports_ok

theorem mutant_mallocng_dataWalk_ok :
    Obj.Interned.checkMultiDataWalkFastB mallocngMultiL f3MallocngMly
      mutantCliElfImage = true := by
  rfl_kernel

theorem mutant_mallocng_blocks_bound :
    Nat.ble mallocngMultiL.blocks.length 24 = true := by
  rfl_kernel

theorem mutant_mallocng_textWalk_00 :
    Obj.Interned.checkMultiTextSliceB mallocngMultiL f3MallocngMly
      mutantCliElfImage 0 24 = true := by
  rfl_kernel

theorem mutant_mallocng_slicesTextVarOk :
    SlicesTextVarOk mallocngMultiL f3MallocngMly mutantCliElfImage 24 :=
  SlicesTextVarOk.zero.step mutant_mallocng_textWalk_00

theorem mutant_mallocng_placed :
    VerifiedLibraries.mallocngLib.Placeable mutantMmpl ∧
    VerifiedLibraries.mallocngLib.InElf mutantCliElfImage mutantMmpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mutantMmpl :=
  checkMultiVarSliced_spec mallocngMultiL_toMultiPlacedLib.symm
    mallocngMultiL_names mutantCliElf_symbols_eq
    mutant_mallocng_meta_ok mutant_mallocng_dataWalk_ok
    mutant_mallocng_blocks_bound mutant_mallocng_slicesTextVarOk

/-- `VerifiedLibraries.mallocngLib` is linked at `mutantMmpl` in the `cheval26-weak-state` mutant ELF. -/
theorem mutant_linkedAt_mg :
    VerifiedLibraries.mallocngLib.LinkedAt mutantCliElfBytes mutantMmpl :=
  ⟨mutantCliElfImage, mutantCliElf_parse,
    mutant_mallocng_placed.1, mutant_mallocng_placed.2.1⟩

end Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
