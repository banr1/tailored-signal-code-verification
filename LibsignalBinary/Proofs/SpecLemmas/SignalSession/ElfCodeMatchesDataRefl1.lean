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


theorem ls_fast_eq :
    libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLibFast lsSharedExterns := by
  rfl_kernel

end ReflectionLemmas

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
