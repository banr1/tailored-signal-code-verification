/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTracePlaced
public import GeneratedLean.BugInjectionMutant
public import GeneratedLean.BugInjectionMutantImage
public import Symbolic.BugInjection.Disproofs.Impl.MutantParse
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Files

/-!
Assembles the placed implementation half (`ImplHalf`) for the `Cheval26SmallSubgroupHighBitCli`
witness on `mutantCliElfBytes` from `mutantCliElf_parse`, exit-file validity, and the three placed
CLI call execution hypotheses.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.ImplPlaced

set_option linter.dupNamespace false

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.BugInjection (mutantCliElfBytes mutantCliElfImage)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection (cliCompShapePlaced)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0 cliCompFitsPinned)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace
  (hbInp0 hbInp1 hbInp2 hbOut0 hbOut1 hbOut2)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTracePlaced
  (impl_half_pinned_of_three_calls_placed)
open Symbolic.BugInjection.Disproofs.Impl.MutantParse (mutantCliElf_parse)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Files
  (ssFiles0 ssFiles1 hbFiles2 ssFiles0_valid ssFiles1_valid)

theorem impl_half_bytes_placed_of_runs
    {mpl mmpl : MultiPlacement} {fs : ElfFullSpecPlaced}
    (hv : ElfFullValidPlaced mpl mmpl mutantCliElfImage fs)
    (hRun0 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 hbInp0 = some (hbOut0 ssFiles0))
    (hRun1 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 (hbInp1 ssFiles0) = some (hbOut1 ssFiles1))
    (hRun2 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 hbInp2 = some (hbOut2 hbFiles2)) :
    ∀ elf : ElfImage, ElfImage.parse mutantCliElfBytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf
        (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
        elf Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  intro elf hparse
  cases mutantCliElf_parse.symm.trans hparse
  exact impl_half_pinned_of_three_calls_placed mpl mmpl mutantCliElfImage
    ssFiles0 ssFiles1 hbFiles2 ssFiles0_valid ssFiles1_valid
    (hRun0 hv) (hRun1 hv) (hRun2 hv)

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.ImplPlaced
