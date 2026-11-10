/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTracePlaced
public import GeneratedLean.BugInjectionMutant
public import GeneratedLean.BugInjectionMutantImage
public import Symbolic.BugInjection.Disproofs.Impl.MutantParse

/-!
Reduces the placed `ImplHalf` obligation on `mutantCliElfBytes` for the `cheval26-weak-state`
witness to `ElfFullValidPlaced` on `mutantCliElfImage` and the seven per-call `cliRunPlacedSig`
executions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.ImplPlaced

set_option linter.dupNamespace false

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.BugInjection (mutantCliElfBytes mutantCliElfImage)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection (cliCompShapePlaced)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0 cliCompFitsPinned)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
  (FileList ValidStepFiles wsInp0 wsInp1 wsInp2 wsInp3 wsInp4 wsInp5 wsInp6
   wsOut0 wsOut1 wsOut2 wsOut3 wsOut4 wsOut5 wsOut6)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTracePlaced
  (impl_half_pinned_of_seven_calls_placed)
open Symbolic.BugInjection.Disproofs.Impl.MutantParse (mutantCliElf_parse)

theorem impl_half_bytes_placed_of_runs
    {mpl mmpl : MultiPlacement} {fs : ElfFullSpecPlaced}
    (files0 files1 files2 files3 files4 files5 files6 : FileList)
    (hValid : ValidStepFiles files0 files1 files2 files3 files4 files5 files6 = true)
    (hv : ElfFullValidPlaced mpl mmpl mutantCliElfImage fs)
    (hRun0 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 wsInp0 = some (wsOut0 files0))
    (hRun1 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp1 files0) = some (wsOut1 files1))
    (hRun2 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp2 files1) = some (wsOut2 files2))
    (hRun3 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 wsInp3 = some (wsOut3 files3))
    (hRun4 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp4 files2) = some (wsOut4 files4))
    (hRun5 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp5 files4) = some (wsOut5 files5))
    (hRun6 : ∀ {elf : ElfImage}, ElfFullValidPlaced mpl mmpl elf fs →
      cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp6 files3) = some (wsOut6 files6)) :
    ∀ elf : ElfImage, ElfImage.parse mutantCliElfBytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf
        (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup)
        elf Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace := by
  intro elf hparse
  cases mutantCliElf_parse.symm.trans hparse
  exact impl_half_pinned_of_seven_calls_placed mpl mmpl mutantCliElfImage
    files0 files1 files2 files3 files4 files5 files6 hValid
    (hRun0 hv) (hRun1 hv) (hRun2 hv) (hRun3 hv) (hRun4 hv) (hRun5 hv) (hRun6 hv)

end Symbolic.BugInjection.Disproofs.Impl.WeakState.ImplPlaced
