/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.ImplPlaced
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Base
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Files
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call5
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call6
public import GeneratedLean.BugInjectionMutant
-- `#guard` evaluates at compile time, so it needs the mutant's constants at the meta stage too.
public meta import GeneratedLean.BugInjectionMutant

/-!
Placed implementation half (`impl_half_bytes_placed`) of the `cheval26-weak-state` security
disproof for the `Cheval26WeakStateIdx1Cli` witness at `(mutantMpl, mutantMmpl)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.NodesPlaced

open Symbolic.BugInjection (cliCompShapePlaced)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (cliCompFitsPinned)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink (mutantMpl mutantMmpl)
open CryptoVerification.BugInjection (mutantCliElfBytes)

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

/-- Any ELF image parsed from `mutantCliElfBytes` produces the `Cheval26WeakStateIdx1Cli` trace at
`(mutantMpl, mutantMmpl)`. -/
theorem impl_half_bytes_placed :
    ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse mutantCliElfBytes = .ok elf →
      (cliCompShapePlaced mutantMpl mutantMmpl).ImplHalf
        (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup)
        elf Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace :=
  Symbolic.BugInjection.Disproofs.Impl.WeakState.ImplPlaced.impl_half_bytes_placed_of_runs
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles0
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles1
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles2
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles3
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles4
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles5
    Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs.wsFiles6
    Symbolic.BugInjection.Disproofs.Impl.WeakState.Files.wsFiles_valid
    Symbolic.BugInjection.Disproofs.Impl.WeakState.Base.wsSpec_valid
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call0.wsRun0 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call1.wsRun1 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.wsRun2 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call3.wsRun3 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.wsRun4 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call5.wsRun5 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.WeakState.Call6.wsRun6 hv)

end Symbolic.BugInjection.Disproofs.Impl.WeakState.NodesPlaced
