/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.ImplPlaced
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Base
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Call0
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Call1
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Call2
public import GeneratedLean.BugInjectionMutant
-- `#guard` evaluates at compile time, so it needs the mutant's constants at the meta stage too.
public meta import GeneratedLean.BugInjectionMutant

/-!
Placed implementation premise (`impl_half_bytes_placed`) of the security disproof for the
`Cheval26SmallSubgroupHighBitCli` witness under `cheval26-small-subgroup` at placements
`(mutantMpl, mutantMmpl)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.NodesPlaced

open Symbolic.BugInjection (cliCompShapePlaced)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (cliCompFitsPinned)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink (mutantMpl mutantMmpl)
open CryptoVerification.BugInjection (mutantCliElfBytes)

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"

/-- Parsing `mutantCliElfBytes` yields an ELF image whose execution at `(mutantMpl, mutantMmpl)`
produces `Cheval26SmallSubgroupHighBitCli.trace` under `cliCompFitsPinned setup`. -/
theorem impl_half_bytes_placed :
    ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse mutantCliElfBytes = .ok elf →
      (cliCompShapePlaced mutantMpl mutantMmpl).ImplHalf
        (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
        elf Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.ImplPlaced.impl_half_bytes_placed_of_runs
    Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Base.ssSpec_valid
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Call0.ssRun0 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Call1.ssRun1 hv)
    (fun hv => Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Call2.hbRun2 hv)

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.NodesPlaced
