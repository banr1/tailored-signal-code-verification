/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShapePlaced
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Nodes
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.NodesPlaced
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh

/-!
# Disproof Carrier for `cheval26-small-subgroup`

Proves `¬ SignalSessionSecurePlaced mutantCliElfBytes` (and `disproof_secureFor`) for the
`cheval26-small-subgroup` mutant from the `cheval26-small-subgroup-high-bit-cli` witness, combining
the linked placements, the symbolic specification half, the placed implementation half, and coin
freshness. Both generated witness obligations (`Cheval26SmallSubgroupHighBitCli` and
`Cheval26SmallSubgroupTorsionCli`) discharge to `disproof` via `scripts/bug_injection.py`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.Cheval26SmallSubgroupHighBitCli

open Symbolic.BugInjection
  (not_signalSessionSecureFor_placed_of_witness not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink (mutantMpl mutantMmpl)
open CryptoVerification.BugInjection (mutantCliElfBytes)

/-- Refutes `SignalSessionSecureFor` on the `cheval26-small-subgroup` mutant at its linked placements. -/
theorem disproof_secureFor :
    ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse mutantCliElfBytes = .ok elf →
      ¬ DY.Libsignal.Composed.Security.SignalSessionSecureFor
          DY.Libsignal.Composed.Refinement.Cli.HooksMatchInterpretation
          (DY.Libsignal.Composed.Refinement.Cli.elfRelPlaced mutantMpl mutantMmpl elf) :=
  not_signalSessionSecureFor_placed_of_witness
    SmallSubgroup.Nodes.spec_half_pinned SmallSubgroup.NodesPlaced.impl_half_bytes_placed
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_cheval26SmallSubgroupHighBitCli

/-- Refutes `SignalSessionSecurePlaced` on the `cheval26-small-subgroup` mutant ELF bytes. -/
theorem disproof : ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced mutantCliElfBytes :=
  not_signalSessionSecurePlaced_of_witness
    SmallSubgroup.MutantLink.mutant_linkedAt_ls SmallSubgroup.MutantLink.mutant_linkedAt_mg
    SmallSubgroup.Nodes.spec_half_pinned SmallSubgroup.NodesPlaced.impl_half_bytes_placed
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_cheval26SmallSubgroupHighBitCli

end Symbolic.BugInjection.Disproofs.Impl.Cheval26SmallSubgroupHighBitCli
