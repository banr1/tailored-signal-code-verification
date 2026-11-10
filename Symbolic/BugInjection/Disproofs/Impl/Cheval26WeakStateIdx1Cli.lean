/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShapePlaced
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Nodes
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.NodesPlaced
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh

/-!
# Disproof Carrier for `cheval26-weak-state`

Proves `¬ SignalSessionSecurePlaced mutantCliElfBytes` (and `disproof_secureFor`) for the
`cheval26-weak-state` mutant from the `cheval26-weak-state-idx1-cli` witness, combining the linked
placements, the symbolic specification half, the placed implementation half, and coin freshness.
Both generated witness obligations (`Cheval26WeakStateIdx1Cli` and `Cheval26WeakStateCli`) discharge
to `disproof` via `scripts/bug_injection.py`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.Cheval26WeakStateIdx1Cli

open Symbolic.BugInjection
  (not_signalSessionSecureFor_placed_of_witness not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink (mutantMpl mutantMmpl)
open CryptoVerification.BugInjection (mutantCliElfBytes)

/-- Refutes `SignalSessionSecureFor` on the `cheval26-weak-state` mutant at its linked placements. -/
theorem disproof_secureFor :
    ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse mutantCliElfBytes = .ok elf →
      ¬ DY.Libsignal.Composed.Security.SignalSessionSecureFor
          DY.Libsignal.Composed.Refinement.Cli.HooksMatchInterpretation
          (DY.Libsignal.Composed.Refinement.Cli.elfRelPlaced mutantMpl mutantMmpl elf) :=
  not_signalSessionSecureFor_placed_of_witness
    WeakState.Nodes.spec_half_pinned WeakState.NodesPlaced.impl_half_bytes_placed
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_cheval26WeakStateIdx1Cli

/-- Refutes `SignalSessionSecurePlaced` on the `cheval26-weak-state` mutant ELF bytes. -/
theorem disproof : ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced mutantCliElfBytes :=
  not_signalSessionSecurePlaced_of_witness
    WeakState.MutantLink.mutant_linkedAt_ls WeakState.MutantLink.mutant_linkedAt_mg
    WeakState.Nodes.spec_half_pinned WeakState.NodesPlaced.impl_half_bytes_placed
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_cheval26WeakStateIdx1Cli

end Symbolic.BugInjection.Disproofs.Impl.Cheval26WeakStateIdx1Cli
