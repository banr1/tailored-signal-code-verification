/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Tests.CliGuards
public import Symbolic.Tests.SetupKyberGuard
public import Symbolic.Tests.ModelNonVacuity
public import Symbolic.Tests.ForwardSecrecyTour
public import Symbolic.Tests.Nonvacuity
public import Symbolic.Tests.CliNonvacuity
public import Symbolic.Tests.ExternWitness
public import Symbolic.Tests.SpecDuplicateGuards
public import Symbolic.Tests.HwAttackerKnowsNonVacuity
public import Symbolic.Tests.RejKeyNonDerivability
-- Composed protocol model and security (`PQXDH ∘ SPQR ∘ Triple Ratchet`)
public import Symbolic.Theorems.ModelSecurity
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
public import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness
public import Symbolic.Proofs.Tests.Refinement.Cli.Cheval26WeakState
public import Symbolic.Proofs.Tests.Refinement.Cli.StmtAuditSym
public import Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks
public import Symbolic.Proofs.Tests.Refinement.Cli.SDetGuard
public import Symbolic.Proofs.Tests.Refinement.Cli.SetupInitDirsGuard
public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuity
public import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
-- Parametric CLI refinement and security (`CliElfLib` builds the `cliElfBytes` instantiations)
public import Symbolic.Theorems.RefinementPreservation
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurity
public import Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedG
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed

/-!
# Symbolic Library Umbrella

Root of the default `Symbolic` library: the DyLean protocol model of libsignal, its parametric
refinement to the AArch64 `signal-session` binary, the default-target theorems in
`Symbolic/Theorems/`, and the guards and non-vacuity witnesses in `Symbolic/Tests/`. Imports
maximal modules only; `CliElfLib` builds `Symbolic/Theorems/Refinement.lean` and
`Symbolic/Theorems/Security.lean`.
-/

@[expose] public section
