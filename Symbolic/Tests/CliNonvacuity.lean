/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ExternInterpretationProofDefs
public import Symbolic.Tests.Nonvacuity.SetupTrace
public import Symbolic.Tests.Nonvacuity.HonestHandshakeWithoutOpk
public import Symbolic.Tests.Nonvacuity.HonestHandshakeWithOpk
public import Symbolic.Tests.Nonvacuity.HonestSession
public import Symbolic.Tests.Nonvacuity.ExposedSession
public import LibsignalBinary.Specifications.SignalSession.PqDir
import Symbolic.Proofs.Tests.CliNonvacuity

/-!
# CLI-Level Reachability of Example Protocol Traces

Defines `CliTraceReachable` and states `cli_nonvacuity_examples_reachable`, the CLI-level counterpart
to `Symbolic.Tests.Nonvacuity.nonvacuity_examples_reachable` for the five example traces in
`Symbolic/Tests/Nonvacuity/`, together with a negative check on `CoinsFresh`.
Proofs live in `Symbolic.Proofs.Tests.CliNonvacuity`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.CliNonvacuity

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   ExternInterpretationTotalOnUsedSymbols ProtocolSetupWF Explains runTrace)
open DY.Libsignal.Composed.Refinement.Cli
  (ExternContractsHoldCli HooksMatchInterpretation CliTurn initDirs CliTraces runFnToRelation
   InvertsGuarded CoinsFresh CollisionAfterExplainedPrefix)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession (Address CliRun CliHooks CliSpecPqxdh)
open Symbolic.Tests.Nonvacuity
  (keySetupTrace honestHandshakeWithoutOpkTrace honestHandshakeWithOpkTrace
   honestSessionTrace exposedSessionTrace)

/-- `CliSpecPqxdh` is satisfiable for every `X` and `W`, so the quantification over `run` in
`CliTraceReachable` is non-vacuous. -/
theorem cliSpecPq_satisfiable (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    ∃ run : CliRun, CliSpecPqxdh run X ⟨W.C, W.Q⟩ :=
  Symbolic.Proofs.Tests.CliNonvacuity.cliSpecPq_satisfiable_proof X W

/-- Reachability of a symbolic trace `target` from `initDirs interp r` via exit-`0` `signal-session`
CLI runs (and optional environment leaks) explained by `(g, ss, vis)` with `runTrace r ss = target`
under every `CliSpecPqxdh`-compliant runner, satisfying the hypotheses of `CompRefinesCli` and
`SignalSessionSecureFor` without triggering `CollisionAfterExplainedPrefix`. -/
def CliTraceReachable (target : ExecTrace) : Prop :=
  ∃ (interp : ExternInterpretation) (W : CliHooks)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (evs : List CliEvent)
    (g : Ghost) (ss : List Step) (vis : List VisEntry),
    (∀ (X : UnreachedPqxdhPrimitives) (run : CliRun), CliSpecPqxdh run X ⟨W.C, W.Q⟩ →
      CliTraces (runFnToRelation run) interp r (CliTurn.init (initDirs interp r)) evs) ∧
    (∀ ev : RunEvent, .run ev ∈ evs → ∃ out, ev.exit = some (0, out)) ∧
    Explains interp r S g ss vis evs ∧
    runTrace r ss = target ∧
    ExternInterpretationTotalOnUsedSymbols interp ∧
    ExternContractsHoldCli interp ∧
    HooksMatchInterpretation interp W ∧
    ProtocolSetupWF r ∧
    InvertsGuarded interp r evs ∧
    CoinsFresh r evs ∧
    ¬ CollisionAfterExplainedPrefix interp r S evs

/-- Each of the five example protocol traces in `Symbolic/Tests/Nonvacuity/` satisfies
`CliTraceReachable`. -/
theorem cli_nonvacuity_examples_reachable :
    CliTraceReachable keySetupTrace ∧
    CliTraceReachable honestHandshakeWithoutOpkTrace ∧
    CliTraceReachable honestHandshakeWithOpkTrace ∧
    CliTraceReachable honestSessionTrace ∧
    CliTraceReachable exposedSessionTrace :=
  Symbolic.Proofs.Tests.CliNonvacuity.cli_nonvacuity_examples_reachable_proof

/-- Two exit-`0` `init` runs with identical `coins` violate `CoinsFresh` because their clamped
ephemeral coin draws collide. -/
theorem not_coinsFresh_two_inits_same_coins (r : ProtocolSetup) (party₁ party₂ : String)
    (peer₁ peer₂ : Address) (bundle₁ bundle₂ : String) (in₁ in₂ coins out₁ out₂ : HwBytes) :
    ¬ CoinsFresh r
      [.run { party := party₁, cmd := .init peer₁ bundle₁, input := in₁, coins := coins,
              exit := some (0, out₁) },
       .run { party := party₂, cmd := .init peer₂ bundle₂, input := in₂, coins := coins,
              exit := some (0, out₂) }] :=
  Symbolic.Proofs.Tests.CliNonvacuity.not_coinsFresh_two_inits_same_coins_proof
    r party₁ party₂ peer₁ peer₂ bundle₁ bundle₂ in₁ in₂ coins out₁ out₂

end Symbolic.Tests.CliNonvacuity
