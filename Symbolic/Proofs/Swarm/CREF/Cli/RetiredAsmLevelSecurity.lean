/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
public import Symbolic.Specifications.Security.Model

/-!
# Move-Based Assembly-Level Security Definitions

Move-based counterparts (`*Moves`) of the trace-level security predicates over `runTraceMoves`,
used as intermediate targets before bridging to the unified-attacker specification.
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)

section
variable (r : ProtocolSetup) (ms : List Move)

/-- Public setup messages and terms from `send`, `recv`, or `leak` entries of `runVis r ms`. -/
def HwAttackerObservesMoves (t : DY.Bytes) : Prop :=
  t ∈ setupSent r ∨
  ∃ v ∈ runVis r ms, t ∈ v.terms ∧
    match v.kind with
    | .send | .recv | .leak => True
    | .pt | .rng | .accept => False

/-- Dolev-Yao attacker closure of `HwAttackerObservesMoves r ms`. -/
def HwAttackerKnowsMoves (t : DY.Bytes) : Prop :=
  Fixpoint.mkLeastFixpoint
    (fun known b => AttackerKnowledge.attackerKnowledge.pred known b ∨ HwAttackerObservesMoves r ms b) t

end

/-- Security queries (`Security.AllSecurityQueriesHold`) on `runTraceMoves r ms` for every
`MatchedPrefix` explanation of `τ`. -/
def AllSecurityQueriesHoldOnHwTraceMoves (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (τ : List MachineEvent) : Prop :=
  ∀ g ms, MatchedPrefix interpretation r S who g ms τ →
    Security.AllSecurityQueriesHold (runTraceMoves r ms) (HwAttackerKnowsMoves r ms)

end DY.Libsignal.Composed.Refinement

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (Inputs Outcome)

/-- Whole-protocol security over `CliTracesMoves` from initial directory snapshots `dirs`,
parameterized by run relation `R`. -/
def CompAsmSecurityCliRMoves {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop)
    (dirs : ExternInterpretation → ProtocolSetup → Participant → DirectorySnapshot) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : ω, Agree interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∃ S : OpaqueSymbolSemantics, ∀ (τ : List MachineEvent) (calls : List (Participant × Bool)),
    CliTracesMoves (R interp W) interp r (CliTurn.init (dirs interp r)) τ calls →
    ∀ (who : List Participant) (ok : Nat → Bool), CallsMatchSchedules calls who ok →
      ((∃ τhw g ms, CoinSplit τ τhw ∧ MatchedPrefix interp r S who g ms τhw) ∧
          ∀ τhw, CoinSplit τ τhw → AllSecurityQueriesHoldOnHwTraceMoves interp r S who τhw) ∨
        CollisionAfterExplainedPrefixMoves interp r S who ok τ

/-- `CompAsmSecurityCliRMoves` instantiated at `initDirs`. -/
def CompAsmSecurityCliMoves {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) : Prop :=
  CompAsmSecurityCliRMoves Agree R initDirs

end DY.Libsignal.Composed.Refinement.Cli
