/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SlotsZ6Pure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import VCVio.Prelude.Core

/-!
# Per-Explanation Receiver Invariant Bundle

Bundles the per-explanation receiver key-length, non-low-order, skipped-key byte-freshness,
history, and randomness-freshness invariants at a fixed `(g, ms)`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR

cref_open
cref_open_tr

open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR

/-- Per-explanation receiver invariant bundle at `(g, ms)`. -/
structure RecvAtFacts (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) : Prop where
  lens : RecvRkLensAll interpretation S g r₀ ms
  notLow : RecvRkNotLowAll interpretation S g r₀ ms
  byteFresh : SkippedInstallByteFresh interpretation S g r₀ ms
  hist : G1.RecvHistInvTR interpretation S g r₀ ms
  fresh : TRRecvFreshAll r₀ ms

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
