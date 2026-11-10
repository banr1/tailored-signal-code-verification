/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
public import ProofLib.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Call-Start Counting and `CoinSplit` Invariance

Proves that `callStarts` ignores `.rng` events, is preserved under `CoinSplit`, and decomposes
`cliEntryEvents` into `cliInputEvent` followed by `.rng`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement.Cli (CliCall CoinSplit CallsMatchSchedules cliEntryEvents cliExitEvents bundleBlob)

theorem callStarts_eq_nil_of_no_recv_pt {evs : List MachineEvent}
    (h : ∀ e ∈ evs, eventKind e ≠ .recv ∧ eventKind e ≠ .pt) :
    callStarts evs = [] := by
  unfold callStarts
  rw [List.filter_eq_nil_iff]
  intro e he
  obtain ⟨h1, h2⟩ := h e he
  cases hk : eventKind e <;> simp_all

@[simp] theorem callStarts_map_rng (pieces : List HwBytes) :
    callStarts (pieces.map MachineEvent.rng) = [] :=
  callStarts_eq_nil_of_no_recv_pt fun e he => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp he; simp [eventKind]

theorem coinSplit_callStarts_eq {τ τhw : List MachineEvent} (h : CoinSplit τ τhw) :
    callStarts τhw = callStarts τ := by
  induction h with
  | nil => rfl
  | keep _ _ ih =>
    unfold callStarts at ih ⊢
    rw [List.filter_cons, List.filter_cons, ih]
  | split _ _ _ ih =>
    rw [callStarts_append, callStarts_map_rng, List.nil_append, ih]
    unfold callStarts
    simp [eventKind]

theorem coinSplit_callStarts_length_eq {τ τhw : List MachineEvent} (h : CoinSplit τ τhw) :
    (callStarts τhw).length = (callStarts τ).length :=
  congrArg List.length (coinSplit_callStarts_eq h)

/-- Input event of a `CliCall` (the unique `recv` or `pt` event at entry). -/
def cliInputEvent (c : CliCall) : MachineEvent :=
  match c.cmd with
  | .init _ _ =>
    .recv (((DY.Libsignal.Composed.Refinement.Cli.parseBundleFiles
      (CryptoVerification.SignalSession.filesOf c.bundle)).map bundleBlob).getD [])
  | .send _ => .pt c.stdin
  | .recv _ => .recv c.stdin

theorem cliEntryEvents_eq (c : CliCall) :
    cliEntryEvents c = [cliInputEvent c, .rng c.coins] := by
  unfold cliEntryEvents cliInputEvent
  cases c.cmd <;> rfl

end Symbolic.Swarm.CREF.CliPure
