/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Lemmas
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure
import VCVio.Prelude.Core

/-!
# `CoinSplit` Inversion and `NoAdjRng` Lemmas

Head-inversion lemmas for `CoinSplit` on kept and `.rng` events, together with the `NoAdjRng`
predicate on `List MachineEvent`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.S1

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Inputs Outcome)

/-- No two consecutive events in `σ` are `.rng` events. -/
def NoAdjRng : List MachineEvent → Prop
  | [] => True
  | [_] => True
  | e₁ :: e₂ :: es => (eventKind e₁ ≠ .rng ∨ eventKind e₂ ≠ .rng) ∧ NoAdjRng (e₂ :: es)

/-- Inversion of `CoinSplit` on a non-`.rng` head event. -/
theorem coinSplit_cons_nonRng_iff {e : MachineEvent} {σ τ : List MachineEvent}
    (he : eventKind e ≠ .rng) :
    CoinSplit (e :: σ) τ ↔ ∃ τ', τ = e :: τ' ∧ CoinSplit σ τ' := by
  constructor
  · intro h
    cases h with
    | keep _ hcs => exact ⟨_, rfl, hcs⟩
    | split => exact absurd rfl he
  · rintro ⟨τ', rfl, hcs⟩
    exact .keep (fun b hb => he (by subst hb; rfl)) hcs

/-- Inversion of `CoinSplit` on an `.rng coins` head event. -/
theorem coinSplit_cons_rng_iff {coins : HwBytes} {σ τ : List MachineEvent} :
    CoinSplit (.rng coins :: σ) τ ↔
      ∃ (pieces : List HwBytes) (τ' : List MachineEvent),
        (∀ p ∈ pieces, p ≠ []) ∧ pieces.flatten <+: coins ∧
        τ = pieces.map MachineEvent.rng ++ τ' ∧ CoinSplit σ τ' := by
  constructor
  · intro h
    cases h with
    | keep hne _ => exact absurd rfl (hne coins)
    | split hne hpref hcs => exact ⟨_, _, hne, hpref, rfl, hcs⟩
  · rintro ⟨pieces, τ', hne, hpref, rfl, hcs⟩
    exact .split hne hpref hcs

end Symbolic.Swarm.Coinsplit.S1
