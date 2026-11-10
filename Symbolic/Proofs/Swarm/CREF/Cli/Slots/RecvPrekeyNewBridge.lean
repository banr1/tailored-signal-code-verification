/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Non-Empty Coin Guard for Fresh Pre-Key `recv`

Proves that a 32-byte coin list is non-empty, discharging the `CoinSplit` guard
on an accepting fresh pre-key `recv`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.Cli

theorem coins_ne_nil_of_len_32 {coins : HwBytes} (hlen : coins.length = 32) : coins ≠ [] := by
  intro h
  rw [h] at hlen
  cases hlen

end Symbolic.Swarm.CREF.Cli.Slots
