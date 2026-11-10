/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRecv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Accepting Whisper Receive Block Shape

Defines `rcvAccBlk` for an accepting whisper receive call block and proves that it satisfies
`RecvBlockShape`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPureRcv

open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

/-- Machine events emitted by an accepting whisper receive call. -/
abbrev rcvAccBlk (body : HwBytes) (mid : List MachineEvent) (sm : StateAndMessage) :
    List MachineEvent :=
  .recv (wireWhisperTag :: body) :: (mid ++ [.accept sm.message])

theorem rcv_accMid_kinds {mid : List MachineEvent} {m : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid = [.rng rb]) :
    ∀ e ∈ mid ++ [.accept m], eventKind e = .rng ∨ eventKind e = .accept := by
  rcases hmid with rfl | ⟨rb, -, rfl⟩ <;> simp [eventKind]

theorem rcv_accBlk_shape {mid : List MachineEvent} {body : HwBytes} {sm : StateAndMessage}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid = [.rng rb]) :
    RecvBlockShape (rcvAccBlk body mid sm) := by
  refine ⟨⟨body, rfl⟩, fun e he => rcv_accMid_kinds hmid e (by simpa using he), ?_⟩
  rcases hmid with rfl | ⟨rb, -, rfl⟩ <;> simp

open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
