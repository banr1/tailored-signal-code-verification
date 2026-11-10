/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SendsFitRun
public import Symbolic.Specifications.Concrete.ImageSymbols
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Whisper Receive Block `SendsFit` Preservation

Proves that appending an accepting whisper receive call block containing only `rng` and
`accept` events preserves `TR.SendsFit`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPureRcv

/-- `SendsFit` holds on `acc ++ (.recv (wireWhisperTag :: body) :: mid)` when `mid` has no `.send`. -/
theorem rcv_blk_sendsFit_pure {acc mid : List MachineEvent} {body : HwBytes}
    (hsf : TR.SendsFit acc)
    (hmid : ∀ e ∈ mid, eventKind e = .rng ∨ eventKind e = .accept) :
    TR.SendsFit (acc ++ (.recv (wireWhisperTag :: body) :: mid)) := by
  refine TR.sendsFit_append hsf fun b hb => ?_
  rcases List.mem_cons.mp hb with h | h
  · cases h
  · rcases hmid (.send b) h with h1 | h1 <;> cases h1

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
