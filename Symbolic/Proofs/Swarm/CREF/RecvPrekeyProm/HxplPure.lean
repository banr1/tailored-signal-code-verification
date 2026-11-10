/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# PreKey Wire Tag and Event-Filtering Helpers

Proves `.rng`-filtering and `parsePreKeyWire` tag/body lemmas used when explaining `.preKey`
promote calls.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)

theorem prom_hmid_filter_head {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    ((mid ++ [MachineEvent.accept pt]).filter fun e => eventKind e != .rng).head? =
      some (.accept pt) := by
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> rfl

theorem promXpl_tag_ne_wireWhisperTag_of_parsePreKeyWire
    {tag : BitVec 8} {body : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire (tag :: body) = some pf) :
    tag ≠ wireWhisperTag := by
  rintro rfl
  unfold parsePreKeyWire wireWhisperTag DY.Libsignal.PQXDH.Refinement.wirePrekeyTag at hpf
  simp at hpf

theorem prom_recvBody_of_parsePreKeyWire {b : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire b = some pf) :
    RecvBody (.recv b) pf.message := by
  cases b with
  | nil => cases hpf
  | cons tag body => exact Or.inr ⟨pf, hpf, rfl⟩

end Symbolic.Swarm.CREF.CliPure
