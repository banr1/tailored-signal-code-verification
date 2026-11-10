/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import Symbolic.Proofs.Swarm.UA.BI.G.SendCore

/-!
# Send Slot Refinement

Proves `uab_slot_send_of : XlateInvSpecB -> UASlotSendSpecB`, showing that the `send` slot
preserves the turn simulation `PqTurnSim1A` and the trace invariant `UAInvB` across prefixes
containing break and invert steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.SlotSend

open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UASlotSendSpecB XlateInvSpecB)
open Symbolic.Proofs.Swarm.UA.BI.G.SendCore (slot_send_of_xlate)

/-- The `send` slot preserves `PqTurnSim1A` and `UAInvB`, given `XlateInvSpecB`. -/
theorem uab_slot_send_of (hXI : XlateInvSpecB) : UASlotSendSpecB :=
  slot_send_of_xlate hXI

end Symbolic.Proofs.Swarm.UA.BI.G.SlotSend
