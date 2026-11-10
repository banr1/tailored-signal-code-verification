/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import ProofLib.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Decode Tree and `.rodata` Jump Tables for `spqr::send::<HookRng>` (`0x3085c..0x33e0c`)

**Checked by Lean.**

Provides the `spqrSendBin` instruction decode tree, entry/offset abbreviations,
`.rodata` jump-table definitions (`0x7e4f0`, `0x7e506`, `0x7e51c`), and `spqr_send_fetches_range`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `spqr::send::<libsignal_session::HookRng>` (`0x3085c`, 3,436 instructions). -/
abbrev spqrSendName : String :=
  "spqr::send::<libsignal_session::HookRng>"

/-- Image offset of `spqr::send::<libsignal_session::HookRng>` (`0x3085c`). -/
abbrev spqrSendOff : Nat := 0x30940

@[simp, arm64_norm]
theorem spqrSend_fnOff :
    libsignalSessionCode.fnOff spqrSendName = 0x30940 :=
  ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>"

/-- Entry address of `spqr::send::<libsignal_session::HookRng>` (`b + 0x3085c`). -/
abbrev spqrSendEntry (b : BitVec 64) : BitVec 64 := b + 0x30940#64

gen_decodes libsignalSessionCode_tree spqrSendBin [0x30940 → 0x33ef0]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside
    `spqr::send::<libsignal_session::HookRng>` (`0x3085c..0x33e0c`). -/
macro "spqr_send_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrSendBin
      $b $H spqrSend_fnOff 0x30940 $k0 $len)

/-! ## `.rodata` Jump Tables (`0x7e4f0`, `0x7e506`, `0x7e51c`) -/

/-- Jump table 1 (`22` bytes = 11 `u16` entries at `0x7e4f0` = `517360`, base `0x309d0` / `entry + 372`):
    dispatches `States::send` across the 11 `States` variants (`0..10`). -/
def spqrSendStatesJumpTableBytes : List (BitVec 8) :=
  [0x00#8, 0x00#8, 0xd1#8, 0x00#8, 0x93#8, 0x00#8, 0xa7#8, 0x00#8,
   0x8a#8, 0x00#8, 0xe4#8, 0x00#8, 0xeb#8, 0x00#8, 0xbd#8, 0x00#8,
   0x0a#8, 0x02#8, 0x91#8, 0x00#8, 0xf4#8, 0x01#8]

/-- Read-only separation-logic assertion for jump table 1 at `b + 0x9d4f0` (`b + 517360#64`). -/
def spqrSendStatesJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x30a94 0x30a98)) ↦ᵣ spqrSendStatesJumpTableBytes

/-- Unpacked 11-halfword (`↦₁₆ᵣ`) form of `spqrSendStatesJumpTableAt b` at `roBase = b + 0x9d4f0#64`. -/
def spqrSendStatesJumpTableWordsAt (roBase : BitVec 64) : SepProp :=
  (roBase ↦₁₆ᵣ 0x0000#16) ∗ ((roBase + 2#64) ↦₁₆ᵣ 0x00d1#16) ∗
  ((roBase + 4#64) ↦₁₆ᵣ 0x0093#16) ∗ ((roBase + 6#64) ↦₁₆ᵣ 0x00a7#16) ∗
  ((roBase + 8#64) ↦₁₆ᵣ 0x008a#16) ∗ ((roBase + 10#64) ↦₁₆ᵣ 0x00e4#16) ∗
  ((roBase + 12#64) ↦₁₆ᵣ 0x00eb#16) ∗ ((roBase + 14#64) ↦₁₆ᵣ 0x00bd#16) ∗
  ((roBase + 16#64) ↦₁₆ᵣ 0x020a#16) ∗ ((roBase + 18#64) ↦₁₆ᵣ 0x0091#16) ∗
  ((roBase + 20#64) ↦₁₆ᵣ 0x01f4#16)

theorem spqrSendStatesJumpTableBytes_eq (roBase : BitVec 64) :
    (roBase ↦ᵣ spqrSendStatesJumpTableBytes) = spqrSendStatesJumpTableWordsAt roBase := by
  have h0000 : ((0x0000#16).extractLsb' 0 8 = 0x00#8) ∧ ((0x0000#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00d1 : ((0x00d1#16).extractLsb' 0 8 = 0xd1#8) ∧ ((0x00d1#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h0093 : ((0x0093#16).extractLsb' 0 8 = 0x93#8) ∧ ((0x0093#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00a7 : ((0x00a7#16).extractLsb' 0 8 = 0xa7#8) ∧ ((0x00a7#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h008a : ((0x008a#16).extractLsb' 0 8 = 0x8a#8) ∧ ((0x008a#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00e4 : ((0x00e4#16).extractLsb' 0 8 = 0xe4#8) ∧ ((0x00e4#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00eb : ((0x00eb#16).extractLsb' 0 8 = 0xeb#8) ∧ ((0x00eb#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h00bd : ((0x00bd#16).extractLsb' 0 8 = 0xbd#8) ∧ ((0x00bd#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h020a : ((0x020a#16).extractLsb' 0 8 = 0x0a#8) ∧ ((0x020a#16).extractLsb' 8 8 = 0x02#8) := ⟨by decide, by decide⟩
  have h0091 : ((0x0091#16).extractLsb' 0 8 = 0x91#8) ∧ ((0x0091#16).extractLsb' 8 8 = 0x00#8) := ⟨by decide, by decide⟩
  have h01f4 : ((0x01f4#16).extractLsb' 0 8 = 0xf4#8) ∧ ((0x01f4#16).extractLsb' 8 8 = 0x01#8) := ⟨by decide, by decide⟩
  unfold spqrSendStatesJumpTableBytes spqrSendStatesJumpTableWordsAt pointsTo16RO
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    h0000.1, h0000.2, h00d1.1, h00d1.2, h0093.1, h0093.2, h00a7.1, h00a7.2,
    h008a.1, h008a.2, h00e4.1, h00e4.2, h00eb.1, h00eb.2, h00bd.1, h00bd.2,
    h020a.1, h020a.2, h0091.1, h0091.2, h01f4.1, h01f4.2,
    sepConj_assoc, arm64_norm]

/-- Jump table 2 (`22` bytes = 11 `u16` entries at `0x7e506` = `517382`, base `0x31df0` / `entry + 5524`):
    dispatches inlined `PqRatchetState::encode_to_vec` across the 11 `V1State.InnerState` variants. -/
def spqrSendEncodeJumpTableBytes : List (BitVec 8) :=
  [0x00#8, 0x00#8, 0xef#8, 0x01#8, 0x56#8, 0x01#8, 0xb3#8, 0x01#8,
   0x20#8, 0x01#8, 0x0b#8, 0x02#8, 0x1b#8, 0x02#8, 0xce#8, 0x01#8,
   0x46#8, 0x02#8, 0x3b#8, 0x01#8, 0x36#8, 0x02#8]

/-- Read-only separation-logic assertion for jump table 2 at `b + 0x9d506` (`b + 517382#64`). -/
def spqrSendEncodeJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x32310 0x32314)) ↦ᵣ spqrSendEncodeJumpTableBytes

/-- Jump table 3 (`20` bytes = 10 `u16` entries at `0x7e51c` = `517404`, base `0x321a4` / `entry + 6472`):
    dispatches inlined `drop_glue::<PqRatchetState>` across `V1State.InnerState` variants. -/
def spqrSendDropJumpTableBytes : List (BitVec 8) :=
  [0xbb#8, 0x00#8, 0x00#8, 0x00#8, 0x7b#8, 0x00#8, 0x00#8, 0x00#8,
   0x3c#8, 0x00#8, 0xc8#8, 0x00#8, 0xe7#8, 0x00#8, 0xa4#8, 0x00#8,
   0x25#8, 0x01#8, 0x66#8, 0x00#8]

/-- Read-only separation-logic assertion for jump table 3 at `b + 0x9d51c` (`b + 517404#64`). -/
def spqrSendDropJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x32270 0x32274)) ↦ᵣ spqrSendDropJumpTableBytes

theorem fnAddr_adrp_309b0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 340#64) &&&
      0xfffffffffffff000#64) = b + 0x30000#64 := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

end CryptoVerification.SpqrV1.Top.Send
