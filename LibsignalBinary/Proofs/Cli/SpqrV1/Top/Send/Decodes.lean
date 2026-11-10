/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.Lemmas

/-!
# Instruction Decode Lemmas & `.rodata` Jump Tables for `spqr::send::<signal_session_ratchet::Coins>`

Generates instruction-decode lemmas and unpacks the `.rodata` jump tables (`0x9d4f0`,
`0x9d506`, `0x9d51c`) for `spqr::send::<signal_session_ratchet::Coins>` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification

open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

/-- Symbol name of `spqr::send::<signal_session_ratchet::Coins>` (3,436 instructions). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName : String :=
  "spqr::send::<libsignal_cli_ratchet::Coins>"

/-- Image offset of `spqr::send::<signal_session_ratchet::Coins>`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendOff : Nat := (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>")

@[simp, arm64_norm]
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") :=
  ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>"

/-- Entry address of `spqr::send::<signal_session_ratchet::Coins>` at base `b`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry (b : BitVec 64) : BitVec 64 := b + (bv% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>"))

gen_decodes libsignalSessionCode_tree spqrSendBinCli [(ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 0) → (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 13744)]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside
    `spqr::send::<signal_session_ratchet::Coins>`. -/
macro "spqr_send_fetches_range_cli " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrSendBinCli
      $b $H CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") $k0 $len)

/-! ## `.rodata` Jump Tables for `spqr::send::<signal_session_ratchet::Coins>` (`0x9d4f0`, `0x9d506`, `0x9d51c`) -/

/-- Read-only separation-logic assertion for jump table 1 at `b + 0x9d4f0` (`b + 517360#64`). -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344))) ↦ᵣ spqrSendStatesJumpTableBytes

/-- Read-only separation-logic assertion for jump table 2 at `b + 0x9d506` (`b + 517382#64`). -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6608) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6612))) ↦ᵣ spqrSendEncodeJumpTableBytes

/-- Read-only separation-logic assertion for jump table 3 at `b + 0x9d51c` (`b + 517404#64`). -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6448) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6452))) ↦ᵣ spqrSendDropJumpTableBytes

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_309b0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 340#64) &&&
      0xfffffffffffff000#64) = b + (bv% (page% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340))) := by
  rw [Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff]
  revert hb; bv_bits

end CryptoVerification.SpqrV1.Top.Send
