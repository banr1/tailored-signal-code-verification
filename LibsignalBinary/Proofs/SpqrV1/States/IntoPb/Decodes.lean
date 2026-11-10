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
# Decode Tree & Symbol Offsets for `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`)

**Checked by Lean.**

Instruction decode tree `statesIntoPbBin` for the 615 instructions (`2,460` bytes) of
`<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`), together with symbol offsets,
the 22-byte `.rodata` jump table at `0x82444` (`533572`), and range-fetch tactic macros.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, 615 instructions). -/
abbrev statesIntoPbName : String :=
  "<spqr::v1::chunked::states::States>::into_pb"

@[simp, arm64_norm]
theorem statesIntoPb_fnOff :
    libsignalSessionCode.fnOff statesIntoPbName = 0x57a28 :=
  ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb"

gen_decodes libsignalSessionCode_tree statesIntoPbBin [0x57a28 → 0x583c4]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside
    `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`). -/
macro "states_into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode statesIntoPbBin
      $b $H statesIntoPb_fnOff 0x57a28 $k0 $len)

/-! ## `.rodata` Jump Table for `0x5ce20` (`States::into_pb`) at `0x82444` (`533572`) -/

/-- The 22-byte (11-halfword) jump table at `0x82444` (`533572`) for
    `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, base `entry + 100`, scaled by `<< 2`). -/
def statesIntoPbJumpTableBytes : List (BitVec 8) :=
  [0#8, 0#8, 199#8, 0#8, 93#8, 0#8, 152#8, 0#8, 10#8, 0#8,
   252#8, 0#8, 29#8, 1#8, 182#8, 0#8, 130#8, 1#8, 65#8, 0#8, 77#8, 1#8]

/-- Read-only separation-logic assertion for the 22-byte jump table at `b + 0xa1444` (`b + 533572#64`). -/
def statesIntoPbJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x57a74 0x57a78)) ↦ᵣ statesIntoPbJumpTableBytes

/-- Expanded 22-byte jump table at `b + 533572#64` (`0x82444`). -/
def statesIntoPbJumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600")) ↦₈ᵣ 0#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 1)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 2)) ↦₈ᵣ 199#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 3)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 4)) ↦₈ᵣ 93#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 5)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 6)) ↦₈ᵣ 152#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 7)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 8)) ↦₈ᵣ 10#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 9)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 10)) ↦₈ᵣ 252#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 11)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 12)) ↦₈ᵣ 29#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 13)) ↦₈ᵣ 1#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 14)) ↦₈ᵣ 182#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 15)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 16)) ↦₈ᵣ 130#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 17)) ↦₈ᵣ 1#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 18)) ↦₈ᵣ 65#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 19)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 20)) ↦₈ᵣ 77#8) ∗ ((b + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600" + 21)) ↦₈ᵣ 1#8)

theorem fnAddr_adrp_5ce6c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesIntoPbName + 76#64) &&&
      0xfffffffffffff000#64) = b + 0x57000#64 := by
  rw [Program.fnAddr_rebase, statesIntoPb_fnOff]
  revert hb; bv_bits

end CryptoVerification.SpqrV1.States.IntoPb
