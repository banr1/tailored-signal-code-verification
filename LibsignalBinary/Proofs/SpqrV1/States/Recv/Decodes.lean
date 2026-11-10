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
import GeneratedLean.LibsignalSessionObj

/-!
# Decode Tree & Symbol Offsets for `<States>::recv` (`0x55454..0x5a0a0`)

**Checked by Lean.** Binary search tree `statesRecvBin` for the 4,884 instructions (`19,536` bytes)
of `<spqr::v1::chunked::states::States>::recv`, with symbol offsets, `.rodata` jump-table definitions, and fetch macros.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `<spqr::v1::chunked::states::States>::recv` (`0x55454`, 4,884 instructions). -/
abbrev statesRecvName : String :=
  "<spqr::v1::chunked::states::States>::recv"

@[simp, arm64_norm]
theorem statesRecv_fnOff :
    libsignalSessionCode.fnOff statesRecvName = 0x5005c :=
  ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv"

gen_decodes libsignalSessionCode_tree statesRecvBin [0x5005c → 0x54ca8]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside
    `<spqr::v1::chunked::states::States>::recv` (`0x55454..0x5a0a0`). -/
macro "states_recv_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode statesRecvBin
      $b $H statesRecv_fnOff 0x5005c $k0 $len)

/-! ## `.rodata` Jump Table for `0x55454` (`States::recv`) at `0x82418` (`533528`) -/

/-- The 22-byte (11-halfword) jump table at `0x82418` (`533528`) for
    `<spqr::v1::chunked::states::States>::recv` (`0x55454`, base `entry + 96` = `0x554b4`, scaled by `<< 2`). -/
def statesRecvJumpTableBytes : List (BitVec 8) :=
  [0#8, 0#8, 169#8, 1#8, 171#8, 0#8, 21#8, 1#8, 33#8, 0#8,
   253#8, 1#8, 31#8, 2#8, 102#8, 1#8, 56#8, 3#8, 123#8, 0#8, 63#8, 2#8]

/-- Read-only separation-logic assertion for the 22-byte jump table at `b + 0xa1418` (`b + 533528#64`). -/
def statesRecvJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x500a4 0x500a8)) ↦ᵣ statesRecvJumpTableBytes

/-- Expanded 22-byte jump table at `b + 533528#64` (`0x82418`). -/
def statesRecvJumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601")) ↦₈ᵣ 0#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 1)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 2)) ↦₈ᵣ 169#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 3)) ↦₈ᵣ 1#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 4)) ↦₈ᵣ 171#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 5)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 6)) ↦₈ᵣ 21#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 7)) ↦₈ᵣ 1#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 8)) ↦₈ᵣ 33#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 9)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 10)) ↦₈ᵣ 253#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 11)) ↦₈ᵣ 1#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 12)) ↦₈ᵣ 31#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 13)) ↦₈ᵣ 2#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 14)) ↦₈ᵣ 102#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 15)) ↦₈ᵣ 1#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 16)) ↦₈ᵣ 56#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 17)) ↦₈ᵣ 3#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 18)) ↦₈ᵣ 123#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 19)) ↦₈ᵣ 0#8) ∗
  ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 20)) ↦₈ᵣ 63#8) ∗ ((b + bv% (ls_bytes% "0000a901ab0015012100fd011f026601" + 21)) ↦₈ᵣ 2#8)

theorem fnAddr_adrp_5549c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 72#64) &&&
      0xfffffffffffff000#64) = b + 0x50000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

theorem rodata_statesRecvJumpTableAt {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesRecvJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0000a901ab0015012100fd011f026601")) (n := 22) (bs := statesRecvJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

end CryptoVerification.SpqrV1.States.Recv
