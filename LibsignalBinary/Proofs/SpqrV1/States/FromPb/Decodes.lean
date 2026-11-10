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
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs -- shake: keep

/-!
# Decode Tree & Symbol Offsets for `<spqr::v1::chunked::states::States>::from_pb`

**Checked by Lean.**

Provides the `gen_decodes` binary search tree `statesFromPbBin` for the 2,911 instructions
(`11,644` bytes) of `<spqr::v1::chunked::states::States>::from_pb`, together with symbol offsets,
`.rodata` jump-table definitions, and range-fetch tactic macros.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.Stubs

export CryptoVerification.SpqrV1.Layout.Stubs (
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_rust_realloc
  stubOff_memcpy
  stubOff_memmove
  stubOff_memset
  stubOff_handle_error
  fnOff_drop_poly16
  fnOff_drop_proto_poly_encoder
  fnOff_drop_poly_encoder_local2
  fnOff_drop_ct1_sent_local2
  fnOff_drop_ek_sent
  fnOff_drop_proto_ct1_sent_ek_received
  fnOff_ct1_sent_from_pb
  fnOff_ek_sent_ct1_received_from_pb
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `<spqr::v1::chunked::states::States>::from_pb` (2,911 instructions). -/
abbrev statesFromPbName : String :=
  "<spqr::v1::chunked::states::States>::from_pb"

@[simp, arm64_norm]
theorem statesFromPb_fnOff :
    libsignalSessionCode.fnOff statesFromPbName =
      num% (ls_off% "<spqr::v1::chunked::states::States>::from_pb") :=
  ls_lemma% fnOff "<spqr::v1::chunked::states::States>::from_pb"

gen_decodes libsignalSessionCode_tree statesFromPbBin [0x54cac → 0x57a28]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside
    `<spqr::v1::chunked::states::States>::from_pb` (`0x5a0a4..0x5ce20`). -/
macro "states_from_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode statesFromPbBin
      $b $H statesFromPb_fnOff 0x54cac $k0 $len)

/-! ## `.rodata` Jump Table for `States::from_pb` -/

/-- The 22-byte (11-halfword) jump table for
    `<spqr::v1::chunked::states::States>::from_pb` (base `entry + 156`, scaled by `<< 2`). -/
def statesFromPbJumpTableBytes : List (BitVec 8) :=
  [0#8, 0#8, 237#8, 0#8, 88#8, 0#8, 134#8, 0#8, 23#8, 0#8,
   41#8, 1#8, 71#8, 1#8, 225#8, 0#8, 146#8, 1#8, 72#8, 0#8, 113#8, 1#8]

/-- Read-only separation-logic assertion for the 22-byte jump table at
    `b + bv% (ls_xref% 0x5a120 0x5a124)`. -/
def statesFromPbJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x54d28 0x54d2c)) ↦ᵣ statesFromPbJumpTableBytes

theorem fnAddr_adrp_5a120 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesFromPbName + 124#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<spqr::v1::chunked::states::States>::from_pb" + 124)) := by
  rw [Program.fnAddr_rebase, statesFromPb_fnOff]
  revert hb; bv_bits

end CryptoVerification.SpqrV1.States.FromPb
