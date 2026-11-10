/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.Bridge

/-!
# Instruction Decode Tree for `V1State::merge` (`0x4e7e8..0x4f544`, 855 insns)

**Checked by Lean.** Isolated into `V1StateFetch.lean` so `gen_decodes` is cached across
`V1StateDefs.lean` and proof edits.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

abbrev v1StateMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::V1State, &mut &[u8]>"

@[simp, arm64_norm]
theorem v1StateMerge_fnOff :
    libsignalSessionCode.fnOff v1StateMergeName = 0x493f0 :=
  libsignalSessionCode_fnOff_0x493f0

gen_decodes libsignalSessionCode_tree v1StateMergeBin [ 0x493f0 → 0x4a14c ]

/-- The 11-byte jump table at `0x8240c` for `V1State::merge` (`0x4e7e8`, base `entry + 300`,
    scaled by `<< 2`, indexed by `tag - 1` for tags `1..11`). -/
def v1StateMergeJumpTableBytes : List (BitVec 8) :=
  [0#8, 66#8, 32#8, 44#8, 9#8, 76#8, 88#8, 54#8, 112#8, 20#8, 100#8]

/-- Read-only separation-logic assertion for the 11-byte jump table at `b + 0xa140c`. -/
def v1StateMergeJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_bytes% "0042202c094c5836701464")) ↦ᵣ v1StateMergeJumpTableBytes

abbrev v1StateMergeJumpTableSym : String :=
  "spqr:.rodata.prost::encoding::message::merge::<spqr::proto::pq_ratchet::V1State, &mut &[u8]>"

/-- Read-only separation-logic assertion for the 11-byte jump table at `lsmpl.ρ v1StateMergeJumpTableSym`. -/
def v1StateMergeJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsmpl.ρ v1StateMergeJumpTableSym) ↦ᵣ v1StateMergeJumpTableBytes

theorem fnAddr_adrp_4e88c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 164#64) &&&
      0xfffffffffffff000#64) = b + 0x49000#64 := by
  rw [Program.fnAddr_rebase, v1StateMerge_fnOff]
  revert hb; bv_bits

end CryptoVerification.SpqrV1.Prost.MessageMerge
