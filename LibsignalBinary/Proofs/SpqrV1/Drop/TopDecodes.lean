/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes

/-!
# Instruction Decode Trees and Layout Offsets for Top-Level SPQR V1 Drop Glue

Isolates `gen_fn_decodes` and `fnOff` lemmas for:
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` (40 instructions)
- `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>` (173 instructions)
- `core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]` (181 instructions)
- `core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]` (109 instructions)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L1

abbrev dropProtoPqRatchetStateName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>"

abbrev dropOptProtoInnerStateName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"

abbrev dropChunkedStatesLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"

abbrev dropChunkedStatesLocal2Name : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"

@[simp, arm64_norm] theorem dropProtoPqRatchetState_fnOff :
    libsignalSessionCode.fnOff dropProtoPqRatchetStateName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>"

@[simp, arm64_norm] theorem dropOptProtoInnerState_fnOff :
    libsignalSessionCode.fnOff dropOptProtoInnerStateName =
      num% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"

@[simp, arm64_norm] theorem dropChunkedStatesLocal1_fnOff :
    libsignalSessionCode.fnOff dropChunkedStatesLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"

@[simp, arm64_norm] theorem dropChunkedStatesLocal2_fnOff :
    libsignalSessionCode.fnOff dropChunkedStatesLocal2Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"

gen_fn_decodes libsignalSessionCode_tree spqrDropTopBin
  ["core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>",
   "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>",
   "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]",
   "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"]

/-- Niche value `-3` (`0xfffffffffffffffd`) used for `None` in `Option<pq_ratchet_state::Inner>`. -/
abbrev none3Cap : BitVec 64 := 0xfffffffffffffffd#64

@[simp, arm64_norm]
theorem none3Cap_add_three_beq_zero : (none3Cap + 3#64 == 0#64) = true := rfl

end CryptoVerification.SpqrV1.Drop
