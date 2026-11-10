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
# Instruction Decodes for CLI SPQR V1 Chunked `States` Drop Glue (`[local#3]`)

Defines `dropChunkedStatesLocal1Name`, `dropChunkedStatesLocal1_fnOff`, and instruction decode
theorems for `core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]` in
`libsignalSessionCode_tree`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.CodeLayout

open CryptoVerification.SpqrV1.Layout.L1

/-- `core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]` (181 insns = 724B). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]"

gen_fn_decodes libsignalSessionCode_tree spqrDropTopBinCli ["core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]"]

end CryptoVerification.SpqrV1.Drop
