/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core

/-!
# Step Helpers for `prost::encoding::bytes::encode_repeated [local#3]`

Provides instruction-decode lemmas and loop-body step helpers (`step_copy`, `step_iter`,
`step_latch_zero`, `step_latch_succ`) for `encode_repeated [local#3]` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib ProofLib.ProgramReflection



open CryptoVerification.CodeLayout




set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Instruction decode lemmas (`+0..+236` in `encode_repeated [local#3]`) -/

gen_decodes libsignalSessionCode_tree libsignalSessionBinCli [(ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" + 0) → (ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]" + 236)]

/-- Symbol name of `prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Varint.encodeRepeated1Name : String :=
  "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"

end CryptoVerification.SpqrV1.Varint
