/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# Instruction Decode Tree for `spqr::recv`

Pre-generated instruction decode lemmas and range-fetch macro for `spqr::recv`
(`0x5462c..0x55208`, 759 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

abbrev spqrRecvFnName : String := "spqr::recv"

@[simp, arm64_norm]
theorem spqrRecv_fnOff_0x5462c :
    libsignalSessionCode.fnOff spqrRecvFnName = 0x4f234 :=
  ls_lemma% fnOff "spqr::recv"

gen_decodes libsignalSessionCode_tree spqrRecvFullBin [0x4f234 → 0x4fe10]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside `spqr::recv`
    (`0x5462c..0x55208`). -/
macro "spqr_recv_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvFullBin
      $b $H spqrRecv_fnOff_0x5462c 0x4f234 $k0 $len)

end CryptoVerification.SpqrV1.Top.Recv

