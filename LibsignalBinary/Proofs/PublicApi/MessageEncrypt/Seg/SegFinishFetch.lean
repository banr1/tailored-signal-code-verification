/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalPublicApi
import ProofLib.GenDecodes

/-!
# Instruction Decode Lemmas for `segFinish_ok`

Kernel-checked decode lemmas for `+0xe88..+0xf2c` and `+0xf3c..+0xfac` of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
theorem libsignalSessionCode_fnOff_0x3cbd8 :
    libsignalSessionCode.fnOff encryptWithStoresName = 0x3cbd8 := by
  exact CryptoVerification.libsignalSessionCode_fnOff_0x3cbd8

gen_decodes libsignalSessionCode_tree segFinishBin [0x3da60 → 0x3db00, 0x3db14 → 0x3db80]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
