/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Decode Lemmas for `segTrust_ok`

Kernel-checked decode lemmas for `+0xa70..+0xab0`, `+0xb7c..+0xbd4`, `+0xc78..+0xc88`, and
`+0xd0c..+0xd40` of `session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
theorem libsignalSessionCode_fnOff_sym_3caf4 :
    libsignalSessionCode.fnOff encryptWithStoresName = num% (ls_off% "session_message_encrypt") := by
  exact (ls_lemma% fnOff "session_message_encrypt")

/-! ## `is_trusted_identity` Shim and Poll (`+0xa70..+0xab0`) -/

gen_decodes libsignalSessionCode_tree segTrustBin [(ls_off% "session_message_encrypt" + 2672) → (ls_off% "session_message_encrypt" + 2728)]

/-! ## `is_trusted_identity` Ready Path (`+0xb7c..+0xbd4`) -/

gen_decodes libsignalSessionCode_tree segTrustBin [(ls_off% "session_message_encrypt" + 2940) → (ls_off% "session_message_encrypt" + 3024)]

/-! ## `UntrustedIdentity` Error Builder (`+0xc78..+0xc88`, `+0xd0c..+0xd40`) -/

gen_decodes libsignalSessionCode_tree segTrustBin [(ls_off% "session_message_encrypt" + 3192) → (ls_off% "session_message_encrypt" + 3204), (ls_off% "session_message_encrypt" + 3340) → (ls_off% "session_message_encrypt" + 3388)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
