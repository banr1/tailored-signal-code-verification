/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Decode Lemmas for `HookSessionStore::store_session`

Per-word `storeSessionBin_decode_0x<off>` lemmas proved by `rfl_kernel` for `code_fetches` on
`libsignalSessionCode`:
* `0x42b38` (31 words): `store_session` future poll;
* `0x42e5c` (24 words): `store_session` async-trait shim;
* `0x3c830 .. 0x3c8d8` (42 words): `store_session` call segment in
  `session_message_decrypt_signal_with_stores`;
* `0x42a44` (1 word): no-op future drop (`ret`).

Right-hand sides remain in canonical register/literal syntax (`.X20`, `.SP`, `0x10#64`) to avoid
kernel recursion blowup during symbolic stepping.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreSession

open Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree storeSessionBin [(ls_off% "session_message_decrypt_signal" + 9096) → (ls_off% "session_message_decrypt_signal" + 9260)]

end CryptoVerification.LibsignalPublicApi.StoreSession
