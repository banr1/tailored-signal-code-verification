/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common

/-!
# MessageEncrypt tail decode and fetch lemmas (`+0x46c .. +0x660` of `0x3caf4`)
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet

/-- Fetch hypotheses for `session_message_encrypt_with_stores`
(`hfn : fnOff encryptWithStoresName = 248564`), from fn-relative offset `k0`, `len` bytes. -/
macro "messageEncryptTail_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| messageEncrypt_code_fetches_from CryptoVerification.libsignalSessionCode messageEncryptTailBin $b $H
    $hfn (num% (ls_off% "session_message_encrypt")) $k0 $len)

-- T1 (`+0x46c .. +0x5b4`, `0x3cf60 .. 0x3d0a4`)
gen_decodes libsignalSessionCode_tree messageEncryptTailBin [(ls_off% "session_message_encrypt" + 1132) → (ls_off% "session_message_encrypt" + 1456)]

-- T2 (`+0x5b4 .. +0x660`, `0x3d0a8 .. 0x3d150`)
gen_decodes libsignalSessionCode_tree messageEncryptTailBin [(ls_off% "session_message_encrypt" + 1460) → (ls_off% "session_message_encrypt" + 1628)]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
