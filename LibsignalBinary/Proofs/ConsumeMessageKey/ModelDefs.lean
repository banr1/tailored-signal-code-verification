/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

set_option warningAsError false

@[expose] public section

set_option autoImplicit false

/-!
# Closed-Form Session-Model Definitions for `consume_message_key`

Pure ratchet-model definitions (`chainStepN`, `skippedKeys`, `ChainsOk`) separated from machine-level
imports.
-/

namespace CryptoVerification.SessionModel

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
/-- Iterated chain-key step (`n` applications of `nextChainKey` without `u32::MAX` overflow checks). -/
def chainStepN (F : ShaCompress) : ℕ → ChainKey → ChainKey
  | 0, ck => ck
  | n + 1, ck =>
    chainStepN F n ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩

/-- Skipped message keys generated across `n` chain steps from `ck`, ordered newest first. -/
def skippedKeys (F : ShaCompress) : ℕ → ChainKey → List MessageKeyGenerator
  | 0, _ => []
  | n + 1, ck =>
    skippedKeys F n ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩ ++
      [ck.messageKeys F]

/-- Representation invariant: each receiver chain holds at most `maxMessageKeys` (2000) non-empty seeds. -/
def ChainsOk (st : RatchetState) : Prop :=
  ∀ c ∈ st.receiverChains, c.messageKeys.length ≤ maxMessageKeys ∧ ∀ k ∈ c.messageKeys, k.seed ≠ []

end CryptoVerification.SessionModel
