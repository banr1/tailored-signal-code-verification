/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead

/-!
# libsignal's symmetric ratchet: the chain step and HMAC as a PRF on chain keys

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Models libsignal v0.105.4 `ChainKey` (`rust/protocol/src/ratchet/keys.rs:140–183`): one-byte
domain-separated HMAC-SHA256 (`chainHmac`, `messageKeySeed = 0x01`, `chainKeySeed = 0x02`) and its
PRF view `hmacPRF`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet

open HMAC HKDF CBC LibsignalAead MACScheme AEADScheme

/-- 256-bit chain key as its 32 LE bytes (`ChainKey.key : [u8; 32]`). -/
abbrev ChainKey := BitVec 256

/-- `ChainKey::calculate_base_material`: `HMAC-SHA256(ck, [b])`. -/
def chainHmac (F : ShaState → List (BitVec 8) → ShaState) (ck : ChainKey) (b : BitVec 8) :
    List (BitVec 8) :=
  hmacWith F (keyToBytes32 ck) [b]

/-- `ChainKey::MESSAGE_KEY_SEED` (`keys.rs:148`). -/
def messageKeySeed : BitVec 8 := 0x01

/-- `ChainKey::CHAIN_KEY_SEED` (`keys.rs:149`). -/
def chainKeySeed : BitVec 8 := 0x02

/-- HMAC-SHA256 on one-byte inputs as a 256-bit PRF (32 LE bytes). -/
def hmacPRF (F : ShaState → List (BitVec 8) → ShaState) : MACScheme ChainKey (BitVec 8) ChainKey :=
  ⟨fun ck b => bytesToKey32 (chainHmac F ck b)⟩

end Ratchet

namespace AEADScheme

variable {K AD AD' M C : Type}

end AEADScheme

namespace Ratchet

open HMAC HKDF CBC LibsignalAead MACScheme AEADScheme

variable {H : Type}

end Ratchet
end CryptoGames
