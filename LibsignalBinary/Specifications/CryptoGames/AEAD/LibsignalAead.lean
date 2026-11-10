/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs

/-!
# Wire-encoding and identity-key types for libsignal's per-message AEAD

**Trusted in part.** The theorems of `Computational/Theorems/` use only `SerializedIdentityKeys` and
`addressCheckPasses` from this file: read them. The rest is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines the fixed-block wire encoding `WireEnc` (for `n`-block CBC bodies, DEV-AEAD2), the
concatenated 66-byte sender/receiver identity keys `SerializedIdentityKeys` authenticated by
`compute_mac`, and the address check `addressCheckPasses` of `verify_mac_with_addresses`
(DEV-AEAD11). The raw-byte wire AEAD used by the session bounds is in `WireAeadDefs.lean`.
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalAead

open CBC HMAC

/-- Abstract wire encoding of a `SignalMessage` header `h : H` and `n`-block CBC body without its
trailing 8-byte MAC tag. -/
structure WireEnc (H : Type) (n : ℕ) where
  /-- Serialize header and `n`-block body into `ver ‖ protobuf(h, c)`. -/
  encode : H → List.Vector Block n → List (BitVec 8)
  /-- Parse serialized bytes back into header and `n`-block body, or `none` on failure. -/
  parse : List (BitVec 8) → Option (H × List.Vector Block n)

/-- Concatenated sender and receiver serialized public identity keys (33 bytes each: type byte
`0x05` followed by 32 key bytes) authenticated by `SignalMessage::compute_mac`. -/
abbrev SerializedIdentityKeys := List.Vector (BitVec 8) 66

/-- Address check of `SignalMessage::verify_mac_with_addresses`, given the message's `addresses`
field (`present`) and locally serialized expected addresses (`expected`): accept if `present` is
`none`, reject if `present` is `some _` and `expected` is `none`, otherwise test equality. -/
def addressCheckPasses (present expected : Option (List (BitVec 8))) : Bool :=
  match present, expected with
  | none, _ => true
  | some _, none => false
  | some a, some e => a == e

end LibsignalAead
end CryptoGames
