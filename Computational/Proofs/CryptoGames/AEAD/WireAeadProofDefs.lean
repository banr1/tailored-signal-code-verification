/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead

/-!
# Wire-Level AEAD Proof Definitions

Generic encode-then-MAC wire AEAD (`etmWire`) and libsignal wire codec helpers (`RoundTripOn`,
`wireMacInput`, `openWire`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace WireAEAD
variable {K AD H M M' C T : Type}

/-- Encode-then-MAC wire AEAD authenticating `(a, encode h c)` and delegating post-MAC opening to `decode`. -/
def etmWire [DecidableEq T] {KE KM : Type} (cipher : CipherScheme KE M C)
    (mac : MACScheme KM (AD × List (BitVec 8)) T) (encode : H → C → List (BitVec 8))
    (decode : KE → List (BitVec 8) → Option (H × M')) : WireAEAD (KE × KM) AD H M M' C T where
  encode := encode
  enc k a h m :=
    let w := encode h (cipher.enc k.1 m)
    (w, mac.tag k.2 (a, w))
  dec k a e := if mac.tag k.2 (a, e.1) == e.2 then decode k.1 e.1 else none

end WireAEAD
namespace LibsignalAead
open CBC HMAC WireAEAD

/-- Restricted round-trip property `parse ∘ encode = some` on header/body pairs satisfying `valid`. -/
def WireCodec.RoundTripOn {H : Type} (codec : WireCodec H) (valid : H → List (BitVec 8) → Prop) :
    Prop :=
  ∀ h body, valid h body → codec.parse (codec.encode h body) = some (h, body)

/-- MAC input bytes `ids ‖ w` for identity keys `ids` and serialized wire bytes `w`. -/
def wireMacInput : SerializedIdentityKeys × List (BitVec 8) → List (BitVec 8)
  | (ids, w) => ids.toList ++ w

/-- Post-MAC wire opening: parses `(h, body)`, CBC-decrypts `body`, and checks header addresses. -/
def openWire {H : Type} (D : AesKey → Block → Block) (codec : WireCodec H)
    (addrs : H → Option (List (BitVec 8))) (expected : Option (List (BitVec 8)))
    (ke : AesKey × Block) (w : List (BitVec 8)) : Option (H × List (BitVec 8)) :=
  match codec.parse w with
  | none => none
  | some (h, body) =>
    match cbcDecRaw D ke.1 ke.2 body with
    | none => none
    | some m => if addressCheckPasses (addrs h) expected then some (h, m) else none

end LibsignalAead
end CryptoGames
