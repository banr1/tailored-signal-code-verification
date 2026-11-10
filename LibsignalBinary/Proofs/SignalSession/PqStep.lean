/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir

set_option warningAsError false

/-!
# Accepted Transitions of `CliSpecPqxdh` (`PqStep` and `lastResortUses`)

Defines `PqStep` (one accepted CLI transition from `st` to `st'`) and `lastResortUses` (total count
of `(spkId, baseKey)` entries recorded across last-resort `.base-keys` files) for `PqClosure.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
/-- One accepted call of `CliSpecPqxdh`'s domain by the party `st`, leaving `st'` (the model
accepts; the run then exits `0` with `encodeDir W st'`): `init` on an empty session slot, `send`,
`recv` of `2 ‖ c`, and `recv` of `3 ‖ m.bytes` with no session or a matching one. -/
inductive PqStep (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) : PqParty → Prop
  | init (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) (st' : PqParty)
      (out : List (BitVec 8)) :
      st.session = none → pqInitModel X W st b t = some (some (st', out)) → PqStep X W st st'
  | send (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64) (st' : PqParty)
      (out : List (BitVec 8)) :
      m.length < 2 ^ 32 → pqSendModel W st m r.toList = some (some (st', out)) →
      PqStep X W st st'
  | recvWhisper (c : List (BitVec 8)) (rc : BitVec 256) (st' : PqParty) (out : List (BitVec 8)) :
      c.length < 2 ^ 32 → pqRecvWhisperModel W st c rc = some (some (st', out)) →
      PqStep X W st st'
  | recvPrekey (m : PreKeyMessageFields) (rc : BitVec 256) (st' : PqParty) (out : List (BitVec 8)) :
      m.inner.length + 2048 < 2 ^ 32 → (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
      pqRecvPrekeyModel X W st m rc = some (some (st', out)) → PqStep X W st st'

/-- The last-resort uses: how many `(signed pre-key id, base key)` pairs the party's
last-resort Kyber pre-keys have accepted (the entries of their `.base-keys` files). -/
def lastResortUses (st : PqParty) : ℕ :=
  (st.kyberLastResort.map fun e => e.2.2.length).sum

end CryptoVerification.SignalSession
