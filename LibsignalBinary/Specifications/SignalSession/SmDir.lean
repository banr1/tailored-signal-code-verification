/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Functional specification of the `signal-session` CLI in SM mode

**Trusted in part.** See `Computational/docs/TRUSTED_BASE.md`. The theorems of
`Computational/Theorems/` use `partyAddress` and `textBytes`; the remaining SM-mode directory and
model definitions (`dirOfE`, `smInputs`, `smSendInputs`, `smRecvInputs`, `smWrites`, `smPreKeyWire`,
`smSendWire`, `smSendModel`, `smRecvModel`) are checked by Lean.

In the ACD19 secure-messaging setting (`spqrOffSessionParams C`), two parties `A` and `B` start from
directories populated directly from session-model states (`dirOfE`), without `keygen` or PQXDH. While
Alice's session is unacknowledged, `send` wraps the `SignalMessage` in `3 ‖ PreKeySignalMessage`
(`smPreKeyWire`, `smSendWire`), and switches to `2 ‖ SignalMessage` after her first receive.

**DEV-CLI1 (libsignal): the SM game delivers the inner `SignalMessage` of a pre-key message.**
ACD19 has no pre-key layer, and on SM directories Bob holds no pre-keys, so `cliScheme` extracts
field 4 (the inner `SignalMessage`) from Alice's printed `3 ‖ PreKeySignalMessage` and delivers
`2 ‖ SignalMessage` (DEV-M5). `smSendModel` specifies the CLI's full stdout including the wrapper.
Effect: none on the security bound.

**DEV-CLI2 (libsignal): the SM spec covers `recv` of whisper messages only.** `smRecvInputs`
passes `2 ‖ c` for all `c` shorter than `2^32` bytes (DEV-M1), matching every ciphertext delivered
by `cliScheme` (DEV-CLI1); `3 ‖ …` inputs are outside the SM spec. Effect: none.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchetRepr

/-! ## The parties' directories -/

/-- **The address of each party**: name `partyAddressName P` (a hyphenated UUID), device 1 (`partyDeviceId`). -/
def partyAddress (P : Party) : Address := ⟨partyAddressName P, 1⟩

/-- The bytes of a text file: the string's UTF-8 encoding. -/
def textBytes (s : String) : List (BitVec 8) := utf8 s

/-- **The directory of party `P` with session record `rec`**, as the SM game writes it:
* `address`: `P`'s address as text;
* `identities/<peer name>`: the peer's identity key (`partyIdentityKey`), serialized (33 bytes): libsignal
  checks the session's remote identity against it (trust on first use, then pinned);
* `sessions/<peer address>`: the record.
The directories are `partyDirs`. -/
def dirOfE (P : Party) (rec : List (BitVec 8)) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress P).text),
   (identityFile (partyAddressName P.other), (partyIdentityKey P.other).serialize),
   (sessionFile (partyAddress P.other), rec)]

/-- **The inputs of one call** of the party of `g` with command `cmd`: its directory with the
record of `g` (`encodeRecord`), the `coins` file `coins`, and stdin `stdin`. -/
def smInputs (g : GhostState Bytes) (cmd : Cmd) (coins stdin : List (BitVec 8)) : Inputs :=
  { argv := cmd.argv
    dirs := partyDirs
    files := dirOfE g.party (encodeRecord g) ++ [(coinsFile, coins)]
    stdin := stdin }

/-- **`send` of plaintext `m`** by the party of `g` to its peer: an empty `coins` file (an SM send
draws no randomness: the sending chain's DH key is drawn when it is created, at a receive). -/
def smSendInputs (g : GhostState Bytes) (m : List (BitVec 8)) : Inputs :=
  smInputs g (.send (partyAddress g.party.other)) [] m

/-- **`recv` of `2 ‖ c`** by the party of `g` from its peer, with the 32 bytes of the receive
coins `rc` in `coins` (the DH ratchet step's key pair, as `session_recv`'s coins input). -/
def smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256) : Inputs :=
  smInputs g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc) (msgTypeWhisper :: c)

/-! ## Each call's outcome in the session model -/

/-- **The files a successful call writes** for the party of `g` with new record `rec`: the peer's
identity key (`save_identity`, the same bytes as before) and the record. -/
def smWrites (P : Party) (rec : List (BitVec 8)) : List (String × List (BitVec 8)) :=
  [(identityFile (partyAddressName P.other), (partyIdentityKey P.other).serialize), (sessionFile (partyAddress P.other), rec)]

/-- **The pre-key message `send` prints on an unacknowledged session** `st` around the
`SignalMessage` bytes `msg` (`message_encrypt`'s pending branch, `PreKeySignalMessage::new`), at
the pending pre-key that `encodeRecord` writes (`encPlaceholderPendingPreKey`: no one-time pre-key, signed
pre-key id 0, the placeholder base key `0x05 ‖ 0^32`, no Kyber pre-key) and the record's local
registration id 0 (`encodeRecord` omits it): type `3`, the version byte of the session's version,
then prost's `PreKeySignalMessage` with fields 2 (base key), 3 (the session's local identity key),
4 (`msg`), 5 (registration id 0) and 6 (signed pre-key id 0). -/
def smPreKeyWire (st : SessionState Bytes) (msg : List (BitVec 8)) : List (BitVec 8) :=
  msgTypePreKey :: versionByte (BitVec.ofNat 8 st.version.toNat) ::
    ProtoPreKeySignalMessage.encode
      { registrationId := some 0, preKeyId := none, signedPreKeyId := some 0,
        kyberPreKeyId := none, kyberCiphertext := none,
        baseKey := some placeholderBaseKey.serialize,
        identityKey := some st.localIdentity.serialize, message := some msg }

/-- **What `send` prints** for the `SignalMessage` bytes `msg` of the session-model state `g`:
`3 ‖ PreKeySignalMessage` (`smPreKeyWire`) while `g`'s pre-key message is unacknowledged, else
`2 ‖ msg`. -/
def smSendWire (g : GhostState Bytes) (msg : List (BitVec 8)) : List (BitVec 8) :=
  if g.session.pendingPreKey then smPreKeyWire g.session msg else msgTypeWhisper :: msg

/-- **`send`'s outcome in the session model** (`Run.lean`'s `observe` argument): `sendModelSpqrOff`
(abort = the model's panic; rejection = its other errors), and on success the files `smWrites`
with the new record, and stdout `smSendWire`. -/
def smSendModel (C : Crypto) (g : GhostState Bytes) (m : List (BitVec 8)) :
    Option (Option (List (String × List (BitVec 8)) × List (BitVec 8))) :=
  (sendModelSpqrOff C g m).map (Option.map fun (rec, msg) => (smWrites g.party rec, smSendWire g msg))

/-- **`recv`'s outcome in the session model** for `2 ‖ c`: `recvModelSpqrOff` on `c` (abort = the
model's panic; rejection = a parse failure or its other errors), and on success the files
`smWrites` with the new record, and stdout the plaintext. -/
def smRecvModel (C : Crypto) (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256) :
    Option (Option (List (String × List (BitVec 8)) × List (BitVec 8))) :=
  (recvModelSpqrOff C g c rc).map (Option.map fun (rec, pt) => (smWrites g.party rec, pt))

end CryptoVerification.SignalSession
