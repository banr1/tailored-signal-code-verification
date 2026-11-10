/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel

/-!
# Wire-Level `send` / `recv` Models and Reachable PQXDH Sessions

**Trusted in part.** `Computational/Theorems/` uses `ReachablePqxdhSession`, `firstMessageBody`,
`wirePrekey`, and `wireWhisper` (via `SignalSession/PqDir.lean`); `sendWirePending`, `sendModelPq`,
`recvModelPq`, and `honestBundle` are checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

Defines the CLI's one-byte wire framing (`2 ‖ SignalMessage` vs `3 ‖ PreKeySignalMessage`), the
pending-session `send` model `sendWirePending` over V1 SPQR (`pqxdhSpqrSession`), the inductive
closure `ReachablePqxdhSession` of PQXDH-initialized sessions under `pqxdhSessionParams`, and
untagged proof-target helpers (`sendModelPq`, `recvModelPq`, `honestBundle`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec

/-! ## Wire tags -/

/-- `WIRE_WHISPER`: the tag of a bare `SignalMessage` on the wire. -/
def wireWhisper : BitVec 8 := 2#8

/-- `WIRE_PREKEY`: the tag of a `PreKeySignalMessage` on the wire. -/
def wirePrekey : BitVec 8 := 3#8

/-! ## The pending-session send model -/

/-- **The first message's body** (`message_encrypt`, `session_cipher.rs:76–115`, pending branch):
`PreKeySignalMessage::new` with the session's version, the record's local registration id, the
pending pre-key's ids and base key, the pending Kyber pre-key (if any), the session's local
identity key, and the encrypted `SignalMessage`. -/
def firstMessageBody (x : RecordExtras) (st : SessionState Bytes) (msg : SignalMessage) : Bytes :=
  (PreKeySignalMessage.new (BitVec.ofNat 8 st.version.toNat) x.localRegistrationId
    x.pending.preKeyId x.pending.signedPreKeyId
    (x.kyber.map fun k => ⟨k.preKeyId, k.ciphertext⟩) x.pending.baseKey st.localIdentity
    msg).serialized

/-- **`send` on a pending session** (Alice's messages before her first successful
receive): the session model's `messageEncrypt` with V1 SPQR (`pqxdhSpqrSession W`), the party's address blob
and random coins `r`, the new record under the same extras, and `3 ‖ PreKeySignalMessage`. -/
def sendWirePending (W : PEParams) (x : RecordExtras) (g : GhostState Bytes) (m : Bytes)
    (r : Bytes) : Option (Option (Bytes × Bytes)) :=
  match SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with
  | (.ok msg, s) => some (some (encodeRecordUnderExtras (fun _ => x) { g with session := s },
      wirePrekey :: firstMessageBody x g.session msg))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-! ## Reachable PQXDH sessions -/

/-- **The sessions a PQXDH handshake starts and `send` / `recv` continue**, with their identity
`me` and record extras `x` (constant over the session). Roots: Alice's state after
`init` (`initiateState`) and Bob's after his pre-key `recv` (`recvPrekeyState`), for
any model extras, inputs and coins. Steps: the session model's `Params.send` / `Params.receive` at
`pqxdhSessionParams W`. -/
inductive ReachablePqxdhSession (W : PEParams) : LocalIdentity → RecordExtras → GhostState Bytes → Prop
  | initiate (X : UnreachedPqxdhPrimitives) (P : Party) (me : LocalIdentity) (b : PreKeyBundleFields)
      (t : List.Vector (BitVec 8) initiateTapeLen) (x : RecordExtras) (g : GhostState Bytes) :
      initiateState X W P me b t = some (x, g) → ReachablePqxdhSession W me x g
  | recvPrekey (X : UnreachedPqxdhPrimitives) (P : Party) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
      (rc : BitVec 256) (x : RecordExtras) (g : GhostState Bytes) (pt : Bytes) :
      recvPrekeyState X W P me k m rc = some (some (x, g, pt)) → ReachablePqxdhSession W me x g
  | send {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes} (m : Bytes) (r : Bytes) :
      ReachablePqxdhSession W me x g → (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 →
      ReachablePqxdhSession W me x ((pqxdhSessionParams W).send g m r).1
  | recv {me : LocalIdentity} {x : RecordExtras} {g g' : GhostState Bytes} {c : Bytes} {rc : BitVec 256}
      {r : ℕ × ℕ × Bytes} :
      ReachablePqxdhSession W me x g → (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 →
      (pqxdhSessionParams W).receive g c rc = some (g', r) → ReachablePqxdhSession W me x g'

/-! ## Proof targets (not trusted) -/

/-- A send's outcome in the session model at `pqxdhSessionParams W` (V1 SPQR) under extras `E`: the new
record and the untagged serialized `SignalMessage`. -/
def sendModelPq (E : Party → RecordExtras) (W : PEParams) (g : GhostState Bytes) (m r : Bytes) :
    Option (Option (Bytes × Bytes)) :=
  match SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
      ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with
  | (.ok msg, s) => some (some (encodeRecordUnderExtras E { g with session := s }, msg.serialized))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- A receive's outcome in the session model at `pqxdhSessionParams W` (V1 SPQR) under extras `E`: parse
the untagged `c` as a `SignalMessage` and decrypt it (type `Whisper`); the new record and the
plaintext. -/
def recvModelPq (E : Party → RecordExtras) (W : PEParams) (g : GhostState Bytes) (c : Bytes)
    (rc : BitVec 256) : Option (Option (Bytes × Bytes)) :=
  match SignalMessage.tryFrom (pqxdhSessionParams W).codec c with
  | .error _ => some none
  | .ok msg =>
    match SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with
    | (.ok pt, s) => some (some (encodeRecordUnderExtras E { g with session := s }, pt))
    | (.error .panic, _) => none
    | (.error _, _) => some none

/-- **Honest bundle**: the bundle Bob publishes from identity `meB` and keys `k` (registration id
`regB`, the signatures `spkSig` / `kpkSig` on his signed and Kyber pre-keys). -/
def honestBundle (C : Crypto) (meB : LocalIdentity) (k : ResponderPreKeySecrets) (spkSig kpkSig : List.Vector (BitVec 8) 64) :
    PreKeyBundleFields :=
  { regId := meB.regId
    opk := k.opk.map fun (i, sk) => (i, (keyPairOf C sk).publicKey.bytes)
    spkId := k.spkId
    spkPub := (keyPairOf C k.spkPriv).publicKey.bytes
    spkSig := spkSig
    kpkId := k.kpkId
    kpkPub := k.kpkPub
    kpkSig := kpkSig
    idPub := (keyPairOf C meB.idPriv).publicKey.bytes }

end CryptoVerification.E2E
