/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.SmDir
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Specifications.RecordCodecs.Proto

/-!
# Functional specification of the `signal-session` CLI on PQXDH directories: `CliSpecPqxdh`

**Trusted: the statement.** Read with `Run.lean` and `SmDir.lean` (`partyAddress`, `textBytes`) to
trust the PQXDH-mode CLI statements (see `Computational/docs/TRUSTED_BASE.md`).

`CliSpecPqxdh run X W` specifies `init`, `send`, and `recv` on directories encoded (`encodeDir`)
from a party state `st : PqParty` in `PqxdhPartyInSpecDomain W st` over model primitives `W : PEParams`
(extern hooks in the binary: DEV-E8, DEV-PQ1) and `X : UnreachedPqxdhPrimitives`:
* `init <peer> bundle` (with `st.session = none`): trust-on-first-use check (`PqParty.trusts`), then
  `initiateState` (`pqInitModel`).
* `send <peer>`: `messageEncrypt` with SPQR V1 (`pqSendModel`), emitting `3 ‖ PreKeySignalMessage`
  while unacknowledged and `2 ‖ SignalMessage` thereafter, followed by the remote-identity trust check.
* `recv <peer>` of `2 ‖ c`: `SignalMessage.tryFrom` and `tryDecryptFromRecord` with `.whisper`
  (`pqRecvWhisperModel`).
* `recv <peer>` of `3 ‖ m.bytes` for canonical `m : PreKeyMessageFields` when `st.session` is `none`
  or matches `m` (`PqSessionMatches`): trust check, then either matching-session decryption or
  `preKeysNamedBy` + `recvPrekeyState` + `markKyberUsed` + `removeOpk` (`pqRecvPrekeyModel`, DEV-PQ8).
* `recv <peer>` with any other leading byte or empty input: rejected with exit `1`.

Non-canonical pre-key encodings and calls that archive an existing session (`init` over an existing
session or `recv` of a non-matching pre-key message; DEV-C-PREV) lie outside `CliSpecPqxdh`'s domain
(for non-matching pre-key `recv`, see `PqDirNoMatch.lean`). Because the CLI clock is `UNIX_EPOCH`
and all reachable records carry timestamp `0`, unacknowledged-session expiry never triggers (DEV-PQ9).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## A party's state -/

/-- A signed pre-key: its private half (the public half is derived, `keyPairOf`), its signature
and its timestamp. -/
structure PqSignedKey where
  /-- The private key (any 32 bytes: deserialization clamps). -/
  priv : List.Vector (BitVec 8) 32
  /-- The XEdDSA signature under the identity key. -/
  sig : List.Vector (BitVec 8) 64
  /-- The record's timestamp (no call reads it). -/
  timestamp : BitVec 64

/-- A Kyber1024 pre-key: public and secret key, its signature and its timestamp. -/
structure PqKyberKey where
  /-- The public key (1568 bytes, serialized behind type byte `0x08`). -/
  pub : List.Vector (BitVec 8) 1568
  /-- The secret key (3168 bytes, serialized behind type byte `0x08`). -/
  sec : List.Vector (BitVec 8) 3168
  /-- The XEdDSA signature under the identity key. -/
  sig : List.Vector (BitVec 8) 64
  /-- The record's timestamp (no call reads it). -/
  timestamp : BitVec 64

/-- **A party's state on PQXDH directories**: everything its directory holds. -/
structure PqParty where
  /-- Which party: its address is `partyAddress party`, its peer's `partyAddress party.other`. -/
  party : Party
  /-- Its identity key pair (private half) and registration id. -/
  me : LocalIdentity
  /-- The peer's pinned identity key (`identities/<peer name>`), if any. -/
  peerId : Option IdentityKey
  /-- The session with the peer (`sessions/<peer address>`), if any: its record extras and
  session-model state, encoded by `encodeRecordUnderExtras`. -/
  session : Option (RecordExtras × GhostState Bytes)
  /-- The signed pre-keys, by id. -/
  signed : List (BitVec 32 × PqSignedKey)
  /-- The one-time pre-keys (private half), by id; `none` = used (an empty file). -/
  oneTime : List (BitVec 32 × Option (List.Vector (BitVec 8) 32))
  /-- The one-time Kyber pre-keys, by id; `none` = used (an empty file). -/
  kyberOneTime : List (BitVec 32 × Option PqKyberKey)
  /-- The last-resort Kyber pre-keys, by id, each with the `(signed pre-key id, base key)` pairs
  it has accepted (its `.base-keys` file, oldest first). -/
  kyberLastResort : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32))

/-! ## The directory of a party (`stores.rs`) -/

/-- The record of a signed pre-key with id `id` (`SignedPreKeyRecord::serialize`): id, the
serialized public key (derived from the private key), the private key, signature, timestamp. -/
def signedRecordBytes (C : Crypto) (id : BitVec 32) (k : PqSignedKey) : List (BitVec 8) :=
  RecordCodecs.SignedPreKeyRecordStructure.encode
    ⟨id, djbKey (keyPairOf C k.priv).publicKey.bytes, k.priv.toList, k.sig.toList, k.timestamp⟩

/-- The record of a Kyber pre-key with id `id` (`KyberPreKeyRecord::serialize`): keys behind type
byte `0x08`. -/
def kyberRecordBytes (id : BitVec 32) (k : PqKyberKey) : List (BitVec 8) :=
  RecordCodecs.SignedPreKeyRecordStructure.encode
    ⟨id, kyberKey k.pub, 0x08#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩

/-- The record of a one-time pre-key with id `id` (`PreKeyRecord::serialize`). -/
def oneTimeRecordBytes (C : Crypto) (id : BitVec 32) (sk : List.Vector (BitVec 8) 32) :
    List (BitVec 8) :=
  RecordCodecs.PreKeyRecordStructure.encode
    ⟨id, djbKey (keyPairOf C sk).publicKey.bytes, sk.toList⟩

/-- The `.base-keys` file of a last-resort Kyber pre-key: `signed id:u32 ‖ base key[33]` each. -/
def baseKeysBytes (seen : List (BitVec 32 × List.Vector (BitVec 8) 32)) : List (BitVec 8) :=
  (seen.map fun (s, b) => le32 s ++ djbKey b).flatten

/-- **The files of a party's directory** (paths relative to it):
* `address` (text), `identity-key-pair` (`IdentityKeyPair::serialize`: the public key derived
  from the private key, and the private key), `registration-id` (`u32` little-endian);
* `identities/<peer name>`: the peer's pinned identity key, if any;
* `sessions/<peer address>`: the session's record (`encodeRecordUnderExtras`), if any;
* each signed pre-key, one-time pre-key and one-time Kyber pre-key record (an empty file when
  used), each last-resort Kyber pre-key record and its `.base-keys` file (always written).
The directories are `partyDirs`. -/
def encodeDir (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress st.party).text),
   (identityKeyPairFile, RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, le32 st.me.regId)] ++
  (match st.peerId with
   | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
   | none => []) ++
  (match st.session with
   | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
   | none => []) ++
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

/-- **The inputs of one call** of the party `st` with command `cmd`: its directory, the files
`extra` (the bundle directory for `init`), the `coins` file `coins`, and stdin `stdin`. -/
def pqInputs (W : PEParams) (st : PqParty) (cmd : Cmd) (extra : List (String × List (BitVec 8)))
    (coins stdin : List (BitVec 8)) : Inputs :=
  { argv := cmd.argv
    dirs := partyDirs ++ (match cmd with | .init _ dir => [dir] | _ => [])
    files := encodeDir W st ++ extra ++ [(coinsFile, coins)]
    stdin := stdin }

/-- The bundle directory's contents for a typed bundle (`public.rs`): keys serialized behind
their type bytes. -/
def publicBundleOf (b : PreKeyBundleFields) : PublicBundle :=
  { identityKey := djbKey b.idPub, registrationId := b.regId, signedId := b.spkId,
    signedKey := djbKey b.spkPub, signedSig := b.spkSig.toList, kyberId := b.kpkId,
    kyberKey := kyberKey b.kpkPub, kyberSig := b.kpkSig.toList,
    oneTime := b.opk.map fun (i, k) => (i, djbKey k) }

/-- **`init <peer> bundle`** by `st` with the typed bundle `b` in the bundle directory and the
192 coin bytes `t`. -/
def pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Inputs :=
  pqInputs W st (.init (partyAddress st.party.other) bundleDir) ((publicBundleOf b).files bundleDir)
    t.toList []

/-- **`send <peer>`** of plaintext `m` by `st` with the 64 coin bytes `r`. -/
def pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : Inputs :=
  pqInputs W st (.send (partyAddress st.party.other)) [] r.toList m

/-- **`recv <peer>`** of the message `c` (type byte included) by `st` with the 32 bytes of the
receive coins `rc`. -/
def pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) : Inputs :=
  pqInputs W st (.recv (partyAddress st.party.other)) [] (HMAC.keyToBytes32 rc) c

/-! ## Each call's outcome in the model -/

/-- **The trust check** (`is_trusted_identity`, trust on first use): no pinned key, or the pinned
key is `k`. -/
def PqParty.trusts (st : PqParty) (k : IdentityKey) : Bool :=
  match st.peerId with
  | none => true
  | some k' => decide (k' = k)

/-- **The run's outcome for the model's answer** `r` on the inputs `i` of the party `W`-encoded
from `st`: `none` = panic (abort); `some none` = rejection (exit 1, files unchanged);
`some (some (st', out))` = acceptance: exit 0, stdout `out`, and the files `i.files` overwritten by
the new directory `encodeDir W st'`. -/
def pqxdhExpectedOutcome (W : PEParams) (i : Inputs) (r : Option (Option (PqParty × List (BitVec 8)))) :
    Outcome :=
  observe i.files (r.map (Option.map fun (st', out) => (encodeDir W st', out)))

/-- **`init`'s model** (`process_prekey_bundle`): the trust check of the bundle's identity key,
then `initiateState` (the bundle's signatures, PQXDH, the initiator session; null on any failure);
on success the peer's identity key is pinned and the session stored. Never panics. -/
def pqInitModel (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Option (Option (PqParty × List (BitVec 8))) :=
  if !st.trusts ⟨⟨b.idPub⟩⟩ then some none
  else match initiateState X W st.party st.me b t with
    | none => some none
    | some (x, g) => some (some ({ st with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) }, []))

/-- **`send`'s model** (`message_encrypt`): no session rejects; else the session model's
`messageEncrypt` with V1 SPQR, the party's address blob and the coins `r` (panic aborts, other
errors reject), then the trust check of the session's remote identity. On success the new session
(same extras) and the remote identity pinned; stdout `3 ‖ firstMessageBody` while unacknowledged,
else `2 ‖ SignalMessage`, as `sendWireModel`. -/
def pqSendModel (W : PEParams) (st : PqParty) (m r : List (BitVec 8)) :
    Option (Option (PqParty × List (BitVec 8))) :=
  match st.session with
  | none => some none
  | some (x, g) =>
    match SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with
    | (.ok msg, s) =>
      match g.session.remoteIdentity with
      | none => some none
      | some k =>
        if !st.trusts k then some none
        else
          let wire := if g.session.pendingPreKey then wirePrekey :: firstMessageBody x g.session msg
            else wireWhisper :: msg.serialized
          some (some ({ st with peerId := some k, session := some (x, { g with session := s }) },
            wire))
    | (.error .panic, _) => none
    | (.error _, _) => some none

/-- **The receiving session's outcome** for a parsed `SignalMessage` `msg` of type `ty` on the
session `(x, g)` (`decrypt_message_with_record` on a record without previous sessions): the
session model's `tryDecryptFromRecord` (the party's expected addresses, coins `rc`; panic aborts,
other errors reject), then the trust check of the remote identity; on success the new session
(same extras, ghost state otherwise unchanged) and the plaintext. -/
def pqxdhSessionDecryptModel (W : PEParams) (st : PqParty) (x : RecordExtras) (g : GhostState Bytes)
    (msg : SignalMessage) (ty : MessageType) (rc : BitVec 256) :
    Option (Option (PqParty × List (BitVec 8))) :=
  match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g.party)
      msg ty rc g.session with
  | (.ok pt, s) =>
    match s.remoteIdentity with
    | none => some none
    | some k =>
      if !st.trusts k then some none
      else some (some ({ st with peerId := some k, session := some (x, { g with session := s }) },
        pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none


/-- **`recv`'s model on `2 ‖ c`** (`message_decrypt_signal`): no session rejects; `c` that does
not parse (`SignalMessage::try_from`) rejects; else `pqxdhSessionDecryptModel` with type `Whisper`. -/
def pqRecvWhisperModel (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    Option (Option (PqParty × List (BitVec 8))) :=
  match st.session with
  | none => some none
  | some (x, g) =>
    match SignalMessage.tryFrom protoSignalCodec c with
    | .error _ => some none
    | .ok msg => pqxdhSessionDecryptModel W st x g msg .whisper rc

/-- **The pre-keys a pre-key message `m` names, from `st`'s stores**, as `ResponderPreKeySecrets` (`none`: one is
missing, so libsignal rejects):
* the signed pre-key `m.spkId` (`get_signed_pre_key`);
* the Kyber pre-key `m.kpkId` (`get_kyber_pre_key`): the one-time key if its file is not empty,
  else the last-resort key with that id;
* the one-time pre-key `m.opkId`, if `m` names one (`get_pre_key`): a used (empty) one is
  missing. -/
def preKeysNamedBy (st : PqParty) (m : PreKeyMessageFields) : Option ResponderPreKeySecrets :=
  match List.lookup m.spkId st.signed with
  | none => none
  | some s =>
    let kyber : Option PqKyberKey :=
      match List.lookup m.kpkId st.kyberOneTime with
      | some (some k) => some k
      | _ => (List.lookup m.kpkId st.kyberLastResort).map (·.1)
    match kyber with
    | none => none
    | some k =>
      let opk : Option (Option (BitVec 32 × List.Vector (BitVec 8) 32)) :=
        match m.opkId with
        | none => some none
        | some j =>
          match List.lookup j st.oneTime with
          | some (some sk) => some (some (j, sk))
          | _ => none
      opk.map fun o =>
        { spkId := m.spkId, spkPriv := s.priv, kpkId := m.kpkId, kpkPub := k.pub, kpkSec := k.sec,
          opk := o }

/-- **`mark_kyber_pre_key_used(m.kpkId, m.spkId, m.baseKey)`** on `st`'s stores (`none`: the
store refuses, so libsignal rejects): a one-time Kyber pre-key whose file is not empty is emptied;
else the last-resort key `m.kpkId` refuses when its `.base-keys` replay list exceeds `fileCapBytes`
(`37 * seen.length > fileCapBytes`, where `Dir::get` / `readFileHook` returns `Err`) or holds the
`(signed pre-key id, base key)` pair (\"reused base key\"), and otherwise appends it. -/
def markKyberUsed (st : PqParty) (m : PreKeyMessageFields) : Option PqParty :=
  match List.lookup m.kpkId st.kyberOneTime with
  | some (some _) =>
    some { st with kyberOneTime := st.kyberOneTime.map fun (i, k) =>
      if i = m.kpkId then (i, none) else (i, k) }
  | _ =>
    match List.lookup m.kpkId st.kyberLastResort with
    | none => none
    | some (_, seen) =>
      if 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen then none
      else some { st with kyberLastResort := st.kyberLastResort.map fun (i, k, s) =>
        if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s) }

/-- **`remove_pre_key(m.opkId)`**, if `m` names a one-time pre-key: its file is emptied. -/
def removeOpk (st : PqParty) (m : PreKeyMessageFields) : PqParty :=
  match m.opkId with
  | none => st
  | some j => { st with oneTime := st.oneTime.map fun (i, k) => if i = j then (i, none) else (i, k) }

/-- **The session `(x, g)` matches the pre-key message `m`** (`promote_matching_session` on the
current session): its `alice_base_key` is `m`'s base key, serialized, and its version is `m`'s
(`currentVersion`, the high nibble of `m.bytes`'s first byte). -/
def PqSessionMatches (x : RecordExtras) (g : GhostState Bytes) (m : PreKeyMessageFields) : Prop :=
  x.aliceBaseKey = djbKey m.baseKey ∧ g.session.sessionVersion = 4

instance (x : RecordExtras) (g : GhostState Bytes) (m : PreKeyMessageFields) :
    Decidable (PqSessionMatches x g m) := by
  unfold PqSessionMatches; infer_instance

/-- **`recv`'s model on `3 ‖ m.bytes`** for a typed pre-key message `m` (`message_decrypt_prekey`):
1. `m.inner` that does not parse (`SignalMessage::try_from`) rejects (`PreKeySignalMessage::
   try_from` parses it);
2. the trust check of `m`'s identity key (`process_prekey`);
3. with a session that matches `m` (`PqSessionMatches`; `promote_matching_session`): the
   session's remote identity must be `m`'s identity key, then the session's
   `tryDecryptFromRecord` with type `PreKey`; no pre-key is used;
4. with no session: `preKeysNamedBy` (a missing pre-key rejects), `recvPrekeyState` (PQXDH, the recipient
   session, the first decryption; panic aborts), `markKyberUsed` (a refusal — missing key,
   last-resort `.base-keys` above `fileCapBytes`, or replayed base key — rejects with exit `1` and
   files unchanged), then `removeOpk`;
5. on success `m`'s identity key is pinned and the session stored; stdout is the plaintext.
A session that does not match `m` is outside `CliSpecPqxdh`'s domain (libsignal would archive it, and
`encodeRecordUnderExtras` writes no previous sessions: DEV-C-PREV); the model then rejects. -/
def pqRecvPrekeyModel (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (m : PreKeyMessageFields)
    (rc : BitVec 256) : Option (Option (PqParty × List (BitVec 8))) :=
  match SignalMessage.tryFrom protoSignalCodec m.inner with
  | .error _ => some none
  | .ok inner =>
    let idA : IdentityKey := ⟨⟨m.idPub⟩⟩
    if !st.trusts idA then some none
    else
      match st.session with
      | some (x, g) =>
        if PqSessionMatches x g m then
          if g.session.remoteIdentity ≠ some idA then some none
          else
            match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with
            | (.ok pt, s) =>
              some (some ({ st with peerId := some idA, session := some (x, { g with session := s }) },
                pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none
        else some none
      | none =>
        match preKeysNamedBy st m with
        | none => some none
        | some k =>
          match recvPrekeyState X W st.party st.me k m rc with
          | none => none
          | some none => some none
          | some (some (x, g, pt)) =>
            match markKyberUsed st m with
            | none => some none
            | some st1 =>
              some (some ({ removeOpk st1 m with peerId := some idA, session := some (x, g) }, pt))

/-! ## The domain and the spec -/

/-- **The party states `CliSpecPqxdh` covers** (the games keep their parties in it):
* a session, if any, encodes as a reachable one (`ReachablePqxdhSession`: a PQXDH handshake started it and the
  wire entries continued it) for `st`'s identity: some reachable `g₀` has the same party and
  session state, is `st.party`'s, and its record is below `2^31` bytes (the bound `ReachablePqxdhSession`'s steps
  carry);
* every file of the directory is below `2^31` bytes, and every file other than a last-resort
  `.base-keys` file (`baseKeysFile i`) is at most `fileCapBytes` (`2^21`) bytes;
* the pre-key ids of each kind are distinct (each names one file).

**DEV-CLI21 (libsignal): bounded I/O caps and stated last-resort `.base-keys` cap rejection (effect:
none).** Each CLI run enforces the bounded-read I/O caps (`stdinCapBytes = 2^20`,
`fileCapBytes = 2^21`, `cliPathMaxBytes = 4096`) and refuses `send` plaintext above
`maxPlaintextBytes` (`1_000_000`) with exit `1`. In `PqxdhPartyInSpecDomain` and `markKyberUsed`:
(i) non-`.base-keys` files are at most `fileCapBytes` (`ReachablePqxdhSession` records are
`≤ 1,209,331` B; other store files are fixed-size), while `.base-keys` (`baseKeysFile i`) stays
below `2^31` bytes; (ii) the `.base-keys` read cap (`37 * seen.length > fileCapBytes` in
`markKyberUsed`, from the `56,681`-st handshake on one unrotated last-resort key) is a modelled
exit-`1` rejection with files unchanged; (iii) `cliPqExp` never reaches that rejection
(`seen.length ≤ 1`).

The session conjunct ignores ghost epochs (`GhostState.epoch`, `chainEpochs`), which are not
serialized by `encodeRecordUnderExtras`. -/
def PqxdhPartyInSpecDomain (W : PEParams) (st : PqParty) : Prop :=
  (∀ x g, st.session = some (x, g) →
    (∃ g₀ : GhostState Bytes, ReachablePqxdhSession W st.me x g₀ ∧ g₀.party = g.party ∧ g₀.session = g.session) ∧
    g.party = st.party ∧ (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) ∧
  (∀ f ∈ encodeDir W st, f.2.length < 2 ^ 31 ∧
    ((∀ i, f.1 ≠ baseKeysFile i) → f.2.length ≤ fileCapBytes)) ∧
  (st.signed.map (·.1)).Nodup ∧ (st.oneTime.map (·.1)).Nodup ∧
  (st.kyberOneTime.map (·.1)).Nodup ∧ (st.kyberLastResort.map (·.1)).Nodup

/-- **The CLI on PQXDH directories** (`run` is any implementation; the real one is the engine
process of the CLI's ELF). For every model primitives `W` and model extras `X`, every party state
`st` in the domain (`PqxdhPartyInSpecDomain`), and each call below, standard input above
`stdinCapBytes` (`2^20`) exits `2` (`read_stdin` cap), `send` plaintext above `maxPlaintextBytes`
(`10^6`) exits `1` before running the model (with every file unchanged in both cases), and
otherwise the run's outcome is the model's (`pqxdhExpectedOutcome`):
1. `init <peer> bundle` with no session (DEV-C-PREV), any typed bundle `b` and the 192 coin bytes
   `t`: `pqInitModel`;
2. `send <peer>` of any plaintext `m` below `2^32` bytes with the 64 coin bytes `r`: exit `2` if
   `m.length > stdinCapBytes`, else exit `1` if `m.length > maxPlaintextBytes`, else `pqSendModel`;
3. `recv <peer>` of `2 ‖ c` for any `c` below `2^32` bytes, with coins `rc`: exit `2` if
   `(2 ‖ c).length > stdinCapBytes`, else `pqRecvWhisperModel`;
4. `recv <peer>` of `3 ‖ m.bytes` for a typed pre-key message `m` (other encodings are outside
   the domain) whose inner message is below `2^32 - 2048` bytes, when there is no session or the
   session matches `m` (DEV-C-PREV), with coins `rc`: exit `2` if
   `(3 ‖ m.bytes).length > stdinCapBytes`, else `pqRecvPrekeyModel`;
5. `recv <peer>` of any input below `2^32` bytes whose first byte is neither `2` nor `3`, or of
   nothing: exit `2` if `c.length > stdinCapBytes`, else exit `1`, with every file unchanged.
In 1–4 `m`'s registration id, ids, keys and inner message are any values (the adversary's). -/
def CliSpecPqxdh (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain W st →
    (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
      run (pqInitInputs W st b t) =
        some (pqxdhExpectedOutcome W (pqInitInputs W st b t) (pqInitModel X W st b t))) ∧
    (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
      run (pqSendInputs W st m r) =
        if m.length > stdinCapBytes then
          some (.exited 2 [] (filesOf (pqSendInputs W st m r).files))
        else if m.length > maxPlaintextBytes then
          some (.exited 1 [] (filesOf (pqSendInputs W st m r).files))
        else
          some (pqxdhExpectedOutcome W (pqSendInputs W st m r) (pqSendModel W st m r.toList))) ∧
    (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
      run (pqRecvInputs W st (wireWhisper :: c) rc) =
        if (wireWhisper :: c).length > stdinCapBytes then
          some (.exited 2 [] (filesOf (pqRecvInputs W st (wireWhisper :: c) rc).files))
        else
          some (pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: c) rc)
            (pqRecvWhisperModel W st c rc))) ∧
    (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
      run (pqRecvInputs W st (wirePrekey :: m.bytes) rc) =
        if (wirePrekey :: m.bytes).length > stdinCapBytes then
          some (.exited 2 [] (filesOf (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files))
        else
          some (pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
            (pqRecvPrekeyModel X W st m rc))) ∧
    (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
      c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
      run (pqRecvInputs W st c rc) =
        if c.length > stdinCapBytes then
          some (.exited 2 [] (filesOf (pqRecvInputs W st c rc).files))
        else
          some (.exited 1 [] (filesOf (pqRecvInputs W st c rc).files)))

end CryptoVerification.SignalSession
