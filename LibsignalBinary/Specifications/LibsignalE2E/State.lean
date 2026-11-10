/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.LibsignalSpqr

/-!
# Binary Party State and Session-Record Encoding (`BinState`, `encodeRecord`)

**Trusted: the statement.** Defines the binary-level party state `BinState` (serialized
`SessionRecord` bytes paired with ACD19 epoch bookkeeping `EpochGhost`, DEV-M12), the SPQR-disabled
ratchet instance `spqrOffB` (DEV-LS24), the `storage.proto` encoder `encodeRecord` (with constant
pending pre-key fields in SM mode, DEV-M9), the state map `binStateOf`, and the `< 2^32`-byte
ciphertext length bound `shortCiphertext` (DEV-M1). See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-- Byte strings. -/
abbrev Bytes := List (BitVec 8)

/-- **SPQR switched off** at `PQ = Bytes`: initial state `[]`, `send` returns the unchanged empty
state, no salt and an empty message for any coins, and `recv` is what the in-image `spqr::recv`
does on the empty state (`LibsignalSpqr.spqrRecvEmpty`): `[]` and no salt if the message's
preamble parses (`msg_preamble`), else `Err(MsgDecode)` (DEV-LS24). `spqrOff`
(`PQ = Unit`, `Computational/Proofs/SignalWireRoundTrip.lean`) is the same except that its `recv`
accepts every message. -/
def spqrOffB : Spqr Bytes Unit :=
  ⟨fun _ _ => [], fun _ _ => some ([], none, []), fun _ msg => LibsignalSpqr.spqrRecvEmpty msg,
    fun _ _ => false, fun _ _ => false⟩

/-! ## The binary state -/

/-- **The epoch bookkeeping of a party**: its epoch counter and, oldest first, the ratchet public key
and epoch of each receiver chain its record stores. -/
structure EpochGhost where
  /-- The party's epoch counter, `t_cur` of ACD19 Fig. 8. -/
  epoch : ℕ
  /-- `(sender ratchet key, epoch)` of each stored receiver chain, oldest first. -/
  chains : List (PublicKey × ℕ)
  deriving DecidableEq

namespace EpochGhost

/-- The epoch bookkeeping of a session-model state: its epoch counter, and its receiver chains'
ratchet keys paired with their epochs. -/
def ofGhost {PQ : Type} (g : GhostState PQ) : EpochGhost :=
  ⟨g.epoch, (g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs⟩

/-- After a successful send by `P` (ACD19 Fig. 2 `ep-mgmt`): the epoch moves to `P`'s next sending
epoch if it is in a receiving one (as the session model's `Params.send`). -/
def send (P : Party) (e : EpochGhost) : EpochGhost :=
  { e with epoch := if P.sendsIn e.epoch then e.epoch else e.epoch + 1 }

/-- After a successful receive of a message with ratchet key `rk`: the epoch `t` of the chain
used and the new bookkeeping. A known key keeps everything; an unknown key starts epoch `epoch + 1`,
which becomes the party's epoch, and its chain is appended (libsignal then keeps the last
`maxReceiverChains` chains, `session.rs` `add_receiver_chain`), as the session model's
`Params.receive`. ACD19 §5.2 "Epoch indexing": Signal names epochs by ratchet keys (DEV-LS8). -/
def recv (e : EpochGhost) (rk : PublicKey) : ℕ × EpochGhost :=
  match e.chains.find? (·.1 == rk) with
  | some (_, t) => (t, e)
  | none =>
    let cs := e.chains ++ [(rk, e.epoch + 1)]
    (e.epoch + 1, ⟨e.epoch + 1, cs.drop (cs.length - maxReceiverChains)⟩)

end EpochGhost

/-- **A party's state in the binary scheme**: the party, its serialized session record (the bytes
the binary returned), and its epoch bookkeeping.

**DEV-M12 (formalization): the state carries bookkeeping the binary does not hold.** ACD19 Fig. 8
keeps an explicit epoch counter `t_cur` in the state. The binary's record has none: Signal names
epochs by ratchet keys (ACD19 §5.2). Lean adds the party and the epochs next to the record bytes;
`corr` also leaks them. Effect: none: they are public bookkeeping. -/
structure BinState where
  /-- Which party (fixes the epoch parity and the binary's `who`). -/
  party : Party
  /-- The serialized `SessionRecord` (opaque). -/
  bytes : Bytes
  /-- The epoch bookkeeping. -/
  epochs : EpochGhost
  deriving DecidableEq

/-! ## Field writers (prost `encode` of one field) -/

/-- A length-delimited field: key, length, payload. -/
def lenField (tag : ℕ) (payload : Bytes) : Bytes :=
  encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 payload.length) ++ payload

/-- proto3 `bytes`: omitted when empty. -/
def bytesField (tag : ℕ) (v : Bytes) : Bytes :=
  if v = [] then [] else lenField tag v

/-- proto3 `uint32`: omitted when 0. -/
def uint32Field (tag : ℕ) (v : BitVec 32) : Bytes :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint (v.setWidth 64)

/-- A sub-message: written whenever present (even if its encoding is empty). -/
def msgField (tag : ℕ) : Option Bytes → Bytes
  | none => []
  | some body => lenField tag body

/-! ## Messages of `storage.proto` -/

/-- `Chain.ChainKey { uint32 index = 1; bytes key = 2; }` (the key's 32 little-endian bytes). -/
def encChainKey (ck : ChainKey) : Bytes :=
  uint32Field 1 ck.index ++ bytesField 2 (HMAC.keyToBytes32 ck.key)

/-- `Chain.MessageKey` in its `Seed` form (the only form the session model has): `index = 1`, `seed = 5`. -/
def encMessageKey (mk : MessageKeyGenerator) : Bytes :=
  uint32Field 1 mk.counter ++ bytesField 5 mk.seed

/-- `Chain` for the sending chain: public key, private key, chain key, no message keys. -/
def encSenderChain (c : SenderChain) : Bytes :=
  bytesField 1 c.ratchetKey.publicKey.serialize ++ bytesField 2 c.ratchetKey.privateKey.bytes.toList ++
    msgField 3 (some (encChainKey c.chainKey))

/-- `Chain` for a receiving chain: public key, chain key, skipped message keys (oldest first). -/
def encReceiverChain (c : ReceiverChain) : Bytes :=
  bytesField 1 c.senderRatchetKey.serialize ++ msgField 3 (c.chainKey.map encChainKey) ++
    (c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten

/-- The placeholder base key of Alice's pending pre-key in `encodeRecord`: the all-zero X25519
key, serialized `0x05 ‖ 0^32` (DEV-M9). -/
def placeholderBaseKey : PublicKey := ⟨List.Vector.replicate 32 0#8⟩

/-- `PendingPreKey { optional uint32 pre_key_id = 1; bytes base_key = 2; int32 signed_pre_key_id = 3;
uint64 timestamp = 4; }` at constant values: `pre_key_id` absent, `signed_pre_key_id`
and `timestamp` 0 (omitted), so only `base_key`. -/
def encPlaceholderPendingPreKey : Bytes := bytesField 2 placeholderBaseKey.serialize

/-- `SessionStructure` of a session-model state, fields in tag order 1–7, 9, 15 (10, 11, 13, 14 are
the omitted defaults: registration ids 0, empty `alice_base_key`, no Kyber pre-key). -/
def encSessionStructureSeed (st : SessionState Bytes) : Bytes :=
  uint32Field 1 st.sessionVersion ++
  bytesField 2 st.localIdentity.serialize ++
  bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++
  uint32Field 5 st.previousCounter ++
  msgField 6 (st.senderChain.map encSenderChain) ++
  (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++
  msgField 9 (if st.pendingPreKey then some encPlaceholderPendingPreKey else none) ++
  bytesField 15 st.pqRatchetState

/-- **`SessionRecord::serialize` of a session-model state**: `RecordStructure { current_session = 1; }` (no
previous sessions). -/
def encodeRecord (g : GhostState Bytes) : Bytes :=
  msgField 1 (some (encSessionStructureSeed g.session))

/-! ## The map to binary states, and the injection filter -/

/-- **`binStateOf`**: the binary state of a session-model state: the same party, `encodeRecord`,
the epoch bookkeeping. Used for the CLI scheme's initial states (`cliScheme`) and to relabel
adversaries (`Adversary.relabel`). -/
def binStateOf (g : GhostState Bytes) : BinState :=
  ⟨g.party, encodeRecord g, EpochGhost.ofGhost g⟩

/-- **`shortCiphertext`**: the injections the CLI games admit: shorter than `2^32` bytes
(`cliPqLenOk`, `Computational/Specifications/Game/StatementPq.lean`). The relabelled adversary
answers the others `none`, as the games do.

**DEV-M1 (machine model): inputs of `2^32` bytes or more are refused.** ACD19 Fig. 2 lets the
adversary inject any ciphertext. Here the games refuse such injections, and the CLI specs say
nothing about them. Why: the run model needs bounded lengths. Effect: restricts the adversary (no
claim for injections of 4 GiB or more); honest ciphertexts are shorter. -/
def shortCiphertext (c : Bytes) : Bool := decide (c.length < 2 ^ 32)

end CryptoVerification.E2E
