/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Party

/-!
# The libsignal session as an SM scheme with receive coins (the adapter)

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Adapts the pure session model of `LibsignalSession.lean` to the receive-coin secure-messaging
components (`initA`, `initB`, `send`, `receive`; DEV-LS1, DEV-LS3, DEV-LS4, DEV-LS17) over
`GhostState` (attaching ghost epoch numbers to ratchet-key-indexed chains, DEV-LS8, DEV-LS18) and
abstract PQXDH `InitKeys` (DEV-LS22, DEV-LS28), preserving unacknowledged address checks (DEV-LS15)
and clone-based atomic decryption failure (DEV-LS16).
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSession

/-- **The adapter state**: a libsignal session plus ghost epochs.

**DEV-LS8 (libsignal): epochs are named by the ratchet key, not numbered.** ACD19 Fig. 8 carries the
epoch number `t` in the header (§5.2 "Epoch indexing"). libsignal identifies an epoch by the
sender's ratchet public key, so the model adds ghost epochs (`epoch`, `chainEpochs`). The MAC binds
the epoch only through its parity (identity-key order), so the per-message AEAD bounds are stated
for adversaries that stay in one epoch (`AllQueriesInOneADClass`), and ratchet-key collisions cost a term
(DEV-LS18). Effect: constants. -/
structure GhostState (PQ : Type) where
  /-- Which party (fixes the epoch parity). -/
  party : Party
  /-- The libsignal session record. -/
  session : SessionState PQ
  /-- Ghost: the party's Fig. 8 epoch counter `t_cur`. -/
  epoch : ℕ
  /-- Ghost: the epoch of each stored receiver chain (aligned with `session.receiverChains`). -/
  chainEpochs : List ℕ
  deriving DecidableEq

/-- **The abstract initial keys** (PQXDH is out of scope; DEV-LS28): the PQXDH root key, chain key
and SPQR key `pqr_key` (both parties' SPQR states are `spqr.init dir pqrKey`, `ratchet.rs:83–96,
146–159`), the coins of Bob's signed pre-key (B's initial ratchet key pair, A's initial "their
ratchet key"), and the coins of Alice's eager first ratchet key pair.

**DEV-LS22 (libsignal): Bob's signed pre-key public key is secret in the model.** ACD19 models CKA
as a secret-key primitive: the initial key `k_CKA = (h, x₀)` with `h = g^{x₀}` is shared and secret
(§4.1.2, §5.2 "Initial key agreement"). In libsignal `h` is Bob's signed pre-key, published in his
pre-key bundle and reused across sessions. Here its coins are fresh, independent and uniform per
session, and only `corr-B` reveals it. Effect: none relative to ACD19, but weaker than deployed
libsignal: no claim against adversaries that know Bob's signed pre-key in advance. DEV-LS3,
DEV-LS4 and the epoch-0 term exist because of it. -/
structure InitKeys where
  /-- PQXDH root key. -/
  rootKey : RootKey
  /-- PQXDH chain key (index 0). -/
  chainKey : BitVec 256
  /-- Coins of Bob's signed pre-key pair. -/
  bobSpkCoins : BitVec 256
  /-- Coins of Alice's first sending ratchet key pair (drawn at initialization). -/
  aliceRatchetCoins : BitVec 256
  /-- PQXDH's SPQR authentication key `pqr_key`. -/
  pqrKey : BitVec 256

/-- Fixed session parameters: primitives, protobuf codec, SPQR, identity keys, and serialized
address blobs (`none` when unserializable). -/
structure Params (PQ PQC : Type) where
  C : Crypto
  codec : SignalMessageProtoCodec
  spqr : Spqr PQ PQC
  idA : IdentityKey
  idB : IdentityKey
  /-- `serialize_addresses(alice, bob)`, carried by `A` while unacknowledged and expected by `B`. -/
  addrAB : Option (List (BitVec 8))
  /-- `serialize_addresses(bob, alice)`, expected by `A` (`B` never sends addresses). -/
  addrBA : Option (List (BitVec 8))

/-- The address blob a party sends (if its session is unacknowledged). -/
def Params.sendAddrs {PQ PQC : Type} (P : Params PQ PQC) : Party → Option (List (BitVec 8))
  | .A => P.addrAB
  | .B => P.addrBA

/-- The address blob a party expects. -/
def Params.expectedAddrs {PQ PQC : Type} (P : Params PQ PQC) : Party → Option (List (BitVec 8))
  | .A => P.addrBA
  | .B => P.addrAB

namespace Params

variable {PQ PQC : Type}

/-- `Init-B`: `initialize_recipient_session` with Bob's signed pre-key pair; epoch 0, no chains. -/
def initB (P : Params PQ PQC) (k : InitKeys) : GhostState PQ :=
  ⟨.B, initializeRecipientSession P.spqr P.idB P.idA (KeyPair.generate P.C k.bobSpkCoins)
    k.rootKey k.chainKey k.pqrKey, 0, []⟩

/-- `Init-A`: `initialize_initiator_session` (eager first sending chain) and
`set_unacknowledged_pre_key_message`; epoch 0, one receiver chain (Bob's signed pre-key, ghost
epoch 0). -/
def initA (P : Params PQ PQC) (k : InitKeys) : GhostState PQ :=
  let spk := (KeyPair.generate P.C k.bobSpkCoins).publicKey
  match initializeInitiatorSession P.C P.spqr P.idA P.idB spk k.rootKey k.chainKey k.pqrKey
      k.aliceRatchetCoins with
  | .ok s => ⟨.A, s.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  | .error _ =>
    ⟨.A, ((SessionState.new currentVersion P.idA P.idB k.rootKey (P.spqr.init .a2b k.pqrKey)).addReceiverChain
      spk ⟨k.chainKey, 0⟩).setUnacknowledgedPreKeyMessage, 0, [0]⟩

/-- `Send(st, m; r)`: `message_encrypt` with SPQR coins `r` and the party's address blob; the ghost
epoch moves to the next sending epoch of the party if it is in a receiving epoch (Fig. 8's
`ep-mgmt`). On failure: the unchanged state and the empty wire.

**DEV-LS17 (formalization): adapter conventions.** ACD19 Def. 6's `Send` always produces a
ciphertext. Here `send` is total: if `message_encrypt` fails it returns the old state and the empty
wire, while the game records a send (honest runs never fail under `Corr.SpqrOffCorrect`). `initA` falls
back to a session without a sender chain if the initial X25519 agreement is all zero, and received
plaintexts pass through `padOrTruncatePlain ℓ` (`libsignalSessionScheme`). Effect: none. -/
def send [Inhabited PQ] (P : Params PQ PQC) (g : GhostState PQ) (m : List (BitVec 8)) (r : PQC) :
    GhostState PQ × List (BitVec 8) :=
  match SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session with
  | (.ok msg, s) =>
    ({ g with session := s, epoch := if g.party.sendsIn g.epoch then g.epoch else g.epoch + 1 },
      msg.serialized)
  | (.error _, _) => (g, [])

/-- `Rcv(st, c; rc)`: `SignalMessage::try_from` and `try_decrypt_from_record` with eager coins
`rc` and the party's expected address blob. On success: the new state (ghost epochs pushed / evicted
with the receiver chains), the ghost epoch of the chain used (`epoch + 1` for a new chain, which
also becomes the party's epoch), the index `counter + 1`, and the plaintext. Any failure is `none`
(the record is unchanged). -/
def receive [Inhabited PQ] (P : Params PQ PQC) (g : GhostState PQ) (c : List (BitVec 8))
    (rc : BitVec 256) : Option (GhostState PQ × ℕ × ℕ × List (BitVec 8)) :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
        g.session with
    | (.error _, _) => none
    | (.ok m, s) =>
      let idx := g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)
      let (t, epochs, cur) := match idx with
        | some i => (g.chainEpochs.getD i 0, g.chainEpochs, g.epoch)
        | none => (g.epoch + 1, g.chainEpochs ++ [g.epoch + 1], g.epoch + 1)
      let epochs := epochs.drop (epochs.length - s.receiverChains.length)
      some ({ g with session := s, epoch := cur, chainEpochs := epochs }, t, msg.counter.toNat + 1, m)

end Params

end LibsignalSession
end CryptoGames
