/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir

/-!
# The `libsignal-cli` CLI's PQXDH model-level statements and deviations

**Checked by Lean.** Model-level steady-state refinement (`PqCliSteadyRefinesSM`) and first-message
roundtrip (`PqCliFirstMessageRoundtrip`, `keysAt`) over the CLI's PQXDH models in `PqDir.lean`,
together with the PQXDH-mode deviation entries (see `Computational/docs/TRUSTED_BASE.md`;
out-of-memory handling on the binary is DEV-CLI15 in `CliBinaryPq.lean`).

**DEV-CLI3 (libsignal): pre-key messages in prost's canonical encoding only.** `CliSpecPqxdh`
covers `recv` of `3 ‖ m.bytes` for typed pre-key messages `m` (`PreKeyMessageFields.bytes`: fields in
`PreKeySignalMessage::new` order, each once), excluding prost's non-canonical decodings (reordered,
unknown, or repeated fields, or trailing key bytes). Effect: out of scope for non-canonical pre-key
messages.

**DEV-PQ5 (libsignal): trust on first use.** The first call that meets the peer's identity key pins
it in `identities/<peer>`, and every later call checks the pinned key (`PqParty.trusts`,
`PqDir.lean`). Effect: out of scope against identity substitution at first contact.

**DEV-PQ8 (libsignal): the CLI's fixed environment.** The clock is `UNIX_EPOCH` (record timestamps
`0`), identities are trusted on first use (DEV-PQ5), pre-keys are looked up by id in directory
files, one-time pre-keys and one-time Kyber pre-keys are emptied on use, and a last-resort Kyber
pre-key's `.base-keys` refuses when above `fileCapBytes` or on a seen `(signed pre-key id, base key)`
(`markKyberUsed`, `removeOpk`). Effect: out of scope.

**DEV-PQ9 (libsignal): unacknowledged sessions never expire.** Because `now` is `UNIX_EPOCH` and
every reachable record has timestamp `0`, libsignal's `MAX_UNACKNOWLEDGED_SESSION_AGE` (30-day)
expiry check never fires. Effect: none.

**DEV-PQ10 (machine model): bounded inputs.** Pre-key `recv` requires inner messages below
`2^32 - 2048` bytes, and `PqxdhPartyInSpecDomain` bounds session records and directory files below
`2^31` bytes and non-`.base-keys` directory files at `fileCapBytes` (`2^21` bytes; DEV-CLI21).
Effect: restricts the adversary.

**DEV-PQ11 (libsignal): no sessions with one's own account.** The models fix `self_session = false`,
matching the distinct party UUIDs of `partyAddress`. Effect: restricts the adversary.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## Proof targets (not trusted; proved in `Computational/Proofs/`) -/

/-- **Steady-state refinement of the CLI's session models**. On a party state `st` whose session `(x, g)` has its pre-key message
acknowledged (`pendingPreKey = false`):
1. send soundness: if `pqSendModel` accepts with `(st', out)`, then `st'` is `st` with the session
   state of the session model's `(pqxdhSessionParams W).send g m r` and the remote identity `k` of `g`
   pinned, and `out` is `2 ‖` its message;
2. receive soundness: if `pqRecvWhisperModel` accepts `2 ‖ c` with `(st', pt)`, then
   `(pqxdhSessionParams W).receive g c rc` succeeds with some `g'` and plaintext `pt`, and `st'` is `st` with
   the session state of `g'` and the remote identity `k` of `g'` pinned;
3. send completeness: if `st` trusts `g`'s remote identity `k`, then `pqSendModel` accepts, rejects
   or panics exactly when `sendModelPq` does, with stdout `2 ‖` its message;
4. receive completeness: if `st` trusts `g`'s remote identity `k`, then `pqRecvWhisperModel`
   accepts, rejects or panics exactly when `recvModelPq` does, with the same plaintext.
The session model's `Params.send` / `Params.receive` at `pqxdhSessionParams W` are what the SM game runs; the
record extras `x` and the ghost epochs are untouched by both. -/
def PqCliSteadyRefinesSM (W : PEParams) : Prop :=
  ∀ (st : PqParty) (x : RecordExtras) (g : GhostState Bytes),
    st.session = some (x, g) → g.session.pendingPreKey = false →
    (∀ (m r : Bytes) (st' : PqParty) (out : Bytes), pqSendModel W st m r = some (some (st', out)) →
      ∃ k, g.session.remoteIdentity = some k ∧
        st' = { st with peerId := some k,
                        session := some (x, { g with session := ((pqxdhSessionParams W).send g m r).1.session }) } ∧
        out = wireWhisper :: ((pqxdhSessionParams W).send g m r).2) ∧
    (∀ (c : Bytes) (rc : BitVec 256) (st' : PqParty) (pt : Bytes),
      pqRecvWhisperModel W st c rc = some (some (st', pt)) →
      ∃ (g' : GhostState Bytes) (t i : ℕ) (k : IdentityKey),
        (pqxdhSessionParams W).receive g c rc = some (g', t, i, pt) ∧ g'.session.remoteIdentity = some k ∧
        st' = { st with peerId := some k, session := some (x, { g with session := g'.session }) }) ∧
    (∀ (k : IdentityKey), g.session.remoteIdentity = some k → st.trusts k = true →
      (∀ m r : Bytes,
        (pqSendModel W st m r).map (Option.map Prod.snd) =
          (sendModelPq (fun _ => x) W g m r).map (Option.map fun (_, w) => wireWhisper :: w)) ∧
      (∀ (c : Bytes) (rc : BitVec 256),
        (pqRecvWhisperModel W st c rc).map (Option.map Prod.snd) =
          (recvModelPq (fun _ => x) W g c rc).map (Option.map Prod.snd)))

/-- **The keys `st` holds under the ids a bundle names** (the `ResponderPreKeySecrets` of `PqxdhCorrectModel.lean`):
the signed pre-key `spkId`, the Kyber pre-key `kpkId` (the one-time key if its file is not empty,
else the last-resort key) and, if named, the one-time pre-key `opkId` (`none` if one is missing or
used). On the ids of a pre-key message this is `preKeysNamedBy`. -/
def keysAt (st : PqParty) (spkId kpkId : BitVec 32) (opkId : Option (BitVec 32)) : Option ResponderPreKeySecrets :=
  preKeysNamedBy st
    { regId := 0, opkId := opkId, spkId := spkId, kpkId := kpkId,
      kyberCt := List.Vector.replicate 1568 0#8, baseKey := List.Vector.replicate 32 0#8,
      idPub := List.Vector.replicate 32 0#8, inner := [] }

/-- **First-message roundtrip through the CLI's models** (the CLI counterpart of
`PqxdhFirstMessageRoundtrip`). Alice `stA` (party A) and Bob `stB` (party B, no pinned identity
and no session) with the keys `k = keysAt stB …` and signatures `spkSig` / `kpkSig` that verify
(`signaturesVerify`) on Bob's bundle (`honestBundle`, Bob's identity and registration id), under the
primitive laws of `PqxdhFirstMessageRoundtrip`, for a plaintext with `pt.length + 2304 < 2^32`: if
Alice's `init` on that bundle and then her `send` of `pt` with coins `rs` are accepted, the wire is
`3 ‖ m.bytes` for a typed pre-key message `m` naming Bob's keys' ids, with
`m.inner.length + 2048 < 2^32` (so `recv` of it is in `CliSpecPqxdh`'s domain), and when
Bob's store accepts the Kyber pre-key's use (`markKyberUsed`: last-resort `.base-keys` at most
`fileCapBytes` and not a replayed `(signed pre-key id, base key)`), Bob's `recv` of it (any coins)
is accepted with stdout `pt`. -/
def PqCliFirstMessageRoundtrip (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ (stA stB : PqParty) (k : ResponderPreKeySecrets) (spkSig kpkSig : List.Vector (BitVec 8) 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) (rs : List.Vector (BitVec 8) 64)
    (rc : BitVec 256) (pt : Bytes) (stA₁ stA₂ : PqParty) (o w : Bytes),
    stA.party = .A → stB.party = .B → stB.peerId = none → stB.session = none →
    keysAt stB k.spkId k.kpkId (k.opk.map Prod.fst) = some k →
    -- X25519: agreement commutes on clamped scalars, and is never all zero between honest keys
    (∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) =
      W.C.X (Ratchet.clampScalar b) (W.C.pubKey (Ratchet.clampScalar a))) →
    (∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8) →
    -- Kyber: decapsulation with Bob's secret key inverts encapsulation to his public key
    (∀ coins, W.Q.decaps k.kpkSec (W.Q.encaps k.kpkPub coins).1 = (W.Q.encaps k.kpkPub coins).2) →
    -- honest X25519 public keys are canonical
    (∀ a, SignalPqxdh.isCanonicalRef (modelPrims X W)
      (vecU8 (W.C.pubKey (Ratchet.clampScalar a))) = true) →
    -- AES-256: decryption inverts encryption
    (∀ key blk, W.C.D key (W.C.E key blk) = blk) →
    pt.length + 2304 < 2 ^ 32 →
    (honestBundle W.C stB.me k spkSig kpkSig).signaturesVerify X W = true →
    pqInitModel X W stA (honestBundle W.C stB.me k spkSig kpkSig) t = some (some (stA₁, o)) →
    pqSendModel W stA₁ pt rs.toList = some (some (stA₂, w)) →
    ∃ m : PreKeyMessageFields, w = wirePrekey :: m.bytes ∧ m.inner.length + 2048 < 2 ^ 32 ∧
      m.spkId = k.spkId ∧ m.kpkId = k.kpkId ∧ m.opkId = k.opk.map Prod.fst ∧
      ∀ stB₁, markKyberUsed stB m = some stB₁ →
        (pqRecvPrekeyModel X W stB m rc).map (Option.map Prod.snd) = some (some pt)

end CryptoVerification.SignalSession
