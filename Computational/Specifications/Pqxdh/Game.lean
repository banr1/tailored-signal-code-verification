/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Multi-session key-indistinguishability game infrastructure for PQXDH

**Trusted: the statement.** Defines the multi-session key-indistinguishability (`KeyInd`) oracle
types and handler (`KeyIndQuery`, `KeyIndResponse`, `KeyIndState`, `pqxdhKeyIndImpl`), freshness
predicates (`isKeyIndInitStillFresh`, `isKeyIndRespStillFresh`), replication bounds (`Setup`), and
query budgets (`QueryBudget`) used by `Security/Headline.lean`, `Security/HeadlineDelta.lean`, and
`Assumptions/{KeyInd1KeyReal,KeyInd1KeyRo}.lean`. See `Computational/docs/TRUSTED_BASE.md`.

Honest parties execute the PQXDH handshake model of
`LibsignalBinary/Specifications/SignalPqxdh/Model.lean` (`Model.acceptKeys`, `buildSecrets`) over
abstract `Primitives` while the adversary controls the network, schedules sessions, corrupts
identity keys, and reveals signed pre-key secrets. Game structure and freshness clauses follow the
CryptoVerif model `PQXDH.m4.ocv` of BJKS24 (Bhargavan, Jacomme, Kiefer, Schmidt, USENIX Security
2024; see `Computational/docs/README.md`).

Key modelling choices (`Computational/docs/DEVIATIONS.md`):
- **One-key identities.** The headline experiments (`KeyInd1KeyReal.lean`, `KeyInd1KeyRo.lean`)
  override `.initPrin` to derive both X25519 (`secIKA0`) and XEdDSA (`secIKAsign`) from a single
  32-byte scalar; `PrincipalEntry` retains separate fields so the standalone two-key game can share
  the remaining handlers.
- **Handshake KDF (DEV-PQ14).** `useRo = true` models `HkdfRO` as a lazy caching random oracle;
  `useRo = false` evaluates `P.hkdfDerive96`.
- **Known-secret-key (KOSK) registration (DEV-PQ15).** Adversarial X25519 identity, signed, and
  one-time pre-keys supplied to honest sessions must be registered with their secret scalar via
  `registerKey` (or be game-generated keys of the same role), weakening the model by restricting the
  adversary.
- **Canonical ephemeral keys (DEV-PQ16).** Responders reject non-canonical X25519 ephemeral keys
  `ekAPk`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

abbrev KeyId := UInt32

open OracleComp OracleSpec ENNReal

/-! ## Uniform byte sampling -/

/-- Little-endian 32-byte encoding of `w`. -/
def word256ToBytes (w : BitVec 256) : Bytes :=
  List.ofFn (fun (i : Fin 32) => UInt8.ofNat ((w.toNat >>> (8 * i.val)) % 256))

/-- Little-endian 16-byte encoding of `w`. -/
def word128ToBytes (w : BitVec 128) : Bytes :=
  List.ofFn (fun (i : Fin 16) => UInt8.ofNat ((w.toNat >>> (8 * i.val)) % 256))

def sampleBytes32 : ProbComp Bytes :=
  word256ToBytes <$> ($ᵗ BitVec 256)

def sampleScalar32 : ProbComp Bytes :=
  sampleBytes32

def sampleCoins32 : ProbComp Bytes :=
  sampleBytes32

def sampleRandom64 : ProbComp Bytes := do
  let b1 ← sampleBytes32
  let b2 ← sampleBytes32
  return (b1 ++ b2)

def sampleDRKey96 : ProbComp DRKey := do
  let rk ← sampleBytes32
  let ck ← sampleBytes32
  let pk ← sampleBytes32
  return { rootKey := rk, chainKey := ck, pqrKey := pk }

def sampleMessageKeys80 : ProbComp MessageKeys := do
  let ck ← sampleBytes32
  let mk ← sampleBytes32
  let iv ← word128ToBytes <$> ($ᵗ BitVec 128)
  return { cipherKey := ck, macKey := mk, iv := iv }

def sampleKemKeyGen (P : Primitives) : ProbComp (Bytes × Bytes) := do
  let seed ← sampleRandom64
  return P.kemKeyGen seed

/-! ## Replication bounds and session identifiers -/

/-- Multi-user, multi-session replication bounds on principals, pre-key bundles, one-time
pre-keys, and sessions (`PQXDH.m4.ocv`). -/
structure Setup where
  N_id          : Nat -- max honest principals (`initPrin`)
  N_recv        : Nat -- max SPK + PQSPK bundles per principal (`genSPK`)
  N_opk         : Nat -- max OPKs / `recvOPK` sessions per bundle (`genOPK`)
  N_no_opk      : Nat -- max `recvNoOPK` sessions per bundle
  N_send_opk    : Nat -- max initiator With-OPK sessions per principal
  N_send_no_opk : Nat -- max initiator No-OPK sessions per principal
  deriving DecidableEq, Repr

namespace Setup

def N_spk_tot (S : Setup) : Nat := S.N_id * S.N_recv

def N_opk_tot (S : Setup) : Nat := S.N_spk_tot * S.N_opk

def N_no_opk_tot (S : Setup) : Nat := S.N_spk_tot * S.N_no_opk

def N_recv_tot (S : Setup) : Nat := S.N_opk_tot + S.N_no_opk_tot

def N_send_opk_tot (S : Setup) : Nat := S.N_id * S.N_send_opk

def N_send_no_opk_tot (S : Setup) : Nat := S.N_id * S.N_send_no_opk

def N_send_tot (S : Setup) : Nat := S.N_send_opk_tot + S.N_send_no_opk_tot

def N_sess_tot (S : Setup) : Nat := S.N_send_tot + S.N_recv_tot

/-- Total honestly generated X25519 keypairs across the game. -/
def N_dh (S : Setup) : Nat := S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot

end Setup

/-- Session slot identifier for initiator (`sendOPK`, `sendNoOPK`) and responder (`recvOPK`,
`recvNoOPK`) sessions. -/
inductive SessionId (S : Setup) where
  | sendOPK   (u : Fin S.N_id) (i : Fin S.N_send_opk)
  | sendNoOPK (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
  | recvOPK   (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
  | recvNoOPK (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
  deriving DecidableEq, Repr

/-! ## Principal, bundle, and pre-key state -/

/-- State of an initialized honest principal `u : Fin S.N_id`. The one-key headline games set
`secIKAsign := secIKA0` and `ikSignPk := ikAPk` from a single scalar; the fields remain separate so
the standalone two-key game can share `pqxdhKeyIndImpl`. -/
structure PrincipalEntry where
  secIKA0    : Bytes -- 32B X25519 identity secret scalar
  ikAPk      : Bytes -- 32B wire identity public key
  secIKAsign : Bytes -- 32B XEdDSA signing secret scalar
  ikSignPk   : Bytes -- 32B XEdDSA verification public key
  corrupted  : Bool  -- true iff `corruptIK u` has been called
  deriving DecidableEq, Repr

/-- Honestly generated signed EC pre-key and Kyber-1024 pre-key bundle `(u, j)`. -/
structure SpkBundleEntry where
  spkSk    : Bytes -- 32B `SPK_B.sk`
  spkPk    : Bytes -- 32B `SPK_B.pk`
  spkSig   : Bytes -- 64B XEdDSA signature over `encodeEC spkPk`
  pqspkSk  : Bytes -- 3168B `PQSPK_B.sk`
  pqspkPk  : Bytes -- 1568B `PQSPK_B.pk`
  pqspkSig : Bytes -- 64B XEdDSA signature over `encodeKEM pqspkPk`
  revealed : Bool := false -- true once `revealSpkSk u j` has been queried
  deriving DecidableEq, Repr

/-- Honestly generated one-time EC pre-key `(u, j, o)`. -/
structure OpkEntry where
  opkSk    : Bytes -- 32B `OPK_B.sk`
  opkPk    : Bytes -- 32B `OPK_B.pk`
  consumed : Bool  -- true once consumed by `acceptOPK`
  deriving DecidableEq, Repr

/-- First honest principal whose `ikAPk` matches `ikB` modulo the cofactor projection `pow8`. -/
def findHonestPrincipal (P : Primitives) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : Option (Nat × PrincipalEntry) :=
  principals.find? (fun (_, entry) => P.pow8 ikB == P.pow8 entry.ikAPk)

/-- XEdDSA verification key for `ikB`: `entry.ikSignPk` if `ikB` belongs to an honest principal,
and `ikB` otherwise. -/
def resolveSigPk (P : Primitives) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) : Bytes :=
  match findHonestPrincipal P principals ikB with
  | some (_, entry) => entry.ikSignPk
  | none            => ikB

/-- Index of the honest principal matching `ikB` if currently uncorrupted, or `none`. -/
def isHonestUncorruptedPeer (P : Primitives) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : Option Nat :=
  match findHonestPrincipal P principals ikB with
  | some (k, entry) => if !entry.corrupted then some k else none
  | none            => none

/-- Whether `(spkB, opkB?, pqspkB)` in `bundle` were honestly generated by the principal owning
`bundle.ikB` (with EC keys compared modulo `pow8`). -/
def checkBundleProvenance (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : Bool × Bool × Bool :=
  match findHonestPrincipal P principals bundle.ikB with
  | none => (false, false, false)
  | some (k, _) =>
    let spkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && P.pow8 b.spkPk == P.pow8 bundle.spkB)
    let pqspkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon :=
      match bundle.opkB? with
      | none => false
      | some (_, opkPk) =>
        opkEntries.any (fun ((u, _, _), e) =>
          u == k && P.pow8 e.opkPk == P.pow8 opkPk)
    (spkHon, opkHon, pqspkHon)

/-! ### Known-secret-key (KOSK) registration (DEV-PQ15)

Every X25519 public key supplied to an honest session in an identity, signed-pre-key, or
one-time-pre-key position must either be a game-generated key of the same role or be registered
with its 32-byte secret scalar via `registerKey sk` (all comparisons modulo `pow8`; `ekAPk` and
`pqspkB` are unrestricted). Without KOSK, adversarial keys with unknown discrete logs induce a
4-point DH relation on `DH1` that a 3-point GapDH oracle cannot test. Registration weakens the
model by disallowing unregistered unknown-secret public keys, while remaining pure bookkeeping that
does not mark keys honest or affect freshness or partnering. -/

def isAdvRegistered (P : Primitives) (advKeys : List (Bytes × Bytes)) (pk : Bytes) : Bool :=
  advKeys.any (fun (_, pk') => P.pow8 pk == P.pow8 pk')

def isGameIdKey (P : Primitives) (principals : List (Nat × PrincipalEntry)) (pk : Bytes) : Bool :=
  (findHonestPrincipal P principals pk).isSome

def isGameSpk (P : Primitives) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    Bool :=
  spkBundles.any (fun (_, b) => P.pow8 b.spkPk == P.pow8 pk)

def isGameOpk (P : Primitives) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (pk : Bytes) :
    Bool :=
  opkEntries.any (fun (_, e) => P.pow8 e.opkPk == P.pow8 pk)

/-- Role-strict KOSK check on an initiator's peer bundle (`ikB`, `spkB`, and `opkB?` modulo
`pow8`). -/
def koskBundleOk (P : Primitives) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) : Bool :=
  (isGameIdKey P principals bundle.ikB || isAdvRegistered P advKeys bundle.ikB) &&
  (isGameSpk P spkBundles bundle.spkB || isAdvRegistered P advKeys bundle.spkB) &&
  (match bundle.opkB? with
   | none => true
   | some (_, opkPk) => isGameOpk P opkEntries opkPk || isAdvRegistered P advKeys opkPk)

/-- Role-strict KOSK check on a responder's claimed sender identity key `ikAPk`. -/
def koskSenderOk (P : Primitives) (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) : Bool :=
  isGameIdKey P principals ikAPk || isAdvRegistered P advKeys ikAPk

/-- Register a 32-byte adversarial secret scalar `sk` as `(P.x25519Base sk, (sk, pk) :: advKeys)`. -/
def registerAdvKey (P : Primitives) (advKeys : List (Bytes × Bytes)) (sk : Bytes) :
    Option (Bytes × List (Bytes × Bytes)) :=
  if sk.length != 32 then none
  else
    let pk := P.x25519Base sk
    some (pk, (sk, pk) :: advKeys)

/-- Evaluate the 96-byte handshake KDF via the lazy caching random oracle `roCache` when
`useRo = true` (DEV-PQ14) or via `P.hkdfDerive96` when `useRo = false`. -/
def evalHkdfOrRo (useRo : Bool) (P : Primitives) (roCache : List (Bytes × DRKey))
    (secrets : Bytes) : ProbComp (DRKey × List (Bytes × DRKey)) := do
  if !useRo then
    return (P.hkdfDerive96 secrets, roCache)
  else
    match roCache.find? (fun (s, _) => s == secrets) with
    | some (_, dk) => return (dk, roCache)
    | none =>
      let dk ← sampleDRKey96
      return (dk, (secrets, dk) :: roCache)

/-- Insert `(k, pqspkId, spkId, ekAPk)` into Bob's seen-base-key set if absent; the `Bool` result
is `true` iff the tuple is fresh. -/
def checkAndMarkKyberBaseKeySeen (usedTriples : List (Nat × KeyId × KeyId × Bytes))
    (k : Nat) (pqspkId spkId : KeyId) (ekAPk : Bytes) :
    Bool × List (Nat × KeyId × KeyId × Bytes) :=
  let entry := (k, pqspkId, spkId, ekAPk)
  if usedTriples.contains entry then
    (false, usedTriples)
  else
    (true, entry :: usedTriples)

/-! ## Key-indistinguishability game (`KeyInd`) -/

/-- Initiator session record in `KeyInd`. -/
structure KeyIndInitiatorEntry (S : Setup) where
  sid         : SessionId S
  honestPeer  : Option Nat -- `some k` iff target `ikB` was honest and uncorrupted at initiation time
  peerIkPk    : Bytes
  peerSpkPk   : Bytes
  peerOpkPk?  : Option Bytes
  peerPqspkPk : Bytes
  spkHonest   : Bool
  opkHonest   : Bool
  pqspkHonest : Bool
  ekASk       : Bytes
  fresh       : Bool
  drKeyReal   : DRKey
  drKeyRand   : DRKey
  hdr         : HandshakeHdr
  tested      : Bool       -- true once `testSession sid` has been queried
  revealed    : Bool := false -- true once `revealSessionKey sid` has been queried
  deriving DecidableEq, Repr

/-- Responder session record in `KeyInd`, created on successful `acceptOPK` or `acceptNoOPK`. -/
structure KeyIndRespEntry (S : Setup) where
  sid          : SessionId S
  respIkPk     : Bytes          -- responder's wire identity key
  spkPk        : Bytes          -- responder's SPK used
  opkPk?       : Option Bytes   -- responder's OPK used (if any)
  pqspkPk      : Bytes          -- responder's PQSPK used
  hdr          : HandshakeHdr   -- received header
  senderHonest : Bool
  drKeyReal    : DRKey
  drKeyRand    : DRKey
  tested       : Bool := false
  revealed     : Bool := false
  deriving DecidableEq, Repr

/-- Partnering between initiator session `s` and responder session `r`: agreement on all
KDF-determining keys (`ikAPk`, `peerIkPk`/`respIkPk`, `spkPk`, and `opkPk?` modulo `pow8`, plus
byte-exact `ekAPk`, `pqspkPk`, and `kemCt`). Malleable header key IDs are ignored. -/
def keyIndPartner {S : Setup} (P : Primitives) (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    Bool :=
  P.pow8 s.hdr.ikAPk == P.pow8 r.hdr.ikAPk &&
  P.pow8 s.peerIkPk == P.pow8 r.respIkPk &&
  P.pow8 s.peerSpkPk == P.pow8 r.spkPk &&
  s.peerOpkPk?.map P.pow8 == r.opkPk?.map P.pow8 &&
  s.hdr.ekAPk == r.hdr.ekAPk &&
  s.peerPqspkPk == r.pqspkPk &&
  s.hdr.kemCt == r.hdr.kemCt

/-- Whether `pk` matches (modulo `pow8`) a game-generated SPK whose secret was revealed via
`revealSpkSk`. -/
def isSpkRevealed (P : Primitives) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    Bool :=
  spkBundles.any (fun (_, b) => b.revealed && P.pow8 b.spkPk == P.pow8 pk)

/-- Post-game key-compromise freshness clause for an initiator session `s` that was fresh at
initiation (`s.fresh = true`):
- Classical (`useRo = true`): either the peer identity key remains uncorrupted, an unrevealed
  honest SPK was used, or an honest OPK was used (`pqspkHonest` is excluded because the classical
  bound does not assume KEM IND-CCA).
- Post-quantum HNDL (`useRo = false`, where `.revealDhSecrets` exposes X25519 scalars):
  `s.pqspkHonest`. -/
def keyIndInitCorruptionClause {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (s : KeyIndInitiatorEntry S) : Bool :=
  s.fresh &&
  (if useRo then
     (isHonestUncorruptedPeer P principals s.peerIkPk).isSome ||
     (s.spkHonest && !isSpkRevealed P spkBundles s.peerSpkPk) || s.opkHonest
   else
     s.pqspkHonest)

/-- End-of-game freshness of a tested initiator session `s`: `keyIndInitCorruptionClause` holds,
`s` is unrevealed, and every partnered responder session is unrevealed with `senderHonest = true`
(dishonest-sender accepts return `.drKeyResp` immediately). -/
def isKeyIndInitStillFresh {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (respSessions : List (KeyIndRespEntry S))
    (s : KeyIndInitiatorEntry S) : Bool :=
  keyIndInitCorruptionClause P useRo principals spkBundles s && !s.revealed &&
  respSessions.all (fun r => !(keyIndPartner P s r) || (r.senderHonest && !r.revealed))

/-- End-of-game freshness of a tested responder session `r`: `r` is unrevealed with
`r.senderHonest = true`, and if `r` has any partnered initiator session then every partner is
unrevealed and satisfies `keyIndInitCorruptionClause`; otherwise (unpartnered) `useRo = true`, the
claimed sender remains uncorrupted, and `r.spkPk` has not been revealed via `revealSpkSk`. -/
def isKeyIndRespStillFresh {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (sessions : List (KeyIndInitiatorEntry S))
    (r : KeyIndRespEntry S) : Bool :=
  !r.revealed && r.senderHonest &&
  (if sessions.any (fun s => keyIndPartner P s r) then
     sessions.all (fun s =>
       !(keyIndPartner P s r) ||
       (!s.revealed && keyIndInitCorruptionClause P useRo principals spkBundles s))
   else
     useRo && (isHonestUncorruptedPeer P principals r.hdr.ikAPk).isSome &&
     !isSpkRevealed P spkBundles r.spkPk)

/-- Oracle queries of the `KeyInd` game. Includes KOSK registration (`registerKey`, DEV-PQ15) and
signed-pre-key secret reveal (`revealSpkSk`, used when composing with the Double Ratchet SM game
where Bob's SPK serves as his initial ratchet key). -/
inductive KeyIndQuery (S : Setup) where
  | initPrin        (u : Fin S.N_id)
  | corruptIK       (u : Fin S.N_id)
  | genSPK          (u : Fin S.N_id) (j : Fin S.N_recv)
  | genOPK          (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
  | initiateOPK     (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
  | initiateNoOPK   (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
  | acceptOPK       (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
  | acceptNoOPK     (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
  | testSession     (sid : SessionId S)
  | roQuery         (secrets : Bytes)
  | revealDhSecrets
  | revealSessionKey (sid : SessionId S)
  | registerKey     (sk : Bytes) -- KOSK registration (DEV-PQ15)
  | revealSpkSk     (u : Fin S.N_id) (j : Fin S.N_recv) -- SPK secret reveal
  deriving DecidableEq, Repr

/-- Oracle responses of the `KeyInd` game. -/
inductive KeyIndResponse where
  | noneResp
  | initPrinResp    (ikAPk ikSignPk : Bytes)
  | pkResp          (pk : Bytes)
  | corrResp        (ikSk sigSk : Bytes)
  | bundleResp      (bundle : PreKeyBundleInput)
  | hdrResp         (hdr : HandshakeHdr)
  | initUnfreshResp (drKey : DRKey) (hdr : HandshakeHdr)
  | acceptFreshResp
  | drKeyResp       (drKey : DRKey)
  | dhSecretsResp   (ikDhSks spkSks opkSks ekSks : List Bytes)
  | spkSkResp       (spkSk : Bytes)
  deriving DecidableEq, Repr

@[reducible] def keyIndSpec (S : Setup) : OracleSpec (KeyIndQuery S) :=
  fun _ => KeyIndResponse

/-- Adversary in the `KeyInd` game. -/
structure KeyIndAdversary (S : Setup) where
  run : OracleComp (unifSpec + keyIndSpec S) Bool

/-- Mutable game state for `KeyInd`. -/
structure KeyIndState (S : Setup) where
  secb             : Bool
  principals       : List (Nat × PrincipalEntry)
  spkBundles       : List ((Nat × Nat) × SpkBundleEntry)
  opkEntries       : List ((Nat × Nat × Nat) × OpkEntry)
  sessions         : List (KeyIndInitiatorEntry S)
  respSessions     : List (KeyIndRespEntry S) := []
  usedRecvOPK      : List (Nat × Nat × Nat)
  usedRecvNoOPK    : List (Nat × Nat × Nat)
  seenKyberBaseKeys : List (Nat × KeyId × KeyId × Bytes)
  roCache          : List (Bytes × DRKey)
  advKeys          : List (Bytes × Bytes) := [] -- registered `(sk, pk)` pairs (DEV-PQ15)

def KeyIndState.empty (S : Setup) (secb : Bool) : KeyIndState S :=
  { secb             := secb
    principals       := []
    spkBundles       := []
    opkEntries       := []
    sessions         := []
    respSessions     := []
    usedRecvOPK      := []
    usedRecvNoOPK    := []
    seenKyberBaseKeys := []
    roCache          := []
    advKeys          := [] }

/-- Whether `testSession sid` is permitted: `sid` must be unrevealed, untested, and initiated
toward an uncorrupted honest peer (`e.fresh`, initiator) or accepted from an honest claimed sender
(`r.senderHonest`, responder). -/
def isKeyIndSessionTestable {S : Setup} (st : KeyIndState S) (sid : SessionId S) : Bool :=
  match st.sessions.find? (fun e => e.sid == sid) with
  | some e => e.fresh && !e.tested && !e.revealed
  | none   =>
    match st.respSessions.find? (fun r => r.sid == sid) with
    | some r => r.senderHonest && !r.tested && !r.revealed
    | none   => false

/-- Record an accepted responder session; reuses a partnered initiator's `drKeyRand` when one
exists so partnered sessions share one random-world key, and samples a fresh key otherwise. -/
def recordKeyIndResp (S : Setup) (P : Primitives) (r : KeyIndRespEntry S) :
    StateT (KeyIndState S) ProbComp Unit := do
  let st ← get
  let drKeyRand ← match st.sessions.find? (fun s => keyIndPartner P s r) with
    | some s => pure s.drKeyRand
    | none   => liftM sampleDRKey96
  set { st with respSessions := { r with drKeyRand := drKeyRand } :: st.respSessions }

/-- Random-world key of an already recorded responder session partnered with `s`, if any. -/
def keyIndPartnerRandKey? {S : Setup} (P : Primitives) (respSessions : List (KeyIndRespEntry S))
    (s : KeyIndInitiatorEntry S) : Option DRKey :=
  (respSessions.find? (fun r => keyIndPartner P s r)).map (fun r => r.drKeyRand)

/-- Execute an initiator handshake query (`initiateOPK` or `initiateNoOPK`); reuses any
already-recorded partnered responder's `drKeyRand` so accept-before-initiate partners remain
consistent in the random world. -/
def runKeyIndInitiate (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.sessions.any (fun e => e.sid == sid) then
    return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let ekASk ← liftM sampleScalar32
  let kemCoins ← liftM sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer := isHonestUncorruptedPeer P st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
  let sessEntry : KeyIndInitiatorEntry S := {
    sid         := sid
    honestPeer  := honestPeer
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    fresh       := honestPeer.isSome
    drKeyReal   := drKeyReal
    drKeyRand   := drKeyReal -- placeholder; replaced below (`keyIndPartner` ignores it)
    hdr         := hdr
    tested      := false
  }
  let drKeyRand ← match keyIndPartnerRandKey? P st.respSessions sessEntry with
    | some k => pure k
    | none   => liftM sampleDRKey96
  set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions,
                roCache := roCache' }
  match findHonestPrincipal P st.principals bundle.ikB with
  | some _ => return .hdrResp hdr
  | none   => return .initUnfreshResp drKeyReal hdr

/-- Shared `KeyInd` oracle handler (`useRo = true` for `HkdfRO`, `useRo = false` for concrete
`P.hkdfDerive96`). The one-key headline handlers override `.initPrin` to derive both identity keys
from a single scalar and delegate all other queries here. -/
def pqxdhKeyIndImpl (useRo : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp) := fun q => do
  let st ← get
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM sampleScalar32
    let ikAPk := P.x25519Base secIKA0
    let secIKAsign ← liftM sampleScalar32
    let ikSignPk := P.sigPkGen secIKAsign
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := secIKAsign
      ikSignPk   := ikSignPk
      corrupted  := false
    }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikSignPk
  | .corruptIK u =>
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return .noneResp
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      set { st with principals := principals' }
      return .corrResp entry.secIKA0 entry.secIKAsign
  | .genSPK u j =>
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return .noneResp
    let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
      | return .noneResp
    let spkSk ← liftM sampleScalar32
    let spkPk := P.x25519Base spkSk
    let rSpk ← liftM sampleRandom64
    let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
    let (pqspkPk, pqspkSk) ← liftM (sampleKemKeyGen P)
    let rPq ← liftM sampleRandom64
    let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry := {
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    set { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return .bundleResp bundleOut
  | .genOPK u j o =>
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return .noneResp
    let opkSk ← liftM sampleScalar32
    let opkPk := P.x25519Base opkSk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    set { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
    return .pkResp opkPk
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then return .noneResp
    runKeyIndInitiate useRo S P (.sendOPK u i) u bundle
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then return .noneResp
    runKeyIndInitiate useRo S P (.sendNoOPK u i) u bundle
  | .acceptOPK k j o hdr =>
    -- header pre-key IDs and 32-byte EC key lengths
    if !(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return .noneResp
    if oEntry.consumed then return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
    let accInp : AcceptKeysInput := {
      ikBSk       := kEntry.secIKA0
      ikBPk       := kEntry.ikAPk
      spkBSk      := bEntry.spkSk
      spkBPk      := bEntry.spkPk
      opkBSk?     := some oEntry.opkSk
      pqspkBSk    := bEntry.pqspkSk
      pqspkBPk    := bEntry.pqspkPk
      trustedPeer := true
      replayOk    := replayOk
      hdr         := hdr
    }
    let some _ := Model.acceptKeys P accInp | return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
    let dh4 := P.x25519 oEntry.opkSk hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    set { st with
      opkEntries       := opkEntries'
      usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
      seenKyberBaseKeys := usedTriples'
      roCache          := roCache' }
    let senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome
    recordKeyIndResp S P {
      sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
      opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
      senderHonest := senderHonest, drKeyReal := drKey, drKeyRand := drKey }
    -- suppress `drKey` whenever `hdr.ikAPk` belongs to an honest principal (even if later corrupted)
    match findHonestPrincipal P st.principals hdr.ikAPk with
    | some _ => return .acceptFreshResp
    | none   => return .drKeyResp drKey
  | .acceptNoOPK k j l hdr =>
    if !(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32) then
      return .noneResp
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
    let accInp : AcceptKeysInput := {
      ikBSk       := kEntry.secIKA0
      ikBPk       := kEntry.ikAPk
      spkBSk      := bEntry.spkSk
      spkBPk      := bEntry.spkPk
      opkBSk?     := none
      pqspkBSk    := bEntry.pqspkSk
      pqspkBPk    := bEntry.pqspkPk
      trustedPeer := true
      replayOk    := replayOk
      hdr         := hdr
    }
    let some _ := Model.acceptKeys P accInp | return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
    set { st with
      usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
      seenKyberBaseKeys := usedTriples'
      roCache          := roCache' }
    let senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome
    recordKeyIndResp S P {
      sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
      opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
      senderHonest := senderHonest, drKeyReal := drKey, drKeyRand := drKey }
    match findHonestPrincipal P st.principals hdr.ikAPk with
    | some _ => return .acceptFreshResp
    | none   => return .drKeyResp drKey
  | .testSession sid =>
    if !isKeyIndSessionTestable st sid then
      return .noneResp
    match st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      let sessions' := st.sessions.map (fun s =>
        if s.sid == sid then { s with tested := true } else s)
      set { st with sessions := sessions' }
      return .drKeyResp (if st.secb then e.drKeyReal else e.drKeyRand)
    | none =>
      match st.respSessions.find? (fun r => r.sid == sid) with
      | none => return .noneResp
      | some r =>
        let resp' := st.respSessions.map (fun x =>
          if x.sid == sid then { x with tested := true } else x)
        set { st with respSessions := resp' }
        return .drKeyResp (if st.secb then r.drKeyReal else r.drKeyRand)
  | .revealSessionKey sid =>
    match st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      if e.tested then return .noneResp
      let sessions' := st.sessions.map (fun s =>
        if s.sid == sid then { s with revealed := true } else s)
      set { st with sessions := sessions' }
      return .drKeyResp e.drKeyReal
    | none =>
      match st.respSessions.find? (fun r => r.sid == sid) with
      | none => return .noneResp
      | some r =>
        if r.tested then return .noneResp
        let resp' := st.respSessions.map (fun x =>
          if x.sid == sid then { x with revealed := true } else x)
        set { st with respSessions := resp' }
        return .drKeyResp r.drKeyReal
  | .revealSpkSk u j =>
    match st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none => return .noneResp
    | some (_, bEntry) =>
      let spkBundles' := st.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
      set { st with spkBundles := spkBundles' }
      return .spkSkResp bEntry.spkSk
  | .registerKey sk =>
    match registerAdvKey P st.advKeys sk with
    | none => return .noneResp
    | some (pk, advKeys') =>
      set { st with advKeys := advKeys' }
      return .pkResp pk
  | .roQuery secrets =>
    if !useRo then
      return .noneResp
    let (dk, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
    set { st with roCache := roCache' }
    return .drKeyResp dk
  | .revealDhSecrets =>
    if useRo then
      return .noneResp
    let ikDhSks := st.principals.map (fun (_, e) => e.secIKA0)
    let spkSks  := st.spkBundles.map (fun (_, b) => b.spkSk)
    let opkSks  := st.opkEntries.map (fun (_, o) => o.opkSk)
    let ekSks   := st.sessions.map (fun s => s.ekASk)
    return .dhSecretsResp ikDhSks spkSks opkSks ekSks

/-! ## Query-budget predicates -/

def isKeyIndRoQuery {S : Setup} : (Nat ⊕ KeyIndQuery S) → Prop
  | .inr (.roQuery _) => True
  | _                 => False

instance {S : Setup} : DecidablePred (@isKeyIndRoQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isKeyIndRoQuery]; infer_instance
  · cases q <;> simp only [isKeyIndRoQuery] <;> infer_instance

def isKeyIndSendQuery {S : Setup} : (Nat ⊕ KeyIndQuery S) → Prop
  | .inr (.initiateOPK _ _ _)   => True
  | .inr (.initiateNoOPK _ _ _) => True
  | _                           => False

instance {S : Setup} : DecidablePred (@isKeyIndSendQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isKeyIndSendQuery]; infer_instance
  · cases q <;> simp only [isKeyIndSendQuery] <;> infer_instance

def isKeyIndRecvQuery {S : Setup} : (Nat ⊕ KeyIndQuery S) → Prop
  | .inr (.acceptOPK _ _ _ _)   => True
  | .inr (.acceptNoOPK _ _ _ _) => True
  | _                           => False

instance {S : Setup} : DecidablePred (@isKeyIndRecvQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isKeyIndRecvQuery]; infer_instance
  · cases q <;> simp only [isKeyIndRecvQuery] <;> infer_instance

/-- Online (non-random-oracle) game queries in `KeyIndQuery S`: every `.inr q` except
`.roQuery _`. -/
def isKeyIndOnlineQuery {S : Setup} : (Nat ⊕ KeyIndQuery S) → Prop
  | .inr (.roQuery _) => False
  | .inr _            => True
  | .inl _            => False

instance {S : Setup} : DecidablePred (@isKeyIndOnlineQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isKeyIndOnlineQuery]; infer_instance
  · cases q <;> simp only [isKeyIndOnlineQuery] <;> infer_instance

/-- Explicit oracle-query budget for a game adversary: `q_ro` `HkdfRO` queries, `q_roRoot`
`RootKdfRO` queries, `q_total` total game-oracle queries (`isGameQuery`), and `q_on` online non-RO
queries (`isKeyIndOnlineQuery`). Passed explicitly to reductions so they never inspect `A`. -/
structure QueryBudget where
  q_ro     : Nat
  q_roRoot : Nat
  q_total  : Nat
  q_on     : Nat
  deriving DecidableEq, Repr

/-- True on game-oracle queries (`.inr _`) and false on uniform random sampling (`.inl _`). -/
def isGameQuery {ι : Type} : (Nat ⊕ ι) → Bool
  | .inr _ => true
  | .inl _ => false

/-- True on game-oracle queries `.inr t` of kind `i` (`kind t = i`) and false on uniform random
sampling (`.inl _`); used to state per-kind query bounds (`CostBoundedByKind`). -/
def isGameQueryOfKind {ι : Type} {n : Nat} (kind : ι → Fin n) (i : Fin n) : (Nat ⊕ ι) → Bool
  | .inr t => decide (kind t = i)
  | .inl _ => false

/-- Typeclass asserting that an adversary `A` respects a `QueryBudget` together with the
session-slot bounds from `Setup`. -/
class HasQueryBound (Adv : Type) where
  QueryBounded : Adv → QueryBudget → Prop

export HasQueryBound (QueryBounded)

instance {S : Setup} : HasQueryBound (KeyIndAdversary S) where
  QueryBounded A b :=
    OracleComp.IsQueryBoundP A.run isKeyIndRoQuery b.q_ro ∧
    OracleComp.IsQueryBoundP A.run isKeyIndSendQuery S.N_send_tot ∧
    OracleComp.IsQueryBoundP A.run isKeyIndRecvQuery S.N_recv_tot ∧
    OracleComp.IsQueryBoundP A.run (fun q => isGameQuery q = true) b.q_total ∧
    OracleComp.IsQueryBoundP A.run isKeyIndOnlineQuery b.q_on

/-- Adversary paired with a proof that it respects query budget `b`. `A` has unrestricted
computation steps; efficiency enters via explicit step-cost bounds on the reductions. -/
def BoundedAdv (Adv : Type) [HasQueryBound Adv] (b : QueryBudget) : Type :=
  { A : Adv // QueryBounded A b }

end SignalPqxdh
