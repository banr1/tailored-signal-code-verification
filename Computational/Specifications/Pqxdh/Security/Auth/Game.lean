/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Bound
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt

/-!
# The one-key first-message `Auth` game (Lemma 1, second conjunct)

**Trusted: the statement.** Every definition in this file is part of the one-key first-message
authentication and privacy statement `SignalPqxdh.Security.PqxdhAuth1KeySecureδ`
(`Security/Auth/Headline.lean`), the second conjunct of `PqxdhSecureδ` in Lemma 1
(`SignalPqxdh.Security.PqxdhCorrectAndSecureδ`, `Security/HeadlineDelta.lean`). See
`Computational/docs/TRUSTED_BASE.md`.

This file defines the mutual-authentication and first-message payload-privacy game (`Auth`),
modeled after Fiedler–Günther (Eurocrypt 2025, Game 2) and Bhargavan–Jacomme–Kiefer–Schmidt (USENIX
Security 2024), together with its key-schedule PRF and AEAD assumptions and closed-form advantage
bound `pqxdhAuthBound`. In `pqxdhAuthImpl1Key`, `.initPrin u` samples a single Curve25519 identity
scalar for both X25519 key agreement and XEdDSA signing (`ikSignPk = ikAPk = P.x25519Base secIKA0`,
DEV-C5) and delegates all other queries to the shared two-key oracle body `pqxdhAuthImpl true true`
(DEV-PQ13); Lemma 1 reads only the one-key advantage `Auth1KeyAdvantage`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open scoped ENNReal
open OracleComp OracleSpec ENNReal

/-! ## Key-schedule and AEAD assumptions -/

/-! ### First-message AEAD (`AeadIndCpa`) -/

/-- Two-stage adversary against one-time left-or-right IND-CPA of the first-message AEAD:
    `choose` outputs `(ad, m0, m1, st)` and `dist` guesses the challenge bit from `st` and the
    challenge ciphertext. -/
structure AeadIndCpaAdv where
  State  : Type := Bytes
  choose : OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × State)
  dist   : State → Option Bytes → OracleComp PrimBaseSpec Bool
  /-- Primitive-oracle budget per stage. -/
  q_prim : Nat

/-- Query-budget compliance: `choose` and `dist` each make at most `A.q_prim` primitive queries. -/
def AeadIndCpaAdv.Bounded (A : AeadIndCpaAdv) : Prop :=
  OracleComp.IsQueryBoundP A.choose (fun q => isPrimQuery₀ q = true) A.q_prim ∧
  (∀ st c, OracleComp.IsQueryBoundP (A.dist st c) (fun q => isPrimQuery₀ q = true) A.q_prim)

/-- One-time left-or-right IND-CPA experiment under uniform 80-byte `MessageKeys`; returns a
    uniform coin if `m0.length ≠ m1.length`. -/
noncomputable def aeadIndCpaExp (P : Primitives) (A : AeadIndCpaAdv) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let mk ← sampleMessageKeys80
  let (ad, m0, m1, st) ← simulateQ (primBaseImpl P) A.choose
  if m0.length != m1.length then do let coin ← $ᵗ Bool; return coin
  let ct := P.aeadEnc mk ad (if b then m1 else m0)
  let b' ← simulateQ (primBaseImpl P) (A.dist st (some ct))
  return (b' == b)

/-- One-time left-or-right IND-CPA advantage against the first-message AEAD. -/
noncomputable def AeadIndCpa (P : Primitives) (A : AeadIndCpaAdv) : ℝ≥0∞ :=
  𝒟[aeadIndCpaExp P A].boolBias

/-! ### HMAC-SHA256 PRF (`PrfHmac`) -/

/-- Evaluation query for `PrfHmac`. -/
inductive PrfHmacQuery where
  | eval (msg : Bytes)
  deriving DecidableEq, Repr

/-- Oracle interface for `PrfHmac` (32-byte outputs). -/
@[reducible] def prfHmacSpec : OracleSpec PrfHmacQuery := fun _ => Bytes

/-- Distinguisher against the PRF security of `hmacSha256Ref P k ·`. -/
structure PrfHmacAdv where
  run    : OracleComp (PrimBaseSpec + prfHmacSpec) Bool
  q_prf  : Nat
  q_prim : Nat

/-- Query-budget compliance: at most `A.q_prf` PRF queries and `A.q_prim` primitive queries. -/
def PrfHmacAdv.Bounded (A : PrfHmacAdv) : Prop :=
  OracleComp.IsQueryBoundP A.run (fun q => q.isRight = true) A.q_prf ∧
  OracleComp.IsQueryBoundP A.run (fun q => isPrimQuery q = true) A.q_prim

/-- Real-or-random PRF experiment for `hmacSha256Ref P k ·` under a uniform 32-byte key `k` versus
    a lazy random function with 32-byte outputs. -/
noncomputable def prfHmacExp (P : Primitives) (A : PrfHmacAdv) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← sampleBytes32
  let impl : QueryImpl prfHmacSpec (StateT (List (Bytes × Bytes)) ProbComp) :=
    fun (.eval msg) => do
      if b then
        return hmacSha256Ref P k msg
      else
        let cache ← get
        match cache.find? (fun (m, _) => m == msg) with
        | some (_, t) => return t
        | none =>
          let t ← liftM sampleBytes32
          set ((msg, t) :: cache)
          return t
  let fullImpl := (primBaseImpl P).liftTarget (StateT (List (Bytes × Bytes)) ProbComp) + impl
  let (b', _) ← (simulateQ fullImpl A.run).run []
  return (b' == b)

/-- PRF advantage against HMAC-SHA256 under a uniform 32-byte key, used for `MessageKeys.macKey`
    on the length-delimited `aeadMacInput` (DEV-PQ31) in first-message ciphertext integrity. -/
noncomputable def PrfHmac (P : Primitives) (A : PrfHmacAdv) : ℝ≥0∞ :=
  𝒟[prfHmacExp P A].boolBias

/-! ### Chain-key PRF (`PrfChainKey`) -/

/-- Distinguisher for `PrfChainKey` on a real or uniform 32-byte pair `(mkSeed, ckNext)`. -/
structure PrfCkAdv where
  dist   : Bytes → Bytes → OracleComp PrimBaseSpec Bool
  q_prf  : Nat := 1
  q_prim : Nat

/-- Query-budget compliance: `dist` makes at most `A.q_prim` primitive queries. -/
def PrfCkAdv.Bounded (A : PrfCkAdv) : Prop :=
  ∀ a b, OracleComp.IsQueryBoundP (A.dist a b) (fun q => isPrimQuery₀ q = true) A.q_prim

/-- Real-or-random PRF experiment for `ck ↦ (chainKdfSeed ck, chainKdfNext ck)` under a uniform
    32-byte chain key `ck`. -/
noncomputable def prfCkExp (P : Primitives) (A : PrfCkAdv) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let ck ← sampleBytes32
  let (mkSeed, ckNext) ←
    if b then
      pure (P.chainKdfSeed ck, P.chainKdfNext ck)
    else do
      let r1 ← sampleBytes32
      let r2 ← sampleBytes32
      pure (r1, r2)
  let b' ← simulateQ (primBaseImpl P) (A.dist mkSeed ckNext)
  return (b' == b)

/-- PRF advantage against the chain KDF `(chainKdfSeed, chainKdfNext)`. -/
noncomputable def PrfChainKey (P : Primitives) (A : PrfCkAdv) : ℝ≥0∞ :=
  𝒟[prfCkExp P A].boolBias

/-! ### Message-key PRF (`PrfMsgKeys`) -/

/-- Effective 32-byte HKDF salt of an optional SPQR salt (`none ↦ 0^32`, `some s ↦ s` zero-padded
    to 32 bytes; RFC 2104 §2, RFC 5869 §2.2). For `s.length ≤ 32`, `deriveMsgKeysRef` at `s?`
    agrees with `deriveMsgKeysRef` at `some (effectiveHkdfSaltBytes s?).toList`. -/
def effectiveHkdfSaltBytes (salt? : Option Bytes) : List.Vector UInt8 32 := CryptoGames.effectiveHkdfSalt salt?

/-- Evaluation query `deriveMsgKeys(mkSeed, some salt)` at a 32-byte effective salt (DEV-LS25).
    Indexing by `{0,1}^256` avoids collisions between equivalent raw salts (`none`, `some []`,
    `some 0^32`) and matches the dual-PRF assumption on HMAC in its message slot (Bellare,
    Bernstein, Gajland, Saha, BBGS'23, Theorem 11). -/
inductive PrfMsgKeysQuery where
  | derive (salt : List.Vector UInt8 32)
  deriving DecidableEq

@[reducible] def prfMsgKeysSpec : OracleSpec PrfMsgKeysQuery := fun _ => MessageKeys

/-- Distinguisher against `PrfMsgKeys` with access to `derive` and the primitive oracle. -/
structure PrfMsgKeysAdv where
  run    : OracleComp (PrimBaseSpec + prfMsgKeysSpec) Bool
  q_prf  : Nat
  q_prim : Nat

/-- Query-budget compliance: at most `A.q_prf` PRF queries and `A.q_prim` primitive queries. -/
def PrfMsgKeysAdv.Bounded (A : PrfMsgKeysAdv) : Prop :=
  OracleComp.IsQueryBoundP A.run (fun q => q.isRight = true) A.q_prf ∧
  OracleComp.IsQueryBoundP A.run (fun q => isPrimQuery q = true) A.q_prim

/-- Real-or-random PRF experiment for `deriveMsgKeys mkSeed (some ·)` under a uniform 32-byte
    `mkSeed` versus a lazy random function into uniform 80-byte `MessageKeys`. -/
noncomputable def prfMsgKeysExp (P : Primitives) (A : PrfMsgKeysAdv) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let mkSeed ← sampleBytes32
  let impl : QueryImpl prfMsgKeysSpec
      (StateT (List (List.Vector UInt8 32 × MessageKeys)) ProbComp) :=
    fun (.derive salt) => do
      if b then
        return P.deriveMsgKeys mkSeed (some salt.toList)
      else
        let cache ← get
        match cache.find? (fun (s, _) => s == salt) with
        | some (_, out) => return out
        | none =>
          let out ← liftM sampleMessageKeys80
          set ((salt, out) :: cache)
          return out
  let fullImpl := (primBaseImpl P).liftTarget
      (StateT (List (List.Vector UInt8 32 × MessageKeys)) ProbComp) + impl
  let (b', _) ← (simulateQ fullImpl A.run).run []
  return (b' == b)

/-- PRF advantage against `deriveMsgKeys(mkSeed, ·)` over 32-byte effective salts. -/
noncomputable def PrfMsgKeys (P : Primitives) (A : PrfMsgKeysAdv) : ℝ≥0∞ :=
  𝒟[prfMsgKeysExp P A].boolBias

/-! ## First root-KDF oracle -/

/-- Evaluates the first `rootCreateChain(rk, dh)` step of a session either concretely
    (`useRo = false`) or via a lazy caching random oracle (`useRo = true`). -/
def evalRootKdfOrRo (useRo : Bool) (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (rk dh : Bytes) : ProbComp ((Bytes × Bytes) × List ((Bytes × Bytes) × (Bytes × Bytes))) := do
  if !useRo then
    return (P.rootCreateChain rk dh, rootRoCache)
  else
    match rootRoCache.find? (fun (inp, _) => inp == (rk, dh)) with
    | some (_, out) => return (out, rootRoCache)
    | none =>
      let rk1 ← sampleBytes32
      let ck1 ← sampleBytes32
      return ((rk1, ck1), ((rk, dh), (rk1, ck1)) :: rootRoCache)

/-! ## First-message authentication and privacy game -/

/-- Recorded honest with-OPK send event for injective authentication matching. -/
structure SentOPKEvent where
  a0      : Bytes -- Sender identity public key
  b0      : Bytes -- Peer identity public key
  sb      : Bytes -- Peer signed EC pre-key
  ob      : Bytes -- Peer one-time EC pre-key
  a1      : Bytes -- Sender ephemeral public key
  pk1     : Bytes -- Peer Kyber-1024 pre-key
  ct      : Bytes -- Kyber-1024 ciphertext
  m       : Bytes -- Encrypted plaintext
  matched : Bool  -- Consumed by a matching `RecvdOPKEvent`
  deriving DecidableEq, Repr

/-- Recorded honest no-OPK send event for injective authentication matching. -/
structure SentNoOPKEvent where
  a0      : Bytes
  b0      : Bytes
  sb      : Bytes
  a1      : Bytes
  pk1     : Bytes
  ct      : Bytes
  m       : Bytes
  matched : Bool
  deriving DecidableEq, Repr

/-- Recorded honest with-OPK receive event. -/
structure RecvdOPKEvent where
  bCorr : Bool  -- Receiver corrupted at `recvOPK` time (KCI when `true`)
  a0    : Bytes -- Claimed sender identity public key
  b0    : Bytes -- Receiver identity public key
  sb    : Bytes -- Receiver signed EC pre-key
  ob    : Bytes -- Receiver one-time EC pre-key
  a1    : Bytes -- Sender ephemeral public key
  pk1   : Bytes -- Receiver Kyber-1024 pre-key
  ct    : Bytes -- Kyber-1024 ciphertext
  m     : Bytes -- Decrypted plaintext
  deriving DecidableEq, Repr

/-- Recorded honest no-OPK receive event. -/
structure RecvdNoOPKEvent where
  bCorr : Bool
  a0    : Bytes
  b0    : Bytes
  sb    : Bytes
  a1    : Bytes
  pk1   : Bytes
  ct    : Bytes
  m     : Bytes
  deriving DecidableEq, Repr

/-- Correspondence predicate between a `RecvdOPKEvent` and an unconsumed `SentOPKEvent`: compares
    EC keys up to cofactor (`pow8`), requires exact `sb` equality unless the receiver is corrupted
    (`bCorr`), and compares fixed-length `pk1`, `ct`, and `m` by byte equality. -/
def matchSentOPK (P : Primitives) (r : RecvdOPKEvent) (s : SentOPKEvent) : Bool :=
  !s.matched &&
  P.pow8 r.a0 == P.pow8 s.a0 &&
  P.pow8 r.b0 == P.pow8 s.b0 &&
  P.pow8 r.ob == P.pow8 s.ob &&
  P.pow8 r.a1 == P.pow8 s.a1 &&
  P.pow8 r.sb == P.pow8 s.sb &&
  (r.bCorr || r.sb == s.sb) &&
  r.pk1 == s.pk1 &&
  r.ct == s.ct &&
  r.m == s.m

/-- No-OPK counterpart of `matchSentOPK` (injective via `(pqspkId, spkId, ekAPk)` replay
    deduplication on receive). -/
def matchSentNoOPK (P : Primitives) (r : RecvdNoOPKEvent) (s : SentNoOPKEvent) : Bool :=
  !s.matched &&
  P.pow8 r.a0 == P.pow8 s.a0 &&
  P.pow8 r.b0 == P.pow8 s.b0 &&
  P.pow8 r.a1 == P.pow8 s.a1 &&
  P.pow8 r.sb == P.pow8 s.sb &&
  (r.bCorr || r.sb == s.sb) &&
  r.pk1 == s.pk1 &&
  r.ct == s.ct &&
  r.m == s.m

/-- Recorded initiator session metadata in `AuthState`. -/
structure AuthInitiatorEntry (S : Setup) where
  sid         : SessionId S
  peerIkPk    : Bytes
  peerSpkPk   : Bytes
  peerOpkPk?  : Option Bytes
  peerPqspkPk : Bytes
  spkHonest   : Bool
  opkHonest   : Bool
  pqspkHonest : Bool
  ekASk       : Bytes
  ephASk      : Bytes
  fresh       : Bool
  challenged  : Bool
  deriving DecidableEq, Repr

/-- Post-game confidentiality freshness for a challenged initiator session: the peer was an
    uncorrupted honest principal at send time (`s.fresh`), and at game end either `useRo = true`
    and the peer identity key remains uncorrupted or one of `(spk, opk, pqspk)` was honestly
    generated, or `useRo = false` and `pqspk` was honestly generated. -/
def authInitCorruptionClause {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry)) (s : AuthInitiatorEntry S) : Bool :=
  s.fresh &&
  (if useRo then
     (isHonestUncorruptedPeer P principals s.peerIkPk).isSome ||
     s.spkHonest || s.opkHonest || s.pqspkHonest
   else
     s.pqspkHonest)

/-- Adversary oracle queries in the `Auth` game: principal and pre-key management, left-or-right
    sends (`sendOPK`, `sendNoOPK`), responder receives (`recvOPK`, `recvNoOPK`), random-oracle
    queries (`roQuery`, `roRootQuery`), HNDL secret reveal (`revealDhSecrets`), and KOSK key
    registration (`registerKey`, DEV-PQ15). -/
inductive AuthQuery (S : Setup) where
  | initPrin        (u : Fin S.N_id)
  | corruptIK       (u : Fin S.N_id)
  | genSPK          (u : Fin S.N_id) (j : Fin S.N_recv)
  | genOPK          (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
  | sendOPK         (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
  | sendNoOPK       (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
  | recvOPK         (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
  | recvNoOPK       (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
  | roQuery         (secrets : Bytes)
  | roRootQuery     (rk dh : Bytes)
  | revealDhSecrets
  | registerKey     (sk : Bytes) -- KOSK registration (DEV-PQ15)
  deriving DecidableEq, Repr

/-- Oracle responses in the `Auth` game. -/
inductive AuthResponse where
  | noneResp
  | initPrinResp    (ikAPk ikSignPk : Bytes)
  | pkResp          (pk : Bytes)
  | corrResp        (ikSk sigSk : Bytes)
  | bundleResp      (bundle : PreKeyBundleInput)
  | sendFreshResp   (msg : PreKeyMsg)
  | sendUnfreshResp (drKey : DRKey) (rk1 ck1_1 : Bytes) (msg : PreKeyMsg)
  | recvHonestResp
  | recvUnfreshResp (drKey : DRKey) (rk1 ck1_1 pt : Bytes)
  | drKeyResp       (drKey : DRKey)
  | rootKdfResp     (rk1 ck1_0 : Bytes)
  | dhSecretsResp   (ikDhSks spkSks opkSks ekSks : List Bytes)
  deriving DecidableEq, Repr

@[reducible] def authSpec (S : Setup) : OracleSpec (AuthQuery S) :=
  fun _ => AuthResponse

/-- Adversary against the `Auth` game at setup `S`. -/
structure AuthAdversary (S : Setup) where
  run : OracleComp (unifSpec + authSpec S) Bool

/-- Mutable state of the `Auth` game. -/
structure AuthState (S : Setup) where
  secb             : Bool
  hasWonAuth       : Bool
  principals       : List (Nat × PrincipalEntry)
  spkBundles       : List ((Nat × Nat) × SpkBundleEntry)
  opkEntries       : List ((Nat × Nat × Nat) × OpkEntry)
  sessions         : List (AuthInitiatorEntry S)
  usedSendSessions : List (SessionId S)
  usedRecvOPK      : List (Nat × Nat × Nat)
  usedRecvNoOPK    : List (Nat × Nat × Nat)
  seenKyberBaseKeys : List (Nat × KeyId × KeyId × Bytes)
  sentOPKEvents    : List SentOPKEvent
  sentNoOPKEvents  : List SentNoOPKEvent
  recvdOPKEvents   : List RecvdOPKEvent
  recvdNoOPKEvents : List RecvdNoOPKEvent
  roCache          : List (Bytes × DRKey)
  rootRoCache      : List ((Bytes × Bytes) × (Bytes × Bytes))
  advKeys          : List (Bytes × Bytes) := [] -- KOSK-registered `(sk, pk)` pairs

def AuthState.empty (S : Setup) (secb : Bool) : AuthState S :=
  { secb             := secb
    hasWonAuth       := false
    principals       := []
    spkBundles       := []
    opkEntries       := []
    sessions         := []
    usedSendSessions := []
    usedRecvOPK      := []
    usedRecvNoOPK    := []
    seenKyberBaseKeys := []
    sentOPKEvents    := []
    sentNoOPKEvents  := []
    recvdOPKEvents   := []
    recvdNoOPKEvents := []
    roCache          := []
    rootRoCache      := []
    advKeys          := [] }

/-- Executes an honest initiator first-message send (`sendOPK` or `sendNoOPK`). Encrypts `m_secb`
    when the peer is an uncorrupted honest principal (`isFreshPeer`) and `m0` otherwise; leaks
    session keys only when the peer identity key is adversarial. -/
def runAuthSend (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthState S) ProbComp AuthResponse := do
  let st ← get
  if m0.length != m1.length then return .noneResp
  if st.usedSendSessions.contains sid then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then
    return .noneResp
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let ekASk ← liftM sampleScalar32
  let kemCoins ← liftM sampleCoins32
  let ephASk ← liftM sampleScalar32
  let spqrCoins ← liftM sampleCoins32
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
  let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
  -- Five-step first-message key schedule.
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ← liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1 := P.chainKdfNext ck1_0
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return .noneResp
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let wireMsg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := ephAPk
    pqRatchetMsg := pqRatchetMsg
    aeadCt       := aeadCt
  }
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
  let sessEntry : AuthInitiatorEntry S := {
    sid         := sid
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    ephASk      := ephASk
    fresh       := isFreshPeer
    challenged  := isFreshPeer && (m0 != m1)
  }
  -- Record send event whenever the peer is an honest principal (corrupted or uncorrupted).
  let (sentOPK', sentNoOPK') :=
    match peerPrincipal?, bundle.opkB? with
    | some (_, pEntry), some (_, opkPk) =>
      let ev : SentOPKEvent := {
        a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB, ob := opkPk,
        a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain, matched := false
      }
      (ev :: st.sentOPKEvents, st.sentNoOPKEvents)
    | some (_, pEntry), none =>
      let ev : SentNoOPKEvent := {
        a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB,
        a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain, matched := false
      }
      (st.sentOPKEvents, ev :: st.sentNoOPKEvents)
    | none, _ => (st.sentOPKEvents, st.sentNoOPKEvents)
  set { st with
    sessions         := sessEntry :: st.sessions
    usedSendSessions := sid :: st.usedSendSessions
    sentOPKEvents    := sentOPK'
    sentNoOPKEvents  := sentNoOPK'
    roCache          := roCache'
    rootRoCache      := rootRoCache' }
  -- Suppress derived keys whenever the peer is an honest principal (including under KCI).
  if peerPrincipal?.isSome then
    return .sendFreshResp wireMsg
  else
    return .sendUnfreshResp drKey rk1 ck1_1 wireMsg

/-- Marks the first unconsumed `SentOPKEvent` that matches `r` as consumed. -/
def consumeMatchingSentOPK (P : Primitives) (r : RecvdOPKEvent) :
    List SentOPKEvent → Bool × List SentOPKEvent
  | [] => (false, [])
  | s :: rest =>
    if matchSentOPK P r s then
      (true, { s with matched := true } :: rest)
    else
      let (ok, rest') := consumeMatchingSentOPK P r rest
      (ok, s :: rest')

/-- Marks the first unconsumed `SentNoOPKEvent` that matches `r` as consumed. -/
def consumeMatchingSentNoOPK (P : Primitives) (r : RecvdNoOPKEvent) :
    List SentNoOPKEvent → Bool × List SentNoOPKEvent
  | [] => (false, [])
  | s :: rest =>
    if matchSentNoOPK P r s then
      (true, { s with matched := true } :: rest)
    else
      let (ok, rest') := consumeMatchingSentNoOPK P r rest
      (ok, s :: rest')

/-- Two-key `Auth` oracle implementation (DEV-PQ13), parameterized by random-oracle mode `useRo`
    and authentication flag `checkAuth`. -/
def pqxdhAuthImpl (useRo checkAuth : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q => do
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
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return .noneResp
    runAuthSend useRo S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return .noneResp
    runAuthSend useRo S P (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return .noneResp
    if oEntry.consumed then return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    -- Reject non-canonical `ekAPk` and `ephAPk` (DEV-PQ16): the `GapDhWithSign` reduction embeds
    -- its challenge in Bob's SPK and needs curve points to simulate `dhRatchet` via DDH; honest
    -- senders always produce canonical keys (`x25519Base`), whereas the binary omits this check.
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
      return .noneResp
    if msg.hdr.kemCt.length != kyberCtLen then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ← liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some (_, senderEntry) =>
      if !senderEntry.corrupted then
        let recvEv : RecvdOPKEvent := {
          bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
          sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
          pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
        }
        let (matchedOk, sentOPK') := consumeMatchingSentOPK P recvEv st.sentOPKEvents
        let wonAuth' := st.hasWonAuth || (checkAuth && !matchedOk)
        set { st with
          hasWonAuth       := wonAuth'
          opkEntries       := opkEntries'
          usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
          seenKyberBaseKeys := usedTriples'
          sentOPKEvents    := sentOPK'
          recvdOPKEvents   := recvEv :: st.recvdOPKEvents
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
      else
        -- Corrupted honest sender: suppress derived keys and plaintext.
        set { st with
          opkEntries       := opkEntries'
          usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
    | none =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .recvNoOPK k j l msg =>
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    -- Canonical `ekAPk` and `ephAPk` check (see `recvOPK`, DEV-PQ16).
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
      return .noneResp
    if msg.hdr.kemCt.length != kyberCtLen then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ← liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some (_, senderEntry) =>
      if !senderEntry.corrupted then
        let recvEv : RecvdNoOPKEvent := {
          bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
          sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
          pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
        }
        let (matchedOk, sentNoOPK') := consumeMatchingSentNoOPK P recvEv st.sentNoOPKEvents
        let wonAuth' := st.hasWonAuth || (checkAuth && !matchedOk)
        set { st with
          hasWonAuth       := wonAuth'
          usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
          seenKyberBaseKeys := usedTriples'
          sentNoOPKEvents  := sentNoOPK'
          recvdNoOPKEvents := recvEv :: st.recvdNoOPKEvents
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
      else
        set { st with
          usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
    | none =>
      set { st with
        usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
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
  | .roRootQuery rk dh =>
    if !useRo then
      return .noneResp
    let (out, rootRoCache') ← liftM (evalRootKdfOrRo true P st.rootRoCache rk dh)
    set { st with rootRoCache := rootRoCache' }
    return .rootKdfResp out.1 out.2
  | .revealDhSecrets =>
    -- In HNDL mode (`useRo = false`), expose all classical X25519 secret scalars.
    if useRo then
      return .noneResp
    let ikDhSks := st.principals.map (fun (_, e) => e.secIKA0)
    let spkSks  := st.spkBundles.map (fun (_, b) => b.spkSk)
    let opkSks  := st.opkEntries.map (fun (_, o) => o.opkSk)
    let ekSks   := (st.sessions.map (fun s => s.ekASk)) ++ (st.sessions.map (fun s => s.ephASk))
    return .dhSecretsResp ikDhSks spkSks opkSks ekSks

/-- Core two-key `Auth` experiment (DEV-PQ13): wins outright if `checkAuth ∧ finalSt.hasWonAuth`,
    returns a uniform coin if any challenged session fails `authInitCorruptionClause`, and
    otherwise checks `b' == secb`. -/
noncomputable def pqxdhAuthExpCore (useRo checkAuth : Bool) (S : Setup)
    (P : Primitives) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthImpl useRo checkAuth S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P useRo finalSt.principals s)
  if checkAuth && finalSt.hasWonAuth then
    return true
  else if !allChallengedClean then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

/-- Two-key `Auth` experiment (`useRo = true`, `checkAuth = true`). -/
noncomputable def pqxdhAuthExp (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool :=
  pqxdhAuthExpCore true true S P A

/-- Advantage `|2 Pr[win] - 1|` (`boolBias`) of `A` in `pqxdhAuthExp`. -/
noncomputable def AuthAdvantage (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ≥0∞ :=
  𝒟[pqxdhAuthExp S P A].boolBias

/-! ## Query-budget predicates -/

def isAuthRoQuery {S : Setup} : (Nat ⊕ AuthQuery S) → Prop
  | .inr (.roQuery _) => True
  | _                 => False

instance {S : Setup} : DecidablePred (@isAuthRoQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isAuthRoQuery]; infer_instance
  · cases q <;> simp only [isAuthRoQuery] <;> infer_instance

def isAuthRoRootQuery {S : Setup} : (Nat ⊕ AuthQuery S) → Prop
  | .inr (.roRootQuery _ _) => True
  | _                       => False

instance {S : Setup} : DecidablePred (@isAuthRoRootQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isAuthRoRootQuery]; infer_instance
  · cases q <;> simp only [isAuthRoRootQuery] <;> infer_instance

def isAuthSendQuery {S : Setup} : (Nat ⊕ AuthQuery S) → Prop
  | .inr (.sendOPK _ _ _ _ _)   => True
  | .inr (.sendNoOPK _ _ _ _ _) => True
  | _                           => False

instance {S : Setup} : DecidablePred (@isAuthSendQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isAuthSendQuery]; infer_instance
  · cases q <;> simp only [isAuthSendQuery] <;> infer_instance

def isAuthRecvQuery {S : Setup} : (Nat ⊕ AuthQuery S) → Prop
  | .inr (.recvOPK _ _ _ _)   => True
  | .inr (.recvNoOPK _ _ _ _) => True
  | _                         => False

instance {S : Setup} : DecidablePred (@isAuthRecvQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isAuthRecvQuery]; infer_instance
  · cases q <;> simp only [isAuthRecvQuery] <;> infer_instance

/-- Online (non-random-oracle) game queries in `AuthQuery S`: every `.inr q` except the offline
    random-oracle queries `.roQuery` and `.roRootQuery`. -/
def isAuthOnlineQuery {S : Setup} : (Nat ⊕ AuthQuery S) → Prop
  | .inr (.roQuery _)       => False
  | .inr (.roRootQuery _ _) => False
  | .inr _                  => True
  | .inl _                  => False

instance {S : Setup} : DecidablePred (@isAuthOnlineQuery S) := fun q => by
  rcases q with _ | q
  · simp only [isAuthOnlineQuery]; infer_instance
  · cases q <;> simp only [isAuthOnlineQuery] <;> infer_instance

/-- Query-budget compliance for `AuthAdversary S`: bounds `HkdfRO` (`b.q_ro`), `RootKdfRO`
    (`b.q_roRoot`), initiator (`S.N_send_tot`), responder (`S.N_recv_tot`), total game
    (`b.q_total`), and online non-RO (`b.q_on`, `isAuthOnlineQuery`) queries. Every online query is
    a game query, so any adversary bounded at `b.q_total` satisfies `q_on` at
    `{ b with q_on := b.q_total }`, and `pqxdhAuthAdvantageBoundδ` does not depend on `q_on`. -/
instance {S : Setup} : HasQueryBound (AuthAdversary S) where
  QueryBounded A b :=
    OracleComp.IsQueryBoundP A.run isAuthRoQuery b.q_ro ∧
    OracleComp.IsQueryBoundP A.run isAuthSendQuery S.N_send_tot ∧
    OracleComp.IsQueryBoundP A.run isAuthRecvQuery S.N_recv_tot ∧
    OracleComp.IsQueryBoundP A.run isAuthRoRootQuery b.q_roRoot ∧
    OracleComp.IsQueryBoundP A.run (fun q => isGameQuery q = true) b.q_total ∧
    OracleComp.IsQueryBoundP A.run isAuthOnlineQuery b.q_on

/-! ## Closed-form advantage bound -/

/-- Statistical `boolBias` term for the first-step root-KDF random oracle across `S.N_sess_tot`
    sessions and `q_roRoot` adversary `.roRootQuery` calls: bounds root-key guesses and session
    input collisions over 32-byte root keys. -/
noncomputable def rootKdfRoTerm (S : Setup) (q_roRoot : ℕ) : ℝ≥0∞ :=
  2 * (S.N_sess_tot : ℝ≥0∞) * ((q_roRoot : ℝ≥0∞) + (S.N_sess_tot : ℝ≥0∞)) / (2 : ℝ≥0∞) ^ 256

/-- Closed-form `boolBias` advantage bound for `Auth`, which extends `pqxdhKeyIndBound` with:
    - `2 · N_send_tot · N_recv_tot / 2^250` for cofactor-8 X25519 collisions between fresh
      initiator ephemeral keys and prior responder receives;
    - `rootKdfRoTerm S q_roRoot` for the first root-KDF random-oracle step;
    - `2 · N_sess_tot · (epsPrfCk + epsPrfMsgKeys)` for the chain-key and message-key PRF steps;
    - `2 · N_send_tot · epsAeadCpa` for left-or-right payload privacy on fresh sends; and
    - `2 · (2 · N_sess_tot · epsPrfHmac + N_recv_tot / 2^64)` for 8-byte HMAC tag forgery across
      at most `N_recv_tot` receives. -/
noncomputable def pqxdhAuthBound
    (S : Setup) (q_roRoot : ℕ)
    (epsSig epsKemShCr epsGapDh
     epsPrfCk epsPrfMsgKeys epsAeadCpa epsPrfHmac : ℝ≥0∞) : ℝ≥0∞ :=
  pqxdhKeyIndBound S epsSig epsKemShCr epsGapDh +
  2 * (S.N_send_tot : ℝ≥0∞) * (S.N_recv_tot : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 250 +
  rootKdfRoTerm S q_roRoot +
  2 * (S.N_sess_tot : ℝ≥0∞) * epsPrfCk +
  2 * (S.N_sess_tot : ℝ≥0∞) * epsPrfMsgKeys +
  2 * (S.N_send_tot : ℝ≥0∞) * epsAeadCpa +
  2 * (2 * (S.N_sess_tot : ℝ≥0∞) * epsPrfHmac + (S.N_recv_tot : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 64)

/-! ## One-key `Auth` game -/

/-- Runs the `Auth` experiment of `pqxdhAuthExpCore` against an arbitrary `authSpec S`
    implementation `impl`. -/
noncomputable def pqxdhAuthExpCoreWith (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (impl : QueryImpl (authSpec S) (StateT (AuthState S) ProbComp)) (A : AuthAdversary S) :
    ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl' := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    impl
  let (b', finalSt) ← (simulateQ impl' A.run).run initSt
  let allChallengedClean := finalSt.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P useRo finalSt.principals s)
  if checkAuth && finalSt.hasWonAuth then
    return true
  else if !allChallengedClean then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

theorem pqxdhAuthExpCore_eq_with (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    pqxdhAuthExpCore useRo checkAuth S P A =
      pqxdhAuthExpCoreWith useRo checkAuth S P (pqxdhAuthImpl useRo checkAuth S P) A :=
  rfl

/-- One-key `Auth` oracle (DEV-C5): `.initPrin u` samples a single Curve25519 scalar `secIKA0`
    for both X25519 and XEdDSA (`secIKAsign := secIKA0`, `ikSignPk := ikAPk = P.x25519Base secIKA0`),
    and delegates all other queries to `pqxdhAuthImpl true true S P`. -/
def pqxdhAuthImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q =>
  match q with
  | .initPrin u => do
    let st ← get
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM sampleScalar32
    let ikAPk := P.x25519Base secIKA0
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := secIKA0
      ikSignPk   := ikAPk
      corrupted  := false
    }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikAPk
  | q => pqxdhAuthImpl true true S P q

/-- One-key `Auth` experiment (`pqxdhAuthExpCoreWith true true` on `pqxdhAuthImpl1Key`). -/
noncomputable def pqxdhAuth1KeyExp (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool :=
  pqxdhAuthExpCoreWith true true S P (pqxdhAuthImpl1Key S P) A

/-- Advantage `|2 Pr[win] - 1|` (`boolBias`) of `A` in `pqxdhAuth1KeyExp`. -/
noncomputable def Auth1KeyAdvantage (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ≥0∞ :=
  𝒟[pqxdhAuth1KeyExp S P A].boolBias

end SignalPqxdh
