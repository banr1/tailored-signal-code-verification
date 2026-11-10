/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.CliSetup
public import Symbolic.Specifications.Concrete.SessionRecord
public import Symbolic.Specifications.Refinement.Concretization

/-!
# Trace Explanation and Collision Excuses

**Trusted: definitions used by the statement.**

Defines when a composed symbolic run `ss` explains a `signal-session` CLI event trace `evs`
(`Explains`), together with receiver decryption trials (`TrialCtx`, `whisperTrials`, `bobTrials`)
and cryptographic collision excuses (`MemoCollisionOn`, `RecvCollisionOn`, `ReselectCollisionOn`,
`BobSessionStartCollidesOrImplicitRejectsOn`).
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Rust
export DY.Libsignal.Rust (bytesField u32Field msgField chainBytes recordBytes KeyInRecord
  EligibleForSessionPromotion)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY.Libsignal.Refinement (le32 slice x25519PublicKeySymbol ExternCryptoLawsHold encodeField)
export DY.Libsignal.Refinement (le32 slice)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm agree errToOption serializedIk)
open DY.Libsignal.PQXDH.Refinement
export DY.Libsignal.PQXDH.Refinement (emptyPreKeyMsg mergePreKeyField decodePreKeyLoop decodePreKey
  ecKeyParses PreKeyFields parsePreKey parsePreKeyWire preKeyWire preKeySpqrIndex decodeLe32)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open TripleRatchet (messageVersion findRecvChain recvHalfStep consumeMessageKey skippedSeeds
  computeMac RecvChain createChain TRState TRSignalMsg parseTrSignalMsg trMsgKeys)

/-- Kyber-1024 decapsulation of `ct` under Bob's setup secret key `r.kyberSecB`. -/
def kyberDecapsBytes (interpretation : ExternInterpretation) (r : ProtocolSetup) (ct : HwBytes) :
    Option HwBytes :=
  interpretation kyberDecapsSymbol [r.kyberSecB.drop 1, ct]

/-- Agreement between `(S, g)` and `ProtocolSetup` `r` on setup random draws, opaque public terms,
and decapsulation under Bob's Kyber prekey. -/
def GhostAndSemMatchSetup (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) : Prop :=
  (∀ p ∈ setupRandomsAt r, g.σ p.1 p.2 = r.fresh p.1 p.2) ∧
    (∀ t ∈ [r.spkSigTerm, r.pqpkPubTerm, r.pqpkSigTerm],
      gamma interpretation S g t = r.opaqueBytes t) ∧
    ∀ ct, S.kemDecap (r.opaqueBytes r.pqpkPubTerm) ct = (kyberDecapsBytes interpretation r ct).getD []

/-- Well-formedness of `ProtocolSetup` `r`: distinct parties, pairwise distinct setup draws of
matching lengths, valid opaque key/signature lengths, and embedded Kyber public key consistency. -/
def ProtocolSetupWF (r : ProtocolSetup) : Prop :=
  r.alice ≠ r.bob ∧
    (∀ p ∈ setupRandomsAt r, (r.fresh p.1 p.2).length = p.2) ∧
    ((setupRandomsAt r).map fun p => r.fresh p.1 p.2).Nodup ∧
    (r.opaqueBytes r.spkSigTerm).length = 64 ∧
    (r.opaqueBytes r.pqpkPubTerm).length = 1568 ∧
    (r.opaqueBytes r.pqpkSigTerm).length = 64 ∧
    r.kyberSecB.length = 3169 ∧
    slice r.kyberSecB 1537 1568 = r.opaqueBytes r.pqpkPubTerm

/-- Any 1813-byte bundle blob `b` carries Bob's setup signed prekey, Kyber prekey, signatures, and
identity key. -/
def HonestBundle (interpretation : ExternInterpretation) (r : ProtocolSetup) (b : HwBytes) : Prop :=
  b.length = preKeyBundleByteLength →
    BundleBlob.spkPub b = ecKey (pubBytes interpretation r.spkSecBytes) ∧
    BundleBlob.spkSig b = r.opaqueBytes r.spkSigTerm ∧
    BundleBlob.kpkPub b = kyberKey (r.opaqueBytes r.pqpkPubTerm) ∧
    BundleBlob.kpkSig b = r.opaqueBytes r.pqpkSigTerm ∧
    BundleBlob.ikPub b = ecKey (pubBytes interpretation r.ikBSecBytes)

/-- Inner `SignalMessage` body of a sent whisper or `PreKeySignalMessage` wire frame. -/
def sentBody (msg : HwBytes) : Option HwBytes :=
  match msg with
  | t :: body => if t = wireWhisperTag then some body else (parsePreKeyWire msg).map (·.message)
  | [] => none

/-- If `body` decodes as a `SignalMessage`, its `pq_ratchet` field matches that of some earlier
sent message body in `sent`. -/
def PqFromHonest (sent : List HwBytes) (body : HwBytes) : Prop :=
  ∀ m : CryptoGames.LibsignalSession.SignalMessage,
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body = .ok m →
    ∃ b ∈ sent, ∃ m' : CryptoGames.LibsignalSession.SignalMessage,
      CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec b = .ok m' ∧
      m'.pqRatchet = m.pqRatchet

abbrev BundlePreKeyIds := Option (BitVec 32) × BitVec 32 × BitVec 32

def bundlePreKeyIds (b : HwBytes) : BundlePreKeyIds :=
  (BundleBlob.opkId b, BundleBlob.spkId b, BundleBlob.kpkId b)

def BundleSignedKeysMatch (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes)
    (spk spkSig pqpk pqpkSig : DY.Bytes) : Prop :=
  let γ := gamma interpretation S g
  b.length = preKeyBundleByteLength ∧ BundleBlob.spkPub b = ecKey (γ spk) ∧
    BundleBlob.spkSig b = γ spkSig ∧ BundleBlob.kpkPub b = kyberKey (γ pqpk) ∧
    BundleBlob.kpkSig b = γ pqpkSig

def PreKeyBundleLayoutMatches (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes) :
    List DY.Bytes → Prop
  | [spk, spkSig, pqpk, pqpkSig] =>
    BundleSignedKeysMatch interpretation S g b spk spkSig pqpk pqpkSig ∧
      BundleBlob.hasOpkByte b = some 0#8
  | [spk, spkSig, pqpk, pqpkSig, opk] =>
    BundleSignedKeysMatch interpretation S g b spk spkSig pqpk pqpkSig ∧
      BundleBlob.hasOpkByte b = some 1#8 ∧
      BundleBlob.opkPub b = ecKey (gamma interpretation S g opk)
  | _ => False

/-- Alice's sent `PreKeySignalMessage` `b` matches `[ek, ct, msg]` under her active `initIds`. -/
def SendMatches (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (initIds : Option BundlePreKeyIds) (b : HwBytes) : List DY.Bytes → Prop
  | [ek, ct, msg] =>
    let γ := gamma interpretation S g
    ∃ preKeyId spkId kpkId,
      initIds = some (preKeyId, spkId, kpkId) ∧
      b = preKeyWire preKeyId spkId kpkId r.regIdA (ecKey (pubBytes interpretation r.ikASecBytes))
        (γ ek) (γ ct) (γ msg)
  | _ => False

/-- One-time prekey header check on `b`: requires `preKeyId = some r.opkId` and `r.withOpk = true`
when `used = true`, and `preKeyId = none` when `used = false`. -/
def OpkNamed (r : ProtocolSetup) (b : HwBytes) (used : Bool) : Prop :=
  ∃ p, parsePreKeyWire b = some p ∧
    if used then p.preKeyId = some r.opkId ∧ r.withOpk = true
    else p.preKeyId = none

/-- Bob's received `PreKeySignalMessage` `b` matches `[ek, ct, msg]` and Bob's setup key IDs. -/
def PreKeyRecvMatches (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : HwBytes) : List DY.Bytes → Prop
  | [ek, ct, msg] =>
    let γ := gamma interpretation S g
    ∃ p, parsePreKeyWire b = some p ∧
      p.baseKey.take 33 = ecKey (γ ek) ∧
      p.kyberCiphertext = some (kyberKey (γ ct)) ∧
      p.message = γ msg ∧
      p.version = 4 ∧
      p.signedPreKeyId = r.spkId ∧
      p.kyberPreKeyId = some r.kpkId ∧
      p.identityKey.take 33 = ecKey (pubBytes interpretation r.ikASecBytes) ∧
      (∃ used, OpkNamed r b used)
  | _ => False

def PreKeyRecvOpkMatches (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (b : HwBytes) : List DY.Bytes → Prop
  | [ek, ct, msg] => PreKeyRecvMatches interpretation r S g b [ek, ct, msg] ∧ OpkNamed r b false
  | [ek, ct, msg, _opk] => PreKeyRecvMatches interpretation r S g b [ek, ct, msg] ∧ OpkNamed r b true
  | _ => False

/-- Concrete bytes `b` of kind `k` match observable model entry `v` according to `v.layout`. -/
def BytesMatchEntry (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k : VisEventKind) (b : HwBytes) (v : VisEntry) (initIds : Option BundlePreKeyIds := none) : Prop :=
  k = v.kind ∧
    let γ := gamma interpretation S g
    match v.layout with
    | .single => v.terms.map γ = [b]
    | .whisper => ∃ t, v.terms = [t] ∧ b = wireWhisperTag :: γ t
    | .bundle => PreKeyBundleLayoutMatches interpretation S g b v.terms
    | .preKeySend => SendMatches interpretation r S g initIds b v.terms
    | .preKeyRecv => PreKeyRecvOpkMatches interpretation r S g b v.terms
    | .preKeyInner eks =>
      ∃ t p, v.terms = [t] ∧ parsePreKeyWire b = some p ∧ p.version = 4 ∧
        p.identityKey.take 33 = ecKey (pubBytes interpretation (secretBytes r 0)) ∧
        (∃ ek ∈ eks, p.baseKey.take 33 = ecKey (γ ek)) ∧ p.message = γ t
    | .fresh n => b.length = n
    | .kyberCoin j =>
      b.length = 4 ∧ ∃ t, v.terms = [t] ∧ (γ t).length = 32 ∧ b.head? = (γ t)[j]?
    | .unconstrained => True
    | .leakPq pq => if pq then b = r.kyberSecB else v.terms.map γ = [b]
    | .leakRecord =>
      ∃ t, v.terms = [t] ∧ (b = γ t ∨ b = clamp (γ t))

/-- Ghost well-formedness on `vis`: nonzero `rng` draws match their requested byte lengths, and
`g.addr` carries serialized `(alice, bob)` protocol addresses on `preKeySend` and `[]` on
`whisper`. -/
def GhostWF (g : Ghost) (vis : List VisEntry) : Prop :=
  (∀ v ∈ vis, v.kind = .rng → ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms → (g.σ ts n).length = n) ∧
  (∀ t, g.addr t = [] ∨ g.addr t = Cli.serializeAddresses ⟨Cli.aliceUuid, 1⟩ ⟨Cli.bobUuid, 1⟩) ∧
  (∀ v ∈ vis, v.kind = .send →
    (v.layout = .preKeySend →
      ∀ ek ct msg pm, v.terms = [ek, ct, msg] → parseTrSignalMsg msg = some pm →
        g.addr pm.wire = Cli.serializeAddresses ⟨Cli.aliceUuid, 1⟩ ⟨Cli.bobUuid, 1⟩) ∧
    (v.layout = .whisper →
      ∀ msg pm, v.terms = [msg] → parseTrSignalMsg msg = some pm →
        g.addr pm.wire = []))

/-- Whether `t`'s outermost symbol belongs to `DY.Spqr`. -/
def spqrHeaded (t : DY.Bytes) : Bool :=
  (t.view? DY.Spqr.InitState.SubF).isSome || (t.view? DY.Spqr.SendState.SubF).isSome ||
    (t.view? DY.Spqr.SendKey.SubF).isSome || (t.view? DY.Spqr.SendMsg.SubF).isSome ||
    (t.view? DY.Spqr.RecvState.SubF).isSome || (t.view? DY.Spqr.RecvKey.SubF).isSome ||
    (t.view? DY.Spqr.ChainKey.SubF).isSome

abbrev FaithfulWireMacAnd (γ : DY.Bytes → HwBytes) (msg : TRSignalMsg) (raw : HwBytes)
    (P : Prop) : Prop :=
  γ msg.wire = raw.take (raw.length - 8) ∧
  γ msg.mac = raw.drop (raw.length - 8) ∧
  spqrHeaded msg.mac = false ∧
  P

abbrev FaithfulDecodedSignalMsg (γ : DY.Bytes → HwBytes) (msg : TRSignalMsg)
    (m : CryptoGames.LibsignalSession.SignalMessage) : Prop :=
  γ msg.ciphertext = m.ciphertext ∧
  γ msg.ratchetKey = m.senderRatchetKey.bytes.toList ∧
  γ msg.pqRatchet = m.pqRatchet ∧
  msg.counter.toNat = m.counter.toNat ∧ msg.version.toNat = m.messageVersion.toNat

abbrev FaithfulSignalMsgFields (γ : DY.Bytes → HwBytes) (msg : TRSignalMsg)
    (raw : HwBytes) (m : CryptoGames.LibsignalSession.SignalMessage) : Prop :=
  FaithfulWireMacAnd γ msg raw (FaithfulDecodedSignalMsg γ msg m)

/-- Attacker-known symbolic terms on `tr` concretizing to `SignalMessage` body `b` with matching
decoded fields and a non-SPQR-headed MAC. -/
def recvRepresentationsOn (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (b : HwBytes) : Set DY.Bytes :=
  let γ := gamma interpretation S g
  {t | t.AttackerKnows tr ∧ γ t = b ∧
    (parseTrSignalMsg t).isSome = true ∧
    ∀ msg, parseTrSignalMsg t = some msg →
      FaithfulWireMacAnd γ msg b
        (∀ m : CryptoGames.LibsignalSession.SignalMessage,
          CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec b = .ok m →
          FaithfulDecodedSignalMsg γ msg m)}

/-- Symbolic `(ek, ct, msg)` representation of a received `PreKeySignalMessage`. -/
structure PreKeyRep where
  ek : DY.Bytes
  ct : DY.Bytes
  msg : DY.Bytes

def FaithfulInner (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (t : DY.Bytes)
    (p : PreKeyFields) : Prop :=
  ∃ msg, parseTrSignalMsg t = some msg ∧
    FaithfulSignalMsgFields (gamma interpretation S g) msg p.message p.inner

/-- Attacker-known `PreKeyRep` triples on `tr` matching received `PreKeySignalMessage` bytes `b`. -/
def preKeyRepresentationsOn (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (b : HwBytes) : Set PreKeyRep :=
  {x | x.ek.AttackerKnows tr ∧ x.ct.AttackerKnows tr ∧ x.msg.AttackerKnows tr ∧
    PreKeyRecvMatches interpretation r S g b [x.ek, x.ct, x.msg] ∧
    ∃ p, parsePreKeyWire b = some p ∧ FaithfulInner interpretation S g x.msg p}

def bobDoneBaseKeys (tr : ExecTrace) : List DY.Bytes :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt PQXDHEvent i with
    | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
    | _ => none

/-- Non-opaque term heads treated as collision-resistant in `MemoCollisionOn`: nonzero-size
`Random`, `dhPk`, `dh`, `kdfExtract`, `symEnc`, `trunc8`, and 32-byte-entropy `Encap` /
`SharedSecret`. -/
def assumedInjective (t : DY.Bytes) : Bool :=
  ((t.view? DY.Random.Random).map (·.size != 0)).getD false ||
    (t.view? DY.DiffieHellman.DhPk.SubF).isSome || (t.view? DY.DiffieHellman.Dh.SubF).isSome ||
    (t.view? DY.KdfExtract.KdfExtract.SubF).isSome || (t.view? DY.SymEnc.Enc.SubF).isSome ||
    (t.view? DY.Trunc.Trunc8.SubF).isSome ||
    (t.view? DY.PQKem.Encap.SubF).isSome || (t.view? DY.PQKem.SharedSecret.SubF).isSome

def honestKeysOf : ExecTrace → List Step → List DY.Bytes
  | _, [] => []
  | tr, s :: ss => (s.publishedSpqrKey? tr).toList ++ honestKeysOf (s.next tr) ss

/-- Candidate SPQR salts (`zeroKey` plus all SPQR keys published by honest encrypts in `ss`). -/
def honestSaltsOf (r : ProtocolSetup) (ss : List Step) : List DY.Bytes :=
  DY.Spqr.zeroKey :: honestKeysOf (setupTrace r) ss

def availableStates (r : ProtocolSetup) (tr : ExecTrace) : List TRState :=
  (storedStates r tr).map (·.state)

/-- Receiver's own `RecvKey` terms for `msg.pqRatchet` across stored states of matching role. -/
def ownKeys (r : ProtocolSetup) (tr : ExecTrace) (st : TRState) (msg : TRSignalMsg) : List DY.Bytes :=
  ((availableStates r tr).filter (·.initiator == st.initiator)).map fun st' =>
    ({st := st'.spqr, msg := msg.pqRatchet} : DY.Spqr.RecvKey.SubF DY.Bytes).pack

def storedSecrets (tr : ExecTrace) : List DY.Bytes :=
  (List.range tr.length).filterMap fun i =>
    (tr.getLocalStateAt PQXDH.PQXDHState i).map serialize

def principalTerms (r : ProtocolSetup) (tr : ExecTrace) (vis : List VisEntry) : List DY.Bytes :=
  (vis.filter (·.kind == .send)).flatMap (·.terms) ++
    (storedStates r tr).map (fun ls => serialize ls) ++ storedSecrets tr

def plaintextTerms (vis : List VisEntry) : List DY.Bytes :=
  (vis.filter (·.kind == .pt)).flatMap (·.terms)

def prefixTerms (r : ProtocolSetup) (tr : ExecTrace) (vis : List VisEntry) : List DY.Bytes :=
  principalTerms r tr vis ++ plaintextTerms vis

/-- Non-opaque subterm collision between `newTerms` and `prefixTerms r tr vis ++ newTerms`: two
memoized subterms with distinct shapes (at least one headed by `assumedInjective`) map to identical
bytes, with plaintext atoms colliding only against attacker-unknown injective terms. -/
def MemoCollisionOn (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (known : DY.Bytes → Prop) (tr : ExecTrace) (vis : List VisEntry) (newTerms : List DY.Bytes)
    (newPts : List DY.Bytes) : Prop :=
  let memo := fun t => (gamma' interpretation S g t).memo
  let new := newTerms.flatMap memo
  let terms := ((prefixTerms r tr vis).flatMap memo) ++ new
  let pts := plaintextTerms vis ++ newPts
  ∃ x₁ ∈ new, ∃ x₂ ∈ terms,
    x₁.2.1 ≠ x₂.2.1 ∧
    (assumedInjective x₁.1 ∨ assumedInjective x₂.1) ∧
    (x₁.1 ∈ pts → x₂.1 ∉ pts ∧ assumedInjective x₂.1 ∧ ¬ known x₂.1) ∧
    (x₂.1 ∈ pts → x₁.1 ∉ pts ∧ assumedInjective x₁.1 ∧ ¬ known x₁.1) ∧
    x₁.2.2 = x₂.2.2

/-- Context of a single receiver decryption trial. -/
structure TrialCtx where
  peerIk : DY.Bytes
  myIk : DY.Bytes
  extra : List DY.Bytes
  ownSalts : List DY.Bytes
  seed? : Option DY.Bytes

/-- Receiver decryption trials across all stored `TRState` snapshots and cached skipped seeds on
`tr` for `msg`. -/
def whisperTrials (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (msg : TRSignalMsg) : List TrialCtx :=
  if msg.version = messageVersion then
    let γ := gamma interpretation S g
    (availableStates r tr).flatMap fun st =>
      let own := ownKeys r tr st msg
      let chains :=
        (st.toDRState.recv.filter fun c => decide (γ c.ratchetKey = γ msg.ratchetKey)) ++
        match findRecvChain st.recv msg.ratchetKey, recvHalfStep st.toDRState msg.ratchetKey with
        | none, some (_, c) => [c]
        | _, _ => []
      (chains.map fun c =>
        match consumeMessageKey c msg.counter with
        | none =>
          { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
            ownSalts := [], seed? := none }
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := own, seed? := some seed }) ++
      (List.range tr.length).filterMap fun i =>
        match tr.getEventAt TripleRatchet.TREvent i with
        | some (.SkippedKeyStored s pk n seed _ _) =>
          if (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome ∧
              γ pk = γ msg.ratchetKey ∧ n = msg.counter then
            some { peerIk := st.peerIk, myIk := st.myIk, extra := [],
                   ownSalts := if st.sessionInfo s.me = s then own else [],
                   seed? := some seed }
          else none
        | _ => none
  else []

/-- Bob's initial decryption trial when starting a session from pre-key message `p` (representation
`x`, inner message `msg`) on `tr`. -/
def bobTrials (r : ProtocolSetup) (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep)
    (msg : TRSignalMsg) : List TrialCtx :=
  match (match p.preKeyId with
    | none => some none
    | some id => if r.withOpk && id == r.opkId then some (some r.opkSecTerm) else none) with
  | none => []
  | some opk =>
    let ekBytes := ((p.baseKey.take 33).drop 1).map BitVec.toNat
    let rkBytes := p.inner.senderRatchetKey.bytes.toList.map BitVec.toNat
    if !(decide (DY.X25519.leValue ekBytes < DY.X25519.p25519) &&
          !DY.X25519.isLowOrderKey ekBytes &&
          !PQXDH.x25519LowOrder x.ek &&
          decide (msg.version = messageVersion) &&
          !DY.X25519.isLowOrderKey rkBytes &&
          !TripleRatchet.x25519LowOrder msg.ratchetKey &&
          opk.all fun s => !PQXDH.opkUsedB tr r.bob (DY.DiffieHellman.dhPk s)) then
      []
    else
      let ikA := r.ikAPubTerm
      let spk := r.spkSecTerm
      let pqsk := r.pqskSecTerm
      let ss := (errToOption (PQKem.kemDecap pqsk x.ct)).getD
        (PQKem.kemRejKey pqsk x.ct)
      let keys := pqxdhKdf (pqxdhIkm (agree ikA spk) (agree x.ek r.ikBSecTerm)
        (agree x.ek spk) (opk.map (agree x.ek ·)) ss)
      let c : RecvChain :=
        { ratchetKey := msg.ratchetKey,
          chainKey := (createChain keys.rk msg.ratchetKey spk).2,
          index := 0, rIdx := 2 }
      let peerIk := serializedIk ikA
      let myIk := serializedIk r.ikBPubTerm
      match consumeMessageKey c msg.counter with
      | none =>
        [{ peerIk, myIk, extra := [keys.rk, keys.ck, keys.pqr, c.chainKey],
           ownSalts := [], seed? := none }]
      | some (seed, c') =>
        let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
          msg.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList
        [{ peerIk, myIk,
           extra := [keys.rk, keys.ck, keys.pqr, c.chainKey, c'.chainKey] ++
             skippedSeeds c msg.counter,
           ownSalts := own, seed? := some seed }]

def trialTerms (salts : List DY.Bytes) (msg : TRSignalMsg) (ctx : TrialCtx) : List DY.Bytes :=
  ctx.extra ++
    match ctx.seed? with
    | none => []
    | some seed =>
      salts.flatMap fun salt =>
        let mk := trMsgKeys salt seed
        [mk.cipherKey, mk.macKey, mk.iv,
          computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire] ++
        (DY.SymEnc.symDec mk.cipherKey mk.iv msg.ciphertext).toList

/-- A receiver trial matches `msg.mac` using an own SPQR salt `k` and an attacker-unknown ratchet
`seed` whose derived message keys differ from every honest salt in `honest`. -/
def UnknownSeedMacGuess (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (known : DY.Bytes → Prop) (honest : List DY.Bytes) (msg : TRSignalMsg)
    (ctxs : List TrialCtx) : Prop :=
  let γ := gamma interpretation S g
  ∃ ctx ∈ ctxs, ∃ seed, ctx.seed? = some seed ∧ ∃ k ∈ ctx.ownSalts,
    let mk := trMsgKeys k seed
    γ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) = γ msg.mac ∧
    ¬ known seed ∧
    ∀ salt ∈ honest,
      let hmk := trMsgKeys salt seed
      (γ hmk.cipherKey, γ hmk.macKey, γ hmk.iv) ≠
        (γ mk.cipherKey, γ mk.macKey, γ mk.iv)

/-- Two receiver trials on concretely distinct ratchet seeds `seed` and `seed₀` produce identical
8-byte truncated HMAC tags for `msg`. -/
def TruncatedMacSeedCollision (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (honest : List DY.Bytes) (msg : TRSignalMsg)
    (ctxs : List TrialCtx) : Prop :=
  let γ := gamma interpretation S g
  ∃ ctx ∈ ctxs, ∃ seed, ctx.seed? = some seed ∧ ∃ k ∈ ctx.ownSalts,
    let mk := trMsgKeys k seed
    γ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) = γ msg.mac ∧
    ∃ ctx₀ ∈ ctxs, ∃ seed₀, ctx₀.seed? = some seed₀ ∧ γ seed ≠ γ seed₀ ∧
      ((∃ salt₀ ∈ ctx₀.ownSalts ++ honest,
          γ (computeMac (trMsgKeys salt₀ seed₀).macKey ctx₀.peerIk ctx₀.myIk msg.wire) =
            γ msg.mac) ∨
        ∃ peerIk₀ myIk₀ salt₀ w,
          msg.mac = computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ w ∧
          γ w = γ msg.wire)

def MacTagForgeryOrCollision (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (known : DY.Bytes → Prop) (honest : List DY.Bytes) (msg : TRSignalMsg)
    (ctxs : List TrialCtx) : Prop :=
  UnknownSeedMacGuess interpretation S g known honest msg ctxs ∨
    TruncatedMacSeedCollision interpretation S g honest msg ctxs

/-- Receive-path collision on symbolic `SignalMessage` term `t` across `whisperTrials`. -/
def RecvCollisionOn (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List DY.Bytes) (t : DY.Bytes) : Prop :=
  let known := fun u : DY.Bytes => u.AttackerKnows tr
  match parseTrSignalMsg t with
  | none => MemoCollisionOn interpretation r S g known tr vis [t] []
  | some msg =>
    let ctxs := whisperTrials interpretation r S g tr msg
    MemoCollisionOn interpretation r S g known tr vis
        (t :: ctxs.flatMap (trialTerms salts msg)) [] ∨
      MacTagForgeryOrCollision interpretation S g known salts msg ctxs

def storedRatchetKeys (r : ProtocolSetup) (tr : ExecTrace) (msg : TRSignalMsg) : List DY.Bytes :=
  ((availableStates r tr).flatMap fun st => st.toDRState.recv.map (·.ratchetKey)) ++
    (List.range tr.length).filterMap fun i =>
      match tr.getEventAt TripleRatchet.TREvent i with
      | some (.SkippedKeyStored _ pk n _ _ _) =>
        if ((availableStates r tr).any fun st =>
            (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome) ∧
            n = msg.counter then some pk
        else none
      | _ => none

def ReselectsTo (msg msg' : TRSignalMsg) (rk : DY.Bytes) : Prop :=
  msg'.ratchetKey = rk ∧ msg'.version = msg.version ∧ msg'.counter = msg.counter ∧
    msg'.ciphertext = msg.ciphertext ∧ msg'.pqRatchet = msg.pqRatchet

/-- Ratchet-key reselection collision: `t`'s ratchet key has the same bytes as a distinct stored
ratchet key `rk`, and every representation of `γ t` reselecting to `rk` hits `RecvCollisionOn`. -/
def ReselectCollisionOn (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List DY.Bytes) (t : DY.Bytes) : Prop :=
  let γ := gamma interpretation S g
  ∃ msg, parseTrSignalMsg t = some msg ∧
    ∃ rk ∈ storedRatchetKeys r tr msg, γ rk = γ msg.ratchetKey ∧ rk ≠ msg.ratchetKey ∧
      (∃ t' ∈ recvRepresentationsOn interpretation S g tr (γ t),
        ∃ msg', parseTrSignalMsg t' = some msg' ∧ ReselectsTo msg msg' rk) ∧
      ∀ t' ∈ recvRepresentationsOn interpretation S g tr (γ t),
        ∀ msg', parseTrSignalMsg t' = some msg' → ReselectsTo msg msg' rk →
          RecvCollisionOn interpretation r S g tr vis salts t'

/-- Session-start collision excuse on `PreKeyRep` `x` across `bobTrials`. -/
def BobSessionStartCollidesOrImplicitRejectsOn (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List DY.Bytes) (p : PreKeyFields)
    (x : PreKeyRep) : Prop :=
  let known := fun u : DY.Bytes => u.AttackerKnows tr
  match parseTrSignalMsg x.msg with
  | none => MemoCollisionOn interpretation r S g known tr vis [x.ek, x.ct, x.msg] []
  | some msg =>
    let ctxs := bobTrials r tr p x msg
    MemoCollisionOn interpretation r S g known tr vis
        ([x.ek, x.ct, x.msg] ++ ctxs.flatMap (trialTerms salts msg)) [] ∨
      MacTagForgeryOrCollision interpretation S g known salts msg ctxs

def kyberEncapsBytes (interpretation : ExternInterpretation) (r : ProtocolSetup) (e : HwBytes) :
    Option (HwBytes × HwBytes) :=
  (interpretation kyberEncapsSymbol [r.opaqueBytes r.pqpkPubTerm, e]).map
    fun out => (out.take 1568, out.drop 1568)

/-- Kyber-1024 correctness failure on `p.kyberCiphertext`: some 32-byte entropy `e` encapsulates to
`(ct, ss)` under Bob's public key while decapsulation under `r.kyberSecB` does not return `ss`. -/
def KyberMismatch (interpretation : ExternInterpretation) (r : ProtocolSetup) (p : PreKeyFields) : Prop :=
  ∃ e ct ss, e.length = 32 ∧ p.kyberCiphertext = some (kyberKey ct) ∧
    kyberEncapsBytes interpretation r e = some (ct, ss) ∧
    kyberDecapsBytes interpretation r ct ≠ some ss

/-- Whether `p.baseKey` matches the base key of some earlier `BobDone` event on `tr`
(`promote_matching_session`). -/
def KnownBaseKeyOn (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace)
    (p : PreKeyFields) : Prop :=
  ∃ ek ∈ bobDoneBaseKeys tr, p.baseKey.take 33 = ecKey (gamma interpretation S g ek)

def ptEntryAt (tr : ExecTrace) : VisEntry := ⟨.pt, [randTerm tr.length 32], .single, none⟩

def Step.FitsCmd : Step → CryptoVerification.SignalSession.Cmd → Prop
  | .aliceStart .., .init _ _ => True
  | .messageEncrypt .., .send _ => True
  | .messageEncryptAbort .., .send _ => True
  | .bobStart .., .recv _ => True
  | .messageDecrypt .., .recv _ => True
  | .messageDecryptSkipped .., .recv _ => True
  | _, _ => False

def Step.MatchesSetupPeer (r : ProtocolSetup) : Step → Prop
  | .aliceStart _ b .. => b = r.bob
  | .bobStart _ a .. => a = r.alice
  | _ => True

def runWrapped (ev : RunEvent) : Bool :=
  match ev.cmd, ev.exit with
  | .send _, some (_, out) => out.head? == some wirePrekeyTag
  | .send _, none => false
  | _, _ => ev.input.head? != some wireWhisperTag

def inputKind (ev : RunEvent) : VisEventKind :=
  match ev.cmd with
  | .send _ => .pt
  | _ => .recv

/-- Input term(s) of `v` belong to `recvRepresentationsOn` or `preKeyRepresentationsOn` of `b` on
`tr`. -/
def ReadsFaithfully (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (v : VisEntry) (b : HwBytes) : Prop :=
  match v.layout, v.terms, b with
  | .whisper, [t], _ :: body => t ∈ recvRepresentationsOn interpretation S g tr body
  | .preKeyInner _, [t], b =>
    ∀ p, parsePreKeyWire b = some p → t ∈ recvRepresentationsOn interpretation S g tr p.message
  | .preKeyRecv, ek :: ct :: msg :: _, b =>
    ⟨ek, ct, msg⟩ ∈ preKeyRepresentationsOn interpretation r S g tr b
  | _, _, _ => True

/-- On a received `PreKeySignalMessage`, `messageDecrypt` / `messageDecryptSkipped` is taken iff its
base key matches an earlier `BobDone` (`promote_matching_session`), and `bobStart` iff it does not. -/
def PathFaithfulAt (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace)
    (s : Step) (b : HwBytes) : Prop :=
  ∀ p, parsePreKeyWire b = some p →
    let known := ∃ ek ∈ bobDoneBaseKeys tr, ecKey (gamma interpretation S g ek) = p.baseKey.take 33
    match s with
    | .messageDecrypt .. | .messageDecryptSkipped .. => known
    | .bobStart .. => ¬ known
    | _ => True

/-- `drs` matches consecutive non-empty slices of a prefix of `coins`. -/
def DrawsMatch (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (drs : List VisEntry) (coins : HwBytes) : Prop :=
  ∃ pieces : List HwBytes,
    (∀ p ∈ pieces, p ≠ []) ∧ pieces.flatten <+: coins ∧
    List.Forall₂ (fun p v => BytesMatchEntry interpretation r S g .rng p v) pieces drs

def OutputsMatch (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ev : RunEvent) (outs : List VisEntry) (initIds : Option BundlePreKeyIds := none) : Prop :=
  match ev.exit, ev.cmd with
  | some (0, out), .send _ => ∃ v, outs = [v] ∧ BytesMatchEntry interpretation r S g .send out v initIds
  | some (0, out), .recv _ => ∃ v, outs = [v] ∧ BytesMatchEntry interpretation r S g .accept out v
  | _, _ => outs = []

/-- Party step `s` from `tr` explains exit-0 CLI run event `ev` with visible entries `vis`. -/
def RunMatches (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (s : Step) (ev : RunEvent) (vis : List VisEntry)
    (initIds : Option BundlePreKeyIds := none) : Prop :=
  s.cls = .party ∧ s.party? = some ev.party ∧ s.FitsCmd ev.cmd ∧ s.MatchesSetupPeer r ∧
    s.ok tr = true ∧ (∃ out, ev.exit = some (0, out)) ∧
    vis = stepView s tr (runWrapped ev) ∧
    ∃ inp drs outs, vis = inp :: (drs ++ outs) ∧
      BytesMatchEntry interpretation r S g (inputKind ev) ev.input inp ∧
      DrawsMatch interpretation r S g drs ev.coins ∧
      OutputsMatch interpretation r S g ev outs initIds ∧
      ReadsFaithfully interpretation r S g tr inp ev.input ∧
      PathFaithfulAt interpretation S g tr s ev.input

/-- Non-exit-0 CLI run event (writes and prints nothing, matched by zero party steps). -/
def RunRejected (ev : RunEvent) : Prop := ∀ out, ev.exit ≠ some (0, out)

def Step.IsLeak : Step → Prop
  | .compromiseIK .. | .compromiseSPK .. | .compromisePQSPK .. | .compromiseOPK .. => True
  | .exposeKey .. | .exposeSpqr .. | .exposeSkipped .. => True
  | _ => False

def invertEntry (s : Step) (tr : ExecTrace) (layout : VisByteLayout) : List VisEntry :=
  ((lastSent tr (s.next tr)).map fun sk => (⟨.leak, [sk], layout, none⟩ : VisEntry)).toList

/-- Environment step `s` from `tr` explains `EnvEvent` `ev` (`leak`, `breakDH`, `breakKEM`,
`invertDH`, or `invertKEM`) with visible entries `vis`. -/
def EnvMatches (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (s : Step) (ev : EnvEvent) (vis : List VisEntry) : Prop :=
  match ev with
  | .leak p k =>
    s.cls = .env ∧ s.IsLeak ∧ (∀ q, s.party? = some q → q = p) ∧
      vis = stepView s tr false ∧
      ∃ v, vis = [v] ∧ BytesMatchEntry interpretation r S g .leak k v
  | .breakDH => s = .breakDH ∧ vis = []
  | .breakKEM => s = .breakKEM ∧ vis = []
  | .invertDH pk sk =>
    ∃ h, s = .invertDH h ∧ s.ok tr = true ∧
      (tr.getMessageSentAt h).map (gamma interpretation S g) = some pk ∧
      vis = invertEntry s tr .leakRecord ∧
      ∃ v, vis = [v] ∧ BytesMatchEntry interpretation r S g .leak sk v
  | .invertKEM pk sk =>
    ∃ h, s = .invertKEM h ∧ s.ok tr = true ∧
      (tr.getMessageSentAt h).map (gamma interpretation S g) = some pk ∧
      vis = invertEntry s tr (.leakPq true) ∧
      ∃ v, vis = [v] ∧ BytesMatchEntry interpretation r S g .leak sk v
  | .registerCorrupt .. => False

def nextBundleIds (initIds : Option BundlePreKeyIds) (ev : RunEvent) : Option BundlePreKeyIds :=
  match ev.cmd with
  | .init _ _ => some (bundlePreKeyIds ev.input)
  | _ => initIds

def stepBundleIds (initIds : Option BundlePreKeyIds) : CliEvent → Option BundlePreKeyIds
  | .run ev =>
    match ev.exit, ev.cmd with
    | some (0, _), .init _ _ => some (bundlePreKeyIds ev.input)
    | _, _ => initIds
  | .env _ => initIds

def activeBundleIds (evs : List CliEvent) : Option BundlePreKeyIds :=
  evs.foldl stepBundleIds none

/-- Event-by-event alignment between model steps `ss` (allowing interleaved invisible `network`
steps) and CLI events `evs` under active bundle IDs `initIds`, accumulating `vis`. -/
inductive MatchesEventsAt (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) : Option BundlePreKeyIds → ExecTrace → List Step → List CliEvent → List VisEntry → Prop
  | nil {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} :
      (∀ x ∈ ss, x.cls = .invisible) →
      MatchesEventsAt interpretation r S g initIds tr ss [] []
  | run1 {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step} {ss : List Step}
      {ev : RunEvent} {evs : List CliEvent} {v vs : List VisEntry} :
      (∀ x ∈ pre, x.cls = .invisible) →
      RunMatches interpretation r S g (runSteps pre tr) s ev v initIds →
      MatchesEventsAt interpretation r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss evs vs →
      MatchesEventsAt interpretation r S g initIds tr (pre ++ s :: ss) (.run ev :: evs) (v ++ vs)
  | run0 {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre ss : List Step} {ev : RunEvent}
      {evs : List CliEvent} {vs : List VisEntry} :
      (∀ x ∈ pre, x.cls = .invisible) →
      RunRejected ev →
      MatchesEventsAt interpretation r S g initIds (runSteps pre tr) ss evs vs →
      MatchesEventsAt interpretation r S g initIds tr (pre ++ ss) (.run ev :: evs) vs
  | env {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step} {ss : List Step}
      {ev : EnvEvent} {evs : List CliEvent} {v vs : List VisEntry} :
      (∀ x ∈ pre, x.cls = .invisible) →
      EnvMatches interpretation r S g (runSteps pre tr) s ev v →
      MatchesEventsAt interpretation r S g initIds (s.next (runSteps pre tr)) ss evs vs →
      MatchesEventsAt interpretation r S g initIds tr (pre ++ s :: ss) (.env ev :: evs) (v ++ vs)

abbrev MatchesEvents (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) : ExecTrace → List Step → List CliEvent → List VisEntry → Prop :=
  MatchesEventsAt interpretation r S g none

/-- Whole-trace explanation: `(S, g)` agree with `r`, `g` satisfies `GhostWF` on `vis`, `ss` is a
faithful model run (`ModelRunWF`), and `ss` aligns with `evs` (`MatchesEvents`). -/
def Explains (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry) (evs : List CliEvent) : Prop :=
  GhostAndSemMatchSetup interpretation r S g ∧ GhostWF g vis ∧ ModelRunWF r ss ∧
    MatchesEvents interpretation r S g (setupTrace r) ss evs vis

/-- Every X25519 public key produced by `x25519PublicKeySymbol` decodes below `p25519`. -/
def X25519PubCanonical (interpretation : ExternInterpretation) : Prop :=
  ∀ s : HwBytes,
    DY.X25519.leValue (((interpretation x25519PublicKeySymbol [s]).getD []).map BitVec.toNat) <
      DY.X25519.p25519

end DY.Libsignal.Composed.Refinement
