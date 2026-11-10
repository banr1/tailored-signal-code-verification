/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect

/-!
# Costed Signature, Operation Tables, and ReductionDsl Programs for Session Reductions

**Checked by Lean.**

Defines the `ReductionDsl` base sorts, unit-size signature, primitive operation and sampler tables,
target oracle interfaces, and source SM game codec shared by the libsignal-to-Fig. 8 simulator,
`DeliverForge`, and `KemFailFind` reductions (`DEV-LS37`). Also constructs the `ReductionDsl`
mirror-bookkeeping expressions and the costed reduction programs `simDeliverForgeProg` and
`kemFailRedProg`.
-/

@[expose] public section

namespace CryptoGames.Ratchet.LibsignalSim

open ReductionDsl OracleSpec OracleComp
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD SM SM.Construction CKA LibsignalSession
  LibsignalInst

/-! ## SPQR V1 braid tracker -/

abbrev SimBraidSt (F : ShaCompress) : Type :=
  CryptoVerification.LibsignalSpqrV1.States
    CryptoVerification.LibsignalSpqrV1.spqrPolyApi
    (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F)

abbrev SimBraidMsg : Type :=
  CryptoVerification.LibsignalSpqrV1.Message CryptoVerification.LibsignalSpqrV1.spqrPolyApi

abbrev SimKemSeed : Type := List.Vector (BitVec 8) 64

abbrev SimKemEncRand : Type := List.Vector (BitVec 8) 32

def simEncRandOf (r : BitVec 512) : SimKemEncRand :=
  ⟨(CryptoVerification.LibsignalSpqrV1.coinBytes r).take 32, by
    simp [CryptoVerification.LibsignalSpqrV1.coinBytes_length]⟩

/-- Coins drawn so far in the current SPQR V1 braid epoch. -/
inductive SimKemCoins where
  | init
  | seed (s : SimKemSeed)
  | both (s : SimKemSeed) (r : SimKemEncRand)

def simEkSideIsA (e : BitVec 64) : Bool :=
  decide (e.toNat % 2 = 1)

def simNextKemCoins (F : ShaCompress) (c : SimKemCoins) (st : SimBraidSt F)
    (tape : List (BitVec 8)) : SimKemCoins :=
  match c, st with
  | .init, .keysUnsampled _ =>
    if h : (tape.take 64).length = 64 then .seed ⟨tape.take 64, h⟩ else .init
  | .seed s, .headerReceived _ =>
    if h : (tape.take 32).length = 32 then .both s ⟨tape.take 32, h⟩ else .seed s
  | c, _ => c

def simBe64 (v : BitVec 64) : List (BitVec 8) :=
  [ v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
    v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb'  8 8, v.extractLsb'  0 8 ]

def simAuthNext (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (e : BitVec 64)
    (auth : CryptoVerification.LibsignalSpqrV1.Authenticator) (s : SimKemSeed)
    (r : SimKemEncRand) : CryptoVerification.LibsignalSpqrV1.Authenticator :=
  let hdr := (K.fromSeed s).1.toList
  let ss0 := ((K.encaps1 hdr r).map fun t => t.2.2.toList).getD []
  let sec := CryptoVerification.LibsignalSpqrV1.hkdfToVecUnchecked F
    (List.replicate 32 0#8) ss0
    (CryptoVerification.LibsignalSpqrV1.sckaKeyInfoPrefix ++ simBe64 e) 32
  auth.update F e sec

/-- Computable SPQR V1 braid tracker monitoring cross-party `(seed, encRand)` pairs along honest sends and deliveries. -/
structure SimKemFailTrack (F : ShaCompress) where
  e : BitVec 64
  auth : CryptoVerification.LibsignalSpqrV1.Authenticator
  c : SimKemCoins
  st : Party → SimBraidSt F
  sentB : List (SimBraidMsg × BitVec 32)
  sendCtr : Party → ℕ → ℕ
  cand : Option (SimKemSeed × SimKemEncRand)

def simDefaultKemCand : SimKemSeed × SimKemEncRand :=
  (List.Vector.replicate 64 0#8, List.Vector.replicate 32 0#8)

def simKemFailCand {F : ShaCompress} (tr : SimKemFailTrack F) : SimKemSeed × SimKemEncRand :=
  tr.cand.getD simDefaultKemCand

def simInitKemFailTrack (F : ShaCompress) (k : BitVec 256) : SimKemFailTrack F :=
  let auth₀ := CryptoVerification.LibsignalSpqrV1.Authenticator.new F (keyToBytes32 k) 1#64
  let dec96 : CryptoVerification.LibsignalSpqrV1.PolyDecoder :=
    { ptsNeeded := 48
      pts := List.replicate 16 CryptoVerification.LibsignalSpqrV1.SortedSetPt.new
      isComplete := false }
  let stA₀ : SimBraidSt F := .keysUnsampled { uc := { epoch := 1#64, auth := auth₀ } }
  let stB₀ : SimBraidSt F := .noHeaderReceived
    { uc := { epoch := 1#64, auth := auth₀ }, receiving_hdr := dec96 }
  { e := 1#64
    auth := auth₀
    c := .init
    st := fun Q => match Q with | .A => stA₀ | .B => stB₀
    sentB := []
    sendCtr := fun _ _ => 0
    cand := none }

/-- Advance `SimKemFailTrack` on a send by `Q` with coins `r`, recording the first exchange failure. -/
def simStepKemFailSend (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (tr : SimKemFailTrack F) (Q : Party) (r : BitVec 512) : SimKemFailTrack F :=
  let cand' :=
    match tr.cand with
    | some p => some p
    | none =>
      if simEkSideIsA tr.e != (Q == .A) then
        match tr.c, tr.st Q with
        | .seed s, .headerReceived _ =>
          if K.honestExchangeFails s (simEncRandOf r) then some (s, simEncRandOf r) else none
        | _, _ => none
      else none
  let tape := CryptoVerification.LibsignalSpqrV1.coinBytes r
  match (tr.st Q).send K tape with
  | .ok (out, _) =>
    let E := out.msg.epoch.toNat - 1
    let n := tr.sendCtr Q E
    { tr with
      c := simNextKemCoins F tr.c (tr.st Q) tape
      st := Function.update tr.st Q out.state
      sentB := tr.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
      sendCtr := Function.update tr.sendCtr Q (Function.update (tr.sendCtr Q) E (n + 1))
      cand := cand' }
  | .error _ => { tr with cand := cand' }

def simStepKemFailDeliver (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (tr : SimKemFailTrack F) (Q : Party) (j : ℕ) : SimKemFailTrack F :=
  match tr.sentB[j]? with
  | none => tr
  | some (m, _) =>
    match (tr.st Q).recv K m with
    | .ok out =>
      let tr1 := { tr with st := Function.update tr.st Q out.state }
      let noneNext : SimBraidMsg := { epoch := tr.e + 1#64, payload := .none }
      if m = noneNext then
        match tr.c with
        | .both s r =>
          { tr1 with e := tr.e + 1#64, auth := simAuthNext F K tr.e tr.auth s r, c := .init }
        | _ => tr1
      else tr1
    | .error _ => tr

/-! ## Sorts and signature -/

/-- Base sorts of `simSig` for the session-level `ReductionDsl` reductions. -/
inductive SimSort
  | ghostSt
  | plain
  | pqc
  | wire
  | pq
  | u32
  | bv64
  | bv256
  | salt32
  | pk
  | keyPair
  | pt
  | lpub
  | lct
  | fig8st
  | vsSt
  | vrSt
  | senderChain
  | recvChain
  | chainSt
  | kemTrack
  | kemCand
  deriving DecidableEq

abbrev SimFig8St (Pt : Type) : Type :=
  PartyState (CKA.DDH.State (BitVec 256) Pt) Pt Ratchet.RootKey
    (FSAEAD.RatchetSenderState (BitVec 256)) (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))

abbrev SimFig8C (Pt : Type) : Type := Header Pt × (ℕ × LibsignalCiphertextWithSalt32)

@[reducible] def SimSort.den (PQ PQC Pt : Type) (ℓ : ℕ) : SimSort → Type
  | .ghostSt => GhostState PQ
  | .plain => Plain ℓ
  | .pqc => PQC
  | .wire => List (BitVec 8)
  | .pq => PQ
  | .u32 => BitVec 32
  | .bv64 => BitVec 64
  | .bv256 => BitVec 256
  | .salt32 => Salt32
  | .pk => PublicKey
  | .keyPair => KeyPair
  | .pt => Pt
  | .lpub => LibsignalMsgPublicPart
  | .lct => ℕ × LibsignalCiphertextWithSalt32
  | .fig8st => SimFig8St Pt
  | .vsSt => FSAEAD.RatchetSenderState (BitVec 256)
  | .vrSt => FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)
  | .senderChain => SenderChain
  | .recvChain => ReceiverChain
  | .chainSt => ℕ × List ℕ
  | .kemTrack => Σ F : ShaCompress, SimKemFailTrack F
  | .kemCand => SimKemSeed × SimKemEncRand

/-- Unit-base-size `ReductionDsl` signature over `SimSort` for the session reductions. -/
@[reducible] def simSig (PQ PQC Pt : Type) (ℓ : ℕ) : Sig where
  Base := SimSort
  den := SimSort.den PQ PQC Pt ℓ
  sz := fun _ _ => 1

@[reducible] def ghostChainTy (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .prod (.opt (.base .pk)) (.prod .nat (.base .chainSt))

@[reducible] def fig8CTy (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .prod (.prod .nat (.opt (.base .pt))) (.base .lct)

@[reducible] def lpubPlainTy (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .prod (.base .lpub) (.base .plain)

@[reducible] def simRrTy (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .sum .unit (.prod .nat (.prod .nat (.opt (.base .plain))))

@[reducible] def fig8RrTy (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .sum .unit (.prod .nat (.prod .nat (.opt (lpubPlainTy PQ PQC Pt ℓ))))

def simTagBytes (t : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map fun j => (t >>> (8 * j)).truncate 8

def simToWire {Pt : Type} (c : SimFig8C Pt) : List (BitVec 8) :=
  c.2.2.1.1 ++ simTagBytes c.2.2.1.2

def simSplitWireTag (w : List (BitVec 8)) : Option (List (BitVec 8) × BitVec 64) :=
  if w.length < 9 then none
  else some (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8)))

def simParseWire (codec : SignalMessageProtoCodec) (ser : List (BitVec 8)) :
    Option (PublicKey × (BitVec 32 × (List (BitVec 8) × Option (List (BitVec 8))))) :=
  ((signalWireCodec codec).parse ser).map fun (h, _) =>
    (h.senderRatchetKey, (h.counter, (h.pqRatchet, h.addresses)))

def simChainAccept (ls : ℕ × List ℕ) (i : ℕ) : ℕ × List ℕ :=
  if ls.1 < i then
    (i, ((List.range (i - 1 - ls.1)).map (fun d => i - 1 - d) ++ ls.2).take 2000)
  else
    (ls.1, ls.2.erase i)

def simChainRejects (ls : ℕ × List ℕ) (i : ℕ) : Bool :=
  if i ≤ ls.1 then !(ls.2.contains i)
  else decide (25000 < i - 1 - ls.1) || decide (2 ^ 32 ≤ i)

def simMkSenderChain (kp : KeyPair) (v : FSAEAD.RatchetSenderState (BitVec 256)) : SenderChain :=
  ⟨kp, ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩⟩

def simMkRecvChain (k? : Option PublicKey) (ls : ℕ × List ℕ)
    (v? : Option (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))) : ReceiverChain :=
  let k := match k? with | some k => k | none => dummyKey
  match v? with
  | some v =>
    ⟨k, some ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩, ls.2.filterMap fun j =>
      (v.skippedKeys.lookup j).map fun mk => ⟨keyToBytes32 mk, BitVec.ofNat 32 (j - 1)⟩⟩
  | none => ⟨k, none, []⟩

def simMkGhostState {PQ PQC : Type} (P : Params PQ PQC) (qB : Bool) (rk : BitVec 256)
    (pn : BitVec 32) (sc : Option SenderChain) (rcs : List ReceiverChain) (ppk : Bool)
    (pq : PQ) (ep : ℕ) (eps : List ℕ) : GhostState PQ :=
  let Q := partyDec qB
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  ⟨Q, { sessionVersion := BitVec.ofNat 32 currentVersion.toNat, localIdentity := idOf Q,
        remoteIdentity := some (idOf Q.other), rootKey := rk, previousCounter := pn,
        senderChain := sc, receiverChains := rcs, pendingPreKey := ppk, pqRatchetState := pq },
    ep, eps⟩

def simChainKeyAfter (F : ShaCompress) : ℕ → BitVec 256 → BitVec 256
  | 0, k => k
  | n + 1, k => simChainKeyAfter F n (bytesToKey32 (Ratchet.chainHmac F k Ratchet.chainKeySeed))

def simChainSeedAt (F : ShaCompress) (ck : LibsignalSession.ChainKey) (counter : BitVec 32) :
    Option (List (BitVec 8)) :=
  if counter.toNat < ck.index.toNat then none
  else some (Ratchet.chainHmac F (simChainKeyAfter F (counter.toNat - ck.index.toNat) ck.key)
    Ratchet.messageKeySeed)

/-- Evaluate one corruption-snapshot seed-derivation step of `LibsignalSimC.snapshotMessageKeySeed` (`DEV-LS37`). -/
def simSnapSeed {PQ PQC : Type} (P : Params PQ PQC) (branch : ℕ) (qB : Bool)
    (w : List (BitVec 8)) (t : ℕ) (e : Bool × (ℕ × GhostState PQ))
    (ePrev? : Option (Bool × (ℕ × GhostState PQ))) : Option (List (BitVec 8)) :=
  let Q := partyDec qB
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let Y := msg.senderRatchetKey
    let n := msg.counter
    match ePrev? with
    | none =>
      if branch = 0 then
        if partyDec e.1 = Q then
          (e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y)).bind fun rc =>
            match rc.messageKeys.find? (·.counter == n) with
            | some mkg => some mkg.seed
            | none => rc.chainKey.bind fun ck => simChainSeedAt P.C.F ck n
        else none
      else if branch = 1 then
        if partyDec e.1 = Q.other then
          e.2.2.session.senderChain.bind fun sc =>
            if sc.ratchetKey.publicKey = Y then simChainSeedAt P.C.F sc.chainKey n else none
        else none
      else if branch = 4 then
        if partyDec e.1 = Q.other ∧ e.2.1 = t then
          e.2.2.session.senderChain.bind fun sc_cur =>
            if sc_cur.ratchetKey.publicKey = Y then
              e.2.2.session.receiverChains.getLast?.map fun _ => []
            else none
        else none
      else
        if partyDec e.1 = Q ∧ Q.sendsIn e.2.1 = true ∧ t = e.2.1 + 1 then
          e.2.2.session.senderChain.bind fun sc =>
            match rootCreateChain P.C e.2.2.session.rootKey Y sc.ratchetKey.privateKey with
            | .ok (_, ck) => simChainSeedAt P.C.F ck n
            | .error _ => none
        else none
    | some e_prev =>
      if partyDec e.1 = Q.other ∧ e.2.1 = t then
        e.2.2.session.senderChain.bind fun sc_cur =>
          if sc_cur.ratchetKey.publicKey = Y then
            e.2.2.session.receiverChains.getLast?.bind fun rc_last =>
              if partyDec e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧
                  t = e_prev.2.1 + 2 then
                e_prev.2.2.session.senderChain.bind fun sc_prev =>
                  match rootCreateChain P.C e_prev.2.2.session.rootKey
                      rc_last.senderRatchetKey sc_prev.ratchetKey.privateKey with
                  | .ok (rk1, _) =>
                    match rootCreateChain P.C rk1 rc_last.senderRatchetKey
                        sc_cur.ratchetKey.privateKey with
                    | .ok (_, ck0) => simChainSeedAt P.C.F ck0 n
                    | .error _ => none
                  | .error _ => none
              else none
          else none
      else none

def simKDecryptFig8 {PQ PQC Pt : Type} (P : Params PQ PQC) (ℓ B : ℕ) (qB : Bool)
    (w : List (BitVec 8)) (c' : SimFig8C Pt) (seed : List (BitVec 8)) :
    Option (ℕ × (ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  let Q := partyDec qB
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let kDec : Option (List (BitVec 8)) :=
    match SignalMessage.tryFrom P.codec w with
    | .error _ => none
    | .ok msg =>
      let mk := deriveMessageKeys P.C.F (some c'.2.2.2) seed
      if !(msg.verifyMacWithAddresses P.C.F (P.expectedAddrs Q) (idOf Q.other) (idOf Q) mk.2) then
        none
      else aesCbcDecrypt P.C.D mk.1.1 mk.1.2 msg.ciphertext
  match lPubOf P.codec c'.2.2, kDec with
  | some pub, some m_raw => some (min c'.1.1 B, (min c'.2.1 B, (pub, padOrTruncatePlain ℓ m_raw)))
  | _, _ => none

/-! ## Operation table -/

/-- Primitive operation tags of `simParamOps`. -/
inductive SimOp
  | spqrInitA
  | spqrInitB
  | spqrSend
  | spqrRecv
  | spqrRecvPanics
  | zeroU32
  | natToU32
  | u32IncToNat (B : ℕ)
  | defaultPlain
  | emptyLPub
  | effectiveHkdfSalt32
  | addrAB
  | addrsOkA
  | addrsOkB
  | mkLPub
  | splitWireTag
  | parseWire
  | mkLCt
  | toWire
  | eqWire
  | eqFig8C
  | lctSaltEq
  | injOK
  | dh
  | dhBase
  | encT
  | decT
  | eqPk
  | isZeroPt
  | keyPairGen
  | emptyChainSt
  | chainAccept
  | chainRejects
  | fig8Root
  | fig8GammaExp
  | fig8VS
  | fig8VR
  | mkSenderChain
  | mkRecvChain
  | mkGhostState
  | fig8Init
  | fig8SendStep (B : ℕ)
  | fig8Receive (B : ℕ)
  | fsReceive (B : ℕ)
  | senderToFreshVr
  | sameWireFig8
  | snapSeed
  | kDecryptFig8 (B : ℕ)
  | initKemFailTrack
  | stepKemFailSend
  | stepKemFailDeliver
  deriving DecidableEq

def simOpCost (cSpqrInit cSpqrSend cSpqrRecv cSpqrRecvPanics cSplitWireTag cParseWire cU32ToNat
    cToWire cEqWire cEqFig8C cInjOK cDh cEncT cDecT cIsZeroPt cKeyPairGen
    cFig8Init cFig8Send cFig8Recv cFsRecv cSentEval cSameWireFig8 cSnapSeed cKDecrypt
    cKemInit cKemSend cKemDeliver : ℕ) : SimOp → ℕ
  | .spqrInitA => cSpqrInit
  | .spqrInitB => cSpqrInit
  | .spqrSend => cSpqrSend
  | .spqrRecv => cSpqrRecv
  | .spqrRecvPanics => cSpqrRecvPanics
  | .zeroU32 => 1
  | .natToU32 => 1
  | .u32IncToNat B => cU32ToNat + bits B
  | .defaultPlain => 1
  | .emptyLPub => 1
  | .effectiveHkdfSalt32 => 1
  | .addrAB => 1
  | .addrsOkA => 1
  | .addrsOkB => 1
  | .mkLPub => 1
  | .splitWireTag => cSplitWireTag
  | .parseWire => cParseWire
  | .mkLCt => 1
  | .toWire => cToWire
  | .eqWire => cEqWire
  | .eqFig8C => cEqFig8C
  | .lctSaltEq => 1
  | .injOK => cInjOK
  | .dh => cDh
  | .dhBase => 1
  | .encT => cEncT
  | .decT => cDecT
  | .eqPk => 1
  | .isZeroPt => cIsZeroPt
  | .keyPairGen => cKeyPairGen
  | .emptyChainSt => 1
  | .chainAccept => 1
  | .chainRejects => 1
  | .fig8Root => 1
  | .fig8GammaExp => 1
  | .fig8VS => 1
  | .fig8VR => 1
  | .mkSenderChain => 1
  | .mkRecvChain => 1
  | .mkGhostState => 1
  | .fig8Init => cFig8Init
  | .fig8SendStep B => cFig8Send + bits B
  | .fig8Receive B => cFig8Recv + 2 * bits B
  | .fsReceive B => cFsRecv + bits B
  | .senderToFreshVr => cSentEval
  | .sameWireFig8 => cSameWireFig8
  | .snapSeed => cSnapSeed
  | .kDecryptFig8 B => cKDecrypt + 2 * bits B
  | .initKemFailTrack => cKemInit
  | .stepKemFailSend => cKemSend
  | .stepKemFailDeliver => cKemDeliver

/-- Parametric `ReductionDsl` operation table for the session reductions. -/
@[reducible] def simParamOps {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512)
    (cSpqrInit cSpqrSend cSpqrRecv cSpqrRecvPanics cSplitWireTag cParseWire cU32ToNat cToWire
      cEqWire cEqFig8C cInjOK cDh cEncT cDecT cIsZeroPt cKeyPairGen
      cFig8Init cFig8Send cFig8Recv cFsRecv cSentEval cSameWireFig8 cSnapSeed cKDecrypt
      cKemInit cKemSend cKemDeliver : ℕ) :
    Ops (simSig PQ PQC Pt ℓ) where
  Op := SimOp
  dom := fun
    | .spqrInitA => .base .bv256
    | .spqrInitB => .base .bv256
    | .spqrSend => .prod (.base .pq) (.base .pqc)
    | .spqrRecv => .prod (.base .pq) (.base .wire)
    | .spqrRecvPanics => .prod (.base .pq) (.base .wire)
    | .zeroU32 => .unit
    | .natToU32 => .nat
    | .u32IncToNat _ => .base .u32
    | .defaultPlain => .unit
    | .emptyLPub => .unit
    | .effectiveHkdfSalt32 => .opt (.base .salt32)
    | .addrAB => .unit
    | .addrsOkA => .opt (.base .wire)
    | .addrsOkB => .opt (.base .wire)
    | .mkLPub =>
      .prod (.base .u32) (.prod (.base .wire) (.prod (.base .salt32) (.opt (.base .wire))))
    | .splitWireTag => .base .wire
    | .parseWire => .base .wire
    | .mkLCt => .prod (.base .u32) (.prod (.prod (.base .wire) (.base .bv64)) (.base .salt32))
    | .toWire => fig8CTy PQ PQC Pt ℓ
    | .eqWire => .prod (.base .wire) (.base .wire)
    | .eqFig8C => .prod (fig8CTy PQ PQC Pt ℓ) (fig8CTy PQ PQC Pt ℓ)
    | .lctSaltEq => .prod (.base .lct) (.base .lct)
    | .injOK => .base .wire
    | .dh => .prod (.base .bv256) (.base .pt)
    | .dhBase => .unit
    | .encT => .base .pt
    | .decT => .base .pk
    | .eqPk => .prod (.base .pk) (.base .pk)
    | .isZeroPt => .opt (.base .pt)
    | .keyPairGen => .base .bv256
    | .emptyChainSt => .unit
    | .chainAccept => .prod (.base .chainSt) .nat
    | .chainRejects => .prod (.base .chainSt) .nat
    | .fig8Root => .base .fig8st
    | .fig8GammaExp => .base .fig8st
    | .fig8VS => .base .fig8st
    | .fig8VR => .prod (.base .fig8st) .nat
    | .mkSenderChain => .prod (.base .keyPair) (.base .vsSt)
    | .mkRecvChain => .prod (.opt (.base .pk)) (.prod (.base .chainSt) (.opt (.base .vrSt)))
    | .mkGhostState =>
      .prod .bool
        (.prod (.base .bv256)
          (.prod (.base .u32)
            (.prod (.opt (.base .senderChain))
              (.prod (.list (.base .recvChain))
                (.prod .bool (.prod (.base .pq) (.prod .nat (.list .nat))))))))
    | .fig8Init => .prod (.base .bv256) (.base .bv256)
    | .fig8SendStep _ =>
      .prod (.base .fig8st) (.opt (.prod (lpubPlainTy PQ PQC Pt ℓ) (.base .bv256)))
    | .fig8Receive _ => .prod (.base .fig8st) (fig8CTy PQ PQC Pt ℓ)
    | .fsReceive _ => .prod (.base .vrSt) (fig8CTy PQ PQC Pt ℓ)
    | .senderToFreshVr => .base .vsSt
    | .sameWireFig8 => .prod (fig8CTy PQ PQC Pt ℓ) (fig8CTy PQ PQC Pt ℓ)
    | .snapSeed =>
      .prod .nat
        (.prod .bool
          (.prod (.base .wire)
            (.prod .nat
              (.prod (.prod .bool (.prod .nat (.base .ghostSt)))
                (.opt (.prod .bool (.prod .nat (.base .ghostSt))))))))
    | .kDecryptFig8 _ =>
      .prod .bool (.prod (.base .wire) (.prod (fig8CTy PQ PQC Pt ℓ) (.base .wire)))
    | .initKemFailTrack => .base .bv256
    | .stepKemFailSend => .prod (.base .kemTrack) (.prod .bool (.base .pqc))
    | .stepKemFailDeliver => .prod (.base .kemTrack) (.prod .bool .nat)
  cod := fun
    | .spqrInitA => .base .pq
    | .spqrInitB => .base .pq
    | .spqrSend => .opt (.prod (.base .pq) (.prod (.opt (.base .salt32)) (.base .wire)))
    | .spqrRecv => .opt (.prod (.base .pq) (.opt (.base .salt32)))
    | .spqrRecvPanics => .bool
    | .zeroU32 => .base .u32
    | .natToU32 => .base .u32
    | .u32IncToNat _ => .nat
    | .defaultPlain => .base .plain
    | .emptyLPub => .base .lpub
    | .effectiveHkdfSalt32 => .base .salt32
    | .addrAB => .opt (.base .wire)
    | .addrsOkA => .bool
    | .addrsOkB => .bool
    | .mkLPub => .base .lpub
    | .splitWireTag => .opt (.prod (.base .wire) (.base .bv64))
    | .parseWire =>
      .opt (.prod (.base .pk) (.prod (.base .u32) (.prod (.base .wire) (.opt (.base .wire)))))
    | .mkLCt => .base .lct
    | .toWire => .base .wire
    | .eqWire => .bool
    | .eqFig8C => .bool
    | .lctSaltEq => .bool
    | .injOK => .bool
    | .dh => .base .pt
    | .dhBase => .base .pt
    | .encT => .base .pk
    | .decT => .opt (.base .pt)
    | .eqPk => .bool
    | .isZeroPt => .bool
    | .keyPairGen => .base .keyPair
    | .emptyChainSt => .base .chainSt
    | .chainAccept => .base .chainSt
    | .chainRejects => .bool
    | .fig8Root => .base .bv256
    | .fig8GammaExp => .opt (.base .bv256)
    | .fig8VS => .opt (.base .vsSt)
    | .fig8VR => .opt (.base .vrSt)
    | .mkSenderChain => .base .senderChain
    | .mkRecvChain => .base .recvChain
    | .mkGhostState => .base .ghostSt
    | .fig8Init => .prod (.base .fig8st) (.base .fig8st)
    | .fig8SendStep _ => .prod .bool (.prod (.base .fig8st) (fig8CTy PQ PQC Pt ℓ))
    | .fig8Receive _ =>
      .opt (.prod (.base .fig8st) (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))
    | .fsReceive _ => .opt (.prod (.base .vrSt) (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))
    | .senderToFreshVr => .base .vrSt
    | .sameWireFig8 => .bool
    | .snapSeed => .opt (.base .wire)
    | .kDecryptFig8 _ => .opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))
    | .initKemFailTrack => .prod (.base .kemTrack) (.base .kemCand)
    | .stepKemFailSend =>
      .prod (.base .kemTrack) (.prod (.base .kemTrack) (.base .kemCand))
    | .stepKemFailDeliver => .base .kemTrack
  eval := fun
    | .spqrInitA, k => P.spqr.init .a2b k
    | .spqrInitB, k => P.spqr.init .b2a k
    | .spqrSend, (pq, rq) => P.spqr.send pq rq
    | .spqrRecv, (pq, pqm) => (P.spqr.recv pq pqm).toOption
    | .spqrRecvPanics, (pq, pqm) => P.spqr.recvPanics pq pqm
    | .zeroU32, () => 0
    | .natToU32, n => BitVec.ofNat 32 n
    | .u32IncToNat B, c => min (c.toNat + 1) B
    | .defaultPlain, () => default
    | .emptyLPub, () => ⟨0, [], effectiveHkdfSalt32 none, none⟩
    | .effectiveHkdfSalt32, s => effectiveHkdfSalt32 s
    | .addrAB, () => P.addrAB
    | .addrsOkA, a => addressCheckPasses a (P.expectedAddrs .A)
    | .addrsOkB, a => addressCheckPasses a (P.expectedAddrs .B)
    | .mkLPub, (pn, (pqm, (s, a))) => ⟨pn, pqm, s, a⟩
    | .splitWireTag, w => simSplitWireTag w
    | .parseWire, ser => simParseWire P.codec ser
    | .mkLCt, (c, (st, s)) => (c.toNat + 1, (st, s))
    | .toWire, c => simToWire c
    | .eqWire, (w₁, w₂) => w₁ == w₂
    | .eqFig8C, (c₁, c₂) => decide (c₁ = c₂)
    | .lctSaltEq, (l₁, l₂) => decide (l₁.2.2 = l₂.2.2)
    | .injOK, w => ratchetKeyAdmissible P.codec decT encT w
    | .dh, (x, Q) => Dh.dh x Q
    | .dhBase, () => Dh.base
    | .encT, T => encT T
    | .decT, k => decT k
    | .eqPk, (k₁, k₂) => k₁ == k₂
    | .isZeroPt, T? => T? == some 0
    | .keyPairGen, x => KeyPair.generate P.C x
    | .emptyChainSt, () => (0, [])
    | .chainAccept, (ls, i) => simChainAccept ls i
    | .chainRejects, (ls, i) => simChainRejects ls i
    | .fig8Root, st => st.root
    | .fig8GammaExp, st => match st.γ with | .exp x => some x | _ => none
    | .fig8VS, st => st.vS
    | .fig8VR, (st, ep) => st.vR ep
    | .mkSenderChain, (kp, v) => simMkSenderChain kp v
    | .mkRecvChain, (k?, (ls, v?)) => simMkRecvChain k? ls v?
    | .mkGhostState, (qB, (rk, (pn, (sc, (rcs, (ppk, (pq, (ep, eps)))))))) =>
      simMkGhostState P qB rk pn sc rcs ppk pq ep eps
    | .fig8Init, k =>
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      (fig.initA k, fig.initB k)
    | .fig8SendStep B, (st, mc?) =>
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let (m, coins) := mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)
      let (st', c) := fig.send st m coins
      (st.id.sendsIn (st.tcur + 1), (st', ((min c.1.1 B, c.1.2), c.2)))
    | .fig8Receive B, (st, c) =>
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      (fig.receive st c).map fun (st', t, i, pm) => (st', (min t B, (min i B, pm)))
    | .fsReceive B, (v, c) =>
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      (fs.receive v c.1 c.2).map fun (v', i, pm) => (v', (min i B, pm))
    | .senderToFreshVr, v => ⟨v.chainKey, v.lastIndex, []⟩
    | .sameWireFig8, (c, c') => decide (c.1 = c'.1 ∧ c.2.1 = c'.2.1 ∧ c.2.2.1 = c'.2.2.1)
    | .snapSeed, (branch, (qB, (w, (t, (e, ePrev?))))) =>
      simSnapSeed P branch qB w t e ePrev?
    | .kDecryptFig8 B, (qB, (w, (c', seed))) =>
      simKDecryptFig8 P ℓ B qB w c' seed
    | .initKemFailTrack, k =>
      (⟨P.C.F, simInitKemFailTrack P.C.F k⟩, simDefaultKemCand)
    | .stepKemFailSend, (⟨F, tr⟩, (qB, rq)) =>
      let tr' := simStepKemFailSend F K tr (partyDec qB) (toKemCoins rq)
      (⟨F, tr'⟩, (⟨F, { tr with cand := tr'.cand }⟩, simKemFailCand tr'))
    | .stepKemFailDeliver, (⟨F, tr⟩, (qB, j)) =>
      ⟨F, simStepKemFailDeliver F K tr (partyDec qB) j⟩
  cost := simOpCost cSpqrInit cSpqrSend cSpqrRecv cSpqrRecvPanics cSplitWireTag cParseWire
    cU32ToNat cToWire cEqWire cEqFig8C cInjOK cDh cEncT cDecT cIsZeroPt cKeyPairGen
    cFig8Init cFig8Send cFig8Recv cFsRecv cSentEval cSameWireFig8 cSnapSeed cKDecrypt
    cKemInit cKemSend cKemDeliver

/-- Unit-cost instantiation of `simParamOps` for `simDeliverForgeProg` and `kemFailRedProg`. -/
@[reducible] def simOpsUnitCost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512) :
    Ops (simSig PQ PQC Pt ℓ) :=
  simParamOps P Dh encPt encT decT lam K toKemCoins
    1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1

/-! ## Samplers, interfaces, and codecs -/

/-- Designated sampleable base sorts of `simSig` (`BitVec 256` and `PQC`). -/
inductive SimBaseSamp
  | bv256
  | pqc
  deriving DecidableEq

def simBaseSampSort : SimBaseSamp → SimSort
  | .bv256 => .bv256
  | .pqc => .pqc

instance instSampleableSimBaseSamp (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ) :
    ∀ b : SimBaseSamp, SampleableType ((simSig PQ PQC Pt ℓ).den (simBaseSampSort b))
  | .bv256 => inferInstanceAs (SampleableType (BitVec 256))
  | .pqc => inferInstanceAs (SampleableType PQC)

def simBaseSampCost (cSampBv256 cSampPqc : ℕ) : SimBaseSamp → ℕ
  | .bv256 => cSampBv256
  | .pqc => cSampPqc

/-- Parametric sampler table over `SimBaseSamp` for the session reductions. -/
@[reducible] def simParamSamplers (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ)
    (cSampBv256 cSampPqc : ℕ) :
    Samplers (simSig PQ PQC Pt ℓ) :=
  unifSamplers (S := simSig PQ PQC Pt ℓ) simBaseSampSort (simBaseSampCost cSampBv256 cSampPqc)

/-- Parametric target Fig. 8 `DeliverForge` oracle interface for `simDeliverForgeProg`. -/
@[reducible] def simParamIfaceDF (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ)
    (cQ cU cSampBv256 cSampPqc : ℕ) :
    Iface (simSig PQ PQC Pt ℓ)
      (unifSpec + SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) where
  fwdU n :=
    query
      (spec := unifSpec + SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
      (.inl n)
  uCost := cU
  Tag := SMTagDF
  dom := fun
    | .tr => .prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256)))
    | .ch =>
      .prod .bool
        (.prod (lpubPlainTy PQ PQC Pt ℓ)
          (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256))))
    | .dl => .prod .bool (fig8CTy PQ PQC Pt ℓ)
    | .ij => .prod .bool (fig8CTy PQ PQC Pt ℓ)
    | .cr => .bool
    | .df => .prod .bool (.prod (fig8CTy PQ PQC Pt ℓ) (fig8CTy PQ PQC Pt ℓ))
  cod := fun
    | .tr => .opt (fig8CTy PQ PQC Pt ℓ)
    | .ch => .opt (fig8CTy PQ PQC Pt ℓ)
    | .dl => .opt (fig8RrTy PQ PQC Pt ℓ)
    | .ij => .opt (fig8RrTy PQ PQC Pt ℓ)
    | .cr => .opt (.base .fig8st)
    | .df => .opt (fig8RrTy PQ PQC Pt ℓ)
  enc := fun
    | .tr, (p, m, r) => .inr (.inl (.inl (.inl (.inl (.inl (partyDec p, m, r))))))
    | .ch, (p, m₀, m₁, r) => .inr (.inl (.inl (.inl (.inl (.inr (partyDec p, m₀, m₁, r))))))
    | .dl, (p, c) => .inr (.inl (.inl (.inl (.inr (partyDec p, c)))))
    | .ij, (p, c) => .inr (.inl (.inl (.inr (partyDec p, c))))
    | .cr, p => .inr (.inl (.inr (partyDec p)))
    | .df, (p, c, c') => .inr (.inr (partyDec p, c, c'))
  dec := fun
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map smRrEnc
    | .ij, _, r => r.map smRrEnc
    | .cr, _, r => r
    | .df, _, r => r.map smRrEnc
  qCost := fun _ => cQ
  smp := simParamSamplers PQ PQC Pt ℓ cSampBv256 cSampPqc

/-- Unit-cost target Fig. 8 `DeliverForge` oracle interface for `simDeliverForgeProg`. -/
@[reducible] def simIfaceDF (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ) :
    Iface (simSig PQ PQC Pt ℓ)
      (unifSpec + SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) :=
  simParamIfaceDF PQ PQC Pt ℓ 1 1 1 1

/-- Parametric coin-only target interface (`unifSpec`) for `kemFailRedProg`. -/
@[reducible] def kemFailParamIface (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ)
    (cU cSampBv256 cSampPqc : ℕ) :
    Iface (simSig PQ PQC Pt ℓ) unifSpec where
  fwdU n := query (spec := unifSpec) n
  uCost := cU
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc := fun t => t.elim
  dec := fun t => t.elim
  qCost := Empty.elim
  smp := simParamSamplers PQ PQC Pt ℓ cSampBv256 cSampPqc

/-- Unit-cost coin-only target interface (`unifSpec`) for `kemFailRedProg`. -/
@[reducible] def kemFailIface (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ) :
    Iface (simSig PQ PQC Pt ℓ) unifSpec :=
  kemFailParamIface PQ PQC Pt ℓ 1 1 1

@[reducible] def simQ (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.prod .bool (.prod (.base .plain) (.opt (.base .pqc))))
          (.prod .bool (.prod (.base .plain) (.prod (.base .plain) (.opt (.base .pqc))))))
        (.prod .bool (.base .wire)))
      (.prod .bool (.base .wire)))
    .bool

@[reducible] def simR (PQ PQC Pt : Type) (ℓ : ℕ) : Ty (simSig PQ PQC Pt ℓ) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.opt (.base .wire))
          (.opt (.base .wire)))
        (.opt (simRrTy PQ PQC Pt ℓ)))
      (.opt (simRrTy PQ PQC Pt ℓ)))
    (.opt (.base .ghostSt))

/-- Source SM game codec for `SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))`. -/
@[reducible] def simCodec (PQ PQC Pt : Type) (ℓ : ℕ) :
    GameCodec (simSig PQ PQC Pt ℓ)
      (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) where
  Q := simQ PQ PQC Pt ℓ
  R := simR PQ PQC Pt ℓ
  qenc := fun
    | .inl (.inl (.inl (.inl (P, m, r)))) =>
      .inl (.inl (.inl (.inl (partyEnc P, m, r))))
    | .inl (.inl (.inl (.inr (P, m₀, m₁, r)))) =>
      .inl (.inl (.inl (.inr (partyEnc P, m₀, m₁, r))))
    | .inl (.inl (.inr (Q, w))) =>
      .inl (.inl (.inr (partyEnc Q, w)))
    | .inl (.inr (Q, w)) =>
      .inl (.inr (partyEnc Q, w))
    | .inr P =>
      .inr (partyEnc P)
  rdec := fun
    | .inl (.inl (.inl (.inl _))), .inl (.inl (.inl (.inl r))) => r
    | .inl (.inl (.inl (.inl _))), _ => none
    | .inl (.inl (.inl (.inr _))), .inl (.inl (.inl (.inr r))) => r
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inl (.inl (.inr r)) => r.map smRrDec
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inl (.inr r) => r.map smRrDec
    | .inl (.inr _), _ => none
    | .inr _, .inr r => r
    | .inr _, _ => none
  codecCost := 6

/-! ## Mirror bookkeeping expressions -/

section SharedStateAndBookkeeping

variable {PQ PQC Pt : Type} {ℓ : ℕ}

local notation "S" => simSig PQ PQC Pt ℓ

@[reducible] def simRecTy : Ty S := .prod posTy (.prod (.base .plain) (.base .wire))

def srecPos
    {O' : Ops S} {Γ} (r : Expr O' Γ simRecTy) : Expr O' Γ posTy := .fst r
def srecCt
    {O' : Ops S} {Γ} (r : Expr O' Γ simRecTy) : Expr O' Γ (.base .wire) := .snd (.snd r)

/-- Parametric mirror `GameState` type in `simSig` over record type `recT`. -/
@[reducible] def mirTy (recT : Ty S) : Ty S :=
  .prod .bool
    (.prod .bool
      (.prod (.prod .nat .nat)
        (.prod (.prod .nat .nat)
          (.prod (.opt .nat)
            (.prod (.list recT)
              (.prod (.list posTy)
                (.prod (.list posTy)
                  (.prod (.prod (.tbl .nat) (.tbl .nat))
                    (.prod (.list .nat)
                      (.list (.prod .bool .nat)))))))))))

@[reducible] def simMirTy : Ty S := mirTy simRecTy

def mB
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) : Expr O' Γ .bool := .fst s
def mWin
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) : Expr O' Γ .bool :=
  .fst (.snd s)
def mEpoch
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd s))
def mIdx
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd s)))
def mTL
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd s))))
def mTrans
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.list recT) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def mChall
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def mComp
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def mMaxAcc
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def mLeaks
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))
def mCorrs
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) :
    Expr O' Γ (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))

def mMk
    {recT : Ty S} {O' : Ops S} {Γ}
    (b win : Expr O' Γ .bool)
    (epoch idx : Expr O' Γ (.prod .nat .nat))
    (tL : Expr O' Γ (.opt .nat))
    (trans : Expr O' Γ (.list recT))
    (chall comp : Expr O' Γ (.list posTy))
    (maxAcc : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ (.list .nat))
    (corrs : Expr O' Γ (.list (.prod .bool .nat))) : Expr O' Γ (mirTy recT) :=
  .pair b
    (.pair win
      (.pair epoch
        (.pair idx
          (.pair tL
            (.pair trans
              (.pair chall
                (.pair comp
                  (.pair maxAcc
                    (.pair leaks corrs)))))))))

def mSetWin
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) (w : Expr O' Γ .bool) :
    Expr O' Γ (mirTy recT) :=
  .letE (.pair s w)
    (let s0 : Expr O' _ (mirTy recT) := .fst .v0
     let w0 : Expr O' _ .bool := .snd .v0
     mMk (mB s0) w0 (mEpoch s0) (mIdx s0) (mTL s0)
       (mTrans s0) (mChall s0) (mComp s0) (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

/-- `SimState PQ Pt ℓ` represented as a `ReductionDsl` type in `simSig`. -/
@[reducible] def simStateTy : Ty S :=
  .prod simMirTy
    (.prod (.prod (.base .pq) (.base .pq))
      (.prod (.prod (.base .u32) (.base .u32))
        (.prod .bool
          (.prod (.list (.prod (.base .wire) (fig8CTy PQ PQC Pt ℓ)))
            (.prod (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.list (ghostChainTy PQ PQC Pt ℓ)))
              (.prod .nat .bool))))))

def ssMir
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) : Expr O' Γ simMirTy := .fst s
def ssPq
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) :
    Expr O' Γ (.prod (.base .pq) (.base .pq)) := .fst (.snd s)
def ssPn
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) :
    Expr O' Γ (.prod (.base .u32) (.base .u32)) := .fst (.snd (.snd s))
def ssUnackA
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd s)))
def ssHonest
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) :
    Expr O' Γ (.list (.prod (.base .wire) (fig8CTy PQ PQC Pt ℓ))) :=
  .fst (.snd (.snd (.snd (.snd s))))
def ssChains
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) :
    Expr O' Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.list (ghostChainTy PQ PQC Pt ℓ))) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def ssAmb
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) : Expr O' Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def ssStopped
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) : Expr O' Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))

def ssMk
    {O' : Ops S} {Γ}
    (mir : Expr O' Γ simMirTy)
    (pq : Expr O' Γ (.prod (.base .pq) (.base .pq)))
    (pn : Expr O' Γ (.prod (.base .u32) (.base .u32)))
    (unackA : Expr O' Γ .bool)
    (honest : Expr O' Γ (.list (.prod (.base .wire) (fig8CTy PQ PQC Pt ℓ))))
    (chains :
      Expr O' Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.list (ghostChainTy PQ PQC Pt ℓ))))
    (amb : Expr O' Γ .nat)
    (stopped : Expr O' Γ .bool) : Expr O' Γ simStateTy :=
  .pair mir (.pair pq (.pair pn (.pair unackA (.pair honest (.pair chains (.pair amb stopped))))))

def ssSetAmb
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) (a : Expr O' Γ .nat) :
    Expr O' Γ simStateTy :=
  .letE (.pair s a)
    (let s0 : Expr O' _ simStateTy := .fst .v0
     ssMk (ssMir s0) (ssPq s0) (ssPn s0) (ssUnackA s0) (ssHonest s0) (ssChains s0)
       (.snd .v0) (ssStopped s0))

def ssSetMirWin
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) : Expr O' Γ simStateTy :=
  .letE s
    (let s0 : Expr O' _ simStateTy := .v0
     ssMk (mSetWin (ssMir s0) (.bool true)) (ssPq s0) (ssPn s0) (ssUnackA s0)
       (ssHonest s0) (ssChains s0) (ssAmb s0) (ssStopped s0))

def ssSetMir
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) (m : Expr O' Γ simMirTy) :
    Expr O' Γ simStateTy :=
  .letE (.pair s m)
    (let s0 : Expr O' _ simStateTy := .fst .v0
     ssMk (.snd .v0) (ssPq s0) (ssPn s0) (ssUnackA s0) (ssHonest s0) (ssChains s0)
       (ssAmb s0) (ssStopped s0))

def mSafeChE
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (healedByE (mTL (.fst .v0)) 3 (pGet (mEpoch (.fst .v0)) (.snd .v0)))

def mSafeInjE
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) : Expr O' Γ .bool :=
  .letE s
    (healedByE (mTL .v0) 3 (minN (.fst (mEpoch .v0)) (.snd (mEpoch .v0))))

def mLeakE
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) (l : Expr O' Γ .nat) :
    Expr O' Γ (mirTy recT) :=
  .letE (.pair s l)
    (let s0 : Expr O' _ (mirTy recT) := .fst .v0
     let m : Expr O' _ .nat := maxOptE (mTL s0) (.snd .v0)
     mMk (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (.some m)
       (mTrans s0) (mChall s0) (mComp s0) (mMaxAcc s0)
       (.cons m (mLeaks s0)) (mCorrs s0))

def mEpMgmtE
    {recT : Ty S} {O' : Ops S} {Γ} (qep : ℕ) (s : Expr O' Γ (mirTy recT)) (p : Expr O' Γ .bool)
    (bad : Expr O' Γ .bool) : Expr O' Γ (.opt (mirTy recT)) :=
  .letE (.pair s (.pair p bad))
    (let s0 : Expr O' _ (mirTy recT) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let bad0 : Expr O' _ .bool := .snd (.snd .v0)
     let epP : Expr O' _ .nat := pGet (mEpoch s0) p0
     let epNext : Expr O' _ .nat := .add epP (.nat 1)
     .ite (sendsInE p0 epNext)
       (.ite (.lt (.nat qep) epNext)
         .none
         (.letE (.ite (.and bad0 (.not (mSafeChE s0 p0))) (mLeakE s0 epNext) s0)
           (let s1 : Expr O' _ (mirTy recT) := .v0
            let p1 : Expr O' _ .bool := .fst (.snd .v1)
            let ep1 : Expr O' _ .nat := .add (pGet (mEpoch s1) p1) (.nat 1)
            .some (mMk (mB s1) (mWin s1)
              (pSet (mEpoch s1) p1 ep1)
              (pSet (mIdx s1) p1 (.nat 0))
              (mTL s1) (mTrans s1) (mChall s1) (mComp s1)
              (mMaxAcc s1) (mLeaks s1) (mCorrs s1)))))
       (.ite (.lt (.nat qep) epP)
         .none
         (.some s0)))

def mRecordE
    {restT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy (.prod posTy restT)))
    (p : Expr O' Γ .bool) (r : Expr O' Γ (.prod posTy restT)) (isChall : Expr O' Γ .bool) :
    Expr O' Γ (mirTy (.prod posTy restT)) :=
  .letE (.pair s (.pair p (.pair r isChall)))
    (let s0 : Expr O' _ (mirTy (.prod posTy restT)) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let r0 : Expr O' _ (.prod posTy restT) := .fst (.snd (.snd .v0))
     let ch0 : Expr O' _ .bool := .snd (.snd (.snd .v0))
     let pos : Expr O' _ posTy := .fst r0
     mMk (mB s0) (mWin s0) (mEpoch s0)
       (pSet (mIdx s0) p0 (posIdx pos))
       (mTL s0)
       (.cons r0 (mTrans s0))
       (.ite ch0 (.cons pos (mChall s0)) (mChall s0))
       (.ite (mSafeChE s0 p0) (mComp s0) (.cons pos (mComp s0)))
       (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

def mDeleteE
    {restT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy (.prod posTy restT)))
    (pos : Expr O' Γ posTy) : Expr O' Γ (mirTy (.prod posTy restT)) :=
  .letE (.pair s pos)
    (let s0 : Expr O' _ (mirTy (.prod posTy restT)) := .fst .v0
     let trans' : Expr O' _ (.list (.prod posTy restT)) :=
       .foldrB K (mTrans s0) .nil
         (.ite (.not (posEq (.fst .v0) (.snd .v2))) (.cons .v0 .v1) .v1)
     let chall' : Expr O' _ (.list posTy) :=
       .foldrB K (mChall s0) .nil
         (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)
     let comp' : Expr O' _ (.list posTy) :=
       .foldrB K (mComp s0) .nil
         (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)
     mMk (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (mTL s0)
       trans' chall' comp' (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

def mAcceptE
    {restT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy (.prod posTy restT)))
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) : Expr O' Γ (mirTy (.prod posTy restT)) :=
  .letE (.pair (mDeleteE K s pos) (.pair p pos))
    (let s1 : Expr O' _ (mirTy (.prod posTy restT)) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let pos0 : Expr O' _ posTy := .snd (.snd .v0)
     let pEpoch : Expr O' _ .nat := posEpoch pos0
     let pIdx : Expr O' _ .nat := posIdx pos0
     mMk (mB s1) (mWin s1)
       (pSet (mEpoch s1) p0 (maxN (pGet (mEpoch s1) p0) pEpoch))
       (mIdx s1) (mTL s1) (mTrans s1) (mChall s1) (mComp s1)
       (maxAccSet (mMaxAcc s1) p0 pEpoch
         (maxN (maxAccGet (mMaxAcc s1) p0 pEpoch) pIdx))
       (mLeaks s1) (mCorrs s1))

def mCompContainsE
    {recT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy recT))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair s pos)
    (.anyB K (mComp (.fst .v0)) (posEq .v0 (.snd .v1)))

def mChallContainsE
    {recT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy recT))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair s pos)
    (.anyB K (mChall (.fst .v0)) (posEq .v0 (.snd .v1)))

def mTrivialE
    {restT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy (.prod posTy restT)))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair s pos)
    (let s0 : Expr O' _ (mirTy (.prod posTy restT)) := .fst .v0
     let pos0 : Expr O' _ posTy := .snd .v0
     orE (mCompContainsE K s0 pos0)
       (.and
         (.not (.anyB K (mTrans s0) (posEq (.fst .v0) (.snd .v1))))
         (.not (healedByE (mTL s0) 3 (posEpoch pos0)))))

def mCorrAllowedE
    {restT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy (.prod posTy restT)))
    (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .letE (.pair s p)
    (let s0 : Expr O' _ (mirTy (.prod posTy restT)) := .fst .v0
     .and
       (.not (.anyB K (mChall s0) (boolEq (posSender .v0) (otherE (.snd .v1)))))
       (.not (.anyB K (mTrans s0)
         (.and (boolEq (posSender (.fst .v0)) (otherE (.snd .v1)))
           (.not (mCompContainsE K (.fst .v1) (.fst .v0)))))))

def mAfterCorrE
    {restT : Ty S} {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ (mirTy (.prod posTy restT)))
    (p : Expr O' Γ .bool) : Expr O' Γ (mirTy (.prod posTy restT)) :=
  .letE (.pair s p)
    (let s0 : Expr O' _ (mirTy (.prod posTy restT)) := .fst .v0
     let p0 : Expr O' _ .bool := .snd .v0
     let comp' : Expr O' _ (.list posTy) :=
       .foldrB K (mTrans s0) (mComp s0)
         (.ite (.and (boolEq (posSender (.fst .v0)) (otherE (.snd .v2)))
                     (.not (.anyB K .v1 (posEq .v0 (.fst .v1)))))
           (.cons (.fst .v0) .v1)
           .v1)
     let s1 : Expr O' _ (mirTy (.prod posTy restT)) :=
       mMk (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (mTL s0)
         (mTrans s0) (mChall s0) comp' (mMaxAcc s0) (mLeaks s0) (mCorrs s0)
     let s2 : Expr O' _ (mirTy (.prod posTy restT)) :=
       mLeakE s1 (maxN (.fst (mEpoch s0)) (.snd (mEpoch s0)))
     mMk (mB s2) (mWin s2) (mEpoch s2) (mIdx s2) (mTL s2)
       (mTrans s2) (mChall s2) (mComp s2) (mMaxAcc s2) (mLeaks s2)
       (.cons (.pair p0 (pGet (mEpoch s0) p0)) (mCorrs s2)))

def mInWinE
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (.not (sendsInE (.snd .v0) (pGet (mEpoch (.fst .v0)) (.snd .v0))))

def mNoBobEpoch0E
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (.not (.and (.snd .v0) (.eqN (.snd (mEpoch (.fst .v0))) (.nat 0))))

def mNoSpkCorrE
    {recT : Ty S} {O' : Ops S} {Γ} (s : Expr O' Γ (mirTy recT)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (.not (.and (.not (.snd .v0)) (.lt (.fst (mEpoch (.fst .v0))) (.nat 10))))

def initSimMirE
    {recT : Ty S} {O' : Ops S} {Γ} : Expr O' Γ (mirTy recT) :=
  mMk (.bool false) (.bool false) (.pair (.nat 0) (.nat 0)) (.pair (.nat 0) (.nat 0))
    .none .nil .nil .nil (.pair (.tconst (.nat 0)) (.tconst (.nat 0))) .nil .nil

end SharedStateAndBookkeeping

/-! ## Decision-C state and costed reductions -/

section SimCProgs

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (toKemCoins : PQC → BitVec 512)

local notation "S" => simSig PQ PQC Pt ℓ
local notation "OFig" => simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K toKemCoins

/-- `ReductionDsl` representation of `LibsignalSimC.Kept Pt`. -/
@[reducible] def keptTy : Ty S :=
  .prod (.opt (.base .fig8st))
    (.prod (.opt (.base .fig8st)) (.tbl (.opt (.opt (.base .vrSt)))))

@[reducible] def snapEntryTy : Ty S :=
  .prod .bool (.prod .nat (.base .ghostSt))

/-- `LibsignalToModularSchemeSimState PQ Pt ℓ` represented as a `ReductionDsl` type in `simSig`. -/
@[reducible] def simStateCTy : Ty S :=
  .prod simStateTy
    (.prod (.prod keptTy keptTy)
      (.prod (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt)))
        (.list snapEntryTy)))

def scBase {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) : Expr O' Γ simStateTy := .fst sC
def scKept {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) :
    Expr O' Γ (.prod keptTy keptTy) := .fst (.snd sC)
def scSent {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) :
    Expr O' Γ (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt))) := .fst (.snd (.snd sC))
def scSnaps {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) :
    Expr O' Γ (.list snapEntryTy) := .snd (.snd (.snd sC))

def scMk {O' : Ops S} {Γ}
    (base : Expr O' Γ simStateTy)
    (kept : Expr O' Γ (.prod keptTy keptTy))
    (sent : Expr O' Γ (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt))))
    (snaps : Expr O' Γ (.list snapEntryTy)) : Expr O' Γ simStateCTy :=
  .pair base (.pair kept (.pair sent snaps))

def scSetBase {O' : Ops S} {Γ} (sC : Expr O' Γ simStateCTy) (b : Expr O' Γ simStateTy) :
    Expr O' Γ simStateCTy :=
  .letE (.pair sC b)
    (let s0 : Expr O' _ simStateCTy := .fst .v0
     scMk (.snd .v0) (scKept s0) (scSent s0) (scSnaps s0))

def keptUnknownE {O' : Ops S} {Γ} : Expr O' Γ keptTy :=
  .pair .none (.pair .none (.tconst .none))

def keptOfStE {O' : Ops S} {Γ} (st : Expr O' Γ (.base .fig8st)) : Expr O' Γ keptTy :=
  .letE st (.pair (.some .v0) (.pair (.some .v0) (.tconst .none)))

def keptRsAtE {Γ} (k : Expr OFig Γ keptTy) (t : Expr OFig Γ .nat) :
    Expr OFig Γ (.opt (.base .vrSt)) :=
  .letE (.pair k t)
    (let k0 : Expr OFig _ keptTy := .fst .v0
     let t0 : Expr OFig _ .nat := .snd .v0
     .caseOpt (.tget (.snd (.snd k0)) t0)
       (.caseOpt (.fst (.snd k0))
         .none
         (Expr.op (O := OFig) SimOp.fig8VR (.pair .v0 (.snd .v1))))
       .v0)

def keptSendE (B : ℕ) {Γ} (k : Expr OFig Γ keptTy) : Expr OFig Γ keptTy :=
  .letE k
    (let k0 : Expr OFig _ keptTy := .v0
     .caseOpt (.fst k0)
       k0
       (let st0 : Expr OFig _ (.base .fig8st) := .v0
        let step : Expr OFig _ (.prod .bool (.prod (.base .fig8st) (fig8CTy PQ PQC Pt ℓ))) :=
          Expr.op (O := OFig) (SimOp.fig8SendStep B) (.pair st0 .none)
        .ite (.fst step)
          (.pair .none (.pair (.some st0) (.tconst .none)))
          (.pair (.some (.fst (.snd step))) (.snd .v1))))

def keptRecvE (B : ℕ) {Γ} (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (k : Expr OFig Γ keptTy) :
    Expr OFig Γ keptTy :=
  .letE (.pair c k)
    (let c0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .fst .v0
     let k0 : Expr OFig _ keptTy := .snd .v0
     .caseOpt (.fst k0)
       (let t0 : Expr OFig _ .nat := .fst (.fst c0)
        let v? : Expr OFig _ (.opt (.base .vrSt)) :=
          keptRsAtE P Dh encPt encT decT lam K toKemCoins k0 t0
        let v' : Expr OFig _ (.opt (.base .vrSt)) :=
          .caseOpt v?
            .none
            (.caseOpt (Expr.op (O := OFig) (SimOp.fsReceive B) (.pair .v0 (.fst .v1)))
              .none
              (.some (.fst .v0)))
        .pair .none (.pair (.fst (.snd k0)) (.tset (.snd (.snd k0)) t0 (.some v'))))
       (.caseOpt (Expr.op (O := OFig) (SimOp.fig8Receive B) (.pair .v0 (.fst .v1)))
         (.pair .none (.pair (.some .v0) (.tconst .none)))
         (.pair (.some (.fst .v0)) (.snd (.snd .v2)))))

def keptEvalE (B : ℕ) {Γ} (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) (k : Expr OFig Γ keptTy) :
    Expr OFig Γ (.opt (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :=
  .letE (.pair c k)
    (let c0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .fst .v0
     let k0 : Expr OFig _ keptTy := .snd .v0
     .caseOpt (.fst k0)
       (let t0 : Expr OFig _ .nat := .fst (.fst c0)
        .caseOpt (keptRsAtE P Dh encPt encT decT lam K toKemCoins k0 t0)
          .none
          (.some
            (.caseOpt (Expr.op (O := OFig) (SimOp.fsReceive B) (.pair .v0 (.fst .v1)))
              .none
              (.some (.pair (.fst (.fst (.fst .v2))) (.snd .v0))))))
       (.some
         (.caseOpt (Expr.op (O := OFig) (SimOp.fig8Receive B) (.pair .v0 (.fst .v1)))
           .none
           (.some (.snd .v0)))))

def sentEvalE (L B : ℕ) {Γ}
    (sent : Expr OFig Γ (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt))))
    (c c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Expr OFig Γ (.opt (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :=
  .letE (.pair sent (.pair c c'))
    (.caseOpt
      (.findB L (.fst .v0)
        (Expr.op (O := OFig) SimOp.eqFig8C (.pair (.fst .v0) (.fst (.snd .v1)))))
      .none
      (let v0 : Expr OFig _ (.base .vsSt) := .snd .v0
       let c'1 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.snd .v1)
       let vr0 : Expr OFig _ (.base .vrSt) := Expr.op (O := OFig) SimOp.senderToFreshVr v0
       .some
         (.caseOpt (Expr.op (O := OFig) (SimOp.fsReceive B) (.pair vr0 c'1))
           .none
           (.some (.pair (.fst (.fst (.snd (.snd .v2)))) (.snd .v0))))))

def orElseOptE {O' : Ops S} {Γ α} (x y : Expr O' Γ (.opt α)) : Expr O' Γ (.opt α) :=
  .caseOpt x y (.some .v0)

def knownSeedRE (L : ℕ) {Γ} (snaps : Expr OFig Γ (.list snapEntryTy))
    (qB : Expr OFig Γ .bool) (t : Expr OFig Γ .nat) (w : Expr OFig Γ (.base .wire)) :
    Expr OFig Γ (.opt (.base .wire)) :=
  .letE (.pair snaps (.pair qB (.pair t w)))
    (let sn0 : Expr OFig _ (.list snapEntryTy) := .fst .v0
     let branchScan (br : ℕ) : Expr OFig _ (.opt (.base .wire)) :=
       .foldrB L sn0 .none
         (.caseOpt
           (Expr.op (O := OFig) SimOp.snapSeed
             (.pair (.nat br)
               (.pair (.fst (.snd .v2))
                 (.pair (.snd (.snd (.snd .v2)))
                   (.pair (.fst (.snd (.snd .v2))) (.pair .v0 .none))))))
           .v1
           (.some .v0))
     let k4CurScan : Expr OFig _ (.opt snapEntryTy) :=
       .foldrB L sn0 .none
         (.caseOpt
           (Expr.op (O := OFig) SimOp.snapSeed
             (.pair (.nat 4)
               (.pair (.fst (.snd .v2))
                 (.pair (.snd (.snd (.snd .v2)))
                   (.pair (.fst (.snd (.snd .v2))) (.pair .v0 .none))))))
           .v1
           (.some .v1))
     let k4Scan : Expr OFig _ (.opt (.base .wire)) :=
       .caseOpt k4CurScan .none
         (.foldrB L (.fst .v1) .none
           (.caseOpt
             (Expr.op (O := OFig) SimOp.snapSeed
               (.pair (.nat 3)
                 (.pair (.fst (.snd .v3))
                   (.pair (.snd (.snd (.snd .v3)))
                     (.pair (.fst (.snd (.snd .v3)))
                       (.pair .v2 (.some .v0)))))))
             .v1
             (.some .v0)))
     orElseOptE (branchScan 0)
       (orElseOptE (branchScan 1)
         (orElseOptE (branchScan 2) k4Scan)))

def evalCKE (L B : ℕ) {Γ} (sC : Expr OFig Γ simStateCTy) (qB : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (c c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Expr OFig Γ (.opt (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :=
  .letE (.pair sC (.pair qB (.pair w (.pair c c'))))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let q0 : Expr OFig _ .bool := .fst (.snd .v0)
     let w0 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v0))
     let c0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .fst (.snd (.snd (.snd .v0)))
     let c'0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.snd (.snd (.snd .v0)))
     let kEval : Expr OFig _ (.opt (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :=
       keptEvalE P Dh encPt encT decT lam K toKemCoins B c'0 (pGet (scKept sC0) q0)
     let sEval : Expr OFig _ (.opt (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :=
       sentEvalE P Dh encPt encT decT lam K toKemCoins L B (scSent sC0) c0 c'0
     let ksEval : Expr OFig _ (.opt (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :=
       .caseOpt
         (knownSeedRE P Dh encPt encT decT lam K toKemCoins L (scSnaps sC0) q0
           (.fst (.fst c0)) w0)
         .none
         (.some
           (Expr.op (O := OFig) (SimOp.kDecryptFig8 B)
             (.pair (.fst (.snd .v1))
               (.pair (.fst (.snd (.snd .v1)))
                 (.pair (.snd (.snd (.snd (.snd .v1)))) .v0)))))
     orElseOptE kEval (orElseOptE sEval ksEval))

def mInTransitFigE (L : ℕ) {Γ} (s : Expr OFig Γ simMirTy)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire)) :
    Expr OFig Γ (.opt simRecTy) :=
  .letE (.pair s (.pair qParty w))
    (.findB L (mTrans (.fst .v0))
      (.and (boolEq (posSender (srecPos .v0)) (.fst (.snd .v1)))
        (Expr.op (O := OFig) SimOp.eqWire (.pair (srecCt .v0) (.snd (.snd .v1))))))

def initChainAFigE {Γ} : Expr OFig Γ (ghostChainTy PQ PQC Pt ℓ) :=
  .pair .none (.pair (.nat 0) (Expr.op (O := OFig) SimOp.emptyChainSt .unit))

def hasUnknownKeyFigE {Γ}
    (cs : Expr OFig Γ (.list (ghostChainTy PQ PQC Pt ℓ))) : Expr OFig Γ .bool :=
  .anyB 5 cs (.caseOpt (.fst .v0) (.bool true) (.bool false))

def findChainFigE {Γ}
    (arg : Expr OFig Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .pk))) :
    Expr OFig Γ (.opt (.prod .nat (ghostChainTy PQ PQC Pt ℓ))) :=
  .letE arg
    (.foldrB 5 (.fst .v0) .none
      (.ite
        (.caseOpt (.fst .v0) (.bool false)
          (Expr.op (O := OFig) SimOp.eqPk (.pair .v0 (.snd .v3))))
        (.some (.pair (.nat 0) .v0))
        (.caseOpt .v1 .none
          (.some (.pair (.add (.fst .v0) (.nat 1)) (.snd .v0))))))

def modifyChainAcceptFigE {Γ}
    (arg : Expr OFig Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod .nat .nat))) :
    Expr OFig Γ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
  .letE arg
    (.foldrB 5 (.fst .v0) .nil
      (.cons
        (.ite (.eqN (.add (.len .v1) (.add (.fst (.snd .v2)) (.nat 1))) (.len (.fst .v2)))
          (.pair (.fst .v0)
            (.pair (.fst (.snd .v0))
              (Expr.op (O := OFig) SimOp.chainAccept (.pair (.snd (.snd .v0)) (.snd (.snd .v2))))))
          .v0)
        .v1))

def pushChainFigE {Γ}
    (arg : Expr OFig Γ
      (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.prod (.base .pk) (.prod .nat .nat)))) :
    Expr OFig Γ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
  .letE arg
    (let cs0 : Expr OFig _ (.list (ghostChainTy PQ PQC Pt ℓ)) := .fst .v0
     let T0 : Expr OFig _ (.base .pk) := .fst (.snd .v0)
     let t0 : Expr OFig _ .nat := .fst (.snd (.snd .v0))
     let i0 : Expr OFig _ .nat := .snd (.snd (.snd .v0))
     let g : Expr OFig _ (ghostChainTy PQ PQC Pt ℓ) :=
       .pair (.some T0)
         (.pair t0
           (Expr.op (O := OFig) SimOp.chainAccept
             (.pair (Expr.op (O := OFig) SimOp.emptyChainSt .unit) i0)))
     .foldrB 5 cs0 (.cons g .nil)
       (.ite (.lt (.len .v1) (.nat 5)) (.cons .v0 .v1) .v1))

def revealSpkChainsFigE {Γ}
    (arg : Expr OFig Γ (.prod (.list (ghostChainTy PQ PQC Pt ℓ)) (.base .fig8st))) :
    Expr OFig Γ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
  .letE arg
    (.caseOpt (Expr.op (O := OFig) SimOp.fig8GammaExp (.snd .v0))
      (.fst .v0)
      (.mapB 5 (.fst .v1)
        (.caseOpt (.fst .v0)
          (.pair
            (.some
              (Expr.op (O := OFig) SimOp.encT
                (Expr.op (O := OFig) SimOp.dh
                  (.pair .v1 (Expr.op (O := OFig) SimOp.dhBase .unit)))))
            (.snd .v0))
          .v1)))

def spqrSendPubFigE {Γ}
    (arg : Expr OFig Γ
      (.prod .bool (.prod .bool (.prod (.base .pq) (.prod (.base .pqc) (.base .u32)))))) :
    Expr OFig Γ (.opt (.prod (.base .pq) (.base .lpub))) :=
  .letE arg
    (let pq : Expr OFig _ (.base .pq) := .fst (.snd (.snd .v0))
     let rq : Expr OFig _ (.base .pqc) := .fst (.snd (.snd (.snd .v0)))
     .caseOpt (Expr.op (O := OFig) SimOp.spqrSend (.pair pq rq))
       .none
       (let pq' : Expr OFig _ (.base .pq) := .fst .v0
        let salt? : Expr OFig _ (.opt (.base .salt32)) := .fst (.snd .v0)
        let pqm : Expr OFig _ (.base .wire) := .snd (.snd .v0)
        let qB1 : Expr OFig _ .bool := .fst .v1
        let unackA1 : Expr OFig _ .bool := .fst (.snd .v1)
        let pn1 : Expr OFig _ (.base .u32) := .snd (.snd (.snd (.snd .v1)))
        let addr : Expr OFig _ (.opt (.base .wire)) :=
          .ite (.and (.not qB1) unackA1) (Expr.op (O := OFig) SimOp.addrAB .unit) .none
        .some
          (.pair pq'
            (Expr.op (O := OFig) SimOp.mkLPub
              (.pair pn1
                (.pair pqm
                  (.pair (Expr.op (O := OFig) SimOp.effectiveHkdfSalt32 salt?) addr)))))))

def parseRecvFigCE (B : ℕ) {Γ}
    (arg : Expr OFig Γ (.prod .bool (.prod (.base .pq) (.base .wire)))) :
    Expr OFig Γ
      (.opt (.prod (.base .pq)
        (.prod .nat (.prod (.base .pk) (.prod (.opt (.base .pt)) (.base .lct)))))) :=
  .letE arg
    (.caseOpt (Expr.op (O := OFig) SimOp.splitWireTag (.snd (.snd .v0)))
      .none
      (.caseOpt (Expr.op (O := OFig) SimOp.parseWire (.fst .v0))
        .none
        (let addrs : Expr OFig _ (.opt (.base .wire)) := .snd (.snd (.snd .v0))
         let qB2 : Expr OFig _ .bool := .fst .v2
         let pq2 : Expr OFig _ (.base .pq) := .fst (.snd .v2)
         let pqm0 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v0))
         .ite
           (.and
             (.ite qB2
               (Expr.op (O := OFig) SimOp.addrsOkB addrs)
               (Expr.op (O := OFig) SimOp.addrsOkA addrs))
             (.not (Expr.op (O := OFig) SimOp.spqrRecvPanics (.pair pq2 pqm0))))
           (.caseOpt (Expr.op (O := OFig) SimOp.spqrRecv (.pair pq2 pqm0))
             .none
             (let pq' : Expr OFig _ (.base .pq) := .fst .v0
              let salt? : Expr OFig _ (.opt (.base .salt32)) := .snd .v0
              let srk : Expr OFig _ (.base .pk) := .fst .v1
              let cnt : Expr OFig _ (.base .u32) := .fst (.snd .v1)
              let serTag : Expr OFig _ (.prod (.base .wire) (.base .bv64)) := .v2
              .some
                (.pair pq'
                  (.pair (Expr.op (O := OFig) (SimOp.u32IncToNat B) cnt)
                    (.pair srk
                      (.pair (Expr.op (O := OFig) SimOp.decT srk)
                        (Expr.op (O := OFig) SimOp.mkLCt
                          (.pair cnt
                            (.pair serTag
                              (Expr.op (O := OFig) SimOp.effectiveHkdfSalt32 salt?))))))))))
           .none)))

def toGhostFigE {Γ}
    (arg : Expr OFig Γ
      (.prod .bool
        (.prod (.base .fig8st)
          (.prod (.base .u32)
            (.prod (.list (ghostChainTy PQ PQC Pt ℓ))
              (.prod .bool (.prod (.base .pq) .nat))))))) :
    Expr OFig Γ (.base .ghostSt) :=
  .letE arg
    (let qB : Expr OFig _ .bool := .fst .v0
     let st : Expr OFig _ (.base .fig8st) := .fst (.snd .v0)
     let pn : Expr OFig _ (.base .u32) := .fst (.snd (.snd .v0))
     let cs : Expr OFig _ (.list (ghostChainTy PQ PQC Pt ℓ)) := .fst (.snd (.snd (.snd .v0)))
     let unackA : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v0))))
     let pq : Expr OFig _ (.base .pq) := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let ep : Expr OFig _ .nat := .snd (.snd (.snd (.snd (.snd (.snd .v0)))))
     let sender : Expr OFig _ (.opt (.base .senderChain)) :=
       .caseOpt (Expr.op (O := OFig) SimOp.fig8GammaExp st)
         .none
         (.caseOpt (Expr.op (O := OFig) SimOp.fig8VS (.fst (.snd .v1)))
           .none
           (.some
             (Expr.op (O := OFig) SimOp.mkSenderChain
               (.pair (Expr.op (O := OFig) SimOp.keyPairGen .v1) .v0))))
     let rcs : Expr OFig _ (.list (.base .recvChain)) :=
       .mapB 5 cs
         (Expr.op (O := OFig) SimOp.mkRecvChain
           (.pair (.fst .v0)
             (.pair (.snd (.snd .v0))
               (Expr.op (O := OFig) SimOp.fig8VR
                 (.pair (.fst (.snd .v1)) (.fst (.snd .v0)))))))
     let eps : Expr OFig _ (.list .nat) :=
       .mapB 5 cs (.fst (.snd .v0))
     Expr.op (O := OFig) SimOp.mkGhostState
       (.pair qB
         (.pair (Expr.op (O := OFig) SimOp.fig8Root st)
           (.pair pn
             (.pair sender
               (.pair rcs
                 (.pair (.and (.not qB) unackA)
                   (.pair pq (.pair ep eps)))))))))

def inTFigE (L : ℕ) {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) : Expr OFig Γ .bool :=
  .letE (.pair s (.pair qParty c))
    (.anyB L (ssHonest (.fst .v0))
      (.and
        (Expr.op (O := OFig) SimOp.eqFig8C (.pair (.snd .v0) (.snd (.snd .v1))))
        (isSomeE (mInTransitFigE P Dh encPt encT decT lam K toKemCoins
          L (ssMir (.fst .v1)) (otherE (.fst (.snd .v1))) (.fst .v0)))))

def onAcceptPreFigE {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (t i : Expr OFig Γ .nat) (ciOpt : Expr OFig Γ (.opt .nat))
    (T : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq)) :
    Expr OFig Γ simStateTy :=
  .letE (.pair s (.pair qParty (.pair t (.pair i (.pair ciOpt (.pair T pq'))))))
    (let s0 : Expr OFig _ simStateTy := .fst .v0
     let q0 : Expr OFig _ .bool := .fst (.snd .v0)
     let t0 : Expr OFig _ .nat := .fst (.snd (.snd .v0))
     let i0 : Expr OFig _ .nat := .fst (.snd (.snd (.snd .v0)))
     let ci0 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd .v0))))
     let T0 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let pq0 : Expr OFig _ (.base .pq) := .snd (.snd (.snd (.snd (.snd (.snd .v0)))))
     let cs : Expr OFig _ (.list (ghostChainTy PQ PQC Pt ℓ)) :=
       .caseOpt ci0
         (pushChainFigE P Dh encPt encT decT lam K toKemCoins
           (.pair (pGet (ssChains s0) q0) (.pair T0 (.pair t0 i0))))
         (modifyChainAcceptFigE P Dh encPt encT decT lam K toKemCoins
           (.pair (pGet (ssChains (.fst .v1)) (.fst (.snd .v1)))
             (.pair .v0 (.fst (.snd (.snd (.snd .v1)))))))
     ssMk (ssMir s0) (pSet (ssPq s0) q0 pq0) (ssPn s0) (.and (ssUnackA s0) q0)
       (ssHonest s0) (pSet (ssChains s0) q0 cs) (ssAmb s0) (ssStopped s0))

def onAcceptFigE (L qep : ℕ) {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (isDel : Expr OFig Γ .bool)
    (t i : Expr OFig Γ .nat) (m : Expr OFig Γ (.base .plain))
    (ciOpt : Expr OFig Γ (.opt .nat)) (T : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) :
    Expr OFig Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  .letE (.pair s (.pair (onAcceptPreFigE P Dh encPt encT decT lam K toKemCoins
      s qParty t i ciOpt T pq')
      (.pair qParty (.pair w (.pair isDel (.pair t (.pair i m)))))))
    (let s0 : Expr OFig _ simStateTy := .fst .v0
     let s'0 : Expr OFig _ simStateTy := .fst (.snd .v0)
     let q0 : Expr OFig _ .bool := .fst (.snd (.snd .v0))
     let w0 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v0)))
     let del0 : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v0))))
     let t0 : Expr OFig _ .nat := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let i0 : Expr OFig _ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let m0 : Expr OFig _ (.base .plain) := .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     .ite del0
       (.caseOpt (mInTransitFigE P Dh encPt encT decT lam K toKemCoins
           L (ssMir s0) (otherE q0) w0)
         (.pair .none s0)
         (let rPos : Expr OFig _ posTy := srecPos .v0
          let s0_1 : Expr OFig _ simStateTy := .fst .v1
          let s'1 : Expr OFig _ simStateTy := .fst (.snd .v1)
          let q0_1 : Expr OFig _ .bool := .fst (.snd (.snd .v1))
          let t0_1 : Expr OFig _ .nat := .fst (.snd (.snd (.snd (.snd (.snd .v1)))))
          let i0_1 : Expr OFig _ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))
          let m0_1 : Expr OFig _ (.base .plain) :=
            .snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))
          let mOut : Expr OFig _ (.opt (.base .plain)) :=
            .ite (mChallContainsE L (ssMir s0_1) rPos) .none (.some m0_1)
          .pair (.some (.inr (.pair t0_1 (.pair i0_1 mOut))))
            (ssSetMir s'1 (mAcceptE L (ssMir s0_1) q0_1 rPos))))
       (.ite (.lt (.nat (qep + 1)) t0)
         (.pair (.some (.inl .unit)) s0)
         (let pos : Expr OFig _ posTy := .pair (otherE q0) (.pair t0 i0)
          .ite (mTrivialE L (ssMir s0) pos)
            (.pair (.some (.inr (.pair t0 (.pair i0 (.some m0)))))
              (ssSetMir s'0 (mAcceptE L (ssMir s0) q0 pos)))
            (.pair (.some (.inl .unit)) (ssSetMirWin s0)))))

def onAnswerFigE (L qep : ℕ) {Γ}
    (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) (isDel : Expr OFig Γ .bool)
    (ciOpt : Expr OFig Γ (.opt .nat)) (T : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq))
    (res : Expr OFig Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) :
    Expr OFig Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
  .letE (.pair s (.pair qParty (.pair w (.pair isDel (.pair ciOpt (.pair T (.pair pq' res)))))))
    (let s0 : Expr OFig _ simStateTy := .fst .v0
     let res0 : Expr OFig _ (.opt (fig8RrTy PQ PQC Pt ℓ)) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     .caseOpt res0
       (.pair (.some (.inl .unit)) s0)
       (.caseSum .v0
         (.pair (.some (.inl .unit)) (.fst .v2))
         (let t : Expr OFig _ .nat := .fst .v0
          let i : Expr OFig _ .nat := .fst (.snd .v0)
          let pm : Expr OFig _ (.opt (.prod (.base .lpub) (.base .plain))) := .snd (.snd .v0)
          let m : Expr OFig _ (.base .plain) :=
            .caseOpt pm (Expr.op (O := OFig) SimOp.defaultPlain .unit) (.snd .v0)
          let s2 : Expr OFig _ simStateTy := .fst .v2
          let q2 : Expr OFig _ .bool := .fst (.snd .v2)
          let w2 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v2))
          let del2 : Expr OFig _ .bool := .fst (.snd (.snd (.snd .v2)))
          let ci2 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd .v2))))
          let T2 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd .v2)))))
          let pq2 : Expr OFig _ (.base .pq) := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
          onAcceptFigE P Dh encPt encT decT lam K toKemCoins L qep
            s2 q2 w2 del2 t i m ci2 T2 pq2)))

def honestCFigE (L : ℕ) {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (w : Expr OFig Γ (.base .wire)) : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)) :=
  .letE (.pair s (.pair qParty w))
    (.caseOpt
      (.findB L (ssHonest (.fst .v0))
        (.and
          (Expr.op (O := OFig) SimOp.eqWire (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v1))))))
      .none
      (.some (.snd .v0)))

def mkCFigE {Γ} (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (lct : Expr OFig Γ (.base .lct)) (t : Expr OFig Γ .nat) (T? : Expr OFig Γ (.opt (.base .pt))) :
    Expr OFig Γ (fig8CTy PQ PQC Pt ℓ) :=
  .letE (.pair honestC (.pair lct (.pair t T?)))
    (let hc : Expr OFig _ (.opt (fig8CTy PQ PQC Pt ℓ)) := .fst .v0
     let lct0 : Expr OFig _ (.base .lct) := .fst (.snd .v0)
     let t0 : Expr OFig _ .nat := .fst (.snd (.snd .v0))
     let T0 : Expr OFig _ (.opt (.base .pt)) := .snd (.snd (.snd .v0))
     let dflt : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .pair (.pair t0 T0) lct0
     .caseOpt hc
       dflt
       (.ite (Expr.op (O := OFig) SimOp.lctSaltEq (.pair (.snd .v0) (.fst (.snd .v1)))) .v0
         (.pair (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))) (.fst (.snd .v1)))))

def ambCondFigE {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool) :
    Expr OFig Γ .bool :=
  orE (mInWinE (ssMir s) qParty)
    (.and (.not qParty)
      (hasUnknownKeyFigE P Dh encPt encT decT lam K toKemCoins (pGet (ssChains s) qParty)))

def sAmbFigE {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool) :
    Expr OFig Γ simStateTy :=
  .ite (ambCondFigE P Dh encPt encT decT lam K toKemCoins s qParty)
    (ssSetAmb s (.add (ssAmb s) (.nat 1)))
    s

def evictedHonestFigE {Γ} (s : Expr OFig Γ simStateTy) (qParty : Expr OFig Γ .bool)
    (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ))) : Expr OFig Γ .bool :=
  .letE (.pair s (.pair qParty honestC))
    (.caseOpt (.snd (.snd .v0))
      (.bool false)
      (.not (.eqN (.fst (.fst .v0))
        (.add (pGet (mEpoch (ssMir (.fst .v1))) (.fst (.snd .v1))) (.nat 1)))))

def honestSaltEqFigE {Γ} (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (lct : Expr OFig Γ (.base .lct)) : Expr OFig Γ .bool :=
  .letE (.pair honestC lct)
    (.caseOpt (.fst .v0)
      (.bool false)
      (Expr.op (O := OFig) SimOp.lctSaltEq (.pair (.snd .v0) (.snd .v1))))

def scPostSendE (B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (s1 : Expr OFig Γ simMirTy)
    (q0 : Expr OFig Γ .bool) (m0 : Expr OFig Γ (.base .plain))
    (isChall : Expr OFig Γ .bool) (pq' : Expr OFig Γ (.base .pq))
    (pn5 : Expr OFig Γ (.base .u32)) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Expr OFig Γ (.prod (.base .wire) simStateCTy) :=
  .letE (.pair sC (.pair s1 (.pair q0 (.pair m0 (.pair isChall (.pair pq' (.pair pn5 c)))))))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let s0 : Expr OFig _ simStateTy := scBase sC0
     let s1_0 : Expr OFig _ simMirTy := .fst (.snd .v0)
     let q : Expr OFig _ .bool := .fst (.snd (.snd .v0))
     let m : Expr OFig _ (.base .plain) := .fst (.snd (.snd (.snd .v0)))
     let ch : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v0))))
     let pq : Expr OFig _ (.base .pq) := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let pn : Expr OFig _ (.base .u32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let c0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let w : Expr OFig _ (.base .wire) := Expr.op (O := OFig) SimOp.toWire c0
     let rec' : Expr OFig _ simRecTy :=
       .pair (.pair q (.pair (pGet (mEpoch s1_0) q) (.add (pGet (mIdx s1_0) q) (.nat 1))))
         (.pair m w)
     let mir' : Expr OFig _ simMirTy := mRecordE s1_0 q rec' ch
     let base' : Expr OFig _ simStateTy :=
       ssMk mir' (pSet (ssPq s0) q pq) (pSet (ssPn s0) q pn) (ssUnackA s0)
         (.cons (.pair w c0) (ssHonest s0)) (ssChains s0) (ssAmb s0) (ssStopped s0)
     let kQ : Expr OFig _ keptTy := pGet (scKept sC0) q
     let sent' : Expr OFig _ (.list (.prod (fig8CTy PQ PQC Pt ℓ) (.base .vsSt))) :=
       .caseOpt (.fst kQ)
         (scSent sC0)
         (let st : Expr OFig _ (.base .fig8st) := .v0
          let step : Expr OFig _ (.prod .bool (.prod (.base .fig8st) (fig8CTy PQ PQC Pt ℓ))) :=
            Expr.op (O := OFig) (SimOp.fig8SendStep B) (.pair st .none)
          .ite (.fst step)
            (scSent (.fst .v1))
            (.caseOpt (Expr.op (O := OFig) SimOp.fig8VS st)
              (scSent (.fst .v1))
              (.cons (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))) .v0)
                (scSent (.fst .v2)))))
     let kept' : Expr OFig _ (.prod keptTy keptTy) :=
       pSet (scKept sC0) q (keptSendE P Dh encPt encT decT lam K toKemCoins B kQ)
     .pair w (scMk base' kept' sent' (scSnaps sC0)))

def scPostFwdKeptE (B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (q : Expr OFig Γ .bool)
    (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (res : Expr OFig Γ (.opt (fig8RrTy PQ PQC Pt ℓ))) :
    Expr OFig Γ simStateCTy :=
  .letE (.pair sC (.pair q (.pair c res)))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let res0 : Expr OFig _ (.opt (fig8RrTy PQ PQC Pt ℓ)) := .snd (.snd (.snd .v0))
     .caseOpt res0
       sC0
       (.caseSum .v0
         (.fst .v2)
         (let sC2 : Expr OFig _ simStateCTy := .fst .v2
          let q2 : Expr OFig _ .bool := .fst (.snd .v2)
          let c2 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .fst (.snd (.snd .v2))
          scMk (scBase sC2)
            (pSet (scKept sC2) q2
              (keptRecvE P Dh encPt encT decT lam K toKemCoins B c2 (pGet (scKept sC2) q2)))
            (scSent sC2) (scSnaps sC2))))

/-- Callback bundle specializing the decision-C `ReductionDsl` oracle handlers to a target game. -/
structure SimHookC {ι : Type} {T : OracleSpec ι} (I : Iface S T) (σExtra : Ty S) where
  sampleBv256 : ∀ {Γ}, Comp OFig I Γ (.base .bv256)
  samplePqc : ∀ {Γ}, Comp OFig I Γ (.base .pqc)
  onSendCoins : ∀ {Γ},
    Expr OFig Γ .bool → Expr OFig Γ (.base .pqc) → Expr OFig Γ σExtra →
      Comp OFig I Γ (.prod σExtra σExtra)
  onTr : ∀ {Γ},
    Expr OFig Γ (.prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256)))) →
      Expr OFig Γ σExtra → Comp OFig I Γ (.prod (.opt (fig8CTy PQ PQC Pt ℓ)) σExtra)
  onCh : ∀ {Γ},
    Expr OFig Γ
        (.prod .bool
          (.prod (lpubPlainTy PQ PQC Pt ℓ)
            (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256))))) →
      Expr OFig Γ σExtra → Comp OFig I Γ (.prod (.opt (fig8CTy PQ PQC Pt ℓ)) σExtra)
  onDl : ∀ {Γ},
    Expr OFig Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ)) →
      Expr OFig Γ σExtra → Comp OFig I Γ (.prod (.opt (fig8RrTy PQ PQC Pt ℓ)) σExtra)
  onIj : ∀ {Γ},
    Expr OFig Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ)) →
      Expr OFig Γ σExtra → Comp OFig I Γ (.prod (.opt (fig8RrTy PQ PQC Pt ℓ)) σExtra)
  onCr : ∀ {Γ},
    Expr OFig Γ .bool →
      Expr OFig Γ σExtra → Comp OFig I Γ (.prod (.opt (.base .fig8st)) σExtra)
  onProbe : ∀ {Γ},
    Expr OFig Γ (.prod .bool (fig8CTy PQ PQC Pt ℓ)) →
      Expr OFig Γ σExtra → Comp OFig I Γ σExtra
  onDeliverPost : ∀ {Γ},
    Expr OFig Γ .bool → Expr OFig Γ (.opt .nat) → Expr OFig Γ (.opt (simRrTy PQ PQC Pt ℓ)) →
      Expr OFig Γ σExtra → Comp OFig I Γ σExtra

def simDrawSendCoinsHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) {Γ}
    (r : Expr OFig Γ (.opt (.base .pqc))) :
    Comp OFig I Γ (.prod (.base .pqc) (.opt (.base .bv256))) :=
  .caseOpt r
    (.bind hk.samplePqc (.ret (.pair .v0 .none)))
    (.bind hk.sampleBv256 (.ret (.pair .v1 (.some .v0))))

def simSendHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (qep B : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy σExtra))
    (qParty : Expr OFig Γ .bool) (m₀ : Expr OFig Γ (.base .plain))
    (chal : Expr OFig Γ (.opt (.base .plain))) (r : Expr OFig Γ (.opt (.base .pqc))) :
    Comp OFig I Γ (.prod (.opt (.base .wire)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair st (.pair qParty (.pair m₀ (.pair chal r)))))
    (let sC0 : Expr OFig _ simStateCTy := .fst (.fst .v0)
     let ex0 : Expr OFig _ σExtra := .snd (.fst .v0)
     let s0 : Expr OFig _ simStateTy := scBase sC0
     let q0 : Expr OFig _ .bool := .fst (.snd .v0)
     let r0 : Expr OFig _ (.opt (.base .pqc)) := .snd (.snd (.snd (.snd .v0)))
     let refuse : Expr OFig _ .bool :=
       orE (ssStopped s0) (orE (mWin (ssMir s0)) (.not (mNoBobEpoch0E (ssMir s0) q0)))
     .ite refuse
       (.ret (.pair .none (.pair sC0 ex0)))
       (.caseOpt (mEpMgmtE qep (ssMir s0) q0 (isSomeE r0))
         (.ret (.pair .none (.pair sC0 ex0)))
         (let s1 : Expr OFig _ simMirTy := .v0
          let st1 : Expr OFig _ (.prod simStateCTy σExtra) := .fst .v1
          let q1 : Expr OFig _ .bool := .fst (.snd .v1)
          let chal1 : Expr OFig _ (.opt (.base .plain)) := .fst (.snd (.snd (.snd .v1)))
          let r1 : Expr OFig _ (.opt (.base .pqc)) := .snd (.snd (.snd (.snd .v1)))
          .ite (.and (isSomeE chal1) (.not (mSafeChE s1 q1)))
            (.ret (.pair .none st1))
            (.bind (simDrawSendCoinsHookC P Dh encPt encT decT lam K toKemCoins hk r1)
              (let rq2 : Expr OFig _ (.base .pqc) := .fst .v0
               let q2 : Expr OFig _ .bool := .fst (.snd .v2)
               let ex2 : Expr OFig _ σExtra := .snd (.fst .v2)
               .bind (hk.onSendCoins q2 rq2 ex2)
                 (let exFail3 : Expr OFig _ σExtra := .snd .v0
                  let rq3 : Expr OFig _ (.base .pqc) := .fst .v1
                  let s1_3 : Expr OFig _ simMirTy := .v2
                  let sC3 : Expr OFig _ simStateCTy := .fst (.fst .v3)
                  let s3 : Expr OFig _ simStateTy := scBase sC3
                  let q3 : Expr OFig _ .bool := .fst (.snd .v3)
                  let pn3 : Expr OFig _ (.base .u32) :=
                    .ite (.not (.eqN (pGet (mEpoch s1_3) q3) (pGet (mEpoch (ssMir s3)) q3)))
                      (Expr.op (O := OFig) SimOp.natToU32
                        (.sub (pGet (mIdx (ssMir s3)) q3) (.nat 1)))
                      (pGet (ssPn s3) q3)
                  .caseOpt
                    (spqrSendPubFigE P Dh encPt encT decT lam K toKemCoins
                      (.pair q3 (.pair (ssUnackA s3) (.pair (pGet (ssPq s3) q3)
                        (.pair rq3 pn3)))))
                    (.ret (.pair .none (.pair sC3 exFail3)))
                    (let pub4 : Expr OFig _ (.base .lpub) := .snd .v0
                     let exOk4 : Expr OFig _ σExtra := .fst .v1
                     let rc4 : Expr OFig _ (.opt (.base .bv256)) := .snd .v2
                     let q4 : Expr OFig _ .bool := .fst (.snd .v4)
                     let m0_4 : Expr OFig _ (.base .plain) := .fst (.snd (.snd .v4))
                     let chal4 : Expr OFig _ (.opt (.base .plain)) :=
                       .fst (.snd (.snd (.snd .v4)))
                     .bind
                       (.caseOpt chal4
                         (hk.onTr (.pair q4 (.pair (.pair pub4 m0_4) rc4)) exOk4)
                         (let pub5 : Expr OFig _ (.base .lpub) := .snd .v1
                          let exOk5 : Expr OFig _ σExtra := .fst .v2
                          let rc5 : Expr OFig _ (.opt (.base .bv256)) := .snd .v3
                          let q5 : Expr OFig _ .bool := .fst (.snd .v5)
                          let m0_5 : Expr OFig _ (.base .plain) := .fst (.snd (.snd .v5))
                          hk.onCh
                            (.pair q5 (.pair (.pair pub5 m0_5) (.pair (.pair pub5 .v0) rc5)))
                            exOk5))
                       (let res5 : Expr OFig _ (.opt (fig8CTy PQ PQC Pt ℓ)) := .fst .v0
                        let sC5 : Expr OFig _ simStateCTy := .fst (.fst .v5)
                        let exFail5 : Expr OFig _ σExtra := .snd .v2
                        .caseOpt res5
                          (.ret (.pair .none (.pair sC5 exFail5)))
                          (let c6 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .v0
                           let ex6 : Expr OFig _ σExtra := .snd .v1
                           let pq'6 : Expr OFig _ (.base .pq) := .fst .v2
                           let s1_6 : Expr OFig _ simMirTy := .v5
                           let sC6 : Expr OFig _ simStateCTy := .fst (.fst .v6)
                           let s6 : Expr OFig _ simStateTy := scBase sC6
                           let q6 : Expr OFig _ .bool := .fst (.snd .v6)
                           let m0_6 : Expr OFig _ (.base .plain) := .fst (.snd (.snd .v6))
                           let chal6 : Expr OFig _ (.opt (.base .plain)) :=
                             .fst (.snd (.snd (.snd .v6)))
                           let pn6 : Expr OFig _ (.base .u32) :=
                             .ite (.not (.eqN (pGet (mEpoch s1_6) q6)
                                 (pGet (mEpoch (ssMir s6)) q6)))
                               (Expr.op (O := OFig) SimOp.natToU32
                                 (.sub (pGet (mIdx (ssMir s6)) q6) (.nat 1)))
                               (pGet (ssPn s6) q6)
                           let wsC' : Expr OFig _ (.prod (.base .wire) simStateCTy) :=
                             scPostSendE P Dh encPt encT decT lam K toKemCoins B
                               sC6 s1_6 q6 m0_6 (isSomeE chal6) pq'6 pn6 c6
                           .ret (.pair (.some (.fst wsC')) (.pair (.snd wsC') ex6)))))))))))

def fwdAnswerHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (ci? : Expr OFig Γ (.opt .nat))
    (Tpk : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq))
    (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Comp OFig I Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair sC (.pair ex (.pair qParty (.pair w (.pair isDel (.pair ci?
      (.pair Tpk (.pair pq' c')))))))))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let ex0 : Expr OFig _ σExtra := .fst (.snd .v0)
     let q0 : Expr OFig _ .bool := .fst (.snd (.snd .v0))
     let c'0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
     .bind
       (.ite (inTFigE P Dh encPt encT decT lam K toKemCoins L (scBase sC0) q0 c'0)
         (hk.onDl (.pair q0 c'0) ex0)
         (hk.onIj (.pair q0 c'0) ex0))
       (let res1 : Expr OFig _ (.opt (fig8RrTy PQ PQC Pt ℓ)) := .fst .v0
        let ex1 : Expr OFig _ σExtra := .snd .v0
        let sC1 : Expr OFig _ simStateCTy := .fst .v1
        let q1 : Expr OFig _ .bool := .fst (.snd (.snd .v1))
        let w1 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v1)))
        let del1 : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v1))))
        let ci1 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd (.snd .v1)))))
        let T1 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))
        let pq1 : Expr OFig _ (.base .pq) :=
          .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
        let c'1 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
          .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
        let sC2 : Expr OFig _ simStateCTy :=
          scPostFwdKeptE P Dh encPt encT decT lam K toKemCoins B sC1 q1 c'1 res1
        let ans : Expr OFig _ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
          onAnswerFigE P Dh encPt encT decT lam K toKemCoins L qep
            (scBase sC2) q1 w1 del1 ci1 T1 pq1 res1
        .ret (.pair (.fst ans) (.pair (scSetBase sC2 (.snd ans)) ex1))))

def resyncHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (ci? : Expr OFig Γ (.opt .nat)) (Tpk : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ))
    (r : Expr OFig Γ (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ))))) :
    Comp OFig I Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair sC (.pair ex (.pair qParty (.pair w (.pair ci? (.pair Tpk
      (.pair pq' (.pair c r)))))))))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let ex0 : Expr OFig _ σExtra := .fst (.snd .v0)
     let r0 : Expr OFig _ (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
     .caseOpt r0
       (.ret (.pair (.some (.inl .unit)) (.pair sC0 ex0)))
       (let ex1 : Expr OFig _ σExtra := .fst (.snd .v1)
        let q1 : Expr OFig _ .bool := .fst (.snd (.snd .v1))
        let c1 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
          .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
        .bind (hk.onDl (.pair q1 c1) ex1)
          (let res2 : Expr OFig _ (.opt (fig8RrTy PQ PQC Pt ℓ)) := .fst .v0
           let ex2 : Expr OFig _ σExtra := .snd .v0
           let sC2 : Expr OFig _ simStateCTy := .fst .v2
           .caseOpt res2
             (.ret (.pair (.some (.inl .unit)) (.pair sC2 ex2)))
             (.caseSum .v0
               (.ret (.pair (.some (.inl .unit)) (.pair (.fst .v4) (.snd .v2))))
               (let ex4 : Expr OFig _ σExtra := .snd .v2
                let t4 : Expr OFig _ .nat := .fst .v3
                let i4 : Expr OFig _ .nat := .fst (.snd .v3)
                let m'4 : Expr OFig _ (.base .plain) := .snd (.snd (.snd .v3))
                let sC4 : Expr OFig _ simStateCTy := .fst .v4
                let q4 : Expr OFig _ .bool := .fst (.snd (.snd .v4))
                let w4 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v4)))
                let ci4 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd .v4))))
                let T4 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd .v4)))))
                let pq4 : Expr OFig _ (.base .pq) :=
                  .fst (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))
                let c4 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
                  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
                let sC5 : Expr OFig _ simStateCTy :=
                  scMk (scBase sC4)
                    (pSet (scKept sC4) q4
                      (keptRecvE P Dh encPt encT decT lam K toKemCoins B c4
                        (pGet (scKept sC4) q4)))
                    (scSent sC4) (scSnaps sC4)
                let acc : Expr OFig _ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) simStateTy) :=
                  onAcceptFigE P Dh encPt encT decT lam K toKemCoins L qep
                    (scBase sC5) q4 w4 (.bool true) t4 i4 m'4 ci4 T4 pq4
                .ret (.pair (.fst acc) (.pair (scSetBase sC5 (.snd acc)) ex4)))))))

def fwdHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (ci? : Expr OFig Γ (.opt .nat))
    (Tpk : Expr OFig Γ (.base .pk)) (pq' : Expr OFig Γ (.base .pq))
    (honestC : Expr OFig Γ (.opt (fig8CTy PQ PQC Pt ℓ)))
    (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Comp OFig I Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair sC (.pair ex (.pair qParty (.pair w (.pair isDel (.pair ci?
      (.pair Tpk (.pair pq' (.pair honestC c'))))))))))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let ex0 : Expr OFig _ σExtra := .fst (.snd .v0)
     let q0 : Expr OFig _ .bool := .fst (.snd (.snd .v0))
     let w0 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v0)))
     let del0 : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v0))))
     let ci0 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let T0 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let pq0 : Expr OFig _ (.base .pq) :=
       .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
     let hc0 : Expr OFig _ (.opt (fig8CTy PQ PQC Pt ℓ)) :=
       .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
     let c'0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
     .caseOpt hc0
       (fwdAnswerHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
         sC0 ex0 q0 w0 del0 ci0 T0 pq0 c'0)
       (let c1 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .v0
        let sC1 : Expr OFig _ simStateCTy := .fst .v1
        let ex1 : Expr OFig _ σExtra := .fst (.snd .v1)
        let q1 : Expr OFig _ .bool := .fst (.snd (.snd .v1))
        let w1 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v1)))
        let del1 : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v1))))
        let ci1 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd (.snd .v1)))))
        let T1 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))
        let pq1 : Expr OFig _ (.base .pq) :=
          .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
        let c'1 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
          .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
        .ite
          (.and (.not (Expr.op (O := OFig) SimOp.eqFig8C (.pair c1 c'1)))
            (.and del1 (.not (mSafeInjE (ssMir (scBase sC1))))))
          (.caseOpt
            (evalCKE P Dh encPt encT decT lam K toKemCoins L B sC1 q1 w1 c1 c'1)
            (.bind (hk.onProbe (.pair q1 c'1) ex1)
              (.ret (.pair (.some (.inl .unit)) (.pair (.fst .v2) .v0))))
            (let r2 : Expr OFig _ (.opt (.prod .nat (.prod .nat (lpubPlainTy PQ PQC Pt ℓ)))) :=
               .v0
             let c2 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .v1
             let sC2 : Expr OFig _ simStateCTy := .fst .v2
             let ex2 : Expr OFig _ σExtra := .fst (.snd .v2)
             let q2 : Expr OFig _ .bool := .fst (.snd (.snd .v2))
             let w2 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v2)))
             let ci2 : Expr OFig _ (.opt .nat) := .fst (.snd (.snd (.snd (.snd (.snd .v2)))))
             let T2 : Expr OFig _ (.base .pk) :=
               .fst (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
             let pq2 : Expr OFig _ (.base .pq) :=
               .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))
             resyncHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
               sC2 ex2 q2 w2 ci2 T2 pq2 c2 r2))
          (fwdAnswerHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
            sC1 ex1 q1 w1 del1 ci1 T1 pq1 c'1)))

def fwdEvictHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L qep B : ℕ) {Γ}
    (sC : Expr OFig Γ simStateCTy) (ex : Expr OFig Γ σExtra)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) (Tpk : Expr OFig Γ (.base .pk))
    (pq' : Expr OFig Γ (.base .pq)) (c' : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Comp OFig I Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair sC (.pair ex
      (.pair qParty (.pair w (.pair isDel (.pair Tpk (.pair pq' c'))))))))
    (let sC0 : Expr OFig _ simStateCTy := .fst .v0
     let ex0 : Expr OFig _ σExtra := .fst (.snd .v0)
     let q0 : Expr OFig _ .bool := .fst (.snd (.snd .v0))
     let w0 : Expr OFig _ (.base .wire) := .fst (.snd (.snd (.snd .v0)))
     let del0 : Expr OFig _ .bool := .fst (.snd (.snd (.snd (.snd .v0))))
     let T0 : Expr OFig _ (.base .pk) := .fst (.snd (.snd (.snd (.snd (.snd .v0)))))
     let pq0 : Expr OFig _ (.base .pq) := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     let c'0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) :=
       .snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
     .ite (.and del0 (.not (mSafeInjE (ssMir (scBase sC0)))))
       (.bind (hk.onProbe (.pair q0 c'0) ex0)
         (.ret (.pair (.some (.inl .unit)) (.pair (.fst .v1) .v0))))
       (fwdAnswerHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
         sC0 ex0 q0 w0 del0 .none T0 pq0 c'0))

def simRecvHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L qep B : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy σExtra))
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire))
    (isDel : Expr OFig Γ .bool) :
    Comp OFig I Γ (.prod (.opt (simRrTy PQ PQC Pt ℓ)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair st (.pair qParty (.pair w isDel))))
    (let sC0 : Expr OFig _ simStateCTy := .fst (.fst .v0)
     let ex0 : Expr OFig _ σExtra := .snd (.fst .v0)
     let s0 : Expr OFig _ simStateTy := scBase sC0
     let q0 : Expr OFig _ .bool := .fst (.snd .v0)
     let w0 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v0))
     let del0 : Expr OFig _ .bool := .snd (.snd (.snd .v0))
     let inTrOpt : Expr OFig _ (.opt simRecTy) :=
       mInTransitFigE P Dh encPt encT decT lam K toKemCoins L (ssMir s0) (otherE q0) w0
     let refuse : Expr OFig _ .bool :=
       orE (ssStopped s0)
         (orE (mWin (ssMir s0))
           (orE (.and del0 (.not (isSomeE inTrOpt)))
             (.and (.not del0)
               (orE (isSomeE inTrOpt)
                 (orE (.not (mSafeInjE (ssMir s0)))
                   (.not (Expr.op (O := OFig) SimOp.injOK w0)))))))
     .ite refuse
       (.ret (.pair .none (.pair sC0 ex0)))
       (.caseOpt (parseRecvFigCE P Dh encPt encT decT lam K toKemCoins (2 ^ 32)
           (.pair q0 (.pair (pGet (ssPq s0) q0) w0)))
         (.ret (.pair (.some (.inl .unit)) (.pair sC0 ex0)))
         (let pk1 : Expr OFig _ (.base .pk) := .fst (.snd (.snd .v0))
          let T?1 : Expr OFig _ (.opt (.base .pt)) := .fst (.snd (.snd (.snd .v0)))
          let lct1 : Expr OFig _ (.base .lct) := .snd (.snd (.snd (.snd .v0)))
          let sC1 : Expr OFig _ simStateCTy := .fst (.fst .v1)
          let ex1 : Expr OFig _ σExtra := .snd (.fst .v1)
          let s1 : Expr OFig _ simStateTy := scBase sC1
          let q1 : Expr OFig _ .bool := .fst (.snd .v1)
          let w1 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v1))
          let hc1 : Expr OFig _ (.opt (fig8CTy PQ PQC Pt ℓ)) :=
            honestCFigE P Dh encPt encT decT lam K toKemCoins L s1 q1 w1
          .caseOpt
            (findChainFigE P Dh encPt encT decT lam K toKemCoins
              (.pair (pGet (ssChains s1) q1) pk1))
            (let evicted1 : Expr OFig _ .bool :=
               evictedHonestFigE P Dh encPt encT decT lam K toKemCoins s1 q1 hc1
             let saltEq1 : Expr OFig _ .bool :=
               honestSaltEqFigE P Dh encPt encT decT lam K toKemCoins hc1 lct1
             let i1 : Expr OFig _ .nat := .fst (.snd .v0)
             let sAmb1 : Expr OFig _ simStateTy :=
               sAmbFigE P Dh encPt encT decT lam K toKemCoins s1 q1
             let sCAmb1 : Expr OFig _ simStateCTy := scSetBase sC1 sAmb1
             .ite (.and evicted1 saltEq1)
               (.ret (.pair (.some (.inl .unit)) (.pair sC1 ex1)))
               (.ite (Expr.op (O := OFig) SimOp.isZeroPt T?1)
                 (.ret (.pair (.some (.inl .unit)) (.pair sC1 ex1)))
                 (.ite (orE (mInWinE (ssMir s1) q1)
                        (orE (.lt (.nat 25000) (.sub i1 (.nat 1))) (leN (.nat (2 ^ 32)) i1)))
                   (.ret (.pair (.some (.inl .unit)) (.pair sCAmb1 ex1)))
                   (.caseOpt T?1
                     (.ret (.pair (.some (.inl .unit)) (.pair sCAmb1 ex1)))
                     (let pq'2 : Expr OFig _ (.base .pq) := .fst .v1
                      let pk2 : Expr OFig _ (.base .pk) := .fst (.snd (.snd .v1))
                      let lct2 : Expr OFig _ (.base .lct) := .snd (.snd (.snd (.snd .v1)))
                      let sC2 : Expr OFig _ simStateCTy := .fst (.fst .v2)
                      let ex2 : Expr OFig _ σExtra := .snd (.fst .v2)
                      let s2 : Expr OFig _ simStateTy := scBase sC2
                      let q2 : Expr OFig _ .bool := .fst (.snd .v2)
                      let w2 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v2))
                      let del2 : Expr OFig _ .bool := .snd (.snd (.snd .v2))
                      let hc2 : Expr OFig _ (.opt (fig8CTy PQ PQC Pt ℓ)) :=
                        honestCFigE P Dh encPt encT decT lam K toKemCoins L s2 q2 w2
                      let sCAmb2 : Expr OFig _ simStateCTy :=
                        scSetBase sC2 (sAmbFigE P Dh encPt encT decT lam K toKemCoins s2 q2)
                      let epNext2 : Expr OFig _ .nat := .add (pGet (mEpoch (ssMir s2)) q2) (.nat 1)
                      .ite (evictedHonestFigE P Dh encPt encT decT lam K toKemCoins s2 q2 hc2)
                        (fwdEvictHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
                          sCAmb2 ex2 q2 w2 del2 pk2 pq'2
                          (.pair (.pair epNext2 (.some .v0)) lct2))
                        (fwdHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
                          sCAmb2 ex2 q2 w2 del2 .none pk2 pq'2 hc2
                          (mkCFigE P Dh encPt encT decT lam K toKemCoins
                            hc2 lct2 epNext2 (.some .v0))))))))
            (let ci2 : Expr OFig _ .nat := .fst .v0
             let g2 : Expr OFig _ (ghostChainTy PQ PQC Pt ℓ) := .snd .v0
             let pq'2 : Expr OFig _ (.base .pq) := .fst .v1
             let i2 : Expr OFig _ .nat := .fst (.snd .v1)
             let pk2 : Expr OFig _ (.base .pk) := .fst (.snd (.snd .v1))
             let T?2 : Expr OFig _ (.opt (.base .pt)) := .fst (.snd (.snd (.snd .v1)))
             let lct2 : Expr OFig _ (.base .lct) := .snd (.snd (.snd (.snd .v1)))
             let sC2 : Expr OFig _ simStateCTy := .fst (.fst .v2)
             let ex2 : Expr OFig _ σExtra := .snd (.fst .v2)
             let s2 : Expr OFig _ simStateTy := scBase sC2
             let q2 : Expr OFig _ .bool := .fst (.snd .v2)
             let w2 : Expr OFig _ (.base .wire) := .fst (.snd (.snd .v2))
             let del2 : Expr OFig _ .bool := .snd (.snd (.snd .v2))
             let hc2 : Expr OFig _ (.opt (fig8CTy PQ PQC Pt ℓ)) :=
               honestCFigE P Dh encPt encT decT lam K toKemCoins L s2 q2 w2
             .ite (Expr.op (O := OFig) SimOp.chainRejects (.pair (.snd (.snd g2)) i2))
               (.ret (.pair (.some (.inl .unit)) (.pair sC2 ex2)))
               (fwdHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
                 sC2 ex2 q2 w2 del2 (.some ci2) pk2 pq'2 hc2
                 (mkCFigE P Dh encPt encT decT lam K toKemCoins
                   hc2 lct2 (.fst (.snd g2)) T?2))))))

def simCorrHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L : ℕ) {Γ}
    (st : Expr OFig Γ (.prod simStateCTy σExtra)) (qParty : Expr OFig Γ .bool) :
    Comp OFig I Γ (.prod (.opt (.base .ghostSt)) (.prod simStateCTy σExtra)) :=
  .bind (.ret (.pair st qParty))
    (let sC0 : Expr OFig _ simStateCTy := .fst (.fst .v0)
     let ex0 : Expr OFig _ σExtra := .snd (.fst .v0)
     let s0 : Expr OFig _ simStateTy := scBase sC0
     let q0 : Expr OFig _ .bool := .snd .v0
     let refuse : Expr OFig _ .bool :=
       orE (ssStopped s0)
         (orE (mWin (ssMir s0))
           (orE (.not (mCorrAllowedE L (ssMir s0) q0))
             (orE (mInWinE (ssMir s0) q0)
               (.not (mNoSpkCorrE (ssMir s0) q0)))))
     .ite refuse
       (.ret (.pair .none (.pair sC0 ex0)))
       (.bind (hk.onCr q0 ex0)
         (let res1 : Expr OFig _ (.opt (.base .fig8st)) := .fst .v0
          let ex1 : Expr OFig _ σExtra := .snd .v0
          let sC1 : Expr OFig _ simStateCTy := .fst (.fst .v1)
          .caseOpt res1
            (.ret (.pair .none (.pair sC1 ex1)))
            (let st2 : Expr OFig _ (.base .fig8st) := .v0
             let ex2 : Expr OFig _ σExtra := .snd .v1
             let sC2 : Expr OFig _ simStateCTy := .fst (.fst .v2)
             let s2 : Expr OFig _ simStateTy := scBase sC2
             let q2 : Expr OFig _ .bool := .snd .v2
             let chains' :
                 Expr OFig _ (.prod (.list (ghostChainTy PQ PQC Pt ℓ))
                   (.list (ghostChainTy PQ PQC Pt ℓ))) :=
               .ite (.and q2 (.eqN (.snd (mEpoch (ssMir s2))) (.nat 0)))
                 (.pair
                   (revealSpkChainsFigE P Dh encPt encT decT lam K toKemCoins
                     (.pair (.fst (ssChains s2)) st2))
                   (.snd (ssChains s2)))
                 (ssChains s2)
             let base' : Expr OFig _ simStateTy :=
               ssMk (mAfterCorrE L (ssMir s2) q2)
                 (ssPq s2) (ssPn s2) (ssUnackA s2) (ssHonest s2) chains'
                 (ssAmb s2) (ssStopped s2)
             let epQ : Expr OFig _ .nat := pGet (mEpoch (ssMir s2)) q2
             let ghostOut : Expr OFig _ (.base .ghostSt) :=
               toGhostFigE P Dh encPt encT decT lam K toKemCoins
                 (.pair q2
                   (.pair st2
                     (.pair (pGet (ssPn s2) q2)
                       (.pair (pGet chains' q2)
                         (.pair (ssUnackA s2)
                           (.pair (pGet (ssPq s2) q2) epQ))))))
             let sC' : Expr OFig _ simStateCTy :=
               scMk base' (pSet (scKept sC2) q2 (keptOfStE st2)) (scSent sC2)
                 (.cons (.pair q2 (.pair epQ ghostOut)) (scSnaps sC2))
             .ret (.pair (.some ghostOut) (.pair sC' ex2))))))

def findRevHonestIdxE (L : ℕ) {Γ} (s : Expr OFig Γ simStateTy)
    (qParty : Expr OFig Γ .bool) (w : Expr OFig Γ (.base .wire)) :
    Expr OFig Γ (.opt .nat) :=
  .letE (.pair s (.pair qParty w))
    (.snd
      (.foldrB L (ssHonest (.fst .v0)) (.pair (.nat 0) .none)
        (let matchHere : Expr OFig _ .bool :=
           .and
             (Expr.op (O := OFig) SimOp.eqWire (.pair (.fst .v0) (.snd (.snd .v2))))
             (boolEq (senderOfE (.fst (.fst (.snd .v0)))) (otherE (.fst (.snd .v2))))
         let idxPrev : Expr OFig _ .nat := .fst .v1
         let foundPrev : Expr OFig _ (.opt .nat) := .snd .v1
         .pair (.add idxPrev (.nat 1))
           (.caseOpt foundPrev
             (.ite matchHere (.some idxPrev) .none)
             (.some .v0)))))

def simHandleHookC {ι : Type} {T : OracleSpec ι} {I : Iface S T} {σExtra : Ty S}
    (hk : SimHookC P Dh encPt encT decT lam K toKemCoins I σExtra) (L qep B : ℕ) :
    Comp OFig I
      [.prod simStateCTy σExtra, (simCodec PQ PQC Pt ℓ).Q]
      (.prod (simCodec PQ PQC Pt ℓ).R (.prod simStateCTy σExtra)) :=
  let q : Expr OFig _ (simCodec PQ PQC Pt ℓ).Q := .v1
  .caseSum q
    (.caseSum .v0
      (.caseSum .v0
        (.caseSum .v0
          (.bind
            (simSendHookC P Dh encPt encT decT lam K toKemCoins hk qep B
              .v4 (.fst .v0) (.fst (.snd .v0)) .none (.snd (.snd .v0)))
            (.ret (.pair (.inl (.inl (.inl (.inl (.fst .v0))))) (.snd .v0))))
          (.bind
            (simSendHookC P Dh encPt encT decT lam K toKemCoins hk qep B
              .v4 (.fst .v0) (.fst (.snd .v0)) (.some (.fst (.snd (.snd .v0))))
              (.snd (.snd (.snd .v0))))
            (.ret (.pair (.inl (.inl (.inl (.inr (.fst .v0))))) (.snd .v0)))))
        (let qParty : Expr OFig _ .bool := .fst .v0
         let w : Expr OFig _ (.base .wire) := .snd .v0
         let j? : Expr OFig _ (.opt .nat) :=
           findRevHonestIdxE P Dh encPt encT decT lam K toKemCoins L (scBase (.fst .v3)) qParty w
         .bind (.ret (.pair qParty j?))
           (.bind
             (simRecvHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
               .v4 (.fst .v1) (.snd .v1) (.bool true))
             (.bind
               (hk.onDeliverPost (.fst .v1) (.snd .v1) (.fst .v0) (.snd (.snd .v0)))
               (.ret
                 (.pair (.inl (.inl (.inr (.fst .v1))))
                   (.pair (.fst (.snd .v1)) .v0)))))))
      (.bind
        (simRecvHookC P Dh encPt encT decT lam K toKemCoins hk L qep B
          .v2 (.fst .v0) (.snd .v0) (.bool false))
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (.bind
      (simCorrHookC P Dh encPt encT decT lam K toKemCoins hk L .v1 .v0)
      (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))

def initSimCE {Γ} (pqrKey : Expr OFig Γ (.base .bv256)) : Expr OFig Γ simStateCTy :=
  .letE pqrKey
    (let pqA : Expr OFig _ (.base .pq) := Expr.op (O := OFig) SimOp.spqrInitA .v0
     let pqB : Expr OFig _ (.base .pq) := Expr.op (O := OFig) SimOp.spqrInitB .v0
     let base0 : Expr OFig _ simStateTy :=
       ssMk initSimMirE (.pair pqA pqB)
         (.pair (Expr.op (O := OFig) SimOp.zeroU32 .unit)
           (Expr.op (O := OFig) SimOp.zeroU32 .unit))
         (.bool true) .nil
         (.pair (.cons (initChainAFigE P Dh encPt encT decT lam K toKemCoins) .nil) .nil)
         (.nat 0) (.bool false)
     scMk base0 (.pair keptUnknownE keptUnknownE) .nil .nil)

/-! ### `DeliverForge` reduction -/

local notation "SIfaceDF" => simIfaceDF PQ PQC Pt ℓ

def deliverForgeHookC (L : ℕ) :
    SimHookC P Dh encPt encT decT lam K toKemCoins SIfaceDF (.list (fig8CTy PQ PQC Pt ℓ)) where
  sampleBv256 := Comp.sample (I := SIfaceDF) (UniformSamplerTag.base SimBaseSamp.bv256) .unit
  samplePqc := Comp.sample (I := SIfaceDF) (UniformSamplerTag.base SimBaseSamp.pqc) .unit
  onSendCoins _ _ ex := .ret (.pair ex ex)
  onTr arg ex :=
    .bind (.ret (.pair arg ex))
      (.bind (Comp.query (I := SIfaceDF) SMTagDF.tr (.fst .v0))
        (.ret
          (.pair .v0
            (.caseOpt .v0 (.snd .v1) (.cons .v0 (.snd .v2))))))
  onCh arg ex :=
    .bind (.ret (.pair arg ex))
      (.bind (Comp.query (I := SIfaceDF) SMTagDF.ch (.fst .v0))
        (.ret
          (.pair .v0
            (.caseOpt .v0 (.snd .v1) (.cons .v0 (.snd .v2))))))
  onDl arg ex :=
    .bind (.ret (.pair arg ex))
      (.bind (Comp.query (I := SIfaceDF) SMTagDF.dl (.fst .v0))
        (.ret (.pair .v0 (.snd .v1))))
  onIj arg ex :=
    .bind (.ret (.pair arg ex))
      (.bind (Comp.query (I := SIfaceDF) SMTagDF.ij (.fst .v0))
        (.ret (.pair .v0 (.snd .v1))))
  onCr arg ex :=
    .bind (.ret (.pair arg ex))
      (.bind (Comp.query (I := SIfaceDF) SMTagDF.cr (.fst .v0))
        (.ret (.pair .v0 (.snd .v1))))
  onProbe arg ex :=
    .bind (.ret (.pair arg ex))
      (let sent0 : Expr OFig _ (.list (fig8CTy PQ PQC Pt ℓ)) := .snd .v0
       .caseOpt
         (.findB L sent0
           (Expr.op (O := OFig) SimOp.sameWireFig8
             (.pair .v0 (.snd (.fst .v1)))))
         (.ret sent0)
         (.bind
           (Comp.query (I := SIfaceDF) SMTagDF.df
             (.pair (.fst (.fst .v1)) (.pair .v0 (.snd (.fst .v1)))))
           (.ret (.snd .v2))))
  onDeliverPost _ _ _ ex := .ret ex

/-- Costed reduction program for `simDeliverForge`. -/
@[reducible] def simDeliverForgeProg (L qep B : ℕ) :
    CostedReduction OFig SIfaceDF
      (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (simCodec PQ PQC Pt ℓ) .unit .unit .bool .bool where
  σ := .prod simStateCTy (.list (fig8CTy PQ PQC Pt ℓ))
  init :=
    .bind (Comp.sample (I := SIfaceDF) (UniformSamplerTag.base SimBaseSamp.bv256) .unit)
      (.ret (.pair .unit (.pair (initSimCE P Dh encPt encT decT lam K toKemCoins .v0) .nil)))
  handle :=
    simHandleHookC P Dh encPt encT decT lam K toKemCoins
      (deliverForgeHookC P Dh encPt encT decT lam K toKemCoins L) L qep B
  finish := .ret .v1

/-! ### `KemFailFind` reduction -/

local notation "KIface" => kemFailIface PQ PQC Pt ℓ

@[reducible] def fig8RecTy : Ty S :=
  .prod posTy (.prod (lpubPlainTy PQ PQC Pt ℓ) (fig8CTy PQ PQC Pt ℓ))

@[reducible] def fig8GsTy : Ty S :=
  .prod (.prod (.base .fig8st) (.base .fig8st)) (mirTy fig8RecTy)

def fgSt {O' : Ops S} {Γ} (g : Expr O' Γ fig8GsTy) :
    Expr O' Γ (.prod (.base .fig8st) (.base .fig8st)) := .fst g
def fgMir {O' : Ops S} {Γ} (g : Expr O' Γ fig8GsTy) : Expr O' Γ (mirTy fig8RecTy) := .snd g

def fgInTransitE (L : ℕ) {Γ} (m : Expr OFig Γ (mirTy fig8RecTy))
    (qParty : Expr OFig Γ .bool) (c : Expr OFig Γ (fig8CTy PQ PQC Pt ℓ)) :
    Expr OFig Γ (.opt fig8RecTy) :=
  .letE (.pair m (.pair qParty c))
    (.findB L (mTrans (.fst .v0))
      (.and (boolEq (posSender (.fst .v0)) (.fst (.snd .v1)))
        (Expr.op (O := OFig) SimOp.eqFig8C (.pair (.snd (.snd .v0)) (.snd (.snd .v1))))))

@[reducible] def kemExtraTy : Ty S :=
  .prod fig8GsTy (.prod (.base .kemTrack) (.base .kemCand))

def samIfNecFig8C {Γ} (r : Expr OFig Γ (.opt (.base .bv256))) :
    Comp OFig KIface Γ (.prod (.base .bv256) .bool) :=
  .caseOpt r
    (.bind (Comp.sample (I := KIface) (UniformSamplerTag.base SimBaseSamp.bv256) .unit)
      (.ret (.pair .v0 (.bool false))))
    (.ret (.pair .v0 (.bool true)))

def kemFailHookC (L qep B : ℕ) :
    SimHookC P Dh encPt encT decT lam K toKemCoins KIface kemExtraTy where
  sampleBv256 := Comp.sample (I := KIface) (UniformSamplerTag.base SimBaseSamp.bv256) .unit
  samplePqc := Comp.sample (I := KIface) (UniformSamplerTag.base SimBaseSamp.pqc) .unit
  onSendCoins qB rq ex :=
    .ret
      (.letE (.pair qB (.pair rq ex))
        (let q0 : Expr OFig _ .bool := .fst .v0
         let rq0 : Expr OFig _ (.base .pqc) := .fst (.snd .v0)
         let ex0 : Expr OFig _ kemExtraTy := .snd (.snd .v0)
         let g0 : Expr OFig _ fig8GsTy := .fst ex0
         let tr0 : Expr OFig _ (.base .kemTrack) := .fst (.snd ex0)
         let step :
             Expr OFig _ (.prod (.base .kemTrack) (.prod (.base .kemTrack) (.base .kemCand))) :=
           Expr.op (O := OFig) SimOp.stepKemFailSend (.pair tr0 (.pair q0 rq0))
         .pair
           (.pair g0 (.pair (.fst step) (.snd (.snd step))))
           (.pair g0 (.pair (.fst (.snd step)) (.snd (.snd step))))))
  onTr arg ex :=
    .bind (.ret (.pair arg ex))
      (let r0 : Expr OFig _ (.opt (.base .bv256)) := .snd (.snd (.fst .v0))
       let ex0 : Expr OFig _ kemExtraTy := .snd .v0
       let g0 : Expr OFig _ fig8GsTy := .fst ex0
       .ite (mWin (fgMir g0))
         (.ret (.pair .none ex0))
         (.bind (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins r0)
           (let bad1 : Expr OFig _ .bool := .snd .v0
            let q1 : Expr OFig _ .bool := .fst (.fst .v1)
            let ex1 : Expr OFig _ kemExtraTy := .snd .v1
            let g1 : Expr OFig _ fig8GsTy := .fst ex1
            .ret
              (.caseOpt (mEpMgmtE (qep + 1) (fgMir g1) q1 bad1)
                (.pair .none ex1)
                (let mir2 : Expr OFig _ (mirTy fig8RecTy) := .v0
                 let coins2 : Expr OFig _ (.base .bv256) := .fst .v1
                 let q2 : Expr OFig _ .bool := .fst (.fst .v2)
                 let m2 : Expr OFig _ (lpubPlainTy PQ PQC Pt ℓ) := .fst (.snd (.fst .v2))
                 let ex2 : Expr OFig _ kemExtraTy := .snd .v2
                 let g2 : Expr OFig _ fig8GsTy := .fst ex2
                 let out2 :
                     Expr OFig _ (.prod .bool (.prod (.base .fig8st) (fig8CTy PQ PQC Pt ℓ))) :=
                   Expr.op (O := OFig) (SimOp.fig8SendStep B)
                     (.pair (pGet (fgSt g2) q2) (.some (.pair m2 coins2)))
                 let st'2 : Expr OFig _ (.base .fig8st) := .fst (.snd out2)
                 let c2 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.snd out2)
                 let rec2 : Expr OFig _ fig8RecTy :=
                   .pair
                     (.pair q2
                       (.pair (pGet (mEpoch mir2) q2) (.add (pGet (mIdx mir2) q2) (.nat 1))))
                     (.pair m2 c2)
                 let g'2 : Expr OFig _ fig8GsTy :=
                   .pair (pSet (fgSt g2) q2 st'2) (mRecordE mir2 q2 rec2 (.bool false))
                 .pair (.some c2) (.pair g'2 (.snd ex2)))))))
  onCh arg ex :=
    .bind (.ret (.pair arg ex))
      (let r0 : Expr OFig _ (.opt (.base .bv256)) := .snd (.snd (.snd (.fst .v0)))
       let ex0 : Expr OFig _ kemExtraTy := .snd .v0
       let g0 : Expr OFig _ fig8GsTy := .fst ex0
       .ite (mWin (fgMir g0))
         (.ret (.pair .none ex0))
         (.bind (samIfNecFig8C P Dh encPt encT decT lam K toKemCoins r0)
           (let bad1 : Expr OFig _ .bool := .snd .v0
            let q1 : Expr OFig _ .bool := .fst (.fst .v1)
            let ex1 : Expr OFig _ kemExtraTy := .snd .v1
            let g1 : Expr OFig _ fig8GsTy := .fst ex1
            .ret
              (.caseOpt (mEpMgmtE (qep + 1) (fgMir g1) q1 bad1)
                (.pair .none ex1)
                (let mir2 : Expr OFig _ (mirTy fig8RecTy) := .v0
                 let coins2 : Expr OFig _ (.base .bv256) := .fst .v1
                 let q2 : Expr OFig _ .bool := .fst (.fst .v2)
                 let m0_2 : Expr OFig _ (lpubPlainTy PQ PQC Pt ℓ) := .fst (.snd (.fst .v2))
                 let m1_2 : Expr OFig _ (lpubPlainTy PQ PQC Pt ℓ) := .fst (.snd (.snd (.fst .v2)))
                 let ex2 : Expr OFig _ kemExtraTy := .snd .v2
                 let g2 : Expr OFig _ fig8GsTy := .fst ex2
                 .ite (.not (mSafeChE mir2 q2))
                   (.pair .none ex2)
                   (let m2 : Expr OFig _ (lpubPlainTy PQ PQC Pt ℓ) :=
                      .ite (mB mir2) m1_2 m0_2
                    let out2 :
                        Expr OFig _ (.prod .bool (.prod (.base .fig8st) (fig8CTy PQ PQC Pt ℓ))) :=
                      Expr.op (O := OFig) (SimOp.fig8SendStep B)
                        (.pair (pGet (fgSt g2) q2) (.some (.pair m2 coins2)))
                    let st'2 : Expr OFig _ (.base .fig8st) := .fst (.snd out2)
                    let c2 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.snd out2)
                    let rec2 : Expr OFig _ fig8RecTy :=
                      .pair
                        (.pair q2
                          (.pair (pGet (mEpoch mir2) q2) (.add (pGet (mIdx mir2) q2) (.nat 1))))
                        (.pair m2 c2)
                    let g'2 : Expr OFig _ fig8GsTy :=
                      .pair (pSet (fgSt g2) q2 st'2) (mRecordE mir2 q2 rec2 (.bool true))
                    .pair (.some c2) (.pair g'2 (.snd ex2))))))))
  onDl arg ex :=
    .ret
      (.letE (.pair arg ex)
        (let q0 : Expr OFig _ .bool := .fst (.fst .v0)
         let c0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.fst .v0)
         let ex0 : Expr OFig _ kemExtraTy := .snd .v0
         let g0 : Expr OFig _ fig8GsTy := .fst ex0
         .ite (mWin (fgMir g0))
           (.pair .none ex0)
           (.caseOpt
             (fgInTransitE P Dh encPt encT decT lam K toKemCoins L (fgMir g0) (otherE q0) c0)
             (.pair .none ex0)
             (let q1 : Expr OFig _ .bool := .fst (.fst .v1)
              let c1 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.fst .v1)
              let ex1 : Expr OFig _ kemExtraTy := .snd .v1
              let g1 : Expr OFig _ fig8GsTy := .fst ex1
              .caseOpt (Expr.op (O := OFig) (SimOp.fig8Receive B) (.pair (pGet (fgSt g1) q1) c1))
                (.pair (.some (.inl .unit)) ex1)
                (let st'2 : Expr OFig _ (.base .fig8st) := .fst .v0
                 let t'2 : Expr OFig _ .nat := .fst (.snd .v0)
                 let i'2 : Expr OFig _ .nat := .fst (.snd (.snd .v0))
                 let m'2 : Expr OFig _ (lpubPlainTy PQ PQC Pt ℓ) := .snd (.snd (.snd .v0))
                 let rPos2 : Expr OFig _ posTy := .fst .v1
                 let q2 : Expr OFig _ .bool := .fst (.fst .v2)
                 let ex2 : Expr OFig _ kemExtraTy := .snd .v2
                 let g2 : Expr OFig _ fig8GsTy := .fst ex2
                 let g'2 : Expr OFig _ fig8GsTy :=
                   .pair (pSet (fgSt g2) q2 st'2) (mAcceptE L (fgMir g2) q2 rPos2)
                 let mOut2 : Expr OFig _ (.opt (lpubPlainTy PQ PQC Pt ℓ)) :=
                   .ite (mChallContainsE L (fgMir g2) rPos2) .none (.some m'2)
                 .pair (.some (.inr (.pair t'2 (.pair i'2 mOut2)))) (.pair g'2 (.snd ex2)))))))
  onIj arg ex :=
    .ret
      (.letE (.pair arg ex)
        (let q0 : Expr OFig _ .bool := .fst (.fst .v0)
         let c0 : Expr OFig _ (fig8CTy PQ PQC Pt ℓ) := .snd (.fst .v0)
         let ex0 : Expr OFig _ kemExtraTy := .snd .v0
         let g0 : Expr OFig _ fig8GsTy := .fst ex0
         let inTr0 : Expr OFig _ (.opt fig8RecTy) :=
           fgInTransitE P Dh encPt encT decT lam K toKemCoins L (fgMir g0) (otherE q0) c0
         .ite (orE (mWin (fgMir g0)) (orE (isSomeE inTr0) (.not (mSafeInjE (fgMir g0)))))
           (.pair .none ex0)
           (.caseOpt (Expr.op (O := OFig) (SimOp.fig8Receive B) (.pair (pGet (fgSt g0) q0) c0))
             (.pair (.some (.inl .unit)) ex0)
             (let st'1 : Expr OFig _ (.base .fig8st) := .fst .v0
              let t'1 : Expr OFig _ .nat := .fst (.snd .v0)
              let i'1 : Expr OFig _ .nat := .fst (.snd (.snd .v0))
              let m'1 : Expr OFig _ (lpubPlainTy PQ PQC Pt ℓ) := .snd (.snd (.snd .v0))
              let q1 : Expr OFig _ .bool := .fst (.fst .v1)
              let ex1 : Expr OFig _ kemExtraTy := .snd .v1
              let g1 : Expr OFig _ fig8GsTy := .fst ex1
              .ite (.lt (.nat (qep + 2)) t'1)
                (.pair (.some (.inl .unit)) ex1)
                (let pos1 : Expr OFig _ posTy := .pair (otherE q1) (.pair t'1 i'1)
                 .ite (mTrivialE L (fgMir g1) pos1)
                   (.pair (.some (.inr (.pair t'1 (.pair i'1 (.some m'1)))))
                     (.pair (.pair (pSet (fgSt g1) q1 st'1) (mAcceptE L (fgMir g1) q1 pos1))
                       (.snd ex1)))
                   (.pair (.some (.inl .unit))
                     (.pair (.pair (fgSt g1) (mSetWin (fgMir g1) (.bool true)))
                       (.snd ex1))))))))
  onCr qB ex :=
    .ret
      (.letE (.pair qB ex)
        (let q0 : Expr OFig _ .bool := .fst .v0
         let ex0 : Expr OFig _ kemExtraTy := .snd .v0
         let g0 : Expr OFig _ fig8GsTy := .fst ex0
         .ite (orE (mWin (fgMir g0)) (.not (mCorrAllowedE L (fgMir g0) q0)))
           (.pair .none ex0)
           (.pair (.some (pGet (fgSt g0) q0))
             (.pair (.pair (fgSt g0) (mAfterCorrE L (fgMir g0) q0)) (.snd ex0)))))
  onProbe _ ex := .ret ex
  onDeliverPost qB j? res ex :=
    .ret
      (.letE (.pair qB (.pair j? (.pair res ex)))
        (let res0 : Expr OFig _ (.opt (simRrTy PQ PQC Pt ℓ)) := .fst (.snd (.snd .v0))
         let ex0 : Expr OFig _ kemExtraTy := .snd (.snd (.snd .v0))
         .caseOpt res0
           ex0
           (.caseSum .v0
             (.snd (.snd (.snd .v2)))
             (let j?2 : Expr OFig _ (.opt .nat) := .fst (.snd .v2)
              let ex2 : Expr OFig _ kemExtraTy := .snd (.snd (.snd .v2))
              .caseOpt j?2
                ex2
                (let j3 : Expr OFig _ .nat := .v0
                 let q3 : Expr OFig _ .bool := .fst .v3
                 let ex3 : Expr OFig _ kemExtraTy := .snd (.snd (.snd .v3))
                 .pair (.fst ex3)
                   (.pair
                     (Expr.op (O := OFig) SimOp.stepKemFailDeliver
                       (.pair (.fst (.snd ex3)) (.pair q3 j3)))
                     (.snd (.snd ex3))))))))

/-- Costed reduction program for `redKemFailHiddenSalt`. -/
@[reducible] def kemFailRedProg (L qep B : ℕ) :
    CostedReduction OFig KIface
      (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (simCodec PQ PQC Pt ℓ) .unit .unit .bool (.base .kemCand) where
  σ := .prod simStateCTy kemExtraTy
  init :=
    .bind (Comp.sample (I := KIface) UniformSamplerTag.bool .unit)
      (.bind (Comp.sample (I := KIface) (UniformSamplerTag.base SimBaseSamp.bv256) .unit)
        (.bind (Comp.sample (I := KIface) (UniformSamplerTag.base SimBaseSamp.bv256) .unit)
          (.bind (Comp.sample (I := KIface) (UniformSamplerTag.base SimBaseSamp.bv256) .unit)
            (let pqrKey : Expr OFig _ (.base .bv256) := .v0
             let k2 : Expr OFig _ (.base .bv256) := .v1
             let k1 : Expr OFig _ (.base .bv256) := .v2
             let b : Expr OFig _ .bool := .v3
             let gFig0 : Expr OFig _ fig8GsTy :=
               .pair (Expr.op (O := OFig) SimOp.fig8Init (.pair k1 k2))
                 (mMk b (.bool false) (.pair (.nat 0) (.nat 0)) (.pair (.nat 0) (.nat 0))
                   .none .nil .nil .nil (.pair (.tconst (.nat 0)) (.tconst (.nat 0))) .nil .nil)
             let trCand0 : Expr OFig _ (.prod (.base .kemTrack) (.base .kemCand)) :=
               Expr.op (O := OFig) SimOp.initKemFailTrack pqrKey
             .ret
               (.pair .unit
                 (.pair (initSimCE P Dh encPt encT decT lam K toKemCoins pqrKey)
                   (.pair gFig0 trCand0)))))))
  handle :=
    simHandleHookC P Dh encPt encT decT lam K toKemCoins
      (kemFailHookC P Dh encPt encT decT lam K toKemCoins L qep B) L qep B
  finish := .ret (.snd (.snd (.snd .v0)))

end SimCProgs

end CryptoGames.Ratchet.LibsignalSim

set_option autoImplicit false

/-! ## Unit-cost simulator tables -/

namespace CryptoGames.Ratchet.LibsignalSim

open ReductionDsl OracleSpec OracleComp
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD SM SM.Construction CKA LibsignalSession
  LibsignalInst

def simDummyMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ := none
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := false

/-- Unit-cost operation table for `Refine.SimProg` and `LibsignalSim.simRunProg`. -/
@[reducible] def simOps {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) :
    Ops (simSig PQ PQC Pt ℓ) :=
  simOpsUnitCost P Dh (fun T => (encT T).1.toList) encT decT (0 : Pt) simDummyMlKem (fun _ => 0)

/-- Unit-cost sampler table for `LibsignalSim.simRun`. -/
@[reducible] def simSamplers (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ) :
    Samplers (simSig PQ PQC Pt ℓ) :=
  simParamSamplers PQ PQC Pt ℓ 1 1

/-- Parametric target Fig. 8 SM oracle interface for `LibsignalSim.simRun`. -/
@[reducible] def simParamIface (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ)
    (cQ cU cSampBv256 cSampPqc : ℕ) :
    Iface (simSig PQ PQC Pt ℓ)
      (unifSpec + SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) where
  fwdU n :=
    query (spec := unifSpec + SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
      (.inl n)
  uCost := cU
  Tag := SMTag
  dom := fun
    | .tr => .prod .bool (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256)))
    | .ch =>
      .prod .bool
        (.prod (lpubPlainTy PQ PQC Pt ℓ)
          (.prod (lpubPlainTy PQ PQC Pt ℓ) (.opt (.base .bv256))))
    | .dl => .prod .bool (fig8CTy PQ PQC Pt ℓ)
    | .ij => .prod .bool (fig8CTy PQ PQC Pt ℓ)
    | .cr => .bool
  cod := fun
    | .tr => .opt (fig8CTy PQ PQC Pt ℓ)
    | .ch => .opt (fig8CTy PQ PQC Pt ℓ)
    | .dl => .opt (fig8RrTy PQ PQC Pt ℓ)
    | .ij => .opt (fig8RrTy PQ PQC Pt ℓ)
    | .cr => .opt (.base .fig8st)
  enc := fun
    | .tr, (p, m, r) => .inr (.inl (.inl (.inl (.inl (partyDec p, m, r)))))
    | .ch, (p, m₀, m₁, r) => .inr (.inl (.inl (.inl (.inr (partyDec p, m₀, m₁, r)))))
    | .dl, (p, c) => .inr (.inl (.inl (.inr (partyDec p, c))))
    | .ij, (p, c) => .inr (.inl (.inr (partyDec p, c)))
    | .cr, p => .inr (.inr (partyDec p))
  dec := fun
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map smRrEnc
    | .ij, _, r => r.map smRrEnc
    | .cr, _, r => r
  qCost := fun _ => cQ
  smp := simParamSamplers PQ PQC Pt ℓ cSampBv256 cSampPqc

/-- Unit-cost target Fig. 8 SM oracle interface for `Refine.SimProg` and `LibsignalSim.simRun`. -/
@[reducible] def simIface (PQ PQC Pt : Type) [SampleableType PQC] (ℓ : ℕ) :
    Iface (simSig PQ PQC Pt ℓ)
      (unifSpec + SM.spec (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) :=
  simParamIface PQ PQC Pt ℓ 1 1 1 1

section SharedStateAndBookkeeping

variable {PQ PQC Pt : Type} {ℓ : ℕ}

local notation "S" => simSig PQ PQC Pt ℓ

def ssSetStopped
    {O' : Ops S} {Γ} (s : Expr O' Γ simStateTy) (stp : Expr O' Γ .bool) :
    Expr O' Γ simStateTy :=
  .letE (.pair s stp)
    (let s0 : Expr O' _ simStateTy := .fst .v0
     ssMk (ssMir s0) (ssPq s0) (ssPn s0) (ssUnackA s0) (ssHonest s0) (ssChains s0)
       (ssAmb s0) (.snd .v0))

end SharedStateAndBookkeeping

end CryptoGames.Ratchet.LibsignalSim
