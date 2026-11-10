/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthPrf
public import Computational.Proofs.SignalPqxdh.Security.CollisionsA
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH `Auth` shared hop interface

Defines the KOSK-aligned hybrid oracles on `AuthHybridStateFixed`, shared post-handshake
decomposition helpers, and the intermediate hop statements and interface bundles for `pqxdh_auth`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-! ## KOSK-aligned hybrid oracle -/

/-- Exact-byte SPK, OPK, and PQSPK provenance check for a pre-key bundle. -/
def checkBundleProvenanceExact (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : Bool × Bool × Bool :=
  match findHonestPrincipal P principals bundle.ikB with
  | none => (false, false, false)
  | some (k, _) =>
    let spkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.spkPk == bundle.spkB)
    let pqspkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon :=
      match bundle.opkB? with
      | none => false
      | some (_, opkPk) =>
        opkEntries.any (fun ((u, _, _), e) =>
          u == k && P.pow8 e.opkPk == P.pow8 opkPk)
    (spkHon, opkHon, pqspkHon)

/-- SPK provenance predicate for `isIdealSend`, relaxing to `pow8` equality on corrupted peers to
    align with `matchSentOPK` and `matchSentNoOPK`. -/
def checkBundleSpkHonIdeal (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) : Bool :=
  match findHonestPrincipal P principals bundle.ikB with
  | none => false
  | some (k, pEntry) =>
    spkBundles.any (fun ((u, _), b) =>
      u == k &&
        ((pEntry.corrupted && P.pow8 b.spkPk == P.pow8 bundle.spkB) || b.spkPk == bundle.spkB))

/-- KOSK-aligned stage-parameterised `send` helper for `Auth` hybrids `G3` through `G5`. -/
def runAuthHybridSendKosk (stage : AuthHybridStage) (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthHybridState S) ProbComp AuthResponse := do
  let hst ← get
  let st := hst.base
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
  let msgPlain :=
    if isFreshPeer then
      if stage.idealFreshAead then m0 else (if st.secb then m1 else m0)
    else
      m0
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
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ←
    if isIdealSend && stage.idealDrKey then do
      let dk ← liftM sampleDRKey96
      pure (dk, st.roCache)
    else
      liftM (evalHkdfOrRo useRo P st.roCache secrets)
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ←
    if isIdealSend && stage.idealRk then do
      let r ← liftM sampleBytes32
      let c ← liftM sampleBytes32
      pure ((r, c), st.rootRoCache)
    else
      liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
  let (mkSeed, ck1_1) ←
    if isIdealSend && stage.idealCk then do
      let ms ← liftM sampleBytes32
      let cn ← liftM sampleBytes32
      pure (ms, cn)
    else
      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return .noneResp
  let deriveMessageKeys ←
    if isIdealSend && stage.idealMsgKeys then
      liftM sampleMessageKeys80
    else
      pure (P.deriveMsgKeys mkSeed spqrSalt?)
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
  let initRec : InitKemRecord S := {
    sid     := sid
    pqspkPk := bundle.pqspkB
    kemCt   := kemCt
    kemSs   := ss
  }
  let idealSessions' :=
    if isIdealSend then
      let idealEntry : IdealAuthSession S := {
        sid          := sid
        ikAPk        := uEntry.ikAPk
        peerIkPk     := bundle.ikB
        peerSpkPk    := bundle.spkB
        peerOpkPk?   := bundle.opkB?.map Prod.snd
        ekAPk        := ekAPk
        peerPqspkPk  := bundle.pqspkB
        kemCt        := kemCt
        ephAPk       := ephAPk
        spqrSalt?    := spqrSalt?
        pqRatchetMsg := pqRatchetMsg
        ad           := ad
        aeadCt       := aeadCt
        msgPlain     := msgPlain
        drKey        := drKey
        rk1          := rk1
        ck1_0        := ck1_0
        mkSeed       := mkSeed
        ck1_1        := ck1_1
        deriveMessageKeys      := deriveMessageKeys
      }
      idealEntry :: hst.idealSessions
    else
      hst.idealSessions
  set { hst with
    base := { st with
      sessions         := sessEntry :: st.sessions
      usedSendSessions := sid :: st.usedSendSessions
      sentOPKEvents    := sentOPK'
      sentNoOPKEvents  := sentNoOPK'
      roCache          := roCache'
      rootRoCache      := rootRoCache' }
    initKemRecs   := initRec :: hst.initKemRecs
    idealSessions := idealSessions' }
  if peerPrincipal?.isSome then
    return .sendFreshResp wireMsg
  else
    return .sendUnfreshResp drKey rk1 ck1_1 wireMsg

/-- KOSK-aligned stage-parameterised `Auth` oracle implementation for hybrids `G3` through `G5`. -/
def pqxdhAuthHybridKoskImpl (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridState S) ProbComp) := fun q => do
  let hst ← get
  let st := hst.base
  if checkAuth && st.hasWonAuth then return .noneResp
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return .noneResp
    runAuthHybridSendKosk stage useRo S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return .noneResp
    runAuthHybridSendKosk stage useRo S P (.sendNoOPK u i) u bundle m0 m1
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
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let rRec : RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
    }
    let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
    set hstDec
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') ←
      liftM (evalAuthHybridRecvSchedule stage useRo P hstDec kEntry bEntry
        (some oEntry.opkPk) secrets msg)
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
        set { hstDec with
          base := { st with
            hasWonAuth       := wonAuth'
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            sentOPKEvents    := sentOPK'
            recvdOPKEvents   := recvEv :: st.recvdOPKEvents
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        return .recvHonestResp
      else
        set { hstDec with
          base := { st with
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        return .recvHonestResp
    | none =>
      set { hstDec with
        base := { st with
          opkEntries       := opkEntries'
          usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' } }
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
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let rRec : RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
    }
    let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
    set hstDec
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') ←
      liftM (evalAuthHybridRecvSchedule stage useRo P hstDec kEntry bEntry none secrets msg)
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
        set { hstDec with
          base := { st with
            hasWonAuth       := wonAuth'
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            sentNoOPKEvents  := sentNoOPK'
            recvdNoOPKEvents := recvEv :: st.recvdNoOPKEvents
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        return .recvHonestResp
      else
        set { hstDec with
          base := { st with
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        return .recvHonestResp
    | none =>
      set { hstDec with
        base := { st with
          usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' } }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | q_other =>
    liftAuthBase (pqxdhAuthImpl useRo checkAuth S P q_other)

/-- Receiver key-schedule and AEAD helper caching `(s.sid, spqrSalt?)` message keys when
    `stage.idealMsgKeys = true`. -/
def evalAuthFixedRecvScheduleCached {S : Setup} (stage : AuthHybridStage) (useRo : Bool)
    (P : Primitives)
    (hst : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    ProbComp
      (Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) ×
      AuthMkSaltCache S) := do
  let st := hst.base
  let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
  let isUncorruptedHonestSender : Bool :=
    match senderPrincipal? with
    | some (_, sEntry) => !sEntry.corrupted
    | none             => false
  let matchedSess? : Option (IdealAuthSession S) :=
    hst.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
  let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
  let (drKey, roCache') ←
    if useIdealBranch && stage.idealDrKey then
      match matchedSess? with
      | some s => pure (s.drKey, st.roCache)
      | none   => do
        let dk ← sampleDRKey96
        pure (dk, st.roCache)
    else
      evalHkdfOrRo useRo P st.roCache secrets
  let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
  let sameEph : Bool :=
    match matchedSess? with
    | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
    | none   => false
  let ((rk1, ck1_0), rootRoCache') ←
    if useIdealBranch && stage.idealRk then
      match matchedSess? with
      | some s =>
        if sameEph then pure ((s.rk1, s.ck1_0), st.rootRoCache)
        else do
          let r ← sampleBytes32
          let c ← sampleBytes32
          pure ((r, c), st.rootRoCache)
      | none => do
        let r ← sampleBytes32
        let c ← sampleBytes32
        pure ((r, c), st.rootRoCache)
    else
      evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet
  let (mkSeed, ck1_1) ←
    if useIdealBranch && stage.idealCk then
      match matchedSess? with
      | some s =>
        if sameEph then pure (s.mkSeed, s.ck1_1)
        else do
          let ms ← sampleBytes32
          let cn ← sampleBytes32
          pure (ms, cn)
      | none => do
        let ms ← sampleBytes32
        let cn ← sampleBytes32
        pure (ms, cn)
    else
      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => return (none, mkSaltCache)
  | some (_pqrStB, spqrSalt?) =>
    let sameMsgKeys : Bool :=
      match matchedSess? with
      | some s => sameEph && (sameSaltKey spqrSalt? s.spqrSalt?)
      | none   => false
    let (deriveMessageKeys, mkSaltCache') ←
      if useIdealBranch && stage.idealMsgKeys then
        match matchedSess? with
        | some s =>
          if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache)
          else if sameEph then
            match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some (_, (_, mk)) => pure (mk, mkSaltCache)
            | none => do
              let mk ← sampleMessageKeys80
              pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
          else do
            let mk ← sampleMessageKeys80
            pure (mk, mkSaltCache)
        | none => do
          let mk ← sampleMessageKeys80
          pure (mk, mkSaltCache)
      else
        pure (P.deriveMsgKeys mkSeed spqrSalt?, mkSaltCache)
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let pt? : Option Bytes :=
      if useIdealBranch then
        if sameMsgKeys && stage.idealFreshAead then
          match matchedSess? with
          | some s => if ad == s.ad && msg.aeadCt == s.aeadCt then some s.msgPlain else none
          | none   => none
        else if !sameMsgKeys && isUncorruptedHonestSender && stage.idealUnmatchedRecvAead then
          none
        else
          P.aeadDec deriveMessageKeys ad msg.aeadCt
      else
        P.aeadDec deriveMessageKeys ad msg.aeadCt
    match pt? with
    | none    => return (none, mkSaltCache')
    | some pt => return (some (drKey, rk1, ck1_1, pt, roCache', rootRoCache'), mkSaltCache')

/-- Stage-parameterised `Auth` oracle on `AuthHybridStateFixed S`, caching `(s.sid, spqrSalt?)`
    message keys up to `effectiveHkdfSaltBytes` (`mkSaltKeyMatch`, DEV-LS25) when
    `stage.idealMsgKeys = true`. -/
def pqxdhAuthHybridFixedImpl (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) := fun q => do
  let hst ← get
  if !stage.idealMsgKeys then
    let (resp, hst') ←
      liftM ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst.toAuthHybridState)
    let recvCount' := if isAuthRecvQuery (.inr q) then hst.recvCount + 1 else hst.recvCount
    set ({ toAuthHybridState := hst', recvCount := recvCount',
           mkSaltCache := hst.mkSaltCache } : AuthHybridStateFixed S)
    return resp
  else
    let st := hst.toAuthHybridState.base
    match q with
    | .recvOPK k j o msg =>
      let recvCount' := hst.recvCount + 1
      if checkAuth && st.hasWonAuth then
        set { hst with recvCount := recvCount' }
        return .noneResp
      if !(msg.hdr.spkId == UInt32.ofNat j.val &&
           msg.hdr.pqspkId == UInt32.ofNat j.val &&
           msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
           msg.hdr.ikAPk.length == 32 &&
           msg.hdr.ekAPk.length == 32 &&
           msg.ephAPk.length == 32) then
        set { hst with recvCount := recvCount' }
        return .noneResp
      if st.usedRecvOPK.contains (k.val, j.val, o.val) then
        set { hst with recvCount := recvCount' }
        return .noneResp
      if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
        set { hst with recvCount := recvCount' }
        return .noneResp
      let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
        | set { hst with recvCount := recvCount' }; return .noneResp
      let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
        | set { hst with recvCount := recvCount' }; return .noneResp
      let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
        | set { hst with recvCount := recvCount' }; return .noneResp
      if oEntry.consumed then
        set { hst with recvCount := recvCount' }
        return .noneResp
      let (replayOk, usedTriples') :=
        checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
        set { hst with recvCount := recvCount' }
        return .noneResp
      let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt
        | set { hst with recvCount := recvCount' }; return .noneResp
      let rRec : RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
      }
      let hstDec := {
        hst.toAuthHybridState with recvKemRecs := rRec :: hst.toAuthHybridState.recvKemRecs }
      let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
      let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
      let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
      let (res?, mkSaltCache') ←
        liftM (evalAuthFixedRecvScheduleCached stage useRo P hstDec hst.recvCount hst.mkSaltCache
          kEntry bEntry (some oEntry.opkPk) secrets msg)
      let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') := res?
        | set ({ toAuthHybridState := hstDec, recvCount := recvCount',
                 mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
          return .noneResp
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
          let hst' : AuthHybridState S := { hstDec with
            base := { st with
              hasWonAuth       := wonAuth'
              opkEntries       := opkEntries'
              usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
              seenKyberBaseKeys := usedTriples'
              sentOPKEvents    := sentOPK'
              recvdOPKEvents   := recvEv :: st.recvdOPKEvents
              roCache          := roCache'
              rootRoCache      := rootRoCache' } }
          set ({ toAuthHybridState := hst', recvCount := recvCount',
                 mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
          return .recvHonestResp
        else
          let hst' : AuthHybridState S := { hstDec with
            base := { st with
              opkEntries       := opkEntries'
              usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
              seenKyberBaseKeys := usedTriples'
              roCache          := roCache'
              rootRoCache      := rootRoCache' } }
          set ({ toAuthHybridState := hst', recvCount := recvCount',
                 mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
          return .recvHonestResp
      | none =>
        let hst' : AuthHybridState S := { hstDec with
          base := { st with
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        set ({ toAuthHybridState := hst', recvCount := recvCount',
               mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
        return .recvUnfreshResp drKey rk1 ck1_1 pt
    | .recvNoOPK k j l msg =>
      let recvCount' := hst.recvCount + 1
      if checkAuth && st.hasWonAuth then
        set { hst with recvCount := recvCount' }
        return .noneResp
      if !(msg.hdr.spkId == UInt32.ofNat j.val &&
           msg.hdr.pqspkId == UInt32.ofNat j.val &&
           msg.hdr.opkId? == none &&
           msg.hdr.ikAPk.length == 32 &&
           msg.hdr.ekAPk.length == 32 &&
           msg.ephAPk.length == 32) then
        set { hst with recvCount := recvCount' }
        return .noneResp
      if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
        set { hst with recvCount := recvCount' }
        return .noneResp
      if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
        set { hst with recvCount := recvCount' }
        return .noneResp
      let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
        | set { hst with recvCount := recvCount' }; return .noneResp
      let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
        | set { hst with recvCount := recvCount' }; return .noneResp
      let (replayOk, usedTriples') :=
        checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
        set { hst with recvCount := recvCount' }
        return .noneResp
      let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt
        | set { hst with recvCount := recvCount' }; return .noneResp
      let rRec : RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
      }
      let hstDec := {
        hst.toAuthHybridState with recvKemRecs := rRec :: hst.toAuthHybridState.recvKemRecs }
      let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
      let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
      let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
      let secrets := buildSecrets dh1 dh2 dh3 none ss
      let (res?, mkSaltCache') ←
        liftM (evalAuthFixedRecvScheduleCached stage useRo P hstDec hst.recvCount hst.mkSaltCache
          kEntry bEntry none secrets msg)
      let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') := res?
        | set ({ toAuthHybridState := hstDec, recvCount := recvCount',
                 mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
          return .noneResp
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
          let hst' : AuthHybridState S := { hstDec with
            base := { st with
              hasWonAuth       := wonAuth'
              usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
              seenKyberBaseKeys := usedTriples'
              sentNoOPKEvents  := sentNoOPK'
              recvdNoOPKEvents := recvEv :: st.recvdNoOPKEvents
              roCache          := roCache'
              rootRoCache      := rootRoCache' } }
          set ({ toAuthHybridState := hst', recvCount := recvCount',
                 mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
          return .recvHonestResp
        else
          let hst' : AuthHybridState S := { hstDec with
            base := { st with
              usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
              seenKyberBaseKeys := usedTriples'
              roCache          := roCache'
              rootRoCache      := rootRoCache' } }
          set ({ toAuthHybridState := hst', recvCount := recvCount',
                 mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
          return .recvHonestResp
      | none =>
        let hst' : AuthHybridState S := { hstDec with
          base := { st with
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        set ({ toAuthHybridState := hst', recvCount := recvCount',
               mkSaltCache := mkSaltCache' } : AuthHybridStateFixed S)
        return .recvUnfreshResp drKey rk1 ck1_1 pt
    | qOther =>
      let (resp, hst') ←
        liftM ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P qOther).run hst.toAuthHybridState)
      let recvCount' := if isAuthRecvQuery (.inr qOther) then hst.recvCount + 1 else hst.recvCount
      set ({ toAuthHybridState := hst', recvCount := recvCount',
             mkSaltCache := hst.mkSaltCache } : AuthHybridStateFixed S)
      return resp

theorem map_toAuthHybridState_pqxdhAuthHybridFixedImpl (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    Prod.map id AuthHybridStateFixed.toAuthHybridState <$>
      (pqxdhAuthHybridFixedImpl stage useRo checkAuth S P q).run hst =
    (pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst.toAuthHybridState := by
  simp [pqxdhAuthHybridFixedImpl, hStage, StateT.run_bind, Prod.map]

theorem map_toAuthHybridState_fullAuthHybridFixedImpl (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    Prod.map id AuthHybridStateFixed.toAuthHybridState <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
        pqxdhAuthHybridFixedImpl stage useRo checkAuth S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl stage useRo checkAuth S P) q).run hst.toAuthHybridState := by
  cases q with
  | inl uq =>
    simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq =>
    exact map_toAuthHybridState_pqxdhAuthHybridFixedImpl stage useRo checkAuth S P kq hst hStage

/-- Stage experiment for `Auth` running `pqxdhAuthHybridKoskImpl` on `AuthHybridState S`. -/
noncomputable def authKoskExpAtStage (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
    pqxdhAuthHybridKoskImpl stage true true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.base.principals s)
  if hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt ||
     hasKemPkCollisionAuth finalSt || hasBadKemShCrAuth P finalSt then
    $ᵗ Bool
  else if finalSt.base.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == secb)

/-- Stage experiment for `Auth` running `pqxdhAuthHybridFixedImpl` on `AuthHybridStateFixed S`. -/
noncomputable def authFixedExpAtStage (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
    pqxdhAuthHybridFixedImpl stage true true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
  if hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
     hasBadSigAuth finalSt.toAuthHybridState ||
     hasKemPkCollisionAuth finalSt.toAuthHybridState ||
     hasBadKemShCrAuth P finalSt.toAuthHybridState then
    $ᵗ Bool
  else if finalSt.toAuthHybridState.base.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == secb)

theorem authFixedExpAtStage_eq_authKoskExpAtStage (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    authFixedExpAtStage stage S P A = authKoskExpAtStage stage S P A := by
  unfold authFixedExpAtStage authKoskExpAtStage
  apply bind_congr; intro secb
  have hsim := _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthHybridStateFixed.toAuthHybridState
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridFixedImpl stage true true S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl stage true true S P)
    (fun q hst => map_toAuthHybridState_fullAuthHybridFixedImpl stage true true S P q hst hStage)
    A.run (AuthHybridStateFixed.empty S secb)
  dsimp only [AuthHybridStateFixed.empty] at hsim ⊢
  rw [← hsim, bind_map_left]
  rfl

noncomputable def authKoskAdvAtStage (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[authKoskExpAtStage stage S P A].boolBias).toReal

noncomputable def authFixedAdvAtStage (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpAtStage stage S P A].boolBias).toReal

theorem authFixedAdvAtStage_eq_authKoskAdvAtStage (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    authFixedAdvAtStage stage S P A = authKoskAdvAtStage stage S P A := by
  unfold authFixedAdvAtStage authKoskAdvAtStage
  rw [authFixedExpAtStage_eq_authKoskExpAtStage stage S P A hStage]

/-- Idealised `Auth` execution branch on `AuthHybridStateFixed S` (`stage = .g5`, `checkAuth =
    false`), where every fresh session encrypts `m0` and unmatched honest-sender `recv` branches
    reject. -/
noncomputable def authFixedIdealBranch (useRo : Bool) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let initSt := AuthHybridStateFixed.empty S false
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
    pqxdhAuthHybridFixedImpl .g5 useRo false S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P useRo finalSt.toAuthHybridState.base.principals s)
  if !allChallengedClean ||
     hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
     hasBadSigAuth finalSt.toAuthHybridState ||
     hasKemPkCollisionAuth finalSt.toAuthHybridState ||
     hasBadKemShCrAuth P finalSt.toAuthHybridState then
    $ᵗ Bool
  else
    return b'

noncomputable def authFixedExpG3 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage .g3 S P A

noncomputable def authFixedExpG3_5 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage .g3_5 S P A

noncomputable def authFixedExpG3_6 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage .g3_6 S P A

noncomputable def authFixedExpG3_7 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage .g3_7 S P A

noncomputable def authFixedExpG3_8 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage .g3_8 S P A

noncomputable def authFixedExpG5 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let z ← if secb then authFixedIdealBranch true S P A else authFixedIdealBranch true S P A
  return (secb == z)

noncomputable def authFixedAdvG3 (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3 S P A].boolBias).toReal

noncomputable def authFixedAdvG3_5 (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_5 S P A].boolBias).toReal

noncomputable def authFixedAdvG3_6 (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_6 S P A].boolBias).toReal

noncomputable def authFixedAdvG3_7 (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_7 S P A].boolBias).toReal

noncomputable def authFixedAdvG3_8 (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_8 S P A].boolBias).toReal

noncomputable def authFixedAdvG5 (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG5 S P A].boolBias).toReal

@[simp]
theorem authFixedAdvG5_eq_zero (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authFixedAdvG5 S P A = 0 := by
  unfold authFixedAdvG5 authFixedExpG5
  rw [evalDist_boolBias_bind_uniformBool, Measure.boolDist_self, ENNReal.toReal_zero]

/-! ## Post-handshake decomposition helpers -/

/-- Finalizes an `Auth` hybrid game execution from `(b', finalSt)`. -/
noncomputable def finalizeAuthGame {S : Setup} {σ : Type} [HasAuthState σ S]
    (useRo checkAuth : Bool) (S_param : Setup) (P : Primitives)
    (b' : Bool) (finalSt : AuthHybridState S) : ProbComp Bool := do
  let _ := S_param
  let st := finalSt.base
  let allChallengedClean := st.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P useRo st.principals s)
  if hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt ||
     hasKemPkCollisionAuth finalSt || hasBadKemShCrAuth P finalSt then
    $ᵗ Bool
  else if checkAuth && st.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == st.secb)

/-- Complete a `sendOPK` / `sendNoOPK` state transition on `AuthHybridState S` once the handshake
    keys, message keys, and ciphertext have been derived. -/
def finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S) : AuthResponse × AuthHybridState S :=
  let st := hst.base
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
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
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
  let initRec : InitKemRecord S := {
    sid     := sid
    pqspkPk := bundle.pqspkB
    kemCt   := kemCt
    kemSs   := ss
  }
  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let idealSessions' :=
    if isIdealSend then
      let idealEntry : IdealAuthSession S := {
        sid          := sid
        ikAPk        := uEntry.ikAPk
        peerIkPk     := bundle.ikB
        peerSpkPk    := bundle.spkB
        peerOpkPk?   := bundle.opkB?.map Prod.snd
        ekAPk        := ekAPk
        peerPqspkPk  := bundle.pqspkB
        kemCt        := kemCt
        ephAPk       := ephAPk
        spqrSalt?    := spqrSalt?
        pqRatchetMsg := pqRatchetMsg
        ad           := ad
        aeadCt       := aeadCt
        msgPlain     := msgPlain
        drKey        := drKey
        rk1          := rk1
        ck1_0        := ck1_0
        mkSeed       := mkSeed
        ck1_1        := ck1_1
        deriveMessageKeys      := deriveMessageKeys
      }
      idealEntry :: hst.idealSessions
    else
      hst.idealSessions
  let hst' : AuthHybridState S := { hst with
    base := { st with
      sessions         := sessEntry :: st.sessions
      usedSendSessions := sid :: st.usedSendSessions
      sentOPKEvents    := sentOPK'
      sentNoOPKEvents  := sentNoOPK'
      roCache          := roCache'
      rootRoCache      := rootRoCache' }
    initKemRecs   := initRec :: hst.initKemRecs
    idealSessions := idealSessions' }
  let resp :=
    if peerPrincipal?.isSome then
      AuthResponse.sendFreshResp wireMsg
    else
      AuthResponse.sendUnfreshResp drKey rk1 ck1_1 wireMsg
  (resp, hst')

def finishAuthHybridRecvOPK {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    AuthResponse × AuthHybridState S :=
  let st := hstDec.base
  match res? with
  | none => (.noneResp, hstDec)
  | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
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
        (.recvHonestResp, { hstDec with
          base := { st with
            hasWonAuth       := wonAuth'
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            sentOPKEvents    := sentOPK'
            recvdOPKEvents   := recvEv :: st.recvdOPKEvents
            roCache          := roCache'
            rootRoCache      := rootRoCache' } })
      else
        (.recvHonestResp, { hstDec with
          base := { st with
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } })
    | none =>
      (.recvUnfreshResp drKey rk1 ck1_1 pt, { hstDec with
        base := { st with
          opkEntries       := opkEntries'
          usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' } })

def finishAuthHybridRecvNoOPK {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    AuthResponse × AuthHybridState S :=
  let st := hstDec.base
  match res? with
  | none => (.noneResp, hstDec)
  | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
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
        (.recvHonestResp, { hstDec with
          base := { st with
            hasWonAuth       := wonAuth'
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            sentNoOPKEvents  := sentNoOPK'
            recvdNoOPKEvents := recvEv :: st.recvdNoOPKEvents
            roCache          := roCache'
            rootRoCache      := rootRoCache' } })
      else
        (.recvHonestResp, { hstDec with
          base := { st with
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } })
    | none =>
      (.recvUnfreshResp drKey rk1 ck1_1 pt, { hstDec with
        base := { st with
          usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' } })

/-- Parsed and validated context for an incoming `recvOPK` or `recvNoOPK` query in
    `AuthHybridState S`. -/
structure PreparedAuthRecv (S : Setup) where
  kEntry                    : PrincipalEntry
  bEntry                    : SpkBundleEntry
  opkPk?                    : Option Bytes
  secrets                   : Bytes
  dhRatchet                 : Bytes
  isUncorruptedHonestSender : Bool
  matchedSess?              : Option (IdealAuthSession S)
  sameEph                   : Bool
  hstDec                    : AuthHybridState S
  finish                    : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
                                List ((Bytes × Bytes) × (Bytes × Bytes))) →
                              AuthResponse × AuthHybridState S

/-- Validates and prepares a `recvOPK k j o msg` query on `hst : AuthHybridState S`. -/
def prepareAuthHybridRecvOPK {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : Option (PreparedAuthRecv S) :=
  let st := hst.base
  if checkAuth && st.hasWonAuth then
    none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    none
  else if st.usedRecvOPK.contains (k.val, j.val, o.val) then
    none
  else if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
    none
  else
    match st.principals.find? (fun (idx, _) => idx == k.val),
          st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)),
          st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
    | some (_, kEntry), some (_, bEntry), some (_, oEntry) =>
      if oEntry.consumed then none
      else
        let (replayOk, usedTriples') :=
          checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val
            msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
        if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
        else
          match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => none
          | some ss =>
            let rRec : RecvKemRecord := {
              k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
              pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
            }
            let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
            let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
            let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
            let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
            let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
            let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
            let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
            let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
            let isUncorruptedHonestSender : Bool :=
              match senderPrincipal? with
              | some (_, sEntry) => !sEntry.corrupted
              | none             => false
            let matchedSess? : Option (IdealAuthSession S) :=
              hstDec.idealSessions.find?
                (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk
                  (some oEntry.opkPk) bEntry.pqspkPk msg.hdr)
            let sameEph : Bool :=
              match matchedSess? with
              | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
              | none   => false
            some {
              kEntry                    := kEntry
              bEntry                    := bEntry
              opkPk?                    := some oEntry.opkPk
              secrets                   := secrets
              dhRatchet                 := dhRatchet
              isUncorruptedHonestSender := isUncorruptedHonestSender
              matchedSess?              := matchedSess?
              sameEph                   := sameEph
              hstDec                    := hstDec
              finish                    := finishAuthHybridRecvOPK checkAuth P k j o
                                             kEntry bEntry oEntry usedTriples' msg hstDec
            }
    | _, _, _ => none

/-- Validates and prepares a `recvNoOPK k j l msg` query on `hst : AuthHybridState S`. -/
def prepareAuthHybridRecvNoOPK {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : Option (PreparedAuthRecv S) :=
  let st := hst.base
  if checkAuth && st.hasWonAuth then
    none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    none
  else if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    none
  else if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
    none
  else
    match st.principals.find? (fun (idx, _) => idx == k.val),
          st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | some (_, kEntry), some (_, bEntry) =>
      let (replayOk, usedTriples') :=
        checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
      else
        match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => none
        | some ss =>
          let rRec : RecvKemRecord := {
            k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
            pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
          }
          let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
          let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
          let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
          let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
          let secrets := buildSecrets dh1 dh2 dh3 none ss
          let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
          let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
          let isUncorruptedHonestSender : Bool :=
            match senderPrincipal? with
            | some (_, sEntry) => !sEntry.corrupted
            | none             => false
          let matchedSess? : Option (IdealAuthSession S) :=
            hstDec.idealSessions.find?
              (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr)
          let sameEph : Bool :=
            match matchedSess? with
            | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
            | none   => false
          some {
            kEntry                    := kEntry
            bEntry                    := bEntry
            opkPk?                    := none
            secrets                   := secrets
            dhRatchet                 := dhRatchet
            isUncorruptedHonestSender := isUncorruptedHonestSender
            matchedSess?              := matchedSess?
            sameEph                   := sameEph
            hstDec                    := hstDec
            finish                    := finishAuthHybridRecvNoOPK checkAuth P k j l
                                           kEntry bEntry usedTriples' msg hstDec
          }
    | _, _ => none

theorem abs_sub_le_sum_range_postHandshake (N : Nat) (H : Nat → ℝ) :
    |H 0 - H N| ≤ ∑ i ∈ Finset.range N, |H i - H (i + 1)| := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      |H 0 - H (n + 1)| = |(H 0 - H n) + (H n - H (n + 1))| := by ring_nf
      _ ≤ |H 0 - H n| + |H n - H (n + 1)| := abs_add_le _ _
      _ ≤ (∑ i ∈ Finset.range n, |H i - H (i + 1)|) + |H n - H (n + 1)| :=
        add_le_add ih le_rfl

/-! ## Hop statements and interface bundles -/

/-- Pre-key and handshake hop `G0 → G3` (`SigEufCma`, EC/KEM collision bounds, and `KemShCr`). -/
def AuthHopG0G3Stmt (S : Setup)
    (sig : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → SigEufCmaAdv)
    (shcr : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → KemShCrAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |AuthAdvantageReal S P A.1 - authFixedAdvG3 S P A.1| ≤
        (S.N_id : ℝ) * SigEufCma P (sig b A) +
        ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcr b A) +
        ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256

/-- Sub-hop `G3.5 → G3.6`: `RootKdfRO` replacement on fresh and unmatched honest-sender sessions. -/
def AuthHopG3_5G3_6Stmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_5 S P A.1 - authFixedAdvG3_6 S P A.1| ≤
        rootKdfRoTermReal S b.q_roRoot

/-- Sub-hop `G3.6 → G3.7`: `PrfChainKey` replacement across `S.N_sess_tot` sessions. -/
def AuthHopG3_6G3_7Stmt (S : Setup)
    (ck : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfCkAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_6 S P A.1 - authFixedAdvG3_7 S P A.1| ≤
        2 * (S.N_sess_tot : ℝ) * PrfChainKeyReal P (ck b A)

/-- Sub-hop `G3.7 → G3.8`: `PrfMsgKeys` replacement across `S.N_sess_tot` sessions. -/
def AuthHopG3_7G3_8Stmt (S : Setup)
    (mk : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfMsgKeysAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_7 S P A.1 - authFixedAdvG3_8 S P A.1| ≤
        2 * (S.N_sess_tot : ℝ) * PrfMsgKeysReal P (mk b A)

/-- Combined sub-hops `G3.8 → G5`: IND-CPA and multi-key INT-CTXT of the first-message AEAD. -/
def AuthHopG3_8G5Stmt (S : Setup)
    (cpa : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadIndCpaAdv)
    (int : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadMuIntCtxtAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_8 S P A.1 - authFixedAdvG5 S P A.1| ≤
        2 * (S.N_send_tot : ℝ) * AeadIndCpaReal P (cpa b A) +
        2 * AeadMuIntCtxt P (int b A)

/-- Interface bundle for AEAD reductions (`cpa`, `int`), query bounds, and `G3.8 → G5`. -/
structure AuthSubHops4to5Bundle (S : Setup) where
  cpa              : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadIndCpaAdv
  int              : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadMuIntCtxtAdv
  int_queries      : ∀ b A, (int b A).q_dec ≤ S.N_recv_tot
  int_enc_queries  : ∀ b A, (int b A).q_enc ≤ S.N_send_tot
  cpa_prim_queries : ∀ b A, (cpa b A).q_prim ≤ primQueryBudget S b
  int_prim_queries : ∀ b A, (int b A).q_prim ≤ primQueryBudget S b
  hop_G3_8_G5      : AuthHopG3_8G5Stmt S cpa int

end SignalPqxdh.Security
