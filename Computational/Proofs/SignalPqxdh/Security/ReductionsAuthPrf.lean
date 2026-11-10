/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndSigKem

/-!
# Black-Box Reductions for PQXDH `Auth`: Key-Schedule PRF Simulators

**Checked by Lean.** Shallow reduction simulators (`prfCkReductionAuthFixed` and
`prfMsgKeysReductionAuthFixed`) for the chain-key and message-key PRF game hops of the PQXDH
`Auth` security game.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open RoKem

/-! ## Shared hybrid state and `PrimBaseSpec` helpers -/

abbrev AuthMkSaltCache (S : Setup) := List ((SessionId S × Option Bytes) × (Nat × MessageKeys))

/-- Salt equivalence up to 32-byte HKDF salt normalization (`effectiveHkdfSaltBytes`, DEV-LS25). -/
def sameSaltKey (s₁ s₂ : Option Bytes) : Bool := effectiveHkdfSaltBytes s₁ == effectiveHkdfSaltBytes s₂

def mkSaltKeyMatch {S : Setup} (k : SessionId S × Option Bytes) (sid : SessionId S)
    (salt? : Option Bytes) : Bool :=
  k.1 == sid && sameSaltKey k.2 salt?

/-- Creation-order hybrid slot table: `nextSlot` counter plus nested lookup tables
    for `.sendOPK u i`, `.sendNoOPK u i`, and responder `rc`. -/
structure AuthSlotState where
  nextSlot     : Nat := 0
  sendOpkTbl   : Nat → Nat → Option Nat := fun _ _ => none
  sendNoOpkTbl : Nat → Nat → Option Nat := fun _ _ => none
  recvTbl      : Nat → Option Nat := fun _ => none

def AuthSlotState.empty : AuthSlotState := {}

def AuthSlotState.lookupSend {S : Setup} (ss : AuthSlotState) : SessionId S → Option Nat
  | .sendOPK u i => ss.sendOpkTbl u.1 i.1
  | .sendNoOPK u i => ss.sendNoOpkTbl u.1 i.1
  | _ => none

def AuthSlotState.lookupSendOrZero {S : Setup} (ss : AuthSlotState) (sid : SessionId S) : Nat :=
  (ss.lookupSend sid).getD 0

def AuthSlotState.allocSend {S : Setup} (ss : AuthSlotState) :
    SessionId S → Nat × AuthSlotState
  | .sendOPK u i =>
    match ss.sendOpkTbl u.1 i.1 with
    | some k => (k, ss)
    | none =>
      let k := ss.nextSlot
      let row := ss.sendOpkTbl u.1
      let row' := fun j => if j = i.1 then some k else row j
      (k, { ss with
        nextSlot := k + 1
        sendOpkTbl := fun u' => if u' = u.1 then row' else ss.sendOpkTbl u' })
  | .sendNoOPK u i =>
    match ss.sendNoOpkTbl u.1 i.1 with
    | some k => (k, ss)
    | none =>
      let k := ss.nextSlot
      let row := ss.sendNoOpkTbl u.1
      let row' := fun j => if j = i.1 then some k else row j
      (k, { ss with
        nextSlot := k + 1
        sendNoOpkTbl := fun u' => if u' = u.1 then row' else ss.sendNoOpkTbl u' })
  | _ => (0, ss)

def AuthSlotState.lookupRecv (ss : AuthSlotState) (rc : Nat) : Option Nat :=
  ss.recvTbl rc

def AuthSlotState.lookupRecvOrZero (ss : AuthSlotState) (rc : Nat) : Nat :=
  (ss.recvTbl rc).getD 0

def AuthSlotState.allocRecv (ss : AuthSlotState) (rc : Nat) : Nat × AuthSlotState :=
  match ss.recvTbl rc with
  | some k => (k, ss)
  | none =>
    let k := ss.nextSlot
    (k, { ss with
      nextSlot := k + 1
      recvTbl := fun r' => if r' = rc then some k else ss.recvTbl r' })

/-- `AuthHybridState S` extended with receiver query counter, salt cache, and creation-order slot table. -/
structure AuthHybridStateFixed (S : Setup) extends AuthHybridState S where
  recvCount   : Nat := 0
  mkSaltCache : AuthMkSaltCache S := []
  slots       : AuthSlotState := {}

def AuthHybridStateFixed.empty (S : Setup) (secb : Bool) : AuthHybridStateFixed S :=
  { toAuthHybridState := AuthHybridState.empty S secb
    recvCount := 0
    mkSaltCache := []
    slots := {} }

namespace AuthSubHops1to3

def evalHkdfRoPure (roCache : List (Bytes × DRKey))
    (secrets : Bytes) : ProbComp (DRKey × List (Bytes × DRKey)) :=
  match roCache.find? (fun (s, _) => s == secrets) with
  | some (_, dk) => pure (dk, roCache)
  | none => do
    let dk ← sampleDRKey96
    pure (dk, (secrets, dk) :: roCache)

def evalRootKdfRoPure (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (rk dh : Bytes) : ProbComp ((Bytes × Bytes) × List ((Bytes × Bytes) × (Bytes × Bytes))) :=
  match rootRoCache.find? (fun (k, _) => k == (rk, dh)) with
  | some (_, out) => pure (out, rootRoCache)
  | none => do
    let r ← sampleBytes32
    let c ← sampleBytes32
    pure ((r, c), ((rk, dh), (r, c)) :: rootRoCache)

def mapMPrim {α β : Type} (f : α → OracleComp PrimBaseSpec β) :
    List α → OracleComp PrimBaseSpec (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapMPrim f xs
    pure (y :: ys)

def consumeFirstMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (mark : α → α) :
    List α → OracleComp PrimBaseSpec (Bool × List α)
  | [] => pure (false, [])
  | x :: xs => do
    if ← p x then
      pure (true, mark x :: xs)
    else
      let (ok, xs') ← consumeFirstMPrim p mark xs
      pure (ok, x :: xs')

def matchSentOPKPrim (r : RecvdOPKEvent) (s : SentOPKEvent) : OracleComp PrimBaseSpec Bool := do
  let pa0r ← primQ (.pow8 r.a0)
  let pa0s ← primQ (.pow8 s.a0)
  let pb0r ← primQ (.pow8 r.b0)
  let pb0s ← primQ (.pow8 s.b0)
  let pobr ← primQ (.pow8 r.ob)
  let pobs ← primQ (.pow8 s.ob)
  let pa1r ← primQ (.pow8 r.a1)
  let pa1s ← primQ (.pow8 s.a1)
  let psbr ← primQ (.pow8 r.sb)
  let psbs ← primQ (.pow8 s.sb)
  return (!s.matched &&
    pa0r == pa0s &&
    pb0r == pb0s &&
    pobr == pobs &&
    pa1r == pa1s &&
    psbr == psbs &&
    (r.bCorr || r.sb == s.sb) &&
    r.pk1 == s.pk1 &&
    r.ct == s.ct &&
    r.m == s.m)

def matchSentNoOPKPrim (r : RecvdNoOPKEvent) (s : SentNoOPKEvent) :
    OracleComp PrimBaseSpec Bool := do
  let pa0r ← primQ (.pow8 r.a0)
  let pa0s ← primQ (.pow8 s.a0)
  let pb0r ← primQ (.pow8 r.b0)
  let pb0s ← primQ (.pow8 s.b0)
  let pa1r ← primQ (.pow8 r.a1)
  let pa1s ← primQ (.pow8 s.a1)
  let psbr ← primQ (.pow8 r.sb)
  let psbs ← primQ (.pow8 s.sb)
  return (!s.matched &&
    pa0r == pa0s &&
    pb0r == pb0s &&
    pa1r == pa1s &&
    psbr == psbs &&
    (r.bCorr || r.sb == s.sb) &&
    r.pk1 == s.pk1 &&
    r.ct == s.ct &&
    r.m == s.m)

def checkBundleProvenanceExactPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec (Bool × Bool × Bool) := do
  match ← findHonestPrincipalPrim S principals bundle.ikB with
  | none => return (false, false, false)
  | some (k, _) =>
    let spkHon := spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB)
    let pqspkHon := spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon ←
      match bundle.opkB? with
      | none => pure false
      | some (_, opkPk) =>
        anyMPrim (fun ((u, _, _), e) => do
          let p1 ← primQ (.pow8 e.opkPk)
          let p2 ← primQ (.pow8 opkPk)
          return (u == k && p1 == p2)) (opkEntries.take S.N_dh)
    return (spkHon, opkHon, pqspkHon)

def checkBundleSpkHonIdealPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec Bool := do
  match ← findHonestPrincipalPrim S principals bundle.ikB with
  | none => return false
  | some (k, pEntry) =>
    anyMPrim (fun ((u, _), b) => do
      let p1 ← primQ (.pow8 b.spkPk)
      let p2 ← primQ (.pow8 bundle.spkB)
      return (u == k && ((pEntry.corrupted && p1 == p2) || b.spkPk == bundle.spkB)))
      (spkBundles.take S.N_dh)

def sameOpkPkPrim (o1 o2 : Option Bytes) : OracleComp PrimBaseSpec Bool :=
  match o1, o2 with
  | none, none => return true
  | some pk1, some pk2 => do
    let p1 ← primQ (.pow8 pk1)
    let p2 ← primQ (.pow8 pk2)
    return (p1 == p2)
  | _, _ => return false

def matchIdealAuthHandshakePrim {S : Setup}
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) : OracleComp PrimBaseSpec Bool := do
  let pIk1 ← primQ (.pow8 hdr.ikAPk)
  let pIk2 ← primQ (.pow8 s.ikAPk)
  let pPeerIk1 ← primQ (.pow8 ikBPk)
  let pPeerIk2 ← primQ (.pow8 s.peerIkPk)
  let pSpk1 ← primQ (.pow8 spkBPk)
  let pSpk2 ← primQ (.pow8 s.peerSpkPk)
  let opkOk ← sameOpkPkPrim opkBPk? s.peerOpkPk?
  let pEk1 ← primQ (.pow8 hdr.ekAPk)
  let pEk2 ← primQ (.pow8 s.ekAPk)
  return (pIk1 == pIk2 &&
          pPeerIk1 == pPeerIk2 &&
          pSpk1 == pSpk2 &&
          opkOk &&
          pEk1 == pEk2 &&
          pqspkBPk == s.peerPqspkPk &&
          hdr.kemCt == s.kemCt)

def allHonestEcPksAuthPrim (S : Setup) (st : AuthState S) :
    OracleComp PrimBaseSpec (List Bytes) := do
  let p1 ← mapMPrim (fun (_, e) => primQ (.pow8 e.ikAPk)) (st.principals.take S.N_dh)
  let p2 ← mapMPrim (fun (_, b) => primQ (.pow8 b.spkPk)) (st.spkBundles.take S.N_dh)
  let p3 ← mapMPrim (fun (_, o) => primQ (.pow8 o.opkPk)) (st.opkEntries.take S.N_dh)
  let p4 ← mapMPrim (fun s => do
    let pk ← primQ (.x25519Base s.ekASk)
    primQ (.pow8 pk)) (st.sessions.take S.N_dh)
  return (p1 ++ p2 ++ p3 ++ p4)

def hasBadKemShCrRecordsPure {S : Setup}
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord) : Bool :=
  initRecs.any (fun i =>
    recvRecs.any (fun r =>
      r.kemSs == i.kemSs &&
      (r.kemCt != i.kemCt || i.pqspkPk != r.pqspkPk)))


def allChallengedCleanPure {S : Setup} (st : AuthState S) : Bool :=
  st.sessions.all (fun s => !s.challenged || (s.fresh && s.pqspkHonest))

def finalizeAuthFixedPrim (S : Setup) (secb b' : Bool) (finalSt : AuthHybridState S) :
    OracleComp PrimBaseSpec Bool := do
  let ecPks ← allHonestEcPksAuthPrim S finalSt.base
  if hasDuplicateBytes ecPks || hasBadSigAuth finalSt ||
     hasKemPkCollisionAuth finalSt ||
     hasBadKemShCrRecordsPure finalSt.initKemRecs finalSt.recvKemRecs then
    embedUnif ($ᵗ Bool)
  else if finalSt.base.hasWonAuth then
    return true
  else if !allChallengedCleanPure finalSt.base then
    embedUnif ($ᵗ Bool)
  else
    return (b' == secb)

inductive RecvFinishTag (S : Setup) where
  | opk (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
        (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
        (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
        (hstDec : AuthHybridState S)
  | noOpk (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
          (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
          (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
          (hstDec : AuthHybridState S)

def RecvFinishTag.hstDec {S : Setup} : RecvFinishTag S → AuthHybridState S
  | .opk _ _ _ _ _ _ _ _ hstDec => hstDec
  | .noOpk _ _ _ _ _ _ _ hstDec => hstDec

def RecvFinishTag.mapState {S : Setup} (f : AuthHybridState S → AuthHybridState S) :
    RecvFinishTag S → RecvFinishTag S
  | .opk k j o kEntry bEntry oEntry usedTriples' msg hstDec =>
    .opk k j o kEntry bEntry oEntry usedTriples' msg (f hstDec)
  | .noOpk k j l kEntry bEntry usedTriples' msg hstDec =>
    .noOpk k j l kEntry bEntry usedTriples' msg (f hstDec)

def RecvFinishTag.runPrim (S : Setup) (checkAuth : Bool) (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridState S) :=
  match tag with
  | .opk k j o kEntry bEntry oEntry usedTriples' msg hstDec => do
    let st := hstDec.base
    match res? with
    | none => return (.noneResp, hstDec)
    | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
      let opkEntries' := st.opkEntries.map (fun (idx, e) =>
        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
      match ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk with
      | some (_, senderEntry) =>
        if !senderEntry.corrupted then
          let recvEv : RecvdOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
          }
          let (matchedOk, sentOPK') ←
            consumeFirstMPrim (matchSentOPKPrim recvEv) (fun s => { s with matched := true })
              (st.sentOPKEvents.take S.N_dh)
          let wonAuth' := st.hasWonAuth || (checkAuth && !matchedOk)
          return (.recvHonestResp, { hstDec with
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
          return (.recvHonestResp, { hstDec with
            base := { st with
              opkEntries       := opkEntries'
              usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
              seenKyberBaseKeys := usedTriples'
              roCache          := roCache'
              rootRoCache      := rootRoCache' } })
      | none =>
        return (.recvUnfreshResp drKey rk1 ck1_1 pt, { hstDec with
          base := { st with
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } })
  | .noOpk k j l kEntry bEntry usedTriples' msg hstDec => do
    let st := hstDec.base
    match res? with
    | none => return (.noneResp, hstDec)
    | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
      match ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk with
      | some (_, senderEntry) =>
        if !senderEntry.corrupted then
          let recvEv : RecvdNoOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
          }
          let (matchedOk, sentNoOPK') ←
            consumeFirstMPrim (matchSentNoOPKPrim recvEv) (fun s => { s with matched := true })
              (st.sentNoOPKEvents.take S.N_dh)
          let wonAuth' := st.hasWonAuth || (checkAuth && !matchedOk)
          return (.recvHonestResp, { hstDec with
            base := { st with
              hasWonAuth       := wonAuth'
              usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
              seenKyberBaseKeys := usedTriples'
              sentNoOPKEvents  := sentNoOPK'
              recvdNoOPKEvents := recvEv :: st.recvdNoOPKEvents
              roCache          := roCache'
              rootRoCache      := rootRoCache' } })
        else
          return (.recvHonestResp, { hstDec with
            base := { st with
              usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
              seenKyberBaseKeys := usedTriples'
              roCache          := roCache'
              rootRoCache      := rootRoCache' } })
      | none =>
        return (.recvUnfreshResp drKey rk1 ck1_1 pt, { hstDec with
          base := { st with
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } })

structure PreparedAuthRecvPrim (S : Setup) where
  kEntry                    : PrincipalEntry
  bEntry                    : SpkBundleEntry
  opkPk?                    : Option Bytes
  secrets                   : Bytes
  dhRatchet                 : Bytes
  isUncorruptedHonestSender : Bool
  matchedSess?              : Option (IdealAuthSession S)
  sameEph                   : Bool
  hstDec                    : AuthHybridState S
  finishTag                 : RecvFinishTag S

def PreparedAuthRecvPrim.mapState {S : Setup} (f : AuthHybridState S → AuthHybridState S)
    (p : PreparedAuthRecvPrim S) : PreparedAuthRecvPrim S :=
  { p with hstDec := f p.hstDec, finishTag := p.finishTag.mapState f }

def prepareAuthHybridRecvOPKPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : OracleComp PrimBaseSpec (Option (PreparedAuthRecvPrim S)) := do
  let st := hst.base
  if st.hasWonAuth then
    return none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    return none
  else if st.usedRecvOPK.contains (k.val, j.val, o.val) then
    return none
  else
    let koskOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
    if !koskOk then
      return none
    else
      match st.principals.find? (fun (idx, _) => idx == k.val),
            st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)),
            st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | some (_, kEntry), some (_, bEntry), some (_, oEntry) =>
        if oEntry.consumed then return none
        else
          let (replayOk, usedTriples') :=
            checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
            msg.hdr.ekAPk
          let canon ← primQ (.isCanonical msg.hdr.ekAPk)
          let canonEph ← primQ (.isCanonical msg.ephAPk)
          if !replayOk || !canon || !canonEph then return none
          else
            match ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt) with
            | none => return none
            | some ss =>
              let rRec : RecvKemRecord := {
                k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
              }
              let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
              let dh1 ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
              let dh2 ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
              let dh3 ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
              let dh4 ← primQ (.x25519 oEntry.opkSk msg.hdr.ekAPk)
              let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
              let dhRatchet ← primQ (.x25519 bEntry.spkSk msg.ephAPk)
              let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
              let isUncorruptedHonestSender : Bool :=
                match senderPrincipal? with
                | some (_, sEntry) => !sEntry.corrupted
                | none             => false
              let matchedSess? ←
                findMPrim
                  (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
                    bEntry.pqspkPk msg.hdr)
                  (hstDec.idealSessions.take S.N_dh)
              let sameEph ←
                match matchedSess? with
                | some s => do
                  let p1 ← primQ (.pow8 msg.ephAPk)
                  let p2 ← primQ (.pow8 s.ephAPk)
                  pure (p1 == p2)
                | none => pure false
              return some {
                kEntry := kEntry, bEntry := bEntry, opkPk? := some oEntry.opkPk,
                secrets := secrets, dhRatchet := dhRatchet,
                isUncorruptedHonestSender := isUncorruptedHonestSender,
                matchedSess? := matchedSess?, sameEph := sameEph, hstDec := hstDec,
                finishTag := .opk k j o kEntry bEntry oEntry usedTriples' msg hstDec }
      | _, _, _ => return none

def prepareAuthHybridRecvNoOPKPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : OracleComp PrimBaseSpec (Option (PreparedAuthRecvPrim S)) := do
  let st := hst.base
  if st.hasWonAuth then
    return none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    return none
  else if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    return none
  else
    let koskOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
    if !koskOk then
      return none
    else
      match st.principals.find? (fun (idx, _) => idx == k.val),
            st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | some (_, kEntry), some (_, bEntry) =>
        let (replayOk, usedTriples') :=
          checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
            msg.hdr.ekAPk
        let canon ← primQ (.isCanonical msg.hdr.ekAPk)
        let canonEph ← primQ (.isCanonical msg.ephAPk)
        if !replayOk || !canon || !canonEph then return none
        else
          match ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt) with
          | none => return none
          | some ss =>
            let rRec : RecvKemRecord := {
              k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
              pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
            }
            let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
            let dh1 ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
            let dh2 ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
            let dh3 ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
            let secrets := buildSecrets dh1 dh2 dh3 none ss
            let dhRatchet ← primQ (.x25519 bEntry.spkSk msg.ephAPk)
            let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
            let isUncorruptedHonestSender : Bool :=
              match senderPrincipal? with
              | some (_, sEntry) => !sEntry.corrupted
              | none             => false
            let matchedSess? ←
              findMPrim
                (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr)
                (hstDec.idealSessions.take S.N_dh)
            let sameEph ←
              match matchedSess? with
              | some s => do
                let p1 ← primQ (.pow8 msg.ephAPk)
                let p2 ← primQ (.pow8 s.ephAPk)
                pure (p1 == p2)
              | none => pure false
            return some {
              kEntry := kEntry, bEntry := bEntry, opkPk? := none,
              secrets := secrets, dhRatchet := dhRatchet,
              isUncorruptedHonestSender := isUncorruptedHonestSender,
              matchedSess? := matchedSess?, sameEph := sameEph, hstDec := hstDec,
              finishTag := .noOpk k j l kEntry bEntry usedTriples' msg hstDec }
      | _, _ => return none

def finishAuthHybridSendPrim (S : Setup)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S) : OracleComp PrimBaseSpec (AuthResponse × AuthHybridState S) := do
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
  let (spkHon, opkHon, pqspkHon) ←
    checkBundleProvenanceExactPrim S st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal ←
    checkBundleSpkHonIdealPrim S st.principals st.spkBundles bundle
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
  return (resp, hst')

def stepAuthOtherPrim (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    return (.noneResp, hst)
  else
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, hst)
    else
      let secIKA0 ← embedUnif sampleScalar32
      let ikAPk ← primQ (.x25519Base secIKA0)
      let secIKAsign ← embedUnif sampleScalar32
      let ikSignPk ← primQ (.sigPkGen secIKAsign)
      let entry : PrincipalEntry := {
        secIKA0    := secIKA0
        ikAPk      := ikAPk
        secIKAsign := secIKAsign
        ikSignPk   := ikSignPk
        corrupted  := false
      }
      let base' := { st with principals := (u.val, entry) :: st.principals }
      return (.initPrinResp ikAPk ikSignPk,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .corruptIK u =>
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, hst)
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      let base' := { st with principals := principals' }
      return (.corrResp entry.secIKA0 entry.secIKAsign,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .genSPK u j =>
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, hst)
    else
      match st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => return (.noneResp, hst)
      | some (_, uEntry) =>
        let spkSk ← embedUnif sampleScalar32
        let spkPk ← primQ (.x25519Base spkSk)
        let rSpk ← embedUnif sampleRandom64
        let spkSig ← primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
        let (pqspkPk, pqspkSk) ← sampleKemKeyGenPrim
        let rPq ← embedUnif sampleRandom64
        let pqspkSig ← primQ (.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq)
        let bEntry : SpkBundleEntry := {
          spkSk    := spkSk
          spkPk    := spkPk
          spkSig   := spkSig
          pqspkSk  := pqspkSk
          pqspkPk  := pqspkPk
          pqspkSig := pqspkSig
        }
        let base' := { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
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
        return (.bundleResp bundleOut,
          { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .genOPK u j o =>
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return (.noneResp, hst)
    else
      let opkSk ← embedUnif sampleScalar32
      let opkPk ← primQ (.x25519Base opkSk)
      let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
      let base' := { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
      return (.pkResp opkPk,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .registerKey sk =>
    if sk.length != 32 then
      return (.noneResp, hst)
    else
      let pk ← primQ (.x25519Base sk)
      let p8 ← primQ (.pow8 pk)
      let base' := { st with advKeys := (p8, pk) :: st.advKeys }
      return (.pkResp pk,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .roQuery secrets =>
    let (dk, roCache') ← embedUnif (evalHkdfRoPure st.roCache secrets)
    let base' := { st with roCache := roCache' }
    return (.drKeyResp dk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .roRootQuery rk dh =>
    let (out, rootRoCache') ← embedUnif (evalRootKdfRoPure st.rootRoCache rk dh)
    let base' := { st with rootRoCache := rootRoCache' }
    return (.rootKdfResp out.1 out.2,
      { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .revealDhSecrets =>
    return (.noneResp, hst)
  | .sendOPK _ _ _ _ _ =>
    return (.noneResp, hst)
  | .sendNoOPK _ _ _ _ _ =>
    return (.noneResp, hst)
  | .recvOPK _ _ _ _ =>
    return (.noneResp, hst)
  | .recvNoOPK _ _ _ _ =>
    return (.noneResp, hst)

/-! ## `PrfChainKey` simulator -/

def finishAuthSendCkPrim (S : Setup)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  let mkSeed := p.1
  let ck1_1 := p.2
  let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlain)
  let (resp, hst') ← finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain st.roCache st.rootRoCache
    hst.toAuthHybridState
  return (resp, { toAuthHybridState := hst', recvCount := hst.recvCount, slots := hst.slots })

def finishAuthRecvCkSlotsPrim (S : Setup)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) (slots' : AuthSlotState) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := prep.hstDec.base
  let mkSeed := p.1
  let ck1_1 := p.2
  let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
  let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  let pt? ← primQ (.aeadDec deriveMessageKeys ad msg.aeadCt)
  let res? := pt?.map (fun pt =>
    (drKey, rk1, ck1_1, pt, st.roCache, st.rootRoCache))
  let (resp, hst') ← prep.finishTag.runPrim S true res?
  return (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := slots' })

def finishAuthRecvCkPrim (S : Setup)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) :=
  finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? recvCount' p {}

def sampCkPairPrim (ideal : Bool) : OracleComp PrimBaseSpec (Bytes × Bytes) := do
  let ck ← embedUnif sampleBytes32
  if ideal then do
    let r1 ← embedUnif sampleBytes32
    let r2 ← embedUnif sampleBytes32
    return (r1, r2)
  else do
    let mkSeed ← primQ (.chainKdfSeed ck)
    let ck1_1 ← primQ (.chainKdfNext ck)
    return (mkSeed, ck1_1)

def sampAtCkPrim (idx : Nat) (p : Bytes × Bytes) (s : Nat) :
    OracleComp PrimBaseSpec (Bytes × Bytes) :=
  if s == idx then pure p else sampCkPairPrim (s < idx)

def authCkSendWithPrim (S : Setup) (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    return (.noneResp, hst)
  else if m0.length != m1.length then
    return (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    return (.noneResp, hst)
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? ← findHonestPrincipalPrim S st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        return (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
        if !koskOk then
          return (.noneResp, hst)
        else
          let ekASk ← embedUnif sampleScalar32
          let kemCoins ← embedUnif sampleCoins32
          let ephASk ← embedUnif sampleScalar32
          let spqrCoins ← embedUnif sampleCoins32
          let sigPkB ← resolveSigPkPrim S st.principals bundle.ikB
          let v1 ← primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
          let v2 ← primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
          if !(v1 && v2) then
            return (.noneResp, hst)
          else
            match ← primQ (.kemEncaps bundle.pqspkB kemCoins) with
            | none => return (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk ← primQ (.x25519Base ekASk)
              let ephAPk ← primQ (.x25519Base ephASk)
              let spkHonIdeal ← checkBundleSpkHonIdealPrim S st.principals st.spkBundles bundle
              let pqspkHon : Bool :=
                (peerPrincipal?.map (fun p =>
                  st.spkBundles.any
                    (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
              if isIdealSend then
                let drKey ← embedUnif sampleDRKey96
                let rk1 ← embedUnif sampleBytes32
                match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
                | none => return (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let (sIdx, slots') := hst.slots.allocSend sid
                  let p ← sampAt sIdx
                  finishAuthSendCkPrim S sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain { hst with slots := slots' } p
              else
                let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
                let dh2 ← primQ (.x25519 ekASk bundle.ikB)
                let dh3 ← primQ (.x25519 ekASk bundle.spkB)
                let dh4? ←
                  Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                    let d4 ← primQ (.x25519 ekASk opkPk)
                    pure (some d4))
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← embedUnif (evalHkdfRoPure st.roCache secrets)
                let dhRatchet ← primQ (.x25519 ephASk bundle.spkB)
                let ((rk1, ck1_0), rootRoCache') ←
                  embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet)
                let mkSeed ← primQ (.chainKdfSeed ck1_0)
                let ck1_1 ← primQ (.chainKdfNext ck1_0)
                match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
                | none => return (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlain)
                  let (resp, hst') ←
                    finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  return (resp, { toAuthHybridState := hst', recvCount := hst.recvCount,
                                  slots := hst.slots })

def authCkRecvWithPrim (S : Setup) (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => return (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match ← primQ (.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg) with
          | none =>
            let (resp, hst') ← prep.finishTag.runPrim S true none
            return (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            finishAuthRecvCkSlotsPrim S msg prep s.drKey s.rk1 spqrSalt? recvCount'
              (s.mkSeed, s.ck1_1) hst.slots
        else
          let rk1 ← embedUnif sampleBytes32
          match ← primQ (.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg) with
          | none =>
            let (resp, hst') ← prep.finishTag.runPrim S true none
            return (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            let p ← sampAt rSlot
            finishAuthRecvCkSlotsPrim S msg prep s.drKey rk1 spqrSalt? recvCount' p slots'
      | none =>
        let drKey ← embedUnif sampleDRKey96
        let rk1 ← embedUnif sampleBytes32
        match ← primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg) with
        | none =>
          let (resp, hst') ← prep.finishTag.runPrim S true none
          return (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          let p ← sampAt rSlot
          finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? recvCount' p slots'
    else
      let (drKey, roCache') ← embedUnif (evalHkdfRoPure st.roCache prep.secrets)
      let ((rk1, ck1_0), rootRoCache') ←
        embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey prep.dhRatchet)
      let mkSeed ← primQ (.chainKdfSeed ck1_0)
      let ck1_1 ← primQ (.chainKdfNext ck1_0)
      match ← primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg) with
      | none =>
        let (resp, hst') ← prep.finishTag.runPrim S true none
        return (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let pt? ← primQ (.aeadDec deriveMessageKeys ad msg.aeadCt)
        let res? := pt?.map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') ← prep.finishTag.runPrim S true res?
        return (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })

def authCkStepWithPrim (S : Setup) (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendWithPrim S sampAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendWithPrim S sampAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg => do
    let prep? ← prepareAuthHybridRecvOPKPrim S k j o msg hst.toAuthHybridState
    authCkRecvWithPrim S sampAt msg prep? hst
  | .recvNoOPK k j l msg => do
    let prep? ← prepareAuthHybridRecvNoOPKPrim S k j l msg hst.toAuthHybridState
    authCkRecvWithPrim S sampAt msg prep? hst
  | qOther =>
    stepAuthOtherPrim S qOther hst

def runWithPrimStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp PrimBaseSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp PrimBaseSpec (α × St))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u s
      | Sum.inr gq => do
        let x ← step gq s
        r x.1 x.2)
    mx st

def authCkPreSampleRunPrim (S : Setup) (idx : Nat)
    (p : Bytes × Bytes) (A : AuthAdversary S) : OracleComp PrimBaseSpec Bool := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt := AuthHybridStateFixed.empty S secb
  let (b', finalSt) ←
    runWithPrimStep (authCkStepWithPrim S (sampAtCkPrim idx p)) A.run initSt
  finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState

/-- `PrfChainKey` reduction for `Auth` embedding the challenge pair at a uniformly sampled creation-order slot. -/
def prfCkReductionAuthFixed (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfCkAdv where
  dist mkSeedChal ck1_1Chal := do
    let idx ← embedUnif (sampleIndexRange (min b.q_total S.N_sess_tot))
    authCkPreSampleRunPrim S idx (mkSeedChal, ck1_1Chal) A.1
  q_prf := 1
  q_prim := b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5

/-! ## `PrfMsgKeys` simulator -/

def finishAuthSendMkPrim (S : Setup) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlain)
  let (resp, hst') ← finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain st.roCache st.rootRoCache
    hst.toAuthHybridState
  return (resp, { toAuthHybridState := hst', recvCount := hst.recvCount,
                  mkSaltCache := hst.mkSaltCache, slots := hst.slots })

inductive PreparedAuthSend (S : Setup) where
  | done (resp : AuthResponse) (hst' : AuthHybridStateFixed S)
  | idealMk
      (uEntry : PrincipalEntry)
      (peerPrincipal? : Option (Nat × PrincipalEntry))
      (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
      (drKey : DRKey) (rk1 : Bytes)
      (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
def PreparedAuthSend.mapState {S : Setup} (f : AuthHybridStateFixed S → AuthHybridStateFixed S) :
    PreparedAuthSend S → PreparedAuthSend S
  | .done resp hst' => .done resp (f hst')
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain

def prepareAuthSendMkPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : OracleComp PrimBaseSpec (PreparedAuthSend S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    return .done .noneResp hst
  else if m0.length != m1.length then
    return .done .noneResp hst
  else if st.usedSendSessions.contains sid then
    return .done .noneResp hst
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return .done .noneResp hst
    | some (_, uEntry) =>
      let peerPrincipal? ← findHonestPrincipalPrim S st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        return .done .noneResp hst
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
        if !koskOk then
          return .done .noneResp hst
        else
          let ekASk ← embedUnif sampleScalar32
          let kemCoins ← embedUnif sampleCoins32
          let ephASk ← embedUnif sampleScalar32
          let spqrCoins ← embedUnif sampleCoins32
          let sigPkB ← resolveSigPkPrim S st.principals bundle.ikB
          let v1 ← primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
          let v2 ← primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
          if !(v1 && v2) then
            return .done .noneResp hst
          else
            match ← primQ (.kemEncaps bundle.pqspkB kemCoins) with
            | none => return .done .noneResp hst
            | some (ss, kemCt) =>
              let ekAPk ← primQ (.x25519Base ekASk)
              let ephAPk ← primQ (.x25519Base ephASk)
              let spkHonIdeal ← checkBundleSpkHonIdealPrim S st.principals st.spkBundles bundle
              let pqspkHon : Bool :=
                (peerPrincipal?.map (fun p =>
                  st.spkBundles.any (fun ((u, _), b) => u == p.1 && b.pqspkPk ==
                    bundle.pqspkB))).getD false
              let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal &&
                pqspkHon)
              if isIdealSend then
                let drKey ← embedUnif sampleDRKey96
                let rk1 ← embedUnif sampleBytes32
                match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
                | none => return .done .noneResp hst
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  return .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
                    drKey rk1 spqrSalt? pqRatchetMsg msgPlain
              else
                let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
                let dh2 ← primQ (.x25519 ekASk bundle.ikB)
                let dh3 ← primQ (.x25519 ekASk bundle.spkB)
                let dh4? ←
                  Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                    let d4 ← primQ (.x25519 ekASk opkPk)
                    pure (some d4))
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← embedUnif (evalHkdfRoPure st.roCache secrets)
                let dhRatchet ← primQ (.x25519 ephASk bundle.spkB)
                let ((rk1, ck1_0), rootRoCache') ←
                  embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet)
                let mkSeed ← primQ (.chainKdfSeed ck1_0)
                let ck1_1 ← primQ (.chainKdfNext ck1_0)
                match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
                | none => return .done .noneResp hst
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlain)
                  let (resp, hst') ← finishAuthHybridSendPrim S sid uEntry peerPrincipal?
                    isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  return .done resp { toAuthHybridState := hst', recvCount := hst.recvCount,
                                      mkSaltCache := hst.mkSaltCache, slots := hst.slots }

def finishAuthRecvMkSlotsPrim (S : Setup) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState)
    (deriveMessageKeys : MessageKeys) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := prep.hstDec.base
  let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  let pt? ← primQ (.aeadDec deriveMessageKeys ad msg.aeadCt)
  let res? := pt?.map (fun pt => (drKey, rk1, ck1_1, pt, st.roCache, st.rootRoCache))
  let (resp, hst') ← prep.finishTag.runPrim S true res?
  return (resp, { toAuthHybridState := hst', recvCount := recvCount',
                  mkSaltCache := mkSaltCache', slots := slots' })

def finishAuthRecvMkPrim (S : Setup) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) :=
  finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' {} deriveMessageKeys

abbrev PrfMkSimSpec : OracleSpec ((ℕ ⊕ PrimQuery) ⊕ PrfMsgKeysQuery) :=
  PrimBaseSpec + prfMsgKeysSpec
abbrev embedPrimMk {α : Type} (mx : OracleComp PrimBaseSpec α) : OracleComp PrfMkSimSpec α :=
  embedPrim (spec := prfMsgKeysSpec) mx
abbrev embedUnifMk {α : Type} (mx : ProbComp α) : OracleComp PrfMkSimSpec α :=
  embedPrimMk (embedUnif mx)
def deriveMkQ (spqrSalt? : Option Bytes) : OracleComp PrfMkSimSpec MessageKeys :=
  query (spec := PrfMkSimSpec) (Sum.inr (.derive (effectiveHkdfSaltBytes spqrSalt?)))

def authMkSendReduction (S : Setup) (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    OracleComp PrfMkSimSpec ((AuthResponse × AuthHybridStateFixed S) × Bool) := do
  match ← embedPrimMk (prepareAuthSendMkPrim S sid u bundle m0 m1 hst) with
  | .done resp hst' => return ((resp, hst'), sentChal)
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    let (sIdx, slots') := hst.slots.allocSend sid
    let hst' := { hst with slots := slots' }
    if !sentChal && (sIdx == idx) then
      let ck1_1 ← embedUnifMk sampleBytes32
      let deriveMessageKeys ← deriveMkQ spqrSalt?
      let res ← embedPrimMk (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys)
      return (res, true)
    else if decide (sIdx < idx) then
      let ck1_1 ← embedUnifMk sampleBytes32
      let deriveMessageKeys ← embedUnifMk sampleMessageKeys80
      let res ← embedPrimMk (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys)
      return (res, sentChal)
    else
      let mkSeed ← embedUnifMk sampleBytes32
      let ck1_1 ← embedUnifMk sampleBytes32
      let deriveMessageKeys ← embedPrimMk (primQ (.deriveMsgKeys mkSeed spqrSalt?))
      let res ← embedPrimMk (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys)
      return (res, sentChal)

def finishAuthRecvUnmatchedSlotsReduction (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) :
    OracleComp PrfMkSimSpec (AuthResponse × AuthHybridStateFixed S) := do
  if rSlot == idx then
    let ck1_1 ← embedUnifMk sampleBytes32
    let deriveMessageKeys ←
      if !sentChal then deriveMkQ spqrSalt?
      else embedUnifMk sampleMessageKeys80
    embedPrimMk (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots' deriveMessageKeys)
  else if decide (rSlot < idx) then
    let ck1_1 ← embedUnifMk sampleBytes32
    let deriveMessageKeys ← embedUnifMk sampleMessageKeys80
    embedPrimMk (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots' deriveMessageKeys)
  else
    let mkSeed ← embedUnifMk sampleBytes32
    let ck1_1 ← embedUnifMk sampleBytes32
    let deriveMessageKeys ← embedPrimMk (primQ (.deriveMsgKeys mkSeed spqrSalt?))
    embedPrimMk (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots' deriveMessageKeys)

def finishAuthRecvUnmatchedReduction (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (sentChal : Bool) :
    OracleComp PrfMkSimSpec (AuthResponse × AuthHybridStateFixed S) :=
  finishAuthRecvUnmatchedSlotsReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount' mkSaltCache {} sentChal

def matchedSameEphMkSlotsReduction (S : Setup) (idx : Nat) (s : IdealAuthSession S) (sIdx : Nat)
    (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    OracleComp PrfMkSimSpec (MessageKeys × List ((SessionId S × Option Bytes) ×
                                                  (Nat × MessageKeys))) :=
  if sIdx == idx then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure (s.deriveMessageKeys, mkSaltCache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure (mk, mkSaltCache)
      | none => do
        let mk ← deriveMkQ spqrSalt?
        pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
  else if decide (sIdx < idx) then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure (s.deriveMessageKeys, mkSaltCache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure (mk, mkSaltCache)
      | none => do
        let mk ← embedUnifMk sampleMessageKeys80
        pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
  else do
    let mk ← embedPrimMk (primQ (.deriveMsgKeys s.mkSeed spqrSalt?))
    pure (mk, mkSaltCache)

def matchedSameEphMkReduction (S : Setup) (idx : Nat) (s : IdealAuthSession S)
    (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    OracleComp PrfMkSimSpec (MessageKeys × List ((SessionId S × Option Bytes) ×
                                                  (Nat × MessageKeys))) :=
  matchedSameEphMkSlotsReduction S idx s (sessionSlotIndex s.sid) spqrSalt? recvCount mkSaltCache

def authMkRecvReduction (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    OracleComp PrfMkSimSpec (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => return (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match ← embedPrimMk (primQ (.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg)) with
          | none =>
            let (resp, hst') ← embedPrimMk (prep.finishTag.runPrim S true none)
            return (resp, { toAuthHybridState := hst', recvCount := recvCount',
                            mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let sIdx := hst.slots.lookupSendOrZero s.sid
            let p ← matchedSameEphMkSlotsReduction S idx s sIdx spqrSalt? hst.recvCount hst.mkSaltCache
            embedPrimMk (finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 recvCount'
              p.2 hst.slots p.1)
        else
          let rk1 ← embedUnifMk sampleBytes32
          match ← embedPrimMk (primQ (.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg)) with
          | none =>
            let (resp, hst') ← embedPrimMk (prep.finishTag.runPrim S true none)
            return (resp, { toAuthHybridState := hst', recvCount := recvCount',
                            mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            finishAuthRecvUnmatchedSlotsReduction S idx msg prep s.drKey rk1 spqrSalt? rSlot recvCount'
              hst.mkSaltCache slots' sentChal
      | none =>
        let drKey ← embedUnifMk sampleDRKey96
        let rk1 ← embedUnifMk sampleBytes32
        match ← embedPrimMk (primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg)) with
        | none =>
          let (resp, hst') ← embedPrimMk (prep.finishTag.runPrim S true none)
          return (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache, slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          finishAuthRecvUnmatchedSlotsReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
            hst.mkSaltCache slots' sentChal
    else
      let (drKey, roCache') ← embedUnifMk (evalHkdfRoPure st.roCache prep.secrets)
      let ((rk1, ck1_0), rootRoCache') ← embedUnifMk (evalRootKdfRoPure st.rootRoCache drKey.rootKey
                                                       prep.dhRatchet)
      let mkSeed ← embedPrimMk (primQ (.chainKdfSeed ck1_0))
      let ck1_1 ← embedPrimMk (primQ (.chainKdfNext ck1_0))
      match ← embedPrimMk (primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg)) with
      | none =>
        let (resp, hst') ← embedPrimMk (prep.finishTag.runPrim S true none)
        return (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache, slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys ← embedPrimMk (primQ (.deriveMsgKeys mkSeed spqrSalt?))
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let pt? ← embedPrimMk (primQ (.aeadDec deriveMessageKeys ad msg.aeadCt))
        let res? := pt?.map (fun pt => (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') ← embedPrimMk (prep.finishTag.runPrim S true res?)
        return (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache, slots := hst.slots })

def authMkStepReduction (S : Setup) (idx : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    OracleComp PrfMkSimSpec (((authSpec S).Range q × AuthHybridStateFixed S) × Bool) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure ((.noneResp, hst), sentChal)
    else authMkSendReduction S idx (.sendOPK u i) u bundle m0 m1 hst sentChal
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure ((.noneResp, hst), sentChal)
    else authMkSendReduction S idx (.sendNoOPK u i) u bundle m0 m1 hst sentChal
  | .recvOPK k j o msg => do
    let prep? ← embedPrimMk (prepareAuthHybridRecvOPKPrim S k j o msg hst.toAuthHybridState)
    let res ← authMkRecvReduction S idx msg prep? hst sentChal
    return (res, sentChal)
  | .recvNoOPK k j l msg => do
    let prep? ← embedPrimMk (prepareAuthHybridRecvNoOPKPrim S k j l msg hst.toAuthHybridState)
    let res ← authMkRecvReduction S idx msg prep? hst sentChal
    return (res, sentChal)
  | qOther => do
    let res ← embedPrimMk (stepAuthOtherPrim S qOther hst)
    return (res, sentChal)
def runWithPrfMkStep {S : Setup} {α : Type}
    (step : (q : AuthQuery S) → AuthHybridStateFixed S → Bool →
      OracleComp PrfMkSimSpec (((authSpec S).Range q × AuthHybridStateFixed S) × Bool))
    (mx : OracleComp (unifSpec + authSpec S) α) (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    OracleComp PrfMkSimSpec ((α × AuthHybridStateFixed S) × Bool) :=
  OracleComp.construct
    (C := fun _ => AuthHybridStateFixed S → Bool →
      OracleComp PrfMkSimSpec ((α × AuthHybridStateFixed S) × Bool))
    (fun a s c => pure ((a, s), c)) (fun q _ r s c =>
      match q with
      | .inl uq => do
        let u ← embedUnifMk (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u s c
      | .inr gq => do
        let ((resp, s'), c') ← step gq s c
        r resp s' c')
    mx hst sentChal

def authMkReductionRun (S : Setup) (idx : Nat) (A : AuthAdversary S) :
    OracleComp PrfMkSimSpec Bool := do
  let secb ← embedUnifMk ($ᵗ Bool)
  let initSt := AuthHybridStateFixed.empty S secb
  let ((b', finalSt), _sentChal) ←
    runWithPrfMkStep (authMkStepReduction S idx) A.run initSt false
  embedPrimMk (finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState)

/-- `PrfMsgKeys` reduction for `Auth` forwarding message-key derivations at a uniformly sampled creation-order slot. -/
def prfMsgKeysReductionAuthFixed (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfMsgKeysAdv where
  run := do
    let idx ← embedUnifMk (sampleIndexRange (min b.q_total S.N_sess_tot))
    authMkReductionRun S idx A.1
  q_prf := S.N_recv_tot + 1
  q_prim := b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5

end AuthSubHops1to3

export AuthSubHops1to3 (
  prfCkReductionAuthFixed
  prfMsgKeysReductionAuthFixed
)

end SignalPqxdh.Security
