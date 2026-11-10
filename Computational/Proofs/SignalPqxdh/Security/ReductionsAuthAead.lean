/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthPrf
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh

/-!
# Black-Box Reductions for PQXDH `Auth`: First-Message AEAD Simulators

**Checked by Lean.** Shallow reduction simulators (`aeadCpaReductionAuthFixed` and
`aeadMuIntReductionAuth`) for the first-message AEAD IND-CPA and multi-key INT-CTXT game hops of
the PQXDH `Auth` security game.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open RoKem

/-! ## Shared `PrimBaseSpec` combinators -/

def eraseAuthEvents {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with
    base := { hst.base with
      hasWonAuth       := false
      sentOPKEvents    := []
      sentNoOPKEvents  := []
      recvdOPKEvents   := []
      recvdNoOPKEvents := [] } }

def evalHkdfRoPure (roCache : List (Bytes × DRKey))
    (secrets : Bytes) : ProbComp (DRKey × List (Bytes × DRKey)) := do
  match roCache.find? (fun (inp, _) => inp == secrets) with
  | some (_, dk) => return (dk, roCache)
  | none =>
    let dk ← sampleDRKey96
    return (dk, (secrets, dk) :: roCache)

def evalRootKdfRoPure (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (rk dh : Bytes) : ProbComp ((Bytes × Bytes) × List ((Bytes × Bytes) × (Bytes × Bytes))) := do
  match rootRoCache.find? (fun (inp, _) => inp == (rk, dh)) with
  | some (_, out) => return (out, rootRoCache)
  | none =>
    let rk1 ← sampleBytes32
    let ck1 ← sampleBytes32
    return ((rk1, ck1), ((rk, dh), (rk1, ck1)) :: rootRoCache)

def mapMPrim {α β : Type} (f : α → OracleComp PrimBaseSpec β) :
    List α → OracleComp PrimBaseSpec (List β)
  | [] => return []
  | x :: xs => do
    let y ← f x
    let ys ← mapMPrim f xs
    return (y :: ys)

def checkBundleProvenanceExactPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec (Bool × Bool × Bool) := do
  match ← findHonestPrincipalPrim S principals bundle.ikB with
  | none => return (false, false, false)
  | some (k, _) =>
    let spkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.spkPk == bundle.spkB)
    let pqspkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon ←
      match bundle.opkB? with
      | none => pure false
      | some (_, opkPk) =>
        anyMPrim (fun ((u, _, _), e) => do
          let p1 ← primQ (.pow8 e.opkPk)
          let p2 ← primQ (.pow8 opkPk)
          return (u == k && p1 == p2)) (opkEntries.take S.N_dh)
    return (spkHon, opkHon, pqspkHon)

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

def finalizeAuthGameNoAuthPrim (S : Setup) (b' : Bool) (finalSt : AuthHybridState S) :
    OracleComp PrimBaseSpec Bool := do
  let ecPks ← allHonestEcPksAuthPrim S finalSt.base
  if hasDuplicateBytes ecPks || hasBadSigAuth finalSt ||
     hasKemPkCollisionAuth finalSt ||
     hasBadKemShCrRecordsPure finalSt.initKemRecs finalSt.recvKemRecs then
    embedUnif ($ᵗ Bool)
  else if !allChallengedCleanPure finalSt.base then
    embedUnif ($ᵗ Bool)
  else
    return (b' == finalSt.base.secb)

def stepAuthOtherPrim (useRo : Bool) (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, hst)
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
    return (.initPrinResp ikAPk ikSignPk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with principals := (u.val, entry) :: st.principals } } })
  | .corruptIK u =>
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, hst)
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      return (.corrResp entry.secIKA0 entry.secIKAsign,
        { hst with toAuthHybridState := { hst.toAuthHybridState with
            base := { st with principals := principals' } } })
  | .genSPK u j =>
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, hst)
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
        { hst with toAuthHybridState := { hst.toAuthHybridState with
            base := { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles } } })
  | .genOPK u j o =>
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return (.noneResp, hst)
    let opkSk ← embedUnif sampleScalar32
    let opkPk ← primQ (.x25519Base opkSk)
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    return (.pkResp opkPk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries } } })
  | .registerKey sk =>
    if sk.length != 32 then
      return (.noneResp, hst)
    let pk ← primQ (.x25519Base sk)
    let p8 ← primQ (.pow8 pk)
    return (.pkResp pk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with advKeys := (p8, pk) :: st.advKeys } } })
  | .roQuery secrets =>
    if !useRo then
      return (.noneResp, hst)
    let (dk, roCache') ← evalHkdfOrRoPrim true st.roCache secrets
    return (.drKeyResp dk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with roCache := roCache' } } })
  | .roRootQuery rk dh =>
    if !useRo then
      return (.noneResp, hst)
    let (out, rootRoCache') ← embedUnif (evalRootKdfRoPure st.rootRoCache rk dh)
    return (.rootKdfResp out.1 out.2,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with rootRoCache := rootRoCache' } } })
  | .revealDhSecrets =>
    if useRo then
      return (.noneResp, hst)
    let ikDhSks := st.principals.map (fun (_, e) => e.secIKA0)
    let spkSks  := st.spkBundles.map (fun (_, b) => b.spkSk)
    let opkSks  := st.opkEntries.map (fun (_, o) => o.opkSk)
    let ekSks   := (st.sessions.map (fun s => s.ekASk)) ++ (st.sessions.map (fun s => s.ephASk))
    return (.dhSecretsResp ikDhSks spkSks opkSks ekSks, hst)
  | .sendOPK _ _ _ _ _ | .sendNoOPK _ _ _ _ _ | .recvOPK _ _ _ _ | .recvNoOPK _ _ _ _ =>
    return (.noneResp, hst)

/-- Per-query `PrimQuery` budget for `Auth` post-handshake reductions. -/
def perQueryAuthPrimBudget (S : Setup) : Nat :=
  S.N_dh * 14 + S.N_sess_tot * 10 + 18

def runWithPrimStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp PrimBaseSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp PrimBaseSpec (α × St))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u s
      | Sum.inr gq => do
        let p ← step gq s
        r p.1 p.2)
    mx st

def runWithPrimStepFuel {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (defaultVal : α)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (fuel : Nat) (st : St) :
    OracleComp PrimBaseSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => Nat → St → OracleComp PrimBaseSpec (α × St))
    (fun a _ s => pure (a, s))
    (fun q _ r f s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (defaultVal, s)
        | f' + 1 => do
          let p ← step gq s
          r p.1 f' p.2)
    mx fuel st

/-- Pre-computed session fields saved when pausing at the target initiator send slot. -/
structure AuthCpaPausePayload (S : Setup) where
  sid          : SessionId S
  uEntry       : PrincipalEntry
  peerPrin?    : Option (Nat × PrincipalEntry)
  bundle       : PreKeyBundleInput
  m0           : Bytes
  m1           : Bytes
  ekASk        : Bytes
  ekAPk        : Bytes
  ss           : Bytes
  kemCt        : Bytes
  ephASk       : Bytes
  ephAPk       : Bytes
  drKey        : DRKey
  rk1          : Bytes
  ck1_0        : Bytes
  mkSeed       : Bytes
  ck1_1        : Bytes
  spqrSalt?    : Option Bytes
  pqRatchetMsg : Bytes
  deriveMessageKeys      : MessageKeys
  ad           : Bytes
  msgPlain     : Bytes
  spkHon       : Bool
  opkHon       : Bool
  pqspkHon     : Bool
  roCache      : List (Bytes × DRKey)
  rootRoCache  : List ((Bytes × Bytes) × (Bytes × Bytes))

inductive AuthCpaPauseResult (S : Setup) (α : Type) where
  | done (val : α) (hst : AuthHybridStateFixed S)
  | paused (ad m0 m1 : Bytes) (payload : AuthCpaPausePayload S)
      (hst : AuthHybridStateFixed S)
      (cont : AuthResponse → OracleComp (unifSpec + authSpec S) α)

abbrev AuthCpaSlotState (S : Setup) := Nat × AuthHybridStateFixed S

inductive AuthCpaSlotPauseResult (S : Setup) (α : Type) where
  | done (val : α) (shst : AuthCpaSlotState S)
  | paused (ad m0 m1 : Bytes) (payload : AuthCpaPausePayload S)
      (shst : AuthCpaSlotState S)
      (cont : AuthResponse → OracleComp (unifSpec + authSpec S) α)

def finalizeAeadCpaGameNoAuthPrim (S : Setup) (b' : Bool) (finalSt : AuthHybridState S) :
    OracleComp PrimBaseSpec Bool := do
  let ecPks ← allHonestEcPksAuthPrim S finalSt.base
  if hasDuplicateBytes ecPks || hasBadSigAuth finalSt ||
     hasKemPkCollisionAuth finalSt ||
     hasBadKemShCrRecordsPure finalSt.initKemRecs finalSt.recvKemRecs then
    embedUnif ($ᵗ Bool)
  else if !allChallengedCleanPure finalSt.base then
    embedUnif ($ᵗ Bool)
  else
    return b'

/-! ## `AeadIndCpa` simulator -/

def finishAuthCpaSendFixedPure {S : Setup} (fresh isIdealSend : Bool)
    (p : AuthCpaPausePayload S) (aeadCt : Bytes) (hst : AuthHybridStateFixed S) :
    AuthResponse × AuthHybridStateFixed S :=
  let st := hst.toAuthHybridState.base
  let hdr : HandshakeHdr := {
    ikAPk   := p.uEntry.ikAPk
    ekAPk   := p.ekAPk
    spkId   := p.bundle.spkId
    opkId?  := p.bundle.opkB?.map Prod.fst
    pqspkId := p.bundle.pqspkId
    kemCt   := p.kemCt
  }
  let wireMsg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := p.ephAPk
    pqRatchetMsg := p.pqRatchetMsg
    aeadCt       := aeadCt
  }
  let sessEntry : AuthInitiatorEntry S := {
    sid         := p.sid
    peerIkPk    := p.bundle.ikB
    peerSpkPk   := p.bundle.spkB
    peerOpkPk?  := p.bundle.opkB?.map Prod.snd
    peerPqspkPk := p.bundle.pqspkB
    spkHonest   := p.spkHon
    opkHonest   := p.opkHon
    pqspkHonest := p.pqspkHon
    ekASk       := p.ekASk
    ephASk      := p.ephASk
    fresh       := fresh
    challenged  := fresh && (p.m0 != p.m1)
  }
  let initRec : InitKemRecord S := {
    sid     := p.sid
    pqspkPk := p.bundle.pqspkB
    kemCt   := p.kemCt
    kemSs   := p.ss
  }
  let idealSessions' :=
    if isIdealSend then
      let idealEntry : IdealAuthSession S := {
        sid          := p.sid
        ikAPk        := p.uEntry.ikAPk
        peerIkPk     := p.bundle.ikB
        peerSpkPk    := p.bundle.spkB
        peerOpkPk?   := p.bundle.opkB?.map Prod.snd
        ekAPk        := p.ekAPk
        peerPqspkPk  := p.bundle.pqspkB
        kemCt        := p.kemCt
        ephAPk       := p.ephAPk
        spqrSalt?    := p.spqrSalt?
        pqRatchetMsg := p.pqRatchetMsg
        ad           := p.ad
        aeadCt       := aeadCt
        msgPlain     := []
        drKey        := p.drKey
        rk1          := p.rk1
        ck1_0        := p.ck1_0
        mkSeed       := p.mkSeed
        ck1_1        := p.ck1_1
        deriveMessageKeys      := (default : MessageKeys)
      }
      idealEntry :: hst.toAuthHybridState.idealSessions
    else
      hst.toAuthHybridState.idealSessions
  let hst' : AuthHybridStateFixed S :=
    { hst with toAuthHybridState := { hst.toAuthHybridState with
        base := { st with
          sessions         := sessEntry :: st.sessions
          usedSendSessions := p.sid :: st.usedSendSessions
          roCache          := p.roCache
          rootRoCache      := p.rootRoCache }
        initKemRecs   := initRec :: hst.toAuthHybridState.initKemRecs
        idealSessions := idealSessions' } }
  let resp : AuthResponse :=
    if p.peerPrin?.isSome then .sendFreshResp wireMsg
    else .sendUnfreshResp p.drKey p.rk1 p.ck1_1 wireMsg
  (resp, hst')

def checkBundleSpkHonIdealFromPeerPrim (S : Setup)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec Bool :=
  match peerPrincipal? with
  | none => return false
  | some (k, pEntry) =>
    anyMPrim (fun ((u, _), b) => do
      let p1 ← primQ (.pow8 b.spkPk)
      let p2 ← primQ (.pow8 bundle.spkB)
      return (u == k && ((pEntry.corrupted && p1 == p2) || b.spkPk == bundle.spkB)))
      (spkBundles.take S.N_dh)

def prepAuthCpaSendFixedPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (Option (Bool × Bool × AuthCpaPausePayload S)) := do
  let st := hst.toAuthHybridState.base
  let some (_, uEntry) := st.principals.find? (fun (i, _) => i == u.val)
    | return none
  let peerPrincipal? ← findHonestPrincipalPrim S st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then
    return none
  let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
  if !koskOk then
    return none
  let ekASk ← embedUnif sampleScalar32
  let kemCoins ← embedUnif sampleCoins32
  let ephASk ← embedUnif sampleScalar32
  let spqrCoins ← embedUnif sampleCoins32
  let sigPkB : Bytes :=
    match peerPrincipal? with
    | some (_, entry) => entry.ikSignPk
    | none            => bundle.ikB
  let v1 ← primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  if !(v1 && v2) then
    return none
  let some (ss, kemCt) ← primQ (.kemEncaps bundle.pqspkB kemCoins)
    | return none
  let ekAPk ← primQ (.x25519Base ekASk)
  let (spkHon, opkHon, pqspkHon) ←
    checkBundleProvenanceExactPrim S st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal ← checkBundleSpkHonIdealFromPeerPrim S peerPrincipal? st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
  let dh2 ← primQ (.x25519 ekASk bundle.ikB)
  let dh3 ← primQ (.x25519 ekASk bundle.spkB)
  let dh4Raw ← primQ (.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD []))
  let dh4? := bundle.opkB?.map (fun _ => dh4Raw)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let ephAPk ← primQ (.x25519Base ephASk)
  let dhRatchet ← primQ (.x25519 ephASk bundle.spkB)
  let (drKey, roCache') ← (
    if isIdealSend then do
      let dk ← embedUnif sampleDRKey96
      pure (dk, st.roCache)
    else
      embedUnif (evalHkdfRoPure st.roCache secrets))
  let ((rk1, ck1_0), rootRoCache') ← (
    if isIdealSend then do
      let r ← embedUnif sampleBytes32
      let c ← embedUnif sampleBytes32
      pure ((r, c), st.rootRoCache)
    else
      embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet))
  let (mkSeed, ck1_1) ← (
    if isIdealSend then do
      let ms ← embedUnif sampleBytes32
      let cn ← embedUnif sampleBytes32
      pure (ms, cn)
    else do
      let ms ← primQ (.chainKdfSeed ck1_0)
      let cn ← primQ (.chainKdfNext ck1_0)
      pure (ms, cn))
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) ← primQ (.spqrInitSend drKey.pqrKey spqrCoins)
    | return none
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let payload : AuthCpaPausePayload S := {
    sid := sid, uEntry := uEntry, peerPrin? := peerPrincipal?, bundle := bundle,
    m0 := m0, m1 := m1, ekASk := ekASk, ekAPk := ekAPk, ss := ss, kemCt := kemCt,
    ephASk := ephASk, ephAPk := ephAPk, drKey := drKey, rk1 := rk1, ck1_0 := ck1_0,
    mkSeed := mkSeed, ck1_1 := ck1_1, spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
    deriveMessageKeys := (default : MessageKeys), ad := ad, msgPlain := m0,
    spkHon := spkHon, opkHon := opkHon, pqspkHon := pqspkHon,
    roCache := roCache', rootRoCache := rootRoCache'
  }
  return some (isFreshPeer, isIdealSend, payload)

def tryPauseAuthCpaSendFixedPrim (allowPause : Bool) (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec
      (Sum (AuthResponse × AuthHybridStateFixed S)
           (Bytes × Bytes × Bytes × AuthCpaPausePayload S × AuthHybridStateFixed S)) := do
  let st := hst.toAuthHybridState.base
  if m0.length != m1.length then return .inl (.noneResp, hst)
  if st.usedSendSessions.contains sid then return .inl (.noneResp, hst)
  let prep? ← prepAuthCpaSendFixedPrim S sid u bundle m0 m1 hst
  match prep? with
  | none => return .inl (.noneResp, hst)
  | some (isFreshPeer, isIdealSend, rawP) =>
    let sIdx := initSessionSlotIdx sid
    if isFreshPeer then
      let msgPlain := if decide (sIdx < cut) then m0 else m1
      let p := { rawP with msgPlain := msgPlain }
      if allowPause && (sIdx == cut) then
        return .inr (p.ad, m0, m1, p, hst)
      else
        let mk ← embedUnif sampleMessageKeys80
        let aeadCt ← primQ (.aeadEnc mk p.ad msgPlain)
        return .inl (finishAuthCpaSendFixedPure true true p aeadCt hst)
    else
      let p := { rawP with msgPlain := m0 }
      let mk ← (
        if isIdealSend then
          embedUnif sampleMessageKeys80
        else
          primQ (.deriveMsgKeys p.mkSeed p.spqrSalt?))
      let aeadCt ← primQ (.aeadEnc mk p.ad m0)
      return .inl (finishAuthCpaSendFixedPure false isIdealSend p aeadCt hst)

def runAuthSendCpaCutoffPrim (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let res ← tryPauseAuthCpaSendFixedPrim false cut S sid u bundle m0 m1 hst
  match res with
  | .inl p => return p
  | .inr _ => return (.noneResp, hst)

def evalAuthRecvScheduleCpaFixedPrim (S : Setup)
    (hstDec : AuthHybridStateFixed S) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    OracleComp PrimBaseSpec
      (Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) ×
        AuthMkSaltCache S) := do
  let st := hstDec.toAuthHybridState.base
  let mkSaltCache := hstDec.mkSaltCache
  let recvCount := hstDec.recvCount
  let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
  let isUncorruptedHonestSender : Bool :=
    match senderPrincipal? with
    | some (_, sEntry) => !sEntry.corrupted
    | none             => false
  let matchedSess? ←
    findMPrim (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
      (hstDec.toAuthHybridState.idealSessions.take S.N_sess_tot)
  let (drKey, roCache') ← (
    match matchedSess? with
    | some s => pure (s.drKey, st.roCache)
    | none   =>
      if isUncorruptedHonestSender then do
        let dk ← embedUnif sampleDRKey96
        pure (dk, st.roCache)
      else
        embedUnif (evalHkdfRoPure st.roCache secrets))
  let dhRatchet ← primQ (.x25519 bEntry.spkSk msg.ephAPk)
  let sameEph ← (
    match matchedSess? with
    | some s => do
      let p1 ← primQ (.pow8 msg.ephAPk)
      let p2 ← primQ (.pow8 s.ephAPk)
      pure (p1 == p2)
    | none => pure false)
  let ((rk1, ck1_0), rootRoCache') ← (
    match matchedSess? with
    | some s =>
      if sameEph then pure ((s.rk1, s.ck1_0), st.rootRoCache)
      else do
        let r ← embedUnif sampleBytes32
        let c ← embedUnif sampleBytes32
        pure ((r, c), st.rootRoCache)
    | none =>
      if isUncorruptedHonestSender then do
        let r ← embedUnif sampleBytes32
        let c ← embedUnif sampleBytes32
        pure ((r, c), st.rootRoCache)
      else
        embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet))
  let (mkSeed, ck1_1) ← (
    match matchedSess? with
    | some s =>
      if sameEph then pure (s.mkSeed, s.ck1_1)
      else do
        let ms ← embedUnif sampleBytes32
        let cn ← embedUnif sampleBytes32
        pure (ms, cn)
    | none =>
      if isUncorruptedHonestSender then do
        let ms ← embedUnif sampleBytes32
        let cn ← embedUnif sampleBytes32
        pure (ms, cn)
      else do
        let ms ← primQ (.chainKdfSeed ck1_0)
        let cn ← primQ (.chainKdfNext ck1_0)
        pure (ms, cn))
  let some (_pqrStB, spqrSalt?) ← primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg)
    | return (none, mkSaltCache)
  let sameMsgKeys : Bool :=
    match matchedSess? with
    | some s => sameEph && sameSaltKey spqrSalt? s.spqrSalt?
    | none   => false
  let (deriveMessageKeys, mkSaltCache') ← (
    match matchedSess? with
    | some s =>
      if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache)
      else if sameEph then
        match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some (_, (_, mk)) => pure (mk, mkSaltCache)
        | none => do
          let mk ← embedUnif sampleMessageKeys80
          pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
      else do
        let mk ← embedUnif sampleMessageKeys80
        pure (mk, mkSaltCache)
    | none =>
      if isUncorruptedHonestSender then do
        let mk ← embedUnif sampleMessageKeys80
        pure (mk, mkSaltCache)
      else do
        let mk ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
        pure (mk, mkSaltCache))
  let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  if sameMsgKeys then
    match matchedSess? with
    | some s =>
      if ad == s.ad && msg.aeadCt == s.aeadCt then
        return (some (drKey, rk1, ck1_1, s.msgPlain, roCache', rootRoCache'), mkSaltCache')
      else
        return (none, mkSaltCache')
    | none => return (none, mkSaltCache')
  else if isUncorruptedHonestSender then
    return (none, mkSaltCache')
  else do
    let some pt ← primQ (.aeadDec deriveMessageKeys ad msg.aeadCt)
      | return (none, mkSaltCache')
    return (some (drKey, rk1, ck1_1, pt, roCache', rootRoCache'), mkSaltCache')

def stepAuthCpaNonSendPrim (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthHybridStateFixed S) :=
  let st := hst.toAuthHybridState.base
  match q with
  | .sendOPK _ _ _ _ _ => return (.noneResp, hst)
  | .sendNoOPK _ _ _ _ _ => return (.noneResp, hst)
  | .recvOPK k j o msg => do
    let recvCount' := hst.recvCount + 1
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return (.noneResp, { hst with recvCount := recvCount' })
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then
      return (.noneResp, { hst with recvCount := recvCount' })
    let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
    if !senderOk then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return (.noneResp, { hst with recvCount := recvCount' })
    if oEntry.consumed then
      return (.noneResp, { hst with recvCount := recvCount' })
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    let isCanEk ← primQ (.isCanonical msg.hdr.ekAPk)
    let isCanEph ← primQ (.isCanonical msg.ephAPk)
    if !replayOk || !isCanEk || !isCanEph then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some ss ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let rRec : RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
    }
    let hstDec : AuthHybridStateFixed S :=
      { toAuthHybridState :=
          { hst.toAuthHybridState with recvKemRecs := rRec :: hst.toAuthHybridState.recvKemRecs }
        recvCount := hst.recvCount
        mkSaltCache := hst.mkSaltCache }
    let dh1 ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
    let dh2 ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
    let dh3 ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
    let dh4 ← primQ (.x25519 oEntry.opkSk msg.hdr.ekAPk)
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleCpaFixedPrim S hstDec kEntry bEntry (some oEntry.opkPk) secrets msg
    let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') := res?
      | return (.noneResp, { hstDec with recvCount := recvCount', mkSaltCache := mkSaltCache' })
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
    let resp : AuthResponse :=
      match senderPrincipal? with
      | some _ => .recvHonestResp
      | none   => .recvUnfreshResp drKey rk1 ck1_1 pt
    return (resp,
      { toAuthHybridState := { hstDec.toAuthHybridState with
          base := { st with
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        recvCount := recvCount'
        mkSaltCache := mkSaltCache' })
  | .recvNoOPK k j l msg => do
    let recvCount' := hst.recvCount + 1
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return (.noneResp, { hst with recvCount := recvCount' })
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
      return (.noneResp, { hst with recvCount := recvCount' })
    let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
    if !senderOk then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return (.noneResp, { hst with recvCount := recvCount' })
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    let isCanEk ← primQ (.isCanonical msg.hdr.ekAPk)
    let isCanEph ← primQ (.isCanonical msg.ephAPk)
    if !replayOk || !isCanEk || !isCanEph then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some ss ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let rRec : RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
    }
    let hstDec : AuthHybridStateFixed S :=
      { toAuthHybridState :=
          { hst.toAuthHybridState with recvKemRecs := rRec :: hst.toAuthHybridState.recvKemRecs }
        recvCount := hst.recvCount
        mkSaltCache := hst.mkSaltCache }
    let dh1 ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
    let dh2 ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
    let dh3 ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleCpaFixedPrim S hstDec kEntry bEntry none secrets msg
    let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') := res?
      | return (.noneResp, { hstDec with recvCount := recvCount', mkSaltCache := mkSaltCache' })
    let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
    let resp : AuthResponse :=
      match senderPrincipal? with
      | some _ => .recvHonestResp
      | none   => .recvUnfreshResp drKey rk1 ck1_1 pt
    return (resp,
      { toAuthHybridState := { hstDec.toAuthHybridState with
          base := { st with
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        recvCount := recvCount'
        mkSaltCache := mkSaltCache' })
  | q_other =>
    stepAuthOtherPrim true S q_other hst

def stepAuthCpaCutoffPrim (cut : Nat) (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then
      return (.noneResp, hst)
    else
      runAuthSendCpaCutoffPrim cut S (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then
      return (.noneResp, hst)
    else
      runAuthSendCpaCutoffPrim cut S (.sendNoOPK u i) u bundle m0 m1 hst
  | q_other =>
    stepAuthCpaNonSendPrim S q_other hst

def stepUntilAuthCpaChallengeFixedPrim (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α)
    (mx : OracleComp (unifSpec + authSpec S) α) (fuel : Nat) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthCpaPauseResult S α) :=
  OracleComp.construct
    (C := fun _ => Nat → AuthHybridStateFixed S → OracleComp PrimBaseSpec (AuthCpaPauseResult S α))
    (fun a _ s => pure (.done a s))
    (fun q cont r f s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (.done defaultVal s)
        | f' + 1 =>
          match gq with
          | .sendOPK u i bundle m0 m1 =>
            if bundle.opkB?.isNone then
              r .noneResp f' s
            else do
              let stepRes ← tryPauseAuthCpaSendFixedPrim true idx S (.sendOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | .sendNoOPK u i bundle m0 m1 =>
            if bundle.opkB?.isSome then
              r .noneResp f' s
            else do
              let stepRes ←
                tryPauseAuthCpaSendFixedPrim true idx S (.sendNoOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | qOther => do
            let (resp, s') ← stepAuthCpaNonSendPrim S qOther s
            r resp f' s')
    mx fuel hst

def resumeAuthCpaAfterChallengeFixedPrim (idx : Nat) (S : Setup) (fuel : Nat) :
    AuthCpaPauseResult S Bool → Option Bytes → OracleComp PrimBaseSpec Bool
  | .done b' hst, _ =>
    finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState
  | .paused _ _ _ p hst cont, chalCt? => do
    let aeadCt := chalCt?.getD []
    let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
    let (b', finalSt) ←
      runWithPrimStepFuel false (stepAuthCpaCutoffPrim idx S) (cont resp) fuel hst'
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

def aeadCpaReductionAuthFixedAtChoose (idx : Nat) (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × AuthCpaPauseResult S Bool) := do
  let initSt := AuthHybridStateFixed.empty S true
  let res ← stepUntilAuthCpaChallengeFixedPrim idx S false A.run fuel initSt
  match res with
  | .paused ad m0 m1 _ _ _ =>
    if m0.length == m1.length then
      return (ad, m0, m1, res)
    else
      return ([], [0], [0], res)
  | .done _ _ =>
    return ([], [0], [0], res)

def aeadCpaReductionAuthFixedChoose (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × (Nat × AuthCpaPauseResult S Bool)) := do
  let idx ← embedUnif (sampleIndexRange S.N_send_tot)
  let (ad, m0, m1, res) ← aeadCpaReductionAuthFixedAtChoose idx S fuel A
  return (ad, m0, m1, (idx, res))

def aeadCpaReductionAuthFixedDist (S : Setup) (fuel : Nat)
    (st : Nat × AuthCpaPauseResult S Bool) (chalCt? : Option Bytes) :
    OracleComp PrimBaseSpec Bool :=
  resumeAuthCpaAfterChallengeFixedPrim st.1 S fuel st.2 chalCt?

def tryPauseAuthCpaSendSlotPrim (allowPause : Bool) (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S) :
    OracleComp PrimBaseSpec
      (Sum (AuthResponse × AuthCpaSlotState S)
           (Bytes × Bytes × Bytes × AuthCpaPausePayload S × AuthCpaSlotState S)) := do
  let (ns, hst) := shst
  let st := hst.toAuthHybridState.base
  if m0.length != m1.length then return .inl (.noneResp, (ns, hst))
  if st.usedSendSessions.contains sid then return .inl (.noneResp, (ns, hst))
  let prep? ← prepAuthCpaSendFixedPrim S sid u bundle m0 m1 hst
  match prep? with
  | none => return .inl (.noneResp, (ns, hst))
  | some (isFreshPeer, isIdealSend, rawP) =>
    if isFreshPeer then
      let msgPlain := if decide (ns < cut) then m0 else m1
      let p := { rawP with msgPlain := msgPlain }
      if allowPause && (ns == cut) then
        return .inr (p.ad, m0, m1, p, (ns, hst))
      else
        let mk ← embedUnif sampleMessageKeys80
        let aeadCt ← primQ (.aeadEnc mk p.ad msgPlain)
        let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
        return .inl (resp, (ns + 1, hst'))
    else
      let p := { rawP with msgPlain := m0 }
      let mk ← (
        if isIdealSend then
          embedUnif sampleMessageKeys80
        else
          primQ (.deriveMsgKeys p.mkSeed p.spqrSalt?))
      let aeadCt ← primQ (.aeadEnc mk p.ad m0)
      let (resp, hst') := finishAuthCpaSendFixedPure false isIdealSend p aeadCt hst
      return .inl (resp, (ns, hst'))

def runAuthSendCpaCutoffSlotPrim (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : AuthCpaSlotState S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthCpaSlotState S) := do
  let res ← tryPauseAuthCpaSendSlotPrim false cut S sid u bundle m0 m1 shst
  match res with
  | .inl p => return p
  | .inr _ => return (.noneResp, shst)

def stepAuthCpaCutoffSlotPrim (cut : Nat) (S : Setup)
    (q : AuthQuery S) (shst : AuthCpaSlotState S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthCpaSlotState S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then
      return (.noneResp, shst)
    else
      runAuthSendCpaCutoffSlotPrim cut S (.sendOPK u i) u bundle m0 m1 shst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then
      return (.noneResp, shst)
    else
      runAuthSendCpaCutoffSlotPrim cut S (.sendNoOPK u i) u bundle m0 m1 shst
  | q_other => do
    let (resp, hst') ← stepAuthCpaNonSendPrim S q_other shst.2
    return (resp, (shst.1, hst'))

def stepUntilAuthCpaChallengeSlotPrim (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α)
    (mx : OracleComp (unifSpec + authSpec S) α) (fuel : Nat) (shst : AuthCpaSlotState S) :
    OracleComp PrimBaseSpec (AuthCpaSlotPauseResult S α) :=
  OracleComp.construct
    (C := fun _ => Nat → AuthCpaSlotState S → OracleComp PrimBaseSpec (AuthCpaSlotPauseResult S α))
    (fun a _ s => pure (.done a s))
    (fun q cont r f s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (.done defaultVal s)
        | f' + 1 =>
          match gq with
          | .sendOPK u i bundle m0 m1 =>
            if bundle.opkB?.isNone then
              r .noneResp f' s
            else do
              let stepRes ← tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | .sendNoOPK u i bundle m0 m1 =>
            if bundle.opkB?.isSome then
              r .noneResp f' s
            else do
              let stepRes ←
                tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | qOther => do
            let (resp, hst') ← stepAuthCpaNonSendPrim S qOther s.2
            r resp f' (s.1, hst'))
    mx fuel shst

def resumeAuthCpaAfterChallengeSlotPrim (idx : Nat) (S : Setup) (fuel : Nat) :
    AuthCpaSlotPauseResult S Bool → Option Bytes → OracleComp PrimBaseSpec Bool
  | .done b' (_, hst), _ =>
    finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState
  | .paused _ _ _ p (_, hst) cont, chalCt? => do
    let aeadCt := chalCt?.getD []
    let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
    let (b', (_, finalSt)) ←
      runWithPrimStepFuel false (stepAuthCpaCutoffSlotPrim idx S) (cont resp) fuel (idx + 1, hst')
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

def aeadCpaReductionAuthSlotAtChoose (idx : Nat) (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × AuthCpaSlotPauseResult S Bool) := do
  let initSt : AuthCpaSlotState S := (0, AuthHybridStateFixed.empty S true)
  let res ← stepUntilAuthCpaChallengeSlotPrim idx S false A.run fuel initSt
  match res with
  | .paused ad m0 m1 _ _ _ =>
    if m0.length == m1.length then
      return (ad, m0, m1, res)
    else
      return ([], [0], [0], res)
  | .done _ _ =>
    return ([], [0], [0], res)

def aeadCpaReductionAuthSlotChoose (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × (Nat × AuthCpaSlotPauseResult S Bool)) := do
  let idx ← embedUnif (sampleIndexRange (min fuel S.N_send_tot))
  let (ad, m0, m1, res) ← aeadCpaReductionAuthSlotAtChoose idx S fuel A
  return (ad, m0, m1, (idx, res))

def aeadCpaReductionAuthSlotDist (S : Setup) (fuel : Nat)
    (st : Nat × AuthCpaSlotPauseResult S Bool) (chalCt? : Option Bytes) :
    OracleComp PrimBaseSpec Bool :=
  resumeAuthCpaAfterChallengeSlotPrim st.1 S fuel st.2 chalCt?

/-- `AeadIndCpaAdv` reduction for `Auth` pausing at a uniformly sampled fresh initiator send slot. -/
def aeadCpaReductionAuthFixed (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : AeadIndCpaAdv where
  State  := Nat × AuthCpaSlotPauseResult S Bool
  choose := aeadCpaReductionAuthSlotChoose S b.q_total A.1
  dist   := aeadCpaReductionAuthSlotDist S b.q_total
  q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5

/-! ## Pre-AEAD handshake preparation -/

def resolveSigPkPeer (peerPrincipal? : Option (Nat × PrincipalEntry)) (ikB : Bytes) : Bytes :=
  match peerPrincipal? with
  | some (_, entry) => entry.ikSignPk
  | none            => ikB

def checkBundleSpkHonIdealPeerPrim (S : Setup)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec Bool :=
  match peerPrincipal? with
  | none => return false
  | some (k, pEntry) =>
    anyMPrim (fun ((u, _), b) => do
      let p1 ← primQ (.pow8 b.spkPk)
      let p2 ← primQ (.pow8 bundle.spkB)
      return (u == k && ((pEntry.corrupted && p1 == p2) || b.spkPk == bundle.spkB)))
      (spkBundles.take S.N_dh)

structure AuthIntSendPrep (S : Setup) where
  uEntry         : PrincipalEntry
  peerPrincipal? : Option (Nat × PrincipalEntry)
  isFreshPeer    : Bool
  isIdealSend    : Bool
  msgPlain       : Bytes
  ekASk          : Bytes
  ekAPk          : Bytes
  ss             : Bytes
  kemCt          : Bytes
  ephASk         : Bytes
  ephAPk         : Bytes
  drKey          : DRKey
  roCache'       : List (Bytes × DRKey)
  rk1            : Bytes
  ck1_0          : Bytes
  rootRoCache'   : List ((Bytes × Bytes) × (Bytes × Bytes))
  mkSeed         : Bytes
  ck1_1          : Bytes
  spqrSalt?      : Option Bytes
  pqRatchetMsg   : Bytes
  ad             : Bytes
  spkHon         : Bool
  opkHon         : Bool
  pqspkHon       : Bool

def prepAuthIntSendPrim (S : Setup) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (Option (AuthIntSendPrep S)) := do
  let st := hst.toAuthHybridState.base
  if m0.length != m1.length then return none
  if st.usedSendSessions.contains sid then return none
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val) | return none
  let peerPrincipal? ← findHonestPrincipalPrim S st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none => false
  if !isFreshPeer && m0 != m1 then return none
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
  if !koskOk then return none
  let ekASk ← embedUnif sampleScalar32
  let kemCoins ← embedUnif sampleCoins32
  let ephASk ← embedUnif sampleScalar32
  let spqrCoins ← embedUnif sampleCoins32
  let sigPkB := resolveSigPkPeer peerPrincipal? bundle.ikB
  let v1 : Bool ← primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
  let v2 : Bool ← primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  if !(v1 && v2) then return none
  let kemRes : Option (Bytes × Bytes) ← primQ (.kemEncaps bundle.pqspkB kemCoins)
  let some (ss, kemCt) := kemRes | return none
  let ekAPk : Bytes ← primQ (.x25519Base ekASk)
  let (spkHon, opkHon, pqspkHon) ←
    checkBundleProvenanceExactPrim S st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal ← checkBundleSpkHonIdealPeerPrim S peerPrincipal? st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let dh1 : Bytes ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
  let dh2 : Bytes ← primQ (.x25519 ekASk bundle.ikB)
  let dh3 : Bytes ← primQ (.x25519 ekASk bundle.spkB)
  let dh4Raw : Bytes ← primQ (.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD []))
  let dh4? := bundle.opkB?.map (fun _ => dh4Raw)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let ephAPk : Bytes ← primQ (.x25519Base ephASk)
  let dhRatchet : Bytes ← primQ (.x25519 ephASk bundle.spkB)
  let (drKey, roCache') ← (
    if isIdealSend then do let dk ← embedUnif sampleDRKey96; pure (dk, st.roCache)
    else embedUnif (evalHkdfRoPure st.roCache secrets))
  let ((rk1, ck1_0), rootRoCache') ← (
    if isIdealSend then do
      let r ← embedUnif sampleBytes32
      let c ← embedUnif sampleBytes32
      pure ((r, c), st.rootRoCache)
    else embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet))
  let (mkSeed, ck1_1) ← (
    if isIdealSend then do
      let ms ← embedUnif sampleBytes32; let cn ← embedUnif sampleBytes32; pure (ms, cn)
    else do
      let ms : Bytes ← primQ (.chainKdfSeed ck1_0)
      let cn : Bytes ← primQ (.chainKdfNext ck1_0)
      pure (ms, cn))
  let spqrRes : Option (Bytes × Option Bytes × Bytes) ← primQ (.spqrInitSend drKey.pqrKey spqrCoins)
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := spqrRes | return none
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  return some {
    uEntry := uEntry, peerPrincipal? := peerPrincipal?, isFreshPeer := isFreshPeer,
    isIdealSend := isIdealSend, msgPlain := msgPlain, ekASk := ekASk, ekAPk := ekAPk,
    ss := ss, kemCt := kemCt, ephASk := ephASk, ephAPk := ephAPk, drKey := drKey,
    roCache' := roCache', rk1 := rk1, ck1_0 := ck1_0, rootRoCache' := rootRoCache',
    mkSeed := mkSeed, ck1_1 := ck1_1, spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
    ad := ad, spkHon := spkHon, opkHon := opkHon, pqspkHon := pqspkHon }

def finishAuthIntSendPure {S : Setup} (sid : SessionId S) (bundle : PreKeyBundleInput)
    (m0 m1 : Bytes) (p : AuthIntSendPrep S) (deriveMessageKeys : MessageKeys) (aeadCt : Bytes)
    (hst : AuthHybridStateFixed S) : AuthResponse × AuthHybridStateFixed S :=
  let st := hst.toAuthHybridState.base
  let hdr : HandshakeHdr := {
    ikAPk := p.uEntry.ikAPk, ekAPk := p.ekAPk, spkId := bundle.spkId,
    opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := p.kemCt }
  let wireMsg : PreKeyMsg := {
    hdr := hdr, ephAPk := p.ephAPk, pqRatchetMsg := p.pqRatchetMsg, aeadCt := aeadCt }
  let sessEntry : AuthInitiatorEntry S := {
    sid := sid, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
    peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB,
    spkHonest := p.spkHon, opkHonest := p.opkHon, pqspkHonest := p.pqspkHon,
    ekASk := p.ekASk, ephASk := p.ephASk, fresh := p.isFreshPeer, challenged :=
        p.isFreshPeer && (m0 != m1) }
  let initRec : InitKemRecord S := {
    sid := sid, pqspkPk := bundle.pqspkB, kemCt := p.kemCt, kemSs := p.ss }
  let idealSessions' :=
    if p.isIdealSend then
      ({ sid := sid, ikAPk := p.uEntry.ikAPk, peerIkPk := bundle.ikB,
         peerSpkPk := bundle.spkB, peerOpkPk? := bundle.opkB?.map Prod.snd,
         ekAPk := p.ekAPk, peerPqspkPk := bundle.pqspkB, kemCt := p.kemCt,
         ephAPk := p.ephAPk, spqrSalt? := p.spqrSalt?, pqRatchetMsg := p.pqRatchetMsg,
         ad := p.ad, aeadCt := aeadCt, msgPlain := p.msgPlain, drKey := p.drKey,
         rk1 := p.rk1, ck1_0 := p.ck1_0, mkSeed := p.mkSeed, ck1_1 := p.ck1_1,
         deriveMessageKeys := deriveMessageKeys } : IdealAuthSession S) :: hst.toAuthHybridState.idealSessions
    else hst.toAuthHybridState.idealSessions
  let hst' : AuthHybridStateFixed S :=
    { hst with
      toAuthHybridState := { hst.toAuthHybridState with
        base := { st with
          sessions := sessEntry :: st.sessions, usedSendSessions := sid :: st.usedSendSessions,
          roCache := p.roCache', rootRoCache := p.rootRoCache' }
        initKemRecs := initRec :: hst.toAuthHybridState.initKemRecs, idealSessions :=
            idealSessions' } }
  let resp := if p.peerPrincipal?.isSome then AuthResponse.sendFreshResp wireMsg
    else AuthResponse.sendUnfreshResp p.drKey p.rk1 p.ck1_1 wireMsg
  (resp, hst')

structure AuthIntRecvPrep (S : Setup) where
  kEntry  : PrincipalEntry
  bEntry  : SpkBundleEntry
  opkPk?  : Option Bytes
  secrets : Bytes
  hstDec  : AuthHybridState S
  finish  : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
      × (Bytes × Bytes))) →
            AuthResponse × AuthHybridState S

def finishErasedRecvOPK {S : Setup} (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (senderIsHonest : Bool)
        (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) :
    AuthResponse × AuthHybridState S :=
  let st := hstDec.base
  match res? with
  | none => (.noneResp, hstDec)
  | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    let hst' : AuthHybridState S := { hstDec with
      base := { st with
        opkEntries := opkEntries', usedRecvOPK := (k.val, j.val, o.val) :: st.usedRecvOPK,
        seenKyberBaseKeys := usedTriples', roCache := roCache', rootRoCache := rootRoCache' } }
    if senderIsHonest then (.recvHonestResp, hst') else (.recvUnfreshResp drKey rk1 ck1_1 pt, hst')

def finishErasedRecvNoOPK {S : Setup} (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (senderIsHonest : Bool)
        (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) :
    AuthResponse × AuthHybridState S :=
  let st := hstDec.base
  match res? with
  | none => (.noneResp, hstDec)
  | some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') =>
    let hst' : AuthHybridState S := { hstDec with
      base := { st with
        usedRecvNoOPK := (k.val, j.val, l.val) :: st.usedRecvNoOPK,
        seenKyberBaseKeys := usedTriples', roCache := roCache', rootRoCache := rootRoCache' } }
    if senderIsHonest then (.recvHonestResp, hst') else (.recvUnfreshResp drKey rk1 ck1_1 pt, hst')

def finishPrepareAuthRecvPrim (S : Setup) (kVal jVal : Nat)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkSk? opkPk? : Option Bytes)
    (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool → AuthHybridState S →
      Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) → AuthResponse × AuthHybridState S)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    OracleComp PrimBaseSpec (Option (AuthIntRecvPrep S)) := do
  let st := hst.base
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys kVal msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
  let isCanEk : Bool ← primQ (.isCanonical msg.hdr.ekAPk)
  let isCanEph : Bool ← primQ (.isCanonical msg.ephAPk)
  if !replayOk || !isCanEk || !isCanEph then return none
  let ss? : Option Bytes ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
  let some ss := ss? | return none
  let rRec : RecvKemRecord := {
    k := kVal, j := jVal, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk, kemCt :=
        msg.hdr.kemCt, kemSs := ss }
  let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
  let dh1 : Bytes ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
  let dh2 : Bytes ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
  let dh3 : Bytes ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
  let dh4? ← (match opkSk? with
    | some opkSk => do let d : Bytes ← primQ (.x25519 opkSk msg.hdr.ekAPk); pure (some d)
    | none => pure none)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
  return some {
    kEntry := kEntry, bEntry := bEntry, opkPk? := opkPk?, secrets := secrets,
    hstDec := hstDec, finish := mkFinish usedTriples' senderPrincipal?.isSome hstDec }

def prepareAuthRecvOPKPrim (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    OracleComp PrimBaseSpec (Option (AuthIntRecvPrep S)) := do
  let st := hst.base
  if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32) then return none
  if st.usedRecvOPK.contains (k.val, j.val, o.val) then return none
  let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
  if !senderOk then return none
  match st.principals.find? (fun (idx, _) => idx == k.val),
        st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)),
        st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
  | some (_, kEntry), some (_, bEntry), some (_, oEntry) =>
    if oEntry.consumed then return none
    finishPrepareAuthRecvPrim S k.val j.val kEntry bEntry (some oEntry.opkSk) (some oEntry.opkPk)
      (finishErasedRecvOPK k j o) msg hst
  | _, _, _ => return none

def prepareAuthRecvNoOPKPrim (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    OracleComp PrimBaseSpec (Option (AuthIntRecvPrep S)) := do
  let st := hst.base
  if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32) then return none
  if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return none
  let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
  if !senderOk then return none
  match st.principals.find? (fun (idx, _) => idx == k.val),
        st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
  | some (_, kEntry), some (_, bEntry) =>
    finishPrepareAuthRecvPrim S k.val j.val kEntry bEntry none none
      (finishErasedRecvNoOPK k j l) msg hst
  | _, _ => return none

structure AuthIntRecvSchedPrep (S : Setup) where
  isUncorruptedHonestSender : Bool
  matchedSess?              : Option (IdealAuthSession S)
  useIdealBranch            : Bool
  drKey                     : DRKey
  roCache'                  : List (Bytes × DRKey)
  sameEph                   : Bool
  rk1                       : Bytes
  ck1_0                     : Bytes
  rootRoCache'              : List ((Bytes × Bytes) × (Bytes × Bytes))
  mkSeed                    : Bytes
  ck1_1                     : Bytes
  spqrSalt?                 : Option Bytes

def prepAuthIntRecvSchedPrim (S : Setup) (hstDec : AuthHybridState S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg) :
    OracleComp PrimBaseSpec (Option (AuthIntRecvSchedPrep S)) := do
  let st := hstDec.base
  let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
  let isUncorruptedHonestSender : Bool :=
    match senderPrincipal? with | some (_, sEntry) => !sEntry.corrupted | none => false
  let matchedSess? ← findMPrim
    (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
    (hstDec.idealSessions.take S.N_sess_tot)
  let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
  let (drKey, roCache') ← (
    if useIdealBranch then
      match matchedSess? with
      | some s => pure (s.drKey, st.roCache)
      | none   => do let dk ← embedUnif sampleDRKey96; pure (dk, st.roCache)
    else embedUnif (evalHkdfRoPure st.roCache secrets))
  let dhRatchet : Bytes ← primQ (.x25519 bEntry.spkSk msg.ephAPk)
  let sameEph ← (
    match matchedSess? with
    | some s => do
      let p1 : Bytes ← primQ (.pow8 msg.ephAPk)
      let p2 : Bytes ← primQ (.pow8 s.ephAPk)
      pure (p1 == p2)
    | none => pure false)
  let ((rk1, ck1_0), rootRoCache') ← (
    if useIdealBranch then
      match matchedSess? with
      | some s =>
        if sameEph then pure ((s.rk1, s.ck1_0), st.rootRoCache)
        else do
          let r ← embedUnif sampleBytes32
          let c ← embedUnif sampleBytes32
          pure ((r, c), st.rootRoCache)
      | none => do
        let r ← embedUnif sampleBytes32
        let c ← embedUnif sampleBytes32
        pure ((r, c), st.rootRoCache)
    else embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey dhRatchet))
  let (mkSeed, ck1_1) ← (
    if useIdealBranch then
      match matchedSess? with
      | some s =>
        if sameEph then pure (s.mkSeed, s.ck1_1)
        else do let ms ← embedUnif sampleBytes32; let cn ← embedUnif sampleBytes32; pure (ms, cn)
      | none => do let ms ← embedUnif sampleBytes32; let cn ← embedUnif sampleBytes32; pure (ms, cn)
    else do
      let ms : Bytes ← primQ (.chainKdfSeed ck1_0)
      let cn : Bytes ← primQ (.chainKdfNext ck1_0)
      pure (ms, cn))
  let spqrRes : Option (Bytes × Option Bytes) ← primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg)
  let some (_pqrStB, spqrSalt?) := spqrRes | return none
  return some {
    isUncorruptedHonestSender := isUncorruptedHonestSender, matchedSess? := matchedSess?,
    useIdealBranch := useIdealBranch, drKey := drKey, roCache' := roCache', sameEph := sameEph,
    rk1 := rk1, ck1_0 := ck1_0, rootRoCache' := rootRoCache', mkSeed := mkSeed,
    ck1_1 := ck1_1, spqrSalt? := spqrSalt? }

/-! ## Multi-key `AeadMuIntCtxt` simulator -/

abbrev AeadMuIntSimSpec : OracleSpec.{0, 0} ((Nat ⊕ PrimQuery) ⊕ AeadMuIntQuery) :=
  PrimBaseSpec + aeadMuIntSpec

def embedPrimMu {α : Type} (oa : OracleComp PrimBaseSpec α) : OracleComp AeadMuIntSimSpec α :=
  embedPrim (spec := aeadMuIntSpec) oa

def unifMu {α : Type} (oa : ProbComp α) : OracleComp AeadMuIntSimSpec α :=
  embedPrimMu (embedUnif oa)

def primMuQ (op : PrimQuery) : OracleComp AeadMuIntSimSpec (primSpec.Range op) :=
  embedPrimMu (primQ op)

def encOnceMuQ (i : Nat) (ad pt : Bytes) : OracleComp AeadMuIntSimSpec (Option Bytes) :=
  liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inr (.encOnce i ad pt)))

def tryForgeMuQ (i : Nat) (ad ct : Bytes) : OracleComp AeadMuIntSimSpec Bool :=
  liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inr (.tryForge i ad ct)))

def runWithMuStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp AeadMuIntSimSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp AeadMuIntSimSpec (α × St))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inl (Sum.inl n)))
        r u s
      | Sum.inr gq => do
        let p ← step gq s
        r p.1 p.2)
    mx st

def runAuthSendMuPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    OracleComp AeadMuIntSimSpec (AuthResponse × AuthHybridStateFixed S) := do
  let some p ← embedPrimMu (prepAuthIntSendPrim S sid u bundle m0 m1 hst) | return (.noneResp, hst)
  let (deriveMessageKeys, aeadCt) ← (
    if p.isIdealSend then do
      let ct? ← encOnceMuQ (initSessionSlotIdx sid) p.ad p.msgPlain
      pure ((default : MessageKeys), ct?.getD [])
    else do
      let mk ← primMuQ (.deriveMsgKeys p.mkSeed p.spqrSalt?)
      let ct ← primMuQ (.aeadEnc mk p.ad p.msgPlain); pure (mk, ct))
  return finishAuthIntSendPure sid bundle m0 m1 p deriveMessageKeys aeadCt hst

def finishAuthRecvScheduleMuPrim {S : Setup}
    (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S) (sp : AuthIntRecvSchedPrep S) :
    OracleComp AeadMuIntSimSpec
      (Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S) := do
  let sameMsgKeys : Bool :=
      match sp.matchedSess? with
      | some s => sp.sameEph && sameSaltKey sp.spqrSalt? s.spqrSalt?
      | none => false
  let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  if sp.useIdealBranch then
    match sp.matchedSess? with
    | some s =>
      if sameMsgKeys then
        if ad == s.ad && msg.aeadCt == s.aeadCt then
          return (some (sp.drKey, sp.rk1, sp.ck1_1, s.msgPlain, sp.roCache', sp.rootRoCache'),
              mkSaltCache)
        else do
          let _ ← tryForgeMuQ (initSessionSlotIdx s.sid) ad msg.aeadCt
          return (none, mkSaltCache)
      else if sp.sameEph then
        match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid sp.spqrSalt?) with
        | some (_, (r0, _)) => do
          let _ ← tryForgeMuQ (S.N_send_tot + r0) ad msg.aeadCt
          return (none, mkSaltCache)
        | none => do
          let _ ← tryForgeMuQ (S.N_send_tot + recvCount) ad msg.aeadCt
          return (none, ((s.sid, sp.spqrSalt?), (recvCount, default)) :: mkSaltCache)
      else do
        let _ ← tryForgeMuQ (S.N_send_tot + recvCount) ad msg.aeadCt
        return (none, mkSaltCache)
    | none => do
      let _ ← tryForgeMuQ (S.N_send_tot + recvCount) ad msg.aeadCt
      return (none, mkSaltCache)
  else do
    let mk : MessageKeys ← primMuQ (.deriveMsgKeys sp.mkSeed sp.spqrSalt?)
    let pt? : Option Bytes ← primMuQ (.aeadDec mk ad msg.aeadCt)
    let some pt := pt? | return (none, mkSaltCache)
    return (some (sp.drKey, sp.rk1, sp.ck1_1, pt, sp.roCache', sp.rootRoCache'), mkSaltCache)

def evalAuthRecvScheduleMuPrim (S : Setup)
    (hstDec : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg) :
    OracleComp AeadMuIntSimSpec
      (Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S) := do
  let some sp ← embedPrimMu (prepAuthIntRecvSchedPrim S hstDec kEntry bEntry opkPk? secrets msg)
    | return (none, mkSaltCache)
  finishAuthRecvScheduleMuPrim kEntry msg recvCount mkSaltCache sp

def stepAuthMuPrim (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp AeadMuIntSimSpec (AuthResponse × AuthHybridStateFixed S) := do
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return (.noneResp, hst)
    else runAuthSendMuPrim S (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return (.noneResp, hst)
    else runAuthSendMuPrim S (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    let some prep ← embedPrimMu (prepareAuthRecvOPKPrim S k j o msg hst.toAuthHybridState)
      | return (.noneResp, { hst with recvCount := hst.recvCount + 1 })
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleMuPrim S prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    let (resp, hst') := prep.finish res?
    return (resp, {
      toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := mkSaltCache' })
  | .recvNoOPK k j l msg =>
    let some prep ← embedPrimMu (prepareAuthRecvNoOPKPrim S k j l msg hst.toAuthHybridState)
      | return (.noneResp, { hst with recvCount := hst.recvCount + 1 })
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleMuPrim S prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    let (resp, hst') := prep.finish res?
    return (resp, {
      toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := mkSaltCache' })
  | qOther => embedPrimMu (stepAuthOtherPrim true S qOther hst)

def aeadMuIntReductionAuthRun (S : Setup) (A : AuthAdversary S) :
    OracleComp AeadMuIntSimSpec Unit := do
  let secb ← unifMu ($ᵗ Bool)
  let _ ← runWithMuStep (stepAuthMuPrim S) A.run (AuthHybridStateFixed.empty S secb)
  return ()

/-- Multi-key `AeadMuIntCtxtAdv` reduction for `Auth` over all ideal session message keys. -/
def aeadMuIntReductionAuth (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : AeadMuIntCtxtAdv where
  run    := aeadMuIntReductionAuthRun S A.1
  q_enc  := S.N_send_tot
  q_dec  := S.N_recv_tot
  q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5

end SignalPqxdh.Security
