/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.Assumptions
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames

/-!
# Two-key `KeyInd` `SigEufCma` and `KemShCr` simulators

**Checked by Lean.** Defines hybrid-game `KemShCr` and `Auth` session records, primitive-oracle
liftings over `PrimBaseSpec`, and shallow `SigEufCma` (`sigReductionKeyInd`) and two-stage
`KemShCr` (`shcrReductionKeyInd`) simulators for the two-key PQXDH `KeyInd` game.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp

/-! ## Hybrid-game state and collision predicates -/

def hasDuplicateBytes : List Bytes → Bool
  | []      => false
  | x :: xs => xs.contains x || hasDuplicateBytes xs

/-- Record of an honest initiator session's Kyber-1024 encapsulation (`G2 → G3`). -/
structure InitKemRecord (S : Setup) where
  sid     : SessionId S
  pqspkPk : Bytes
  kemCt   : Bytes
  kemSs   : Bytes
  deriving DecidableEq, Repr

/-- Record of an honest receiver bundle's Kyber-1024 decapsulation (`G2 → G3`). -/
structure RecvKemRecord where
  k       : Nat
  j       : Nat
  pqspkPk : Bytes
  pqspkSk : Bytes
  kemCt   : Bytes
  kemSs   : Bytes
  deriving DecidableEq, Repr

inductive AuthHybridStage where
  | g3
  | g3_5
  | g3_6
  | g3_7
  | g3_8
  | g4
  | g5
  deriving DecidableEq, Repr

namespace AuthHybridStage

def idealDrKey : AuthHybridStage → Bool
  | .g3 => false
  | _   => true

def idealRk : AuthHybridStage → Bool
  | .g3 | .g3_5 => false
  | _           => true

def idealCk : AuthHybridStage → Bool
  | .g3 | .g3_5 | .g3_6 => false
  | _                   => true

def idealMsgKeys : AuthHybridStage → Bool
  | .g3 | .g3_5 | .g3_6 | .g3_7 => false
  | _                           => true

def idealFreshAead : AuthHybridStage → Bool
  | .g4 | .g5 => true
  | _         => false

def idealUnmatchedRecvAead : AuthHybridStage → Bool
  | .g5 => true
  | _   => false

end AuthHybridStage

/-- Shared session record for a fresh initiator session in `Auth` hybrids `G3.5`–`G5`. -/
structure IdealAuthSession (S : Setup) where
  sid          : SessionId S
  ikAPk        : Bytes
  peerIkPk     : Bytes
  peerSpkPk    : Bytes
  peerOpkPk?   : Option Bytes
  ekAPk        : Bytes
  peerPqspkPk  : Bytes
  kemCt        : Bytes
  ephAPk       : Bytes
  spqrSalt?    : Option Bytes
  pqRatchetMsg : Bytes
  ad           : Bytes
  aeadCt       : Bytes
  msgPlain     : Bytes
  drKey        : DRKey
  rk1          : Bytes
  ck1_0        : Bytes
  mkSeed       : Bytes
  ck1_1        : Bytes
  deriveMessageKeys      : MessageKeys
  deriving DecidableEq, Repr

/-- Extended hybrid state for `Auth` (`G3`–`G5`) tracking `KemShCr` records and idealised sessions. -/
structure AuthHybridState (S : Setup) where
  base          : AuthState S
  initKemRecs   : List (InitKemRecord S)
  recvKemRecs   : List RecvKemRecord
  idealSessions : List (IdealAuthSession S)

def AuthHybridState.empty (S : Setup) (secb : Bool) : AuthHybridState S :=
  { base          := AuthState.empty S secb
    initKemRecs   := []
    recvKemRecs   := []
    idealSessions := [] }

/-- Recover the `(kemCt, kemSs)` pair encapsulated by initiator session `s` from `AuthState S`. -/
def recoverAuthSessionKemSs {S : Setup} (P : Primitives) (st : AuthState S)
    (s : AuthInitiatorEntry S) : Option (Bytes × Bytes) :=
  let senderUid := match s.sid with
    | .sendOPK u _     => u.val
    | .sendNoOPK u _   => u.val
    | .recvOPK u _ _   => u.val
    | .recvNoOPK u _ _ => u.val
  match st.principals.find? (fun (idx, _) => idx == senderUid) with
  | some (_, uEntry) =>
    let dh1 := P.x25519 uEntry.secIKA0 s.peerSpkPk
    let dh2 := P.x25519 s.ekASk s.peerIkPk
    let dh3 := P.x25519 s.ekASk s.peerSpkPk
    let dh4? := s.peerOpkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk)
    let pfx := match dh4? with
      | none     => F_X25519 ++ dh1 ++ dh2 ++ dh3
      | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4
    let ekAPk := P.x25519Base s.ekASk
    let ct? : Option Bytes :=
      match s.peerOpkPk? with
      | some _ =>
        (st.sentOPKEvents.find? (fun ev => P.pow8 ev.a1 == P.pow8 ekAPk)).map (fun ev => ev.ct)
      | none =>
        (st.sentNoOPKEvents.find? (fun ev => P.pow8 ev.a1 == P.pow8 ekAPk)).map (fun ev => ev.ct)
    match ct?, st.roCache.find? (fun (sec, _) =>
        sec.take pfx.length == pfx && sec.length == pfx.length + 32) with
    | some ct, some (sec, _) => some (ct, sec.drop pfx.length)
    | _, _ => none
  | none => none

/-- Projection of `AuthState S` and `KemShCr` records from `AuthState S` or `AuthHybridState S`. -/
class HasAuthState (σ : Type) (S : outParam Setup) where
  toAuthState   : σ → AuthState S
  toInitKemRecs : Primitives → σ → List (InitKemRecord S)
  toRecvKemRecs : Primitives → σ → List RecvKemRecord

instance {S : Setup} : HasAuthState (AuthState S) S where
  toAuthState st := st
  toInitKemRecs P st :=
    st.sessions.filterMap (fun s =>
      (recoverAuthSessionKemSs P st s).map (fun (ct, ss) =>
        { sid := s.sid, pqspkPk := s.peerPqspkPk, kemCt := ct, kemSs := ss }))
  toRecvKemRecs P st :=
    let recvCts := (st.recvdOPKEvents.map (fun r => (r.pk1, r.ct))) ++
                   (st.recvdNoOPKEvents.map (fun r => (r.pk1, r.ct)))
    st.spkBundles.flatMap (fun ((k, j), b) =>
      recvCts.filterMap (fun (pk1, ct) =>
        if b.pqspkPk == pk1 then
          (P.kemDecaps b.pqspkSk ct).map (fun ss =>
            { k := k, j := j, pqspkPk := b.pqspkPk, pqspkSk := b.pqspkSk,
              kemCt := ct, kemSs := ss })
        else none))

instance {S : Setup} : HasAuthState (AuthHybridState S) S where
  toAuthState st := st.base
  toInitKemRecs _ st := st.initKemRecs
  toRecvKemRecs _ st := st.recvKemRecs

def allHonestKemPksAuth {S : Setup} {σ : Type} [HasAuthState σ S] (st : σ) : List Bytes :=
  (HasAuthState.toAuthState st).spkBundles.map (fun (_, b) => b.pqspkPk)

def hasKemPkCollisionAuth {S : Setup} {σ : Type} [HasAuthState σ S] (st : σ) : Bool :=
  hasDuplicateBytes (allHonestKemPksAuth st)

/-- Whether any fresh `Auth` session accepted a bundle whose `spkB` or `pqspkB` is dishonest. -/
def hasBadSigAuth {S : Setup} {σ : Type} [HasAuthState σ S] (st : σ) : Bool :=
  (HasAuthState.toAuthState st).sessions.any (fun s =>
    s.fresh && (!s.spkHonest || !s.pqspkHonest))

def opkSlotFlatIdx (S : Setup) (p : Nat × Nat × Nat) : Nat :=
  (p.1 * S.N_recv + p.2.1) * S.N_opk + p.2.2

/-! ## Primitive-oracle liftings and `SigEufCma` simulator -/

def embedUnif {α : Type} (mx : ProbComp α) : OracleComp PrimBaseSpec α :=
  liftComp mx PrimBaseSpec

def primQ (q : PrimQuery) : OracleComp PrimBaseSpec (primSpec.Range q) :=
  query (spec := PrimBaseSpec) (Sum.inr q)

def embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) : OracleComp (PrimBaseSpec + spec) α :=
  OracleComp.construct
    (C := fun _ => OracleComp (PrimBaseSpec + spec) α)
    pure
    (fun q _ r => liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>= r)
    mx

namespace FgGapDh

def sampleIndexRange (N : ℕ) : ProbComp ℕ :=
  if h : 0 < N then
    letI : NeZero N := ⟨Nat.ne_of_gt h⟩
    do
      let x ← $ᵗ (Fin N)
      return x.val
  else
    return 0

end FgGapDh

def findMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) :
    List α → OracleComp PrimBaseSpec (Option α)
  | [] => pure none
  | x :: xs => do
    if ← p x then return some x else findMPrim p xs

def anyMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) :
    List α → OracleComp PrimBaseSpec Bool
  | [] => pure false
  | x :: xs => do
    if ← p x then return true else anyMPrim p xs


inductive SigStepResultPrim (St R : Type) where
  | done (res : R) (st' : St)
  | signTwo
      (msg1 : Bytes)
      (k1 : (Bytes × Bytes) → Bytes → Bytes × (Bytes → R × St))
      (fallback : R × St)


def sampleKemKeyGenPrim : OracleComp PrimBaseSpec (Bytes × Bytes) := do
  let seed ← embedUnif sampleRandom64
  primQ (.kemKeyGen seed)


def runWithSigBudgetPrim {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) (budget : Nat) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (α × St) :=
  OracleComp.construct
    (C := fun _ => St → Nat → OracleComp (PrimBaseSpec + sigOracleSpec) (α × St))
    (fun x st _ => pure (x, st))
    (fun q _ r st budget =>
      match q with
      | Sum.inl n => do
        let q := (Sum.inl (Sum.inl n) : (ℕ ⊕ PrimQuery) ⊕ SigQuery)
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec) q)
        r u st budget
      | Sum.inr gq => do
        let sr ← embedPrim (spec := sigOracleSpec) (step gq st)
        match sr with
        | .done res st' => r res st' budget
        | .signTwo msg1 k1 fallback =>
          match budget with
          | 0 => r fallback.1 fallback.2 0
          | b' + 1 => do
            let sig1 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg1))
            let pq ← embedPrim (spec := sigOracleSpec) sampleKemKeyGenPrim
            let (msg2, k2) := k1 pq sig1
            let sig2 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg2))
            let p := k2 sig2
            r p.1 p.2 b')
    mx st budget


def findHonestPrincipalPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : OracleComp PrimBaseSpec (Option (Nat × PrincipalEntry)) :=
  findMPrim (fun (_, entry) => do
    let p1 ← primQ (.pow8 ikB)
    let p2 ← primQ (.pow8 entry.ikAPk)
    return (p1 == p2)) (principals.take S.N_dh)


def resolveSigPkPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : OracleComp PrimBaseSpec Bytes := do
  match ← findHonestPrincipalPrim S principals ikB with
  | some (_, entry) => return entry.ikSignPk
  | none            => return ikB


def isHonestUncorruptedPeerPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : OracleComp PrimBaseSpec (Option Nat) := do
  match ← findHonestPrincipalPrim S principals ikB with
  | some (k, entry) => return (if !entry.corrupted then some k else none)
  | none            => return none


def checkBundleProvenancePrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec (Bool × Bool × Bool) := do
  match ← findHonestPrincipalPrim S principals bundle.ikB with
  | none => return (false, false, false)
  | some (k, _) =>
    let spkHon ← anyMPrim (fun ((u, _), b) => do
      let p1 ← primQ (.pow8 b.spkPk)
      let p2 ← primQ (.pow8 bundle.spkB)
      return (u == k && p1 == p2)) (spkBundles.take S.N_dh)
    let pqspkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon ← match bundle.opkB? with
      | none => pure false
      | some (_, opkPk) =>
        anyMPrim (fun ((u, _, _), e) => do
          let p1 ← primQ (.pow8 e.opkPk)
          let p2 ← primQ (.pow8 opkPk)
          return (u == k && p1 == p2)) (opkEntries.take S.N_dh)
    return (spkHon, opkHon, pqspkHon)


def isAdvRegisteredPrim (advKeys : List (Bytes × Bytes)) (pk : Bytes) :
    OracleComp PrimBaseSpec Bool := do
  let p ← primQ (.pow8 pk)
  return advKeys.any (fun (p8, _) => p == p8)


def isGameIdKeyPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (pk : Bytes) : OracleComp PrimBaseSpec Bool := do
  let r ← findHonestPrincipalPrim S principals pk
  return r.isSome


def isGameSpkPrim (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (pk : Bytes) : OracleComp PrimBaseSpec Bool :=
  anyMPrim (fun (_, b) => do
    let p1 ← primQ (.pow8 b.spkPk)
    let p2 ← primQ (.pow8 pk)
    return (p1 == p2)) (spkBundles.take S.N_dh)


def isGameOpkPrim (S : Setup) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (pk : Bytes) : OracleComp PrimBaseSpec Bool :=
  anyMPrim (fun (_, e) => do
    let p1 ← primQ (.pow8 e.opkPk)
    let p2 ← primQ (.pow8 pk)
    return (p1 == p2)) (opkEntries.take S.N_dh)


def koskBundleOkPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    OracleComp PrimBaseSpec Bool := do
  let idG ← isGameIdKeyPrim S principals bundle.ikB
  let idA ← isAdvRegisteredPrim advKeys bundle.ikB
  let spkG ← isGameSpkPrim S spkBundles bundle.spkB
  let spkA ← isAdvRegisteredPrim advKeys bundle.spkB
  match bundle.opkB? with
  | none =>
    return ((idG || idA) && (spkG || spkA) && true)
  | some (_, opkPk) =>
    let opkG ← isGameOpkPrim S opkEntries opkPk
    let opkA ← isAdvRegisteredPrim advKeys opkPk
    return ((idG || idA) && (spkG || spkA) && (opkG || opkA))


def koskSenderOkPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) :
    OracleComp PrimBaseSpec Bool := do
  let idG ← isGameIdKeyPrim S principals ikAPk
  let idA ← isAdvRegisteredPrim advKeys ikAPk
  return (idG || idA)


def extractBundleForgery (P : Primitives)
    (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (prevForgery : Option (Bytes × Bytes)) : Option (Bytes × Bytes) :=
  match prevForgery with
  | some fg => some fg
  | none =>
    match isHonestUncorruptedPeer P principals bundle.ikB with
    | some k =>
      if k == targetParty then
        let spkExact := spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB)
        let pqspkExact := spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB)
        if P.sigVerify targetPk (encodeEC bundle.spkB) bundle.spkSig && !spkExact then
          some (encodeEC bundle.spkB, bundle.spkSig)
        else if P.sigVerify targetPk (encodeKEM bundle.pqspkB) bundle.pqspkSig && !pqspkExact then
          some (encodeKEM bundle.pqspkB, bundle.pqspkSig)
        else
          none
      else
        none
    | none => none

def extractBundleForgeryPrim (S : Setup)
    (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (prevForgery : Option (Bytes × Bytes)) : OracleComp PrimBaseSpec (Option (Bytes × Bytes)) := do
  let peer? ← isHonestUncorruptedPeerPrim S principals bundle.ikB
  let v1 ← primQ (.sigVerify targetPk (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primQ (.sigVerify targetPk (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  return (match prevForgery with
    | some fg => some fg
    | none =>
      match peer? with
      | some k =>
        if k == targetParty then
          let spkExact := spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB)
          let pqspkExact := spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB)
          if v1 && !spkExact then
            some (encodeEC bundle.spkB, bundle.spkSig)
          else if v2 && !pqspkExact then
            some (encodeKEM bundle.pqspkB, bundle.pqspkSig)
          else
            none
        else
          none
      | none => none)


def keyIndPartnerPrim {S : Setup} (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    OracleComp PrimBaseSpec Bool := do
  let sIk ← primQ (.pow8 s.hdr.ikAPk)
  let rIk ← primQ (.pow8 r.hdr.ikAPk)
  let sPeer ← primQ (.pow8 s.peerIkPk)
  let rResp ← primQ (.pow8 r.respIkPk)
  let sSpk ← primQ (.pow8 s.peerSpkPk)
  let rSpk ← primQ (.pow8 r.spkPk)
  let sOpk ← primQ (.pow8 (s.peerOpkPk?.getD []))
  let rOpk ← primQ (.pow8 (r.opkPk?.getD []))
  return (sIk == rIk &&
          sPeer == rResp &&
          sSpk == rSpk &&
          s.peerOpkPk?.map (fun _ => sOpk) == r.opkPk?.map (fun _ => rOpk) &&
          s.hdr.ekAPk == r.hdr.ekAPk &&
          s.peerPqspkPk == r.pqspkPk &&
          s.hdr.kemCt == r.hdr.kemCt)


def recordKeyIndRespPrim (S : Setup) (r : KeyIndRespEntry S) :
    StateT (KeyIndState S) (OracleComp PrimBaseSpec) Unit := do
  let st ← get
  let found ← liftM (findMPrim (fun s => keyIndPartnerPrim s r) (st.sessions.take S.N_dh))
  let drKeyRand ← match found with
    | some s => pure s.drKeyRand
    | none   => liftM (embedUnif sampleDRKey96)
  set { st with respSessions := { r with drKeyRand := drKeyRand } :: st.respSessions }


def evalHkdfOrRoPrim (useRo : Bool) (roCache : List (Bytes × DRKey))
    (secrets : Bytes) : OracleComp PrimBaseSpec (DRKey × List (Bytes × DRKey)) := do
  if !useRo then
    let dk ← primQ (.hkdfDerive96 secrets)
    return (dk, roCache)
  else
    match roCache.find? (fun (inp, _) => inp == secrets) with
    | some (_, dk) => return (dk, roCache)
    | none =>
      let dk ← embedUnif sampleDRKey96
      return (dk, (secrets, dk) :: roCache)


def acceptKeysPrim (inp : AcceptKeysInput) : OracleComp PrimBaseSpec (Option DRKey) := do
  let canon ← primQ (.isCanonical inp.hdr.ekAPk)
  let dh1 ← primQ (.x25519 inp.spkBSk inp.hdr.ikAPk)
  let dh2 ← primQ (.x25519 inp.ikBSk inp.hdr.ekAPk)
  let dh3 ← primQ (.x25519 inp.spkBSk inp.hdr.ekAPk)
  let dh4Raw ← primQ (.x25519 (inp.opkBSk?.getD []) inp.hdr.ekAPk)
  let ss? ← primQ (.kemDecaps inp.pqspkBSk inp.hdr.kemCt)
  let dh4? : Option (Option Bytes) := match inp.hdr.opkId?, inp.opkBSk? with
    | none,   none   => some none
    | some _, some _ => some (some dh4Raw)
    | _,      _      => none
  let hkdf ← primQ (.hkdfDerive96 (buildSecrets dh1 dh2 dh3 (dh4?.getD none) (ss?.getD [])))
  return (do
    «guard» inp.trustedPeer
    «guard» inp.replayOk
    «guard» (inp.hdr.ikAPk.length == 32)
    «guard» (inp.hdr.ekAPk.length == 32)
    «guard» canon
    «guard» (dh1 != List.replicate 32 0)
    «guard» (dh2 != List.replicate 32 0)
    «guard» (dh3 != List.replicate 32 0)
    let d4 ← dh4?
    «guard» (dhOptNonZero d4)
    let _ ← ss?
    some hkdf)


def runKeyIndInitiatePrim (useRo : Bool) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) :
    StateT (KeyIndState S) (OracleComp PrimBaseSpec) KeyIndResponse := do
  let st ← get
  if st.sessions.any (fun e => e.sid == sid) then
    return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let koskOk ← liftM
    (koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle)
  if !koskOk then
    return .noneResp
  let ekASk ← liftM (embedUnif sampleScalar32)
  let kemCoins ← liftM (embedUnif sampleCoins32)
  let sigPkB ← liftM (resolveSigPkPrim S st.principals bundle.ikB)
  let v1 ← liftM (primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig))
  let v2 ← liftM (primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig))
  if !(v1 && v2) then
    return .noneResp
  let some (ss, kemCt) ← liftM (primQ (.kemEncaps bundle.pqspkB kemCoins))
    | return .noneResp
  let ekAPk ← liftM (primQ (.x25519Base ekASk))
  let dh1 ← liftM (primQ (.x25519 uEntry.secIKA0 bundle.spkB))
  let dh2 ← liftM (primQ (.x25519 ekASk bundle.ikB))
  let dh3 ← liftM (primQ (.x25519 ekASk bundle.spkB))
  let dh4Raw ← liftM (primQ (.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD [])))
  let dh4? := bundle.opkB?.map (fun _ => dh4Raw)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ← liftM (evalHkdfOrRoPrim useRo st.roCache secrets)
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer ← liftM (isHonestUncorruptedPeerPrim S st.principals bundle.ikB)
  let (spkHon, opkHon, pqspkHon) ←
    liftM (checkBundleProvenancePrim S st.principals st.spkBundles st.opkEntries bundle)
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
    drKeyRand   := drKeyReal
    hdr         := hdr
    tested      := false
  }
  let found ← liftM
    (findMPrim (fun r => keyIndPartnerPrim sessEntry r) (st.respSessions.take S.N_sess_tot))
  let drKeyRand ← match found with
    | some r => pure r.drKeyRand
    | none   => liftM (embedUnif sampleDRKey96)
  set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions,
                roCache := roCache' }
  match ← liftM (findHonestPrincipalPrim S st.principals bundle.ikB) with
  | some _ => return .hdrResp hdr
  | none   => return .initUnfreshResp drKeyReal hdr


def pqxdhKeyIndImplPrim (useRo : Bool) (S : Setup) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) (OracleComp PrimBaseSpec)) := fun q => do
  let st ← get
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM (embedUnif sampleScalar32)
    let ikAPk ← liftM (primQ (.x25519Base secIKA0))
    let secIKAsign ← liftM (embedUnif sampleScalar32)
    let ikSignPk ← liftM (primQ (.sigPkGen secIKAsign))
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
    let spkSk ← liftM (embedUnif sampleScalar32)
    let spkPk ← liftM (primQ (.x25519Base spkSk))
    let rSpk ← liftM (embedUnif sampleRandom64)
    let spkSig ← liftM (primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk))
    let (pqspkPk, pqspkSk) ← liftM sampleKemKeyGenPrim
    let rPq ← liftM (embedUnif sampleRandom64)
    let pqspkSig ← liftM (primQ (.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq))
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
    let opkSk ← liftM (embedUnif sampleScalar32)
    let opkPk ← liftM (primQ (.x25519Base opkSk))
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    set { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
    return .pkResp opkPk
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then return .noneResp
    runKeyIndInitiatePrim useRo S (.sendOPK u i) u bundle
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then return .noneResp
    runKeyIndInitiatePrim useRo S (.sendNoOPK u i) u bundle
  | .acceptOPK k j o hdr =>
    if !(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then return .noneResp
    if !(← liftM (koskSenderOkPrim S st.principals st.advKeys hdr.ikAPk)) then return .noneResp
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
    let some _ ← liftM (acceptKeysPrim accInp) | return .noneResp
    let some ss ← liftM (primQ (.kemDecaps bEntry.pqspkSk hdr.kemCt)) | return .noneResp
    let dh1 ← liftM (primQ (.x25519 bEntry.spkSk hdr.ikAPk))
    let dh2 ← liftM (primQ (.x25519 kEntry.secIKA0 hdr.ekAPk))
    let dh3 ← liftM (primQ (.x25519 bEntry.spkSk hdr.ekAPk))
    let dh4 ← liftM (primQ (.x25519 oEntry.opkSk hdr.ekAPk))
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (drKey, roCache') ← liftM (evalHkdfOrRoPrim useRo st.roCache secrets)
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    set { st with
      opkEntries       := opkEntries'
      usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
      seenKyberBaseKeys := usedTriples'
      roCache          := roCache' }
    let senderHonest := (← liftM (findHonestPrincipalPrim S st.principals hdr.ikAPk)).isSome
    recordKeyIndRespPrim S {
      sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
      opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
      senderHonest := senderHonest, drKeyReal := drKey, drKeyRand := drKey }
    match ← liftM (findHonestPrincipalPrim S st.principals hdr.ikAPk) with
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
    if !(← liftM (koskSenderOkPrim S st.principals st.advKeys hdr.ikAPk)) then return .noneResp
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
    let some _ ← liftM (acceptKeysPrim accInp) | return .noneResp
    let some ss ← liftM (primQ (.kemDecaps bEntry.pqspkSk hdr.kemCt)) | return .noneResp
    let dh1 ← liftM (primQ (.x25519 bEntry.spkSk hdr.ikAPk))
    let dh2 ← liftM (primQ (.x25519 kEntry.secIKA0 hdr.ekAPk))
    let dh3 ← liftM (primQ (.x25519 bEntry.spkSk hdr.ekAPk))
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (drKey, roCache') ← liftM (evalHkdfOrRoPrim useRo st.roCache secrets)
    set { st with
      usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
      seenKyberBaseKeys := usedTriples'
      roCache          := roCache' }
    let senderHonest := (← liftM (findHonestPrincipalPrim S st.principals hdr.ikAPk)).isSome
    recordKeyIndRespPrim S {
      sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
      opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
      senderHonest := senderHonest, drKeyReal := drKey, drKeyRand := drKey }
    match ← liftM (findHonestPrincipalPrim S st.principals hdr.ikAPk) with
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
  | .roQuery secrets =>
    if !useRo then
      return .noneResp
    let (dk, roCache') ← liftM (evalHkdfOrRoPrim true st.roCache secrets)
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
  | .registerKey sk =>
    if sk.length != 32 then return .noneResp
    let pk ← liftM (primQ (.x25519Base sk))
    let p8 ← liftM (primQ (.pow8 pk))
    set { st with advKeys := (p8, pk) :: st.advKeys }
    return .pkResp pk
  | .revealSpkSk u j =>
    match st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none => return .noneResp
    | some (_, bEntry) =>
      let spkBundles' := st.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
      set { st with spkBundles := spkBundles' }
      return .spkSkResp bEntry.spkSk


structure SigReductionState (GameSt : Type) where
  gameState   : GameSt
  targetParty : Nat
  targetPk    : Bytes
  forgery     : Option (Bytes × Bytes)

def stepKeyIndForSigPrim (useRo : Bool) (S : Setup)
    (q : KeyIndQuery S) (s : SigReductionState (KeyIndState S)) :
    OracleComp PrimBaseSpec
      (SigStepResultPrim (SigReductionState (KeyIndState S)) KeyIndResponse) := do
  if s.forgery.isSome then
    return .done .noneResp s
  else
    match q with
    | .initPrin u =>
      if s.gameState.principals.any (fun (idx, _) => idx == u.val) then
        return .done .noneResp s
      else if u.val == s.targetParty then
        let secIKA0 ← embedUnif sampleScalar32
        let ikAPk ← primQ (.x25519Base secIKA0)
        let entry : PrincipalEntry := {
          secIKA0    := secIKA0
          ikAPk      := ikAPk
          secIKAsign := []
          ikSignPk   := s.targetPk
          corrupted  := false
        }
        let gs' := { s.gameState with principals := (u.val, entry) :: s.gameState.principals }
        return .done (.initPrinResp ikAPk s.targetPk) { s with gameState := gs' }
      else
        let (out, gs') ← (pqxdhKeyIndImplPrim useRo S (.initPrin u)).run s.gameState
        return .done out { s with gameState := gs' }
    | .corruptIK u =>
      if u.val == s.targetParty then
        match s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
        | none => return .done .noneResp s
        | some _ =>
          let principals' := s.gameState.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
          let gs' := { s.gameState with principals := principals' }
          return .done .noneResp { s with gameState := gs' }
      else
        let (out, gs') ← (pqxdhKeyIndImplPrim useRo S (.corruptIK u)).run s.gameState
        return .done out { s with gameState := gs' }
    | .genSPK u j =>
      if u.val == s.targetParty then
        if s.gameState.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
          return .done .noneResp s
        else
          match s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
          | none => return .done .noneResp s
          | some (_, uEntry) =>
            let spkSk ← embedUnif sampleScalar32
            let spkPk ← primQ (.x25519Base spkSk)
            return .signTwo (encodeEC spkPk)
              (fun (pqspkPk, pqspkSk) spkSig =>
                (encodeKEM pqspkPk, fun pqspkSig =>
                  let bEntry : SpkBundleEntry := {
                    spkSk    := spkSk
                    spkPk    := spkPk
                    spkSig   := spkSig
                    pqspkSk  := pqspkSk
                    pqspkPk  := pqspkPk
                    pqspkSig := pqspkSig
                  }
                  let spks' := ((u.val, j.val), bEntry) :: s.gameState.spkBundles
                  let gs' := { s.gameState with spkBundles := spks' }
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
                  (.bundleResp bundleOut, { s with gameState := gs' })))
              (.noneResp, s)
      else
        let (out, gs') ← (pqxdhKeyIndImplPrim useRo S (.genSPK u j)).run s.gameState
        return .done out { s with gameState := gs' }
    | .initiateOPK u i bundle =>
      let forgery' ← extractBundleForgeryPrim S s.targetParty s.targetPk
        s.gameState.principals s.gameState.spkBundles bundle s.forgery
      let (out, gs') ← (pqxdhKeyIndImplPrim useRo S (.initiateOPK u i bundle)).run s.gameState
      return .done out { s with gameState := gs', forgery := forgery' }
    | .initiateNoOPK u i bundle =>
      let forgery' ← extractBundleForgeryPrim S s.targetParty s.targetPk
        s.gameState.principals s.gameState.spkBundles bundle s.forgery
      let (out, gs') ← (pqxdhKeyIndImplPrim useRo S (.initiateNoOPK u i bundle)).run s.gameState
      return .done out { s with gameState := gs', forgery := forgery' }
    | q_other =>
      let (out, gs') ← (pqxdhKeyIndImplPrim useRo S q_other).run s.gameState
      return .done out { s with gameState := gs' }


def simulateForSigPrim {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St : Type}
    (S : Setup) (emptySt : Bool → St)
    (stepPrim : (q : ιI) → SigReductionState St →
      OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (targetParty : Nat) (targetPk : Bytes)
    (oa : OracleComp (unifSpec + GSpec) Bool) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (Bytes × Bytes) := do
  let secb ← embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ Bool))
  let initSt : SigReductionState St := {
    gameState   := emptySt secb
    targetParty := targetParty
    targetPk    := targetPk
    forgery     := none
  }
  let (_, finalSt) ← runWithSigBudgetPrim stepPrim oa initSt S.N_spk_tot
  return finalSt.forgery.getD ([], [])


@[reducible]
def simulateKeyIndForSigPrim (useRo : Bool) (S : Setup)
    (targetParty : Nat) (targetPk : Bytes) (A : KeyIndAdversary S) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (Bytes × Bytes) :=
  simulateForSigPrim S (KeyIndState.empty S) (stepKeyIndForSigPrim useRo S)
    targetParty targetPk A.run


def sigReductionKeyIndCoreRun (useRo : Bool) (S : Setup)
    (A : KeyIndAdversary S) (pk : Bytes) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (Bytes × Bytes) :=
  if hN : 0 < S.N_id then
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    do
      let k ← embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ (Fin S.N_id)))
      simulateKeyIndForSigPrim useRo S k.val pk A
  else
    pure ([], [])


def sigReductionKeyIndCore (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : SigEufCmaAdv where
  run          := sigReductionKeyIndCoreRun useRo S A.val
  q_sig        := 2 * S.N_spk_tot

  q_prim       := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 17)

def sigReductionKeyInd (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    SigEufCmaAdv :=
  sigReductionKeyIndCore true S b A

def sigReductionHndlKeyInd (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    SigEufCmaAdv :=
  sigReductionKeyIndCore false S b A

abbrev sigReduction (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    SigEufCmaAdv :=
  sigReductionKeyInd S b A


/-! ## `KemShCr` two-stage simulator -/

namespace RoKem

def extractDh1 (secrets : Bytes) : Bytes :=
  (secrets.drop 32).take 32

def extractDh3 (secrets : Bytes) : Bytes :=
  (secrets.drop 96).take 32

structure InitKemRecord (S : Setup) where
  sendIdx : Nat
  sid     : SessionId S
  pqspkPk : Bytes
  kemCt   : Bytes
  kemSs   : Bytes
  deriving DecidableEq, Repr

structure RecvKemRecord where
  bIdx    : Nat
  k       : Nat
  j       : Nat
  pqspkPk : Bytes
  pqspkSk : Bytes
  kemCt   : Bytes
  kemSs   : Bytes
  deriving DecidableEq, Repr


def spkBundleFlatIdx (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) : Nat :=
  u.val * S.N_recv + j.val


structure ShCrState (S : Setup) (Base : Type) where
  base        : Base
  targetBIdx? : Option Nat := none
  targetPk    : Bytes := []
  targetSk    : Bytes := []
  sendCount   : Nat := 0
  initKemRecs : List (InitKemRecord S) := []
  recvKemRecs : List RecvKemRecord := []


def applyShCrFinish {S : Setup} {Base Resp : Type}
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : ShCrState S Base)
    (out : Resp × Option Base) : Resp × ShCrState S Base :=
  match out.2 with
  | none => (out.1, { hst with sendCount := hst.sendCount + 1 })
  | some base' =>
    let initRec : InitKemRecord S := {
      sendIdx := hst.sendCount
      sid     := sid
      pqspkPk := pqspkPk
      kemCt   := kemCt
      kemSs   := ss
    }
    (out.1, { hst with
      base        := base'
      sendCount   := hst.sendCount + 1
      initKemRecs := initRec :: hst.initKemRecs })


abbrev KeyIndShCrState (S : Setup) := ShCrState S (KeyIndState S)


def isNoneKeyIndResp : KeyIndResponse → Bool
  | .noneResp => true
  | _ => false


def sessionSlotIndex {S : Setup} : SessionId S → Nat
  | .sendOPK u i     => u.val * S.N_send_opk + i.val
  | .sendNoOPK u i   => S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val)
  | .recvOPK _ _ _   => 0
  | .recvNoOPK _ _ _ => 0


def liftShCrBasePrim {S : Setup} {Base α : Type}
    (m : StateT Base (OracleComp PrimBaseSpec) α) :
    StateT (ShCrState S Base) (OracleComp PrimBaseSpec) α := fun hst => do
  let (a, base') ← m.run hst.base
  return (a, { hst with base := base' })


def recordAcceptKemGenericPrim {S : Setup} {Base Resp : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) : StateT (ShCrState S Base) (OracleComp PrimBaseSpec) Resp := fun hst =>
  if isNoneResp out then
    pure (out, hst)
  else
    match (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => pure (out, hst)
    | some (_, bEntry) => do
      match ← primQ (.kemDecaps bEntry.pqspkSk hdr.kemCt) with
      | none => return (out, hst)
      | some ss =>
        let recEntry : RecvKemRecord := {
          bIdx    := spkBundleFlatIdx S k j
          k       := k.val
          j       := j.val
          pqspkPk := bEntry.pqspkPk
          pqspkSk := bEntry.pqspkSk
          kemCt   := hdr.kemCt
          kemSs   := ss
        }
        return (out, { hst with recvKemRecs := recEntry :: hst.recvKemRecs })


def runKeyIndShCrAcceptPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : KeyIndQuery S) :
    StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec) KeyIndResponse := do
  let out ← liftShCrBasePrim (pqxdhKeyIndImplPrim true S gq)
  recordAcceptKemGenericPrim KeyIndState.spkBundles isNoneKeyIndResp k j hdr out


def genSpkTargetKeyIndPrim (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec) KeyIndResponse := fun hst => do
  let st := hst.base
  if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
    return (.noneResp, hst)
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, hst)
  let spkSk ← embedUnif sampleScalar32
  let spkPk ← primQ (.x25519Base spkSk)
  let rSpk ← embedUnif sampleRandom64
  let spkSig ← primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
  let pqspkPk := hst.targetPk
  let pqspkSk := hst.targetSk
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
    { hst with base := { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles } })


def runKeyIndShCrGenSPKPrim (embedTarget : Bool) (S : Setup)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec) KeyIndResponse := fun hst =>
  if !embedTarget then
    (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst
  else
    match hst.targetBIdx? with
    | none => (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst
    | some bIdx =>
      if spkBundleFlatIdx S u j == bIdx then
        (genSpkTargetKeyIndPrim S u j).run hst
      else
        (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst


def preCheckKeyIndPrim (S : Setup) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    OracleComp PrimBaseSpec (Option PrincipalEntry) :=
  if st.sessions.any (fun e => e.sid == sid) then pure none
  else match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure none
    | some (_, uEntry) => do
      let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
      if !koskOk then return none
      else return some uEntry


def checkBundleSigsPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec Bool := do
  let sigPkB ← resolveSigPkPrim S principals bundle.ikB
  let v1 ← primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  return (v1 && v2)


def finishKeyIndBasePrim (S : Setup)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ss kemCt : Bytes) (st : KeyIndState S) :
    OracleComp PrimBaseSpec (KeyIndResponse × Option (KeyIndState S)) := do
  let ekAPk ← primQ (.x25519Base ekASk)
  let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
  let dh2 ← primQ (.x25519 ekASk bundle.ikB)
  let dh3 ← primQ (.x25519 ekASk bundle.spkB)
  let dh4Raw ← primQ (.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD []))
  let dh4? := bundle.opkB?.map (fun _ => dh4Raw)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ← evalHkdfOrRoPrim true st.roCache secrets
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer ← isHonestUncorruptedPeerPrim S st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) ←
    checkBundleProvenancePrim S st.principals st.spkBundles st.opkEntries bundle
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
    drKeyRand   := drKeyReal
    hdr         := hdr
    tested      := false
  }
  let found ← findMPrim (fun r => keyIndPartnerPrim sessEntry r) (st.respSessions.take S.N_sess_tot)
  let drKeyRand ←
    match found with
    | some r => pure r.drKeyRand
    | none   => embedUnif sampleDRKey96
  let base' : KeyIndState S :=
    let sess' := { sessEntry with drKeyRand := drKeyRand } :: st.sessions
    { st with sessions := sess', roCache := roCache' }
  let peerPrin? ← findHonestPrincipalPrim S st.principals bundle.ikB
  let resp : KeyIndResponse :=
    match peerPrin? with
    | some _ => .hdrResp hdr
    | none   => .initUnfreshResp drKeyReal hdr
  return (resp, some base')


def postKemKeyIndPrim (S : Setup)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (hst : KeyIndShCrState S) (ss kemCt : Bytes) :
    OracleComp PrimBaseSpec (KeyIndResponse × KeyIndShCrState S) := do
  let ekASk ← embedUnif sampleScalar32
  let out ← finishKeyIndBasePrim S sid bundle uEntry ekASk ss kemCt hst.base
  return applyShCrFinish sid bundle.pqspkB ss kemCt hst out


def runKeyIndShCrInitiatePrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) :
    StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec) KeyIndResponse := fun hst => do
  match ← preCheckKeyIndPrim S sid u bundle hst.base with
  | none => return (.noneResp, hst)
  | some uEntry =>
    let ekASk ← embedUnif sampleScalar32
    let kemCoins ← embedUnif sampleCoins32
    let sigOk ← checkBundleSigsPrim S hst.base.principals bundle
    if !sigOk then
      return (.noneResp, hst)
    else
      match ← primQ (.kemEncaps bundle.pqspkB kemCoins) with
      | none =>
        return (.noneResp, { hst with sendCount := hst.sendCount + 1 })
      | some (ss, kemCt) =>
        let out ← finishKeyIndBasePrim S sid bundle uEntry ekASk ss kemCt hst.base
        return applyShCrFinish sid bundle.pqspkB ss kemCt hst out


def pqxdhKeyIndShCrPrimImpl (embedTarget : Bool) (S : Setup) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec))
  | .genSPK u j => runKeyIndShCrGenSPKPrim embedTarget S u j
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then pure .noneResp
    else runKeyIndShCrInitiatePrim S (.sendOPK u i) u bundle
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then pure .noneResp
    else runKeyIndShCrInitiatePrim S (.sendNoOPK u i) u bundle
  | .acceptOPK k j o hdr =>
    runKeyIndShCrAcceptPrim S k j hdr (.acceptOPK k j o hdr)
  | .acceptNoOPK k j l hdr =>
    runKeyIndShCrAcceptPrim S k j hdr (.acceptNoOPK k j l hdr)
  | q_other => liftShCrBasePrim (pqxdhKeyIndImplPrim true S q_other)


def isWinningKemShCrCtPrim (pk sk chosenPk ct ss candCt : Bytes) :
    OracleComp PrimBaseSpec Bool := do
  let dec ← primQ (.kemDecaps sk candCt)
  return (decide (dec = some ss) && decide (candCt ≠ ct ∨ chosenPk ≠ pk))


def extractCollidingKemCtPrim (N : ℕ)
    (pk sk chosenPk ct ss : Bytes) (recvRecs : List RecvKemRecord) :
    OracleComp PrimBaseSpec Bytes := do
  let pred := fun (r : RecvKemRecord) => isWinningKemShCrCtPrim pk sk chosenPk ct ss r.kemCt
  match ← findMPrim pred (recvRecs.take N) with
  | some r => return r.kemCt
  | none   => return ct


structure PausedShCrData (S : Setup) where
  sid    : SessionId S
  bundle : PreKeyBundleInput
  uEntry : PrincipalEntry
  hst    : KeyIndShCrState S
  cont   : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool


def tryPauseKeyIndQueryPrim (S : Setup) (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) : OracleComp PrimBaseSpec (Option (PausedShCrData S)) :=
  match gq, cont with
  | .initiateOPK u i bundle, cont =>
    if bundle.opkB?.isNone then pure none
    else do
      match ← preCheckKeyIndPrim S (.sendOPK u i) u bundle hst.base with
      | none => pure none
      | some uEntry =>
        let sigOk ← checkBundleSigsPrim S hst.base.principals bundle
        if !sigOk then pure none
        else if hst.sendCount == sIdx then
          pure (some {
            sid    := .sendOPK u i
            bundle := bundle
            uEntry := uEntry
            hst    := hst
            cont   := cont
          })
        else pure none
  | .initiateNoOPK u i bundle, cont =>
    if bundle.opkB?.isSome then pure none
    else do
      match ← preCheckKeyIndPrim S (.sendNoOPK u i) u bundle hst.base with
      | none => pure none
      | some uEntry =>
        let sigOk ← checkBundleSigsPrim S hst.base.principals bundle
        if !sigOk then pure none
        else if hst.sendCount == sIdx then
          pure (some {
            sid    := .sendNoOPK u i
            bundle := bundle
            uEntry := uEntry
            hst    := hst
            cont   := cont
          })
        else pure none
  | _, _ => pure none


def runWithFuelKeyIndShCrPrim (S : Setup)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ) :
    OracleComp PrimBaseSpec (Bool × KeyIndShCrState S) :=
  OracleComp.construct
    (C := fun _ => KeyIndShCrState S → ℕ → OracleComp PrimBaseSpec (Bool × KeyIndShCrState S))
    (fun b hst _ => return (b, hst))
    (fun q _ r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return (false, hst)
        | f + 1 => do
          let (out, hst') ← (pqxdhKeyIndShCrPrimImpl true S gq).run hst
          r out hst' f)
    oa hst fuel


def stepUntilShCrFuelKeyIndPrim (S : Setup) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ) :
    OracleComp PrimBaseSpec (Sum (Bool × KeyIndShCrState S) (PausedShCrData S)) :=
  OracleComp.construct
    (C := fun _ => KeyIndShCrState S → ℕ →
      OracleComp PrimBaseSpec (Sum (Bool × KeyIndShCrState S) (PausedShCrData S)))
    (fun b hst _ => return Sum.inl (b, hst))
    (fun q cont r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return Sum.inl (false, hst)
        | f + 1 => do
          match ← tryPauseKeyIndQueryPrim S sIdx gq cont hst with
          | some d => return Sum.inr d
          | none =>
            let (out, hst') ← (pqxdhKeyIndShCrPrimImpl true S gq).run hst
            r out hst' f)
    oa hst fuel


def resumePausedKeyIndPrim (S : Setup) (fuel : ℕ) (d : PausedShCrData S)
    (ss kemCt : Bytes) : OracleComp PrimBaseSpec (Bool × KeyIndShCrState S) := do
  let (resp, hst') ← postKemKeyIndPrim S d.sid d.bundle d.uEntry d.hst ss kemCt
  runWithFuelKeyIndShCrPrim S (d.cont resp) hst' fuel


abbrev ShCrFinishState (S : Setup) :=
  Bytes × Bytes × Bytes × Sum (Bool × KeyIndShCrState S) (PausedShCrData S)

def choosePkKeyIndPrimAt (S : Setup) (b : QueryBudget) (bIdx sIdx : ℕ)
    (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (Bytes × ShCrFinishState S) := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt : KeyIndShCrState S := {
    base        := KeyIndState.empty S secb
    targetBIdx? := some bIdx
    targetPk    := pk
    targetSk    := sk
  }
  let res ← stepUntilShCrFuelKeyIndPrim S sIdx A.run initSt b.q_total
  let chosenPk := match res with
    | Sum.inl _ => pk
    | Sum.inr d => d.bundle.pqspkB
  return (chosenPk, (pk, sk, chosenPk, res))

def findCollisionKeyIndPrim (S : Setup) (b : QueryBudget)
    (st : ShCrFinishState S) (ss ct : Bytes) : OracleComp PrimBaseSpec Bytes := do
  let (pk, sk, chosenPk, res) := st
  let (_, finalHst) ← match res with
    | Sum.inl done => pure done
    | Sum.inr d    => resumePausedKeyIndPrim S b.q_total d ss ct
  extractCollidingKemCtPrim b.q_total pk sk chosenPk ct ss finalHst.recvKemRecs


def sampleIndexRange (N : ℕ) : ProbComp ℕ :=
  if h : 0 < N then
    letI : NeZero N := ⟨Nat.ne_of_gt h⟩
    do
      let k ← ($ᵗ (Fin N) : ProbComp (Fin N))
      return k.val
  else
    return 0


def shcrReductionKeyIndCore (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) : KemShCrAdv where
  State := ShCrFinishState S
  choosePk := fun pk sk => do
    let idx ← embedUnif (sampleIndexRange (S.N_spk_tot * S.N_send_tot))
    choosePkKeyIndPrimAt S b (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk
  findCollision := findCollisionKeyIndPrim S b
  q_prim := primQueryBudget S b

/-- Two-stage `KemShCr` reduction adversary for two-key `KeyInd` (`G2 → G3`). -/
def shcrReductionKeyInd (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv :=
  shcrReductionKeyIndCore S b A.1



end RoKem

export RoKem (
  extractDh1
  extractDh3
  spkBundleFlatIdx
  ShCrState
  applyShCrFinish
  KeyIndShCrState
  isNoneKeyIndResp
  sessionSlotIndex
  liftShCrBasePrim
  recordAcceptKemGenericPrim
  runKeyIndShCrAcceptPrim
  genSpkTargetKeyIndPrim
  runKeyIndShCrGenSPKPrim
  preCheckKeyIndPrim
  checkBundleSigsPrim
  finishKeyIndBasePrim
  postKemKeyIndPrim
  runKeyIndShCrInitiatePrim
  pqxdhKeyIndShCrPrimImpl
  isWinningKemShCrCtPrim
  extractCollidingKemCtPrim
  PausedShCrData
  tryPauseKeyIndQueryPrim
  runWithFuelKeyIndShCrPrim
  stepUntilShCrFuelKeyIndPrim
  resumePausedKeyIndPrim
  ShCrFinishState
  choosePkKeyIndPrimAt
  findCollisionKeyIndPrim
  shcrReductionKeyIndCore
  shcrReductionKeyInd
)

end SignalPqxdh.Security
