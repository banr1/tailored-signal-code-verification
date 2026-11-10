/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KeyInd1KeyReal
public import Computational.Proofs.E2E.ComposedPrefixHelpers
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingF
import Computational.Proofs.E2E.ComposedPrefixTagSync
import VCVio.EvalDist.Monad.Basic

/-!
# Tag-Synchronized Lazy `KeyInd` Stepping for the 1-Key Real-HKDF Game

**Checked by Lean.**

Proves eager-to-lazy equivalence between the 1-key (`DEV-PQ13`) real-HKDF `KeyInd` oracle
`pqxdhKeyIndImpl1KeyReal` and the tag-synchronized lazy-`drKeyRand` implementation
`pqxdhKeyIndTagImpl1KeyReal`, along with the driver synchronization invariant
`DrvTagSyncInv1KeyReal` and its bridge to `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Prefix
open Proofs.SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security Proofs.SignalPqxdh.Security

namespace CryptoVerification.E2E

@[simp]
private theorem stateT_run_lift_1key {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM_1key {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

/-! ## 1-key real-HKDF `KeyInd` oracle -/

/-- Single-scalar `.initPrin` handler for the 1-key identity (`DEV-PQ13`). -/
def runKeyIndInitPrin1Key (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) :
    StateT (SignalPqxdh.KeyIndState S) ProbComp SignalPqxdh.KeyIndResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then
    return .noneResp
  let secIKA0 ← liftM SignalPqxdh.sampleScalar32
  let ikAPk := P.x25519Base secIKA0
  let ikSignPk := P.sigPkGen secIKA0
  let entry : SignalPqxdh.PrincipalEntry := {
    secIKA0    := secIKA0
    ikAPk      := ikAPk
    secIKAsign := secIKA0
    ikSignPk   := ikSignPk
    corrupted  := false
  }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp ikAPk ikSignPk

/-- Standard-model 1-key real-HKDF `KeyInd` oracle with `.revealDhSecrets` disabled. -/
def pqxdhKeyIndImpl1KeyReal (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) :
    QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp) := fun q =>
  match q with
  | .initPrin u => runKeyIndInitPrin1Key S P u
  | .roQuery secrets => do
    let st ← get
    let (dk, roCache') ← liftM (SignalPqxdh.evalHkdfOrRo false P st.roCache secrets)
    set { st with roCache := roCache' }
    return .drKeyResp dk
  | .revealDhSecrets => pure .noneResp
  | q => SignalPqxdh.pqxdhKeyIndImpl false S P q

@[simp]
theorem pqxdhKeyIndImpl1KeyReal_initPrin (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) :
    pqxdhKeyIndImpl1KeyReal S P (.initPrin u) = runKeyIndInitPrin1Key S P u := rfl

@[simp]
theorem pqxdhKeyIndImpl1KeyReal_roQuery (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (secrets : SignalPqxdh.Bytes) :
    pqxdhKeyIndImpl1KeyReal S P (.roQuery secrets) = (do
      let st ← get
      let (dk, roCache') ← liftM (SignalPqxdh.evalHkdfOrRo false P st.roCache secrets)
      set { st with roCache := roCache' }
      return .drKeyResp dk) := rfl

/-! ## Tag-synchronized lazy `drKeyRand` implementation -/

/-- Lazy-`drKeyRand` state for the 1-key real-HKDF `KeyInd` game. -/
structure KeyInd1KeyLazyState (S : SignalPqxdh.Setup) where
  base      : SignalPqxdh.KeyIndState S
  randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey) := []

def KeyInd1KeyLazyState.empty (S : SignalPqxdh.Setup) : KeyInd1KeyLazyState S :=
  { base := SignalPqxdh.KeyIndState.empty S false, randCache := [] }

def randLens1Key (S : SignalPqxdh.Setup) :
    CacheLens (KeyInd1KeyLazyState S) SignalPqxdh.Bytes where
  get lst := lst.randCache
  set lst c := { lst with randCache := c }
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  set_get _ := rfl

inductive Lazy1KeyPost where
  | done      (resp : SignalPqxdh.KeyIndResponse)
  | evalRand  (pid : SignalPqxdh.Bytes) (mkResp : SignalPqxdh.DRKey → SignalPqxdh.KeyIndResponse)
  | handshake (resp : SignalPqxdh.KeyIndResponse) (pid? : Option SignalPqxdh.Bytes)

def runLazy1KeyPost (eagerRand : Bool) (S : SignalPqxdh.Setup)
    (post : Lazy1KeyPost) (lst : KeyInd1KeyLazyState S) :
    ProbComp (SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S) :=
  match post with
  | .done resp => pure (resp, lst)
  | .evalRand pid mkResp => do
    let (dk, lst1) ← (randLens1Key S).eval lst pid
    return (mkResp dk, lst1)
  | .handshake resp pid? =>
    match pid? with
    | none => pure (resp, lst)
    | some pid =>
      if eagerRand then
        (randLens1Key S).eval lst pid >>= fun (_, lst1) => pure (resp, lst1)
      else
        pure (resp, lst)

def tagStepInitiate1KeyReal (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (st : SignalPqxdh.KeyIndState S) :
    ProbComp (Lazy1KeyPost × SignalPqxdh.KeyIndState S) := do
  if st.sessions.any (fun e => e.sid == sid) then
    return (.done .noneResp, st)
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return (.done .noneResp, st)
  if !SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return (.done .noneResp, st)
  let ekASk ← SignalPqxdh.sampleScalar32
  let kemCoins ← SignalPqxdh.sampleCoins32
  let sigPkB := SignalPqxdh.resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.done .noneResp, st)
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return (.done .noneResp, st)
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := SignalPqxdh.buildSecrets dh1 dh2 dh3 dh4? ss
  let drKeyReal := P.hkdfDerive96 secrets
  let hdr : SignalPqxdh.HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer := SignalPqxdh.isHonestUncorruptedPeer P st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    SignalPqxdh.checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
  let s0 : SignalPqxdh.KeyIndInitiatorEntry S := {
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
  let (randTag, pid?) := match st.respSessions.find? (fun r => SignalPqxdh.keyIndPartner P s0 r) with
    | some r => (r.drKeyRand, none)
    | none   => (tagDRKey (freshPidBytes st), some (freshPidBytes st))
  let resp := match SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with
    | some _ => SignalPqxdh.KeyIndResponse.hdrResp hdr
    | none   => SignalPqxdh.KeyIndResponse.initUnfreshResp drKeyReal hdr
  return (.handshake resp pid?,
          { st with sessions := { s0 with drKeyRand := randTag } :: st.sessions })

def tagStepAcceptOPK1KeyReal (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : SignalPqxdh.HandshakeHdr)
    (st : SignalPqxdh.KeyIndState S) :
    ProbComp (Lazy1KeyPost × SignalPqxdh.KeyIndState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.done .noneResp, st)
  if st.usedRecvOPK.contains (k.val, j.val, o.val) then
    return (.done .noneResp, st)
  if !SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk then
    return (.done .noneResp, st)
  let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
    | return (.done .noneResp, st)
  let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.done .noneResp, st)
  let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.done .noneResp, st)
  if oEntry.consumed then
    return (.done .noneResp, st)
  let (replayOk, usedTriples') :=
    SignalPqxdh.checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let accInp : SignalPqxdh.AcceptKeysInput := {
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
  let some _ := SignalPqxdh.Model.acceptKeys P accInp | return (.done .noneResp, st)
  let some ss := P.kemDecaps bEntry.pqspkSk hdr.kemCt | return (.done .noneResp, st)
  let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
  let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
  let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
  let dh4 := P.x25519 oEntry.opkSk hdr.ekAPk
  let secrets := SignalPqxdh.buildSecrets dh1 dh2 dh3 (some dh4) ss
  let drKey := P.hkdfDerive96 secrets
  let opkEntries' := st.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  let senderHonest := (SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk).isSome
  let r0 : SignalPqxdh.KeyIndRespEntry S := {
    sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
    opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
    senderHonest := senderHonest, drKeyReal := drKey, drKeyRand := drKey }
  let (randTag, pid?) := match st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r0) with
    | some s => (s.drKeyRand, none)
    | none   => (tagDRKey (freshPidBytes st), some (freshPidBytes st))
  let resp := match SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk with
    | some _ => SignalPqxdh.KeyIndResponse.acceptFreshResp
    | none   => SignalPqxdh.KeyIndResponse.drKeyResp drKey
  return (.handshake resp pid?, {
    st with
      opkEntries       := opkEntries'
      usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
      seenKyberBaseKeys := usedTriples'
      respSessions     := { r0 with drKeyRand := randTag } :: st.respSessions })

def tagStepAcceptNoOPK1KeyReal (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : SignalPqxdh.HandshakeHdr)
    (st : SignalPqxdh.KeyIndState S) :
    ProbComp (Lazy1KeyPost × SignalPqxdh.KeyIndState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.done .noneResp, st)
  if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    return (.done .noneResp, st)
  if !SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk then
    return (.done .noneResp, st)
  let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
    | return (.done .noneResp, st)
  let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.done .noneResp, st)
  let (replayOk, usedTriples') :=
    SignalPqxdh.checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let accInp : SignalPqxdh.AcceptKeysInput := {
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
  let some _ := SignalPqxdh.Model.acceptKeys P accInp | return (.done .noneResp, st)
  let some ss := P.kemDecaps bEntry.pqspkSk hdr.kemCt | return (.done .noneResp, st)
  let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
  let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
  let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
  let secrets := SignalPqxdh.buildSecrets dh1 dh2 dh3 none ss
  let drKey := P.hkdfDerive96 secrets
  let senderHonest := (SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk).isSome
  let r0 : SignalPqxdh.KeyIndRespEntry S := {
    sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
    opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
    senderHonest := senderHonest, drKeyReal := drKey, drKeyRand := drKey }
  let (randTag, pid?) := match st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r0) with
    | some s => (s.drKeyRand, none)
    | none   => (tagDRKey (freshPidBytes st), some (freshPidBytes st))
  let resp := match SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk with
    | some _ => SignalPqxdh.KeyIndResponse.acceptFreshResp
    | none   => SignalPqxdh.KeyIndResponse.drKeyResp drKey
  return (.handshake resp pid?, {
    st with
      usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
      seenKyberBaseKeys := usedTriples'
      respSessions     := { r0 with drKeyRand := randTag } :: st.respSessions })

def tagStepTestSession1KeyReal (testReal : Bool) (S : SignalPqxdh.Setup)
    (sid : SignalPqxdh.SessionId S) (st : SignalPqxdh.KeyIndState S) :
    ProbComp (Lazy1KeyPost × SignalPqxdh.KeyIndState S) := do
  if !SignalPqxdh.isKeyIndSessionTestable st sid then
    return (.done .noneResp, st)
  match st.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    let sessions' := st.sessions.map (fun s =>
      if s.sid == sid then { s with tested := true } else s)
    let post := if testReal then .done (.drKeyResp e.drKeyReal)
                else .evalRand e.drKeyRand.rootKey SignalPqxdh.KeyIndResponse.drKeyResp
    return (post, { st with sessions := sessions' })
  | none =>
    match st.respSessions.find? (fun r => r.sid == sid) with
    | none => return (.done .noneResp, st)
    | some r =>
      let resp' := st.respSessions.map (fun x =>
        if x.sid == sid then { x with tested := true } else x)
      let post := if testReal then .done (.drKeyResp r.drKeyReal)
                  else .evalRand r.drKeyRand.rootKey SignalPqxdh.KeyIndResponse.drKeyResp
      return (post, { st with respSessions := resp' })

def tagStepView1KeyReal (testReal : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S) :
    ProbComp (Lazy1KeyPost × SignalPqxdh.KeyIndState S) :=
  match q with
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then pure (.done .noneResp, st)
    else tagStepInitiate1KeyReal S P (.sendOPK u i) u bundle st
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then pure (.done .noneResp, st)
    else tagStepInitiate1KeyReal S P (.sendNoOPK u i) u bundle st
  | .acceptOPK k j o hdr => tagStepAcceptOPK1KeyReal S P k j o hdr st
  | .acceptNoOPK k j l hdr => tagStepAcceptNoOPK1KeyReal S P k j l hdr st
  | .testSession sid => tagStepTestSession1KeyReal testReal S sid st
  | q => do
    let (r, st') ← (pqxdhKeyIndImpl1KeyReal S P q).run st
    return (.done r, st')

/-- Tag-synchronized lazy-`drKeyRand` query implementation parameterized by `eagerRand` and `testReal`. -/
def pqxdhKeyIndTagImpl1KeyReal (eagerRand testReal : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) :
    QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (KeyInd1KeyLazyState S) ProbComp) := fun q =>
  StateT.mk fun lst => do
    let (post, base') ← tagStepView1KeyReal testReal S P q lst.base
    runLazy1KeyPost eagerRand S post { lst with base := base' }

private theorem isInvariant_pureResp_1Key {S : SignalPqxdh.Setup} (α : Type)
    (resp : SignalPqxdh.KeyIndResponse)
    {f : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool}
    (hf : (randLens1Key S).IsInvariant f) :
    (randLens1Key S).IsInvariant (fun (p : α × KeyInd1KeyLazyState S) => f (resp, p.2)) :=
  CacheLens.IsInvariant.map_state (randLens1Key S) (fun (_ : α) st => (resp, st))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) f hf

private theorem isInvariant_randLens1Key_runLazy1KeyPost_false {S : SignalPqxdh.Setup} {α : Type}
    (post : Lazy1KeyPost)
    {f : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool}
    (hf : (randLens1Key S).IsInvariant f) :
    (randLens1Key S).IsInvariant (fun (p : α × KeyInd1KeyLazyState S) =>
      runLazy1KeyPost false S post p.2 >>= f) := by
  cases post with
  | done resp =>
    simpa [runLazy1KeyPost] using isInvariant_pureResp_1Key α resp hf
  | evalRand pid mkResp =>
    simpa [runLazy1KeyPost, bind_assoc, pure_bind] using
      CacheLens.IsInvariant.eval_step (randLens1Key S)
        (fun _ _ => pid) (fun _ _ _ => rfl)
        (fun dk (p : α × KeyInd1KeyLazyState S) => f (mkResp dk, p.2))
        (fun dk => isInvariant_pureResp_1Key α (mkResp dk) hf)
  | handshake resp pid? =>
    cases pid? <;> simpa [runLazy1KeyPost] using isInvariant_pureResp_1Key α resp hf

theorem isInvariant_randLens1Key_tagImpl1KeyReal_false {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S)
    (f : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hf : (randLens1Key S).IsInvariant f) :
    (randLens1Key S).IsInvariant (fun (p : Unit × KeyInd1KeyLazyState S) =>
      (pqxdhKeyIndTagImpl1KeyReal false testReal S P q).run p.2 >>= f) := by
  have h1 := CacheLens.IsInvariant.bind_indep (randLens1Key S)
    (fun (_ : Unit) (lst : KeyInd1KeyLazyState S) => tagStepView1KeyReal testReal S P q lst.base)
    (fun _ _ _ => rfl)
    (fun y (p : Unit × KeyInd1KeyLazyState S) =>
      runLazy1KeyPost false S y.1 { p.2 with base := y.2 } >>= f)
    (fun y => CacheLens.IsInvariant.map_state (randLens1Key S)
      (fun (_ : Unit) (lst : KeyInd1KeyLazyState S) => ((), { lst with base := y.2 }))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun (p : Unit × KeyInd1KeyLazyState S) => runLazy1KeyPost false S y.1 p.2 >>= f)
      (isInvariant_randLens1Key_runLazy1KeyPost_false y.1 hf))
  simpa [pqxdhKeyIndTagImpl1KeyReal, StateT.run_mk, bind_assoc] using h1

private theorem evalDist_runLazy1KeyPost_eagerRand_eq {S : SignalPqxdh.Setup}
    (post : Lazy1KeyPost) (lst : KeyInd1KeyLazyState S)
    {f : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool}
    (hf : (randLens1Key S).IsInvariant f) :
    𝒟[runLazy1KeyPost true S post lst >>= f] =
      𝒟[runLazy1KeyPost false S post lst >>= f] := by
  cases post with
  | done _ => rfl
  | evalRand _ _ => rfl
  | handshake resp pid? =>
    cases pid? with
    | none => rfl
    | some pid =>
      dsimp only [runLazy1KeyPost]
      simp only [↓reduceIte, Bool.false_eq_true, bind_assoc, pure_bind]
      exact (isInvariant_pureResp_1Key Unit resp hf).2 () lst pid

theorem evalDist_tagImpl1KeyReal_eagerRand_eq {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (lst : KeyInd1KeyLazyState S)
    (f : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hf : (randLens1Key S).IsInvariant f) :
    𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P q).run lst >>= f] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal false testReal S P q).run lst >>= f] := by
  simp only [pqxdhKeyIndTagImpl1KeyReal, StateT.run_mk, bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨post, base'⟩ _ => ?_
  exact evalDist_runLazy1KeyPost_eagerRand_eq post { lst with base := base' } hf

theorem evalDist_simulateQ_tagImpl1KeyReal_eagerRand_eq {S : SignalPqxdh.Setup} {α : Type}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (oa : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α)
    {obs : α × KeyInd1KeyLazyState S → ProbComp Bool}
    (hObs : (randLens1Key S).IsInvariant obs)
    (lst : KeyInd1KeyLazyState S) :
    𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal true testReal S P)) oa).run lst >>= obs] =
      𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false testReal S P)) oa).run lst >>=
        obs] :=
  CacheLens.evalDist_simulateQ_eq_of_isInvariant (randLens1Key S)
    (pqxdhKeyIndTagImpl1KeyReal true testReal S P)
    (pqxdhKeyIndTagImpl1KeyReal false testReal S P)
    (isInvariant_randLens1Key_tagImpl1KeyReal_false testReal P)
    (evalDist_tagImpl1KeyReal_eagerRand_eq testReal P)
    oa hObs lst lst (CacheLens.Equiv.refl (randLens1Key S) lst)

/-! ## Eager-to-lazy equivalence -/

def resolveRandSessionEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (s : SignalPqxdh.KeyIndInitiatorEntry S) : SignalPqxdh.KeyIndInitiatorEntry S :=
  { s with drKeyRand := lookupCacheKey randCache s.drKeyRand.rootKey }

def resolveRandRespEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (r : SignalPqxdh.KeyIndRespEntry S) : SignalPqxdh.KeyIndRespEntry S :=
  { r with drKeyRand := lookupCacheKey randCache r.drKeyRand.rootKey }

def resolveRandBase {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (st : SignalPqxdh.KeyIndState S) : SignalPqxdh.KeyIndState S :=
  { st with
    sessions     := st.sessions.map (resolveRandSessionEntry randCache)
    respSessions := st.respSessions.map (resolveRandRespEntry randCache) }

@[simp]
theorem eraseSessionKeys_resolveRandSessionEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (s : SignalPqxdh.KeyIndInitiatorEntry S) :
    eraseSessionKeys (resolveRandSessionEntry randCache s) = eraseSessionKeys s := rfl

@[simp]
theorem eraseRespKeys_resolveRandRespEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (r : SignalPqxdh.KeyIndRespEntry S) :
    eraseRespKeys (resolveRandRespEntry randCache r) = eraseRespKeys r := rfl

@[simp]
theorem eraseStateKeysAndCache_resolveRandBase {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (st : SignalPqxdh.KeyIndState S) :
    eraseStateKeysAndCache (resolveRandBase randCache st) = eraseStateKeysAndCache st := by
  unfold eraseStateKeysAndCache resolveRandBase
  simp [List.map_map, Function.comp_def]

private theorem composedClean_eraseStateKeysAndCache_1Key {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (st : SignalPqxdh.KeyIndState S) :
    composedClean P (eraseStateKeysAndCache st) = composedClean P st := by
  unfold composedClean eraseStateKeysAndCache
  dsimp only
  rw [List.all_map, List.all_map]
  have h1 : ((fun s => !s.tested || SignalPqxdh.isKeyIndInitStillFresh P true st.principals
        st.spkBundles (List.map eraseRespKeys st.respSessions) s) ∘ eraseSessionKeys) =
      (fun s => !s.tested || SignalPqxdh.isKeyIndInitStillFresh P true st.principals
        st.spkBundles st.respSessions s) := by
    funext s; dsimp only [Function.comp_apply]; rw [isKeyIndInitStillFresh_erase]; rfl
  have h2 : ((fun r => !r.tested || SignalPqxdh.isKeyIndRespStillFresh P true st.principals
        st.spkBundles (List.map eraseSessionKeys st.sessions) r) ∘ eraseRespKeys) =
      (fun r => !r.tested || SignalPqxdh.isKeyIndRespStillFresh P true st.principals
        st.spkBundles st.sessions r) := by
    funext r; dsimp only [Function.comp_apply]; rw [isKeyIndRespStillFresh_erase]; rfl
  rw [h1, h2]

theorem composedClean_resolveRandBase {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives)
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (st : SignalPqxdh.KeyIndState S) :
    composedClean P (resolveRandBase randCache st) = composedClean P st := by
  rw [← composedClean_eraseStateKeysAndCache_1Key P (resolveRandBase randCache st),
      eraseStateKeysAndCache_resolveRandBase,
      composedClean_eraseStateKeysAndCache_1Key]

@[simp]
private theorem keyIndPartner_resolveRandSessionEntry {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives)
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (s : SignalPqxdh.KeyIndInitiatorEntry S) (r : SignalPqxdh.KeyIndRespEntry S) :
    SignalPqxdh.keyIndPartner P (resolveRandSessionEntry randCache s) r =
      SignalPqxdh.keyIndPartner P s r := rfl

@[simp]
private theorem keyIndPartner_resolveRandRespEntry {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives)
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (s : SignalPqxdh.KeyIndInitiatorEntry S) (r : SignalPqxdh.KeyIndRespEntry S) :
    SignalPqxdh.keyIndPartner P s (resolveRandRespEntry randCache r) =
      SignalPqxdh.keyIndPartner P s r := rfl

private theorem find_sid_map_resolveRandSessionEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (sessions : List (SignalPqxdh.KeyIndInitiatorEntry S)) (sid : SignalPqxdh.SessionId S) :
    (sessions.map (resolveRandSessionEntry randCache)).find? (fun e => e.sid == sid) =
      (sessions.find? (fun e => e.sid == sid)).map (resolveRandSessionEntry randCache) := by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons]
    have hSid : (resolveRandSessionEntry randCache s).sid = s.sid := rfl
    rw [hSid]
    cases (s.sid == sid) <;> [exact ih; rfl]

private theorem find_sid_map_resolveRandRespEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (respSessions : List (SignalPqxdh.KeyIndRespEntry S)) (sid : SignalPqxdh.SessionId S) :
    (respSessions.map (resolveRandRespEntry randCache)).find? (fun r => r.sid == sid) =
      (respSessions.find? (fun r => r.sid == sid)).map (resolveRandRespEntry randCache) := by
  induction respSessions with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons]
    have hSid : (resolveRandRespEntry randCache r).sid = r.sid := rfl
    rw [hSid]
    cases (r.sid == sid) <;> [exact ih; rfl]

private theorem find_partner_map_resolveRandSessionEntry {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives)
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (sessions : List (SignalPqxdh.KeyIndInitiatorEntry S))
    (r : SignalPqxdh.KeyIndRespEntry S) :
    (sessions.map (resolveRandSessionEntry randCache)).find?
        (fun s => SignalPqxdh.keyIndPartner P s r) =
      (sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r)).map
        (resolveRandSessionEntry randCache) := by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons, keyIndPartner_resolveRandSessionEntry]
    cases SignalPqxdh.keyIndPartner P s r <;> [exact ih; rfl]

private theorem find_partner_map_resolveRandRespEntry {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives)
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (respSessions : List (SignalPqxdh.KeyIndRespEntry S))
    (s : SignalPqxdh.KeyIndInitiatorEntry S) :
    (respSessions.map (resolveRandRespEntry randCache)).find?
        (fun r => SignalPqxdh.keyIndPartner P s r) =
      (respSessions.find? (fun r => SignalPqxdh.keyIndPartner P s r)).map
        (resolveRandRespEntry randCache) := by
  induction respSessions with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons, keyIndPartner_resolveRandRespEntry]
    cases SignalPqxdh.keyIndPartner P s r <;> [exact ih; rfl]

@[simp]
private theorem isFreshKeyIndSession_resolveRandBase {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (st : SignalPqxdh.KeyIndState S) (sid : SignalPqxdh.SessionId S) :
    SignalPqxdh.isKeyIndSessionTestable (resolveRandBase randCache st) sid =
      SignalPqxdh.isKeyIndSessionTestable st sid := by
  unfold SignalPqxdh.isKeyIndSessionTestable resolveRandBase
  dsimp only
  rw [find_sid_map_resolveRandSessionEntry, find_sid_map_resolveRandRespEntry]
  cases st.sessions.find? (fun e => e.sid == sid) with
  | some _ => rfl
  | none =>
    cases st.respSessions.find? (fun r => r.sid == sid) <;> rfl

private theorem map_resolveRandSessionEntry_cons {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (pid : SignalPqxdh.Bytes) (dk : SignalPqxdh.DRKey)
    (sessions : List (SignalPqxdh.KeyIndInitiatorEntry S))
    (hRand : ∀ s ∈ sessions,
      (randCache.find? (fun (x, _) => x == s.drKeyRand.rootKey)).isSome = true)
    (hNone : randCache.find? (fun (x, _) => x == pid) = none) :
    sessions.map (resolveRandSessionEntry ((pid, dk) :: randCache)) =
      sessions.map (resolveRandSessionEntry randCache) := by
  refine List.map_congr_left (fun s hs => ?_)
  have h1 := (lookupCacheKey_cons_of_find_none_of_isSome randCache s.drKeyRand.rootKey pid dk
    (hRand s hs) hNone).1
  simp [resolveRandSessionEntry, h1]

private theorem map_resolveRandRespEntry_cons {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (pid : SignalPqxdh.Bytes) (dk : SignalPqxdh.DRKey)
    (respSessions : List (SignalPqxdh.KeyIndRespEntry S))
    (hRand : ∀ r ∈ respSessions,
      (randCache.find? (fun (x, _) => x == r.drKeyRand.rootKey)).isSome = true)
    (hNone : randCache.find? (fun (x, _) => x == pid) = none) :
    respSessions.map (resolveRandRespEntry ((pid, dk) :: randCache)) =
      respSessions.map (resolveRandRespEntry randCache) := by
  refine List.map_congr_left (fun r hr => ?_)
  have h1 := (lookupCacheKey_cons_of_find_none_of_isSome randCache r.drKeyRand.rootKey pid dk
    (hRand r hr) hNone).1
  simp [resolveRandRespEntry, h1]

private theorem map_comm_resolveRandSessionEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (f : SignalPqxdh.KeyIndInitiatorEntry S → SignalPqxdh.KeyIndInitiatorEntry S)
    (hf : ∀ s, resolveRandSessionEntry randCache (f s) = f (resolveRandSessionEntry randCache s))
    (sessions : List (SignalPqxdh.KeyIndInitiatorEntry S)) :
    (sessions.map f).map (resolveRandSessionEntry randCache) =
      (sessions.map (resolveRandSessionEntry randCache)).map f := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun s _ => hf s)

private theorem map_comm_resolveRandRespEntry {S : SignalPqxdh.Setup}
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (f : SignalPqxdh.KeyIndRespEntry S → SignalPqxdh.KeyIndRespEntry S)
    (hf : ∀ r, resolveRandRespEntry randCache (f r) = f (resolveRandRespEntry randCache r))
    (respSessions : List (SignalPqxdh.KeyIndRespEntry S)) :
    (respSessions.map f).map (resolveRandRespEntry randCache) =
      (respSessions.map (resolveRandRespEntry randCache)).map f := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun r _ => hf r)

/-- Well-formedness invariant on `KeyInd1KeyLazyState S` when `eagerRand = true`. -/
structure WellFormed1KeyLazy {S : SignalPqxdh.Setup} (testReal : Bool)
    (lst : KeyInd1KeyLazyState S) : Prop where
  secb_eq   : lst.base.secb = testReal
  sess_rand : ∀ s ∈ lst.base.sessions,
    (lst.randCache.find? (fun (x, _) => x == s.drKeyRand.rootKey)).isSome = true
  resp_rand : ∀ r ∈ lst.base.respSessions,
    (lst.randCache.find? (fun (x, _) => x == r.drKeyRand.rootKey)).isSome = true
  rand_len  : ∀ p ∈ lst.randCache,
    p.1.length < lst.base.sessions.length + lst.base.respSessions.length

/-- Coupling relation between `pqxdhKeyIndImpl1KeyReal` and `pqxdhKeyIndTagImpl1KeyReal true`. -/
def RelEagerTag1Key {S : SignalPqxdh.Setup} (testReal : Bool)
    (st : SignalPqxdh.KeyIndState S) (lst : KeyInd1KeyLazyState S) : Prop :=
  st = resolveRandBase lst.randCache lst.base ∧ WellFormed1KeyLazy testReal lst

private theorem wellFormed1KeyLazy_of_map_sessions {S : SignalPqxdh.Setup} {testReal : Bool}
    (lst : KeyInd1KeyLazyState S)
    (f : SignalPqxdh.KeyIndInitiatorEntry S → SignalPqxdh.KeyIndInitiatorEntry S)
    (hRand : ∀ s, (f s).drKeyRand = s.drKeyRand)
    (hWF : WellFormed1KeyLazy testReal lst) :
    WellFormed1KeyLazy testReal
      { lst with base := { lst.base with sessions := lst.base.sessions.map f } } := by
  refine ⟨hWF.secb_eq, ?_, hWF.resp_rand, ?_⟩
  · intro s hs
    rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
    rw [hRand]; exact hWF.sess_rand s0 hs0
  · intro p hp
    simpa [List.length_map] using hWF.rand_len p hp

private theorem wellFormed1KeyLazy_of_map_respSessions {S : SignalPqxdh.Setup} {testReal : Bool}
    (lst : KeyInd1KeyLazyState S)
    (f : SignalPqxdh.KeyIndRespEntry S → SignalPqxdh.KeyIndRespEntry S)
    (hRand : ∀ r, (f r).drKeyRand = r.drKeyRand)
    (hWF : WellFormed1KeyLazy testReal lst) :
    WellFormed1KeyLazy testReal
      { lst with base := { lst.base with respSessions := lst.base.respSessions.map f } } := by
  refine ⟨hWF.secb_eq, hWF.sess_rand, ?_, ?_⟩
  · intro r hr
    rcases List.mem_map.mp hr with ⟨r0, hr0, rfl⟩
    rw [hRand]; exact hWF.resp_rand r0 hr0
  · intro p hp
    simpa [List.length_map] using hWF.rand_len p hp

private def IsSimple1KeyQuery {S : SignalPqxdh.Setup} (q : SignalPqxdh.KeyIndQuery S) : Prop :=
  (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
  (∃ u j, q = .genSPK u j) ∨ (∃ u j o, q = .genOPK u j o) ∨
  (∃ u j, q = .revealSpkSk u j) ∨ (∃ sk, q = .registerKey sk) ∨
  (∃ sec, q = .roQuery sec) ∨ q = .revealDhSecrets

private theorem pqxdhKeyIndImpl1KeyReal_resolveRandBase_of_simple {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives)
    (randCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (q : SignalPqxdh.KeyIndQuery S) (hSimple : IsSimple1KeyQuery q)
    (st : SignalPqxdh.KeyIndState S) :
    (pqxdhKeyIndImpl1KeyReal S P q).run (resolveRandBase randCache st) =
      Prod.map id (resolveRandBase randCache) <$> (pqxdhKeyIndImpl1KeyReal S P q).run st ∧
    (∀ y ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st),
      (y.2.secb, y.2.sessions, y.2.respSessions) = (st.secb, st.sessions, st.respSessions)) := by
  refine ⟨?_, ?_⟩
  · rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ |
      ⟨u, j, rfl⟩ | ⟨sk, rfl⟩ | ⟨sec, rfl⟩ | rfl
    · unfold pqxdhKeyIndImpl1KeyReal runKeyIndInitPrin1Key resolveRandBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs <;> simp [StateT.run_pure, StateT.run_set,
        Prod.map, map_eq_bind_pure_comp, bind_assoc]
    · unfold pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl resolveRandBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.principals.find? (fun (idx, _) => idx == u.val) <;>
        simp [StateT.run_pure, StateT.run_set, Prod.map]
    · unfold pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl resolveRandBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp [StateT.run_pure, Prod.map]
      · cases st.principals.find? (fun (idx, _) => idx == u.val) with
        | none => simp [StateT.run_pure, Prod.map]
        | some _ =>
          simp [StateT.run_bind, StateT.run_set, StateT.run_pure,
            Prod.map, map_eq_bind_pure_comp, bind_assoc]
    · unfold pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl resolveRandBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp [StateT.run_pure, Prod.map]
      · simp [StateT.run_bind, StateT.run_set, StateT.run_pure,
          Prod.map, map_eq_bind_pure_comp, bind_assoc]
    · unfold pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl resolveRandBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;>
        simp [StateT.run_pure, StateT.run_set, Prod.map]
    · unfold pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl resolveRandBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases SignalPqxdh.registerAdvKey P st.advKeys sk <;>
        simp [StateT.run_pure, StateT.run_set, Prod.map]
    · unfold pqxdhKeyIndImpl1KeyReal SignalPqxdh.evalHkdfOrRo resolveRandBase
      simp [StateT.run_pure, Prod.map]
    · unfold pqxdhKeyIndImpl1KeyReal resolveRandBase
      simp [StateT.run_pure, Prod.map]
  · change PreservesAt (fun s => (s.secb, s.sessions, s.respSessions)) st
      (pqxdhKeyIndImpl1KeyReal S P q)
    rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ |
      ⟨u, j, rfl⟩ | ⟨sk, rfl⟩ | ⟨sec, rfl⟩ | rfl
    · unfold pqxdhKeyIndImpl1KeyReal runKeyIndInitPrin1Key
      dsimp only
      prove_preserves_at
    all_goals
      unfold pqxdhKeyIndImpl1KeyReal
      try unfold SignalPqxdh.pqxdhKeyIndImpl
      try unfold SignalPqxdh.evalHkdfOrRo
      dsimp only
      prove_preserves_at

private theorem evalDist_step_relEagerTag1Key_of_simple {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (hSimple : IsSimple1KeyQuery q)
    (lst : KeyInd1KeyLazyState S) (hWF : WellFormed1KeyLazy testReal lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndImpl1KeyReal S P q).run (resolveRandBase lst.randCache lst.base) >>= k1] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P q).run lst >>= k2] := by
  have hBase := pqxdhKeyIndImpl1KeyReal_resolveRandBase_of_simple P lst.randCache q hSimple lst.base
  have hTag : (pqxdhKeyIndTagImpl1KeyReal true testReal S P q).run lst =
      ((pqxdhKeyIndImpl1KeyReal S P q).run lst.base >>= fun z =>
        pure (z.1, { lst with base := z.2 })) := by
    rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ |
        ⟨u, j, rfl⟩ | ⟨sk, rfl⟩ | ⟨sec, rfl⟩ | rfl <;>
      simp [pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal, runLazy1KeyPost,
        StateT.run_mk]
  rw [hBase.1, hTag, bind_map_left, bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
  have hEq := hBase.2 z hz
  injection hEq with hSecb hRest
  injection hRest with hSess hResp
  refine hk z.1 _ { lst with base := z.2 } ⟨rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [hSecb]; exact hWF.secb_eq
  · dsimp only; rw [hSess]; exact hWF.sess_rand
  · dsimp only; rw [hResp]; exact hWF.resp_rand
  · dsimp only; rw [hSess, hResp]; exact hWF.rand_len

private theorem pqxdhKeyIndImpl1KeyReal_revealSessionKey_run {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (st : SignalPqxdh.KeyIndState S) :
    (pqxdhKeyIndImpl1KeyReal S P (.revealSessionKey sid)).run st =
      match st.sessions.find? (fun e => e.sid == sid) with
      | some e =>
        if e.tested then pure (.noneResp, st)
        else
          let sessions' := st.sessions.map (fun s =>
            if s.sid == sid then { s with revealed := true } else s)
          pure (.drKeyResp e.drKeyReal, { st with sessions := sessions' })
      | none =>
        match st.respSessions.find? (fun r => r.sid == sid) with
        | none => pure (.noneResp, st)
        | some r =>
          if r.tested then pure (.noneResp, st)
          else
            let resp' := st.respSessions.map (fun x =>
              if x.sid == sid then { x with revealed := true } else x)
            pure (.drKeyResp r.drKeyReal, { st with respSessions := resp' }) := by
  dsimp only [pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    dsimp only
    cases e.tested <;> rfl
  | none =>
    dsimp only
    cases st.respSessions.find? (fun r => r.sid == sid) with
    | none => rfl
    | some r =>
      dsimp only
      cases r.tested <;> rfl

private theorem evalDist_step_relEagerTag1Key_revealSessionKey {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S)
    (lst : KeyInd1KeyLazyState S) (hWF : WellFormed1KeyLazy testReal lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndImpl1KeyReal S P (.revealSessionKey sid)).run
        (resolveRandBase lst.randCache lst.base) >>= k1] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P (.revealSessionKey sid)).run lst >>= k2] := by
  dsimp only [pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal, StateT.run_mk]
  simp only [pqxdhKeyIndImpl1KeyReal_revealSessionKey_run, bind_assoc]
  have hFindS : (resolveRandBase lst.randCache lst.base).sessions.find? (fun e => e.sid == sid) =
      (lst.base.sessions.find? (fun e => e.sid == sid)).map
        (resolveRandSessionEntry lst.randCache) :=
    find_sid_map_resolveRandSessionEntry lst.randCache lst.base.sessions sid
  have hFindR : (resolveRandBase lst.randCache lst.base).respSessions.find?
        (fun r => r.sid == sid) =
      (lst.base.respSessions.find? (fun r => r.sid == sid)).map
        (resolveRandRespEntry lst.randCache) :=
    find_sid_map_resolveRandRespEntry lst.randCache lst.base.respSessions sid
  rw [hFindS, hFindR]
  cases lst.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    dsimp only [Option.map]
    have hT : (resolveRandSessionEntry lst.randCache e).tested = e.tested := rfl
    have hK : (resolveRandSessionEntry lst.randCache e).drKeyReal = e.drKeyReal := rfl
    rw [hT, hK]
    cases e.tested
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazy1KeyPost]
      refine hk (.drKeyResp e.drKeyReal) _ _ ⟨?_, ?_⟩
      · unfold resolveRandBase
        simp only [map_comm_resolveRandSessionEntry lst.randCache
          (fun s => if s.sid == sid then { s with revealed := true } else s)
          (fun s => by
            have hs : (resolveRandSessionEntry lst.randCache s).sid = s.sid := rfl
            rw [hs]; cases s.sid == sid <;> rfl)]
      · exact wellFormed1KeyLazy_of_map_sessions lst
          (fun s => if s.sid == sid then { s with revealed := true } else s)
          (fun s => by cases s.sid == sid <;> rfl) hWF
    · simp only [↓reduceIte, pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
  | none =>
    dsimp only [Option.map]
    cases lst.base.respSessions.find? (fun r => r.sid == sid) with
    | none =>
      dsimp only [Option.map]
      simp only [pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
    | some r =>
      dsimp only [Option.map]
      have hT : (resolveRandRespEntry lst.randCache r).tested = r.tested := rfl
      have hK : (resolveRandRespEntry lst.randCache r).drKeyReal = r.drKeyReal := rfl
      rw [hT, hK]
      cases r.tested
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazy1KeyPost]
        refine hk (.drKeyResp r.drKeyReal) _ _ ⟨?_, ?_⟩
        · unfold resolveRandBase
          simp only [map_comm_resolveRandRespEntry lst.randCache
            (fun x => if x.sid == sid then { x with revealed := true } else x)
            (fun x => by
              have hx : (resolveRandRespEntry lst.randCache x).sid = x.sid := rfl
              rw [hx]; cases x.sid == sid <;> rfl)]
        · exact wellFormed1KeyLazy_of_map_respSessions lst
            (fun x => if x.sid == sid then { x with revealed := true } else x)
            (fun x => by cases x.sid == sid <;> rfl) hWF
      · simp only [↓reduceIte, pure_bind, runLazy1KeyPost]
        exact hk .noneResp _ lst ⟨rfl, hWF⟩

private theorem pqxdhKeyIndImpl1KeyReal_testSession_run {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (st : SignalPqxdh.KeyIndState S) :
    (pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run st =
      if !SignalPqxdh.isKeyIndSessionTestable st sid then
        pure (.noneResp, st)
      else
        match st.sessions.find? (fun e => e.sid == sid) with
        | some e =>
          let sessions' := st.sessions.map (fun s =>
            if s.sid == sid then { s with tested := true } else s)
          pure (.drKeyResp (if st.secb then e.drKeyReal else e.drKeyRand),
                { st with sessions := sessions' })
        | none =>
          match st.respSessions.find? (fun r => r.sid == sid) with
          | none => pure (.noneResp, st)
          | some r =>
            let resp' := st.respSessions.map (fun x =>
              if x.sid == sid then { x with tested := true } else x)
            pure (.drKeyResp (if st.secb then r.drKeyReal else r.drKeyRand),
                  { st with respSessions := resp' }) := by
  dsimp only [pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !SignalPqxdh.isKeyIndSessionTestable st sid
  · cases st.sessions.find? (fun e => e.sid == sid) with
    | some _ => rfl
    | none =>
      cases st.respSessions.find? (fun r => r.sid == sid) <;> rfl
  · rfl

private theorem evalDist_step_relEagerTag1Key_testSession {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S)
    (lst : KeyInd1KeyLazyState S) (hWF : WellFormed1KeyLazy testReal lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run
        (resolveRandBase lst.randCache lst.base) >>= k1] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P (.testSession sid)).run lst >>= k2] := by
  rw [pqxdhKeyIndImpl1KeyReal_testSession_run]
  dsimp only [pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal, tagStepTestSession1KeyReal,
    StateT.run_mk]
  have hFresh := isFreshKeyIndSession_resolveRandBase lst.randCache lst.base sid
  have hSecb : (resolveRandBase lst.randCache lst.base).secb = testReal := hWF.secb_eq
  have hFindS : (resolveRandBase lst.randCache lst.base).sessions.find? (fun e => e.sid == sid) =
      (lst.base.sessions.find? (fun e => e.sid == sid)).map
        (resolveRandSessionEntry lst.randCache) :=
    find_sid_map_resolveRandSessionEntry lst.randCache lst.base.sessions sid
  have hFindR : (resolveRandBase lst.randCache lst.base).respSessions.find?
        (fun r => r.sid == sid) =
      (lst.base.respSessions.find? (fun r => r.sid == sid)).map
        (resolveRandRespEntry lst.randCache) :=
    find_sid_map_resolveRandRespEntry lst.randCache lst.base.respSessions sid
  rw [hFresh, hFindS, hFindR]
  cases !SignalPqxdh.isKeyIndSessionTestable lst.base sid
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    cases hS : lst.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only [Option.map]
      have hMem : e ∈ lst.base.sessions := List.mem_of_find?_eq_some hS
      let fS : SignalPqxdh.KeyIndInitiatorEntry S → SignalPqxdh.KeyIndInitiatorEntry S :=
        fun s => if s.sid == sid then { s with tested := true } else s
      have hWF' := wellFormed1KeyLazy_of_map_sessions lst fS
        (fun s => by dsimp only [fS]; cases s.sid == sid <;> rfl) hWF
      have hStateEq :
          { resolveRandBase lst.randCache lst.base with
            sessions := (resolveRandBase lst.randCache lst.base).sessions.map fS } =
          resolveRandBase lst.randCache { lst.base with sessions := lst.base.sessions.map fS } := by
        unfold resolveRandBase
        simp only [map_comm_resolveRandSessionEntry lst.randCache fS
          (fun s => by
            dsimp only [fS]
            have hs : (resolveRandSessionEntry lst.randCache s).sid = s.sid := rfl
            rw [hs]; cases s.sid == sid <;> rfl)]
      cases hTr : testReal
      · have hKey : (if (resolveRandBase lst.randCache lst.base).secb
            then (resolveRandSessionEntry lst.randCache e).drKeyReal
            else (resolveRandSessionEntry lst.randCache e).drKeyRand) =
            lookupCacheKey lst.randCache e.drKeyRand.rootKey := by
          rw [hSecb, hTr]; rfl
        rw [hKey]
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazy1KeyPost,
          randLens1Key, CacheLens.eval, bind_assoc]
        rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ e.drKeyRand.rootKey (hWF.sess_rand e hMem)]
        simp only [pure_bind]
        exact hk (.drKeyResp (lookupCacheKey lst.randCache e.drKeyRand.rootKey)) _ _
          ⟨hStateEq, hWF'⟩
      · have hKey : (if (resolveRandBase lst.randCache lst.base).secb
            then (resolveRandSessionEntry lst.randCache e).drKeyReal
            else (resolveRandSessionEntry lst.randCache e).drKeyRand) = e.drKeyReal := by
          rw [hSecb, hTr]; rfl
        rw [hKey]
        simp only [↓reduceIte, pure_bind, runLazy1KeyPost]
        exact hk (.drKeyResp e.drKeyReal) _ _ ⟨hStateEq, hWF'⟩
    | none =>
      dsimp only [Option.map]
      cases hR : lst.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        dsimp only [Option.map]
        simp only [pure_bind, runLazy1KeyPost]
        exact hk .noneResp _ lst ⟨rfl, hWF⟩
      | some r =>
        dsimp only [Option.map]
        have hMem : r ∈ lst.base.respSessions := List.mem_of_find?_eq_some hR
        let fR : SignalPqxdh.KeyIndRespEntry S → SignalPqxdh.KeyIndRespEntry S :=
          fun x => if x.sid == sid then { x with tested := true } else x
        have hWF' := wellFormed1KeyLazy_of_map_respSessions lst fR
          (fun x => by dsimp only [fR]; cases x.sid == sid <;> rfl) hWF
        have hStateEq :
            { resolveRandBase lst.randCache lst.base with
              respSessions := (resolveRandBase lst.randCache lst.base).respSessions.map fR } =
            resolveRandBase lst.randCache
              { lst.base with respSessions := lst.base.respSessions.map fR } := by
          unfold resolveRandBase
          simp only [map_comm_resolveRandRespEntry lst.randCache fR
            (fun x => by
              dsimp only [fR]
              have hx : (resolveRandRespEntry lst.randCache x).sid = x.sid := rfl
              rw [hx]; cases x.sid == sid <;> rfl)]
        cases hTr : testReal
        · have hKey : (if (resolveRandBase lst.randCache lst.base).secb
              then (resolveRandRespEntry lst.randCache r).drKeyReal
              else (resolveRandRespEntry lst.randCache r).drKeyRand) =
              lookupCacheKey lst.randCache r.drKeyRand.rootKey := by
            rw [hSecb, hTr]; rfl
          rw [hKey]
          simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazy1KeyPost,
            randLens1Key, CacheLens.eval, bind_assoc]
          rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ r.drKeyRand.rootKey
            (hWF.resp_rand r hMem)]
          simp only [pure_bind]
          exact hk (.drKeyResp (lookupCacheKey lst.randCache r.drKeyRand.rootKey)) _ _
            ⟨hStateEq, hWF'⟩
        · have hKey : (if (resolveRandBase lst.randCache lst.base).secb
              then (resolveRandRespEntry lst.randCache r).drKeyReal
              else (resolveRandRespEntry lst.randCache r).drKeyRand) = r.drKeyReal := by
            rw [hSecb, hTr]; rfl
          rw [hKey]
          simp only [↓reduceIte, pure_bind, runLazy1KeyPost]
          exact hk (.drKeyResp r.drKeyReal) _ _ ⟨hStateEq, hWF'⟩
  · simp only [↓reduceIte, pure_bind, runLazy1KeyPost]
    exact hk .noneResp _ lst ⟨rfl, hWF⟩

private theorem evalHkdfOrRo_false (P : SignalPqxdh.Primitives)
    (roCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) (secrets : SignalPqxdh.Bytes) :
    SignalPqxdh.evalHkdfOrRo false P roCache secrets = pure (P.hkdfDerive96 secrets, roCache) :=
  rfl

private theorem evalDist_run_bind_eq_of_run_eq_pure {σ τ α : Type}
    {m : StateT σ ProbComp α} {resp : α}
    (hm : ∀ s, m.run s = pure (resp, s))
    (s1 : σ) (s2 : τ)
    (k1 : α × σ → ProbComp Bool) (k2 : α × τ → ProbComp Bool)
    (hk : 𝒟[k1 (resp, s1)] = 𝒟[k2 (resp, s2)]) :
    𝒟[m.run s1 >>= k1] = 𝒟[k2 (resp, s2)] := by
  rw [hm s1, pure_bind]
  exact hk

private theorem evalDist_step_relEagerTag1Key_initiate {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (lst : KeyInd1KeyLazyState S) (hWF : WellFormed1KeyLazy testReal lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(SignalPqxdh.runKeyIndInitiate false S P sid u bundle).run
        (resolveRandBase lst.randCache lst.base) >>= k1] =
      𝒟[(do
          let (post, base') ← tagStepInitiate1KeyReal S P sid u bundle lst.base
          runLazy1KeyPost true S post { lst with base := base' }) >>= k2] := by
  unfold SignalPqxdh.runKeyIndInitiate tagStepInitiate1KeyReal
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  have hAny : (resolveRandBase lst.randCache lst.base).sessions.any (fun e => e.sid == sid) =
      lst.base.sessions.any (fun e => e.sid == sid) := by
    unfold resolveRandBase; dsimp only; rw [List.any_map]; rfl
  have hPrin : (resolveRandBase lst.randCache lst.base).principals = lst.base.principals := rfl
  have hSpk : (resolveRandBase lst.randCache lst.base).spkBundles = lst.base.spkBundles := rfl
  have hOpk : (resolveRandBase lst.randCache lst.base).opkEntries = lst.base.opkEntries := rfl
  have hAdv : (resolveRandBase lst.randCache lst.base).advKeys = lst.base.advKeys := rfl
  have hRo : (resolveRandBase lst.randCache lst.base).roCache = lst.base.roCache := rfl
  rw [hAny]
  cases lst.base.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte, hPrin]
    cases lst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
    | some up =>
      rcases up with ⟨_, uEntry⟩
      dsimp only
      rw [hSpk, hOpk, hAdv]
      cases !SignalPqxdh.koskBundleOk P lst.base.principals lst.base.spkBundles
          lst.base.opkEntries lst.base.advKeys bundle
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_liftM_1key,
          bind_assoc, pure_bind]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ekASk _ => ?_
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun kemCoins _ => ?_
        cases !(P.sigVerify (SignalPqxdh.resolveSigPk P lst.base.principals bundle.ikB)
              (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P lst.base.principals bundle.ikB)
              (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
            exact hk .noneResp _ lst ⟨rfl, hWF⟩
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            dsimp only [SignalPqxdh.keyIndPartnerRandKey?]
            rw [hRo, evalHkdfOrRo_false]
            simp only [StateT.run_bind, stateT_run_liftM_1key, pure_bind]
            have hRespMap : (resolveRandBase lst.randCache lst.base).respSessions =
                lst.base.respSessions.map (resolveRandRespEntry lst.randCache) := rfl
            rw [hRespMap, find_partner_map_resolveRandRespEntry]
            set s0 : SignalPqxdh.KeyIndInitiatorEntry S := {
              sid := sid
              honestPeer := SignalPqxdh.isHonestUncorruptedPeer P lst.base.principals bundle.ikB
              peerIkPk := bundle.ikB
              peerSpkPk := bundle.spkB
              peerOpkPk? := bundle.opkB?.map Prod.snd
              peerPqspkPk := bundle.pqspkB
              spkHonest := (SignalPqxdh.checkBundleProvenance P lst.base.principals
                lst.base.spkBundles lst.base.opkEntries bundle).1
              opkHonest := (SignalPqxdh.checkBundleProvenance P lst.base.principals
                lst.base.spkBundles lst.base.opkEntries bundle).2.1
              pqspkHonest := (SignalPqxdh.checkBundleProvenance P lst.base.principals
                lst.base.spkBundles lst.base.opkEntries bundle).2.2
              ekASk := ekASk
              fresh := (SignalPqxdh.isHonestUncorruptedPeer P lst.base.principals bundle.ikB).isSome
              drKeyReal := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                (P.x25519 uEntry.secIKA0 bundle.spkB)
                (P.x25519 ekASk bundle.ikB)
                (P.x25519 ekASk bundle.spkB)
                (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss)
              drKeyRand := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                (P.x25519 uEntry.secIKA0 bundle.spkB)
                (P.x25519 ekASk bundle.ikB)
                (P.x25519 ekASk bundle.spkB)
                (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss)
              hdr := { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk,
                       spkId := bundle.spkId, opkId? := bundle.opkB?.map Prod.fst,
                       pqspkId := bundle.pqspkId, kemCt := kemCt }
              tested := false }
            cases hPart : lst.base.respSessions.find?
                (fun r => SignalPqxdh.keyIndPartner P s0 r) with
            | some r =>
              have hrMem : r ∈ lst.base.respSessions := List.mem_of_find?_eq_some hPart
              simp only [Option.map_some, StateT.run_bind, StateT.run_set,
                pure_bind, runLazy1KeyPost]
              refine evalDist_run_bind_eq_of_run_eq_pure
                (fun _ => by
                  cases SignalPqxdh.findHonestPrincipal P lst.base.principals bundle.ikB <;> rfl)
                _ _ k1 k2 ?_
              refine hk _ _ _ ⟨rfl, hWF.secb_eq, ?_, hWF.resp_rand, ?_⟩
              · intro s hs
                rcases List.mem_cons.mp hs with rfl | hs
                · exact hWF.resp_rand r hrMem
                · exact hWF.sess_rand s hs
              · intro p hp
                simp only [List.length_cons]
                have hlt := hWF.rand_len p hp
                omega
            | none =>
              have hFindPid : lst.randCache.find?
                  (fun (x, _) => x == freshPidBytes lst.base) = none :=
                find_none_of_length_lt lst.randCache (freshPidBytes lst.base)
                  (lst.base.sessions.length + lst.base.respSessions.length)
                  hWF.rand_len (freshPidBytes_length lst.base)
              simp only [Option.map_none, StateT.run_bind, stateT_run_liftM_1key, StateT.run_set,
                runLazy1KeyPost, ↓reduceIte, randLens1Key,
                CacheLens.eval, bind_assoc, pure_bind]
              rw [evalCache_eq_sample_of_find_none lst.randCache (freshPidBytes lst.base) hFindPid]
              simp only [bind_assoc, pure_bind]
              refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk _ => ?_
              refine evalDist_run_bind_eq_of_run_eq_pure
                (fun _ => by
                  cases SignalPqxdh.findHonestPrincipal P lst.base.principals bundle.ikB <;> rfl)
                _ _ k1 k2 ?_
              refine hk _ _ _ ⟨?_, hWF.secb_eq, ?_, ?_, ?_⟩
              · unfold resolveRandBase
                dsimp only [List.map]
                rw [map_resolveRandSessionEntry_cons lst.randCache (freshPidBytes lst.base) dk
                      lst.base.sessions hWF.sess_rand hFindPid,
                    map_resolveRandRespEntry_cons lst.randCache (freshPidBytes lst.base) dk
                      lst.base.respSessions hWF.resp_rand hFindPid]
                dsimp only [resolveRandSessionEntry]
                simp only [tagDRKey_rootKey, lookupCacheKey_cons_self]
              · intro s hs
                rcases List.mem_cons.mp hs with rfl | hs
                · simp [tagDRKey_rootKey]
                · exact find_cons_isSome_of_isSome _ _ _ _ (hWF.sess_rand s hs)
              · intro r hr
                exact find_cons_isSome_of_isSome _ _ _ _ (hWF.resp_rand r hr)
              · intro p hp
                simp only [List.mem_cons, List.length_cons] at hp ⊢
                rcases hp with rfl | hp
                · dsimp only; rw [freshPidBytes_length]; omega
                · have hlt := hWF.rand_len p hp; omega
        · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
          exact hk .noneResp _ lst ⟨rfl, hWF⟩
      · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
        exact hk .noneResp _ lst ⟨rfl, hWF⟩
  · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
    exact hk .noneResp _ lst ⟨rfl, hWF⟩

private theorem evalDist_step_relEagerTag1Key_acceptOPK {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : SignalPqxdh.HandshakeHdr)
    (lst : KeyInd1KeyLazyState S) (hWF : WellFormed1KeyLazy testReal lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndImpl1KeyReal S P (.acceptOPK k j o hdr)).run
        (resolveRandBase lst.randCache lst.base) >>= k1] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P (.acceptOPK k j o hdr)).run lst >>= k2] := by
  dsimp only [pqxdhKeyIndImpl1KeyReal, pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal,
    SignalPqxdh.pqxdhKeyIndImpl, tagStepAcceptOPK1KeyReal, StateT.run_mk]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  have hUsed : (resolveRandBase lst.randCache lst.base).usedRecvOPK = lst.base.usedRecvOPK := rfl
  have hPrin : (resolveRandBase lst.randCache lst.base).principals = lst.base.principals := rfl
  have hAdv : (resolveRandBase lst.randCache lst.base).advKeys = lst.base.advKeys := rfl
  have hSpk : (resolveRandBase lst.randCache lst.base).spkBundles = lst.base.spkBundles := rfl
  have hOpk : (resolveRandBase lst.randCache lst.base).opkEntries = lst.base.opkEntries := rfl
  have hKyb : (resolveRandBase lst.randCache lst.base).seenKyberBaseKeys =
      lst.base.seenKyberBaseKeys := rfl
  have hRo : (resolveRandBase lst.randCache lst.base).roCache = lst.base.roCache := rfl
  cases !(hdr.spkId == UInt32.ofNat j.val &&
          hdr.pqspkId == UInt32.ofNat j.val &&
          hdr.opkId? == some (UInt32.ofNat o.val) &&
          hdr.ikAPk.length == 32 &&
          hdr.ekAPk.length == 32)
  · simp only [Bool.false_eq_true, ↓reduceIte, hUsed]
    cases lst.base.usedRecvOPK.contains (k.val, j.val, o.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, hPrin, hAdv]
      cases !SignalPqxdh.koskSenderOk P lst.base.principals lst.base.advKeys hdr.ikAPk
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases lst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
          exact hk .noneResp _ lst ⟨rfl, hWF⟩
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          dsimp only
          rw [hSpk]
          cases lst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
            exact hk .noneResp _ lst ⟨rfl, hWF⟩
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            rw [hOpk]
            cases lst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none =>
              simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
              exact hk .noneResp _ lst ⟨rfl, hWF⟩
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              cases oEntry.consumed
              · simp only [Bool.false_eq_true, ↓reduceIte, hKyb]
                let ckyb := SignalPqxdh.checkAndMarkKyberBaseKeySeen lst.base.seenKyberBaseKeys k.val
                  hdr.pqspkId hdr.spkId hdr.ekAPk
                let accInp : SignalPqxdh.AcceptKeysInput := {
                  ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
                  spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
                  opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk,
                  pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                  replayOk := ckyb.1, hdr := hdr }
                cases SignalPqxdh.Model.acceptKeys P accInp with
                | none =>
                  simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
                  exact hk .noneResp _ lst ⟨rfl, hWF⟩
                | some _ =>
                  dsimp only
                  cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none =>
                    simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
                    exact hk .noneResp _ lst ⟨rfl, hWF⟩
                  | some ss =>
                    dsimp only [SignalPqxdh.recordKeyIndResp]
                    rw [hRo, evalHkdfOrRo_false]
                    simp only [StateT.run_bind, stateT_run_liftM_1key, StateT.run_set,
                      StateT.run_get, pure_bind, bind_assoc]
                    have hSessMap : (resolveRandBase lst.randCache lst.base).sessions =
                        lst.base.sessions.map (resolveRandSessionEntry lst.randCache) := rfl
                    rw [hSessMap, find_partner_map_resolveRandSessionEntry]
                    set r0 : SignalPqxdh.KeyIndRespEntry S := {
                      sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                      opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                      senderHonest :=
                        (SignalPqxdh.findHonestPrincipal P lst.base.principals hdr.ikAPk).isSome,
                      drKeyReal := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                        (P.x25519 bEntry.spkSk hdr.ikAPk)
                        (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                        (P.x25519 bEntry.spkSk hdr.ekAPk)
                        (some (P.x25519 oEntry.opkSk hdr.ekAPk)) ss),
                      drKeyRand := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                        (P.x25519 bEntry.spkSk hdr.ikAPk)
                        (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                        (P.x25519 bEntry.spkSk hdr.ekAPk)
                        (some (P.x25519 oEntry.opkSk hdr.ekAPk)) ss) }
                    cases hPart : lst.base.sessions.find?
                        (fun s => SignalPqxdh.keyIndPartner P s r0) with
                    | some s =>
                      have hsMem : s ∈ lst.base.sessions := List.mem_of_find?_eq_some hPart
                      simp only [Option.map_some, StateT.run_set,
                        pure_bind, runLazy1KeyPost]
                      refine evalDist_run_bind_eq_of_run_eq_pure
                        (fun _ => by
                          cases SignalPqxdh.findHonestPrincipal P lst.base.principals hdr.ikAPk <;>
                            rfl)
                        _ _ k1 k2 ?_
                      refine hk _ _ _ ⟨rfl, hWF.secb_eq, hWF.sess_rand, ?_, ?_⟩
                      · intro r hr
                        rcases List.mem_cons.mp hr with rfl | hr
                        · exact hWF.sess_rand s hsMem
                        · exact hWF.resp_rand r hr
                      · intro p hp
                        simp only [List.length_cons]
                        have hlt := hWF.rand_len p hp
                        omega
                    | none =>
                      have hFindPid : lst.randCache.find?
                          (fun (x, _) => x == freshPidBytes lst.base) = none :=
                        find_none_of_length_lt lst.randCache (freshPidBytes lst.base)
                          (lst.base.sessions.length + lst.base.respSessions.length)
                          hWF.rand_len (freshPidBytes_length lst.base)
                      simp only [Option.map_none, StateT.run_bind, stateT_run_liftM_1key,
                        StateT.run_set, runLazy1KeyPost, ↓reduceIte,
                        randLens1Key, CacheLens.eval, bind_assoc, pure_bind]
                      rw [evalCache_eq_sample_of_find_none lst.randCache (freshPidBytes lst.base)
                            hFindPid]
                      simp only [bind_assoc, pure_bind]
                      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk _ => ?_
                      refine evalDist_run_bind_eq_of_run_eq_pure
                        (fun _ => by
                          cases SignalPqxdh.findHonestPrincipal P lst.base.principals hdr.ikAPk <;>
                            rfl)
                        _ _ k1 k2 ?_
                      refine hk _ _ _ ⟨?_, hWF.secb_eq, ?_, ?_, ?_⟩
                      · unfold resolveRandBase
                        dsimp only [List.map]
                        rw [map_resolveRandSessionEntry_cons lst.randCache (freshPidBytes lst.base)
                              dk lst.base.sessions hWF.sess_rand hFindPid,
                            map_resolveRandRespEntry_cons lst.randCache (freshPidBytes lst.base)
                              dk lst.base.respSessions hWF.resp_rand hFindPid]
                        dsimp only [resolveRandRespEntry]
                        simp only [tagDRKey_rootKey, lookupCacheKey_cons_self]
                      · intro s hs
                        exact find_cons_isSome_of_isSome _ _ _ _ (hWF.sess_rand s hs)
                      · intro r hr
                        rcases List.mem_cons.mp hr with rfl | hr
                        · simp [tagDRKey_rootKey]
                        · exact find_cons_isSome_of_isSome _ _ _ _ (hWF.resp_rand r hr)
                      · intro p hp
                        simp only [List.mem_cons, List.length_cons] at hp ⊢
                        rcases hp with rfl | hp
                        · dsimp only; rw [freshPidBytes_length]; omega
                        · have hlt := hWF.rand_len p hp; omega
              · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
                exact hk .noneResp _ lst ⟨rfl, hWF⟩
      · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
        exact hk .noneResp _ lst ⟨rfl, hWF⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
  · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
    exact hk .noneResp _ lst ⟨rfl, hWF⟩

private theorem evalDist_step_relEagerTag1Key_acceptNoOPK {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : SignalPqxdh.HandshakeHdr)
    (lst : KeyInd1KeyLazyState S) (hWF : WellFormed1KeyLazy testReal lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndImpl1KeyReal S P (.acceptNoOPK k j l hdr)).run
        (resolveRandBase lst.randCache lst.base) >>= k1] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P (.acceptNoOPK k j l hdr)).run lst >>= k2] := by
  dsimp only [pqxdhKeyIndImpl1KeyReal, pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal,
    SignalPqxdh.pqxdhKeyIndImpl, tagStepAcceptNoOPK1KeyReal, StateT.run_mk]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  have hUsed : (resolveRandBase lst.randCache lst.base).usedRecvNoOPK =
      lst.base.usedRecvNoOPK := rfl
  have hPrin : (resolveRandBase lst.randCache lst.base).principals = lst.base.principals := rfl
  have hAdv : (resolveRandBase lst.randCache lst.base).advKeys = lst.base.advKeys := rfl
  have hSpk : (resolveRandBase lst.randCache lst.base).spkBundles = lst.base.spkBundles := rfl
  have hKyb : (resolveRandBase lst.randCache lst.base).seenKyberBaseKeys =
      lst.base.seenKyberBaseKeys := rfl
  have hRo : (resolveRandBase lst.randCache lst.base).roCache = lst.base.roCache := rfl
  cases !(hdr.spkId == UInt32.ofNat j.val &&
          hdr.pqspkId == UInt32.ofNat j.val &&
          hdr.opkId? == none &&
          hdr.ikAPk.length == 32 &&
          hdr.ekAPk.length == 32)
  · simp only [Bool.false_eq_true, ↓reduceIte, hUsed]
    cases lst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, hPrin, hAdv]
      cases !SignalPqxdh.koskSenderOk P lst.base.principals lst.base.advKeys hdr.ikAPk
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases lst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
          exact hk .noneResp _ lst ⟨rfl, hWF⟩
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          dsimp only
          rw [hSpk]
          cases lst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
            exact hk .noneResp _ lst ⟨rfl, hWF⟩
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            rw [hKyb]
            let ckyb := SignalPqxdh.checkAndMarkKyberBaseKeySeen lst.base.seenKyberBaseKeys k.val
              hdr.pqspkId hdr.spkId hdr.ekAPk
            let accInp : SignalPqxdh.AcceptKeysInput := {
              ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
              spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
              opkBSk? := none, pqspkBSk := bEntry.pqspkSk,
              pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
              replayOk := ckyb.1, hdr := hdr }
            cases SignalPqxdh.Model.acceptKeys P accInp with
            | none =>
              simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
              exact hk .noneResp _ lst ⟨rfl, hWF⟩
            | some _ =>
              dsimp only
              cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
              | none =>
                simp only [StateT.run_pure, pure_bind, runLazy1KeyPost]
                exact hk .noneResp _ lst ⟨rfl, hWF⟩
              | some ss =>
                dsimp only [SignalPqxdh.recordKeyIndResp]
                rw [hRo, evalHkdfOrRo_false]
                simp only [StateT.run_bind, stateT_run_liftM_1key, StateT.run_set,
                  StateT.run_get, pure_bind, bind_assoc]
                have hSessMap : (resolveRandBase lst.randCache lst.base).sessions =
                    lst.base.sessions.map (resolveRandSessionEntry lst.randCache) := rfl
                rw [hSessMap, find_partner_map_resolveRandSessionEntry]
                set r0 : SignalPqxdh.KeyIndRespEntry S := {
                  sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                  opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                  senderHonest :=
                    (SignalPqxdh.findHonestPrincipal P lst.base.principals hdr.ikAPk).isSome,
                  drKeyReal := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                    (P.x25519 bEntry.spkSk hdr.ikAPk)
                    (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                    (P.x25519 bEntry.spkSk hdr.ekAPk)
                    none ss),
                  drKeyRand := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                    (P.x25519 bEntry.spkSk hdr.ikAPk)
                    (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                    (P.x25519 bEntry.spkSk hdr.ekAPk)
                    none ss) }
                cases hPart : lst.base.sessions.find?
                    (fun s => SignalPqxdh.keyIndPartner P s r0) with
                | some s =>
                  have hsMem : s ∈ lst.base.sessions := List.mem_of_find?_eq_some hPart
                  simp only [Option.map_some, StateT.run_set,
                    pure_bind, runLazy1KeyPost]
                  refine evalDist_run_bind_eq_of_run_eq_pure
                    (fun _ => by
                      cases SignalPqxdh.findHonestPrincipal P lst.base.principals hdr.ikAPk <;>
                        rfl)
                    _ _ k1 k2 ?_
                  refine hk _ _ _ ⟨rfl, hWF.secb_eq, hWF.sess_rand, ?_, ?_⟩
                  · intro r hr
                    rcases List.mem_cons.mp hr with rfl | hr
                    · exact hWF.sess_rand s hsMem
                    · exact hWF.resp_rand r hr
                  · intro p hp
                    simp only [List.length_cons]
                    have hlt := hWF.rand_len p hp
                    omega
                | none =>
                  have hFindPid : lst.randCache.find?
                      (fun (x, _) => x == freshPidBytes lst.base) = none :=
                    find_none_of_length_lt lst.randCache (freshPidBytes lst.base)
                      (lst.base.sessions.length + lst.base.respSessions.length)
                      hWF.rand_len (freshPidBytes_length lst.base)
                  simp only [Option.map_none, StateT.run_bind, stateT_run_liftM_1key,
                    StateT.run_set, runLazy1KeyPost, ↓reduceIte,
                    randLens1Key, CacheLens.eval, bind_assoc, pure_bind]
                  rw [evalCache_eq_sample_of_find_none lst.randCache (freshPidBytes lst.base)
                        hFindPid]
                  simp only [bind_assoc, pure_bind]
                  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk _ => ?_
                  refine evalDist_run_bind_eq_of_run_eq_pure
                    (fun _ => by
                      cases SignalPqxdh.findHonestPrincipal P lst.base.principals hdr.ikAPk <;>
                        rfl)
                    _ _ k1 k2 ?_
                  refine hk _ _ _ ⟨?_, hWF.secb_eq, ?_, ?_, ?_⟩
                  · unfold resolveRandBase
                    dsimp only [List.map]
                    rw [map_resolveRandSessionEntry_cons lst.randCache (freshPidBytes lst.base)
                          dk lst.base.sessions hWF.sess_rand hFindPid,
                        map_resolveRandRespEntry_cons lst.randCache (freshPidBytes lst.base)
                          dk lst.base.respSessions hWF.resp_rand hFindPid]
                    dsimp only [resolveRandRespEntry]
                    simp only [tagDRKey_rootKey, lookupCacheKey_cons_self]
                  · intro s hs
                    exact find_cons_isSome_of_isSome _ _ _ _ (hWF.sess_rand s hs)
                  · intro r hr
                    rcases List.mem_cons.mp hr with rfl | hr
                    · simp [tagDRKey_rootKey]
                    · exact find_cons_isSome_of_isSome _ _ _ _ (hWF.resp_rand r hr)
                  · intro p hp
                    simp only [List.mem_cons, List.length_cons] at hp ⊢
                    rcases hp with rfl | hp
                    · dsimp only; rw [freshPidBytes_length]; omega
                    · have hlt := hWF.rand_len p hp; omega
      · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
        exact hk .noneResp _ lst ⟨rfl, hWF⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
  · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
    exact hk .noneResp _ lst ⟨rfl, hWF⟩

private theorem evalDist_step_relEagerTag1Key {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (lst : KeyInd1KeyLazyState S)
    (hRel : RelEagerTag1Key testReal st lst)
    (k1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S → ProbComp Bool)
    (k2 : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag1Key testReal s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndImpl1KeyReal S P q).run st >>= k1] =
      𝒟[(pqxdhKeyIndTagImpl1KeyReal true testReal S P q).run lst >>= k2] := by
  rcases hRel with ⟨rfl, hWF⟩
  cases q with
  | initPrin u =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _ (Or.inl ⟨u, rfl⟩) lst hWF k1 k2 hk
  | corruptIK u =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inl ⟨u, rfl⟩)) lst hWF k1 k2 hk
  | genSPK u j =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inr (Or.inl ⟨u, j, rfl⟩))) lst hWF k1 k2 hk
  | genOPK u j o =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, j, o, rfl⟩)))) lst hWF k1 k2 hk
  | revealSpkSk u j =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, j, rfl⟩))))) lst hWF k1 k2 hk
  | registerKey sk =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sk, rfl⟩)))))) lst hWF k1 k2 hk
  | roQuery sec =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sec, rfl⟩))))))) lst hWF k1 k2 hk
  | revealDhSecrets =>
    exact evalDist_step_relEagerTag1Key_of_simple testReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) lst hWF k1 k2 hk
  | revealSessionKey sid =>
    exact evalDist_step_relEagerTag1Key_revealSessionKey testReal P sid lst hWF k1 k2 hk
  | testSession sid =>
    exact evalDist_step_relEagerTag1Key_testSession testReal P sid lst hWF k1 k2 hk
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndImpl1KeyReal, pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal,
      SignalPqxdh.pqxdhKeyIndImpl, StateT.run_mk]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact evalDist_step_relEagerTag1Key_initiate testReal P (.sendOPK u i) u bundle lst hWF k1 k2
        hk
    · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndImpl1KeyReal, pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal,
      SignalPqxdh.pqxdhKeyIndImpl, StateT.run_mk]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact evalDist_step_relEagerTag1Key_initiate testReal P (.sendNoOPK u i) u bundle lst hWF k1
        k2 hk
    · simp only [↓reduceIte, StateT.run_pure, pure_bind, runLazy1KeyPost]
      exact hk .noneResp _ lst ⟨rfl, hWF⟩
  | acceptOPK k j o hdr =>
    exact evalDist_step_relEagerTag1Key_acceptOPK testReal P k j o hdr lst hWF k1 k2 hk
  | acceptNoOPK k j l hdr =>
    exact evalDist_step_relEagerTag1Key_acceptNoOPK testReal P k j l hdr lst hWF k1 k2 hk

/-- Eager-to-lazy equivalence for `pqxdhKeyIndImpl1KeyReal` under any `resolveRandBase`-invariant observation. -/
theorem evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_eq_tagImpl_obs
    {S : SignalPqxdh.Setup} {α : Type} (secb : Bool) (P : SignalPqxdh.Primitives)
    (oa : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α)
    (obs : α → SignalPqxdh.KeyIndState S → ProbComp Bool)
    (hObs : ∀ a rc st, obs a (resolveRandBase rc st) = obs a st) :
    𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndImpl1KeyReal S P)) oa).run
        (SignalPqxdh.KeyIndState.empty S secb) >>= fun (a, st) => obs a st] =
    𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false secb S P)) oa).run
        { base := SignalPqxdh.KeyIndState.empty S secb, randCache := [] } >>=
        fun (a, lst) => obs a lst.base] := by
  have hStepA :
      𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndImpl1KeyReal S P)) oa).run
          (SignalPqxdh.KeyIndState.empty S secb) >>= fun (a, st) => obs a st] =
      𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal true secb S P)) oa).run
          { base := SignalPqxdh.KeyIndState.empty S secb, randCache := [] } >>=
          fun (a, lst) => obs a lst.base] := by
    dsimp only [kioFullImpl]
    exact CacheLens.evalDist_simulateQ_eq_of_rel
      (RelEagerTag1Key secb)
      (pqxdhKeyIndImpl1KeyReal S P)
      (pqxdhKeyIndTagImpl1KeyReal true secb S P)
      (evalDist_step_relEagerTag1Key secb P)
      (fun p => obs p.1 p.2)
      (fun p => obs p.1 p.2.base)
      (fun a s1 s2 ⟨hEq, _⟩ => by subst hEq; rw [hObs])
      oa
      (SignalPqxdh.KeyIndState.empty S secb)
      { base := SignalPqxdh.KeyIndState.empty S secb, randCache := [] }
      ⟨rfl, rfl, by simp [SignalPqxdh.KeyIndState.empty],
       by simp [SignalPqxdh.KeyIndState.empty], by simp⟩
  rw [hStepA]
  exact evalDist_simulateQ_tagImpl1KeyReal_eagerRand_eq secb P oa
    (CacheLens.IsInvariant.of_cache_indep (randLens1Key S) _ (fun _ _ _ => rfl))
    { base := SignalPqxdh.KeyIndState.empty S secb, randCache := [] }

/-- Eager-to-lazy equivalence for `pqxdhKeyIndImpl1KeyReal` at `secb = false` under `composedClean P`. -/
theorem evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_false_eq_tagImpl
    {S : SignalPqxdh.Setup} {α : Type} (P : SignalPqxdh.Primitives)
    (oa : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α)
    (g : α → Bool → ProbComp Bool) :
    𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndImpl1KeyReal S P)) oa).run
        (SignalPqxdh.KeyIndState.empty S false) >>= fun (a, st) => g a (composedClean P st)] =
    𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false false S P)) oa).run
        (KeyInd1KeyLazyState.empty S) >>=
        fun (a, lst) => g a (composedClean P lst.base)] :=
  evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_eq_tagImpl_obs false P oa
    (fun a st => g a (composedClean P st))
    (fun a rc st => by rw [composedClean_resolveRandBase])

/-! ## Driver synchronization invariant -/

/-- Structural invariant on `KeyIndState S` combining `ValidLazyRand` and 32-byte `spkSk` length. -/
structure ValidTag1KeyCore {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) : Prop where
  rand : ValidLazyRand S P st
  spkSk_len : ∀ p ∈ st.spkBundles, p.2.spkSk.length = 32

theorem validTag1KeyCore_empty (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (secb : Bool) :
    ValidTag1KeyCore P (SignalPqxdh.KeyIndState.empty S secb) :=
  ⟨validLazyRand_empty S P secb, fun _ h => nomatch h⟩

private theorem initRandCases_1Key {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) (s : SignalPqxdh.KeyIndInitiatorEntry S)
    (hTag : s.drKeyRand =
      match st.respSessions.find? (fun r => SignalPqxdh.keyIndPartner P s r) with
      | some r => r.drKeyRand
      | none   => tagDRKey (freshPidBytes st)) :
    (∃ r0 ∈ st.respSessions, SignalPqxdh.keyIndPartner P s r0 = true ∧
      s.drKeyRand.rootKey = r0.drKeyRand.rootKey) ∨
    ((∀ r ∈ st.respSessions, SignalPqxdh.keyIndPartner P s r = false) ∧
      s.drKeyRand.rootKey.length = st.sessions.length + st.respSessions.length) := by
  cases hF : st.respSessions.find? (fun r => SignalPqxdh.keyIndPartner P s r) with
  | some r0 =>
    rw [hF] at hTag
    exact Or.inl ⟨r0, List.mem_of_find?_eq_some hF, List.find?_some hF,
      congrArg (·.rootKey) hTag⟩
  | none =>
    rw [hF] at hTag
    refine Or.inr ⟨fun r hr => Bool.eq_false_iff.mpr (fun hP => List.find?_eq_none.mp hF r hr hP),
      ?_⟩
    rw [hTag, tagDRKey_rootKey, freshPidBytes_length]

private theorem respRandCases_1Key {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) (r0 : SignalPqxdh.KeyIndRespEntry S) :
    let randTag := match st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r0) with
      | some s => s.drKeyRand
      | none   => tagDRKey (freshPidBytes st)
    let r := { r0 with drKeyRand := randTag }
    (∃ s0 ∈ st.sessions, SignalPqxdh.keyIndPartner P s0 r = true ∧
      r.drKeyRand.rootKey = s0.drKeyRand.rootKey) ∨
    ((∀ s ∈ st.sessions, SignalPqxdh.keyIndPartner P s r = false) ∧
      r.drKeyRand.rootKey.length = st.sessions.length + st.respSessions.length) := by
  dsimp only
  cases hF : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r0) with
  | some s0 =>
    have hp : SignalPqxdh.keyIndPartner P s0 r0 = true :=
      @List.find?_some _ (fun s => SignalPqxdh.keyIndPartner P s r0) _ _ hF
    exact Or.inl ⟨s0, List.mem_of_find?_eq_some hF, hp, rfl⟩
  | none =>
    refine Or.inr ⟨fun s hs => Bool.eq_false_iff.mpr (fun hP => List.find?_eq_none.mp hF s hs hP),
      ?_⟩
    dsimp only
    rw [tagDRKey_rootKey, freshPidBytes_length]

private theorem validTag1KeyCore_of_tagStepInitiate1KeyReal {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id)
    (bundle : SignalPqxdh.PreKeyBundleInput) (st : SignalPqxdh.KeyIndState S)
    (hCore : ValidTag1KeyCore P st)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepInitiate1KeyReal S P sid u bundle st)) :
    ValidTag1KeyCore P y.2 := by
  unfold tagStepInitiate1KeyReal at hy
  by_cases hAny : st.sessions.any (fun e => e.sid == sid) = true
  · simp only [hAny, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hCore
  · have hAnyF : st.sessions.any (fun e => e.sid == sid) = false := Bool.eq_false_iff.mpr hAny
    simp only [hAnyF, Bool.false_eq_true, ↓reduceIte] at hy
    cases hP : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hP] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hCore
    | some up =>
      rcases up with ⟨_, uEntry⟩
      rw [hP] at hy; dsimp only at hy
      cases hKosk : !SignalPqxdh.koskBundleOk P st.principals st.spkBundles
          st.opkEntries st.advKeys bundle
      · rw [hKosk] at hy
        simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind] at hy
        rcases hy with ⟨ekASk, _, kemCoins, _, hy⟩
        cases hSig : !(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)
        · rw [hSig] at hy
          simp only [Bool.false_eq_true, ↓reduceIte] at hy
          cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            rw [hKem] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
            subst hy; exact hCore
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            rw [hKem] at hy; dsimp only at hy
            simp only [support_pure, Set.mem_singleton_iff] at hy
            subst hy
            have hSidFresh : sid ∉ st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid := by
              intro hMem
              rcases List.mem_map.mp hMem with ⟨e, he, heSid⟩
              have hTrue : st.sessions.any (fun e => e.sid == sid) = true :=
                List.any_eq_true.mpr ⟨e, he, beq_iff_eq.mpr heSid⟩
              rw [hAnyF] at hTrue; cases hTrue
            refine ⟨validLazyRand_cons_session P hCore.rand _ rfl rfl
              (fun _ h => h) (fun _ h => h) (fun _ h => h) hSidFresh ?_, hCore.spkSk_len⟩
            refine initRandCases_1Key P st _ ?_
            dsimp only [SignalPqxdh.keyIndPartner]
            cases st.respSessions.find? _ <;> rfl
        · rw [hSig] at hy
          simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
          subst hy; exact hCore
      · rw [hKosk] at hy
        simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact hCore

private theorem validTag1KeyCore_of_tagStepAcceptOPK1KeyReal {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : SignalPqxdh.HandshakeHdr) (st : SignalPqxdh.KeyIndState S)
    (hCore : ValidTag1KeyCore P st)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepAcceptOPK1KeyReal S P k j o hdr st)) :
    ValidTag1KeyCore P y.2 := by
  unfold tagStepAcceptOPK1KeyReal at hy
  cases hHdrOk : (hdr.spkId == UInt32.ofNat j.val &&
      hdr.pqspkId == UInt32.ofNat j.val &&
      hdr.opkId? == some (UInt32.ofNat o.val) &&
      hdr.ikAPk.length == 32 &&
      hdr.ekAPk.length == 32)
  · rw [hHdrOk] at hy
    simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hCore
  · rw [hHdrOk] at hy
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hy
    simp only [Bool.and_eq_true, beq_iff_eq] at hHdrOk
    have hSpkId : hdr.spkId = UInt32.ofNat j.val := hHdrOk.1.1.1.1
    have hPqId : hdr.pqspkId = UInt32.ofNat j.val := hHdrOk.1.1.1.2
    by_cases hUsed : st.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [hUsed, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hCore
    · have hUsedF : st.usedRecvOPK.contains (k.val, j.val, o.val) = false :=
        Bool.eq_false_iff.mpr hUsed
      have hNotUsed : (k.val, j.val, o.val) ∉ st.usedRecvOPK :=
        fun hIn => hUsed (List.contains_iff_mem.mpr hIn)
      simp only [hUsedF, Bool.false_eq_true, ↓reduceIte] at hy
      cases hKosk : !SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk
      · rw [hKosk] at hy
        simp only [Bool.false_eq_true, ↓reduceIte] at hy
        cases hK : st.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          rw [hK] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
          subst hy; exact hCore
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          rw [hK] at hy; dsimp only at hy
          cases hB : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            rw [hB] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
            subst hy; exact hCore
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            rw [hB] at hy; dsimp only at hy
            cases hO : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none =>
              rw [hO] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy; exact hCore
            | some op =>
              rcases op with ⟨_, oEntry⟩
              rw [hO] at hy; dsimp only at hy
              cases hCons : oEntry.consumed
              · rw [hCons] at hy
                simp only [Bool.false_eq_true, ↓reduceIte] at hy
                let ckyb := SignalPqxdh.checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val
                  hdr.pqspkId hdr.spkId hdr.ekAPk
                let accInp : SignalPqxdh.AcceptKeysInput := {
                  ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
                  spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
                  opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk,
                  pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                  replayOk := ckyb.1, hdr := hdr }
                cases hAcc : SignalPqxdh.Model.acceptKeys P accInp with
                | none =>
                  have hAcc' := hAcc; dsimp only [accInp, ckyb] at hAcc'
                  rw [hAcc'] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
                  subst hy; exact hCore
                | some dkAcc =>
                  have hAcc' := hAcc; dsimp only [accInp, ckyb] at hAcc'
                  have hReplay : ckyb.1 = true := (acceptKeys_eq_some_imp P accInp hAcc).1
                  have hKybPair := checkAndMarkKyberUsed_eq_imp st.seenKyberBaseKeys
                    k.val hdr.pqspkId hdr.spkId hdr.ekAPk rfl hReplay
                  have hNotKyb : (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) ∉
                      st.seenKyberBaseKeys := hKybPair.1
                  have hTriplesEq : ckyb.2 =
                      (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) :: st.seenKyberBaseKeys :=
                    hKybPair.2
                  cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none =>
                    rw [hAcc'] at hy; dsimp only at hy
                    rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
                    subst hy; exact hCore
                  | some ss =>
                    rw [hAcc'] at hy; dsimp only at hy
                    rw [hDec] at hy; dsimp only at hy
                    simp only [support_pure, Set.mem_singleton_iff] at hy
                    subst hy
                    have hSidFresh : (.recvOPK k j o : SignalPqxdh.SessionId S) ∉
                        st.respSessions.map SignalPqxdh.KeyIndRespEntry.sid := by
                      intro hMem
                      rcases List.mem_map.mp hMem with ⟨r1, hr1, hr1Sid⟩
                      exact hNotUsed (hCore.rand.resp_used_opk r1 hr1 k j o hr1Sid)
                    have hBndFresh : (respBundleIdx (.recvOPK k j o : SignalPqxdh.SessionId S),
                        hdr.ekAPk) ∉ st.respSessions.map
                          (fun r' => (respBundleIdx r'.sid, r'.hdr.ekAPk)) := by
                      intro hMem
                      rcases List.mem_map.mp hMem with ⟨r1, hr1, hPair⟩
                      injection hPair with hIdx hEk
                      dsimp only [respBundleIdx] at hIdx
                      have hMemK := hCore.rand.resp_kyber_mem r1 hr1 k.val j.val hIdx
                      rw [hEk] at hMemK
                      have hNotKyb' := hNotKyb
                      rw [hPqId, hSpkId] at hNotKyb'
                      exact hNotKyb' hMemK
                    refine ⟨validLazyRand_cons_respSession P hCore.rand _ rfl rfl
                      (fun x hx => by
                        dsimp only; change x ∈ ckyb.2
                        rw [hTriplesEq]; exact List.mem_cons_of_mem _ hx)
                      (fun x hx => List.mem_cons_of_mem _ hx)
                      (fun x hx => hx)
                      hSidFresh hBndFresh
                      (fun k' j' hIdx => by
                        dsimp only [respBundleIdx] at hIdx
                        injection hIdx with hPair; injection hPair with hk' hj'
                        subst hk'; subst hj'
                        dsimp only; change _ ∈ ckyb.2
                        rw [hTriplesEq, hPqId, hSpkId]; exact List.mem_cons_self)
                      (fun k' j' o' hSid => by
                        dsimp only at hSid
                        injection hSid with hk' hj' ho'
                        subst hk'; subst hj'; subst ho'
                        exact List.mem_cons_self)
                      (fun _ _ _ hSid => by cases hSid)
                      ?_, hCore.spkSk_len⟩
                    let r0 : SignalPqxdh.KeyIndRespEntry S := {
                      sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                      opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                      senderHonest :=
                        (SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                      drKeyReal := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                        (P.x25519 bEntry.spkSk hdr.ikAPk)
                        (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                        (P.x25519 bEntry.spkSk hdr.ekAPk)
                        (some (P.x25519 oEntry.opkSk hdr.ekAPk)) ss),
                      drKeyRand := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                        (P.x25519 bEntry.spkSk hdr.ikAPk)
                        (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                        (P.x25519 bEntry.spkSk hdr.ekAPk)
                        (some (P.x25519 oEntry.opkSk hdr.ekAPk)) ss) }
                    have hRC := respRandCases_1Key P st r0
                    dsimp only at hRC
                    cases hFind : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r0) <;>
                      (rw [hFind] at hRC; exact hRC)
              · rw [hCons] at hy
                simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
                subst hy; exact hCore
      · rw [hKosk] at hy
        simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact hCore

private theorem validTag1KeyCore_of_tagStepAcceptNoOPK1KeyReal {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : SignalPqxdh.HandshakeHdr) (st : SignalPqxdh.KeyIndState S)
    (hCore : ValidTag1KeyCore P st)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepAcceptNoOPK1KeyReal S P k j l hdr st)) :
    ValidTag1KeyCore P y.2 := by
  unfold tagStepAcceptNoOPK1KeyReal at hy
  cases hHdrOk : (hdr.spkId == UInt32.ofNat j.val &&
      hdr.pqspkId == UInt32.ofNat j.val &&
      hdr.opkId? == none &&
      hdr.ikAPk.length == 32 &&
      hdr.ekAPk.length == 32)
  · rw [hHdrOk] at hy
    simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hCore
  · rw [hHdrOk] at hy
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hy
    simp only [Bool.and_eq_true, beq_iff_eq] at hHdrOk
    have hSpkId : hdr.spkId = UInt32.ofNat j.val := hHdrOk.1.1.1.1
    have hPqId : hdr.pqspkId = UInt32.ofNat j.val := hHdrOk.1.1.1.2
    by_cases hUsed : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [hUsed, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hCore
    · have hUsedF : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = false :=
        Bool.eq_false_iff.mpr hUsed
      have hNotUsed : (k.val, j.val, l.val) ∉ st.usedRecvNoOPK :=
        fun hIn => hUsed (List.contains_iff_mem.mpr hIn)
      simp only [hUsedF, Bool.false_eq_true, ↓reduceIte] at hy
      cases hKosk : !SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk
      · rw [hKosk] at hy
        simp only [Bool.false_eq_true, ↓reduceIte] at hy
        cases hK : st.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          rw [hK] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
          subst hy; exact hCore
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          rw [hK] at hy; dsimp only at hy
          cases hB : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            rw [hB] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
            subst hy; exact hCore
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            rw [hB] at hy; dsimp only at hy
            let ckyb := SignalPqxdh.checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val
              hdr.pqspkId hdr.spkId hdr.ekAPk
            let accInp : SignalPqxdh.AcceptKeysInput := {
              ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
              spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
              opkBSk? := none, pqspkBSk := bEntry.pqspkSk,
              pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
              replayOk := ckyb.1, hdr := hdr }
            cases hAcc : SignalPqxdh.Model.acceptKeys P accInp with
            | none =>
              have hAcc' := hAcc; dsimp only [accInp, ckyb] at hAcc'
              rw [hAcc'] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy; exact hCore
            | some dkAcc =>
              have hAcc' := hAcc; dsimp only [accInp, ckyb] at hAcc'
              have hReplay : ckyb.1 = true := (acceptKeys_eq_some_imp P accInp hAcc).1
              have hKybPair := checkAndMarkKyberUsed_eq_imp st.seenKyberBaseKeys
                k.val hdr.pqspkId hdr.spkId hdr.ekAPk rfl hReplay
              have hNotKyb : (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) ∉
                  st.seenKyberBaseKeys := hKybPair.1
              have hTriplesEq : ckyb.2 =
                  (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) :: st.seenKyberBaseKeys :=
                hKybPair.2
              cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
              | none =>
                rw [hAcc'] at hy; dsimp only at hy
                rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
                subst hy; exact hCore
              | some ss =>
                rw [hAcc'] at hy; dsimp only at hy
                rw [hDec] at hy; dsimp only at hy
                simp only [support_pure, Set.mem_singleton_iff] at hy
                subst hy
                have hSidFresh : (.recvNoOPK k j l : SignalPqxdh.SessionId S) ∉
                    st.respSessions.map SignalPqxdh.KeyIndRespEntry.sid := by
                  intro hMem
                  rcases List.mem_map.mp hMem with ⟨r1, hr1, hr1Sid⟩
                  exact hNotUsed (hCore.rand.resp_used_no_opk r1 hr1 k j l hr1Sid)
                have hBndFresh : (respBundleIdx (.recvNoOPK k j l : SignalPqxdh.SessionId S),
                    hdr.ekAPk) ∉ st.respSessions.map
                      (fun r' => (respBundleIdx r'.sid, r'.hdr.ekAPk)) := by
                  intro hMem
                  rcases List.mem_map.mp hMem with ⟨r1, hr1, hPair⟩
                  injection hPair with hIdx hEk
                  dsimp only [respBundleIdx] at hIdx
                  have hMemK := hCore.rand.resp_kyber_mem r1 hr1 k.val j.val hIdx
                  rw [hEk] at hMemK
                  have hNotKyb' := hNotKyb
                  rw [hPqId, hSpkId] at hNotKyb'
                  exact hNotKyb' hMemK
                refine ⟨validLazyRand_cons_respSession P hCore.rand _ rfl rfl
                  (fun x hx => by
                    dsimp only; change x ∈ ckyb.2
                    rw [hTriplesEq]; exact List.mem_cons_of_mem _ hx)
                  (fun x hx => hx)
                  (fun x hx => List.mem_cons_of_mem _ hx)
                  hSidFresh hBndFresh
                  (fun k' j' hIdx => by
                    dsimp only [respBundleIdx] at hIdx
                    injection hIdx with hPair; injection hPair with hk' hj'
                    subst hk'; subst hj'
                    dsimp only; change _ ∈ ckyb.2
                    rw [hTriplesEq, hPqId, hSpkId]; exact List.mem_cons_self)
                  (fun _ _ _ hSid => by nomatch hSid)
                  (fun k' j' l' hSid => by
                    dsimp only at hSid
                    injection hSid with hk' hj' hl'
                    subst hk'; subst hj'; subst hl'
                    exact List.mem_cons_self)
                  ?_, hCore.spkSk_len⟩
                let r0 : SignalPqxdh.KeyIndRespEntry S := {
                  sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
                  opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
                  senderHonest :=
                    (SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk).isSome,
                  drKeyReal := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                    (P.x25519 bEntry.spkSk hdr.ikAPk)
                    (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                    (P.x25519 bEntry.spkSk hdr.ekAPk)
                    none ss),
                  drKeyRand := P.hkdfDerive96 (SignalPqxdh.buildSecrets
                    (P.x25519 bEntry.spkSk hdr.ikAPk)
                    (P.x25519 kEntry.secIKA0 hdr.ekAPk)
                    (P.x25519 bEntry.spkSk hdr.ekAPk)
                    none ss) }
                have hRC := respRandCases_1Key P st r0
                dsimp only at hRC
                cases hFind : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r0) <;>
                  (rw [hFind] at hRC; exact hRC)
      · rw [hKosk] at hy
        simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact hCore

private theorem validTag1KeyCore_of_tagStepTestSession1KeyReal {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (st : SignalPqxdh.KeyIndState S) (hCore : ValidTag1KeyCore P st)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepTestSession1KeyReal testReal S sid st)) :
    ValidTag1KeyCore P y.2 := by
  unfold tagStepTestSession1KeyReal at hy
  cases hFr : !SignalPqxdh.isKeyIndSessionTestable st sid
  · rw [hFr] at hy
    simp only [Bool.false_eq_true, ↓reduceIte] at hy
    cases hS : st.sessions.find? (fun e => e.sid == sid) with
    | some _ =>
      rw [hS] at hy; dsimp only at hy
      simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      refine ⟨validLazyRand_of_map_flags P hCore.rand
        (fun s => if s.sid == sid then { s with tested := true } else s) id
        rfl (List.map_id _).symm rfl rfl rfl
        (fun s => by cases s.sid == sid <;> rfl)
        (fun s => by cases s.sid == sid <;> rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun s _ => by cases s.sid == sid <;> rfl), hCore.spkSk_len⟩
    | none =>
      rw [hS] at hy; dsimp only at hy
      cases hR : st.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        rw [hR] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact hCore
      | some _ =>
        rw [hR] at hy; dsimp only at hy
        simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        refine ⟨validLazyRand_of_map_flags P hCore.rand
          id (fun r => if r.sid == sid then { r with tested := true } else r)
          (List.map_id _).symm rfl rfl rfl rfl
          (fun _ => rfl) (fun _ => rfl)
          (fun r => by cases r.sid == sid <;> rfl)
          (fun r => by cases r.sid == sid <;> rfl)
          (fun r => by cases r.sid == sid <;> rfl)
          (fun _ r => by cases r.sid == sid <;> rfl), hCore.spkSk_len⟩
  · rw [hFr] at hy
    simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hCore

private theorem eq_fields_of_otherBase1KeyReal {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (q : SignalPqxdh.KeyIndQuery S)
    (hOther : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
              (∃ u j o, q = .genOPK u j o) ∨ (∃ sk, q = .registerKey sk) ∨
              (∃ sec, q = .roQuery sec) ∨ q = .revealDhSecrets)
    (st : SignalPqxdh.KeyIndState S)
    {z : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hz : z ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    (z.2.sessions, z.2.respSessions, z.2.seenKyberBaseKeys,
      z.2.usedRecvOPK, z.2.usedRecvNoOPK, z.2.spkBundles) =
    (st.sessions, st.respSessions, st.seenKyberBaseKeys,
      st.usedRecvOPK, st.usedRecvNoOPK, st.spkBundles) := by
  have hPres : PreservesAt
      (fun s => (s.sessions, s.respSessions, s.seenKyberBaseKeys,
                 s.usedRecvOPK, s.usedRecvNoOPK, s.spkBundles))
      st (pqxdhKeyIndImpl1KeyReal S P q) := by
    rcases hOther with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, o, rfl⟩ | ⟨sk, rfl⟩ | ⟨sec, rfl⟩ | rfl
    · unfold pqxdhKeyIndImpl1KeyReal runKeyIndInitPrin1Key
      dsimp only
      prove_preserves_at
    all_goals
      unfold pqxdhKeyIndImpl1KeyReal
      try unfold SignalPqxdh.pqxdhKeyIndImpl
      try unfold SignalPqxdh.evalHkdfOrRo
      dsimp only
      prove_preserves_at
  exact hPres z hz

private theorem validTag1KeyCore_of_otherBase1KeyReal {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (q : SignalPqxdh.KeyIndQuery S)
    (hOther : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
              (∃ u j o, q = .genOPK u j o) ∨ (∃ sk, q = .registerKey sk) ∨
              (∃ sec, q = .roQuery sec) ∨ q = .revealDhSecrets)
    (st : SignalPqxdh.KeyIndState S) (hCore : ValidTag1KeyCore P st)
    {z : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hz : z ∈ support ((pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    ValidTag1KeyCore P z.2 ∧ z.2.sessions = st.sessions ∧ z.2.spkBundles = st.spkBundles := by
  have hEq := eq_fields_of_otherBase1KeyReal P q hOther st hz
  injection hEq with hSess h1
  injection h1 with hResp h2
  injection h2 with hKyb h3
  injection h3 with hOpk h4
  injection h4 with hNoOpk hSpk
  exact ⟨⟨validLazyRand_of_eq_fields P hCore.rand hSess hResp
    (fun x hx => hKyb ▸ hx) (fun x hx => hOpk ▸ hx) (fun x hx => hNoOpk ▸ hx),
    fun p hp => hCore.spkSk_len p (hSpk ▸ hp)⟩, hSess, hSpk⟩

private theorem validTag1KeyCore_of_tagStepView1KeyReal {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S)
    (hCore : ValidTag1KeyCore P st)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepView1KeyReal testReal S P q st)) :
    ValidTag1KeyCore P y.2 := by
  cases q with
  | initiateOPK u i bundle =>
    dsimp only [tagStepView1KeyReal] at hy
    split_ifs at hy
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact hCore
    · exact validTag1KeyCore_of_tagStepInitiate1KeyReal P (.sendOPK u i) u bundle st hCore hy
  | initiateNoOPK u i bundle =>
    dsimp only [tagStepView1KeyReal] at hy
    split_ifs at hy
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact hCore
    · exact validTag1KeyCore_of_tagStepInitiate1KeyReal P (.sendNoOPK u i) u bundle st hCore hy
  | acceptOPK k j o hdr =>
    exact validTag1KeyCore_of_tagStepAcceptOPK1KeyReal P k j o hdr st hCore hy
  | acceptNoOPK k j l hdr =>
    exact validTag1KeyCore_of_tagStepAcceptNoOPK1KeyReal P k j l hdr st hCore hy
  | testSession sid =>
    exact validTag1KeyCore_of_tagStepTestSession1KeyReal testReal P sid st hCore hy
  | revealSessionKey sid =>
    dsimp only [tagStepView1KeyReal] at hy
    rw [pqxdhKeyIndImpl1KeyReal_revealSessionKey_run] at hy
    cases hS : st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      rw [hS] at hy; dsimp only at hy
      split_ifs at hy
      · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy; exact hCore
      · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ⟨validLazyRand_of_map_flags P hCore.rand
          (fun s => if s.sid == sid then { s with revealed := true } else s) id
          rfl (List.map_id _).symm rfl rfl rfl
          (fun s => by cases s.sid == sid <;> rfl)
          (fun s => by cases s.sid == sid <;> rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun s _ => by cases s.sid == sid <;> rfl), hCore.spkSk_len⟩
    | none =>
      rw [hS] at hy; dsimp only at hy
      cases hR : st.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        rw [hR] at hy; simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact hCore
      | some r =>
        rw [hR] at hy; dsimp only at hy
        split_ifs at hy
        · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy; exact hCore
        · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
          exact ⟨validLazyRand_of_map_flags P hCore.rand
            id (fun x => if x.sid == sid then { x with revealed := true } else x)
            (List.map_id _).symm rfl rfl rfl rfl
            (fun _ => rfl) (fun _ => rfl)
            (fun x => by cases x.sid == sid <;> rfl)
            (fun x => by cases x.sid == sid <;> rfl)
            (fun x => by cases x.sid == sid <;> rfl)
            (fun _ x => by cases x.sid == sid <;> rfl), hCore.spkSk_len⟩
  | genSPK u j =>
    dsimp only [tagStepView1KeyReal, pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl] at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hCore
    · cases hP : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hP] at hy
        simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact hCore
      | some up =>
        rcases up with ⟨_, uEntry⟩
        rw [hP] at hy; dsimp only at hy
        simp only [StateT.run_bind, stateT_run_liftM_1key, StateT.run_set, StateT.run_pure,
          pure_bind, bind_assoc, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hy
        rcases hy with ⟨spkSk, hSpkSk, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        refine ⟨validLazyRand_of_eq_fields P hCore.rand rfl rfl
          (fun _ h => h) (fun _ h => h) (fun _ h => h), ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact length_of_mem_support_sampleScalar32 hSpkSk
        · exact hCore.spkSk_len p hp
  | revealSpkSk u j =>
    dsimp only [tagStepView1KeyReal, pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl] at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    cases hB : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      rw [hB] at hy
      simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hCore
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      rw [hB] at hy; dsimp only at hy
      have hRun : (do
          let spkBundles' := st.spkBundles.map (fun (idx, b) =>
            if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
          set { st with spkBundles := spkBundles' }
          return SignalPqxdh.KeyIndResponse.spkSkResp bEntry.spkSk :
            StateT (SignalPqxdh.KeyIndState S) ProbComp _).run st =
          pure (.spkSkResp bEntry.spkSk,
            { st with spkBundles := st.spkBundles.map (fun (idx, b) =>
                if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) }) :=
        rfl
      rw [hRun] at hy
      simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨validLazyRand_of_eq_fields P hCore.rand rfl rfl
        (fun _ h => h) (fun _ h => h) (fun _ h => h), ?_⟩
      intro p hp
      rcases List.mem_map.mp hp with ⟨⟨idx, b⟩, hb, rfl⟩
      split_ifs <;> exact hCore.spkSk_len (idx, b) hb
  | initPrin u =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (validTag1KeyCore_of_otherBase1KeyReal P _ (Or.inl ⟨u, rfl⟩) st hCore hz).1
  | corruptIK u =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (validTag1KeyCore_of_otherBase1KeyReal P _ (Or.inr (Or.inl ⟨u, rfl⟩)) st hCore hz).1
  | genOPK u j o =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (validTag1KeyCore_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inl ⟨u, j, o, rfl⟩))) st hCore hz).1
  | registerKey sk =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (validTag1KeyCore_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨sk, rfl⟩)))) st hCore hz).1
  | roQuery sec =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (validTag1KeyCore_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sec, rfl⟩))))) st hCore hz).1
  | revealDhSecrets =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (validTag1KeyCore_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) st hCore hz).1

private theorem runLazy1KeyPost_base_eq {S : SignalPqxdh.Setup}
    (eagerRand : Bool) (post : Lazy1KeyPost) (lst : KeyInd1KeyLazyState S)
    {z : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S}
    (hz : z ∈ support (runLazy1KeyPost eagerRand S post lst)) :
    z.2.base = lst.base := by
  cases post with
  | done _ =>
    simp only [runLazy1KeyPost, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | evalRand pid mkR =>
    simp only [runLazy1KeyPost, randLens1Key, CacheLens.eval, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨⟨_, _⟩, _, rfl⟩
    rfl
  | handshake _ pid? =>
    cases pid? with
    | none =>
      simp only [runLazy1KeyPost, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
    | some pid =>
      cases eagerRand
      · simp only [runLazy1KeyPost, Bool.false_eq_true, ↓reduceIte, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; rfl
      · simp only [runLazy1KeyPost, ↓reduceIte, randLens1Key, CacheLens.eval, bind_assoc,
          pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨⟨_, _⟩, _, rfl⟩
        rfl

theorem validTag1KeyCore_of_tagImpl1KeyReal {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (eagerRand testReal : Bool)
    (q : SignalPqxdh.KeyIndQuery S) (lst : KeyInd1KeyLazyState S)
    (hCore : ValidTag1KeyCore P lst.base)
    {z : SignalPqxdh.KeyIndResponse × KeyInd1KeyLazyState S}
    (hz : z ∈ support ((pqxdhKeyIndTagImpl1KeyReal eagerRand testReal S P q).run lst)) :
    ValidTag1KeyCore P z.2.base := by
  dsimp only [pqxdhKeyIndTagImpl1KeyReal, StateT.run_mk] at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨post, base'⟩, hStep, hPost⟩
  rw [runLazy1KeyPost_base_eq eagerRand post { lst with base := base' } hPost]
  exact validTag1KeyCore_of_tagStepView1KeyReal testReal P q lst.base hCore hStep

private def entryEkAPk1Key {S : SignalPqxdh.Setup} :
    SignalPqxdh.KeyIndInitiatorEntry S ⊕ SignalPqxdh.KeyIndRespEntry S → SignalPqxdh.Bytes
  | .inl s => s.hdr.ekAPk
  | .inr r => r.hdr.ekAPk

private theorem samePartnerComp_entryEkAPk_eq_1Key {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (st : SignalPqxdh.KeyIndState S)
    {x y : SignalPqxdh.KeyIndInitiatorEntry S ⊕ SignalPqxdh.KeyIndRespEntry S}
    (h : SamePartnerComp P st x y) :
    entryEkAPk1Key x = entryEkAPk1Key y := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | partner _ _ hp =>
    unfold SignalPqxdh.keyIndPartner at hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hp.1.1.2

/-- Driver synchronization invariant between `DrvState S ℓ` and `KeyInd1KeyLazyState S`. -/
structure DrvTagSyncInv1KeyReal {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives)
    (ds : DrvState S ℓ) (lst : KeyInd1KeyLazyState S) : Prop where
  core : ValidTag1KeyCore P lst.base
  sends_sess : ∀ x ∈ ds.sends, ∃ e ∈ lst.base.sessions, e.sid = x.1 ∧ e.hdr = x.2.2
  bundles_spk : ∀ b ∈ ds.bundles,
    lst.base.spkBundles.any (fun (idx, _) => idx == (b.1.1.val, b.1.2.val)) = true
  cache_insts : ∀ k ∈ lst.randCache.map Prod.fst, ∃ d ∈ ds.insts, ∃ e ∈ lst.base.sessions,
    e.drKeyRand.rootKey = k ∧ d.hdr.ekAPk = e.hdr.ekAPk

theorem drvTagSyncInv1KeyReal_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives) :
    DrvTagSyncInv1KeyReal P ({} : DrvState S ℓ) (KeyInd1KeyLazyState.empty S) :=
  ⟨validTag1KeyCore_empty S P false,
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h)⟩

theorem DrvTagSyncInv1KeyReal.empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives) :
    DrvTagSyncInv1KeyReal P ({} : DrvState S ℓ) (KeyInd1KeyLazyState.empty S) :=
  drvTagSyncInv1KeyReal_empty P

theorem DrvTagSyncInv1KeyReal.of_randCache_map_fst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {ds : DrvState S ℓ} {lst : KeyInd1KeyLazyState S}
    (h : DrvTagSyncInv1KeyReal P ds lst) {rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)}
    (hrc : lst.randCache.map Prod.fst = rc2.map Prod.fst) :
    DrvTagSyncInv1KeyReal P ds { lst with randCache := rc2 } :=
  ⟨h.core, h.sends_sess, h.bundles_spk, fun k hk => h.cache_insts k (hrc.symm ▸ hk)⟩

private def Lazy1KeyPost.respOf : Lazy1KeyPost → SignalPqxdh.KeyIndResponse
  | .done resp => resp
  | .evalRand _ mkResp => mkResp (tagDRKey [])
  | .handshake resp _ => resp

private theorem Lazy1KeyPost.done_ne_evalRand (r : SignalPqxdh.KeyIndResponse) :
    ∀ pid mkR, Lazy1KeyPost.done r ≠ .evalRand pid mkR :=
  fun _ _ h => by cases h

private theorem Lazy1KeyPost.handshake_ne_evalRand (r : SignalPqxdh.KeyIndResponse)
    (pid? : Option SignalPqxdh.Bytes) :
    ∀ pid mkR, Lazy1KeyPost.handshake r pid? ≠ .evalRand pid mkR :=
  fun _ _ h => by cases h

private theorem runLazy1KeyPost_false_of_not_evalRand {S : SignalPqxdh.Setup}
    {post : Lazy1KeyPost} (h : ∀ pid mkR, post ≠ .evalRand pid mkR)
    (lst : KeyInd1KeyLazyState S) :
    runLazy1KeyPost false S post lst = pure (post.respOf, lst) := by
  cases post with
  | done _ => rfl
  | evalRand pid mkR => exact False.elim (h pid mkR rfl)
  | handshake _ pid? => cases pid? <;> rfl

private structure TagStepSync1KeyReal {S : SignalPqxdh.Setup}
    (q : SignalPqxdh.KeyIndQuery S) (st0 : SignalPqxdh.KeyIndState S)
    (post : Lazy1KeyPost) (st' : SignalPqxdh.KeyIndState S) : Prop where
  not_evalRand : ∀ pid mkR, post ≠ .evalRand pid mkR
  sess_mono : ∀ e ∈ st0.sessions,
    ∃ e' ∈ st'.sessions, e'.sid = e.sid ∧ e'.hdr = e.hdr ∧ e'.drKeyRand = e.drKeyRand
  spk_mono : ∀ (u : Fin S.N_id) (j' : Fin S.N_recv),
    st0.spkBundles.any (fun (k, _) => k == (u.val, j'.val)) = true →
    st'.spkBundles.any (fun (k, _) => k == (u.val, j'.val)) = true
  init_post : ∀ bnd (sid : SignalPqxdh.SessionId S),
    ((∃ u i, q = .initiateOPK u i bnd ∧ sid = .sendOPK u i) ∨
     (∃ u i, q = .initiateNoOPK u i bnd ∧ sid = .sendNoOPK u i)) →
    ∀ hdr, post.respOf = .hdrResp hdr →
      ∃ e' ∈ st'.sessions, e'.sid = sid ∧ e'.hdr = hdr
  genSpk_post : ∀ u j' bnd, q = .genSPK u j' → post.respOf = .bundleResp bnd →
    st'.spkBundles.any (fun (k, _) => k == (u.val, j'.val)) = true

private theorem tagStepSync1KeyReal_of_initiate {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (sid : SignalPqxdh.SessionId S)
    (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (hq : ∀ bnd' (sid' : SignalPqxdh.SessionId S),
      ((∃ u' i', q = .initiateOPK u' i' bnd' ∧ sid' = .sendOPK u' i') ∨
       (∃ u' i', q = .initiateNoOPK u' i' bnd' ∧ sid' = .sendNoOPK u' i')) → sid' = sid)
    (hqGen : ∀ u' j', q ≠ .genSPK u' j')
    (st : SignalPqxdh.KeyIndState S)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepInitiate1KeyReal S P sid u bundle st)) :
    TagStepSync1KeyReal q st y.1 y.2 := by
  have hNone : TagStepSync1KeyReal q st (.done .noneResp) st :=
    ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
     fun _ _ h => h, fun _ _ _ _ h => (by cases h),
     fun u' j' _ h _ => False.elim (hqGen u' j' h)⟩
  unfold tagStepInitiate1KeyReal at hy
  cases hAny : st.sessions.any (fun e => e.sid == sid)
  · rw [hAny] at hy; simp only [Bool.false_eq_true, ↓reduceIte] at hy
    cases hP : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hP] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hNone
    | some up =>
      rcases up with ⟨_, uEntry⟩
      rw [hP] at hy; dsimp only at hy
      cases hKosk : !SignalPqxdh.koskBundleOk P st.principals st.spkBundles
          st.opkEntries st.advKeys bundle
      · rw [hKosk] at hy
        simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind] at hy
        rcases hy with ⟨ekASk, _, kemCoins, _, hy⟩
        cases hSig : !(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)
        · rw [hSig] at hy; simp only [Bool.false_eq_true, ↓reduceIte] at hy
          cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            rw [hKem] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy
            subst hy; exact hNone
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            rw [hKem] at hy; dsimp only at hy
            simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
            refine ⟨Lazy1KeyPost.handshake_ne_evalRand _ _,
              fun e he => ⟨e, List.mem_cons_of_mem _ he, rfl, rfl, rfl⟩,
              fun _ _ h => h,
              fun bnd' sid' hInit hdr' hResp => ?_,
              fun u' j' _ h _ => False.elim (hqGen u' j' h)⟩
            have hsid := hq bnd' sid' hInit
            subst hsid
            dsimp only [Lazy1KeyPost.respOf] at hResp
            cases hF : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with
            | some _ =>
              rw [hF] at hResp; dsimp only at hResp
              injection hResp with hEq
              subst hEq
              exact ⟨_, List.mem_cons_self, rfl, rfl⟩
            | none =>
              rw [hF] at hResp; dsimp only at hResp
              cases hResp
        · rw [hSig] at hy; simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
          subst hy; exact hNone
      · rw [hKosk] at hy; simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact hNone
  · rw [hAny] at hy; simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hNone

private theorem tagStepSync1KeyReal_of_tagStepView {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (hNeTest : ∀ sid, q ≠ .testSession sid)
    (st : SignalPqxdh.KeyIndState S)
    {y : Lazy1KeyPost × SignalPqxdh.KeyIndState S}
    (hy : y ∈ support (tagStepView1KeyReal testReal S P q st)) :
    TagStepSync1KeyReal q st y.1 y.2 := by
  have hTriv : ∀ {post : Lazy1KeyPost},
      (∀ pid mkR, post ≠ .evalRand pid mkR) →
      (∀ bnd (sid : SignalPqxdh.SessionId S),
        ¬((∃ u i, q = .initiateOPK u i bnd ∧ sid = .sendOPK u i) ∨
          (∃ u i, q = .initiateNoOPK u i bnd ∧ sid = .sendNoOPK u i))) →
      (∀ u j', q ≠ .genSPK u j') →
      TagStepSync1KeyReal q st post st :=
    fun hNE hNoInit hNoGen =>
      ⟨hNE, fun e he => ⟨e, he, rfl, rfl, rfl⟩, fun _ _ h => h,
       fun bnd sid h _ _ => False.elim (hNoInit bnd sid h),
       fun u j' _ h _ => False.elim (hNoGen u j' h)⟩
  cases q with
  | testSession sid => exact False.elim (hNeTest sid rfl)
  | initiateOPK u i bundle =>
    dsimp only [tagStepView1KeyReal] at hy
    cases hNoneB : bundle.opkB?.isNone
    · rw [hNoneB] at hy; simp only [Bool.false_eq_true, ↓reduceIte] at hy
      exact tagStepSync1KeyReal_of_initiate P (.initiateOPK u i bundle) (.sendOPK u i) u bundle
        (by
          rintro bnd' sid' (⟨u', i', h1, rfl⟩ | ⟨u', i', h1, _⟩)
          · injection h1 with h2 h3; subst h2; subst h3; rfl
          · cases h1)
        (fun _ _ h => by cases h) st hy
    · rw [hNoneB] at hy; simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
        fun _ _ h => h, fun _ _ _ _ h => (by cases h), fun _ _ _ h _ => (by cases h)⟩
  | initiateNoOPK u i bundle =>
    dsimp only [tagStepView1KeyReal] at hy
    cases hSomeB : bundle.opkB?.isSome
    · rw [hSomeB] at hy; simp only [Bool.false_eq_true, ↓reduceIte] at hy
      exact tagStepSync1KeyReal_of_initiate P (.initiateNoOPK u i bundle) (.sendNoOPK u i) u bundle
        (by
          rintro bnd' sid' (⟨u', i', h1, _⟩ | ⟨u', i', h1, rfl⟩)
          · cases h1
          · injection h1 with h2 h3; subst h2; subst h3; rfl)
        (fun _ _ h => by cases h) st hy
    · rw [hSomeB] at hy; simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
        fun _ _ h => h, fun _ _ _ _ h => (by cases h), fun _ _ _ h _ => (by cases h)⟩
  | acceptOPK k j o hdr =>
    have hNI : ∀ bnd (sid : SignalPqxdh.SessionId S),
        ¬((∃ u i, (SignalPqxdh.KeyIndQuery.acceptOPK k j o hdr) = .initiateOPK u i bnd ∧
            sid = .sendOPK u i) ∨
          (∃ u i, (SignalPqxdh.KeyIndQuery.acceptOPK k j o hdr) = .initiateNoOPK u i bnd ∧
            sid = .sendNoOPK u i)) :=
      fun _ _ h => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h)
    have hNG : ∀ u j', (SignalPqxdh.KeyIndQuery.acceptOPK k j o hdr) ≠ .genSPK u j' :=
      fun _ _ h => by cases h
    dsimp only [tagStepView1KeyReal] at hy
    unfold tagStepAcceptOPK1KeyReal at hy
    split_ifs at hy
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    · rcases hK : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
      · rw [hK] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
      · rw [hK] at hy; dsimp only at hy
        rcases hB : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
        · rw [hB] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
          exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
        · rw [hB] at hy; dsimp only at hy
          rcases hO : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            _ | ⟨_, oEntry⟩
          · rw [hO] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
            exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
          · rw [hO] at hy; dsimp only at hy
            split_ifs at hy
            · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
              exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
            · rcases hAcc : SignalPqxdh.Model.acceptKeys P _ with _ | accOut
              · rw [hAcc] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
                exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
              · rw [hAcc] at hy; dsimp only at hy
                rcases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
                · rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
                  exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
                · rw [hDec] at hy; dsimp only at hy
                  simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
                  exact ⟨Lazy1KeyPost.handshake_ne_evalRand _ _,
                    fun e he => ⟨e, he, rfl, rfl, rfl⟩,
                    fun _ _ h => h, fun bnd sid h _ _ => False.elim (hNI bnd sid h),
                    fun u j' _ h _ => False.elim (hNG u j' h)⟩
  | acceptNoOPK k j l hdr =>
    have hNI : ∀ bnd (sid : SignalPqxdh.SessionId S),
        ¬((∃ u i, (SignalPqxdh.KeyIndQuery.acceptNoOPK k j l hdr) = .initiateOPK u i bnd ∧
            sid = .sendOPK u i) ∨
          (∃ u i, (SignalPqxdh.KeyIndQuery.acceptNoOPK k j l hdr) = .initiateNoOPK u i bnd ∧
            sid = .sendNoOPK u i)) :=
      fun _ _ h => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h)
    have hNG : ∀ u j', (SignalPqxdh.KeyIndQuery.acceptNoOPK k j l hdr) ≠ .genSPK u j' :=
      fun _ _ h => by cases h
    dsimp only [tagStepView1KeyReal] at hy
    unfold tagStepAcceptNoOPK1KeyReal at hy
    split_ifs at hy
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    · rcases hK : st.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩
      · rw [hK] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
      · rw [hK] at hy; dsimp only at hy
        rcases hB : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with _ | ⟨_, bEntry⟩
        · rw [hB] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
          exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
        · rw [hB] at hy; dsimp only at hy
          rcases hAcc : SignalPqxdh.Model.acceptKeys P _ with _ | accOut
          · rw [hAcc] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
            exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
          · rw [hAcc] at hy; dsimp only at hy
            rcases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with _ | ss
            · rw [hDec] at hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
              exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
            · rw [hDec] at hy; dsimp only at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
              exact ⟨Lazy1KeyPost.handshake_ne_evalRand _ _,
                fun e he => ⟨e, he, rfl, rfl, rfl⟩,
                fun _ _ h => h, fun bnd sid h _ _ => False.elim (hNI bnd sid h),
                fun u j' _ h _ => False.elim (hNG u j' h)⟩
  | revealSessionKey sid =>
    have hNI : ∀ bnd (sid' : SignalPqxdh.SessionId S),
        ¬((∃ u i, (SignalPqxdh.KeyIndQuery.revealSessionKey sid) = .initiateOPK u i bnd ∧
            sid' = .sendOPK u i) ∨
          (∃ u i, (SignalPqxdh.KeyIndQuery.revealSessionKey sid) = .initiateNoOPK u i bnd ∧
            sid' = .sendNoOPK u i)) :=
      fun _ _ h => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h)
    have hNG : ∀ u j', (SignalPqxdh.KeyIndQuery.revealSessionKey sid) ≠ .genSPK u j' :=
      fun _ _ h => by cases h
    dsimp only [tagStepView1KeyReal] at hy
    rw [pqxdhKeyIndImpl1KeyReal_revealSessionKey_run] at hy
    cases hS : st.sessions.find? (fun e => e.sid == sid) with
    | some e0 =>
      rw [hS] at hy; dsimp only at hy
      cases hTestE : e0.tested
      · rw [hTestE] at hy
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨Lazy1KeyPost.done_ne_evalRand _,
          fun e he => ⟨if e.sid == sid then { e with revealed := true } else e,
            List.mem_map_of_mem he, by split_ifs <;> exact ⟨rfl, rfl, rfl⟩⟩,
          fun _ _ h => h,
          fun bnd sid' h _ _ => False.elim (hNI bnd sid' h),
          fun u j' _ h _ => False.elim (hNG u j' h)⟩
      · rw [hTestE] at hy
        simp only [↓reduceIte, pure_bind, support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    | none =>
      rw [hS] at hy; dsimp only at hy
      cases hR : st.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        rw [hR] at hy; simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
      | some r0 =>
        rw [hR] at hy; dsimp only at hy
        cases hTestR : r0.tested
        · rw [hTestR] at hy
          simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, support_pure,
            Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
            fun _ _ h => h, fun bnd sid' h _ _ => False.elim (hNI bnd sid' h),
            fun u j' _ h _ => False.elim (hNG u j' h)⟩
        · rw [hTestR] at hy
          simp only [↓reduceIte, pure_bind, support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
  | genSPK u j =>
    have hNI : ∀ bnd (sid : SignalPqxdh.SessionId S),
        ¬((∃ u' i, (SignalPqxdh.KeyIndQuery.genSPK u j) = .initiateOPK u' i bnd ∧
            sid = .sendOPK u' i) ∨
          (∃ u' i, (SignalPqxdh.KeyIndQuery.genSPK u j) = .initiateNoOPK u' i bnd ∧
            sid = .sendNoOPK u' i)) :=
      fun _ _ h => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h)
    dsimp only [tagStepView1KeyReal, pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl] at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
        fun _ _ h => h, fun bnd sid h _ _ => False.elim (hNI bnd sid h),
        fun _ _ _ _ h => (by cases h)⟩
    · cases hP : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hP] at hy
        simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
          fun _ _ h => h, fun bnd sid h _ _ => False.elim (hNI bnd sid h),
          fun _ _ _ _ h => (by cases h)⟩
      | some up =>
        rcases up with ⟨_, uEntry⟩
        rw [hP] at hy; dsimp only at hy
        simp only [StateT.run_bind, stateT_run_liftM_1key, StateT.run_set, StateT.run_pure,
          pure_bind, bind_assoc, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hy
        rcases hy with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        refine ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
          fun u' j' h => by simp [List.any_cons, h],
          fun bnd sid h _ _ => False.elim (hNI bnd sid h),
          fun u' j' _ h _ => ?_⟩
        injection h with hu hj; subst hu; subst hj
        simp [List.any_cons]
  | revealSpkSk u j =>
    have hNI : ∀ bnd (sid : SignalPqxdh.SessionId S),
        ¬((∃ u' i, (SignalPqxdh.KeyIndQuery.revealSpkSk u j) = .initiateOPK u' i bnd ∧
            sid = .sendOPK u' i) ∨
          (∃ u' i, (SignalPqxdh.KeyIndQuery.revealSpkSk u j) = .initiateNoOPK u' i bnd ∧
            sid = .sendNoOPK u' i)) :=
      fun _ _ h => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h)
    have hNG : ∀ u' j', (SignalPqxdh.KeyIndQuery.revealSpkSk u j) ≠ .genSPK u' j' :=
      fun _ _ h => by cases h
    dsimp only [tagStepView1KeyReal, pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl] at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    cases hB : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      rw [hB] at hy
      simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact hTriv (Lazy1KeyPost.done_ne_evalRand _) hNI hNG
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      rw [hB] at hy; dsimp only at hy
      have hRun : (do
          let spkBundles' := st.spkBundles.map (fun (idx, b) =>
            if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
          set { st with spkBundles := spkBundles' }
          return SignalPqxdh.KeyIndResponse.spkSkResp bEntry.spkSk :
            StateT (SignalPqxdh.KeyIndState S) ProbComp _).run st =
          pure (.spkSkResp bEntry.spkSk,
            { st with spkBundles := st.spkBundles.map (fun (idx, b) =>
                if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) }) :=
        rfl
      rw [hRun] at hy
      simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
      refine ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, he, rfl, rfl, rfl⟩,
        fun u' j' h => ?_,
        fun bnd sid h _ _ => False.elim (hNI bnd sid h),
        fun u' j' _ h _ => False.elim (hNG u' j' h)⟩
      exact (list_any_map_cond_fst st.spkBundles (u.val, j.val)
        (fun x => { x with revealed := true })
        (fun idx => idx == (u'.val, j'.val))).trans h
  | initPrin u =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hEq := eq_fields_of_otherBase1KeyReal P _ (Or.inl ⟨u, rfl⟩) st hz
    injection hEq with hSess h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ hSpk
    exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, hSess.symm ▸ he, rfl, rfl, rfl⟩,
      fun _ _ h => hSpk.symm ▸ h,
      fun _ _ h _ _ => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h),
      fun _ _ _ h _ => (by cases h)⟩
  | corruptIK u =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hEq := eq_fields_of_otherBase1KeyReal P _ (Or.inr (Or.inl ⟨u, rfl⟩)) st hz
    injection hEq with hSess h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ hSpk
    exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, hSess.symm ▸ he, rfl, rfl, rfl⟩,
      fun _ _ h => hSpk.symm ▸ h,
      fun _ _ h _ _ => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h),
      fun _ _ _ h _ => (by cases h)⟩
  | genOPK u j o =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hEq := eq_fields_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inl ⟨u, j, o, rfl⟩))) st hz
    injection hEq with hSess h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ hSpk
    exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, hSess.symm ▸ he, rfl, rfl, rfl⟩,
      fun _ _ h => hSpk.symm ▸ h,
      fun _ _ h _ _ => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h),
      fun _ _ _ h _ => (by cases h)⟩
  | registerKey sk =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hEq := eq_fields_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨sk, rfl⟩)))) st hz
    injection hEq with hSess h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ hSpk
    exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, hSess.symm ▸ he, rfl, rfl, rfl⟩,
      fun _ _ h => hSpk.symm ▸ h,
      fun _ _ h _ _ => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h),
      fun _ _ _ h _ => (by cases h)⟩
  | roQuery sec =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hEq := eq_fields_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sec, rfl⟩))))) st hz
    injection hEq with hSess h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ hSpk
    exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, hSess.symm ▸ he, rfl, rfl, rfl⟩,
      fun _ _ h => hSpk.symm ▸ h,
      fun _ _ h _ _ => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h),
      fun _ _ _ h _ => (by cases h)⟩
  | revealDhSecrets =>
    dsimp only [tagStepView1KeyReal] at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hEq := eq_fields_of_otherBase1KeyReal P _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) st hz
    injection hEq with hSess h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ hSpk
    exact ⟨Lazy1KeyPost.done_ne_evalRand _, fun e he => ⟨e, hSess.symm ▸ he, rfl, rfl, rfl⟩,
      fun _ _ h => hSpk.symm ▸ h,
      fun _ _ h _ _ => h.elim (fun ⟨_, _, h, _⟩ => by cases h) (fun ⟨_, _, h, _⟩ => by cases h),
      fun _ _ _ h _ => (by cases h)⟩

/-- Non-test queries commute with `randCache` replacement and preserve `DrvTagSyncInv1KeyReal`. -/
theorem pqxdhKeyIndTagImpl1KeyReal_non_test_sync {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (testReal : Bool) (P : SignalPqxdh.Primitives) (q : SignalPqxdh.KeyIndQuery S)
    (hNeTest : ∀ sid, q ≠ .testSession sid)
    (ds : DrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P ds lst)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    (pqxdhKeyIndTagImpl1KeyReal false testReal S P q).run { lst with randCache := rc2 } =
      (fun (r, l1) => (r, { l1 with randCache := rc2 })) <$>
        (pqxdhKeyIndTagImpl1KeyReal false testReal S P q).run lst ∧
    ∀ r l1, (r, l1) ∈ support ((pqxdhKeyIndTagImpl1KeyReal false testReal S P q).run lst) →
      DrvTagSyncInv1KeyReal P (drvMirror ds q r) l1 ∧ l1.randCache = lst.randCache := by
  refine ⟨?_, fun r l1 hy => ?_⟩
  · dsimp only [pqxdhKeyIndTagImpl1KeyReal, StateT.run_mk]
    rw [map_bind]
    refine prob_bind_congr_of_support _ _ _ (fun ⟨post, base'⟩ hStep => ?_)
    have hTS := tagStepSync1KeyReal_of_tagStepView testReal P q hNeTest lst.base hStep
    rw [runLazy1KeyPost_false_of_not_evalRand hTS.not_evalRand
          { lst with randCache := rc2, base := base' },
        runLazy1KeyPost_false_of_not_evalRand hTS.not_evalRand { lst with base := base' }]
    simp only [map_pure]
  · have hCore' := validTag1KeyCore_of_tagImpl1KeyReal P false testReal q lst hSync.core hy
    dsimp only [pqxdhKeyIndTagImpl1KeyReal, StateT.run_mk] at hy
    rw [MonadAttach.mem_support_bind] at hy
    rcases hy with ⟨⟨post, base'⟩, hStep, hPost⟩
    dsimp only at hPost
    have hTS := tagStepSync1KeyReal_of_tagStepView testReal P q hNeTest lst.base hStep
    rw [runLazy1KeyPost_false_of_not_evalRand hTS.not_evalRand { lst with base := base' },
        support_pure, Set.mem_singleton_iff] at hPost
    rcases Prod.mk.inj hPost with ⟨rfl, rfl⟩
    dsimp only
    have hOldSess : ∀ x ∈ ds.sends, ∃ e ∈ base'.sessions, e.sid = x.1 ∧ e.hdr = x.2.2 := by
      intro x hx
      rcases hSync.sends_sess x hx with ⟨e, he, hsid, hhdr⟩
      rcases hTS.sess_mono e he with ⟨e', he', h1, h2, _⟩
      exact ⟨e', he', h1.trans hsid, h2.trans hhdr⟩
    have hOldSpk : ∀ b ∈ ds.bundles,
        base'.spkBundles.any (fun (idx, _) => idx == (b.1.1.val, b.1.2.val)) = true :=
      fun b hb => hTS.spk_mono b.1.1 b.1.2 (hSync.bundles_spk b hb)
    refine ⟨⟨hCore', ?_, ?_, ?_⟩, rfl⟩
    · dsimp only [drvMirror]
      cases q with
      | initiateOPK u i bnd =>
        cases hR : post.respOf <;> dsimp only
        case hdrResp hdr =>
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hTS.init_post bnd (.sendOPK u i) (Or.inl ⟨u, i, rfl, rfl⟩) hdr hR
          · exact hOldSess x hx
        all_goals exact hOldSess
      | initiateNoOPK u i bnd =>
        cases hR : post.respOf <;> dsimp only
        case hdrResp hdr =>
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hTS.init_post bnd (.sendNoOPK u i) (Or.inr ⟨u, i, rfl, rfl⟩) hdr hR
          · exact hOldSess x hx
        all_goals exact hOldSess
      | _ => cases post.respOf <;> exact hOldSess
    · dsimp only [drvMirror]
      cases q with
      | genSPK u j' =>
        cases hR : post.respOf <;> dsimp only
        case bundleResp bnd =>
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hTS.genSpk_post u j' bnd rfl hR
          · exact hOldSpk b hb
        all_goals exact hOldSpk
      | _ => cases post.respOf <;> exact hOldSpk
    · intro k hk
      dsimp only at hk ⊢
      rcases hSync.cache_insts k hk with ⟨d, hd, e, he, hk_eq, hek_eq⟩
      rcases hTS.sess_mono e he with ⟨e', he', _, hhdr, hrand⟩
      exact ⟨d, by cases q <;> cases post.respOf <;> exact hd, e', he',
        by rw [hrand, hk_eq], by rw [hhdr, hek_eq]⟩

theorem randCache_find?_eq_none_of_drvGuard_1KeyReal {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {ds : DrvState S ℓ} {lst : KeyInd1KeyLazyState S}
    (hSync : DrvTagSyncInv1KeyReal P ds lst) {hdr : SignalPqxdh.HandshakeHdr}
    (hinst : ∀ d ∈ ds.insts, d.hdr.ekAPk ≠ hdr.ekAPk)
    {e₀ : SignalPqxdh.KeyIndInitiatorEntry S} (he₀ : e₀ ∈ lst.base.sessions)
    (hhdr : e₀.hdr = hdr) :
    lst.randCache.find? (fun (x, _) => x == e₀.drKeyRand.rootKey) = none := by
  rw [List.find?_eq_none]
  rintro ⟨k0, v0⟩ hmem hk0
  have hk0_eq : k0 = e₀.drKeyRand.rootKey := beq_iff_eq.mp hk0
  have hk0_fst : k0 ∈ lst.randCache.map Prod.fst :=
    List.mem_map.mpr ⟨(k0, v0), hmem, rfl⟩
  rcases hSync.cache_insts k0 hk0_fst with ⟨d, hd, e₁, he₁, he₁_k, hd_ek⟩
  have hComp : SamePartnerComp P lst.base (.inl e₁) (.inl e₀) :=
    hSync.core.rand.rand_comp (.inl e₁) (.inl e₀) he₁ he₀
      (by dsimp [randRootKey]; rw [he₁_k, hk0_eq])
  have hek : e₁.hdr.ekAPk = e₀.hdr.ekAPk :=
    samePartnerComp_entryEkAPk_eq_1Key P lst.base hComp
  exact hinst d hd (by rw [hd_ek, hek, hhdr])

theorem pqxdhKeyIndTagImpl1KeyReal_testSession_of_not_fresh {S : SignalPqxdh.Setup}
    (testReal : Bool) (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (lst : KeyInd1KeyLazyState S)
    (hNotFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) = true)
    (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    (pqxdhKeyIndTagImpl1KeyReal false testReal S P (.testSession sid)).run
        { lst with randCache := rc } =
      pure (.noneResp, { lst with randCache := rc }) := by
  dsimp only [pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal, tagStepTestSession1KeyReal,
    StateT.run_mk]
  rw [hNotFresh]
  simp only [↓reduceIte, pure_bind, runLazy1KeyPost]

/-- `startDR` step decomposition for `pqxdhKeyIndTagImpl1KeyReal false false`. -/
theorem tagImpl1KeyReal_startDR_steps {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (ds : DrvState S ℓ) (lst : KeyInd1KeyLazyState S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hSync : DrvTagSyncInv1KeyReal P ds lst)
    (hsend : (sid, bnd, hdr) ∈ ds.sends)
    (hbnd : ∃ pk, ((u, j'), pk) ∈ ds.bundles)
    (hinst : ∀ d ∈ ds.insts, d.hdr.ekAPk ≠ hdr.ekAPk)
    (hFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) = false) :
    ∃ (rootKey spkSk : SignalPqxdh.Bytes) (base_t base_after : SignalPqxdh.KeyIndState S),
      spkSk.length = 32 ∧
      (∀ (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)),
        lst.randCache.map Prod.fst = rc.map Prod.fst →
        (pqxdhKeyIndTagImpl1KeyReal false false S P (.testSession sid)).run
            { lst with randCache := rc } =
          (SignalPqxdh.sampleDRKey96 >>= fun dk =>
            pure (.drKeyResp dk,
              { base := base_t, randCache := (rootKey, dk) :: rc }))) ∧
      (∀ (rc' : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)),
        (pqxdhKeyIndTagImpl1KeyReal false false S P (.revealSpkSk u j')).run
            { base := base_t, randCache := rc' } =
          pure (.spkSkResp spkSk, { base := base_after, randCache := rc' })) ∧
      (∀ dk ∈ support SignalPqxdh.sampleDRKey96,
        ∀ (ds' : DrvState S ℓ) (d_new : DrvInst S ℓ),
          ds'.sends = ds.sends →
          ds'.bundles = ds.bundles →
          ds'.insts = ds.insts ++ [d_new] →
          d_new.hdr = hdr →
          DrvTagSyncInv1KeyReal P ds'
            { base := base_after, randCache := (rootKey, dk) :: lst.randCache }) := by
  rcases hbnd with ⟨pk, hbnd⟩
  rcases hSync.sends_sess (sid, bnd, hdr) hsend with ⟨e_s, he_s, he_s_sid, he_s_hdr⟩
  cases hFindS : lst.base.sessions.find? (fun e => e.sid == sid) with
  | none =>
    exact False.elim (List.find?_eq_none.mp hFindS e_s he_s (beq_iff_eq.mpr he_s_sid))
  | some e₀ =>
    have he₀ : e₀ ∈ lst.base.sessions := List.mem_of_find?_eq_some hFindS
    have he₀_sid := List.find?_some hFindS
    simp only [beq_iff_eq] at he₀_sid
    have he₀_eq : e₀ = e_s :=
      eq_of_mem_of_nodup_map (·.sid) hSync.core.rand.sid_nodup he₀ he_s
        (he₀_sid.trans he_s_sid.symm)
    have he₀_hdr : e₀.hdr = hdr := he₀_eq ▸ he_s_hdr
    rcases List.any_eq_true.mp (hSync.bundles_spk ((u, j'), pk) hbnd) with ⟨b0, hb0, hb0_eq⟩
    cases hFindB : lst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j'.val)) with
    | none =>
      exact False.elim (List.find?_eq_none.mp hFindB b0 hb0 hb0_eq)
    | some bPair =>
      rcases bPair with ⟨idx_b, bEntry⟩
      have hbEntry_mem : (idx_b, bEntry) ∈ lst.base.spkBundles :=
        List.mem_of_find?_eq_some hFindB
      have hSpkLen : bEntry.spkSk.length = 32 := hSync.core.spkSk_len (idx_b, bEntry) hbEntry_mem
      let sessions' := lst.base.sessions.map (fun s =>
        if s.sid == sid then { s with tested := true } else s)
      let spkBundles' := lst.base.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j'.val) then (idx, { b with revealed := true }) else (idx, b))
      let base_t : SignalPqxdh.KeyIndState S := { lst.base with sessions := sessions' }
      let base_after : SignalPqxdh.KeyIndState S :=
        { lst.base with sessions := sessions', spkBundles := spkBundles' }
      have hTestRun : ∀ (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)),
          lst.randCache.map Prod.fst = rc.map Prod.fst →
          (pqxdhKeyIndTagImpl1KeyReal false false S P (.testSession sid)).run
              { lst with randCache := rc } =
            (SignalPqxdh.sampleDRKey96 >>= fun dk =>
              pure (.drKeyResp dk,
                { base := base_t, randCache := (e₀.drKeyRand.rootKey, dk) :: rc })) := by
        intro rc hrc
        have hRC := randCache_find?_eq_none_of_drvGuard_1KeyReal
          (hSync.of_randCache_map_fst hrc) hinst he₀ he₀_hdr
        dsimp only [pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal, tagStepTestSession1KeyReal,
          StateT.run_mk]
        rw [hFresh]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hFindS]
        simp only [pure_bind, runLazy1KeyPost, CacheLens.eval, randLens1Key, evalCache, bind_assoc]
        rw [hRC]
        rfl
      have hRevRun : ∀ (rc' : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)),
          (pqxdhKeyIndTagImpl1KeyReal false false S P (.revealSpkSk u j')).run
              { base := base_t, randCache := rc' } =
            pure (.spkSkResp bEntry.spkSk, { base := base_after, randCache := rc' }) := by
        intro rc'
        have hFindB' : base_t.spkBundles.find?
            (fun (idx, _) => idx == (u.val, j'.val)) = some (idx_b, bEntry) := hFindB
        dsimp only [pqxdhKeyIndTagImpl1KeyReal, tagStepView1KeyReal, pqxdhKeyIndImpl1KeyReal,
          SignalPqxdh.pqxdhKeyIndImpl, StateT.run_mk]
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        rw [hFindB']
        rfl
      refine ⟨e₀.drKeyRand.rootKey, bEntry.spkSk, base_t, base_after,
        hSpkLen, hTestRun, hRevRun, ?_⟩
      intro dk hdk ds' d_new hSendsEq hBndsEq hInstsEq hdHdr
      have hMem1 : (SignalPqxdh.KeyIndResponse.drKeyResp dk,
          { base := base_t, randCache := (e₀.drKeyRand.rootKey, dk) :: lst.randCache }) ∈
          support ((pqxdhKeyIndTagImpl1KeyReal false false S P (.testSession sid)).run lst) := by
        have hRun0 := hTestRun lst.randCache rfl
        have hEqLst : { lst with randCache := lst.randCache } = lst := rfl
        rw [hEqLst] at hRun0
        rw [hRun0, support_bind]
        exact Set.mem_iUnion₂.mpr ⟨dk, hdk, by simp⟩
      have hCore1 := validTag1KeyCore_of_tagImpl1KeyReal P false false
        (.testSession sid) lst hSync.core hMem1
      have hMem2 : (SignalPqxdh.KeyIndResponse.spkSkResp bEntry.spkSk,
          { base := base_after, randCache := (e₀.drKeyRand.rootKey, dk) :: lst.randCache }) ∈
          support ((pqxdhKeyIndTagImpl1KeyReal false false S P (.revealSpkSk u j')).run
            { base := base_t, randCache := (e₀.drKeyRand.rootKey, dk) :: lst.randCache }) := by
        rw [hRevRun, support_pure, Set.mem_singleton_iff]
      have hCore2 := validTag1KeyCore_of_tagImpl1KeyReal P false false
        (.revealSpkSk u j')
        { base := base_t, randCache := (e₀.drKeyRand.rootKey, dk) :: lst.randCache }
        hCore1 hMem2
      refine ⟨hCore2, ?_, ?_, ?_⟩
      · intro x hx
        rw [hSendsEq] at hx
        rcases hSync.sends_sess x hx with ⟨e, he, hsid, hhdr⟩
        refine ⟨if e.sid == sid then { e with tested := true } else e,
          List.mem_map_of_mem he, ?_⟩
        split_ifs <;> exact ⟨hsid, hhdr⟩
      · intro b hb
        rw [hBndsEq] at hb
        change spkBundles'.any (fun (idx, _) => idx == (b.1.1.val, b.1.2.val)) = true
        exact (list_any_map_cond_fst lst.base.spkBundles (u.val, j'.val)
          (fun x => { x with revealed := true })
          (fun idx => idx == (b.1.1.val, b.1.2.val))).trans (hSync.bundles_spk b hb)
      · intro k hk
        simp only [List.map_cons, List.mem_cons] at hk
        rw [hInstsEq]
        change ∃ d ∈ ds.insts ++ [d_new],
          ∃ e ∈ sessions', e.drKeyRand.rootKey = k ∧ d.hdr.ekAPk = e.hdr.ekAPk
        rcases hk with rfl | hk
        · refine ⟨d_new, List.mem_append_right _ (List.mem_singleton.mpr rfl),
            if e₀.sid == sid then { e₀ with tested := true } else e₀,
            List.mem_map_of_mem he₀, ?_⟩
          split_ifs <;> exact ⟨rfl, by rw [hdHdr, he₀_hdr]⟩
        · rcases hSync.cache_insts k hk with ⟨d0, hd0, e1, he1, hk_eq, hek_eq⟩
          refine ⟨d0, List.mem_append_left _ hd0,
            if e1.sid == sid then { e1 with tested := true } else e1,
            List.mem_map_of_mem he1, ?_⟩
          split_ifs <;> exact ⟨hk_eq, hek_eq⟩

/-! ## Bridge to `SignalPqxdh.pqxdhKeyIndImpl1KeyReal` -/

/-- Under `P.sigPkGen = P.x25519Base`, `SignalPqxdh.pqxdhKeyIndImpl1KeyReal` equals `pqxdhKeyIndImpl1KeyReal`. -/
theorem signalPqxdh_pqxdhKeyIndImpl1KeyReal_eq (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (hSig : P.sigPkGen = P.x25519Base) :
    SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P =
      CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P := by
  funext q
  cases q with
  | initPrin u =>
    dsimp only [SignalPqxdh.pqxdhKeyIndImpl1KeyReal, pqxdhKeyIndImpl1KeyReal,
      runKeyIndInitPrin1Key]
    rw [hSig]
  | _ => rfl

end CryptoVerification.E2E
