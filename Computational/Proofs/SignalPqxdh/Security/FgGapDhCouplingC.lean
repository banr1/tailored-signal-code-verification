/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingB
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Hop 4 (`G3 → G3.5`): Lazy Tagged Implementation

Defines the lazily tagged `KeyInd` implementation `pqxdhKeyIndAdvTagImpl`, proves distributional
equivalence between pre-warmed and lazy caches, and establishes per-query `RelEagerTag` couplings.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security

/-- Build a `KeyInd` `QueryImpl` on `KeyIndLazyState S` from a view-level step function. -/
def mkLazyKeyIndImpl (eagerRoHonest eagerRand : Bool) (S : Setup)
    (stepView : KeyIndQuery S → KeyIndAdvCutoffState S → ProbComp (LazyPost × KeyIndAdvCutoffState
      S)) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndLazyState S) ProbComp) := fun q =>
  StateT.mk fun lst => do
    let (post, lst1) ← liftTagView (stepView q) lst
    runLazyPost eagerRoHonest eagerRand S post lst1

theorem isInvariant_randLens_mkLazyKeyIndImpl_false {S : Setup}
    (eagerRoHonest : Bool)
    (stepView : KeyIndQuery S → KeyIndAdvCutoffState S → ProbComp (LazyPost × KeyIndAdvCutoffState
      S))
    (q : KeyIndQuery S)
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hf : (randLens S).IsInvariant f) :
    (randLens S).IsInvariant (fun (p : Unit × KeyIndLazyState S) =>
      (mkLazyKeyIndImpl eagerRoHonest false S stepView q).run p.2 >>= f) := by
  simpa [mkLazyKeyIndImpl, StateT.run_mk, bind_assoc] using
    isInvariant_randLens_liftTagView (fun (_ : Unit) => stepView q)
      (fun post (p : Unit × KeyIndLazyState S) => runLazyPost eagerRoHonest false S post p.2 >>= f)
      (fun post => isInvariant_randLens_runLazyPost_false eagerRoHonest post hf)

theorem isInvariant_roLens_mkLazyKeyIndImpl_false_false {S : Setup}
    (stepView : KeyIndQuery S → KeyIndAdvCutoffState S → ProbComp (LazyPost × KeyIndAdvCutoffState
      S))
    (q : KeyIndQuery S)
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hf : (roLens S).IsInvariant f) :
    (roLens S).IsInvariant (fun (p : Unit × KeyIndLazyState S) =>
      (mkLazyKeyIndImpl false false S stepView q).run p.2 >>= f) := by
  simpa [mkLazyKeyIndImpl, StateT.run_mk, bind_assoc] using
    isInvariant_roLens_liftTagView (fun (_ : Unit) => stepView q)
      (fun post (p : Unit × KeyIndLazyState S) => runLazyPost false false S post p.2 >>= f)
      (fun post => isInvariant_roLens_runLazyPost_false_false post hf)

theorem evalDist_mkLazyKeyIndImpl_eagerRand_eq {S : Setup}
    (eagerRoHonest : Bool)
    (stepView : KeyIndQuery S → KeyIndAdvCutoffState S → ProbComp (LazyPost × KeyIndAdvCutoffState
      S))
    (q : KeyIndQuery S) (lst : KeyIndLazyState S)
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hf : (randLens S).IsInvariant f) :
    𝒟[(mkLazyKeyIndImpl eagerRoHonest true S stepView q).run lst >>= f] =
      𝒟[(mkLazyKeyIndImpl eagerRoHonest false S stepView q).run lst >>= f] := by
  simp only [mkLazyKeyIndImpl, StateT.run_mk, bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨post, lst1⟩ _ => ?_
  exact evalDist_runLazyPost_eagerRand_eq eagerRoHonest post lst1 hf

theorem evalDist_mkLazyKeyIndImpl_eagerRoHonest_eq {S : Setup}
    (stepView : KeyIndQuery S → KeyIndAdvCutoffState S → ProbComp (LazyPost × KeyIndAdvCutoffState
      S))
    (q : KeyIndQuery S) (lst : KeyIndLazyState S)
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hf : (roLens S).IsInvariant f) :
    𝒟[(mkLazyKeyIndImpl true false S stepView q).run lst >>= f] =
      𝒟[(mkLazyKeyIndImpl false false S stepView q).run lst >>= f] := by
  simp only [mkLazyKeyIndImpl, StateT.run_mk, bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨post, lst1⟩ _ => ?_
  exact evalDist_runLazyPost_eagerRoHonest_eq post lst1 hf

/-- Pre-warmed (`true, true`) and lazy (`false, false`) `mkLazyKeyIndImpl` runs agree on any
    cache-invariant observation. -/
theorem evalDist_simulateQ_mkLazyKeyIndImpl_true_true_eq_false_false {S : Setup} {α : Type}
    (stepView : KeyIndQuery S → KeyIndAdvCutoffState S → ProbComp (LazyPost × KeyIndAdvCutoffState
      S))
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    {obs : α × KeyIndLazyState S → ProbComp Bool}
    (hObsRand : (randLens S).IsInvariant obs)
    (hObsRo : (roLens S).IsInvariant obs)
    (lst : KeyIndLazyState S) :
    let full11 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + mkLazyKeyIndImpl true true S stepView
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + mkLazyKeyIndImpl false false S stepView
    𝒟[(_root_.simulateQ full11 oa).run lst >>= obs] =
      𝒟[(_root_.simulateQ full00 oa).run lst >>= obs] := by
  intro full11 full00
  let full10 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + mkLazyKeyIndImpl true false S stepView
  have h1 : 𝒟[(_root_.simulateQ full11 oa).run lst >>= obs] =
      𝒟[(_root_.simulateQ full10 oa).run lst >>= obs] :=
    CacheLens.evalDist_simulateQ_eq_of_isInvariant (randLens S)
      (mkLazyKeyIndImpl true true S stepView)
      (mkLazyKeyIndImpl true false S stepView)
      (isInvariant_randLens_mkLazyKeyIndImpl_false true stepView)
      (evalDist_mkLazyKeyIndImpl_eagerRand_eq true stepView)
      oa hObsRand lst lst (CacheLens.Equiv.refl (randLens S) lst)
  have h2 : 𝒟[(_root_.simulateQ full10 oa).run lst >>= obs] =
      𝒟[(_root_.simulateQ full00 oa).run lst >>= obs] :=
    CacheLens.evalDist_simulateQ_eq_of_isInvariant (roLens S)
      (mkLazyKeyIndImpl true false S stepView)
      (mkLazyKeyIndImpl false false S stepView)
      (isInvariant_roLens_mkLazyKeyIndImpl_false_false stepView)
      (evalDist_mkLazyKeyIndImpl_eagerRoHonest_eq stepView)
      oa hObsRo lst lst (CacheLens.Equiv.refl (roLens S) lst)
  exact h1.trans h2

def tagStepInitiate (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) := do
  let hst := adv.shCr
  let st := hst.base
  let some uEntry := preCheckKeyInd S P sid u bundle st
    | return (.done .noneResp, adv)
  let ekASk ← sampleScalar32
  let kemCoins ← sampleCoins32
  if !checkBundleSigs P st.principals bundle then
    return (.done .noneResp, adv)
  match P.kemEncaps bundle.pqspkB kemCoins with
  | none =>
    return (.done .noneResp, { adv with shCr := { hst with sendCount := hst.sendCount + 1 } })
  | some (ss, kemCt) =>
    let ekAPk := P.x25519Base ekASk
    let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
    let dh2 := P.x25519 ekASk bundle.ikB
    let dh3 := P.x25519 ekASk bundle.spkB
    let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
    let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
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
    let s0 : KeyIndInitiatorEntry S := {
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
      drKeyReal   := tagDRKey secrets
      drKeyRand   := default
      hdr         := hdr
      tested      := false
    }
    let (randTag, pid?) := match st.respSessions.find? (fun r => keyIndPartner P s0 r) with
      | some r => (r.drKeyRand, none)
      | none   => (tagDRKey (freshPidBytes st), some (freshPidBytes st))
    let base' : KeyIndState S :=
      { st with sessions := { s0 with drKeyRand := randTag } :: st.sessions }
    let (_, shCr') := applyShCrFinish sid bundle.pqspkB ss kemCt hst (KeyIndResponse.noneResp, some
      base')
    let isHonest := (findHonestPrincipal P st.principals bundle.ikB).isSome
    return (.handshake isHonest (.hdrResp hdr) (fun dk => .initUnfreshResp dk hdr) secrets pid?,
            { adv with shCr := shCr' })

def tagStepAcceptOPK (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) := do
  let hst := adv.shCr
  let st := hst.base
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.done .noneResp, adv)
  if st.usedRecvOPK.contains (k.val, j.val, o.val) then return (.done .noneResp, adv)
  if !koskSenderOk P st.principals st.advKeys hdr.ikAPk then return (.done .noneResp, adv)
  let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
    | return (.done .noneResp, adv)
  let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.done .noneResp, adv)
  let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.done .noneResp, adv)
  if oEntry.consumed then return (.done .noneResp, adv)
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
  let some _ := Model.acceptKeys P accInp | return (.done .noneResp, adv)
  let some ss := P.kemDecaps bEntry.pqspkSk hdr.kemCt | return (.done .noneResp, adv)
  let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
  let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
  let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
  let dh4 := P.x25519 oEntry.opkSk hdr.ekAPk
  let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
  let opkEntries' := st.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  let senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome
  let r0 : KeyIndRespEntry S := {
    sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
    opkPk? := some oEntry.opkPk, pqspkPk := bEntry.pqspkPk, hdr := hdr,
    senderHonest := senderHonest, drKeyReal := tagDRKey secrets, drKeyRand := default }
  let (randTag, pid?) := match st.sessions.find? (fun s => keyIndPartner P s r0) with
    | some s => (s.drKeyRand, none)
    | none   => (tagDRKey (freshPidBytes st), some (freshPidBytes st))
  let base' : KeyIndState S := { st with
    opkEntries       := opkEntries'
    usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { r0 with drKeyRand := randTag } :: st.respSessions }
  let recEntry : RecvKemRecord := {
    bIdx    := spkBundleFlatIdx S k j
    k       := k.val
    j       := j.val
    pqspkPk := bEntry.pqspkPk
    pqspkSk := bEntry.pqspkSk
    kemCt   := hdr.kemCt
    kemSs   := ss
  }
  let shCr' : KeyIndShCrState S := { hst with
    base        := base'
    recvKemRecs := recEntry :: hst.recvKemRecs }
  return (.handshake senderHonest .acceptFreshResp KeyIndResponse.drKeyResp secrets pid?,
          { adv with shCr := shCr' })

def tagStepAcceptNoOPK (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) := do
  let hst := adv.shCr
  let st := hst.base
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.done .noneResp, adv)
  if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return (.done .noneResp, adv)
  if !koskSenderOk P st.principals st.advKeys hdr.ikAPk then return (.done .noneResp, adv)
  let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
    | return (.done .noneResp, adv)
  let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.done .noneResp, adv)
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
  let some _ := Model.acceptKeys P accInp | return (.done .noneResp, adv)
  let some ss := P.kemDecaps bEntry.pqspkSk hdr.kemCt | return (.done .noneResp, adv)
  let dh1 := P.x25519 bEntry.spkSk hdr.ikAPk
  let dh2 := P.x25519 kEntry.secIKA0 hdr.ekAPk
  let dh3 := P.x25519 bEntry.spkSk hdr.ekAPk
  let secrets := buildSecrets dh1 dh2 dh3 none ss
  let senderHonest := (findHonestPrincipal P st.principals hdr.ikAPk).isSome
  let r0 : KeyIndRespEntry S := {
    sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := bEntry.spkPk,
    opkPk? := none, pqspkPk := bEntry.pqspkPk, hdr := hdr,
    senderHonest := senderHonest, drKeyReal := tagDRKey secrets, drKeyRand := default }
  let (randTag, pid?) := match st.sessions.find? (fun s => keyIndPartner P s r0) with
    | some s => (s.drKeyRand, none)
    | none   => (tagDRKey (freshPidBytes st), some (freshPidBytes st))
  let base' : KeyIndState S := { st with
    usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { r0 with drKeyRand := randTag } :: st.respSessions }
  let recEntry : RecvKemRecord := {
    bIdx    := spkBundleFlatIdx S k j
    k       := k.val
    j       := j.val
    pqspkPk := bEntry.pqspkPk
    pqspkSk := bEntry.pqspkSk
    kemCt   := hdr.kemCt
    kemSs   := ss
  }
  let shCr' : KeyIndShCrState S := { hst with
    base        := base'
    recvKemRecs := recEntry :: hst.recvKemRecs }
  return (.handshake senderHonest .acceptFreshResp KeyIndResponse.drKeyResp secrets pid?,
          { adv with shCr := shCr' })

def tagStepRevealSessionKey (S : Setup) (sid : SessionId S)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) :=
  let st := adv.shCr.base
  match st.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    if e.tested then pure (.done .noneResp, adv)
    else
      let sessions' := st.sessions.map (fun s =>
        if s.sid == sid then { s with revealed := true } else s)
      let adv' := { adv with shCr := { adv.shCr with base := { st with sessions := sessions' } } }
      pure (.evalRo e.drKeyReal.rootKey KeyIndResponse.drKeyResp, adv')
  | none =>
    match st.respSessions.find? (fun r => r.sid == sid) with
    | none => pure (.done .noneResp, adv)
    | some r =>
      if r.tested then pure (.done .noneResp, adv)
      else
        let resp' := st.respSessions.map (fun x =>
          if x.sid == sid then { x with revealed := true } else x)
        let adv' := { adv with shCr := { adv.shCr with base := { st with respSessions := resp' } } }
        pure (.evalRo r.drKeyReal.rootKey KeyIndResponse.drKeyResp, adv')

def tagStepTestSession (testReal : Bool) (S : Setup) (sid : SessionId S)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) :=
  let st := adv.shCr.base
  if !isKeyIndSessionTestable st sid then
    pure (.done .noneResp, adv)
  else
    match st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      let sessions' := st.sessions.map (fun s =>
        if s.sid == sid then { s with tested := true } else s)
      let adv' := { adv with shCr := { adv.shCr with base := { st with sessions := sessions' } } }
      if testReal then
        pure (.evalRo e.drKeyReal.rootKey KeyIndResponse.drKeyResp, adv')
      else
        pure (.evalRand e.drKeyRand.rootKey KeyIndResponse.drKeyResp, adv')
    | none =>
      match st.respSessions.find? (fun r => r.sid == sid) with
      | none => pure (.done .noneResp, adv)
      | some r =>
        let resp' := st.respSessions.map (fun x =>
          if x.sid == sid then { x with tested := true } else x)
        let adv' := { adv with shCr := { adv.shCr with base := { st with respSessions := resp' } } }
        if testReal then
          pure (.evalRo r.drKeyReal.rootKey KeyIndResponse.drKeyResp, adv')
        else
          pure (.evalRand r.drKeyRand.rootKey KeyIndResponse.drKeyResp, adv')

def tagStepView (testReal : Bool) (S : Setup) (P : Primitives) (q : KeyIndQuery S)
    (adv : KeyIndAdvCutoffState S) : ProbComp (LazyPost × KeyIndAdvCutoffState S) :=
  match q with
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then pure (.done .noneResp, adv)
    else tagStepInitiate S P (.sendOPK u i) u bundle adv
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then pure (.done .noneResp, adv)
    else tagStepInitiate S P (.sendNoOPK u i) u bundle adv
  | .acceptOPK k j o hdr => tagStepAcceptOPK S P k j o hdr adv
  | .acceptNoOPK k j l hdr => tagStepAcceptNoOPK S P k j l hdr adv
  | .revealSessionKey sid => tagStepRevealSessionKey S sid adv
  | .testSession sid => tagStepTestSession testReal S sid adv
  | .roQuery sec =>
    pure (.evalRo sec KeyIndResponse.drKeyResp, { adv with advRoLog := sec :: adv.advRoLog })
  | q_simple => do
    let (r, adv') ← (pqxdhKeyIndAdvG3Impl S P q_simple).run adv
    return (.done r, adv')

/-- Tagged `KeyInd` oracle implementation on `KeyIndLazyState S` parameterized by cache eagerness
    (`eagerRoHonest`, `eagerRand`) and test mode (`testReal`). -/
def pqxdhKeyIndAdvTagImpl (eagerRoHonest eagerRand testReal : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndLazyState S) ProbComp) :=
  mkLazyKeyIndImpl eagerRoHonest eagerRand S (tagStepView testReal S P)

theorem evalDist_simulateQ_pqxdhKeyIndAdvTagImpl_true_true_eq_false_false {S : Setup} {α : Type}
    (testReal : Bool) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    {obs : α × KeyIndLazyState S → ProbComp Bool}
    (hObsRand : (randLens S).IsInvariant obs)
    (hObsRo : (roLens S).IsInvariant obs)
    (lst : KeyIndLazyState S) :
    let full11 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl true true testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false testReal S P
    𝒟[(_root_.simulateQ full11 oa).run lst >>= obs] =
      𝒟[(_root_.simulateQ full00 oa).run lst >>= obs] :=
  evalDist_simulateQ_mkLazyKeyIndImpl_true_true_eq_false_false (tagStepView testReal S P)
    oa hObsRand hObsRo lst

theorem isInvariant_randLens_finalizeKeyIndG3 (S : Setup) (P : Primitives) (secb : Bool) :
    (randLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      finalizeKeyIndG3 S P secb p.1 p.2.adv.shCr) :=
  CacheLens.IsInvariant.of_cache_indep (randLens S) _ (fun _ _ _ => rfl)

theorem isInvariant_roLens_finalizeKeyIndG3 (S : Setup) (P : Primitives) (secb : Bool) :
    (roLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      finalizeKeyIndG3 S P secb p.1 p.2.adv.shCr) :=
  CacheLens.IsInvariant.of_cache_indep (roLens S) _ (fun a lst c => by
    dsimp only [roLens, withAdvRoCache]
    exact finalizeKeyIndG3_withShCrRoCache S P secb a c lst.adv.shCr)

theorem isInvariant_randLens_badKeyIndFgAny (S : Setup) (P : Primitives) (maxLen : ℕ) :
    (randLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      pure (badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog)) :=
  CacheLens.IsInvariant.of_cache_indep (randLens S) _ (fun _ _ _ => rfl)

theorem isInvariant_roLens_badKeyIndFgAny (S : Setup) (P : Primitives) (maxLen : ℕ) :
    (roLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      pure (badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog)) :=
  CacheLens.IsInvariant.of_cache_indep (roLens S) _ (fun _ lst c => by
    dsimp only [roLens, withAdvRoCache, withShCrRoCache]
    rw [badKeyIndFgAny_withBaseRoCache])

theorem evalCache_eq_sample_of_find_none {K : Type} [BEq K]
    (c : List (K × DRKey)) (k : K)
    (hFind : c.find? (fun (x, _) => x == k) = none) :
    evalCache c k = (sampleDRKey96 >>= fun dk => pure (dk, (k, dk) :: c)) := by
  simp [evalCache, hFind]

theorem evalCache_find_some_self {K : Type} [BEq K] [LawfulBEq K]
    (c : List (K × DRKey)) (k : K)
    (q : DRKey × List (K × DRKey))
    (hq : q ∈ support (evalCache c k)) :
    ∃ x, q.2.find? (fun (y, _) => y == k) = some (x, q.1) := by
  unfold evalCache at hq
  cases hFind : c.find? (fun (x, _) => x == k) with
  | some p =>
    rcases p with ⟨x, dk⟩
    simp only [hFind, support_pure, Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨x, hFind⟩
  | none =>
    simp only [hFind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hq
    rcases hq with ⟨dk, _, rfl⟩
    exact ⟨k, by simp⟩

theorem evalCache_preserves_find_some {K : Type} [BEq K] [LawfulBEq K]
    (c : List (K × DRKey)) (k k' : K) (p : K × DRKey)
    (hFind : c.find? (fun (x, _) => x == k) = some p)
    (q : DRKey × List (K × DRKey))
    (hq : q ∈ support (evalCache c k')) :
    q.2.find? (fun (x, _) => x == k) = some p := by
  unfold evalCache at hq
  cases hFind' : c.find? (fun (x, _) => x == k') with
  | some p' =>
    rcases p' with ⟨x', dk'⟩
    simp only [hFind', support_pure, Set.mem_singleton_iff] at hq
    subst hq
    exact hFind
  | none =>
    simp only [hFind', MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hq
    rcases hq with ⟨dk', _, rfl⟩
    have hne : (k' == k) = false := by
      cases hkk : (k' == k)
      · rfl
      · have heq : k' = k := eq_of_beq hkk
        subst heq
        rw [hFind] at hFind'
        cases hFind'
    simp [List.find?, hne, hFind]

def lookupCacheKey (c : List (Bytes × DRKey)) (k : Bytes) : DRKey :=
  match c.find? (fun (x, _) => x == k) with
  | some (_, dk) => dk
  | none => default

theorem lookupCacheKey_eq_of_find_some (c : List (Bytes × DRKey)) (k : Bytes) (p : Bytes × DRKey)
    (hFind : c.find? (fun (x, _) => x == k) = some p) :
    lookupCacheKey c k = p.2 := by
  rcases p with ⟨x, dk⟩
  simp [lookupCacheKey, hFind]

theorem evalCache_eq_pure_lookupCacheKey_of_isSome (c : List (Bytes × DRKey)) (k : Bytes)
    (hSome : (c.find? (fun (x, _) => x == k)).isSome = true) :
    evalCache c k = pure (lookupCacheKey c k, c) := by
  cases hFind : c.find? (fun (x, _) => x == k) with
  | none => simp [hFind] at hSome
  | some p =>
    rcases p with ⟨x, dk⟩
    simp [evalCache, lookupCacheKey, hFind]

theorem lookupCacheKey_evalCache_self (c : List (Bytes × DRKey)) (k : Bytes)
    (q : DRKey × List (Bytes × DRKey)) (hq : q ∈ support (evalCache c k)) :
    lookupCacheKey q.2 k = q.1 ∧ (q.2.find? (fun (x, _) => x == k)).isSome = true := by
  rcases evalCache_find_some_self c k q hq with ⟨x, hFind⟩
  exact ⟨lookupCacheKey_eq_of_find_some q.2 k (x, q.1) hFind, by simp [hFind]⟩

theorem lookupCacheKey_evalCache_preserves (c : List (Bytes × DRKey)) (k k' : Bytes)
    (hSome : (c.find? (fun (x, _) => x == k)).isSome = true)
    (q : DRKey × List (Bytes × DRKey)) (hq : q ∈ support (evalCache c k')) :
    lookupCacheKey q.2 k = lookupCacheKey c k ∧
    (q.2.find? (fun (x, _) => x == k)).isSome = true := by
  cases hFind : c.find? (fun (x, _) => x == k) with
  | none => simp [hFind] at hSome
  | some p =>
    have hFind' := evalCache_preserves_find_some c k k' p hFind q hq
    exact ⟨by rw [lookupCacheKey_eq_of_find_some q.2 k p hFind',
                  lookupCacheKey_eq_of_find_some c k p hFind],
           by simp [hFind']⟩

theorem find_none_of_length_lt (c : List (Bytes × DRKey)) (k : Bytes) (n : ℕ)
    (hLen : ∀ p ∈ c, p.1.length < n) (hk : k.length = n) :
    c.find? (fun (x, _) => x == k) = none := by
  rw [List.find?_eq_none]
  rintro ⟨x, dk⟩ hMem hEq
  dsimp only at hEq
  have hx : x = k := eq_of_beq hEq
  subst hx
  have hlt := hLen (x, dk) hMem
  dsimp only at hlt
  omega

theorem lookupCacheKey_cons_of_find_none_of_isSome
    (c : List (Bytes × DRKey)) (k pid : Bytes) (dk : DRKey)
    (hSome : (c.find? (fun (x, _) => x == k)).isSome = true)
    (hNone : c.find? (fun (x, _) => x == pid) = none) :
    lookupCacheKey ((pid, dk) :: c) k = lookupCacheKey c k ∧
    ((((pid, dk) :: c).find? (fun (x, _) => x == k)).isSome = true) := by
  have hne : (pid == k) = false := by
    cases hpk : (pid == k)
    · rfl
    · have heq : pid = k := eq_of_beq hpk
      subst heq
      simp [hNone] at hSome
  simp [lookupCacheKey, List.find?, hne, hSome]

def resolveSessionEntry {S : Setup} (roCache randCache : List (Bytes × DRKey))
    (s : KeyIndInitiatorEntry S) : KeyIndInitiatorEntry S :=
  { s with
    drKeyReal := lookupCacheKey roCache s.drKeyReal.rootKey
    drKeyRand := lookupCacheKey randCache s.drKeyRand.rootKey }

def resolveRespEntry {S : Setup} (roCache randCache : List (Bytes × DRKey))
    (r : KeyIndRespEntry S) : KeyIndRespEntry S :=
  { r with
    drKeyReal := lookupCacheKey roCache r.drKeyReal.rootKey
    drKeyRand := lookupCacheKey randCache r.drKeyRand.rootKey }

def resolveLazyBase {S : Setup} (randCache : List (Bytes × DRKey))
    (st : KeyIndState S) : KeyIndState S :=
  { st with
    sessions := st.sessions.map (resolveSessionEntry st.roCache randCache)
    respSessions := st.respSessions.map (resolveRespEntry st.roCache randCache) }

def resolveLazyShCr {S : Setup} (randCache : List (Bytes × DRKey))
    (hst : KeyIndShCrState S) : KeyIndShCrState S :=
  { hst with base := resolveLazyBase randCache hst.base }

def resolveLazyAdv {S : Setup} (lst : KeyIndLazyState S) : KeyIndAdvCutoffState S :=
  { lst.adv with shCr := resolveLazyShCr lst.randCache lst.adv.shCr }

structure WellFormedLazy {S : Setup} (lst : KeyIndLazyState S) : Prop where
  sess_ro : ∀ s ∈ lst.adv.shCr.base.sessions,
    (lst.adv.shCr.base.roCache.find? (fun (x, _) => x == s.drKeyReal.rootKey)).isSome = true
  sess_rand : ∀ s ∈ lst.adv.shCr.base.sessions,
    (lst.randCache.find? (fun (x, _) => x == s.drKeyRand.rootKey)).isSome = true
  resp_ro : ∀ r ∈ lst.adv.shCr.base.respSessions,
    (lst.adv.shCr.base.roCache.find? (fun (x, _) => x == r.drKeyReal.rootKey)).isSome = true
  resp_rand : ∀ r ∈ lst.adv.shCr.base.respSessions,
    (lst.randCache.find? (fun (x, _) => x == r.drKeyRand.rootKey)).isSome = true
  rand_len : ∀ p ∈ lst.randCache,
    p.1.length < lst.adv.shCr.base.sessions.length + lst.adv.shCr.base.respSessions.length

theorem wellFormedLazy_empty (S : Setup) : WellFormedLazy (KeyIndLazyState.empty S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [KeyIndLazyState.empty, KeyIndState.empty]

@[simp]
theorem eraseSessionKeys_resolveSessionEntry {S : Setup} (roCache randCache : List (Bytes × DRKey))
    (s : KeyIndInitiatorEntry S) :
    eraseSessionKeys (resolveSessionEntry roCache randCache s) = eraseSessionKeys s := rfl

@[simp]
theorem eraseRespKeys_resolveRespEntry {S : Setup} (roCache randCache : List (Bytes × DRKey))
    (r : KeyIndRespEntry S) :
    eraseRespKeys (resolveRespEntry roCache randCache r) = eraseRespKeys r := rfl

@[simp]
theorem eraseStateKeysAndCache_resolveLazyBase {S : Setup} (randCache : List (Bytes × DRKey))
    (st : KeyIndState S) :
    eraseStateKeysAndCache (resolveLazyBase randCache st) = eraseStateKeysAndCache st := by
  unfold eraseStateKeysAndCache resolveLazyBase
  simp [List.map_map, Function.comp_def]

@[simp]
theorem eraseShCrKeysAndCache_resolveLazyShCr {S : Setup} (randCache : List (Bytes × DRKey))
    (hst : KeyIndShCrState S) :
    eraseShCrKeysAndCache (resolveLazyShCr randCache hst) = eraseShCrKeysAndCache hst := by
  unfold eraseShCrKeysAndCache resolveLazyShCr
  simp

@[simp]
theorem finalizeKeyIndG3_resolveLazyShCr (S : Setup) (P : Primitives)
    (secb b' : Bool) (randCache : List (Bytes × DRKey)) (hst : KeyIndShCrState S) :
    finalizeKeyIndG3 S P secb b' (resolveLazyShCr randCache hst) =
      finalizeKeyIndG3 S P secb b' hst := by
  rw [← finalizeKeyIndG3_eraseShCrKeysAndCache S P secb b' (resolveLazyShCr randCache hst),
      eraseShCrKeysAndCache_resolveLazyShCr,
      finalizeKeyIndG3_eraseShCrKeysAndCache]

@[simp]
theorem badKeyIndFgAny_resolveLazyBase {S : Setup} (P : Primitives) (maxLen : ℕ)
    (randCache : List (Bytes × DRKey)) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgAny4 P maxLen (resolveLazyBase randCache st) advRoLog =
      badKeyIndFgAny4 P maxLen st advRoLog := by
  rw [← badKeyIndFgAny4_eraseStateKeysAndCache P maxLen (resolveLazyBase randCache st) advRoLog,
      eraseStateKeysAndCache_resolveLazyBase,
      badKeyIndFgAny4_eraseStateKeysAndCache]

theorem map_resolveSessionEntry_evalCache_ro {S : Setup}
    (roCache randCache : List (Bytes × DRKey)) (sec : Bytes)
    (sessions : List (KeyIndInitiatorEntry S))
    (hRo : ∀ s ∈ sessions, (roCache.find? (fun (x, _) => x == s.drKeyReal.rootKey)).isSome = true)
    (q : DRKey × List (Bytes × DRKey)) (hq : q ∈ support (evalCache roCache sec)) :
    sessions.map (resolveSessionEntry q.2 randCache) =
      sessions.map (resolveSessionEntry roCache randCache) := by
  refine List.map_congr_left (fun s hs => ?_)
  have h1 := (lookupCacheKey_evalCache_preserves roCache s.drKeyReal.rootKey sec (hRo s hs) q hq).1
  simp [resolveSessionEntry, h1]

theorem map_resolveRespEntry_evalCache_ro {S : Setup}
    (roCache randCache : List (Bytes × DRKey)) (sec : Bytes)
    (respSessions : List (KeyIndRespEntry S))
    (hRo : ∀ r ∈ respSessions, (roCache.find? (fun (x, _) => x == r.drKeyReal.rootKey)).isSome =
      true)
    (q : DRKey × List (Bytes × DRKey)) (hq : q ∈ support (evalCache roCache sec)) :
    respSessions.map (resolveRespEntry q.2 randCache) =
      respSessions.map (resolveRespEntry roCache randCache) := by
  refine List.map_congr_left (fun r hr => ?_)
  have h1 := (lookupCacheKey_evalCache_preserves roCache r.drKeyReal.rootKey sec (hRo r hr) q hq).1
  simp [resolveRespEntry, h1]

theorem map_resolveSessionEntry_cons_rand {S : Setup}
    (roCache randCache : List (Bytes × DRKey)) (pid : Bytes) (dk : DRKey)
    (sessions : List (KeyIndInitiatorEntry S))
    (hRand : ∀ s ∈ sessions, (randCache.find? (fun (x, _) => x == s.drKeyRand.rootKey)).isSome =
      true)
    (hNone : randCache.find? (fun (x, _) => x == pid) = none) :
    sessions.map (resolveSessionEntry roCache ((pid, dk) :: randCache)) =
      sessions.map (resolveSessionEntry roCache randCache) := by
  refine List.map_congr_left (fun s hs => ?_)
  have h1 := (lookupCacheKey_cons_of_find_none_of_isSome randCache s.drKeyRand.rootKey pid dk (hRand
    s hs) hNone).1
  simp [resolveSessionEntry, h1]

theorem map_resolveRespEntry_cons_rand {S : Setup}
    (roCache randCache : List (Bytes × DRKey)) (pid : Bytes) (dk : DRKey)
    (respSessions : List (KeyIndRespEntry S))
    (hRand : ∀ r ∈ respSessions, (randCache.find? (fun (x, _) => x == r.drKeyRand.rootKey)).isSome =
      true)
    (hNone : randCache.find? (fun (x, _) => x == pid) = none) :
    respSessions.map (resolveRespEntry roCache ((pid, dk) :: randCache)) =
      respSessions.map (resolveRespEntry roCache randCache) := by
  refine List.map_congr_left (fun r hr => ?_)
  have h1 := (lookupCacheKey_cons_of_find_none_of_isSome randCache r.drKeyRand.rootKey pid dk (hRand
    r hr) hNone).1
  simp [resolveRespEntry, h1]

theorem find_sid_map_resolveSessionEntry {S : Setup}
    (roCache randCache : List (Bytes × DRKey))
    (sessions : List (KeyIndInitiatorEntry S)) (sid : SessionId S) :
    (sessions.map (resolveSessionEntry roCache randCache)).find? (fun e => e.sid == sid) =
      (sessions.find? (fun e => e.sid == sid)).map (resolveSessionEntry roCache randCache) := by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons]
    have hSid : (resolveSessionEntry roCache randCache s).sid = s.sid := rfl
    rw [hSid]
    cases (s.sid == sid) <;> [exact ih; rfl]

theorem find_sid_map_resolveRespEntry {S : Setup}
    (roCache randCache : List (Bytes × DRKey))
    (respSessions : List (KeyIndRespEntry S)) (sid : SessionId S) :
    (respSessions.map (resolveRespEntry roCache randCache)).find? (fun r => r.sid == sid) =
      (respSessions.find? (fun r => r.sid == sid)).map (resolveRespEntry roCache randCache) := by
  induction respSessions with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons]
    have hSid : (resolveRespEntry roCache randCache r).sid = r.sid := rfl
    rw [hSid]
    cases (r.sid == sid) <;> [exact ih; rfl]

@[simp]
theorem keyIndPartner_resolveSessionEntry {S : Setup} (P : Primitives)
    (roCache randCache : List (Bytes × DRKey))
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    keyIndPartner P (resolveSessionEntry roCache randCache s) r = keyIndPartner P s r := rfl

@[simp]
theorem keyIndPartner_resolveRespEntry {S : Setup} (P : Primitives)
    (roCache randCache : List (Bytes × DRKey))
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    keyIndPartner P s (resolveRespEntry roCache randCache r) = keyIndPartner P s r := rfl

theorem find_partner_map_resolveSessionEntry {S : Setup} (P : Primitives)
    (roCache randCache : List (Bytes × DRKey))
    (sessions : List (KeyIndInitiatorEntry S)) (r : KeyIndRespEntry S) :
    (sessions.map (resolveSessionEntry roCache randCache)).find? (fun s => keyIndPartner P s r) =
      (sessions.find? (fun s => keyIndPartner P s r)).map (resolveSessionEntry roCache randCache) :=
        by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons, keyIndPartner_resolveSessionEntry]
    cases keyIndPartner P s r <;> [exact ih; rfl]

theorem find_partner_map_resolveRespEntry {S : Setup} (P : Primitives)
    (roCache randCache : List (Bytes × DRKey))
    (respSessions : List (KeyIndRespEntry S)) (s : KeyIndInitiatorEntry S) :
    (respSessions.map (resolveRespEntry roCache randCache)).find? (fun r => keyIndPartner P s r) =
      (respSessions.find? (fun r => keyIndPartner P s r)).map (resolveRespEntry roCache randCache)
        := by
  induction respSessions with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.find?_cons, keyIndPartner_resolveRespEntry]
    cases keyIndPartner P s r <;> [exact ih; rfl]

@[simp]
theorem isFreshKeyIndSession_resolveLazyBase {S : Setup}
    (randCache : List (Bytes × DRKey)) (st : KeyIndState S) (sid : SessionId S) :
    isKeyIndSessionTestable (resolveLazyBase randCache st) sid = isKeyIndSessionTestable st sid := by
  unfold isKeyIndSessionTestable resolveLazyBase
  dsimp only
  rw [find_sid_map_resolveSessionEntry, find_sid_map_resolveRespEntry]
  cases st.sessions.find? (fun e => e.sid == sid) with
  | some e => rfl
  | none =>
    cases st.respSessions.find? (fun r => r.sid == sid) with
    | some r => rfl
    | none => rfl

@[simp]
theorem preCheckKeyInd_resolveLazyBase (S : Setup) (P : Primitives) (sid : SessionId S) (u : Fin
  S.N_id)
    (bundle : PreKeyBundleInput) (randCache : List (Bytes × DRKey)) (st : KeyIndState S) :
    preCheckKeyInd S P sid u bundle (resolveLazyBase randCache st) = preCheckKeyInd S P sid u bundle
      st := by
  unfold preCheckKeyInd resolveLazyBase
  dsimp only
  rw [List.any_map]
  rfl

theorem pqxdhKeyIndImpl_resolveLazyBase_of_simple {S : Setup} (P : Primitives)
    (randCache : List (Bytes × DRKey)) (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j, q = .genSPK u j) ∨ (∃ u j o, q = .genOPK u j o) ∨
               q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (st : KeyIndState S) :
    (pqxdhKeyIndImpl true S P q).run (resolveLazyBase randCache st) =
      Prod.map id (resolveLazyBase randCache) <$> (pqxdhKeyIndImpl true S P q).run st ∧
    (∀ y ∈ support ((pqxdhKeyIndImpl true S P q).run st),
      (y.2.sessions, y.2.respSessions, y.2.roCache) =
        (st.sessions, st.respSessions, st.roCache)) := by
  refine ⟨?_, ?_⟩
  · rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u,
      j, rfl⟩
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
        Prod.map, map_eq_bind_pure_comp, bind_assoc]
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.principals.find? (fun (idx, _) => idx == u.val) <;>
        simp [StateT.run_pure, StateT.run_set, Prod.map]
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp [StateT.run_pure, Prod.map]
      · cases st.principals.find? (fun (idx, _) => idx == u.val) with
        | none => simp [StateT.run_pure, Prod.map]
        | some p =>
          simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            Prod.map, map_eq_bind_pure_comp, bind_assoc]
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp [StateT.run_pure, Prod.map]
      · simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          Prod.map, map_eq_bind_pure_comp, bind_assoc]
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp [StateT.run_pure, Prod.map]
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases registerAdvKey P st.advKeys sk <;>
        simp [StateT.run_pure, StateT.run_set, Prod.map]
    · unfold pqxdhKeyIndImpl resolveLazyBase
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;>
        simp [StateT.run_pure, StateT.run_set, Prod.map]
  · change PreservesAt (fun s => (s.sessions, s.respSessions, s.roCache)) st (pqxdhKeyIndImpl true S
      P q)
    rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u,
      j, rfl⟩ <;>
    · unfold pqxdhKeyIndImpl
      dsimp only
      prove_preserves_at

theorem liftShCrBase_resolveLazyShCr {S : Setup} {α : Type} (randCache : List (Bytes × DRKey))
    (m : StateT (KeyIndState S) ProbComp α) (hst : KeyIndShCrState S)
    (hm : m.run (resolveLazyBase randCache hst.base) =
      Prod.map id (resolveLazyBase randCache) <$> m.run hst.base) :
    (liftShCrBase m).run (resolveLazyShCr randCache hst) =
      Prod.map id (resolveLazyShCr randCache) <$> (liftShCrBase m).run hst := by
  change (do let (a, base') ← m.run (resolveLazyBase randCache hst.base); pure (a,
    { resolveLazyShCr randCache hst with base := base' })) =
    Prod.map id (resolveLazyShCr randCache) <$> (do let (a, base') ← m.run hst.base; pure (a,
      { hst with base := base' }))
  rw [hm, bind_map_left, map_bind]
  rfl

theorem liftKeyIndAdvShCr_resolveLazyAdv {S : Setup} (randCache : List (Bytes × DRKey))
    (m : StateT (KeyIndShCrState S) ProbComp KeyIndResponse) (adv : KeyIndAdvCutoffState S)
    (hm : m.run (resolveLazyShCr randCache adv.shCr) =
      Prod.map id (resolveLazyShCr randCache) <$> m.run adv.shCr) :
    (liftKeyIndAdvShCr m).run { adv with shCr := resolveLazyShCr randCache adv.shCr } =
      Prod.map id (fun a => { a with shCr := resolveLazyShCr randCache a.shCr }) <$>
        (liftKeyIndAdvShCr m).run adv := by
  simp [liftKeyIndAdvShCr, StateT.run_mk, hm, Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndAdvTagImpl_run_of_simple {S : Setup} (eagerRoHonest eagerRand testReal : Bool)
    (P : Primitives) (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j, q = .genSPK u j) ∨ (∃ u j o, q = .genOPK u j o) ∨
               q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (lst : KeyIndLazyState S) :
    (pqxdhKeyIndAdvTagImpl eagerRoHonest eagerRand testReal S P q).run lst =
      (do
        let (r, adv') ← (pqxdhKeyIndAdvG3Impl S P q).run lst.adv
        pure (r, { lst with adv := adv' })) := by
  have hCache := pqxdhKeyIndAdvG3Impl_withAdvRoCache_of_simple S P q hSimple
    (withAdvRoCache [] lst.adv) lst.adv.shCr.base.roCache
  have hId : withAdvRoCache lst.adv.shCr.base.roCache (withAdvRoCache [] lst.adv) = lst.adv := rfl
  rw [hId] at hCache
  rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u, j,
    rfl⟩ <;>
  · dsimp only [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, tagStepView, liftTagView,
      getLazyView, setLazyView]
    rw [StateT.run_mk, hCache]
    simp [runLazyPost, Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem evalHkdfOrRo_true_eq_evalCache (P : Primitives) (c : List (Bytes × DRKey)) (sec : Bytes) :
    evalHkdfOrRo true P c sec = evalCache c sec := by
  unfold evalHkdfOrRo evalCache
  cases c.find? (fun (s, _) => s == sec) <;> simp

theorem mem_support_base_of_pqxdhKeyIndAdvG3Impl {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S)
    (z : KeyIndResponse × KeyIndAdvCutoffState S)
    (hz : z ∈ support ((pqxdhKeyIndAdvG3Impl S P q).run adv)) :
    (z.1, z.2.shCr.base) ∈ support ((pqxdhKeyIndImpl true S P q).run adv.shCr.base) := by
  have h1 : Prod.map id ShCrState.base <$>
      (Prod.map id KeyIndAdvCutoffState.shCr <$> ((pqxdhKeyIndAdvG3Impl S P q).run adv)) =
      (pqxdhKeyIndImpl true S P q).run adv.shCr.base := by
    rw [pqxdhKeyIndAdvG3Impl_shCr, map_base_pqxdhKeyIndShCrImpl_false]
  rw [← h1]
  simp only [Functor.map_map, support_map, Set.mem_image]
  exact ⟨z, hz, rfl⟩

def RelEagerTag {S : Setup} (s1 : KeyIndAdvCutoffState S) (s2 : KeyIndLazyState S) : Prop :=
  s1 = resolveLazyAdv s2 ∧ WellFormedLazy s2

theorem relEagerTag_empty (S : Setup) :
    RelEagerTag { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
      (KeyIndLazyState.empty S) :=
  ⟨rfl, wellFormedLazy_empty S⟩

theorem evalDist_step_relEagerTag_of_simple {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j, q = .genSPK u j) ∨ (∃ u j o, q = .genOPK u j o) ∨
               q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (lst : KeyIndLazyState S) (hWF : WellFormedLazy lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P q).run (resolveLazyAdv lst) >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P q).run lst >>= k2] := by
  rw [pqxdhKeyIndAdvTagImpl_run_of_simple true true testReal P q hSimple lst]
  have hBase := pqxdhKeyIndImpl_resolveLazyBase_of_simple P lst.randCache q hSimple
    lst.adv.shCr.base
  have hAdv : (pqxdhKeyIndAdvTestImpl testReal S P q).run (resolveLazyAdv lst) =
      Prod.map id (fun a => { a with shCr := resolveLazyShCr lst.randCache a.shCr }) <$>
        (pqxdhKeyIndAdvG3Impl S P q).run lst.adv := by
    rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u,
      j, rfl⟩ <;>
      exact liftKeyIndAdvShCr_resolveLazyAdv lst.randCache
        (liftShCrBase (pqxdhKeyIndImpl true S P _)) lst.adv
        (liftShCrBase_resolveLazyShCr lst.randCache _ lst.adv.shCr hBase.1)
  rw [hAdv, bind_map_left, bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
  have hzBase := mem_support_base_of_pqxdhKeyIndAdvG3Impl P q lst.adv z hz
  have hEq := hBase.2 (z.1, z.2.shCr.base) hzBase
  injection hEq with hSess hRest
  injection hRest with hResp hRo
  refine hk z.1 _ { lst with adv := z.2 } ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [hSess, hRo]; exact hWF.sess_ro
  · dsimp only; rw [hSess]; exact hWF.sess_rand
  · dsimp only; rw [hResp, hRo]; exact hWF.resp_ro
  · dsimp only; rw [hResp]; exact hWF.resp_rand
  · dsimp only; rw [hSess, hResp]; exact hWF.rand_len

@[simp]
theorem liftShCrBase_run {S : Setup} {α : Type} (m : StateT (KeyIndState S) ProbComp α)
    (hst : KeyIndShCrState S) :
    (liftShCrBase m).run hst =
      (do
        let (a, base') ← m.run hst.base
        pure (a, { hst with base := base' })) := rfl

theorem liftKeyIndAdvShCr_liftKeyIndShCrBase_run {S : Setup}
    (m : StateT (KeyIndState S) ProbComp KeyIndResponse) (adv : KeyIndAdvCutoffState S) :
    (liftKeyIndAdvShCr (liftKeyIndShCrBase m)).run adv =
      (do
        let (r, base') ← m.run adv.shCr.base
        pure (r, { adv with shCr := { adv.shCr with base := base' } })) := by
  simp [liftKeyIndAdvShCr, liftKeyIndShCrBase, liftShCrBase_run, StateT.run_mk]

@[simp]
theorem setLazyView_roCache {S : Setup} (adv' : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S) :
    (setLazyView adv' lst).adv.shCr.base.roCache = lst.adv.shCr.base.roCache := rfl

@[simp]
theorem setLazyView_randCache {S : Setup} (adv' : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
  :
    (setLazyView adv' lst).randCache = lst.randCache := rfl

@[simp]
theorem setLazyView_getLazyView {S : Setup} (lst : KeyIndLazyState S) :
    setLazyView (getLazyView lst) lst = lst := rfl

theorem pqxdhKeyIndAdvTagImpl_run {S : Setup} (eagerRoHonest eagerRand testReal : Bool)
    (P : Primitives) (q : KeyIndQuery S) (lst : KeyIndLazyState S) :
    (pqxdhKeyIndAdvTagImpl eagerRoHonest eagerRand testReal S P q).run lst =
      (do
        let (post, adv') ← tagStepView testReal S P q (getLazyView lst)
        runLazyPost eagerRoHonest eagerRand S post (setLazyView adv' lst)) := by
  simp [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, liftTagView, StateT.run_mk]

theorem evalDist_step_relEagerTag_roQuery {S : Setup} (testReal : Bool) (P : Primitives)
    (sec : Bytes) (lst : KeyIndLazyState S) (hWF : WellFormedLazy lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.roQuery sec)).run (resolveLazyAdv lst) >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.roQuery sec)).run lst >>= k2] := by
  have hEval := evalHkdfOrRo_true_eq_evalCache P lst.adv.shCr.base.roCache sec
  have hLHS : ((pqxdhKeyIndAdvTestImpl testReal S P (.roQuery sec)).run (resolveLazyAdv lst) >>= k1)
    =
      (evalCache lst.adv.shCr.base.roCache sec >>= fun q =>
        k1 (.drKeyResp q.1, {
          shCr := { lst.adv.shCr with base :=
            { (resolveLazyBase lst.randCache lst.adv.shCr.base) with roCache := q.2 } }
          advRoLog := sec :: lst.adv.advRoLog })) := by
    dsimp only [pqxdhKeyIndAdvTestImpl, pqxdhKeyIndAdvG3Impl, pqxdhKeyIndShCrImpl,
      liftKeyIndShCrBase, pqxdhKeyIndImpl, resolveLazyAdv, resolveLazyShCr]
    simp only [StateT.run_mk, liftShCrBase_run, StateT.run_bind, StateT.run_get, pure_bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc]
    have hRo : (resolveLazyBase lst.randCache lst.adv.shCr.base).roCache = lst.adv.shCr.base.roCache
      := rfl
    rw [hRo, hEval]
  have hRHS : ((pqxdhKeyIndAdvTagImpl true true testReal S P (.roQuery sec)).run lst >>= k2) =
      (evalCache lst.adv.shCr.base.roCache sec >>= fun q =>
        k2 (.drKeyResp q.1, { lst with adv := {
          shCr := { lst.adv.shCr with base := { lst.adv.shCr.base with roCache := q.2 } }
          advRoLog := sec :: lst.adv.advRoLog } })) := by
    dsimp only [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, tagStepView, liftTagView,
      getLazyView, setLazyView, runLazyPost, roLens, CacheLens.eval,
      withAdvRoCache, withShCrRoCache, withBaseRoCache]
    simp only [StateT.run_mk, pure_bind, bind_assoc]
  rw [hLHS, hRHS]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun q hq => ?_
  have hSess := map_resolveSessionEntry_evalCache_ro
    lst.adv.shCr.base.roCache lst.randCache sec lst.adv.shCr.base.sessions hWF.sess_ro q hq
  have hResp := map_resolveRespEntry_evalCache_ro
    lst.adv.shCr.base.roCache lst.randCache sec lst.adv.shCr.base.respSessions hWF.resp_ro q hq
  refine hk (.drKeyResp q.1) _ _ ⟨?_, ?_, hWF.sess_rand, ?_, hWF.resp_rand, hWF.rand_len⟩
  · simp [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, hSess, hResp]
  · intro s hs
    exact (lookupCacheKey_evalCache_preserves _ s.drKeyReal.rootKey sec (hWF.sess_ro s hs) q hq).2
  · intro r hr
    exact (lookupCacheKey_evalCache_preserves _ r.drKeyReal.rootKey sec (hWF.resp_ro r hr) q hq).2

theorem map_markRevealed_resolveSessionEntry {S : Setup}
    (roCache randCache : List (Bytes × DRKey))
    (sessions : List (KeyIndInitiatorEntry S)) (sid : SessionId S) :
    (sessions.map (fun s => if s.sid == sid then { s with revealed := true } else s)).map
      (resolveSessionEntry roCache randCache) =
    (sessions.map (resolveSessionEntry roCache randCache)).map
      (fun s => if s.sid == sid then { s with revealed := true } else s) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun s _ => ?_)
  dsimp only [Function.comp_apply]
  have hSid : (resolveSessionEntry roCache randCache s).sid = s.sid := rfl
  rw [hSid]
  cases s.sid == sid <;> rfl

theorem map_markRevealed_resolveRespEntry {S : Setup}
    (roCache randCache : List (Bytes × DRKey))
    (respSessions : List (KeyIndRespEntry S)) (sid : SessionId S) :
    (respSessions.map (fun r => if r.sid == sid then { r with revealed := true } else r)).map
      (resolveRespEntry roCache randCache) =
    (respSessions.map (resolveRespEntry roCache randCache)).map
      (fun r => if r.sid == sid then { r with revealed := true } else r) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  dsimp only [Function.comp_apply]
  have hSid : (resolveRespEntry roCache randCache r).sid = r.sid := rfl
  rw [hSid]
  cases r.sid == sid <;> rfl

theorem map_markTested_resolveSessionEntry {S : Setup}
    (roCache randCache : List (Bytes × DRKey))
    (sessions : List (KeyIndInitiatorEntry S)) (sid : SessionId S) :
    (sessions.map (fun s => if s.sid == sid then { s with tested := true } else s)).map
      (resolveSessionEntry roCache randCache) =
    (sessions.map (resolveSessionEntry roCache randCache)).map
      (fun s => if s.sid == sid then { s with tested := true } else s) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun s _ => ?_)
  dsimp only [Function.comp_apply]
  have hSid : (resolveSessionEntry roCache randCache s).sid = s.sid := rfl
  rw [hSid]
  cases s.sid == sid <;> rfl

theorem map_markTested_resolveRespEntry {S : Setup}
    (roCache randCache : List (Bytes × DRKey))
    (respSessions : List (KeyIndRespEntry S)) (sid : SessionId S) :
    (respSessions.map (fun r => if r.sid == sid then { r with tested := true } else r)).map
      (resolveRespEntry roCache randCache) =
    (respSessions.map (resolveRespEntry roCache randCache)).map
      (fun r => if r.sid == sid then { r with tested := true } else r) := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun r _ => ?_)
  dsimp only [Function.comp_apply]
  have hSid : (resolveRespEntry roCache randCache r).sid = r.sid := rfl
  rw [hSid]
  cases r.sid == sid <;> rfl

theorem wellFormedLazy_of_map_sessions {S : Setup} (lst : KeyIndLazyState S)
    (f : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S)
    (hReal : ∀ s, (f s).drKeyReal = s.drKeyReal)
    (hRand : ∀ s, (f s).drKeyRand = s.drKeyRand)
    (hWF : WellFormedLazy lst) :
    WellFormedLazy { lst with adv := { lst.adv with shCr := { lst.adv.shCr with base :=
      { lst.adv.shCr.base with sessions := lst.adv.shCr.base.sessions.map f } } } } := by
  refine ⟨?_, ?_, hWF.resp_ro, hWF.resp_rand, ?_⟩
  · intro s hs
    rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
    rw [hReal]; exact hWF.sess_ro s0 hs0
  · intro s hs
    rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
    rw [hRand]; exact hWF.sess_rand s0 hs0
  · intro p hp
    simpa [List.length_map] using hWF.rand_len p hp

theorem wellFormedLazy_of_map_respSessions {S : Setup} (lst : KeyIndLazyState S)
    (f : KeyIndRespEntry S → KeyIndRespEntry S)
    (hReal : ∀ r, (f r).drKeyReal = r.drKeyReal)
    (hRand : ∀ r, (f r).drKeyRand = r.drKeyRand)
    (hWF : WellFormedLazy lst) :
    WellFormedLazy { lst with adv := { lst.adv with shCr := { lst.adv.shCr with base :=
      { lst.adv.shCr.base with respSessions := lst.adv.shCr.base.respSessions.map f } } } } := by
  refine ⟨hWF.sess_ro, hWF.sess_rand, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_map.mp hr with ⟨r0, hr0, rfl⟩
    rw [hReal]; exact hWF.resp_ro r0 hr0
  · intro r hr
    rcases List.mem_map.mp hr with ⟨r0, hr0, rfl⟩
    rw [hRand]; exact hWF.resp_rand r0 hr0
  · intro p hp
    simpa [List.length_map] using hWF.rand_len p hp

theorem pqxdhKeyIndAdvTestImpl_revealSessionKey_run {S : Setup} (testReal : Bool) (P : Primitives)
    (sid : SessionId S) (adv : KeyIndAdvCutoffState S) :
    (pqxdhKeyIndAdvTestImpl testReal S P (.revealSessionKey sid)).run adv =
      (let st := adv.shCr.base
       match st.sessions.find? (fun e => e.sid == sid) with
       | some e =>
         if e.tested then pure (.noneResp, adv)
         else
           let sessions' := st.sessions.map (fun s =>
             if s.sid == sid then { s with revealed := true } else s)
           pure (.drKeyResp e.drKeyReal,
             { adv with shCr := { adv.shCr with base := { st with sessions := sessions' } } })
       | none =>
         match st.respSessions.find? (fun r => r.sid == sid) with
         | none => pure (.noneResp, adv)
         | some r =>
           if r.tested then pure (.noneResp, adv)
           else
             let resp' := st.respSessions.map (fun x =>
               if x.sid == sid then { x with revealed := true } else x)
             pure (.drKeyResp r.drKeyReal,
               { adv with shCr :=
                 { adv.shCr with base := { st with respSessions := resp' } } })) := by
  change (liftKeyIndAdvShCr (liftKeyIndShCrBase (pqxdhKeyIndImpl true S P (.revealSessionKey
    sid)))).run adv = _
  rw [liftKeyIndAdvShCr_liftKeyIndShCrBase_run]
  dsimp only [pqxdhKeyIndImpl]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    dsimp only
    split_ifs <;> [simp [StateT.run_pure]; simp [StateT.run_set]]
  | none =>
    dsimp only
    cases adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
    | none => simp [StateT.run_pure]
    | some r =>
      dsimp only
      split_ifs <;> [simp [StateT.run_pure]; simp [StateT.run_set]]

theorem pqxdhKeyIndAdvTestImpl_testSession_run {S : Setup} (testReal : Bool) (P : Primitives)
    (sid : SessionId S) (adv : KeyIndAdvCutoffState S) :
    (pqxdhKeyIndAdvTestImpl testReal S P (.testSession sid)).run adv =
      (let st := adv.shCr.base
       if !isKeyIndSessionTestable st sid then
         pure (.noneResp, adv)
       else
         match st.sessions.find? (fun e => e.sid == sid) with
         | some e =>
           let sessions' := st.sessions.map (fun s =>
             if s.sid == sid then { s with tested := true } else s)
           pure (.drKeyResp (if testReal then e.drKeyReal else e.drKeyRand),
             { adv with shCr := { adv.shCr with base := { st with sessions := sessions' } } })
         | none =>
           match st.respSessions.find? (fun r => r.sid == sid) with
           | none => pure (.noneResp, adv)
           | some r =>
             let resp' := st.respSessions.map (fun x =>
               if x.sid == sid then { x with tested := true } else x)
             pure (.drKeyResp (if testReal then r.drKeyReal else r.drKeyRand),
               { adv with shCr :=
                 { adv.shCr with base := { st with respSessions := resp' } } })) := by
  change (liftKeyIndAdvShCr (liftKeyIndShCrBase (runKeyIndTestSession testReal S sid))).run adv = _
  rw [liftKeyIndAdvShCr_liftKeyIndShCrBase_run]
  dsimp only [runKeyIndTestSession]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (!isKeyIndSessionTestable adv.shCr.base sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
    | some e => simp [StateT.run_set]
    | none =>
      cases adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
      | none => simp [StateT.run_pure]
      | some r => simp [StateT.run_set]
  · simp [StateT.run_pure]

theorem evalDist_step_relEagerTag_revealSessionKey {S : Setup} (testReal : Bool) (P : Primitives)
    (sid : SessionId S) (lst : KeyIndLazyState S) (hWF : WellFormedLazy lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.revealSessionKey sid)).run (resolveLazyAdv lst) >>= k1]
      =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.revealSessionKey sid)).run lst >>= k2] := by
  rw [pqxdhKeyIndAdvTestImpl_revealSessionKey_run, pqxdhKeyIndAdvTagImpl_run]
  dsimp only [tagStepView, tagStepRevealSessionKey]
  have hFindSess : (resolveLazyAdv lst).shCr.base.sessions.find? (fun e => e.sid == sid) =
      (lst.adv.shCr.base.sessions.find? (fun e => e.sid == sid)).map
        (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache) :=
    find_sid_map_resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache
      lst.adv.shCr.base.sessions sid
  have hFindResp : (resolveLazyAdv lst).shCr.base.respSessions.find? (fun r => r.sid == sid) =
      (lst.adv.shCr.base.respSessions.find? (fun r => r.sid == sid)).map
        (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache) :=
    find_sid_map_resolveRespEntry lst.adv.shCr.base.roCache lst.randCache
      lst.adv.shCr.base.respSessions sid
  have hSessTag : (getLazyView lst).shCr.base.sessions = lst.adv.shCr.base.sessions := rfl
  have hRespTag : (getLazyView lst).shCr.base.respSessions = lst.adv.shCr.base.respSessions := rfl
  rw [hFindSess, hFindResp, hSessTag, hRespTag]
  cases hS : lst.adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    dsimp only [Option.map]
    have hTested : (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache e).tested = e.tested
      := rfl
    rw [hTested]
    cases e.tested
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazyPost, roLens,
        CacheLens.eval, setLazyView_roCache, bind_assoc]
      have hMem : e ∈ lst.adv.shCr.base.sessions := List.mem_of_find?_eq_some hS
      rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ e.drKeyReal.rootKey (hWF.sess_ro e hMem)]
      simp only [pure_bind]
      refine hk (.drKeyResp (lookupCacheKey lst.adv.shCr.base.roCache e.drKeyReal.rootKey)) _ _ ⟨?_,
        ?_⟩
      · simp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, getLazyView, setLazyView,
          withAdvRoCache, withShCrRoCache, withBaseRoCache,
          map_markRevealed_resolveSessionEntry]
      · exact wellFormedLazy_of_map_sessions lst
          (fun s => if s.sid == sid then { s with revealed := true } else s)
          (fun s => by cases s.sid == sid <;> rfl)
          (fun s => by cases s.sid == sid <;> rfl) hWF
    · simp only [↓reduceIte, pure_bind, runLazyPost, setLazyView_getLazyView]
      exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
  | none =>
    dsimp only [Option.map]
    cases hR : lst.adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
    | none =>
      dsimp only [Option.map]
      simp only [pure_bind, runLazyPost, setLazyView_getLazyView]
      exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
    | some r =>
      dsimp only [Option.map]
      have hTested : (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache r).tested = r.tested
        := rfl
      rw [hTested]
      cases r.tested
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazyPost, roLens,
          CacheLens.eval, setLazyView_roCache, bind_assoc]
        have hMem : r ∈ lst.adv.shCr.base.respSessions := List.mem_of_find?_eq_some hR
        rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ r.drKeyReal.rootKey (hWF.resp_ro r hMem)]
        simp only [pure_bind]
        refine hk (.drKeyResp (lookupCacheKey lst.adv.shCr.base.roCache r.drKeyReal.rootKey)) _ _
          ⟨?_, ?_⟩
        · simp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, getLazyView, setLazyView,
            withAdvRoCache, withShCrRoCache, withBaseRoCache,
            map_markRevealed_resolveRespEntry]
        · exact wellFormedLazy_of_map_respSessions lst
            (fun x => if x.sid == sid then { x with revealed := true } else x)
            (fun x => by cases x.sid == sid <;> rfl)
            (fun x => by cases x.sid == sid <;> rfl) hWF
      · simp only [↓reduceIte, pure_bind, runLazyPost, setLazyView_getLazyView]
        exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩

theorem evalDist_step_relEagerTag_testSession {S : Setup} (testReal : Bool) (P : Primitives)
    (sid : SessionId S) (lst : KeyIndLazyState S) (hWF : WellFormedLazy lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.testSession sid)).run (resolveLazyAdv lst) >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.testSession sid)).run lst >>= k2] := by
  rw [pqxdhKeyIndAdvTestImpl_testSession_run, pqxdhKeyIndAdvTagImpl_run]
  dsimp only [tagStepView, tagStepTestSession]
  have hFresh1 : isKeyIndSessionTestable (resolveLazyAdv lst).shCr.base sid =
      isKeyIndSessionTestable lst.adv.shCr.base sid :=
    isFreshKeyIndSession_resolveLazyBase lst.randCache lst.adv.shCr.base sid
  have hFresh2 : isKeyIndSessionTestable (getLazyView lst).shCr.base sid =
      isKeyIndSessionTestable lst.adv.shCr.base sid := rfl
  have hFindSess : (resolveLazyAdv lst).shCr.base.sessions.find? (fun e => e.sid == sid) =
      (lst.adv.shCr.base.sessions.find? (fun e => e.sid == sid)).map
        (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache) :=
    find_sid_map_resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache
      lst.adv.shCr.base.sessions sid
  have hFindResp : (resolveLazyAdv lst).shCr.base.respSessions.find? (fun r => r.sid == sid) =
      (lst.adv.shCr.base.respSessions.find? (fun r => r.sid == sid)).map
        (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache) :=
    find_sid_map_resolveRespEntry lst.adv.shCr.base.roCache lst.randCache
      lst.adv.shCr.base.respSessions sid
  have hSessTag : (getLazyView lst).shCr.base.sessions = lst.adv.shCr.base.sessions := rfl
  have hRespTag : (getLazyView lst).shCr.base.respSessions = lst.adv.shCr.base.respSessions := rfl
  rw [hFresh1, hFresh2, hFindSess, hFindResp, hSessTag, hRespTag]
  cases (!isKeyIndSessionTestable lst.adv.shCr.base sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hS : lst.adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only [Option.map]
      have hMem : e ∈ lst.adv.shCr.base.sessions := List.mem_of_find?_eq_some hS
      have hWF' : WellFormedLazy
        { lst with adv := { lst.adv with shCr := { lst.adv.shCr with base :=
          { lst.adv.shCr.base with sessions := lst.adv.shCr.base.sessions.map (fun s => if s.sid ==
            sid then { s with tested := true } else s) } } } } :=
        wellFormedLazy_of_map_sessions lst
          (fun s => if s.sid == sid then { s with tested := true } else s)
          (fun s => by cases s.sid == sid <;> rfl)
          (fun s => by cases s.sid == sid <;> rfl) hWF
      cases testReal
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazyPost, randLens,
          CacheLens.eval, setLazyView_randCache, bind_assoc]
        rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ e.drKeyRand.rootKey (hWF.sess_rand e hMem)]
        simp only [pure_bind]
        refine hk (.drKeyResp (lookupCacheKey lst.randCache e.drKeyRand.rootKey)) _ _ ⟨?_, hWF'⟩
        simp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, getLazyView, setLazyView,
          withAdvRoCache, withShCrRoCache, withBaseRoCache,
          map_markTested_resolveSessionEntry]
      · simp only [↓reduceIte, pure_bind, runLazyPost, roLens,
          CacheLens.eval, setLazyView_roCache, bind_assoc]
        rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ e.drKeyReal.rootKey (hWF.sess_ro e hMem)]
        simp only [pure_bind]
        refine hk (.drKeyResp (lookupCacheKey lst.adv.shCr.base.roCache e.drKeyReal.rootKey)) _ _
          ⟨?_, hWF'⟩
        simp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, getLazyView, setLazyView,
          withAdvRoCache, withShCrRoCache, withBaseRoCache,
          map_markTested_resolveSessionEntry]
    | none =>
      dsimp only [Option.map]
      cases hR : lst.adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        dsimp only [Option.map]
        simp only [pure_bind, runLazyPost, setLazyView_getLazyView]
        exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
      | some r =>
        dsimp only [Option.map]
        have hMem : r ∈ lst.adv.shCr.base.respSessions := List.mem_of_find?_eq_some hR
        have hWF' : WellFormedLazy
          { lst with adv := { lst.adv with shCr := { lst.adv.shCr with base :=
            { lst.adv.shCr.base with respSessions := lst.adv.shCr.base.respSessions.map (fun x => if
              x.sid == sid then { x with tested := true } else x) } } } } :=
          wellFormedLazy_of_map_respSessions lst
            (fun x => if x.sid == sid then { x with tested := true } else x)
            (fun x => by cases x.sid == sid <;> rfl)
            (fun x => by cases x.sid == sid <;> rfl) hWF
        cases testReal
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, runLazyPost, randLens,
            CacheLens.eval, setLazyView_randCache, bind_assoc]
          rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ r.drKeyRand.rootKey (hWF.resp_rand r
            hMem)]
          simp only [pure_bind]
          refine hk (.drKeyResp (lookupCacheKey lst.randCache r.drKeyRand.rootKey)) _ _ ⟨?_, hWF'⟩
          simp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, getLazyView, setLazyView,
            withAdvRoCache, withShCrRoCache, withBaseRoCache,
            map_markTested_resolveRespEntry]
        · simp only [↓reduceIte, pure_bind, runLazyPost, roLens,
            CacheLens.eval, setLazyView_roCache, bind_assoc]
          rw [evalCache_eq_pure_lookupCacheKey_of_isSome _ r.drKeyReal.rootKey (hWF.resp_ro r hMem)]
          simp only [pure_bind]
          refine hk (.drKeyResp (lookupCacheKey lst.adv.shCr.base.roCache r.drKeyReal.rootKey)) _ _
            ⟨?_, hWF'⟩
          simp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, getLazyView, setLazyView,
            withAdvRoCache, withShCrRoCache, withBaseRoCache,
            map_markTested_resolveRespEntry]
  · simp only [↓reduceIte, pure_bind, runLazyPost, setLazyView_getLazyView]
    exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩

@[simp]
theorem find_cons_isSome_of_isSome {α β : Type} [BEq α]
    (k : α) (v : β) (c : List (α × β)) (x : α)
    (h : (c.find? (fun (s, _) => s == x)).isSome = true) :
    (((k, v) :: c).find? (fun (s, _) => s == x)).isSome = true := by
  simp only [List.find?_cons]
  cases k == x <;> simp [h]

@[simp]
theorem lookupCacheKey_cons_self (c : List (Bytes × DRKey)) (k : Bytes) (v : DRKey) :
    lookupCacheKey ((k, v) :: c) k = v := by
  unfold lookupCacheKey
  simp

theorem tagStepInitiate_getLazyView (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (lst : KeyIndLazyState S) :
    (do
      let (post, adv') ← tagStepInitiate S P sid u bundle (getLazyView lst)
      runLazyPost true true S post (setLazyView adv' lst)) =
    (do
      let (post, adv') ← tagStepInitiate S P sid u bundle lst.adv
      runLazyPost true true S post { lst with adv := adv' }) := by
  unfold tagStepInitiate getLazyView setLazyView withAdvRoCache withShCrRoCache
  dsimp only
  have hPre : preCheckKeyInd S P sid u bundle (withBaseRoCache [] lst.adv.shCr.base) =
      preCheckKeyInd S P sid u bundle lst.adv.shCr.base := rfl
  rw [hPre]
  cases preCheckKeyInd S P sid u bundle lst.adv.shCr.base with
  | none => rfl
  | some uEntry =>
    simp only [bind_assoc]
    congr 1; funext ekASk; congr 1; funext kemCoins
    have hPrin : (withBaseRoCache [] lst.adv.shCr.base).principals = lst.adv.shCr.base.principals :=
      rfl
    rw [hPrin]
    cases (!checkBundleSigs P lst.adv.shCr.base.principals bundle)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins <;> rfl
    · rfl

theorem evalDist_step_relEagerTag_initiate {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(liftKeyIndAdvShCr (runKeyIndShCrInitiate false S P sid u bundle)).run adv >>= k1] =
      𝒟[(do
          let (post, adv') ← tagStepInitiate S P sid u bundle (getLazyView lst)
          runLazyPost true true S post (setLazyView adv' lst)) >>= k2] := by
  rcases hRel with ⟨rfl, hWF⟩
  rw [tagStepInitiate_getLazyView]
  dsimp only [liftKeyIndAdvShCr, runKeyIndShCrInitiate, tagStepInitiate,
    resolveLazyAdv, resolveLazyShCr]
  rw [StateT.run_mk]
  dsimp only [runShCrInitiate2, StateT.run]
  rw [preCheckKeyInd_resolveLazyBase]
  cases hPre : preCheckKeyInd S P sid u bundle lst.adv.shCr.base with
  | none =>
    simp only [pure_bind, runLazyPost]
    exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
  | some uEntry =>
    simp only [bind_assoc, pure_bind]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
    have hPrin : (resolveLazyBase lst.randCache lst.adv.shCr.base).principals =
        lst.adv.shCr.base.principals := rfl
    rw [hPrin]
    by_cases hSigs : !checkBundleSigs P lst.adv.shCr.base.principals bundle
    · simp only [hSigs, ↓reduceIte, pure_bind, runLazyPost]
      exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
    · simp only [hSigs, Bool.false_eq_true, ↓reduceIte]
      cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
      | none =>
        simp only [pure_bind, runLazyPost]
        refine hk .noneResp _ _ ⟨rfl, hWF.sess_ro, hWF.sess_rand, hWF.resp_ro, hWF.resp_rand,
          hWF.rand_len⟩
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        dsimp only [finishKeyIndBase, keyIndPartnerRandKey?]
        have hRoEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).roCache =
            lst.adv.shCr.base.roCache := rfl
        have hSpkEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).spkBundles =
            lst.adv.shCr.base.spkBundles := rfl
        have hOpkEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).opkEntries =
            lst.adv.shCr.base.opkEntries := rfl
        rw [hPrin, hSpkEq, hOpkEq, hRoEq, evalHkdfOrRo_true_eq_evalCache]
        simp only [runLazyPost, Bool.or_true, applyShCrFinish, evalRoIf, ↓reduceIte, roLens,
          CacheLens.eval,
          withAdvRoCache, withShCrRoCache, withBaseRoCache,
          bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun q hq => ?_)
        rcases q with ⟨drKeyReal, roCache'⟩
        let s0 : KeyIndInitiatorEntry S := {
          sid := sid
          honestPeer := isHonestUncorruptedPeer P lst.adv.shCr.base.principals bundle.ikB
          peerIkPk := bundle.ikB
          peerSpkPk := bundle.spkB
          peerOpkPk? := bundle.opkB?.map Prod.snd
          peerPqspkPk := bundle.pqspkB
          spkHonest := (checkBundleProvenance P lst.adv.shCr.base.principals
            lst.adv.shCr.base.spkBundles lst.adv.shCr.base.opkEntries bundle).1
          opkHonest := (checkBundleProvenance P lst.adv.shCr.base.principals
            lst.adv.shCr.base.spkBundles lst.adv.shCr.base.opkEntries bundle).2.1
          pqspkHonest := (checkBundleProvenance P lst.adv.shCr.base.principals
            lst.adv.shCr.base.spkBundles lst.adv.shCr.base.opkEntries bundle).2.2
          ekASk := ekASk
          fresh := (isHonestUncorruptedPeer P lst.adv.shCr.base.principals bundle.ikB).isSome
          drKeyReal := tagDRKey (buildSecrets (P.x25519 uEntry.secIKA0 bundle.spkB) (P.x25519 ekASk
            bundle.ikB) (P.x25519 ekASk bundle.spkB) (bundle.opkB?.map (fun (_, opkPk) => P.x25519
            ekASk opkPk)) ss)
          drKeyRand := default
          hdr := { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bundle.spkId, opkId?
            := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
          tested := false }
        have hPartMap :
            (resolveLazyBase lst.randCache lst.adv.shCr.base).respSessions.find?
              (fun r => keyIndPartner P
                { s0 with drKeyReal := drKeyReal, drKeyRand := drKeyReal } r) =
            (lst.adv.shCr.base.respSessions.find? (fun r => keyIndPartner P s0 r)).map
              (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache) := by
          have hEqFn : (fun r => keyIndPartner P
            { s0 with drKeyReal := drKeyReal, drKeyRand := drKeyReal } r) =
              (fun r => keyIndPartner P s0 r) := rfl
          rw [hEqFn]
          exact find_partner_map_resolveRespEntry P lst.adv.shCr.base.roCache lst.randCache
            lst.adv.shCr.base.respSessions s0
        have hRespEq :
            (match findHonestPrincipal P lst.adv.shCr.base.principals bundle.ikB with
             | some _ => KeyIndResponse.hdrResp
                 { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bundle.spkId, opkId?
                 := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
             | none => KeyIndResponse.initUnfreshResp drKeyReal
                 { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bundle.spkId, opkId?
                 := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }) =
            (if (findHonestPrincipal P lst.adv.shCr.base.principals bundle.ikB).isSome then
               KeyIndResponse.hdrResp
                 { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bundle.spkId, opkId?
                 := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
             else
               KeyIndResponse.initUnfreshResp drKeyReal
                 { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bundle.spkId, opkId?
                 := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }) := by
          cases findHonestPrincipal P lst.adv.shCr.base.principals bundle.ikB <;> rfl
        rw [hPartMap]
        cases hPart : lst.adv.shCr.base.respSessions.find? (fun r => keyIndPartner P s0 r) with
        | some r =>
          simp only [Option.map_some, pure_bind, ← hRespEq]
          have hrMem : r ∈ lst.adv.shCr.base.respSessions := List.mem_of_find?_eq_some hPart
          refine hk _ _ _ ⟨?_, ?_⟩
          · dsimp only [applyShCrFinish, resolveLazyAdv, resolveLazyShCr, resolveLazyBase, List.map]
            have hHead :
                resolveSessionEntry roCache' lst.randCache { s0 with drKeyRand := r.drKeyRand } =
                { s0 with drKeyReal := drKeyReal,
                          drKeyRand := (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache
                            r).drKeyRand } := by
              unfold resolveSessionEntry resolveRespEntry
              dsimp only [s0]
              simp only [tagDRKey_rootKey, (lookupCacheKey_evalCache_self _ _ (drKeyReal, roCache')
                hq).1]
            have hTailSess :
                List.map (resolveSessionEntry roCache' lst.randCache) lst.adv.shCr.base.sessions =
                List.map (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache)
                  lst.adv.shCr.base.sessions :=
              map_resolveSessionEntry_evalCache_ro _ _ _ _ hWF.sess_ro (drKeyReal, roCache') hq
            have hResp :
                List.map (resolveRespEntry roCache' lst.randCache) lst.adv.shCr.base.respSessions =
                List.map (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache)
                  lst.adv.shCr.base.respSessions :=
              map_resolveRespEntry_evalCache_ro _ _ _ _ hWF.resp_ro (drKeyReal, roCache') hq
            rw [hHead, hTailSess, hResp]
          · refine ⟨?_, ?_, ?_, hWF.resp_rand, ?_⟩
            · intro s hs
              simp only [List.mem_cons] at hs ⊢
              rcases hs with rfl | hs
              · dsimp only [s0]
                rw [tagDRKey_rootKey]
                exact (lookupCacheKey_evalCache_self _ _ (drKeyReal, roCache') hq).2
              · exact (lookupCacheKey_evalCache_preserves _ s.drKeyReal.rootKey _ (hWF.sess_ro s hs)
                  (drKeyReal, roCache') hq).2
            · intro s hs
              simp only [List.mem_cons] at hs ⊢
              rcases hs with rfl | hs
              · exact hWF.resp_rand r hrMem
              · exact hWF.sess_rand s hs
            · intro r' hr'
              exact (lookupCacheKey_evalCache_preserves _ r'.drKeyReal.rootKey _ (hWF.resp_ro r'
                hr') (drKeyReal, roCache') hq).2
            · intro p hp
              simp only [List.length_cons]
              have hplen := hWF.rand_len p hp
              omega
        | none =>
          simp only [Option.map_none, evalRandIf, ↓reduceIte, randLens, CacheLens.eval, bind_assoc,
            pure_bind]
          have hFindPid : lst.randCache.find? (fun (x, _) => x == freshPidBytes lst.adv.shCr.base) =
            none := by
            refine find_none_of_length_lt lst.randCache (freshPidBytes lst.adv.shCr.base)
              (lst.adv.shCr.base.sessions.length + lst.adv.shCr.base.respSessions.length)
                hWF.rand_len ?_
            exact freshPidBytes_length lst.adv.shCr.base
          rw [evalCache_eq_sample_of_find_none lst.randCache (freshPidBytes lst.adv.shCr.base)
            hFindPid]
          simp only [bind_assoc, pure_bind]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKeyRand _ => ?_)
          rw [← hRespEq]
          refine hk _ _ _ ⟨?_, ?_⟩
          · dsimp only [applyShCrFinish, resolveLazyAdv, resolveLazyShCr, resolveLazyBase, List.map]
            have hHead :
                resolveSessionEntry roCache' ((freshPidBytes lst.adv.shCr.base, drKeyRand) ::
                  lst.randCache)
                  { s0 with drKeyRand := tagDRKey (freshPidBytes lst.adv.shCr.base) } =
                { s0 with drKeyReal := drKeyReal, drKeyRand := drKeyRand } := by
              unfold resolveSessionEntry
              dsimp only [s0]
              simp only [tagDRKey_rootKey, lookupCacheKey_cons_self,
                (lookupCacheKey_evalCache_self _ _ (drKeyReal, roCache') hq).1]
            have hTailSess :
                List.map (resolveSessionEntry roCache' ((freshPidBytes lst.adv.shCr.base, drKeyRand)
                  :: lst.randCache))
                  lst.adv.shCr.base.sessions =
                List.map (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache)
                  lst.adv.shCr.base.sessions := by
              rw [map_resolveSessionEntry_evalCache_ro _ _ _ _ hWF.sess_ro (drKeyReal, roCache') hq,
                  map_resolveSessionEntry_cons_rand _ _ _ _ _ hWF.sess_rand hFindPid]
            have hResp :
                List.map (resolveRespEntry roCache' ((freshPidBytes lst.adv.shCr.base, drKeyRand) ::
                  lst.randCache))
                  lst.adv.shCr.base.respSessions =
                List.map (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache)
                  lst.adv.shCr.base.respSessions := by
              rw [map_resolveRespEntry_evalCache_ro _ _ _ _ hWF.resp_ro (drKeyReal, roCache') hq,
                  map_resolveRespEntry_cons_rand _ _ _ _ _ hWF.resp_rand hFindPid]
            rw [hHead, hTailSess, hResp]
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro s hs
              simp only [List.mem_cons] at hs ⊢
              rcases hs with rfl | hs
              · dsimp only [s0]
                simp only [tagDRKey_rootKey]
                exact (lookupCacheKey_evalCache_self _ _ (drKeyReal, roCache') hq).2
              · exact (lookupCacheKey_evalCache_preserves _ s.drKeyReal.rootKey _ (hWF.sess_ro s hs)
                  (drKeyReal, roCache') hq).2
            · intro s hs
              simp only [List.mem_cons] at hs ⊢
              rcases hs with rfl | hs
              · simp [tagDRKey_rootKey]
              · exact find_cons_isSome_of_isSome _ _ _ _ (hWF.sess_rand s hs)
            · intro r hr
              simp only at hr ⊢
              exact (lookupCacheKey_evalCache_preserves _ r.drKeyReal.rootKey _ (hWF.resp_ro r hr)
                (drKeyReal, roCache') hq).2
            · intro r hr
              simp only at hr ⊢
              exact find_cons_isSome_of_isSome _ _ _ _ (hWF.resp_rand r hr)
            · intro p hp
              simp only [List.mem_cons, List.length_cons] at hp ⊢
              rcases hp with rfl | hp
              · dsimp only
                rw [freshPidBytes_length]
                omega
              · have hklen := hWF.rand_len p hp
                omega

theorem evalDist_step_relEagerTag_initiateOPK {S : Setup} (testReal : Bool) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.initiateOPK u i bundle)).run adv >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.initiateOPK u i bundle)).run lst >>= k2] :=
        by
  rw [pqxdhKeyIndAdvTagImpl_run]
  dsimp only [pqxdhKeyIndAdvTestImpl, pqxdhKeyIndAdvG3Impl, pqxdhKeyIndShCrImpl, tagStepView]
  cases bundle.opkB?.isNone
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact evalDist_step_relEagerTag_initiate P (.sendOPK u i) u bundle adv lst hRel k1 k2 hk
  · rcases hRel with ⟨rfl, hWF⟩
    simp only [↓reduceIte, liftKeyIndAdvShCr, StateT.run_mk, StateT.run_pure,
      pure_bind, runLazyPost, setLazyView_getLazyView]
    exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩

theorem evalDist_step_relEagerTag_initiateNoOPK {S : Setup} (testReal : Bool) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.initiateNoOPK u i bundle)).run adv >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.initiateNoOPK u i bundle)).run lst >>= k2]
        := by
  rw [pqxdhKeyIndAdvTagImpl_run]
  dsimp only [pqxdhKeyIndAdvTestImpl, pqxdhKeyIndAdvG3Impl, pqxdhKeyIndShCrImpl, tagStepView]
  cases bundle.opkB?.isSome
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact evalDist_step_relEagerTag_initiate P (.sendNoOPK u i) u bundle adv lst hRel k1 k2 hk
  · rcases hRel with ⟨rfl, hWF⟩
    simp only [↓reduceIte, liftKeyIndAdvShCr, StateT.run_mk, StateT.run_pure,
      pure_bind, runLazyPost, setLazyView_getLazyView]
    exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩

theorem tagStepAcceptOPK_getLazyView (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (lst : KeyIndLazyState S) :
    (do
      let (post, adv') ← tagStepAcceptOPK S P k j o hdr (getLazyView lst)
      runLazyPost true true S post (setLazyView adv' lst)) =
    (do
      let (post, adv') ← tagStepAcceptOPK S P k j o hdr lst.adv
      runLazyPost true true S post { lst with adv := adv' }) := by
  unfold tagStepAcceptOPK getLazyView setLazyView withAdvRoCache withShCrRoCache
    withBaseRoCache freshPidBytes
  dsimp only
  cases (!(hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val &&
      hdr.opkId? == some (UInt32.ofNat o.val) && hdr.ikAPk.length == 32 && hdr.ekAPk.length == 32))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases lst.adv.shCr.base.usedRecvOPK.contains (k.val, j.val, o.val)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases (!koskSenderOk P lst.adv.shCr.base.principals lst.adv.shCr.base.advKeys hdr.ikAPk)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases lst.adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => rfl
      | some kp =>
        dsimp only
        cases lst.adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => rfl
        | some bp =>
          dsimp only
          cases lst.adv.shCr.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
            with
          | none => rfl
          | some op =>
            dsimp only
            cases op.2.consumed
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases Model.acceptKeys P
                { ikBSk := kp.2.secIKA0, ikBPk := kp.2.ikAPk, spkBSk := bp.2.spkSk,
                  spkBPk := bp.2.spkPk, opkBSk? := some op.2.opkSk, pqspkBSk := bp.2.pqspkSk,
                  pqspkBPk := bp.2.pqspkPk, trustedPeer := true,
                  replayOk := (checkAndMarkKyberBaseKeySeen lst.adv.shCr.base.seenKyberBaseKeys k.val
                    hdr.pqspkId hdr.spkId hdr.ekAPk).1,
                  hdr := hdr } with
              | none => rfl
              | some _ =>
                cases P.kemDecaps bp.2.pqspkSk hdr.kemCt <;> rfl
            · rfl
      · rfl
    · rfl
  · rfl

theorem tagStepAcceptNoOPK_getLazyView (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (lst : KeyIndLazyState S) :
    (do
      let (post, adv') ← tagStepAcceptNoOPK S P k j l hdr (getLazyView lst)
      runLazyPost true true S post (setLazyView adv' lst)) =
    (do
      let (post, adv') ← tagStepAcceptNoOPK S P k j l hdr lst.adv
      runLazyPost true true S post { lst with adv := adv' }) := by
  unfold tagStepAcceptNoOPK getLazyView setLazyView withAdvRoCache withShCrRoCache
    withBaseRoCache freshPidBytes
  dsimp only
  cases (!(hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val &&
      hdr.opkId? == none && hdr.ikAPk.length == 32 && hdr.ekAPk.length == 32))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases lst.adv.shCr.base.usedRecvNoOPK.contains (k.val, j.val, l.val)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases (!koskSenderOk P lst.adv.shCr.base.principals lst.adv.shCr.base.advKeys hdr.ikAPk)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases lst.adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => rfl
      | some kp =>
        dsimp only
        cases lst.adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => rfl
        | some bp =>
          dsimp only
          cases Model.acceptKeys P
            { ikBSk := kp.2.secIKA0, ikBPk := kp.2.ikAPk, spkBSk := bp.2.spkSk,
              spkBPk := bp.2.spkPk, opkBSk? := none, pqspkBSk := bp.2.pqspkSk,
              pqspkBPk := bp.2.pqspkPk, trustedPeer := true,
              replayOk := (checkAndMarkKyberBaseKeySeen lst.adv.shCr.base.seenKyberBaseKeys k.val
                hdr.pqspkId hdr.spkId hdr.ekAPk).1,
              hdr := hdr } with
          | none => rfl
          | some _ =>
            cases P.kemDecaps bp.2.pqspkSk hdr.kemCt <;> rfl
      · rfl
    · rfl
  · rfl

end Proofs.SignalPqxdh.Security
