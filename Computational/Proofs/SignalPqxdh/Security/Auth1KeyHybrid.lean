/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthPrf
public import Computational.Proofs.SignalPqxdh.Security.CollisionsA
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key `Auth` hybrid games and sub-hop interfaces (`G3 .. G5`)

Defines the stage-parameterised one-key `Auth` hybrid oracles `pqxdhAuthHybridKoskImpl1Key` and
`pqxdhAuthHybridFixedImpl1Key`, the stage experiments `authFixedExpAtStage1Key`, and the sub-hop
statement interfaces for `G3.5 → G5` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-- KOSK-aligned stage-parameterised one-key `Auth` hybrid oracle for `G3 .. G5`. -/
def pqxdhAuthHybridKoskImpl1Key (stage : AuthHybridStage) (useRo checkAuth : Bool)
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
    liftAuthBase (pqxdhAuthImpl1KeyG useRo checkAuth S P q_other)

/-- Stage-parameterised one-key `Auth` hybrid oracle on `AuthHybridStateFixed S`, caching message
keys up to effective HKDF salt (`mkSaltKeyMatch`, DEV-LS25) for stages `.g3_8 .. .g5`. -/
def pqxdhAuthHybridFixedImpl1Key (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) := fun q => do
  let hst ← get
  if !stage.idealMsgKeys then
    let (resp, hst') ←
      liftM ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst.toAuthHybridState)
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
        liftM ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P qOther).run hst.toAuthHybridState)
      let recvCount' := if isAuthRecvQuery (.inr qOther) then hst.recvCount + 1 else hst.recvCount
      set ({ toAuthHybridState := hst', recvCount := recvCount',
             mkSaltCache := hst.mkSaltCache } : AuthHybridStateFixed S)
      return resp

theorem map_toAuthHybridState_pqxdhAuthHybridFixedImpl1Key (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    Prod.map id AuthHybridStateFixed.toAuthHybridState <$>
      (pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P q).run hst =
    (pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst.toAuthHybridState := by
  simp [pqxdhAuthHybridFixedImpl1Key, hStage, StateT.run_bind, Prod.map]

theorem map_toAuthHybridState_fullAuthHybridFixedImpl1Key (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    Prod.map id AuthHybridStateFixed.toAuthHybridState <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
        pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P) q).run hst.toAuthHybridState := by
  cases q with
  | inl uq =>
    simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq =>
    exact map_toAuthHybridState_pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P kq hst hStage

/-- Stage experiment for `Auth` running `pqxdhAuthHybridKoskImpl1Key` on `AuthHybridState S`. -/
noncomputable def authKoskExpAtStage1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
    pqxdhAuthHybridKoskImpl1Key stage true true S P
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

/-- Stage experiment for `Auth` running `pqxdhAuthHybridFixedImpl1Key` on `AuthHybridStateFixed S`. -/
noncomputable def authFixedExpAtStage1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
    pqxdhAuthHybridFixedImpl1Key stage true true S P
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

theorem authFixedExpAtStage_eq_authKoskExpAtStage1Key (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    authFixedExpAtStage1Key stage S P A = authKoskExpAtStage1Key stage S P A := by
  unfold authFixedExpAtStage1Key authKoskExpAtStage1Key
  apply bind_congr; intro secb
  have hsim := _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthHybridStateFixed.toAuthHybridState
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridFixedImpl1Key stage true true S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl1Key stage true true S P)
    (fun q hst => map_toAuthHybridState_fullAuthHybridFixedImpl1Key stage true true S P q hst hStage)
    A.run (AuthHybridStateFixed.empty S secb)
  dsimp only [AuthHybridStateFixed.empty] at hsim ⊢
  rw [← hsim, bind_map_left]
  rfl

noncomputable def authFixedAdvAtStage1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpAtStage1Key stage S P A].boolBias).toReal

/-- Idealised `Auth` execution branch on `AuthHybridStateFixed S` (`stage = .g5`, `checkAuth =
    false`), where every fresh session encrypts `m0` and unmatched honest-sender `recv` branches
    reject. -/
noncomputable def authFixedIdealBranch1Key (useRo : Bool) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let initSt := AuthHybridStateFixed.empty S false
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
    pqxdhAuthHybridFixedImpl1Key .g5 useRo false S P
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

noncomputable def authFixedExpG3_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage1Key .g3 S P A

noncomputable def authFixedExpG3_5_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage1Key .g3_5 S P A

noncomputable def authFixedExpG3_6_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage1Key .g3_6 S P A

noncomputable def authFixedExpG3_7_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage1Key .g3_7 S P A

noncomputable def authFixedExpG3_8_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool :=
  authFixedExpAtStage1Key .g3_8 S P A

noncomputable def authFixedExpG5_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let z ← if secb then authFixedIdealBranch1Key true S P A else authFixedIdealBranch1Key true S P A
  return (secb == z)

noncomputable def authFixedAdvG3_1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_1Key S P A].boolBias).toReal

noncomputable def authFixedAdvG3_5_1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_5_1Key S P A].boolBias).toReal

noncomputable def authFixedAdvG3_6_1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_6_1Key S P A].boolBias).toReal

noncomputable def authFixedAdvG3_7_1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_7_1Key S P A].boolBias).toReal

noncomputable def authFixedAdvG3_8_1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG3_8_1Key S P A].boolBias).toReal

noncomputable def authFixedAdvG5_1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) : ℝ :=
  (𝒟[authFixedExpG5_1Key S P A].boolBias).toReal

@[simp]
theorem authFixedAdvG5_eq_zero1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authFixedAdvG5_1Key S P A = 0 := by
  unfold authFixedAdvG5_1Key authFixedExpG5_1Key
  rw [evalDist_boolBias_bind_uniformBool, Measure.boolDist_self, ENNReal.toReal_zero]

/-- Sub-hop `G3.5 → G3.6` (`RootKdfRO`) bound statement for one-key `Auth`. -/
def AuthHopG3_5G3_6Stmt1Key (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_5_1Key S P A.1 - authFixedAdvG3_6_1Key S P A.1| ≤
        rootKdfRoTermReal S b.q_roRoot

/-- Sub-hop `G3.6 → G3.7` (`PrfChainKey`) bound statement for one-key `Auth`. -/
def AuthHopG3_6G3_7Stmt1Key (S : Setup)
    (ck : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfCkAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_6_1Key S P A.1 - authFixedAdvG3_7_1Key S P A.1| ≤
        2 * (S.N_sess_tot : ℝ) * PrfChainKeyReal P (ck b A)

/-- Sub-hop `G3.7 → G3.8` (`PrfMsgKeys`) bound statement for one-key `Auth`. -/
def AuthHopG3_7G3_8Stmt1Key (S : Setup)
    (mk : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfMsgKeysAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_7_1Key S P A.1 - authFixedAdvG3_8_1Key S P A.1| ≤
        2 * (S.N_sess_tot : ℝ) * PrfMsgKeysReal P (mk b A)

/-- Combined sub-hop `G3.8 → G5` (`AeadIndCpa` + `AeadMuIntCtxt`) bound statement for one-key `Auth`. -/
def AuthHopG3_8G5Stmt1Key (S : Setup)
    (cpa : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadIndCpaAdv)
    (int : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadMuIntCtxtAdv) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3_8_1Key S P A.1 - authFixedAdvG5_1Key S P A.1| ≤
        2 * (S.N_send_tot : ℝ) * AeadIndCpaReal P (cpa b A) +
        2 * AeadMuIntCtxt P (int b A)

/-- AEAD reductions, query bounds, and `G3.8 → G5` hop bundle for one-key `Auth`. -/
structure AuthSubHops4to5Bundle1Key (S : Setup) where
  cpa              : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadIndCpaAdv
  int              : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadMuIntCtxtAdv
  int_queries      : ∀ b A, (int b A).q_dec ≤ S.N_recv_tot
  int_enc_queries  : ∀ b A, (int b A).q_enc ≤ S.N_send_tot
  cpa_prim_queries : ∀ b A, (cpa b A).q_prim ≤ primQueryBudget S b
  int_prim_queries : ∀ b A, (int b A).q_prim ≤ primQueryBudget S b
  hop_G3_8_G5      : AuthHopG3_8G5Stmt1Key S cpa int

theorem pqxdhAuthHybridKoskImpl1Key_eq_of_ne_initPrin (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q =
      pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem pqxdhAuthHybridFixedImpl1Key_eq_of_ne_initPrin (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P q =
      pqxdhAuthHybridFixedImpl stage useRo checkAuth S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ =>
    have hK := pqxdhAuthHybridKoskImpl1Key_eq_of_ne_initPrin stage useRo checkAuth S P _ hq
    unfold pqxdhAuthHybridFixedImpl1Key pqxdhAuthHybridFixedImpl
    simp only [hK] <;> rfl

end SignalPqxdh.Security
