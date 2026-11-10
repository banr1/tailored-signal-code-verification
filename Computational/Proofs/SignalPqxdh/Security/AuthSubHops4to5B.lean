/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA -- shake: keep
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC -- shake: keep

@[expose] public section
set_option autoImplicit false
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators
namespace SignalPqxdh.Security
open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt
                                                  initSessionSlotIdx_sendNoOPK_lt
                                                    initSessionSlotIdx_inj_of_lt RelProbUpToBad
                                                      simulateQ_relProbUpToBad
                                                        evalDist_simulateQ_eq_of_step_or_bad)
/-!
## Split send/receive stage hybrid and `hasWonAuth` reset

Defines the split-stage `Auth` hybrid `authSplitFixedExp`, whose send and receive queries run at
independent stages, and shows that resetting `hasWonAuth` commutes with `checkAuth = false` steps.
-/
def pqxdhAuthHybridSplitKoskImpl (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridState S) ProbComp) := fun q => do
  let hst ← get
  let st := hst.base
  if checkAuth && st.hasWonAuth then
    return .noneResp
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return .noneResp
    runAuthHybridSendKosk sendStage useRo S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return .noneResp
    runAuthHybridSendKosk sendStage useRo S P (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then
      return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
      return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return .noneResp
    if oEntry.consumed then
      return .noneResp
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
      liftM (evalAuthHybridRecvSchedule recvStage useRo P hstDec kEntry bEntry (some oEntry.opkPk)
              secrets msg)
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
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
      return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
      return .noneResp
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
      liftM (evalAuthHybridRecvSchedule recvStage useRo P hstDec kEntry bEntry none secrets msg)
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
  | q => liftAuthBase (pqxdhAuthImpl useRo checkAuth S P q)
def pqxdhAuthHybridSplitFixedImpl (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) := fun q => do
  let hst ← get
  if !recvStage.idealMsgKeys then
    let (resp, hst') ←
      liftM ((pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo checkAuth S P q).run
              hst.toAuthHybridState)
    let recvCount' := if isAuthRecvQuery (.inr q) then hst.recvCount + 1 else hst.recvCount
    set ({ toAuthHybridState := hst', recvCount := recvCount', mkSaltCache := hst.mkSaltCache } :
          AuthHybridStateFixed S)
    return resp
  else
    match q with
    | .recvOPK k j o msg =>
      pqxdhAuthHybridFixedImpl recvStage useRo checkAuth S P (.recvOPK k j o msg)
    | .recvNoOPK k j l msg =>
      pqxdhAuthHybridFixedImpl recvStage useRo checkAuth S P (.recvNoOPK k j l msg)
    | qOther =>
      let (resp, hst') ←
        liftM ((pqxdhAuthHybridKoskImpl sendStage useRo checkAuth S P qOther).run
                hst.toAuthHybridState)
      let recvCount' := if isAuthRecvQuery (.inr qOther) then hst.recvCount + 1 else hst.recvCount
      set ({ toAuthHybridState := hst', recvCount := recvCount', mkSaltCache := hst.mkSaltCache } :
            AuthHybridStateFixed S)
      return resp
@[simp]
theorem pqxdhAuthHybridSplitKoskImpl_same (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    pqxdhAuthHybridSplitKoskImpl stage stage useRo checkAuth S P =
      pqxdhAuthHybridKoskImpl stage useRo checkAuth S P := rfl
@[simp]
theorem pqxdhAuthHybridSplitFixedImpl_same (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    pqxdhAuthHybridSplitFixedImpl stage stage useRo checkAuth S P =
      pqxdhAuthHybridFixedImpl stage useRo checkAuth S P := by
  funext q; apply StateT.ext; intro hst
  unfold pqxdhAuthHybridSplitFixedImpl pqxdhAuthHybridFixedImpl
  cases stage.idealMsgKeys <;> cases q <;> simp
noncomputable def authSplitFixedExp (sendStage recvStage : AuthHybridStage) (checkAuth : Bool)
    (S : Setup) (P : Primitives) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) +
    pqxdhAuthHybridSplitFixedImpl sendStage recvStage true checkAuth S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
  if hasEcPkCollisionAuth P finalSt.toAuthHybridState ||
     hasBadSigAuth finalSt.toAuthHybridState ||
     hasKemPkCollisionAuth finalSt.toAuthHybridState ||
     hasBadKemShCrAuth P finalSt.toAuthHybridState then
    $ᵗ Bool
  else if checkAuth && finalSt.toAuthHybridState.base.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == secb)
theorem authSplitFixedExp_same_true (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authSplitFixedExp stage stage true S P A = authFixedExpAtStage stage S P A := by
  unfold authSplitFixedExp authFixedExpAtStage
  simp [pqxdhAuthHybridSplitFixedImpl_same]
def resetWonAuth {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with base := { hst.base with hasWonAuth := false } }
def resetWonAuthFixed {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { hst with toAuthHybridState := resetWonAuth hst.toAuthHybridState }
@[simp]
theorem resetWonAuth_idem {S : Setup} (hst : AuthHybridState S) :
    resetWonAuth (resetWonAuth hst) = resetWonAuth hst := rfl
@[simp]
theorem resetWonAuth_empty (S : Setup) (secb : Bool) :
    resetWonAuth (AuthHybridState.empty S secb) = AuthHybridState.empty S secb := rfl
@[simp]
theorem resetWonAuthFixed_empty (S : Setup) (secb : Bool) :
    resetWonAuthFixed (AuthHybridStateFixed.empty S secb) = AuthHybridStateFixed.empty S secb := rfl
theorem finishAuthHybridRecvOPK_resetWonAuth {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes))
    (msg : PreKeyMsg) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List
                     ((Bytes × Bytes) × (Bytes × Bytes)))) :
    Prod.map id resetWonAuth
      (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec res?)
        =
    finishAuthHybridRecvOPK false P k j o kEntry bEntry oEntry usedTriples' msg
      (resetWonAuth hstDec) res? := by
  unfold finishAuthHybridRecvOPK resetWonAuth
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only [Prod.map, id_eq]
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only
      split_ifs <;> rfl
theorem finishAuthHybridRecvNoOPK_resetWonAuth {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes))
    (msg : PreKeyMsg) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List
                     ((Bytes × Bytes) × (Bytes × Bytes)))) :
    Prod.map id resetWonAuth
      (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?) =
    finishAuthHybridRecvNoOPK false P k j l kEntry bEntry usedTriples' msg (resetWonAuth hstDec)
      res? := by
  unfold finishAuthHybridRecvNoOPK resetWonAuth
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only [Prod.map, id_eq]
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only
      split_ifs <;> rfl
theorem pqxdhAuthHybridSplitKoskImpl_recvOPK_eq {S : Setup}
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo checkAuth S P (.recvOPK k j o msg)).run
      hst =
      match prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
      | none => pure (.noneResp, hst)
      | some prep =>
        prep.finish <$>
          evalAuthHybridRecvSchedule recvStage useRo P prep.hstDec prep.kEntry prep.bEntry
            prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridSplitKoskImpl prepareAuthHybridRecvOPK
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases Bool.eq_false_or_eq_true (checkAuth && hst.base.hasWonAuth) with h0 | h0
  · simp only [h0, ↓reduceIte, StateT.run_pure]
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, StateT.run_pure]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, StateT.run_pure]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => dsimp only; simp only [StateT.run_pure]
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => dsimp only; simp only [StateT.run_pure]
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => dsimp only; simp only [StateT.run_pure]
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, StateT.run_pure]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, StateT.run_pure]
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => dsimp only; simp only [StateT.run_pure]
                  | some ss =>
                    dsimp only
                    simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
                      map_eq_bind_pure_comp, bind_assoc, pure_bind]
                    congr 1; funext res?
                    cases res? with
                    | none => rfl
                    | some r =>
                      rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                      dsimp only [finishAuthHybridRecvOPK, Function.comp_apply]
                      cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                      | none =>
                        dsimp only
                        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                      | some sp =>
                        rcases sp with ⟨_, senderEntry⟩
                        dsimp only
                        split_ifs <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                                                  pure_bind]
theorem pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq {S : Setup}
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo checkAuth S P
      (.recvNoOPK k j l msg)).run hst =
      match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
      | none => pure (.noneResp, hst)
      | some prep =>
        prep.finish <$>
          evalAuthHybridRecvSchedule recvStage useRo P prep.hstDec prep.kEntry prep.bEntry
            prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridSplitKoskImpl prepareAuthHybridRecvNoOPK
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases Bool.eq_false_or_eq_true (checkAuth && hst.base.hasWonAuth) with h0 | h0
  · simp only [h0, ↓reduceIte, StateT.run_pure]
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, StateT.run_pure]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, StateT.run_pure]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => dsimp only; simp only [StateT.run_pure]
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => dsimp only; simp only [StateT.run_pure]
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                              msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h5, ↓reduceIte, StateT.run_pure]
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => dsimp only; simp only [StateT.run_pure]
              | some ss =>
                dsimp only
                simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
                  map_eq_bind_pure_comp, bind_assoc, pure_bind]
                congr 1; funext res?
                cases res? with
                | none => rfl
                | some r =>
                  rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                  dsimp only [finishAuthHybridRecvNoOPK, Function.comp_apply]
                  cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                  | none =>
                    dsimp only
                    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩
                    dsimp only
                    split_ifs <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                                              pure_bind]
theorem mem_support_fmap_iff {α β : Type} (f : α → β) (oa : ProbComp α) (b : β) :
    b ∈ support (f <$> oa) ↔ ∃ a ∈ support oa, f a = b := by
  simp [map_eq_bind_pure_comp, eq_comm]
theorem run_liftAuthBase {S : Setup} {α : Type}
    (m : StateT (AuthState S) ProbComp α) (hst : AuthHybridState S) :
    (liftAuthBase m).run hst =
      Prod.map id (fun base' => { hst with base := base' }) <$> m.run hst.base := by
  unfold liftAuthBase
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl
def evalAuthHybridSendSchedule (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (roCache : List (Bytes × DRKey))
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (isFreshPeer : Bool) (secrets dhRatchet : Bytes) :
    ProbComp (DRKey × List (Bytes × DRKey) × (Bytes × Bytes) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)) × (Bytes × Bytes)) := do
  let (drKey, roCache') ←
    if isFreshPeer && stage.idealDrKey then do
      let dk ← sampleDRKey96
      pure (dk, roCache)
    else
      evalHkdfOrRo useRo P roCache secrets
  let ((rk1, ck1_0), rootRoCache') ←
    if isFreshPeer && stage.idealRk then do
      let r ← sampleBytes32
      let c ← sampleBytes32
      pure ((r, c), rootRoCache)
    else
      evalRootKdfOrRo useRo P rootRoCache drKey.rootKey dhRatchet
  let (mkSeed, ck1_1) ←
    if isFreshPeer && stage.idealCk then do
      let ms ← sampleBytes32
      let cn ← sampleBytes32
      pure (ms, cn)
    else
      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  return (drKey, roCache', (rk1, ck1_0), rootRoCache', (mkSeed, ck1_1))
def evalAuthHybridSendKosk (stage : AuthHybridStage) (useRo : Bool)
    (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) : ProbComp (AuthResponse × AuthHybridState S) := do
  let st := hst.base
  if m0.length != m1.length then return (.noneResp, hst)
  if st.usedSendSessions.contains sid then return (.noneResp, hst)
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, hst)
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then
    return (.noneResp, hst)
  let msgPlain :=
    if isFreshPeer then
      if stage.idealFreshAead then m0 else (if st.secb then m1 else m0)
    else
      m0
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return (.noneResp, hst)
  let ekASk ← sampleScalar32
  let kemCoins ← sampleCoins32
  let ephASk ← sampleScalar32
  let spqrCoins ← sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, hst)
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return (.noneResp, hst)
  let ekAPk := P.x25519Base ekASk
  let (_spkHon, _opkHon, pqspkHon) :=
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let (drKey, roCache', (rk1, ck1_0), rootRoCache', (mkSeed, ck1_1)) ←
    evalAuthHybridSendSchedule stage useRo P st.roCache st.rootRoCache isIdealSend secrets dhRatchet
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return (.noneResp, hst)
  let deriveMessageKeys ←
    (if isIdealSend && stage.idealMsgKeys then
      sampleMessageKeys80
    else
      pure (P.deriveMsgKeys mkSeed spqrSalt?))
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  return finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst
theorem runAuthHybridSendKosk_eq (stage : AuthHybridStage) (useRo : Bool)
    (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) :
    (runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst =
      evalAuthHybridSendKosk stage useRo S P sid u bundle m0 m1 hst := by
  unfold runAuthHybridSendKosk evalAuthHybridSendKosk evalAuthHybridSendSchedule
    finishAuthHybridSend
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, StateT.run_pure]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => dsimp only; simp only [StateT.run_pure]
      | some up =>
        rcases up with ⟨_, uEntry⟩
        cases findHonestPrincipal P hst.base.principals bundle.ikB with
        | none =>
          dsimp only
          simp only [Option.isSome, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]
          by_cases h3 : (m0 != m1) = true
          · simp only [h3, ↓reduceIte, StateT.run_pure]
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            by_cases h4 : (!koskBundleOk P hst.base.principals hst.base.spkBundles
                             hst.base.opkEntries hst.base.advKeys bundle) = true
            · simp only [h4, ↓reduceIte, StateT.run_pure]
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]
              simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                (encodeEC bundle.spkB) bundle.spkSig &&
                               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [h5, ↓reduceIte, StateT.run_pure]
              · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => dsimp only; simp only [StateT.run_pure]
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
                  congr 1; funext ⟨drKey, roCache'⟩
                  congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => dsimp only; simp only [StateT.run_pure]
                  | some pqr =>
                    rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    dsimp only
                    simp only [StateT.run_bind, StateT.run_set, pure_bind]
                    rfl
        | some pp =>
          rcases pp with ⟨_, pEntry⟩
          dsimp only
          by_cases hcorr : pEntry.corrupted = true
          · simp only [hcorr, Option.isSome, Bool.not_true, Bool.not_false, Bool.true_and,
                        Bool.false_or]
            by_cases h3 : (m0 != m1) = true
            · simp only [h3, ↓reduceIte, StateT.run_pure]
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              by_cases h4 : (!koskBundleOk P hst.base.principals hst.base.spkBundles
                               hst.base.opkEntries hst.base.advKeys bundle) = true
              · simp only [h4, ↓reduceIte, StateT.run_pure]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
                congr 1; funext ekASk; congr 1; funext kemCoins
                congr 1; funext ephASk; congr 1; funext spqrCoins
                by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                  (encodeEC bundle.spkB) bundle.spkSig &&
                                 P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                  (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
                · simp only [h5, ↓reduceIte, StateT.run_pure]
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemEncaps bundle.pqspkB kemCoins with
                  | none => dsimp only; simp only [StateT.run_pure]
                  | some sc =>
                    rcases sc with ⟨ss, kemCt⟩
                    dsimp only
                    generalize (checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles
                                 bundle &&
                      (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
                        hst.base.opkEntries bundle).2.2) = isIdealSend
                    cases isIdealSend <;> cases stage <;>
                    { try dsimp only
                      simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
                        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
                        Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                        StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
                      repeat (first
                        | (cases P.spqrInitSend _ spqrCoins with
                           | none => dsimp only; simp only [StateT.run_pure]
                           | some pqr =>
                             rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                             dsimp only
                             simp [StateT.run_bind, StateT.run_monadLift, StateT.run_pure,
                               StateT.run_set, map_eq_bind_pure_comp, bind_assoc, pure_bind,
                               Function.comp_apply])
                        | (congr 1; funext _)) }
          · have hcorr_f : pEntry.corrupted = false := Bool.eq_false_iff.mpr hcorr
            simp only [hcorr_f, Bool.not_false, Bool.not_true, Bool.false_and, Bool.false_eq_true,
                        ↓reduceIte]
            by_cases h4 : (!koskBundleOk P hst.base.principals hst.base.spkBundles
                             hst.base.opkEntries hst.base.advKeys bundle) = true
            · simp only [h4, ↓reduceIte, StateT.run_pure]
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]
              simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                (encodeEC bundle.spkB) bundle.spkSig &&
                               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [h5, ↓reduceIte, StateT.run_pure]
              · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => dsimp only; simp only [StateT.run_pure]
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩
                  cases stage <;>
                  { dsimp only
                    simp only [Option.isSome, Bool.true_or,
                      AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
                      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
                      Bool.true_and, Bool.false_eq_true, ↓reduceIte,
                      StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
                    repeat (first
                      | (cases P.spqrInitSend _ spqrCoins with
                         | none => dsimp only; simp only [StateT.run_pure]
                         | some pqr =>
                           rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                           dsimp only
                           simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_pure,
                             StateT.run_set, bind_assoc, pure_bind]
                           try congr 1
                           try simp only [hcorr_f, Option.isSome, Bool.not_false, Bool.true_or,
                             StateT.run_bind, StateT.run_monadLift, StateT.run_pure,
                             StateT.run_set, map_eq_bind_pure_comp, bind_assoc, pure_bind,
                             Function.comp_apply, ↓reduceIte]
                           try rfl)
                      | (congr 1; funext _)) }
theorem evalAuthHybridSendKosk_resetWonAuth (stage : AuthHybridStage) (useRo : Bool)
    (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) :
    Prod.map id resetWonAuth <$>
        evalAuthHybridSendKosk stage useRo S P sid u bundle m0 m1 hst =
      evalAuthHybridSendKosk stage useRo S P sid u bundle m0 m1 (resetWonAuth hst) := by
  unfold evalAuthHybridSendKosk
  have hb_used : (resetWonAuth hst).base.usedSendSessions = hst.base.usedSendSessions := rfl
  have hb_princ : (resetWonAuth hst).base.principals = hst.base.principals := rfl
  have hb_spk : (resetWonAuth hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_opk : (resetWonAuth hst).base.opkEntries = hst.base.opkEntries := rfl
  have hb_adv : (resetWonAuth hst).base.advKeys = hst.base.advKeys := rfl
  have hb_ro : (resetWonAuth hst).base.roCache = hst.base.roCache := rfl
  have hb_rro : (resetWonAuth hst).base.rootRoCache = hst.base.rootRoCache := rfl
  have hb_secb : (resetWonAuth hst).base.secb = hst.base.secb := rfl
  dsimp only
  rw [hb_used, hb_princ, hb_spk, hb_opk, hb_adv, hb_ro, hb_rro, hb_secb]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, map_pure]; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, map_pure]; rfl
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp only [map_pure]; rfl
      | some up =>
        rcases up with ⟨_, uEntry⟩
        dsimp only
        by_cases h3 : (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
                         | some (_, pEntry) => !pEntry.corrupted
                         | none => false) && (m0 != m1)) = true
        · simp only [h3, ↓reduceIte, map_pure]; rfl
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (!koskBundleOk P hst.base.principals hst.base.spkBundles
                           hst.base.opkEntries hst.base.advKeys bundle) = true
          · simp only [h4, ↓reduceIte, map_pure]; rfl
          · simp only [h4, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp,
              bind_assoc]
            congr 1; funext ekASk; congr 1; funext kemCoins
            congr 1; funext ephASk; congr 1; funext spqrCoins
            by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                              (encodeEC bundle.spkB) bundle.spkSig &&
                             P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h5, ↓reduceIte, pure_bind]; rfl
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => dsimp only; simp only [pure_bind]; rfl
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩
                dsimp only
                simp only [bind_assoc]
                congr 1; funext ⟨drKey, roCache', ⟨rk1, ck1_0⟩, rootRoCache', ⟨mkSeed, ck1_1⟩⟩
                cases P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => dsimp only; simp only [pure_bind]; rfl
                | some pqr =>
                  rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  dsimp only
                  simp only [bind_assoc]
                  congr 1
theorem prepareAuthHybridRecvOPK_resetWonAuth {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hNoWin : hst.base.hasWonAuth = false) :
    prepareAuthHybridRecvOPK false P k j o msg (resetWonAuth hst) =
      (prepareAuthHybridRecvOPK checkAuth P k j o msg hst).map (fun prep =>
        { prep with
          hstDec := resetWonAuth prep.hstDec
          finish := fun res? => Prod.map id resetWonAuth (prep.finish res?) }) := by
  unfold prepareAuthHybridRecvOPK
  have hb_won : (resetWonAuth hst).base.hasWonAuth = false := rfl
  have hb_used : (resetWonAuth hst).base.usedRecvOPK = hst.base.usedRecvOPK := rfl
  have hb_princ : (resetWonAuth hst).base.principals = hst.base.principals := rfl
  have hb_adv : (resetWonAuth hst).base.advKeys = hst.base.advKeys := rfl
  have hb_spk : (resetWonAuth hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_opk : (resetWonAuth hst).base.opkEntries = hst.base.opkEntries := rfl
  have hb_kyber : (resetWonAuth hst).base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := rfl
  have hb_rec : (resetWonAuth hst).recvKemRecs = hst.recvKemRecs := rfl
  have hb_ideal : (resetWonAuth hst).idealSessions = hst.idealSessions := rfl
  dsimp only
  rw [hb_won, hNoWin, hb_used, hb_princ, hb_adv, hb_spk, hb_opk, hb_kyber, hb_rec, hb_ideal]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, Option.map]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, Option.map]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, Option.map]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => rfl
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, Option.map]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, Option.map]
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => rfl
                  | some ss =>
                    dsimp only [Option.map]
                    congr 1; congr 1
                    funext res?
                    exact (finishAuthHybridRecvOPK_resetWonAuth checkAuth P k j o kEntry bEntry
                            oEntry
                      (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).2
                      msg { hst with recvKemRecs := { k := k.val, j := j.val, pqspkPk
                                                      := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
                                                        kemCt := msg.hdr.kemCt, kemSs := ss }
                                                          :: hst.recvKemRecs } res?).symm
theorem prepareAuthHybridRecvNoOPK_resetWonAuth {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hNoWin : hst.base.hasWonAuth = false) :
    prepareAuthHybridRecvNoOPK false P k j l msg (resetWonAuth hst) =
      (prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst).map (fun prep =>
        { prep with
          hstDec := resetWonAuth prep.hstDec
          finish := fun res? => Prod.map id resetWonAuth (prep.finish res?) }) := by
  unfold prepareAuthHybridRecvNoOPK
  have hb_won : (resetWonAuth hst).base.hasWonAuth = false := rfl
  have hb_used : (resetWonAuth hst).base.usedRecvNoOPK = hst.base.usedRecvNoOPK := rfl
  have hb_princ : (resetWonAuth hst).base.principals = hst.base.principals := rfl
  have hb_adv : (resetWonAuth hst).base.advKeys = hst.base.advKeys := rfl
  have hb_spk : (resetWonAuth hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_kyber : (resetWonAuth hst).base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := rfl
  have hb_rec : (resetWonAuth hst).recvKemRecs = hst.recvKemRecs := rfl
  have hb_ideal : (resetWonAuth hst).idealSessions = hst.idealSessions := rfl
  dsimp only
  rw [hb_won, hNoWin, hb_used, hb_princ, hb_adv, hb_spk, hb_kyber, hb_rec, hb_ideal]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, Option.map]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, Option.map]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, Option.map]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                              msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h5, ↓reduceIte, Option.map]
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => rfl
              | some ss =>
                dsimp only [Option.map]
                congr 1; congr 1
                funext res?
                exact (finishAuthHybridRecvNoOPK_resetWonAuth checkAuth P k j l kEntry bEntry
                  (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                    msg.hdr.spkId msg.hdr.ekAPk).2
                  msg { hst with recvKemRecs := { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                                                  pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt,
                                                    kemSs := ss } :: hst.recvKemRecs } res?).symm
theorem pqxdhAuthHybridFixedImpl_recvOPK_eq {S : Setup}
    (stage : AuthHybridStage) (hStage : stage.idealMsgKeys = true)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl stage useRo checkAuth S P (.recvOPK k j o msg)).run hst =
      match prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
      | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
      | some prep =>
        (fun (res?, mkSaltCache') =>
          let (resp, hst') := prep.finish res?
          (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache
                   := mkSaltCache' })) <$>
          evalAuthFixedRecvScheduleCached stage useRo P prep.hstDec hst.recvCount hst.mkSaltCache
            prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridFixedImpl prepareAuthHybridRecvOPK
  simp only [hStage, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
              pure_bind]
  rcases Bool.eq_false_or_eq_true (checkAuth && hst.toAuthHybridState.base.hasWonAuth) with h0 | h0
  · simp only [h0, ↓reduceIte]; rfl
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte]; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.toAuthHybridState.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte]; rfl
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
                      hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte]; rfl
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
            with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hst.toAuthHybridState.base.opkEntries.find?
              (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => rfl
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte]; rfl
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
                                  k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte]; rfl
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => rfl
                  | some ss =>
                    dsimp only
                    simp only [StateT.run_bind, StateT.run_monadLift,
                      map_eq_bind_pure_comp, bind_assoc, pure_bind]
                    congr 1; funext ⟨res?, mkSaltCache'⟩
                    cases res? with
                    | none => rfl
                    | some r =>
                      rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                      dsimp only [finishAuthHybridRecvOPK, Function.comp_apply]
                      cases findHonestPrincipal P hst.toAuthHybridState.base.principals
                        msg.hdr.ikAPk with
                      | none => rfl
                      | some sp =>
                        rcases sp with ⟨_, senderEntry⟩
                        dsimp only
                        split_ifs <;> rfl
theorem pqxdhAuthHybridFixedImpl_recvNoOPK_eq {S : Setup}
    (stage : AuthHybridStage) (hStage : stage.idealMsgKeys = true)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl stage useRo checkAuth S P (.recvNoOPK k j l msg)).run hst =
      match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
      | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
      | some prep =>
        (fun (res?, mkSaltCache') =>
          let (resp, hst') := prep.finish res?
          (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache
                   := mkSaltCache' })) <$>
          evalAuthFixedRecvScheduleCached stage useRo P prep.hstDec hst.recvCount hst.mkSaltCache
            prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridFixedImpl prepareAuthHybridRecvNoOPK
  simp only [hStage, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
              pure_bind]
  rcases Bool.eq_false_or_eq_true (checkAuth && hst.toAuthHybridState.base.hasWonAuth) with h0 | h0
  · simp only [h0, ↓reduceIte]; rfl
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte]; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.toAuthHybridState.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte]; rfl
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
                      hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte]; rfl
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
            with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
                              msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h5, ↓reduceIte]; rfl
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => rfl
              | some ss =>
                dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift,
                  map_eq_bind_pure_comp, bind_assoc, pure_bind]
                congr 1; funext ⟨res?, mkSaltCache'⟩
                cases res? with
                | none => rfl
                | some r =>
                  rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                  dsimp only [finishAuthHybridRecvNoOPK, Function.comp_apply]
                  cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk
                    with
                  | none => rfl
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩
                    dsimp only
                    split_ifs <;> rfl
theorem evalAuthHybridRecvSchedule_resetWonAuth {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthHybridRecvSchedule stage useRo P (resetWonAuth hst) kEntry bEntry opkPk? secrets msg =
      evalAuthHybridRecvSchedule stage useRo P hst kEntry bEntry opkPk? secrets msg := rfl
theorem evalAuthFixedRecvScheduleCached_resetWonAuth {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    evalAuthFixedRecvScheduleCached stage useRo P (resetWonAuth hst) recvCount mkSaltCache
      kEntry bEntry opkPk? secrets msg =
      evalAuthFixedRecvScheduleCached stage useRo P hst recvCount mkSaltCache
        kEntry bEntry opkPk? secrets msg := rfl
theorem map_resetWonAuth_pqxdhAuthHybridSplitKoskImpl
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S)
    (hNoWin : hst.base.hasWonAuth = false) :
    Prod.map id resetWonAuth <$>
        ((pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo checkAuth S P q).run hst) =
      (pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo false S P q).run (resetWonAuth hst)
        := by
  have hb_won : (resetWonAuth hst).base.hasWonAuth = false := rfl
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    by_cases h : bundle.opkB?.isNone = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq]
      exact evalAuthHybridSendKosk_resetWonAuth sendStage useRo S P (.sendOPK u i) u bundle m0 m1
        hst
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    by_cases h : bundle.opkB?.isSome = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq]
      exact evalAuthHybridSendKosk_resetWonAuth sendStage useRo S P (.sendNoOPK u i) u bundle m0 m1
        hst
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq, pqxdhAuthHybridSplitKoskImpl_recvOPK_eq,
      prepareAuthHybridRecvOPK_resetWonAuth checkAuth P k j o msg hst hNoWin]
    cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_resetWonAuth, Functor.map_map]
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq, pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq,
      prepareAuthHybridRecvNoOPK_resetWonAuth checkAuth P k j l msg hst hNoWin]
    cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_resetWonAuth, Functor.map_map]
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb : (resetWonAuth hst).base.principals = hst.base.principals := rfl
    rw [hb]
    by_cases h : (hst.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | corruptIK u =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb : (resetWonAuth hst).base.principals = hst.base.principals := rfl
    rw [hb]
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [Prod.map]
    | some up =>
      rcases up with ⟨_, pEntry⟩
      simp [StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | genSPK u j =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb1 : (resetWonAuth hst).base.principals = hst.base.principals := rfl
    have hb2 : (resetWonAuth hst).base.spkBundles = hst.base.spkBundles := rfl
    rw [hb1, hb2]
    by_cases h : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [Prod.map]
      | some up =>
        rcases up with ⟨_, pEntry⟩
        simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | genOPK u j o =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb : (resetWonAuth hst).base.opkEntries = hst.base.opkEntries := rfl
    rw [hb]
    by_cases h : (hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | registerKey sk =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb : (resetWonAuth hst).base.advKeys = hst.base.advKeys := rfl
    rw [hb]
    cases registerAdvKey P hst.base.advKeys sk with
    | none => simp [Prod.map]
    | some kp =>
      rcases kp with ⟨pk, advKeys'⟩
      simp [StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | roQuery secrets =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb : (resetWonAuth hst).base.roCache = hst.base.roCache := rfl
    rw [hb]
    by_cases h : (!useRo) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | roRootQuery rk dh =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won]
    have hb : (resetWonAuth hst).base.rootRoCache = hst.base.rootRoCache := rfl
    rw [hb]
    by_cases h : (!useRo) = true
    · simp [h, Prod.map]
    · simp [h, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, resetWonAuth]
  | revealDhSecrets =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    rw [run_liftAuthBase, run_liftAuthBase]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hb1 : (resetWonAuth hst).base.principals = hst.base.principals := rfl
    have hb2 : (resetWonAuth hst).base.spkBundles = hst.base.spkBundles := rfl
    have hb3 : (resetWonAuth hst).base.opkEntries = hst.base.opkEntries := rfl
    have hb4 : (resetWonAuth hst).base.sessions = hst.base.sessions := rfl
    rw [hb1, hb2, hb3, hb4]
    by_cases h : useRo = true <;> simp [h, Prod.map, resetWonAuth]
theorem map_resetWonAuthFixed_fullSplitFixedImpl
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false) :
    Prod.map id resetWonAuthFixed <$>
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (AuthHybridStateFixed S) ProbComp) +
          pqxdhAuthHybridSplitFixedImpl sendStage recvStage useRo checkAuth S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
        pqxdhAuthHybridSplitFixedImpl sendStage recvStage useRo false S P) q).run
        (resetWonAuthFixed hst) := by
  cases q with
  | inl uq =>
    change Prod.map id resetWonAuthFixed <$>
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp)
           uq).run hst) =
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp)
        uq).run
        (resetWonAuthFixed hst)
    simp [QueryImpl.liftTarget, StateT.run_monadLift, map_eq_bind_pure_comp, Prod.map]
  | inr kq =>
    change Prod.map id resetWonAuthFixed <$>
        ((pqxdhAuthHybridSplitFixedImpl sendStage recvStage useRo checkAuth S P kq).run hst) =
      (pqxdhAuthHybridSplitFixedImpl sendStage recvStage useRo false S P kq).run
        (resetWonAuthFixed hst)
    have hto : (resetWonAuthFixed hst).toAuthHybridState = resetWonAuth hst.toAuthHybridState := rfl
    have hrc : (resetWonAuthFixed hst).recvCount = hst.recvCount := rfl
    have hmc : (resetWonAuthFixed hst).mkSaltCache = hst.mkSaltCache := rfl
    by_cases hIdeal : recvStage.idealMsgKeys = true
    · have hSend := map_resetWonAuth_pqxdhAuthHybridSplitKoskImpl sendStage sendStage useRo
        checkAuth S P kq hst.toAuthHybridState hNoWin
      rw [pqxdhAuthHybridSplitKoskImpl_same, pqxdhAuthHybridSplitKoskImpl_same] at hSend
      cases kq with
      | recvOPK k j o msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvOPK_eq recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvOPK_resetWonAuth checkAuth P k j o msg hst.toAuthHybridState hNoWin]
        cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
        | none => simp [Prod.map, resetWonAuthFixed]
        | some prep =>
          simp [Option.map, evalAuthFixedRecvScheduleCached_resetWonAuth, Functor.map_map, Prod.map,
                 resetWonAuthFixed]
      | recvNoOPK k j l msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvNoOPK_eq recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvNoOPK_resetWonAuth checkAuth P k j l msg hst.toAuthHybridState
            hNoWin]
        cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
        | none => simp [Prod.map, resetWonAuthFixed]
        | some prep =>
          simp [Option.map, evalAuthFixedRecvScheduleCached_resetWonAuth, Functor.map_map, Prod.map,
                 resetWonAuthFixed]
      | sendOPK u i bundle m0 m1 | sendNoOPK u i bundle m0 m1 | initPrin u | corruptIK u
      | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets | roRootQuery rk dh
      | revealDhSecrets =>
        unfold pqxdhAuthHybridSplitFixedImpl
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_get,
          StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        rw [hto, hrc, hmc, ← hSend]
        simp [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
               resetWonAuthFixed]
    · have hIdealF : recvStage.idealMsgKeys = false := Bool.eq_false_iff.mpr hIdeal
      unfold pqxdhAuthHybridSplitFixedImpl
      simp only [hIdealF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      have h := map_resetWonAuth_pqxdhAuthHybridSplitKoskImpl sendStage recvStage useRo checkAuth S
        P kq hst.toAuthHybridState hNoWin
      rw [hto, hrc, hmc, ← h]
      simp [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
             resetWonAuthFixed]
