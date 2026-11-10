/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key Split-Stage `Auth` Hybrid Oracles (`G3.8` to `G5`)

Defines split send/receive stage `Auth` hybrid implementations (`authSplitFixedExp1Key`) over
`pqxdhAuthImpl1KeyG` and proves receive-step unfolding and `resetWonAuth` commutation lemmas.
-/

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

def pqxdhAuthHybridSplitKoskImpl1Key (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
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
  | q => liftAuthBase (pqxdhAuthImpl1KeyG useRo checkAuth S P q)
def pqxdhAuthHybridSplitFixedImpl1Key (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) := fun q => do
  let hst ← get
  if !recvStage.idealMsgKeys then
    let (resp, hst') ←
      liftM ((pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo checkAuth S P q).run
              hst.toAuthHybridState)
    let recvCount' := if isAuthRecvQuery (.inr q) then hst.recvCount + 1 else hst.recvCount
    set ({ toAuthHybridState := hst', recvCount := recvCount', mkSaltCache := hst.mkSaltCache } :
          AuthHybridStateFixed S)
    return resp
  else
    match q with
    | .recvOPK k j o msg =>
      pqxdhAuthHybridFixedImpl1Key recvStage useRo checkAuth S P (.recvOPK k j o msg)
    | .recvNoOPK k j l msg =>
      pqxdhAuthHybridFixedImpl1Key recvStage useRo checkAuth S P (.recvNoOPK k j l msg)
    | qOther =>
      let (resp, hst') ←
        liftM ((pqxdhAuthHybridKoskImpl1Key sendStage useRo checkAuth S P qOther).run
                hst.toAuthHybridState)
      let recvCount' := if isAuthRecvQuery (.inr qOther) then hst.recvCount + 1 else hst.recvCount
      set ({ toAuthHybridState := hst', recvCount := recvCount', mkSaltCache := hst.mkSaltCache } :
            AuthHybridStateFixed S)
      return resp
@[simp]
theorem pqxdhAuthHybridSplitKoskImpl_same1Key (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    pqxdhAuthHybridSplitKoskImpl1Key stage stage useRo checkAuth S P =
      pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P := rfl
@[simp]
theorem pqxdhAuthHybridSplitFixedImpl_same1Key (stage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) :
    pqxdhAuthHybridSplitFixedImpl1Key stage stage useRo checkAuth S P =
      pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P := by
  funext q; apply StateT.ext; intro hst
  unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridFixedImpl1Key
  cases stage.idealMsgKeys <;> cases q <;> simp
noncomputable def authSplitFixedExp1Key (sendStage recvStage : AuthHybridStage) (checkAuth : Bool)
    (S : Setup) (P : Primitives) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) +
    pqxdhAuthHybridSplitFixedImpl1Key sendStage recvStage true checkAuth S P
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
theorem authSplitFixedExp_same_true1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authSplitFixedExp1Key stage stage true S P A = authFixedExpAtStage1Key stage S P A := by
  unfold authSplitFixedExp1Key authFixedExpAtStage1Key
  simp [pqxdhAuthHybridSplitFixedImpl_same1Key]

theorem pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key {S : Setup}
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo checkAuth S P (.recvOPK k j o msg)).run
      hst =
      match prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
      | none => pure (.noneResp, hst)
      | some prep =>
        prep.finish <$>
          evalAuthHybridRecvSchedule recvStage useRo P prep.hstDec prep.kEntry prep.bEntry
            prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridSplitKoskImpl1Key prepareAuthHybridRecvOPK
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
theorem pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key {S : Setup}
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo checkAuth S P
      (.recvNoOPK k j l msg)).run hst =
      match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
      | none => pure (.noneResp, hst)
      | some prep =>
        prep.finish <$>
          evalAuthHybridRecvSchedule recvStage useRo P prep.hstDec prep.kEntry prep.bEntry
            prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridSplitKoskImpl1Key prepareAuthHybridRecvNoOPK
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

theorem pqxdhAuthHybridFixedImpl_recvOPK_eq1Key {S : Setup}
    (stage : AuthHybridStage) (hStage : stage.idealMsgKeys = true)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P (.recvOPK k j o msg)).run hst =
      match prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
      | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
      | some prep =>
        (fun (res?, mkSaltCache') =>
          let (resp, hst') := prep.finish res?
          (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache
                   := mkSaltCache' })) <$>
          evalAuthFixedRecvScheduleCached stage useRo P prep.hstDec hst.recvCount hst.mkSaltCache
            prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridFixedImpl1Key prepareAuthHybridRecvOPK
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
theorem pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key {S : Setup}
    (stage : AuthHybridStage) (hStage : stage.idealMsgKeys = true)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P (.recvNoOPK k j l msg)).run hst =
      match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
      | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
      | some prep =>
        (fun (res?, mkSaltCache') =>
          let (resp, hst') := prep.finish res?
          (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache
                   := mkSaltCache' })) <$>
          evalAuthFixedRecvScheduleCached stage useRo P prep.hstDec hst.recvCount hst.mkSaltCache
            prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg := by
  unfold pqxdhAuthHybridFixedImpl1Key prepareAuthHybridRecvNoOPK
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

theorem map_resetWonAuth_pqxdhAuthHybridSplitKoskImpl1Key
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S)
    (hNoWin : hst.base.hasWonAuth = false) :
    Prod.map id resetWonAuth <$>
        ((pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo checkAuth S P q).run hst) =
      (pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo false S P q).run (resetWonAuth hst)
        := by
  have hb_won : (resetWonAuth hst).base.hasWonAuth = false := rfl
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    by_cases h : bundle.opkB?.isNone = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq]
      exact evalAuthHybridSendKosk_resetWonAuth sendStage useRo S P (.sendOPK u i) u bundle m0 m1
        hst
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hNoWin, hb_won, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte]
    by_cases h : bundle.opkB?.isSome = true
    · simp [h, Prod.map]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq]
      exact evalAuthHybridSendKosk_resetWonAuth sendStage useRo S P (.sendNoOPK u i) u bundle m0 m1
        hst
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key, pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key,
      prepareAuthHybridRecvOPK_resetWonAuth checkAuth P k j o msg hst hNoWin]
    cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_resetWonAuth, Functor.map_map]
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key, pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key,
      prepareAuthHybridRecvNoOPK_resetWonAuth checkAuth P k j l msg hst hNoWin]
    cases prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
    | none => simp [Prod.map]
    | some prep =>
      simp only [Option.map, evalAuthHybridRecvSchedule_resetWonAuth, Functor.map_map]
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG
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
theorem map_resetWonAuthFixed_fullSplitFixedImpl1Key
    (sendStage recvStage : AuthHybridStage) (useRo checkAuth : Bool)
    (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false) :
    Prod.map id resetWonAuthFixed <$>
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (AuthHybridStateFixed S) ProbComp) +
          pqxdhAuthHybridSplitFixedImpl1Key sendStage recvStage useRo checkAuth S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
        pqxdhAuthHybridSplitFixedImpl1Key sendStage recvStage useRo false S P) q).run
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
        ((pqxdhAuthHybridSplitFixedImpl1Key sendStage recvStage useRo checkAuth S P kq).run hst) =
      (pqxdhAuthHybridSplitFixedImpl1Key sendStage recvStage useRo false S P kq).run
        (resetWonAuthFixed hst)
    have hto : (resetWonAuthFixed hst).toAuthHybridState = resetWonAuth hst.toAuthHybridState := rfl
    have hrc : (resetWonAuthFixed hst).recvCount = hst.recvCount := rfl
    have hmc : (resetWonAuthFixed hst).mkSaltCache = hst.mkSaltCache := rfl
    by_cases hIdeal : recvStage.idealMsgKeys = true
    · have hSend := map_resetWonAuth_pqxdhAuthHybridSplitKoskImpl1Key sendStage sendStage useRo
        checkAuth S P kq hst.toAuthHybridState hNoWin
      rw [pqxdhAuthHybridSplitKoskImpl_same1Key, pqxdhAuthHybridSplitKoskImpl_same1Key] at hSend
      cases kq with
      | recvOPK k j o msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl1Key
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvOPK_eq1Key recvStage hIdeal, hto, hrc, hmc,
          prepareAuthHybridRecvOPK_resetWonAuth checkAuth P k j o msg hst.toAuthHybridState hNoWin]
        cases prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
        | none => simp [Prod.map, resetWonAuthFixed]
        | some prep =>
          simp [Option.map, evalAuthFixedRecvScheduleCached_resetWonAuth, Functor.map_map, Prod.map,
                 resetWonAuthFixed]
      | recvNoOPK k j l msg =>
        clear hSend
        unfold pqxdhAuthHybridSplitFixedImpl1Key
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_get, pure_bind,
          pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key recvStage hIdeal, hto, hrc, hmc,
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
        unfold pqxdhAuthHybridSplitFixedImpl1Key
        simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_get,
          StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        rw [hto, hrc, hmc, ← hSend]
        simp [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
               resetWonAuthFixed]
    · have hIdealF : recvStage.idealMsgKeys = false := Bool.eq_false_iff.mpr hIdeal
      unfold pqxdhAuthHybridSplitFixedImpl1Key
      simp only [hIdealF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      have h := map_resetWonAuth_pqxdhAuthHybridSplitKoskImpl1Key sendStage recvStage useRo checkAuth S
        P kq hst.toAuthHybridState hNoWin
      rw [hto, hrc, hmc, ← h]
      simp [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map,
             resetWonAuthFixed]
