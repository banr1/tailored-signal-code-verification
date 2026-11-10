/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingB
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` `G3 -> G3.5` Receive Step Couplings

Receive step unfoldings and `RelProbUpToBad` step couplings for `.recvOPK` and `.recvNoOPK` on
`pqxdhAuthAdvLatchedStageImpl1Key`.
-/

@[expose] public section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

theorem pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key stage S P (.recvOPK k j o msg)).run s =
      match parseAuthRecvOPKPre P k j o msg s.hyb.base with
      | none => pure (wrapAuthAdvLatchedRecv k j msg s (.noneResp, s.hyb))
      | some (kEntry, bEntry, oEntry, usedTriples', ss) =>
        let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
          k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
          pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
        let hstDec := { s.hyb with recvKemRecs := rRec :: s.hyb.recvKemRecs }
        let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
        let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
        evalAuthHybridRecvSchedule stage true P hstDec kEntry bEntry
            (some oEntry.opkPk) secrets msg >>= fun res? =>
          pure (finishLatchedRecvOPK P k j o kEntry bEntry oEntry
            usedTriples' msg s hstDec res?) := by
  unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key
    parseAuthRecvOPKPre finishLatchedRecvOPK wrapAuthAdvLatchedRecv
    recvHandshakeSecrets AuthAdvLatchedState.hyb
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hWon h1 h2 h3 h5
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        cases s.adv.hyb.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => simp [StateT.run_pure]
        | some po =>
          rcases po with ⟨_, oEntry⟩
          dsimp only; split_ifs <;> simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        cases s.adv.hyb.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => simp [StateT.run_pure]
        | some po =>
          rcases po with ⟨_, oEntry⟩
          dsimp (config := { zetaHave := true }) only
          split_ifs with h4
          · simp [StateT.run_pure]
          · cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => simp [StateT.run_pure]
            | some ss =>
              simp only [Bool.true_and] at hWon
              simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
                monadLift_self, pure_bind, bind_assoc]
              congr 1
              funext res?
              cases res? with
              | none => simp [finishAuthHybridRecvOPK, StateT.run_pure]
              | some r =>
                rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                dsimp only [finishAuthHybridRecvOPK]
                rcases findHonestPrincipal P s.adv.hyb.base.principals msg.hdr.ikAPk with
                  _ | ⟨_, senderEntry⟩
                · simp [StateT.run_set, hWon]
                · dsimp only
                  split_ifs <;> simp [StateT.run_set, hWon]

theorem pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key stage S P (.recvNoOPK k j l msg)).run s =
      match parseAuthRecvNoOPKPre P k j l msg s.hyb.base with
      | none => pure (wrapAuthAdvLatchedRecv k j msg s (.noneResp, s.hyb))
      | some (kEntry, bEntry, usedTriples', ss) =>
        let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
          k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
          pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
        let hstDec := { s.hyb with recvKemRecs := rRec :: s.hyb.recvKemRecs }
        let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
        evalAuthHybridRecvSchedule stage true P hstDec kEntry bEntry none secrets msg >>=
          fun res? =>
            pure (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec res?) := by
  unfold pqxdhAuthAdvLatchedStageImpl1Key pqxdhAuthAdvStageImpl1Key pqxdhAuthHybridKoskImpl1Key
    parseAuthRecvNoOPKPre finishLatchedRecvNoOPK wrapAuthAdvLatchedRecv
    recvHandshakeSecrets AuthAdvLatchedState.hyb
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hWon h1 h2 h3 h4
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        dsimp (config := { zetaHave := true }) only
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => simp [StateT.run_pure]
        | some ss =>
          simp only [Bool.true_and] at hWon
          simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
            monadLift_self, pure_bind, bind_assoc]
          congr 1
          funext res?
          cases res? with
          | none => simp [finishAuthHybridRecvNoOPK, StateT.run_pure]
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
            dsimp only [finishAuthHybridRecvNoOPK]
            rcases findHonestPrincipal P s.adv.hyb.base.principals msg.hdr.ikAPk with
              _ | ⟨_, senderEntry⟩
            · simp [StateT.run_set, hWon]
            · dsimp only
              split_ifs <;> simp [StateT.run_set, hWon]

theorem fgAuthStepCoupling_cutoff_latched_recvOPK1Key {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s35 s3 : AuthAdvLatchedState S) (_hInv : Inv s35 s3) (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hRunInv : ValidAuthHybridRunInv S P s3.hyb) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRej : parseAuthRecvOPKPre P k j o msg s3.hyb.base = none →
      Inv (wrapAuthAdvLatchedRecv k j msg s35 (.noneResp, s35.hyb)).2
          (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2 ∨
      badAuthFgAnyLatchedMono P maxRo
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.toFg = true)
    (hSchedNone : ∀ kEntry bEntry oEntry usedTriples' ss,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      isAuthG3Abort P hstDec = false →
      Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
            s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) none).2
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec none).2 ∨
      badAuthFgAnyLatchedMono P maxRo
        (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
          s3 hstDec none).2.toFg = true) (hSubA : ∀ kEntry bEntry oEntry usedTriples' ss s,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk msg.hdr) = some s →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (secrets, s.drKey) ∧
      ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
          support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache
            kEntry bEntry msg s.drKey) →
        Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
              s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
              (some (s.drKey, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
            (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
              (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
        badAuthFgAnyLatchedMono P maxRo
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
            (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)
    (hSubB : ∀ kEntry bEntry oEntry usedTriples' ss, parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk msg.hdr) = none →
      (match findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none             => false) = false → ((∃ sec35 sec3 dk,
          s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec35, dk) ∧
          s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec3, dk) ∧
          ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                  (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) ∨
       (s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
            some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)))
    (hSubC : ∀ kEntry bEntry oEntry usedTriples' ss u_r senderEntry,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk msg.hdr) = none →
      findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk = some (u_r, senderEntry) →
      (!senderEntry.corrupted) = true →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
      ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
          some (rk1, ck1_1, pt, rootRoCache') ∈
            support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
          let recvEv : RecvdOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          (consumeMatchingSentOPK P recvEv s3.hyb.base.sentOPKEvents).1 = false →
          Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
                s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
              (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
          badAuthFgAnyLatchedMono P maxRo
            (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
              (some (dk, rk1, ck1_1, pt,
                (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.recvOPK k j o msg)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.recvOPK k j o msg)).run s3) := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq1Key, pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq1Key]
  have hBase35 : s35.hyb.base = withAuthBaseRoCache s35.hyb.base.roCache s3.hyb.base := by
    conv_lhs => rw [hAg]
    rfl
  have hPreEq : parseAuthRecvOPKPre P k j o msg s35.hyb.base =
      parseAuthRecvOPKPre P k j o msg s3.hyb.base := by
    rw [hBase35, parseAuthRecvOPKPre_withAuthBaseRoCache]
  rw [hPreEq]
  cases hPre : parseAuthRecvOPKPre P k j o msg s3.hyb.base with
  | none =>
    rcases hRej hPre with hInv' | hBad'
    · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv'⟩)
    · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
        rw [mem_support_pure_iff] at hy; subst hy; exact hBad')
  | some p =>
    rcases p with ⟨kEntry, bEntry, oEntry, usedTriples', ss⟩
    dsimp only
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec3 := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    have hDecEq : ({
        base := s35.hyb.base, initKemRecs := s35.hyb.initKemRecs,
        recvKemRecs := rRec :: s35.hyb.recvKemRecs,
        idealSessions := s35.hyb.idealSessions } : AuthHybridState S) =
        withAuthHybRoCache s35.hyb.base.roCache hstDec3 := by
      change { s35.hyb with recvKemRecs := rRec :: s35.hyb.recvKemRecs } = _
      conv_lhs => rw [hAg]
      rfl
    by_cases hAbDec : isAuthG3Abort P hstDec3 = true
    · refine RelProbUpToBad.of_support_rel _ _ (fun y35 hy35 y3 hy3 _ => ?_)
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy35 hy3
      rcases hy35 with ⟨res35, _, rfl⟩
      rcases hy3 with ⟨res3, _, rfl⟩
      refine Or.inr ?_
      rw [isAuthG3Abort_finishLatchedRecvOPK, isAuthG3Abort_finishLatchedRecvOPK,
          hDecEq, isAuthG3Abort_withBaseRoCache]
      exact ⟨hAbDec, hAbDec⟩
    · have hAbDecF : isAuthG3Abort P hstDec3 = false := Bool.eq_false_iff.mpr hAbDec
      rw [hDecEq]
      refine relProbUpToBad_evalAuthHybridRecvSchedule_bind _ _ P
        (withAuthHybRoCache s35.hyb.base.roCache hstDec3) hstDec3 kEntry bEntry
        (some oEntry.opkPk) _ msg _ _ rfl rfl rfl ?_ ?_ ?_ ?_
      · rcases hSchedNone kEntry bEntry oEntry usedTriples' ss hPre hAbDecF with hI | hB
        · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro s hMatch
        rcases hSubA kEntry bEntry oEntry usedTriples' ss s hPre hAbDecF hMatch with
          ⟨hRoFind, hPostA⟩
        refine ⟨hRoFind, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
        rcases hPostA rk1 ck1_1 pt rootRoCache' hCore with hI | hB
        · have hFst := congrArg Prod.fst
            (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
              usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
              s3 hstDec3 s.drKey rk1 ck1_1 pt rootRoCache')
          rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hNotHon
        rcases hSubB kEntry bEntry oEntry usedTriples' ss hPre hAbDecF hMatchNone hNotHon with
          ⟨sec35, sec3, dk, hF35, hF3, hHit⟩ | ⟨hF35, hF3, hMiss⟩
        · left
          refine ⟨sec35, sec3, dk, hF35, hF3, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hHit rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
                usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
        · right
          refine ⟨hF35, hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hMiss dk hdk rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
                usedTriples' msg s35.adv.hyb.base.roCache
                ((recvHandshakeSecrets P kEntry bEntry
                  (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss msg.hdr, dk) ::
                    s35.hyb.base.roCache)
                ((recvHandshakeSecrets P kEntry bEntry
                  (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss msg.hdr, dk) ::
                    s3.hyb.base.roCache)
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hHon
        rcases hFp : findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
          _ | ⟨u_r, senderEntry⟩
        · rw [hFp] at hHon; nomatch hHon
        · rw [hFp] at hHon; dsimp only at hHon
          rcases hSubC kEntry bEntry oEntry usedTriples' ss u_r senderEntry
              hPre hAbDecF hMatchNone hFp hHon with ⟨hF3, hPostC⟩
          refine ⟨hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          let recvEv : RecvdOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          cases hCons : (consumeMatchingSentOPK P recvEv s3.hyb.base.sentOPKEvents).1
          · rcases hPostC dk hdk rk1 ck1_1 pt rootRoCache' hCore hCons with hI | hB
            · have hFst := congrArg Prod.fst
                (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
                  usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache
                  ((recvHandshakeSecrets P kEntry bEntry
                    (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss msg.hdr, dk) ::
                      s3.hyb.base.roCache)
                  s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
              rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
            · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
                rw [mem_support_pure_iff] at hy; subst hy; exact hB)
          · exfalso
            rcases parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre with
              ⟨_, _, _, _, _, _, hkMem, hbMem, _, _⟩
            rcases consumeMatchingSentOPK_true_imp_abort_or_badLatchedMono_of_matched_none P hP
                maxRo s3 hRunInv hMatchNone hkMem hbMem
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hFp hHon hCons with hAb | hBad
            · rw [hAbF] at hAb; nomatch hAb
            · rw [hbF] at hBad; nomatch hBad

theorem fgAuthStepCoupling_cutoff_latched_recvNoOPK1Key {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (s35 s3 : AuthAdvLatchedState S) (_hInv : Inv s35 s3) (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hRunInv : ValidAuthHybridRunInv S P s3.hyb) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRej : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base = none →
      Inv (wrapAuthAdvLatchedRecv k j msg s35 (.noneResp, s35.hyb)).2
          (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2 ∨
      badAuthFgAnyLatchedMono P maxRo
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.toFg = true)
    (hSchedNone : ∀ kEntry bEntry usedTriples' ss, parseAuthRecvNoOPKPre P k j l msg s3.hyb.base =
        some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      isAuthG3Abort P hstDec = false →
      Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
            s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) none).2
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec none).2 ∨
      badAuthFgAnyLatchedMono P maxRo (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
          s3 hstDec none).2.toFg = true) (hSubA : ∀ kEntry bEntry usedTriples' ss s,
      parseAuthRecvNoOPKPre P k j l msg s3.hyb.base = some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none
          bEntry.pqspkPk msg.hdr) = some s →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (secrets, s.drKey) ∧
      ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
          support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache
            kEntry bEntry msg s.drKey) →
        Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
              s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
              (some (s.drKey, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
            (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
              (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
        badAuthFgAnyLatchedMono P maxRo
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
            (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)
    (hSubB : ∀ kEntry bEntry usedTriples' ss, parseAuthRecvNoOPKPre P k j l msg s3.hyb.base =
        some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr) = none →
      (match findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none             => false) = false → ((∃ sec35 sec3 dk,
          s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec35, dk) ∧
          s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec3, dk) ∧
          ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                  (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) ∨
       (s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
            some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)))
    (hSubC : ∀ kEntry bEntry usedTriples' ss u_r senderEntry,
      parseAuthRecvNoOPKPre P k j l msg s3.hyb.base = some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr) = none →
      findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk = some (u_r, senderEntry) →
      (!senderEntry.corrupted) = true →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
      ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
          some (rk1, ck1_1, pt, rootRoCache') ∈
            support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
          let recvEv : RecvdNoOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          (consumeMatchingSentNoOPK P recvEv s3.hyb.base.sentNoOPKEvents).1 = false →
          Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
                s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
              (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
          badAuthFgAnyLatchedMono P maxRo
            (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
              (some (dk, rk1, ck1_1, pt,
                (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.recvNoOPK k j l msg)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.recvNoOPK k j l msg)).run s3) := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq1Key, pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq1Key]
  have hBase35 : s35.hyb.base = withAuthBaseRoCache s35.hyb.base.roCache s3.hyb.base := by
    conv_lhs => rw [hAg]
    rfl
  have hPreEq : parseAuthRecvNoOPKPre P k j l msg s35.hyb.base =
      parseAuthRecvNoOPKPre P k j l msg s3.hyb.base := by
    rw [hBase35, parseAuthRecvNoOPKPre_withAuthBaseRoCache]
  rw [hPreEq]
  cases hPre : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base with
  | none =>
    rcases hRej hPre with hInv' | hBad'
    · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv'⟩)
    · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
        rw [mem_support_pure_iff] at hy; subst hy; exact hBad')
  | some p =>
    rcases p with ⟨kEntry, bEntry, usedTriples', ss⟩
    dsimp only
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec3 := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    have hDecEq : ({
        base := s35.hyb.base, initKemRecs := s35.hyb.initKemRecs,
        recvKemRecs := rRec :: s35.hyb.recvKemRecs,
        idealSessions := s35.hyb.idealSessions } : AuthHybridState S) =
        withAuthHybRoCache s35.hyb.base.roCache hstDec3 := by
      change { s35.hyb with recvKemRecs := rRec :: s35.hyb.recvKemRecs } = _
      conv_lhs => rw [hAg]
      rfl
    by_cases hAbDec : isAuthG3Abort P hstDec3 = true
    · refine RelProbUpToBad.of_support_rel _ _ (fun y35 hy35 y3 hy3 _ => ?_)
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy35 hy3
      rcases hy35 with ⟨res35, _, rfl⟩
      rcases hy3 with ⟨res3, _, rfl⟩
      refine Or.inr ?_
      rw [isAuthG3Abort_finishLatchedRecvNoOPK, isAuthG3Abort_finishLatchedRecvNoOPK,
          hDecEq, isAuthG3Abort_withBaseRoCache]
      exact ⟨hAbDec, hAbDec⟩
    · have hAbDecF : isAuthG3Abort P hstDec3 = false := Bool.eq_false_iff.mpr hAbDec
      rw [hDecEq]
      refine relProbUpToBad_evalAuthHybridRecvSchedule_bind _ _ P
        (withAuthHybRoCache s35.hyb.base.roCache hstDec3) hstDec3 kEntry bEntry
        none _ msg _ _ rfl rfl rfl ?_ ?_ ?_ ?_
      · rcases hSchedNone kEntry bEntry usedTriples' ss hPre hAbDecF with hI | hB
        · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro s hMatch
        rcases hSubA kEntry bEntry usedTriples' ss s hPre hAbDecF hMatch with
          ⟨hRoFind, hPostA⟩
        refine ⟨hRoFind, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
        rcases hPostA rk1 ck1_1 pt rootRoCache' hCore with hI | hB
        · have hFst := congrArg Prod.fst
            (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
              usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
              s3 hstDec3 s.drKey rk1 ck1_1 pt rootRoCache')
          rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hNotHon
        rcases hSubB kEntry bEntry usedTriples' ss hPre hAbDecF hMatchNone hNotHon with
          ⟨sec35, sec3, dk, hF35, hF3, hHit⟩ | ⟨hF35, hF3, hMiss⟩
        · left
          refine ⟨sec35, sec3, dk, hF35, hF3, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hHit rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
                usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
        · right
          refine ⟨hF35, hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hMiss dk hdk rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
                usedTriples' msg s35.adv.hyb.base.roCache
                ((recvHandshakeSecrets P kEntry bEntry none ss msg.hdr, dk) ::
                  s35.hyb.base.roCache)
                ((recvHandshakeSecrets P kEntry bEntry none ss msg.hdr, dk) :: s3.hyb.base.roCache)
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hHon
        rcases hFp : findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
          _ | ⟨u_r, senderEntry⟩
        · rw [hFp] at hHon; nomatch hHon
        · rw [hFp] at hHon; dsimp only at hHon
          rcases hSubC kEntry bEntry usedTriples' ss u_r senderEntry
              hPre hAbDecF hMatchNone hFp hHon with ⟨hF3, hPostC⟩
          refine ⟨hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          let recvEv : RecvdNoOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          cases hCons : (consumeMatchingSentNoOPK P recvEv s3.hyb.base.sentNoOPKEvents).1
          · rcases hPostC dk hdk rk1 ck1_1 pt rootRoCache' hCore hCons with hI | hB
            · have hFst := congrArg Prod.fst
                (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
                  usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache
                  ((recvHandshakeSecrets P kEntry bEntry none ss msg.hdr, dk) ::
                    s3.hyb.base.roCache)
                  s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
              rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
            · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
                rw [mem_support_pure_iff] at hy; subst hy; exact hB)
          · exfalso
            rcases parseAuthRecvNoOPKPre_some_props P k j l msg s3.hyb hPre with
              ⟨_, _, _, _, _, _, hkMem, hbMem, _⟩
            rcases consumeMatchingSentNoOPK_true_imp_abort_or_badLatchedMono_of_matched_none P hP
                maxRo s3 hRunInv hMatchNone hkMem hbMem
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hFp hHon hCons with hAb | hBad
            · rw [hAbF] at hAb; nomatch hAb
            · rw [hbF] at hBad; nomatch hBad

end Proofs.SignalPqxdh.Security
