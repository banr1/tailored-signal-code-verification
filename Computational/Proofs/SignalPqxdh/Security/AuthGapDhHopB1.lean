/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHop
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopB
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hop `G0 → G3`: split-key hash collision simulation

Defines the `KemShCr` simulation `runAuthShCrSim` and bounds `badKemShCrProbAuth` by the sum of
per-index `KemShCr` advantages.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Classical
open scoped BigOperators ENNReal
open MeasureTheory
open SignalPqxdh
open SignalPqxdh.Security
open OracleComp

namespace Proofs.SignalPqxdh.Security

export _root_.SignalPqxdh.Security (InitKemRecord RecvKemRecord AuthShCrState isNoneAuthShCrResp runAuthShCrAcceptPrim genSpkTargetAuthPrim)

abbrev liftAuthShCrBase {S : Setup} {α : Type}
    (m : StateT (AuthState S) ProbComp α) : StateT (AuthShCrState S) ProbComp α :=
  liftShCrBase m

def preCheckAuthSim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) : Option (PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes) :=
  if m0.length != m1.length then none
  else if st.usedSendSessions.contains sid then none
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => none
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then none
      else if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then none
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        some (uEntry, peerPrincipal?, msgPlain)

def finishAuthSimBase (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (st : AuthState S) : ProbComp (AuthResponse × Option (AuthState S)) := do
  let (uEntry, peerPrincipal?, msgPlain) := uInfo
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ←
    evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1 := P.chainKdfNext ck1_0
  match P.spqrInitSend drKey.pqrKey spqrCoins with
  | none => return (.noneResp, none)
  | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
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
    let (spkHon, opkHon, pqspkHon) :=
      match peerPrincipal? with
      | none => (false, false, false)
      | some (k, _) =>
        (st.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
         false,
         st.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))
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
    let base' : AuthState S := { st with
      sessions         := sessEntry :: st.sessions
      usedSendSessions := sid :: st.usedSendSessions
      roCache          := roCache'
      rootRoCache      := rootRoCache' }
    let resp : AuthResponse :=
      if peerPrincipal?.isSome then .sendFreshResp wireMsg
      else .sendUnfreshResp drKey rk1 ck1_1 wireMsg
    return (resp, some base')

theorem finishAuthSimBase_spkBundles (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (st : AuthState S) (out : AuthResponse × Option (AuthState S))
    (hout : out ∈ support (finishAuthSimBase S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss
      kemCt st)) :
    ∀ base', out.2 = some base' → base'.spkBundles = st.spkBundles := by
  intro base' hbase
  unfold finishAuthSimBase at hout
  rcases uInfo with ⟨uEntry, peerPrincipal?, msgPlain⟩
  dsimp only at hout
  simp only [MonadAttach.mem_support_bind] at hout
  rcases hout with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hout⟩
  dsimp only at hout
  revert hout
  cases P.spqrInitSend drKey.pqrKey spqrCoins
  · intro hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout; cases hbase
  · rename_i spqrTriple
    rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
    intro hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    injection hbase with h; subst h; rfl

theorem finishAuthSimBase_validAuthSim (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (st : AuthState S) (hV : ValidAuthSim S P st)
    (out : AuthResponse × Option (AuthState S))
    (hout : out ∈ support (finishAuthSimBase S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss
      kemCt st)) :
    ∀ base', out.2 = some base' → ValidAuthSim S P base' := by
  intro base' hbase
  unfold finishAuthSimBase at hout
  rcases uInfo with ⟨uEntry, peerPrincipal?, msgPlain⟩
  dsimp only at hout
  simp only [MonadAttach.mem_support_bind] at hout
  rcases hout with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hout⟩
  dsimp only at hout
  revert hout
  cases P.spqrInitSend drKey.pqrKey spqrCoins
  · intro hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout; cases hbase
  · rename_i spqrTriple
    rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
    intro hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    injection hbase with h; subst h; exact hV

abbrev runAuthShCrSend (_checkG2 : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthShCrState S) ProbComp AuthResponse :=
  runShCrInitiate4 P AuthState.principals AuthResponse.noneResp
    (preCheckAuthSim S P sid u bundle m0 m1) sid bundle (finishAuthSimBase S P sid bundle m0 m1)

abbrev runAuthShCrGenSPK (embedTarget : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (AuthShCrState S) ProbComp AuthResponse :=
  runShCrGenSPKGeneric embedTarget P AuthState.principals AuthState.spkBundles
    (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u j

def pqxdhAuthShCrSimImpl (embedTarget : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthShCrState S) ProbComp)
  | .genSPK u j => runAuthShCrGenSPK embedTarget S P u j
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure .noneResp
    else runAuthShCrSend embedTarget S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure .noneResp
    else runAuthShCrSend embedTarget S P (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    runShCrAcceptGeneric P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr
  | .recvNoOPK k j l msg =>
    runShCrAcceptGeneric P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr
  | q_other => liftAuthShCrBase (pqxdhAuthSimImpl S P q_other)

noncomputable def tryPauseAuthQuery (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : AuthQuery S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) : Option (PausedShCrKem S (AuthState S)) :=
  match gq, cont with
  | .sendOPK u i bundle m0 m1, cont =>
    if bundle.opkB?.isNone then none
    else tryPause4 P AuthState.principals (pqxdhAuthShCrSimImpl true S P)
      (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
      (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) sIdx cont hst
  | .sendNoOPK u i bundle m0 m1, cont =>
    if bundle.opkB?.isSome then none
    else tryPause4 P AuthState.principals (pqxdhAuthShCrSimImpl true S P)
      (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
      (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) sIdx cont hst
  | _, _ => none

noncomputable def shcrChoosePkAuthAt (S : Setup) (P : Primitives)
    (bIdx sIdx : Nat) (A : AuthAdversary S) :
    Bytes → Bytes → ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes)) :=
  shcrChoosePkGenericAt P ($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb))
    (pqxdhAuthShCrSimImpl true S P) (tryPauseAuthQuery S P) bIdx sIdx A.run

noncomputable def runAuthShCrSim (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthShCrState S) := do
  let secb ← $ᵗ Bool
  let initSt : AuthShCrState S := { base := AuthState.empty S secb }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl false S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

noncomputable def badKemShCrProbAuthAt (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) : ℝ :=
  (𝒟[runAuthShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (_root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs
      finalHst.recvKemRecs)] {true}).toReal

noncomputable def badKemShCrProbAuth (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[runAuthShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (_root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords S P finalHst.initKemRecs
      finalHst.recvKemRecs)] {true}).toReal

theorem badKemShCrProbAuth_le_sum (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    badKemShCrProbAuth S P A ≤
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot), badKemShCrProbAuthAt S P idx A := by
  unfold badKemShCrProbAuth badKemShCrProbAuthAt
    _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords
  exact toReal_any_range_le_sum (runAuthShCrSim S P A) (S.N_spk_tot * S.N_send_tot)
    (fun idx (_, _, finalHst) => _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecordsAt S P idx
      finalHst.initKemRecs finalHst.recvKemRecs)

theorem pqxdhAuthSimImpl_preserves_spkBundles (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S)
    (hNotGen : ∀ u j, q ≠ .genSPK u j) :
    ∀ y ∈ support ((pqxdhAuthSimImpl S P q).run st),
      y.2.spkBundles = st.spkBundles := by
  cases q with
  | genSPK u j => exact False.elim (hNotGen u j rfl)
  | sendOPK u i bnd m0 m1 =>
    intro y hy
    exact (pqxdhAuthSimImpl_sendOPK_pres S P u i bnd m0 m1 st y hy).2.1
  | sendNoOPK u i bnd m0 m1 =>
    intro y hy
    exact (pqxdhAuthSimImpl_sendNoOPK_pres S P u i bnd m0 m1 st y hy).2.1
  | initPrin _ | corruptIK _ | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _
      | roRootQuery _ _ | revealDhSecrets | registerKey _ =>
    change PreservesAt AuthState.spkBundles st (pqxdhAuthSimImpl S P _)
    unfold pqxdhAuthSimImpl pqxdhAuthImpl
    dsimp only
    prove_preserves_at

theorem pqxdhAuthShCrSimImpl_clearFalse (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthShCrState S) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((pqxdhAuthShCrSimImpl false S P q).run hst), clearShCrTarget x.2 = x.2 := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_clearFalse P AuthState.principals AuthState.spkBundles
      (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u j
        hst hClear
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_clearFalse P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) hst hClear
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hClear
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_clearFalse P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) hst hClear
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hClear
  | recvOPK k j o msg =>
    exact runShCrAcceptGeneric_clearFalse P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr hst hClear
  | recvNoOPK k j l msg =>
    exact runShCrAcceptGeneric_clearFalse P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr hst hClear
  | initPrin u => exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P (.initPrin u)) hst hClear
  | corruptIK u => exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P (.corruptIK u)) hst hClear
  | genOPK u j o => exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P (.genOPK u j o)) hst hClear
  | roQuery secrets =>
    exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P (.roQuery secrets)) hst hClear
  | roRootQuery rk dh =>
    exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P (.roRootQuery rk dh)) hst hClear
  | revealDhSecrets =>
    exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P .revealDhSecrets) hst hClear
  | registerKey sk =>
    exact liftShCrBase_clearFalse (pqxdhAuthSimImpl S P (.registerKey sk)) hst hClear

theorem pqxdhAuthShCrSimImpl_afterGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : AuthQuery S) (hst : AuthShCrState S) (hClear : clearShCrTarget hst = hst)
    (hGen : hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhAuthShCrSimImpl true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (pqxdhAuthShCrSimImpl false S P q).run
        hst) ∧
    (∀ x ∈ support ((pqxdhAuthShCrSimImpl false S P q).run hst),
      hasGeneratedTargetBundle S bIdx x.2.base.spkBundles) := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_afterGen P AuthState.principals AuthState.spkBundles
      (fun st bs => { st with spkBundles := bs }) (fun _ _ => rfl) AuthResponse.noneResp
        AuthResponse.bundleResp u j bIdx hst hClear hGen
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_afterGen P AuthState.principals AuthState.spkBundles
        AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) bIdx hst
        (fun uInfo ekASk ephASk spqrCoins ss kemCt out hout =>
          finishAuthSimBase_spkBundles S P (.sendOPK u i) bundle m0 m1 uInfo ekASk ephASk spqrCoins
            ss kemCt hst.base out hout) hGen
    · simp only [↓reduceIte]
      refine ⟨fun _ _ => by simp [StateT.run_pure, Prod.map], fun x hx => ?_⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hGen
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_afterGen P AuthState.principals AuthState.spkBundles
        AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) bIdx hst
        (fun uInfo ekASk ephASk spqrCoins ss kemCt out hout =>
          finishAuthSimBase_spkBundles S P (.sendNoOPK u i) bundle m0 m1 uInfo ekASk ephASk
            spqrCoins ss kemCt hst.base out hout) hGen
    · simp only [↓reduceIte]
      refine ⟨fun _ _ => by simp [StateT.run_pure, Prod.map], fun x hx => ?_⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hGen
  | recvOPK k j o msg =>
    exact runShCrAcceptGeneric_afterGen P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr bIdx hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.recvOPK k j o msg) hst.base
        (by intro _ _ h; cases h)) hGen
  | recvNoOPK k j l msg =>
    exact runShCrAcceptGeneric_afterGen P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr bIdx hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.recvNoOPK k j l msg) hst.base
        (by intro _ _ h; cases h)) hGen
  | initPrin u =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P (.initPrin u)) bIdx hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.initPrin u) hst.base (by intro _ _ h; cases h))
        hGen
  | corruptIK u =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P (.corruptIK u)) bIdx hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.corruptIK u) hst.base (by intro _ _ h; cases h))
        hGen
  | genOPK u j o =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P (.genOPK u j o)) bIdx hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.genOPK u j o) hst.base (by intro _ _ h; cases h))
        hGen
  | roQuery secrets =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P (.roQuery secrets)) bIdx
      hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.roQuery secrets) hst.base (by intro _ _ h; cases
        h)) hGen
  | roRootQuery rk dh =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P (.roRootQuery rk dh))
      bIdx hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.roRootQuery rk dh) hst.base
        (by intro _ _ h; cases h)) hGen
  | revealDhSecrets =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P .revealDhSecrets) bIdx
      hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P .revealDhSecrets hst.base (by intro _ _ h; cases
        h)) hGen
  | registerKey sk =>
    exact liftShCrBase_afterGen AuthState.spkBundles (pqxdhAuthSimImpl S P (.registerKey sk)) bIdx
      hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.registerKey sk) hst.base (by intro _ _ h; cases
        h)) hGen

theorem pqxdhAuthShCrSimImpl_beforeGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : AuthQuery S) (hst : AuthShCrState S) (hClear : clearShCrTarget hst = hst)
    (hNotGen : ¬ hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhAuthShCrSimImpl true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (pqxdhAuthShCrSimImpl false S P q).run
        hst) ∨
    ((∀ obs : (authSpec S).Range q × AuthShCrState S → ProbComp Bool,
      𝒟[sampleKemKeyGen P >>= fun pair =>
        (pqxdhAuthShCrSimImpl true S P q).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x =>
        obs (x.1, clearShCrTarget x.2)] =
      𝒟[(pqxdhAuthShCrSimImpl false S P q).run hst >>= obs]) ∧
     (∀ pk sk, ∀ x ∈ support ((pqxdhAuthShCrSimImpl true S P q).run (setShCrTarget hst bIdx pk sk)),
      x.2 = setShCrTarget (clearShCrTarget x.2) bIdx pk sk ∧
      hasGeneratedTargetBundle S bIdx (clearShCrTarget x.2).base.spkBundles)) := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_beforeGen P AuthState.principals AuthState.spkBundles
      (fun st bs => { st with spkBundles := bs }) (fun _ _ => rfl) AuthResponse.noneResp
        AuthResponse.bundleResp u j bIdx hst hClear hNotGen
  | sendOPK u i bundle m0 m1 =>
    left; intro pk sk; dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_setShCrTarget P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) hst bIdx pk sk
    · simp [StateT.run_pure, Prod.map]
  | sendNoOPK u i bundle m0 m1 =>
    left; intro pk sk; dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_setShCrTarget P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) hst bIdx pk sk
    · simp [StateT.run_pure, Prod.map]
  | recvOPK k j o msg =>
    left; exact runShCrAcceptGeneric_setShCrTarget P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr hst bIdx
  | recvNoOPK k j l msg =>
    left; exact runShCrAcceptGeneric_setShCrTarget P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr hst bIdx
  | initPrin u =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P (.initPrin u)) hst bIdx
  | corruptIK u =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P (.corruptIK u)) hst bIdx
  | genOPK u j o =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P (.genOPK u j o)) hst bIdx
  | roQuery secrets =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P (.roQuery secrets)) hst bIdx
  | roRootQuery rk dh =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P (.roRootQuery rk dh)) hst bIdx
  | revealDhSecrets =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P .revealDhSecrets) hst bIdx
  | registerKey sk =>
    left; exact liftShCrBase_setShCrTarget (pqxdhAuthSimImpl S P (.registerKey sk)) hst bIdx

theorem pqxdhAuthShCrSimImpl_validStep (S : Setup) (P : Primitives) (bIdx : Nat) (pk sk : Bytes)
    (q : AuthQuery S) (hst : AuthShCrState S)
    (hV : ValidTargetRecv AuthState.spkBundles bIdx pk sk hst) :
    ∀ x ∈ support ((pqxdhAuthShCrSimImpl true S P q).run hst),
      ValidTargetRecv AuthState.spkBundles bIdx pk sk x.2 := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_validStep P AuthState.principals AuthState.spkBundles
      (fun st bs => { st with spkBundles := bs }) (fun _ _ => rfl) AuthResponse.noneResp
        AuthResponse.bundleResp u j bIdx pk sk hst hV
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_validStep P AuthState.principals AuthState.spkBundles
        AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) bIdx pk sk hst
        (fun uInfo ekASk ephASk spqrCoins ss kemCt out hout =>
          finishAuthSimBase_spkBundles S P (.sendOPK u i) bundle m0 m1 uInfo ekASk ephASk spqrCoins
            ss kemCt hst.base out hout) hV
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hV
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_validStep P AuthState.principals AuthState.spkBundles
        AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) bIdx pk sk hst
        (fun uInfo ekASk ephASk spqrCoins ss kemCt out hout =>
          finishAuthSimBase_spkBundles S P (.sendNoOPK u i) bundle m0 m1 uInfo ekASk ephASk
            spqrCoins ss kemCt hst.base out hout) hV
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hV
  | recvOPK k j o msg =>
    exact runShCrAcceptGeneric_validStep P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr bIdx pk sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.recvOPK k j o msg) hst.base
        (by intro _ _ h; cases h)) hV
  | recvNoOPK k j l msg =>
    exact runShCrAcceptGeneric_validStep P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr bIdx pk sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.recvNoOPK k j l msg) hst.base
        (by intro _ _ h; cases h)) hV
  | initPrin u =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P (.initPrin u)) bIdx pk
      sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.initPrin u) hst.base (by intro _ _ h; cases h))
        hV
  | corruptIK u =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P (.corruptIK u)) bIdx pk
      sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.corruptIK u) hst.base (by intro _ _ h; cases h))
        hV
  | genOPK u j o =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P (.genOPK u j o)) bIdx pk
      sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.genOPK u j o) hst.base (by intro _ _ h; cases h))
        hV
  | roQuery secrets =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P (.roQuery secrets)) bIdx
      pk sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.roQuery secrets) hst.base (by intro _ _ h; cases
        h)) hV
  | roRootQuery rk dh =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P (.roRootQuery rk dh))
      bIdx pk sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.roRootQuery rk dh) hst.base
        (by intro _ _ h; cases h)) hV
  | revealDhSecrets =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P .revealDhSecrets) bIdx
      pk sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P .revealDhSecrets hst.base (by intro _ _ h; cases
        h)) hV
  | registerKey sk' =>
    exact liftShCrBase_validStep AuthState.spkBundles (pqxdhAuthSimImpl S P (.registerKey sk')) bIdx
      pk sk hst
      (pqxdhAuthSimImpl_preserves_spkBundles S P (.registerKey sk') hst.base (by intro _ _ h; cases
        h)) hV

theorem pqxdhAuthShCrSimImpl_sendStep (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthShCrState S) :
    ∀ x ∈ support ((pqxdhAuthShCrSimImpl true S P q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_sendStep' P AuthState.principals AuthState.spkBundles
      (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u j
        hst
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_sendStep P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) hst
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact ⟨le_rfl, fun i hi => Or.inl hi⟩
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate4_sendStep P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) hst
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact ⟨le_rfl, fun i hi => Or.inl hi⟩
  | recvOPK k j o msg =>
    exact runShCrAcceptGeneric_sendStep' P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr hst
  | recvNoOPK k j l msg =>
    exact runShCrAcceptGeneric_sendStep' P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr hst
  | initPrin u => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P (.initPrin u)) hst
  | corruptIK u => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P (.corruptIK u)) hst
  | genOPK u j o => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P (.genOPK u j o)) hst
  | roQuery secrets => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P (.roQuery secrets)) hst
  | roRootQuery rk dh => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P (.roRootQuery rk dh)) hst
  | revealDhSecrets => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P .revealDhSecrets) hst
  | registerKey sk => exact liftShCrBase_sendStep (pqxdhAuthSimImpl S P (.registerKey sk)) hst

theorem pqxdhAuthShCrSimImpl_pauseNone (S : Setup) (P : Primitives) (sIdx : Nat)
    (gq : AuthQuery S) (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPauseAuthQuery S P sIdx gq cont hst = none) :
    ∀ x ∈ support ((pqxdhAuthShCrSimImpl true S P gq).run hst), x.2.sendCount ≤ sIdx := by
  cases gq with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_pauseNone P AuthState.principals AuthState.spkBundles
      (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u j
        sIdx hst hLe
  | sendOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQuery] at hNone
    dsimp only [pqxdhAuthShCrSimImpl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate4_pauseNone P AuthState.principals
        (pqxdhAuthShCrSimImpl true S P) AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQuery] at hNone
    dsimp only [pqxdhAuthShCrSimImpl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate4_pauseNone P AuthState.principals
        (pqxdhAuthShCrSimImpl true S P) AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | recvOPK k j o msg =>
    exact runShCrAcceptGeneric_pauseNone P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) k j msg.hdr sIdx hst hLe
  | recvNoOPK k j l msg =>
    exact runShCrAcceptGeneric_pauseNone P AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) k j msg.hdr sIdx hst hLe
  | initPrin u => exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P (.initPrin u)) sIdx hst hLe
  | corruptIK u => exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P (.corruptIK u)) sIdx hst hLe
  | genOPK u j o => exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P (.genOPK u j o)) sIdx hst hLe
  | roQuery secrets =>
    exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P (.roQuery secrets)) sIdx hst hLe
  | roRootQuery rk dh =>
    exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P (.roRootQuery rk dh)) sIdx hst hLe
  | revealDhSecrets =>
    exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P .revealDhSecrets) sIdx hst hLe
  | registerKey sk =>
    exact liftShCrBase_pauseNone (pqxdhAuthSimImpl S P (.registerKey sk)) sIdx hst hLe

theorem pqxdhAuthShCrSimImpl_pauseSome (S : Setup) (P : Primitives) (bIdx sIdx : Nat) (pk sk :
  Bytes)
    (gq : AuthQuery S) (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (paused : PausedShCrKem S (AuthState S))
    (hV : ValidTargetRecv AuthState.spkBundles bIdx pk sk hst)
    (hSome : tryPauseAuthQuery S P sIdx gq cont hst = some paused) :
    ∃ (noneOut : (authSpec S).Range gq)
      (postKem : Bytes → Bytes → ProbComp ((authSpec S).Range gq × AuthShCrState S)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl true S P) (cont y.1)).run
              y.2)) ∧
      (∀ obs : (authSpec S).Range gq × AuthShCrState S → ProbComp Bool,
        𝒟[(pqxdhAuthShCrSimImpl true S P gq).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecv AuthState.spkBundles bIdx pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQuery] at hSome
    rw [show pqxdhAuthShCrSimImpl true S P (.sendOPK u i bundle m0 m1) =
      (if bundle.opkB?.isNone then pure .noneResp else runAuthShCrSend true S P (.sendOPK u i) u
        bundle m0 m1) from rfl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate4_pauseSome P AuthState.principals AuthState.spkBundles
        (pqxdhAuthShCrSimImpl true S P) AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ephASk spqrCoins ss kemCt out hout =>
          finishAuthSimBase_spkBundles S P (.sendOPK u i) bundle m0 m1 uInfo ekASk ephASk spqrCoins
            ss kemCt hst.base out hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQuery] at hSome
    rw [show pqxdhAuthShCrSimImpl true S P (.sendNoOPK u i bundle m0 m1) =
      (if bundle.opkB?.isSome then pure .noneResp else runAuthShCrSend true S P (.sendNoOPK u i) u
        bundle m0 m1) from rfl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate4_pauseSome P AuthState.principals AuthState.spkBundles
        (pqxdhAuthShCrSimImpl true S P) AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ephASk spqrCoins ss kemCt out hout =>
          finishAuthSimBase_spkBundles S P (.sendNoOPK u i) bundle m0 m1 uInfo ekASk ephASk
            spqrCoins ss kemCt hst.base out hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | genSPK u j => cases hSome
  | recvOPK k j o msg => cases hSome
  | recvNoOPK k j l msg => cases hSome
  | initPrin u => cases hSome
  | corruptIK u => cases hSome
  | genOPK u j o => cases hSome
  | roQuery secrets => cases hSome
  | roRootQuery rk dh => cases hSome
  | revealDhSecrets => cases hSome
  | registerKey sk => cases hSome

theorem badKemShCrProbAuthAt_le_kemShCrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    badKemShCrProbAuthAt S P idx A ≤
      (𝒟[kemShCrExpProb P (shcrChoosePkAuthAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A)]
        {true}).toReal := by
  unfold badKemShCrProbAuthAt shcrChoosePkAuthAt
  have hEq :
      (runAuthShCrSim S P A >>= fun (_, _, finalHst) =>
        pure (_root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs
          finalHst.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl false S P) A.run).run { base :=
            b0 } >>= fun x =>
        pure (_root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecordsAt S P idx x.2.initKemRecs
          x.2.recvKemRecs)) := by
    simp [runAuthShCrSim]
  rw [hEq]
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  exact badKemShCrProbGenericAt_le_kemShCr P
    ($ᵗ Bool >>= fun secb => pure (AuthState.empty S secb))
    AuthState.spkBundles
    (pqxdhAuthShCrSimImpl false S P)
    (pqxdhAuthShCrSimImpl true S P)
    (tryPauseAuthQuery S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhAuthShCrSimImpl_clearFalse S P)
    (pqxdhAuthShCrSimImpl_afterGen S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_beforeGen S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_validStep S P (idx / S.N_send_tot))
    (pqxdhAuthShCrSimImpl_sendStep S P)
    (pqxdhAuthShCrSimImpl_pauseNone S P (idx % S.N_send_tot))
    (pqxdhAuthShCrSimImpl_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

theorem postKem4_validAuthSim_and_recvKemRecs (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (hst : AuthShCrState S) (ss kemCt : Bytes)
    (hV : ValidAuthSim S P hst.base) :
    ∀ y ∈ support (postKem4 sid bundle uInfo (finishAuthSimBase S P sid bundle m0 m1) hst ss kemCt),
      ValidAuthSim S P y.2.base ∧ y.2.recvKemRecs = hst.recvKemRecs := by
  intro y hy
  unfold postKem4 at hy
  simp only [MonadAttach.mem_support_bind, support_map, Set.mem_image] at hy
  rcases hy with ⟨ekASk, _, ephASk, _, spqrCoins, _, out, hout, rfl⟩
  rcases out with ⟨resp, none | base'⟩
  · exact ⟨hV, rfl⟩
  · exact ⟨finishAuthSimBase_validAuthSim S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt
      hst.base hV (resp, some base') hout base' rfl, rfl⟩

theorem pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs (embedTarget : Bool) (S : Setup) (P :
  Primitives)
    (gq : AuthQuery S) (hst : AuthShCrState S) (hV : ValidAuthSim S P hst.base) :
    ∀ x ∈ support ((pqxdhAuthShCrSimImpl embedTarget S P gq).run hst),
      ValidAuthSim S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
  intro x hx
  cases gq with
  | genSPK u j =>
    dsimp only [pqxdhAuthShCrSimImpl, runAuthShCrGenSPK, runShCrGenSPKGeneric, StateT.run] at hx
    have hBase : ∀ x ∈ support ((liftShCrBase (genSpkBaseGeneric P AuthState.principals
      AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u
          j)).run hst),
        ValidAuthSim S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
      intro x hx
      simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hx
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨?_, by simp⟩
      rcases mem_support_genSpkBaseGeneric P AuthState.principals AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u
          j hst.base y hy with
        rfl | ⟨uEntry, spkSk, rSpk, pqspkPk, pqspkSk, rPq, hFresh, rfl⟩
      · exact hV
      · exact ⟨hV.1, (validSpkBundles_cons S u j _ hst.base.spkBundles hV.2.1 hFresh).1, hV.2.2⟩
    have hTarget : ∀ x ∈ support ((genSpkTargetGeneric P AuthState.principals AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u
          j).run hst),
        ValidAuthSim S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
      intro x hx
      rcases mem_support_genSpkTargetGeneric P AuthState.principals AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u
          j hst x hx with
        rfl | ⟨uEntry, spkSk, rSpk, rPq, hFresh, rfl⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨⟨hV.1, (validSpkBundles_cons S u j _ hst.base.spkBundles hV.2.1 hFresh).1, hV.2.2⟩,
          by simp⟩
    revert hx
    cases embedTarget
    · exact hBase x
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hst.targetBIdx? with
      | none => exact hBase x
      | some bIdx =>
        dsimp only
        split_ifs
        · exact hTarget x
        · exact hBase x
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl] at hx
    split_ifs at hx with hopk
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, by simp⟩
    · rcases mem_support_runShCrInitiate4 P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
        (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) hst x hx with
        ⟨rfl, _⟩ | ⟨uInfo, hPre, _, rfl | ⟨ekASk, ephASk, spqrCoins, ss, kemCt, out, hout, rfl⟩⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨hV, by simp⟩
      · rcases out with ⟨resp, none | base'⟩
        · exact ⟨hV, by simp [applyShCrFinish]⟩
        · exact ⟨finishAuthSimBase_validAuthSim S P (.sendOPK u i) bundle m0 m1 uInfo ekASk ephASk
            spqrCoins ss kemCt hst.base hV (resp, some base') hout base' rfl, by simp
            [applyShCrFinish]⟩
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrSimImpl] at hx
    split_ifs at hx with hopk
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, by simp⟩
    · rcases mem_support_runShCrInitiate4 P AuthState.principals AuthResponse.noneResp
        (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
        (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) hst x hx with
        ⟨rfl, _⟩ | ⟨uInfo, hPre, _, rfl | ⟨ekASk, ephASk, spqrCoins, ss, kemCt, out, hout, rfl⟩⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨hV, by simp⟩
      · rcases out with ⟨resp, none | base'⟩
        · exact ⟨hV, by simp [applyShCrFinish]⟩
        · exact ⟨finishAuthSimBase_validAuthSim S P (.sendNoOPK u i) bundle m0 m1 uInfo ekASk ephASk
            spqrCoins ss kemCt hst.base hV (resp, some base') hout base' rfl, by simp
            [applyShCrFinish]⟩
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthShCrSimImpl] at hx
    unfold runShCrAcceptGeneric at hx
    simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx⟩
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hVz := pqxdhAuthSimImpl_validAuthSim_step S P (.recvOPK k j o msg) hst.base hV z hz
    rcases mem_support_recordAcceptKemGeneric P AuthState.spkBundles isNoneAuthShCrResp k j msg.hdr
      z.1 { hst with base := z.2 } x hx with
      rfl | ⟨_, _, _, _, _, rfl⟩
    · exact ⟨hVz, by simp⟩
    · exact ⟨hVz, by simp⟩
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthShCrSimImpl] at hx
    unfold runShCrAcceptGeneric at hx
    simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx⟩
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hVz := pqxdhAuthSimImpl_validAuthSim_step S P (.recvNoOPK k j l msg) hst.base hV z hz
    rcases mem_support_recordAcceptKemGeneric P AuthState.spkBundles isNoneAuthShCrResp k j msg.hdr
      z.1 { hst with base := z.2 } x hx with
      rfl | ⟨_, _, _, _, _, rfl⟩
    · exact ⟨hVz, by simp⟩
    · exact ⟨hVz, by simp⟩
  | initPrin u =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P (.initPrin u) hst.base hV z hz, by simp⟩
  | corruptIK u =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P (.corruptIK u) hst.base hV z hz, by simp⟩
  | genOPK u j o =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P (.genOPK u j o) hst.base hV z hz, by simp⟩
  | roQuery secrets =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P (.roQuery secrets) hst.base hV z hz, by simp⟩
  | roRootQuery rk dh =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P (.roRootQuery rk dh) hst.base hV z hz, by simp⟩
  | revealDhSecrets =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P .revealDhSecrets hst.base hV z hz, by simp⟩
  | registerKey sk =>
    dsimp only [pqxdhAuthShCrSimImpl, liftAuthShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhAuthSimImpl_validAuthSim_step S P (.registerKey sk) hst.base hV z hz, by simp⟩

theorem simulateQ_runAuthShCrAcceptPrim (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : AuthQuery S)
    (hst : AuthShCrState S) (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) ((runAuthShCrAcceptPrim S k j hdr gq).run hst) =
      (runShCrAcceptGeneric P AuthState.spkBundles isNoneAuthShCrResp
        (pqxdhAuthSimImpl S P gq) k j hdr).run hst := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, hSpk, hOpk⟩
  unfold runAuthShCrAcceptPrim runShCrAcceptGeneric
  simp only [StateT.run_bind, simulateQ_bind,
    simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P gq hst.base hPrin hSpk hOpk hV.2.2.2)]
  congr 1; ext x
  exact simulateQ_recordAcceptKemGenericPrim P AuthState.spkBundles isNoneAuthShCrResp k j hdr x.1
    x.2

theorem simulateQ_genSpkTargetAuthPrim (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : AuthShCrState S) :
    simulateQ (primBaseImpl P) ((genSpkTargetAuthPrim S u j).run hst) =
      (genSpkTargetGeneric P AuthState.principals AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs })
        AuthResponse.noneResp AuthResponse.bundleResp u j).run hst := by
  dsimp only [genSpkTargetAuthPrim, genSpkTargetGeneric, StateT.run]
  split_ifs
  · rfl
  · cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rfl
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [simulateQ_bind, simulateQ_embedUnif, mkSpkBundlePair]
      congr 1

end Proofs.SignalPqxdh.Security
