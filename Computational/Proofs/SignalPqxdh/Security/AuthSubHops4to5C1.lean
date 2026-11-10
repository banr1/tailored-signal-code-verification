/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
public import Computational.Proofs.GameHop.Swap
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B2
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# `SlotM` Lazy/Eager Equivalence and `AeadIntCtxt` Cutoff Hybrid

Re-exports `SlotM` lazy/eager sampling lemmas, defines the `IdealSessionsAeadValid` invariant,
and constructs the session-indexed `INT-CTXT` cutoff hybrid (`authIntCutoffExp`) with its
boundary identities across `G3.8`, `G4`, and `G5`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt RelProbUpToBad simulateQ_relProbUpToBad evalDist_simulateQ_eq_of_step_or_bad)

export Computational.Proofs.GameHop.Swap (SlotM)

namespace SlotM
export Computational.Proofs.GameHop.Swap.SlotM
  (fill1 fill1_some fill1_none bind_fill1_of_keep getSlot getSlot_run_some getSlot_run_none)
end SlotM

/-- Invariant that every recorded fresh initiator session in `idealSessions` has valid `aeadCt`
    and slot index below `S.N_send_tot`. -/
def IdealSessionsAeadValid {S : Setup} (P : Primitives) (hst : AuthHybridStateFixed S) : Prop :=
  ∀ s ∈ hst.toAuthHybridState.idealSessions,
    s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧ initSessionSlotIdx s.sid < S.N_send_tot
theorem idealSessionsAeadValid_empty (S : Setup) (P : Primitives) (secb : Bool) :
    IdealSessionsAeadValid P (AuthHybridStateFixed.empty S secb) := by
  intro s hs
  cases hs
theorem idealSessionsAeadValid_finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSid : initSessionSlotIdx sid < S.N_send_tot)
    (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (isFreshPeer : Bool) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey)
    (rk1 ck1_0 mkSeed ck1_1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S)
    (hInv : ∀ s ∈ hst.idealSessions,
      s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧ initSessionSlotIdx s.sid < S.N_send_tot) :
    ∀ s ∈ (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt? pqRatchetMsg
      deriveMessageKeys ad (P.aeadEnc deriveMessageKeys ad msgPlain) msgPlain roCache' rootRoCache'
        hst).2.idealSessions,
      s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧ initSessionSlotIdx s.sid < S.N_send_tot := by
  unfold finishAuthHybridSend
  dsimp only
  split_ifs with hFresh
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact ⟨rfl, hSid⟩
    · exact hInv s hs'
  · exact hInv
theorem idealSessionsAeadValid_evalAuthHybridSendKosk {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (sid : SessionId S) (hSid : initSessionSlotIdx sid < S.N_send_tot)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S)
    (hInv : ∀ s ∈ hst.idealSessions,
      s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧ initSessionSlotIdx s.sid < S.N_send_tot)
    {p : AuthResponse × AuthHybridState S}
    (hp : p ∈ support (evalAuthHybridSendKosk stage useRo S P sid u bundle m0 m1 hst)) :
    ∀ s ∈ p.2.idealSessions,
      s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧ initSessionSlotIdx s.sid < S.N_send_tot := by
  unfold evalAuthHybridSendKosk at hp
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
    by_cases h2 : (hst.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hp
      cases hfind : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hfind] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
      | some up =>
        rcases up with ⟨_, uEntry⟩
        rw [hfind] at hp
        dsimp only at hp
        rcases ite_mem_support hp with hp | hp
        · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
        · by_cases h4 : (!koskBundleOk P hst.base.principals hst.base.spkBundles
                           hst.base.opkEntries hst.base.advKeys bundle) = true
          · simp only [h4, ↓reduceIte, support_pure,
              Set.mem_singleton_iff] at hp; subst hp; exact hInv
          · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hp
            rw [MonadAttach.mem_support_bind] at hp
            rcases hp with ⟨ekASk, _, hp⟩
            rw [MonadAttach.mem_support_bind] at hp
            rcases hp with ⟨kemCoins, _, hp⟩
            rw [MonadAttach.mem_support_bind] at hp
            rcases hp with ⟨ephASk, _, hp⟩
            rw [MonadAttach.mem_support_bind] at hp
            rcases hp with ⟨spqrCoins, _, hp⟩
            by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                              (encodeEC bundle.spkB) bundle.spkSig &&
                             P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h5, ↓reduceIte, support_pure,
                Set.mem_singleton_iff] at hp; subst hp; exact hInv
            · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hp
              cases hkem : P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                rw [hkem] at hp
                simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩
                rw [hkem] at hp
                dsimp only at hp
                rw [MonadAttach.mem_support_bind] at hp
                rcases hp with ⟨⟨drKey, roCache', ⟨rk1, ck1_0⟩, rootRoCache', ⟨mkSeed, ck1_1⟩⟩, _,
                  hp⟩
                cases hspqr : P.spqrInitSend drKey.pqrKey spqrCoins with
                | none =>
                  rw [hspqr] at hp
                  simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hInv
                | some pqr =>
                  rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  rw [hspqr] at hp
                  dsimp only at hp
                  rw [MonadAttach.mem_support_bind] at hp
                  rcases hp with ⟨deriveMessageKeys, _, hp⟩
                  simp only [support_pure, Set.mem_singleton_iff] at hp
                  subst hp
                  exact idealSessionsAeadValid_finishAuthHybridSend P sid hSid uEntry _ _ bundle m0
                    m1
                    ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys _ _ roCache' rootRoCache' hst hInv
theorem finishAuthHybridRecvOPK_idealSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) ×
      (Bytes × Bytes)))) :
    (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
      res?).2.idealSessions =
      hstDec.idealSessions := by
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only
      split_ifs <;> rfl
theorem finishAuthHybridRecvNoOPK_idealSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) ×
      (Bytes × Bytes)))) :
    (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec
      res?).2.idealSessions =
      hstDec.idealSessions := by
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only
      split_ifs <;> rfl
theorem prepareAuthHybridRecvOPK_idealSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) {prep : PreparedAuthRecv S}
    (hp : prepareAuthHybridRecvOPK checkAuth P k j o msg hst = some prep) :
    prep.hstDec.idealSessions = hst.idealSessions ∧
    ∀ res?, (prep.finish res?).2.idealSessions = hst.idealSessions := by
  unfold prepareAuthHybridRecvOPK at hp
  have h0 : (checkAuth && hst.base.hasWonAuth) = false := by
    cases h : (checkAuth && hst.base.hasWonAuth) <;> simp [h] at hp ⊢
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hp
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, reduceCtorEq] at hp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, reduceCtorEq] at hp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hp
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, reduceCtorEq] at hp
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hp
        cases hf1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp only [hf1, reduceCtorEq] at hp
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hf2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp only [hf1, hf2, reduceCtorEq] at hp
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hf3 : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
              o.val)) with
            | none => simp only [hf1, hf2, hf3, reduceCtorEq] at hp
            | some op =>
              rcases op with ⟨_, oEntry⟩
              simp only [hf1, hf2, hf3] at hp
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, reduceCtorEq] at hp
              · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hp
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, reduceCtorEq] at hp
                · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hp
                  cases hkem : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => simp only [hkem, reduceCtorEq] at hp
                  | some ss =>
                    simp only [hkem, Option.some.injEq] at hp
                    subst hp
                    exact ⟨rfl, fun res? => finishAuthHybridRecvOPK_idealSessions checkAuth P k j o
                      kEntry bEntry oEntry _ msg _ res?⟩
theorem prepareAuthHybridRecvNoOPK_idealSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) {prep : PreparedAuthRecv S}
    (hp : prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst = some prep) :
    prep.hstDec.idealSessions = hst.idealSessions ∧
    ∀ res?, (prep.finish res?).2.idealSessions = hst.idealSessions := by
  unfold prepareAuthHybridRecvNoOPK at hp
  have h0 : (checkAuth && hst.base.hasWonAuth) = false := by
    cases h : (checkAuth && hst.base.hasWonAuth) <;> simp [h] at hp ⊢
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hp
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                   msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none &&
                   msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 &&
                   msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, reduceCtorEq] at hp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, reduceCtorEq] at hp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hp
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, reduceCtorEq] at hp
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hp
        cases hf1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp only [hf1, reduceCtorEq] at hp
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hf2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp only [hf1, hf2, reduceCtorEq] at hp
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            simp only [hf1, hf2] at hp
            by_cases h4 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
              msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h4, ↓reduceIte, reduceCtorEq] at hp
            · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hp
              cases hkem : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => simp only [hkem, reduceCtorEq] at hp
              | some ss =>
                simp only [hkem, Option.some.injEq] at hp
                subst hp
                exact ⟨rfl, fun res? => finishAuthHybridRecvNoOPK_idealSessions checkAuth P k j l
                  kEntry bEntry _ msg _ res?⟩
theorem idealSessionsAeadValid_nonRecvSplitFixed {S : Setup}
    (sendStage recvStage : AuthHybridStage) (hIdeal : recvStage.idealMsgKeys = true)
    (useRo checkAuth : Bool) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : IdealSessionsAeadValid P hst)
    {p : (authSpec S).Range q × AuthHybridStateFixed S}
    (hp : p ∈ support ((pqxdhAuthHybridSplitFixedImpl sendStage recvStage useRo checkAuth S P q).run
      hst)) :
    IdealSessionsAeadValid P p.2 := by
  unfold pqxdhAuthHybridSplitFixedImpl at hp
  simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, pure_bind] at hp
  unfold IdealSessionsAeadValid at hInv ⊢
  cases q with
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridFixedImpl_recvOPK_eq recvStage hIdeal] at hp
    cases hprep : prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
    | none =>
      simp only [hprep, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hp
      rcases hp with ⟨⟨res?, mkSaltCache'⟩, _, hEq⟩
      have hSt : p.2.toAuthHybridState = (prep.finish res?).2 := by
        simpa using congrArg (fun x => x.2.toAuthHybridState) hEq.symm
      rw [hSt, (prepareAuthHybridRecvOPK_idealSessions checkAuth P k j o msg hst.toAuthHybridState
        hprep).2 res?]
      exact hInv
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridFixedImpl_recvNoOPK_eq recvStage hIdeal] at hp
    cases hprep : prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
    | none =>
      simp only [hprep, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hp
      rcases hp with ⟨⟨res?, mkSaltCache'⟩, _, hEq⟩
      have hSt : p.2.toAuthHybridState = (prep.finish res?).2 := by
        simpa using congrArg (fun x => x.2.toAuthHybridState) hEq.symm
      rw [hSt, (prepareAuthHybridRecvNoOPK_idealSessions checkAuth P k j l msg hst.toAuthHybridState
        hprep).2 res?]
      exact hInv
  | sendOPK u i bundle m0 m1 =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨resp, hst'⟩, hp, rfl⟩
    dsimp only [pqxdhAuthHybridKoskImpl] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · rw [runAuthHybridSendKosk_eq] at hp
      exact idealSessionsAeadValid_evalAuthHybridSendKosk sendStage useRo P (.sendOPK u i)
        (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)) u bundle m0
          m1 hst.toAuthHybridState hInv hp
  | sendNoOPK u i bundle m0 m1 =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨resp, hst'⟩, hp, rfl⟩
    dsimp only [pqxdhAuthHybridKoskImpl] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · rw [runAuthHybridSendKosk_eq] at hp
      exact idealSessionsAeadValid_evalAuthHybridSendKosk sendStage useRo P (.sendNoOPK u i)
        (initSessionSlotIdx_sendNoOPK_lt u i) u bundle m0 m1 hst.toAuthHybridState hInv hp
  | _ =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨resp, hst'⟩, hp, rfl⟩
    dsimp only [pqxdhAuthHybridKoskImpl] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hInv
    · simp only [run_liftAuthBase, support_map, Set.mem_image] at hp
      rcases hp with ⟨⟨_, _⟩, _, hEq⟩
      cases hEq
      exact hInv

@[simp] theorem resolveSigPkPeer_findHonestPrincipal (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    resolveSigPkPeer (findHonestPrincipal P principals ikB) ikB =
      resolveSigPk P principals ikB := rfl

theorem primBounded_checkBundleSpkHonIdealPeerPrim (S : Setup)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) :
    PrimBounded (checkBundleSpkHonIdealPeerPrim S peerPrincipal? spkBundles bundle)
      (S.N_dh * 2) := by
  unfold checkBundleSpkHonIdealPeerPrim
  cases peerPrincipal? with
  | none => exact primBounded_pure'
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    dsimp only
    refine primBounded_anyMPrim_take _ 2 S.N_dh spkBundles (fun ((u, _), b) => ?_)
    refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_checkBundleSpkHonIdealPeerPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (hSpk : spkBundles.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (checkBundleSpkHonIdealPeerPrim S
        (findHonestPrincipal P principals bundle.ikB) spkBundles bundle) =
      pure (checkBundleSpkHonIdeal P principals spkBundles bundle) := by
  unfold checkBundleSpkHonIdealPeerPrim checkBundleSpkHonIdeal
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    dsimp only
    rw [List.take_of_length_le hSpk,
        simulateQ_anyMPrim P _
          (fun ((u, _), b) => u == k && ((pEntry.corrupted && P.pow8 b.spkPk ==
            P.pow8 bundle.spkB) || b.spkPk == bundle.spkB))
          (fun _ => rfl) spkBundles]

end SignalPqxdh.Security
