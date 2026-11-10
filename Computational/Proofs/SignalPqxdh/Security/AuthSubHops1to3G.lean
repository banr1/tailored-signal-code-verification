/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# PQXDH authentication sub-hop 1 (`G3.5 → G3.6`, `RootKdfRO`): boundary and cache bounds

Proves the boundary equivalences for `authRkCutoffExp` (`0` vs `.g3_5` and `S.N_sess_tot` vs
`.g3_6`) together with `rootRoCache` length bounds and `cacheHasRk` monotonicity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

namespace SignalPqxdh.Security.AuthSubHops1to3

/-! ## Cutoff boundary equivalences -/

def normAuthFixed {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { toAuthHybridState := hst.toAuthHybridState, recvCount := hst.recvCount }

@[simp] theorem normAuthFixed_empty (S : Setup) (secb : Bool) :
    normAuthFixed (AuthHybridStateFixed.empty S secb) = AuthHybridStateFixed.empty S secb := rfl

@[simp] theorem normAuthFixed_toAuthHybridState {S : Setup} (hst : AuthHybridStateFixed S) :
    (normAuthFixed hst).toAuthHybridState = hst.toAuthHybridState := rfl

@[simp] theorem normAuthFixed_recvCount {S : Setup} (hst : AuthHybridStateFixed S) :
    (normAuthFixed hst).recvCount = hst.recvCount := rfl

private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp

theorem authCkOtherStep_normAuthFixed {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    (authCkOtherStep S P q hst >>= fun x => k (x.1, normAuthFixed x.2)) =
      (authCkOtherStep S P q (normAuthFixed hst) >>= k) := by
  unfold authCkOtherStep
  rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon <;>
    simp [hWon, normAuthFixed]

theorem evalDist_sampleDRKey96_bind_eq (F : DRKey → ProbComp Bool) :
    𝒟[sampleDRKey96 >>= F] =
      𝒟[sampleBytes32 >>= fun ck => sampleBytes32 >>= fun pk => sampleBytes32 >>= fun rk =>
        F { rootKey := rk, chainKey := ck, pqrKey := pk }] := by
  unfold sampleDRKey96
  simp only [bind_assoc, pure_bind]
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ fun ck _ => ?_
  rw [OracleComp.evalDist_bind_bind_swap]

def InvRkIdealSid {S : Setup} (hst : AuthHybridState S) : Prop :=
  ∀ s ∈ hst.idealSessions, sessionSlotIndex s.sid < S.N_sess_tot

theorem invRkIdealSid_empty (S : Setup) (secb : Bool) :
    InvRkIdealSid (AuthHybridState.empty S secb) := by
  intro s hs; cases hs

theorem invRkIdealSid_finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S)
    (hSid : sessionSlotIndex sid < S.N_sess_tot)
    (hInv : InvRkIdealSid hst) :
    InvRkIdealSid (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst).2 := by
  unfold finishAuthHybridSend InvRkIdealSid
  dsimp only
  split
  · intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hSid
    · exact hInv s hs
  · exact hInv

private theorem option_eq_none_or_eq_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

private theorem forall_support_bind {α β : Type} (m : ProbComp α)
    (f : α → ProbComp β) (P : β → Prop)
    (h : ∀ a, ∀ b ∈ support (f a), P b) :
    ∀ b ∈ support (m >>= f), P b := by
  intro b hb
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hb
  rcases hb with ⟨a, _, hb⟩
  exact h a b hb

private theorem forall_support_pure {α : Type} (x : α) (P : α → Prop) (h : P x) :
    ∀ b ∈ support (pure x : ProbComp α), P b := by
  intro b hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  exact hb ▸ h

def InvRkIdealSidAt {S : Setup} (mx : ProbComp (AuthResponse × AuthHybridState S)) : Prop :=
  ∀ x ∈ support mx, InvRkIdealSid x.2

theorem InvRkIdealSidAt.pure {S : Setup} {x : AuthResponse × AuthHybridState S}
    (h : InvRkIdealSid x.2) : InvRkIdealSidAt (pure x) :=
  forall_support_pure x (fun y => InvRkIdealSid y.2) h

theorem InvRkIdealSidAt.bind {S : Setup} {α : Type} (m : ProbComp α)
    {f : α → ProbComp (AuthResponse × AuthHybridState S)}
    (hf : ∀ a, InvRkIdealSidAt (f a)) : InvRkIdealSidAt (m >>= f) :=
  forall_support_bind m f (fun y => InvRkIdealSid y.2) hf

theorem invRkIdealSid_runAuthHybridSendKosk {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S)
    (hSid : sessionSlotIndex sid < S.N_sess_tot)
    (hInv : InvRkIdealSid hst) :
    InvRkIdealSidAt ((runAuthHybridSendKosk .g3_6 true S P sid u bundle m0 m1).run hst) := by
  rw [runAuthHybridSendKosk_eq]
  simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
    AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  repeat (first
    | (with_reducible apply InvRkIdealSidAt.pure;
       first
       | exact hInv
       | exact invRkIdealSid_finishAuthHybridSend P sid _ _ _ bundle m0 m1
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst hSid hInv)
    | (with_reducible apply InvRkIdealSidAt.bind; intro _)
    | split)

theorem evalDist_send_eq_authRkSendWith {S : Setup} (stage : AuthHybridStage) (cutoff : Nat)
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hDr : stage.idealDrKey = true)
    (hCk : stage.idealCk = false)
    (hMk : stage.idealMsgKeys = false)
    (hAead : stage.idealFreshAead = false)
    (hCut : decide (sessionSlotIndex sid < cutoff) = stage.idealRk)
    (hWon : hst.toAuthHybridState.base.hasWonAuth = false)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[((runAuthHybridSendKosk stage true S P sid u bundle m0 m1).run hst.toAuthHybridState) >>=
        fun x => k (x.1, { toAuthHybridState := x.2, recvCount := hst.recvCount })] =
      𝒟[authRkSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff))
          sid u bundle m0 m1
          (normAuthFixed hst) >>= k] := by
  rw [runAuthHybridSendKosk_eq]
  unfold authRkSendWith
  dsimp only [normAuthFixed]
  simp only [hWon, hDr, hCk, hMk, hAead,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (m0.length != m1.length) with h1 | h1 <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true
    (hst.toAuthHybridState.base.usedSendSessions.contains sid) with h2 | h2 <;>
    simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases option_eq_none_or_eq_some
    (hst.toAuthHybridState.base.principals.find? (fun x => x.1 == u.val)) with
    h3 | ⟨⟨_, uEntry⟩, h3⟩ <;>
    rw [h3]
  · simp only [pure_bind]
  · dsimp only
    rcases option_eq_none_or_eq_some
      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB) with
      hpeer | ⟨⟨pIdx, pEntry⟩, hpeer⟩ <;>
      rw [hpeer] <;> dsimp only
    · rcases bool_eq_false_or_eq_true (m0 != m1) with hm | hm <;>
        simp only [hm, Bool.not_false, Bool.and_false, Bool.and_true,
          Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases bool_eq_false_or_eq_true
        (!koskBundleOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
          hst.toAuthHybridState.base.advKeys bundle) with hk | hk <;>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      rcases bool_eq_false_or_eq_true
        (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
             (encodeEC bundle.spkB) bundle.spkSig &&
           P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
             (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
      · simp only [pure_bind]
      · dsimp only
        simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true,
          ↓reduceIte, bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
        refine OracleComp.evalDist_bind_congr_of_support _ _ _
          (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
        rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
        · simp only [pure_bind]
        · simp only [pure_bind]
    · rcases bool_eq_false_or_eq_true (! !pEntry.corrupted && (m0 != m1)) with hm | hm <;>
        simp only [hm, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases bool_eq_false_or_eq_true
        (!koskBundleOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
          hst.toAuthHybridState.base.advKeys bundle) with hk | hk <;>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      rcases bool_eq_false_or_eq_true
        (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
             (encodeEC bundle.spkB) bundle.spkSig &&
           P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
             (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
      · simp only [pure_bind]
      · dsimp only
        rcases bool_eq_false_or_eq_true
          (!pEntry.corrupted ||
           ((some (pIdx, pEntry)).isSome &&
            checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles bundle &&
            (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles
              hst.toAuthHybridState.base.opkEntries bundle).2.2)) with hIdeal | hIdeal <;>
          simp only [hIdeal, Bool.true_and, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, bind_assoc]
        · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _
            (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
          rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
          · simp only [pure_bind]
          · simp only [pure_bind]
        · rw [evalDist_sampleDRKey96_bind_eq]
          refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun ck _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun pk _ => ?_)
          dsimp only
          unfold finishAuthSendAfterRk
          simp only [hCut]
          rcases P.spqrInitSend pk spqrCoins with
            _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩ <;> dsimp only
          · cases stage.idealRk <;>
              simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
            · trans 𝒟[sampleBytes32 >>= fun _ =>
                k (.noneResp,
                  { toAuthHybridState := hst.toAuthHybridState, recvCount := hst.recvCount })]
              · refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun rk _ => ?_)
                exact OracleComp.evalDist_bind_const _ _
              · exact OracleComp.evalDist_bind_const sampleBytes32 _
            · simp only [evalDist_sampleBytes32_bind_const]
          · cases stage.idealRk <;>
              simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]

theorem evalAuthHybridRecvSchedule_g3_5_of_wf {S : Setup} (useRo : Bool)
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridState S) (prep : PreparedAuthRecv S)
    (hWf : PreparedAuthRecvWf P msg hst prep) :
    evalAuthHybridRecvSchedule .g3_5 useRo P prep.hstDec
      prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg = (do
      let st := prep.hstDec.base
      let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
      if prep.matchedSess?.isSome || prep.isUncorruptedHonestSender then
        match prep.matchedSess? with
        | some s => do
          let ((rk1, ck1_0), rootRoCache') ←
            evalRootKdfOrRo useRo P st.rootRoCache s.drKey.rootKey prep.dhRatchet
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => pure none
          | some (_pqrStB, spqrSalt?) =>
            let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?
            pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
              (s.drKey, rk1, P.chainKdfNext ck1_0, pt, st.roCache, rootRoCache')))
        | none => do
          let dk ← sampleDRKey96
          let ((rk1, ck1_0), rootRoCache') ←
            evalRootKdfOrRo useRo P st.rootRoCache dk.rootKey prep.dhRatchet
          match P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
          | none => pure none
          | some (_pqrStB, spqrSalt?) =>
            let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?
            pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
              (dk, rk1, P.chainKdfNext ck1_0, pt, st.roCache, rootRoCache')))
      else do
        let (drKey, roCache') ← evalHkdfOrRo useRo P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ←
          evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey prep.dhRatchet
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => pure none
        | some (_pqrStB, spqrSalt?) =>
          let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?
          pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
            (drKey, rk1, P.chainKdfNext ck1_0, pt, roCache', rootRoCache')))) := by
  unfold evalAuthHybridRecvSchedule
  dsimp only
  rw [hWf.matchedSess_eq, hWf.dhRatchet_eq]
  have hU := hWf.isUncorrupted_eq
  rcases option_eq_none_or_eq_some
    (findHonestPrincipal P prep.hstDec.base.principals msg.hdr.ikAPk) with
    hs | ⟨⟨_, sEntry⟩, hs⟩ <;>
    simp only [hs] at hU <;>
    rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · simp only [hs, hms, hU.symm, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      Option.isSome, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
    refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
    rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
      first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hs, hms, hU.symm, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
      Option.isSome, Bool.or_false, Bool.true_and, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
    rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
      first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      simp only [hs, hms, hU.symm, hsc, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.false_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun dk => ?_)
      refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
      refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      simp only [hs, hms, hU.symm, hsc, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.true_or, Bool.true_and,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)

theorem evalDist_recv_schedule_g3_5_eq_authRkRecvWith_zero {S : Setup}
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (prep : PreparedAuthRecv S)
    (hWf : PreparedAuthRecvWf P msg hst.toAuthHybridState prep)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[(do
        let res? ← evalAuthHybridRecvSchedule .g3_5 true P prep.hstDec
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        let (resp, hst') := prep.finish res?
        k (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1 }))] =
      𝒟[authRkRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0))
          msg (some prep) (normAuthFixed hst) >>= k] := by
  rw [evalAuthHybridRecvSchedule_g3_5_of_wf true P msg hst.toAuthHybridState prep hWf]
  have hCut0 : ∀ n : Nat, decide (n < 0) = false := fun _ => by simp
  unfold authRkRecvWith finishAuthRecvUnmatchedAfterRk finishAuthRecvRk sampleDRKey96 normAuthFixed
  dsimp only
  simp only [hCut0, Bool.false_eq_true, ↓reduceIte]
  rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · rcases bool_eq_false_or_eq_true prep.isUncorruptedHonestSender with hU | hU
    · simp only [hms, hU, Option.isSome, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · simp only [hms, hU, Option.isSome, Bool.false_or, ↓reduceIte, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ck _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun pk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
      rcases P.spqrInitRecv pk msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms, Option.isSome, Bool.true_or, ↓reduceIte, bind_assoc, pure_bind]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _
      (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
    rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
      first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)

theorem evalDist_recv_schedule_g3_6_eq_authRkRecvWith_end {S : Setup}
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (prep : PreparedAuthRecv S)
    (hInv : InvRkIdealSid hst.toAuthHybridState)
    (hWf : PreparedAuthRecvWf P msg hst.toAuthHybridState prep)
    (hCut : S.N_send_tot + hst.recvCount < S.N_sess_tot)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[(do
        let res? ← evalAuthHybridRecvSchedule .g3_6 true P prep.hstDec
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        let (resp, hst') := prep.finish res?
        k (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1 }))] =
      𝒟[authRkRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
          msg (some prep) (normAuthFixed hst) >>= k] := by
  rw [evalAuthHybridRecvSchedule_g3_6_of_wf true P msg hst.toAuthHybridState prep hWf]
  have hCutD : decide (S.N_send_tot + hst.recvCount < S.N_sess_tot) = true := decide_eq_true hCut
  unfold authRkRecvWith finishAuthRecvUnmatchedAfterRk finishAuthRecvRk sampleDRKey96 normAuthFixed
  dsimp only
  simp only [hCutD, ↓reduceIte]
  rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · rcases bool_eq_false_or_eq_true prep.isUncorruptedHonestSender with hU | hU
    · simp only [hms, hU, Option.isSome, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · simp only [hms, hU, Option.isSome, Bool.false_or, ↓reduceIte, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ck _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun pk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun c _ => ?_)
      rcases P.spqrInitRecv pk msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · have hs_mem : s ∈ hst.toAuthHybridState.idealSessions :=
      hWf.idealSessions_eq ▸ List.mem_of_find?_eq_some (hWf.matchedSess_eq.trans hms)
    have hs_lt : decide (sessionSlotIndex s.sid < S.N_sess_tot) = true :=
      decide_eq_true (hInv s hs_mem)
    rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hms, hs_lt, hEph, Option.isSome, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, pure_bind]
    · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun c _ => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)

theorem step_g3_5_eq_authRkStepWith_zero {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (_hInv : True) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl .g3_5 true true S P q).run hst >>=
          fun x => k (x.1, normAuthFixed x.2)] =
        𝒟[(authRkCutoffImpl S P 0 q).run (normAuthFixed hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl .g3_5 true true S P q).run hst), True) := by
  dsimp only [authRkCutoffImpl, StateT.run_mk]
  rw [pqxdhAuthHybridFixedImpl_run_eq .g3_5]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        exact ⟨fun k => evalDist_send_eq_authRkSendWith .g3_5 0 P (.sendOPK u i) u bundle m0 m1 hst
          rfl rfl rfl rfl (by simp [AuthHybridStage.idealRk]) hWon k, fun _ _ => trivial⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind] <;>
        exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        exact ⟨fun k => evalDist_send_eq_authRkSendWith .g3_5 0 P (.sendNoOPK u i) u bundle m0 m1
          hst rfl rfl rfl rfl (by simp [AuthHybridStage.idealRk]) hWon k, fun _ _ => trivial⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind] <;>
        exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | recvOPK k' j o msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      exact ⟨fun k => evalDist_recv_schedule_g3_5_eq_authRkRecvWith_zero P msg hst prep hWf k,
        fun _ _ => trivial⟩
  | recvNoOPK k' j l msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      exact ⟨fun k => evalDist_recv_schedule_g3_5_eq_authRkRecvWith_zero P msg hst prep hWf k,
        fun _ _ => trivial⟩
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte,
      authRkStepWith, pqxdhAuthHybridKoskImpl]
    rw [liftAuthBase_other_eq_slots0]
    exact ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_normAuthFixed P _ { hst with slots := {} } k),
      fun _ _ => trivial⟩

theorem step_g3_6_eq_authRkStepWith_end {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : InvRkIdealSid hst.toAuthHybridState)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl .g3_6 true true S P q).run hst >>=
          fun x => k (x.1, normAuthFixed x.2)] =
        𝒟[(authRkCutoffImpl S P S.N_sess_tot q).run (normAuthFixed hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl .g3_6 true true S P q).run hst),
      InvRkIdealSid x.2.toAuthHybridState ∧
      x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0)) := by
  dsimp only [authRkCutoffImpl, StateT.run_mk]
  rw [pqxdhAuthHybridFixedImpl_run_eq .g3_6]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
      have := sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k =>
          evalDist_send_eq_authRkSendWith .g3_6 S.N_sess_tot P (.sendOPK u i) u bundle m0 m1 hst
          rfl rfl rfl rfl (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invRkIdealSid_runAuthHybridSendKosk P (.sendOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        refine ⟨fun _ => trivial, fun x hx => ?_⟩ <;>
        (subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | sendNoOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
      have := sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k =>
          evalDist_send_eq_authRkSendWith .g3_6 S.N_sess_tot P (.sendNoOPK u i) u bundle m0 m1 hst
          rfl rfl rfl rfl (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invRkIdealSid_runAuthHybridSendKosk P (.sendNoOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        refine ⟨fun _ => trivial, fun x hx => ?_⟩ <;>
        (subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      refine ⟨fun _ => rfl, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k =>
        evalDist_recv_schedule_g3_6_eq_authRkRecvWith_end P msg hst prep hInv hWf hLt k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨res?, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      refine ⟨fun _ => rfl, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k =>
        evalDist_recv_schedule_g3_6_eq_authRkRecvWith_end P msg hst prep hInv hWf hLt k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨res?, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte,
      authRkStepWith, pqxdhAuthHybridKoskImpl]
    rw [liftAuthBase_other_eq_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_normAuthFixed P _ { hst with slots := {} } k),
      fun x hx => ?_⟩
    obtain ⟨hId, hCnt⟩ := support_authCkOtherStep P _ { hst with slots := {} } hx
    refine ⟨fun s hs => ?_, Nat.le_trans (le_of_eq hCnt) (Nat.le_add_right _ _)⟩
    rw [hId] at hs
    exact hInv s hs

theorem evalDist_authRkCutoffExp_zero_eq_g3_5 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[authRkCutoffExp S P 0 A] = 𝒟[authFixedExpAtStage .g3_5 S P A] := by
  symm
  unfold authFixedExpAtStage authRkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_proj_inv
    (normAuthFixed (S := S))
    (fun _ => True)
    (pqxdhAuthHybridFixedImpl .g3_5 true true S P)
    (authRkCutoffImpl S P 0)
    (fun q hst hInv => step_g3_5_eq_authRkStepWith_zero P q hst hInv)
    A.run
    (AuthHybridStateFixed.empty S secb)
    trivial
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

theorem evalDist_authRkCutoffExp_end_eq_g3_6 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authRkCutoffExp S P S.N_sess_tot A.1] = 𝒟[authFixedExpAtStage .g3_6 S P A.1] := by
  symm
  unfold authFixedExpAtStage authRkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound :
      OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (normAuthFixed (S := S))
    (fun hst => InvRkIdealSid hst.toAuthHybridState)
    (fun hst => hst.recvCount)
    (isAuthRecvQueryB (S := S))
    (fun _ => rfl)
    S.N_recv_tot
    (pqxdhAuthHybridFixedImpl .g3_6 true true S P)
    (authRkCutoffImpl S P S.N_sess_tot)
    (fun q hst hInv hRecv => step_g3_6_eq_authRkStepWith_end P q hst hInv hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb)
    (invRkIdealSid_empty S secb)
    (by simp [AuthHybridStateFixed.empty])
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

theorem authRkCutoffAdv_zero_eq_g3_5 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authRkCutoffAdv S P 0 A = authFixedAdvAtStage .g3_5 S P A := by
  unfold authRkCutoffAdv authFixedAdvAtStage
  rw [evalDist_authRkCutoffExp_zero_eq_g3_5]

theorem authRkCutoffAdv_end_eq_g3_6 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    authRkCutoffAdv S P S.N_sess_tot A.1 = authFixedAdvAtStage .g3_6 S P A.1 := by
  unfold authRkCutoffAdv authFixedAdvAtStage
  rw [evalDist_authRkCutoffExp_end_eq_g3_6 S P b A]

/-! ## `rootRoCache` length bounds -/

def isAuthSendQueryB {S : Setup} : (Nat ⊕ AuthQuery S) → Bool
  | .inr (.sendOPK _ _ _ _ _)   => true
  | .inr (.sendNoOPK _ _ _ _ _) => true
  | _                           => false

def isAuthRoRootQueryB {S : Setup} : (Nat ⊕ AuthQuery S) → Bool
  | .inr (.roRootQuery _ _) => true
  | _                       => false

@[simp] theorem isAuthSendQueryB_eq_true_iff {S : Setup} (q : Nat ⊕ AuthQuery S) :
    isAuthSendQueryB q = true ↔ isAuthSendQuery q := by
  rcases q with _ | q
  · simp [isAuthSendQueryB, isAuthSendQuery]
  · cases q <;> simp [isAuthSendQueryB, isAuthSendQuery]

@[simp] theorem isAuthRoRootQueryB_eq_true_iff {S : Setup} (q : Nat ⊕ AuthQuery S) :
    isAuthRoRootQueryB q = true ↔ isAuthRoRootQuery q := by
  rcases q with _ | q
  · simp [isAuthRoRootQueryB, isAuthRoRootQuery]
  · cases q <;> simp [isAuthRoRootQueryB, isAuthRoRootQuery]

def AuthRootRoCacheLenLe {S : Setup} (hst : AuthHybridStateFixed S) (k : Nat)
    (mx : ProbComp (AuthResponse × AuthHybridStateFixed S)) : Prop :=
  ∀ y ∈ support mx,
    y.2.toAuthHybridState.base.rootRoCache.length ≤
      hst.toAuthHybridState.base.rootRoCache.length + k

theorem AuthRootRoCacheLenLe.bind {S : Setup} {α : Type} (hst : AuthHybridStateFixed S)
    (k : Nat) (m : ProbComp α) {f : α → ProbComp (AuthResponse × AuthHybridStateFixed S)}
    (hf : ∀ a ∈ support m, AuthRootRoCacheLenLe hst k (f a)) :
    AuthRootRoCacheLenLe hst k (m >>= f) := by
  intro y hy
  simp only [MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, ha, hy'⟩
  exact hf a ha y hy'

theorem AuthRootRoCacheLenLe.bind_pure_left {S : Setup} {α : Type} (hst : AuthHybridStateFixed S)
    (k : Nat) (a : α) {f : α → ProbComp (AuthResponse × AuthHybridStateFixed S)}
    (hf : AuthRootRoCacheLenLe hst k (f a)) :
    AuthRootRoCacheLenLe hst k (pure a >>= f) := by
  rw [pure_bind]; exact hf

theorem finishAuthSendAfterRk_rootRoCache_length_le {S : Setup} (P : Primitives)
    (useIdealRkAt : Nat → Bool) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (rk : Bytes) :
    AuthRootRoCacheLenLe hst 1
      (finishAuthSendAfterRk P useIdealRkAt sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk dhRatchet ck pk
        spqrSalt? pqRatchetMsg msgPlain hst rk) := by
  unfold finishAuthSendAfterRk
  dsimp only
  split
  · refine AuthRootRoCacheLenLe.bind hst 1 sampleBytes32 (fun r _ => ?_)
    refine AuthRootRoCacheLenLe.bind hst 1 sampleBytes32 (fun c _ => ?_)
    apply AuthRootRoCacheLenLe.bind_pure_left
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    dsimp only [finishAuthHybridSend]
    omega
  · refine AuthRootRoCacheLenLe.bind hst 1 _ (fun x hx => ?_)
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact evalRootKdfOrRo_length_le P rk dhRatchet hst.toAuthHybridState.base.rootRoCache x hx

theorem AuthRootRoCacheLenLe.pure {S : Setup} {hst : AuthHybridStateFixed S} {k : Nat}
    {x : AuthResponse × AuthHybridStateFixed S}
    (h : x.2.toAuthHybridState.base.rootRoCache.length ≤
      hst.toAuthHybridState.base.rootRoCache.length + k) :
    AuthRootRoCacheLenLe hst k (pure x) := by
  intro y hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  exact h

theorem authRkSendWith_rootRoCache_length_le {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    AuthRootRoCacheLenLe hst 1
      (authRkSendWith S P sampRkAt useIdealRkAt sid u bundle m0 m1 hst) := by
  unfold authRkSendWith; dsimp only
  cases hst.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  repeat (first
    | (with_reducible apply AuthRootRoCacheLenLe.pure;
       dsimp only [finishAuthHybridSend];
       first
       | omega
       | exact evalRootKdfOrRo_length_le P _ _
           hst.toAuthHybridState.base.rootRoCache _ (by assumption))
    | with_reducible apply finishAuthSendAfterRk_rootRoCache_length_le
    | with_reducible apply AuthRootRoCacheLenLe.bind_pure_left
    | (with_reducible apply AuthRootRoCacheLenLe.bind; intro _ _)
    | split)

structure PreparedAuthRecvCacheWf {S : Setup} (hst : AuthHybridState S)
    (prep : PreparedAuthRecv S) : Prop where
  base_eq : prep.hstDec.base = hst.base
  finish_rootRoCache : ∀ res?,
    (prep.finish res?).2.base.rootRoCache =
      match res? with
      | none => hst.base.rootRoCache
      | some (_, _, _, _, _, rootRoCache') => rootRoCache'

theorem prepareAuthHybridRecvOPK_cacheWf {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    ∀ prep, prepareAuthHybridRecvOPK checkAuth P k j o msg hst = some prep →
      PreparedAuthRecvCacheWf hst prep := by
  unfold prepareAuthHybridRecvOPK
  dsimp only
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split
  · split; · intro _ h; cases h
    split; · intro _ h; cases h
    split
    · intro _ h; cases h
    · intro prep h; injection h with h; subst h
      refine ⟨rfl, fun res? => ?_⟩
      unfold finishAuthHybridRecvOPK
      cases res? with
      | none => rfl
      | some r =>
        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
        dsimp only
        cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
        | none => rfl
        | some p =>
          rcases p with ⟨_, senderEntry⟩
          dsimp only
          cases senderEntry.corrupted <;> rfl
  · intro _ h; cases h

theorem prepareAuthHybridRecvNoOPK_cacheWf {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    ∀ prep, prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst = some prep →
      PreparedAuthRecvCacheWf hst prep := by
  unfold prepareAuthHybridRecvNoOPK
  dsimp only
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split
  · split; · intro _ h; cases h
    split
    · intro _ h; cases h
    · intro prep h; injection h with h; subst h
      refine ⟨rfl, fun res? => ?_⟩
      unfold finishAuthHybridRecvNoOPK
      cases res? with
      | none => rfl
      | some r =>
        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
        dsimp only
        cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
        | none => rfl
        | some p =>
          rcases p with ⟨_, senderEntry⟩
          dsimp only
          cases senderEntry.corrupted <;> rfl
  · intro _ h; cases h

theorem authCkOtherStep_roRootQuery_eq {S : Setup} (P : Primitives)
    (rk dh : Bytes) (hst : AuthHybridStateFixed S) :
    authCkOtherStep S P (.roRootQuery rk dh) hst =
      if hst.toAuthHybridState.base.hasWonAuth then
        pure (.noneResp, hst)
      else (do
        let (out, rootRoCache') ←
          evalRootKdfOrRo true P hst.toAuthHybridState.base.rootRoCache rk dh
        pure (.rootKdfResp out.1 out.2,
          { hst with toAuthHybridState := { hst.toAuthHybridState with
              base := { hst.toAuthHybridState.base with rootRoCache := rootRoCache' } } })) := by
  unfold authCkOtherStep pqxdhAuthImpl
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, pure_bind]

def IsAuthOtherNonRoRoot {S : Setup} (q : AuthQuery S) : Prop :=
  (∀ u i bundle m0 m1, q ≠ .sendOPK u i bundle m0 m1) ∧
  (∀ u i bundle m0 m1, q ≠ .sendNoOPK u i bundle m0 m1) ∧
  (∀ k j o msg, q ≠ .recvOPK k j o msg) ∧
  (∀ k j l msg, q ≠ .recvNoOPK k j l msg) ∧
  (∀ rk dh, q ≠ .roRootQuery rk dh)

theorem authCkOtherStep_preserves_rootRoCache {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (hst : AuthHybridStateFixed S) :
    ∀ y ∈ support (authCkOtherStep S P q hst),
      y.2.toAuthHybridState.base.rootRoCache = hst.toAuthHybridState.base.rootRoCache := by
  have hPres : PreservesAt AuthState.rootRoCache hst.toAuthHybridState.base
      (pqxdhAuthImpl true true S P q) := by
    cases q with
    | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
    | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
    | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
    | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
    | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
    | _ =>
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
  intro y hy
  unfold authCkOtherStep at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩
    exact hPres (resp, base') hbase

end SignalPqxdh.Security.AuthSubHops1to3
