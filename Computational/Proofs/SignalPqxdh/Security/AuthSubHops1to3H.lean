/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3G3
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H3
public import Computational.Proofs.SignalPqxdh.Security.SaltKey
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3F
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators
namespace SignalPqxdh.Security
open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
namespace AuthSubHops1to3
/-- The `PrfMsgKeys` oracle cache: 32-byte effective salt ↦ message keys. -/
abbrev PrfMkCache := List (List.Vector UInt8 32 × MessageKeys)
def prfMsgKeysOracleImpl (b : Bool) (P : Primitives) (mkSeed : Bytes) :
    QueryImpl prfMsgKeysSpec (StateT PrfMkCache ProbComp) :=
  fun (.derive salt) => do
    if b then
      return P.deriveMsgKeys mkSeed (some salt.toList)
    else
      let cache ← get
      match cache.find? (fun (s, _) => s == salt) with
      | some (_, out) => return out
      | none =>
        let out ← liftM sampleMessageKeys80
        set ((salt, out) :: cache)
        return out
def evalPrfMkReal (P : Primitives) (mkSeedStar : Bytes)
    (salt? : Option Bytes) (cache : PrfMkCache) :
    ProbComp (MessageKeys × PrfMkCache) :=
  pure (deriveMsgKeysEff P mkSeedStar salt?, cache)
def evalPrfMkIdeal (salt? : Option Bytes) (cache : PrfMkCache) :
    ProbComp (MessageKeys × PrfMkCache) :=
  match cache.find? (fun (s, _) => s == effectiveHkdfSaltBytes salt?) with
  | some (_, out) => pure (out, cache)
  | none => do
    let out ← sampleMessageKeys80
    pure (out, (effectiveHkdfSaltBytes salt?, out) :: cache)
theorem prfMsgKeysOracleImpl_true_run (P : Primitives) (mkSeedStar : Bytes)
    (salt? : Option Bytes) (cache : PrfMkCache) :
    ((prfMsgKeysOracleImpl true P mkSeedStar) (.derive (effectiveHkdfSaltBytes salt?))).run cache =
      evalPrfMkReal P mkSeedStar salt? cache := by
  simp [prfMsgKeysOracleImpl, evalPrfMkReal, deriveMsgKeysEff]
theorem prfMsgKeysOracleImpl_false_run (P : Primitives) (mkSeedStar : Bytes)
    (salt? : Option Bytes) (cache : PrfMkCache) :
    ((prfMsgKeysOracleImpl false P mkSeedStar) (.derive (effectiveHkdfSaltBytes salt?))).run cache =
      evalPrfMkIdeal salt? cache := by
  unfold prfMsgKeysOracleImpl evalPrfMkIdeal
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
  cases cache.find? (fun (s, _) => s == effectiveHkdfSaltBytes salt?) with
  | some p => simp
  | none => simp [StateT.run_monadLift, monadLift_self]
def matchedSameEphMkWith {S : Setup} (P : Primitives) (useIdealMkAt : Nat → Bool)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    ProbComp (MessageKeys × List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :=
  if useIdealMkAt (sessionSlotIndex s.sid) then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure (s.deriveMessageKeys, mkSaltCache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure (mk, mkSaltCache)
      | none => do
        let mk ← sampleMessageKeys80
        pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
  else
    pure (P.deriveMsgKeys s.mkSeed spqrSalt?, mkSaltCache)
theorem decide_lt_of_beq_true {s idx : Nat} (h : (s == idx) = true) :
    decide (s < idx) = false := by
  have heq : s = idx := beq_iff_eq.mp h
  subst heq
  simp
theorem decide_lt_succ_of_beq_true {s idx : Nat} (h : (s == idx) = true) :
    decide (s < idx + 1) = true := by
  have heq : s = idx := beq_iff_eq.mp h
  subst heq
  simp
theorem decide_lt_succ_of_beq_false {s idx : Nat} (h : (s == idx) = false) :
    decide (s < idx + 1) = decide (s < idx) := by
  have hne : s ≠ idx := beq_eq_false_iff_ne.mp h
  by_cases hlt : s < idx
  · have hlt' : s < idx + 1 := by omega
    simp [hlt, hlt']
  · have hlt' : ¬ (s < idx + 1) := by omega
    simp [hlt, hlt']
theorem authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le {S : Setup} {idx : Nat}
    {hst hst' : AuthHybridStateFixed S}
    (hUsed : hst'.toAuthHybridState.base.usedSendSessions =
      hst.toAuthHybridState.base.usedSendSessions)
    (hRC : hst.recvCount ≤ hst'.recvCount) (hNF : authSlotFired S idx hst' = false) :
    authSlotFired S idx hst = false := by
  cases hF : authSlotFired S idx hst
  · rfl
  · have hF' := authSlotFired_of_usedSendSessions_eq_and_recvCount_le hF hUsed hRC
    rw [hF'] at hNF; cases hNF
private theorem forall_mem_support_ite_mk {α : Type} (c : Bool) (t e : ProbComp α) (Q : α → Prop)
    (ht : ∀ x ∈ support t, Q x) (he : ∀ x ∈ support e, Q x) :
    ∀ x ∈ support (if c then t else e), Q x := by
  cases c <;> [exact he; exact ht]
private theorem forall_mem_support_ite_mk_eq {α : Type} (c : Bool) (t e : ProbComp α)
    (Q : α → Prop) (he : c = false → ∀ x ∈ support e, Q x)
    (ht : c = true → ∀ x ∈ support t, Q x) :
    ∀ x ∈ support (if c then t else e), Q x := by
  cases hc : c
  · exact he hc
  · exact ht hc
theorem support_prepareAuthSendMk_full_props {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    ∀ p ∈ support (prepareAuthSendMk S P sid u bundle m0 m1 hst),
      match p with
      | .done _ hst' =>
        hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
        hst'.mkSaltCache = hst.mkSaltCache ∧
        hst'.recvCount = hst.recvCount ∧
        (∀ sid0, hst.toAuthHybridState.base.usedSendSessions.contains sid0 = true →
          hst'.toAuthHybridState.base.usedSendSessions.contains sid0 = true)
      | .idealMk _ _ _ _ _ _ _ _ _ _ spqrSalt? _ _ =>
        hst.toAuthHybridState.base.usedSendSessions.contains sid = false ∧
        (WellFormedPrimitivesδ P → SaltOK spqrSalt?) := by
  unfold prepareAuthSendMk
  dsimp only
  refine forall_mem_support_ite_mk _ _ _ _ (fun x hx =>
    by simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩) ?_
  refine forall_mem_support_ite_mk _ _ _ _ (fun x hx =>
    by simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩) ?_
  cases hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · intro x hx; simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩
    · refine forall_mem_support_ite_mk _ _ _ _ (fun x hx =>
        by simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩) ?_
      refine forall_mem_support_ite_mk _ _ _ _ (fun x hx =>
        by simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩) ?_
      intro x hx
      simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨ekASk, _, kemCoins, _, ephASk, _, spqrCoins, _, hx⟩
      revert x hx
      refine forall_mem_support_ite_mk _ _ _ _ (fun x hx =>
        by simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩) ?_
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => intro x hx; simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        dsimp only
        refine forall_mem_support_ite_mk_eq _ _ _ _ (fun hI => ?_) (fun _ => ?_)
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
          revert x hx
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => intro x hx; simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            intro x hx
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx
            unfold finishAuthHybridSend
            dsimp only at hI ⊢
            exact ⟨ite_eq_right_iff.mpr (fun hTrue => False.elim
                                          (Bool.noConfusion (hI.symm.trans hTrue))),
              rfl, rfl, fun sid0 h0 =>
              List.contains_iff_mem.mpr (List.mem_cons.mpr (Or.inr (List.contains_iff_mem.mp h0)))⟩
        · intro x hx
          simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩
          revert x hx
          cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => intro x hx; simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩
          | some spqrVal =>
            rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
            intro x hx
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx
            exact ⟨trivial, fun hWF => saltOK_of_spqrInitSend hWF hSpqr⟩
  · simp only [↓reduceIte]
    intro x hx; simp at hx; subst hx; exact ⟨rfl, rfl, rfl, fun _ h => h⟩
theorem finishAuthSendMk_full_props {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    let hst' := (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys).2
    hst'.mkSaltCache = hst.mkSaltCache ∧
    hst'.recvCount = hst.recvCount ∧
    hst'.toAuthHybridState.base.usedSendSessions = sid ::
      hst.toAuthHybridState.base.usedSendSessions ∧
    (hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∨
     ∃ s0 : IdealAuthSession S,
       s0.sid = sid ∧ s0.mkSeed = mkSeed ∧ s0.spqrSalt? = spqrSalt? ∧ s0.deriveMessageKeys = deriveMessageKeys ∧
       hst'.toAuthHybridState.idealSessions = s0 :: hst.toAuthHybridState.idealSessions) := by
  exact ⟨rfl, rfl, rfl,
    (finishAuthSendMk_idealSessions_props P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys).2.2⟩
theorem finishAuthHybridRecvOPK_idealSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List
                     ((Bytes × Bytes) × (Bytes × Bytes)))) :
    (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
      res?).2.idealSessions =
      hstDec.idealSessions := by
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some res =>
    rcases res with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      split <;> rfl
theorem finishAuthHybridRecvNoOPK_idealSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List
                     ((Bytes × Bytes) × (Bytes × Bytes)))) :
    (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec
      res?).2.idealSessions =
      hstDec.idealSessions := by
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some res =>
    rcases res with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      split <;> rfl
theorem prepareAuthHybridRecvOPK_props {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (prep : PreparedAuthRecv S)
    (h : prepareAuthHybridRecvOPK true P k j o msg hst = some prep) :
    (∀ s, prep.matchedSess? = some s → s ∈ hst.idealSessions) ∧
    (∀ res?, (prep.finish res?).2.idealSessions = hst.idealSessions ∧
             (prep.finish res?).2.base.usedSendSessions = hst.base.usedSendSessions) := by
  unfold prepareAuthHybridRecvOPK at h
  dsimp only at h
  repeat (split at h <;> try cases h)
  refine ⟨fun s hs => List.mem_of_find?_eq_some hs, fun res? => ⟨?_, ?_⟩⟩
  · exact finishAuthHybridRecvOPK_idealSessions true P k j o _ _ _ _ msg _ res?
  · exact finishAuthHybridRecvOPK_usedSendSessions true P k j o _ _ _ _ msg _ res?
theorem prepareAuthHybridRecvNoOPK_props {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (prep : PreparedAuthRecv S)
    (h : prepareAuthHybridRecvNoOPK true P k j l msg hst = some prep) :
    (∀ s, prep.matchedSess? = some s → s ∈ hst.idealSessions) ∧
    (∀ res?, (prep.finish res?).2.idealSessions = hst.idealSessions ∧
             (prep.finish res?).2.base.usedSendSessions = hst.base.usedSendSessions) := by
  unfold prepareAuthHybridRecvNoOPK at h
  dsimp only at h
  repeat (split at h <;> try cases h)
  refine ⟨fun s hs => List.mem_of_find?_eq_some hs, fun res? => ⟨?_, ?_⟩⟩
  · exact finishAuthHybridRecvNoOPK_idealSessions true P k j l _ _ _ msg _ res?
  · exact finishAuthHybridRecvNoOPK_usedSendSessions true P k j l _ _ _ msg _ res?
theorem support_authCkOtherStep_props {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hNoSendOPK : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (hNoSendNoOPK : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1)
    (hNoRecvOPK : ∀ k j o m, q ≠ .recvOPK k j o m)
    (hNoRecvNoOPK : ∀ k j l m, q ≠ .recvNoOPK k j l m) :
    ∀ x ∈ support (authCkOtherStep S P q hst),
      x.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
      x.2.toAuthHybridState.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions ∧
      x.2.mkSaltCache = hst.mkSaltCache ∧
      x.2.recvCount = hst.recvCount := by
  have hPres : PreservesAt AuthState.usedSendSessions hst.toAuthHybridState.base
      (pqxdhAuthImpl true true S P q) := by
    cases q with
    | sendOPK u i b m0 m1 => exact False.elim (hNoSendOPK u i b m0 m1 rfl)
    | sendNoOPK u i b m0 m1 => exact False.elim (hNoSendNoOPK u i b m0 m1 rfl)
    | recvOPK k j o msg => exact False.elim (hNoRecvOPK k j o msg rfl)
    | recvNoOPK k j l msg => exact False.elim (hNoRecvNoOPK k j l msg rfl)
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
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩
  exact ⟨rfl, hPres (resp, base') hbase, rfl, rfl⟩
structure InvMkTrue (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache) : Prop where
  sentChal_imp : st.1.2 = true → idx < S.N_send_tot ∧ authSlotFired S idx st.1.1 = true
  ideal_msgKeys : ∀ s ∈ st.1.1.toAuthHybridState.idealSessions,
    (sessionSlotIndex s.sid == idx) = true → s.deriveMessageKeys = deriveMsgKeysEff P mkSeedStar s.spqrSalt?
  cache_msgKeys : ∀ e ∈ st.1.1.mkSaltCache,
    (sessionSlotIndex e.1.1 == idx) = true → e.2.2 = deriveMsgKeysEff P mkSeedStar e.1.2
theorem invMkTrue_empty (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes) (secb : Bool)
  :
    InvMkTrue S P idx mkSeedStar ((AuthHybridStateFixed.empty S secb, false), []) where
  sentChal_imp h := by cases h
  ideal_msgKeys _ hs := by cases hs
  cache_msgKeys _ he := by cases he
theorem matchedSameEphMkRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (hWF : WellFormedPrimitivesδ P) (hSaltOK : SaltOK spqrSalt?)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (cache : PrfMkCache) (hsMsg : (sessionSlotIndex s.sid == idx) = true →
      s.deriveMessageKeys = deriveMsgKeysEff P mkSeedStar s.spqrSalt?)
    (hCache : ∀ e ∈ mkSaltCache,
      (sessionSlotIndex e.1.1 == idx) = true → e.2.2 = deriveMsgKeysEff P mkSeedStar e.1.2) :
    ((fun ((mk, mkSaltCache'), _) => (mk, filterOutMkSaltCacheAtIdx idx mkSaltCache')) <$>
      matchedSameEphMkRedProb S P idx (evalPrfMkReal P mkSeedStar) s spqrSalt? recvCount mkSaltCache
        cache) =
      matchedSameEphMkWith P (fun slot => decide (slot < idx))
        (restoreIdealMkAtIdx idx mkSeedStar s) spqrSalt? recvCount
        (filterOutMkSaltCacheAtIdx idx mkSaltCache) ∧
    (∀ x ∈ support (matchedSameEphMkRedProb S P idx (evalPrfMkReal P mkSeedStar) s spqrSalt?
                     recvCount mkSaltCache cache),
      ∀ e ∈ x.1.2, (sessionSlotIndex e.1.1 == idx) = true → e.2.2 = deriveMsgKeysEff P mkSeedStar
        e.1.2) := by
  unfold matchedSameEphMkRedProb matchedSameEphMkWith evalPrfMkReal
  have hSid : (restoreIdealMkAtIdx idx mkSeedStar s).sid = s.sid := by
    unfold restoreIdealMkAtIdx; split <;> rfl
  have hSalt : (restoreIdealMkAtIdx idx mkSeedStar s).spqrSalt? = s.spqrSalt? := by
    unfold restoreIdealMkAtIdx; split <;> rfl
  have hMsg : (restoreIdealMkAtIdx idx mkSeedStar s).deriveMessageKeys = s.deriveMessageKeys := by
    unfold restoreIdealMkAtIdx; split <;> rfl
  dsimp only
  simp only [hSid, hSalt, hMsg]
  cases hIdx : (sessionSlotIndex s.sid == idx)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hLt : sessionSlotIndex s.sid < idx
    · simp only [hLt, decide_true, ↓reduceIte]
      cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [find?_filterOutMkSaltCacheAtIdx_of_ne idx s.sid spqrSalt? hIdx mkSaltCache]
        cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some entry =>
          rcases entry with ⟨k, rc, mk⟩
          dsimp only
          refine ⟨by simp, fun x hx => ?_⟩
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hCache
        | none =>
          dsimp only
          refine ⟨?_, fun x hx => ?_⟩
          · simp [filterOutMkSaltCacheAtIdx_cons_of_ne idx s.sid spqrSalt? _ mkSaltCache hIdx]
          · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨mk, _, rfl⟩
            intro e he hEIdx
            rcases List.mem_cons.mp he with rfl | he'
            · dsimp only at hEIdx
              rw [hIdx] at hEIdx; cases hEIdx
            · exact hCache e he' hEIdx
      · simp only [↓reduceIte]
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact hCache
    · simp only [hLt, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hMk : (restoreIdealMkAtIdx idx mkSeedStar s).mkSeed = s.mkSeed := by
        unfold restoreIdealMkAtIdx; simp [hIdx]
      rw [hMk]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hCache
  · have hLtF : decide (sessionSlotIndex s.sid < idx) = false := decide_lt_of_beq_true hIdx
    have hMk : (restoreIdealMkAtIdx idx mkSeedStar s).mkSeed = mkSeedStar := by
      unfold restoreIdealMkAtIdx; simp [hIdx]
    simp only [↓reduceIte, hLtF, Bool.false_eq_true, hMk]
    cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some entry =>
        rcases entry with ⟨k, rc, mk⟩
        have hMem := List.mem_of_find?_eq_some hFind
        have hPred := List.find?_some hFind
        dsimp only at hPred
        obtain ⟨hKSid, hKSalt⟩ := mkSaltKeyMatch_sameSaltKey hPred
        have hMkEq : mk = P.deriveMsgKeys mkSeedStar spqrSalt? := by
          have hC := hCache (k, (rc, mk)) hMem (by dsimp only; rw [hKSid]; exact hIdx)
          dsimp only at hC
          rw [hC, deriveMsgKeysEff_congr P mkSeedStar hKSalt,
            deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
        subst hMkEq
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact hCache
      | none =>
        dsimp only [Option.map]
        refine ⟨?_, fun x hx => ?_⟩
        · simp [filterOutMkSaltCacheAtIdx_cons_of_eq idx s.sid spqrSalt? _ mkSaltCache hIdx,
            deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
        · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hx
          subst hx
          intro e he hEIdx
          rcases List.mem_cons.mp he with rfl | he'
          · rfl
          · exact hCache e he' hEIdx
    · simp only [↓reduceIte]
      rw [hsMsg hIdx, ← deriveMsgKeysEff_congr P mkSeedStar hSameSalt,
        deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hCache
theorem finishAuthRecvUnmatchedRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (hWF : WellFormedPrimitivesδ P) (hSaltOK : SaltOK spqrSalt?)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hSent : sentChal = true → idx < S.N_send_tot ∧ authSlotFired S idx hst = true)
    (hPrep : ∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
                     (prep.finish res?).2.base.usedSendSessions =
                       hst.toAuthHybridState.base.usedSendSessions) :
    ((fun ((resp, hst'), _) => (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst')) <$>
      finishAuthRecvUnmatchedRedProb S P idx (evalPrfMkReal P mkSeedStar) msg prep
        drKey rk1 spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1)
        hst.mkSaltCache sentChal cache) =
      finishAuthRecvUnmatchedAfterMk P (fun s => if s == idx then pure mkSeedStar else
                                         sampleBytes32)
        (fun s => decide (s < idx)) msg (restorePreparedAuthRecvMk idx mkSeedStar prep)
        drKey rk1 spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1)
        (filterOutMkSaltCacheAtIdx idx hst.mkSaltCache) ∧
    (∀ x ∈ support (finishAuthRecvUnmatchedRedProb S P idx (evalPrfMkReal P mkSeedStar) msg prep
        drKey rk1 spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1)
        hst.mkSaltCache sentChal cache),
      (sentChal = true → idx < S.N_send_tot ∧ authSlotFired S idx x.1.2 = true) ∧
      x.1.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
      x.1.2.mkSaltCache = hst.mkSaltCache) := by
  unfold finishAuthRecvUnmatchedRedProb finishAuthRecvUnmatchedAfterMk evalPrfMkReal
  dsimp only
  cases hIdx : (S.N_send_tot + hst.recvCount == idx)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hLt : decide (S.N_send_tot + hst.recvCount < idx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp [map_bind, finishAuthRecvMk_restorePreparedAuthRecvMk], fun x hx => ?_⟩
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
      refine ⟨fun hS => ⟨(hSent hS).1, ?_⟩, (hPrep _).1, rfl⟩
      exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hSent hS).2 (hPrep _).2
        (Nat.le_succ _)
    · simp only [↓reduceIte]
      refine ⟨by simp [map_bind, finishAuthRecvMk_restorePreparedAuthRecvMk], fun x hx => ?_⟩
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      refine ⟨fun hS => ⟨(hSent hS).1, ?_⟩, (hPrep _).1, rfl⟩
      exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hSent hS).2 (hPrep _).2
        (Nat.le_succ _)
  · obtain ⟨_, hSC⟩ := sentChal_false_of_recv_slot (hst := hst) (sentChal := sentChal) hSent hIdx
    have hLtF : decide (S.N_send_tot + hst.recvCount < idx) = false := decide_lt_of_beq_true hIdx
    simp only [↓reduceIte, hSC, Bool.not_false, hLtF, Bool.false_eq_true, pure_bind]
    refine ⟨by simp [finishAuthRecvMk_restorePreparedAuthRecvMk,
      deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK], fun x hx => ?_⟩
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨ck1_1, _, rfl⟩
    exact ⟨False.elim, (hPrep _).1, rfl⟩
theorem authMkRecvRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hWF : WellFormedPrimitivesδ P)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkTrue S P idx mkSeedStar ((hst, sentChal), cache))
    (hPrepProps : ∀ prep, prep? = some prep →
      (∀ s, prep.matchedSess? = some s → s ∈ hst.toAuthHybridState.idealSessions) ∧
      (∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
               (prep.finish res?).2.base.usedSendSessions =
                 hst.toAuthHybridState.base.usedSendSessions)) :
    ((fun ((resp, hst'), _) => (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst')) <$>
      authMkRecvRedProb S P idx (evalPrfMkReal P mkSeedStar) msg prep? hst sentChal cache) =
      authMkRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (prep?.map (restorePreparedAuthRecvMk idx mkSeedStar))
        (restoreAuthFixedMkAtIdx idx mkSeedStar hst) ∧
    (∀ x ∈ support (authMkRecvRedProb S P idx (evalPrfMkReal P mkSeedStar) msg prep? hst sentChal
                     cache),
      InvMkTrue S P idx mkSeedStar ((x.1.2, sentChal), x.2)) := by
  cases hP : prep? with
  | none =>
    unfold authMkRecvRedProb authMkRecvWith restoreAuthFixedMkAtIdx
    dsimp only
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
             authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2 rfl
               (Nat.le_succ _)⟩,
           hInv.ideal_msgKeys, hInv.cache_msgKeys⟩
  | some prep =>
    obtain ⟨hMatchMem, hFinProps⟩ := hPrepProps prep hP
    unfold authMkRecvRedProb authMkRecvWith
    dsimp only [Option.map]
    have hMatch : (restorePreparedAuthRecvMk idx mkSeedStar prep).matchedSess? =
        prep.matchedSess?.map (restoreIdealMkAtIdx idx mkSeedStar) := rfl
    have hHon : (restorePreparedAuthRecvMk idx mkSeedStar prep).isUncorruptedHonestSender =
        prep.isUncorruptedHonestSender := rfl
    have hEph : (restorePreparedAuthRecvMk idx mkSeedStar prep).sameEph = prep.sameEph := rfl
    have hSec : (restorePreparedAuthRecvMk idx mkSeedStar prep).secrets = prep.secrets := rfl
    have hDh : (restorePreparedAuthRecvMk idx mkSeedStar prep).dhRatchet = prep.dhRatchet := rfl
    have hKE : (restorePreparedAuthRecvMk idx mkSeedStar prep).kEntry = prep.kEntry := rfl
    have hRo : (restorePreparedAuthRecvMk idx mkSeedStar prep).hstDec.base.roCache =
        prep.hstDec.base.roCache := rfl
    have hRootRo : (restorePreparedAuthRecvMk idx mkSeedStar prep).hstDec.base.rootRoCache =
        prep.hstDec.base.rootRoCache := rfl
    have hRC : (restoreAuthFixedMkAtIdx idx mkSeedStar hst).recvCount = hst.recvCount := rfl
    have hMC : (restoreAuthFixedMkAtIdx idx mkSeedStar hst).mkSaltCache =
        filterOutMkSaltCacheAtIdx idx hst.mkSaltCache := rfl
    have hFinNone :
        ((prep.finish none).1,
         restoreAuthFixedMkAtIdx idx mkSeedStar
           { toAuthHybridState := (prep.finish none).2,
             recvCount := hst.recvCount + 1,
             mkSaltCache := hst.mkSaltCache }) =
        (((restorePreparedAuthRecvMk idx mkSeedStar prep).finish none).1,
         { toAuthHybridState := ((restorePreparedAuthRecvMk idx mkSeedStar prep).finish none).2,
           recvCount := hst.recvCount + 1,
           mkSaltCache := filterOutMkSaltCacheAtIdx idx hst.mkSaltCache }) := by
      simp [restorePreparedAuthRecvMk, restoreAuthFixedMkAtIdx]
    have hInvNone : InvMkTrue S P idx mkSeedStar
        (({ toAuthHybridState := (prep.finish none).2,
            recvCount := hst.recvCount + 1,
            mkSaltCache := hst.mkSaltCache }, sentChal), cache) := by
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                  (hFinProps none).2 (Nat.le_succ _)⟩,
              ?_, hInv.cache_msgKeys⟩
      rw [(hFinProps none).1]
      exact hInv.ideal_msgKeys
    simp only [hMatch, hHon, hEph, hSec, hDh, hKE, hRo, hRootRo, hRC, hMC, Option.isSome_map]
    split
    · cases hMS : prep.matchedSess? with
      | some s =>
        have hsMem : s ∈ hst.toAuthHybridState.idealSessions := hMatchMem s hMS
        have hDr : (restoreIdealMkAtIdx idx mkSeedStar s).drKey = s.drKey := by
          unfold restoreIdealMkAtIdx; split <;> rfl
        have hRk1 : (restoreIdealMkAtIdx idx mkSeedStar s).rk1 = s.rk1 := by
          unfold restoreIdealMkAtIdx; split <;> rfl
        have hCk : (restoreIdealMkAtIdx idx mkSeedStar s).ck1_1 = s.ck1_1 := by
          unfold restoreIdealMkAtIdx; split <;> rfl
        dsimp only [Option.map]
        rw [hDr, hRk1, hCk]
        split
        · cases hR : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            refine ⟨by simp [hFinNone], fun x hx => ?_⟩
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvNone
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            obtain ⟨hEqM, hSuppM⟩ := matchedSameEphMkRedProb_evalPrfMkReal P idx mkSeedStar s
              spqrSalt?
              hst.recvCount hWF (saltOK_of_spqrInitRecv hWF hR) hst.mkSaltCache cache
              (hInv.ideal_msgKeys s hsMem) hInv.cache_msgKeys
            refine ⟨?_, fun x hx => ?_⟩
            · trans ((fun (deriveMessageKeys, mkSaltCache') =>
                  finishAuthRecvMk P msg (restorePreparedAuthRecvMk idx mkSeedStar prep)
                    s.drKey s.rk1 s.ck1_1 (hst.recvCount + 1) mkSaltCache' deriveMessageKeys) <$>
                matchedSameEphMkWith P (fun slot => decide (slot < idx))
                  (restoreIdealMkAtIdx idx mkSeedStar s)
                  spqrSalt? hst.recvCount (filterOutMkSaltCacheAtIdx idx hst.mkSaltCache))
              · rw [← hEqM, Functor.map_map, bind_pure_comp, Functor.map_map]
                congr 1
              · unfold matchedSameEphMkWith
                split
                · split
                  · simp
                  · cases List.find? (fun (x : (SessionId S × Option Bytes) × ℕ × MessageKeys) =>
                        match x with
                        | (k, _) => mkSaltKeyMatch k (restoreIdealMkAtIdx idx mkSeedStar s).sid
                                      spqrSalt?)
                        (filterOutMkSaltCacheAtIdx idx hst.mkSaltCache) with
                    | none => simp
                    | some entry => rcases entry with ⟨_, _, _⟩; simp
                · simp
            · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨⟨⟨mk, mkSaltCache'⟩, cache'⟩, hMemM, rfl⟩
              refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                        authSlotFired_of_usedSendSessions_eq_and_recvCount_le
                          (hInv.sentChal_imp hS).2
                          (hFinProps _).2 (Nat.le_succ _)⟩,
                      ?_, hSuppM _ hMemM⟩
              unfold finishAuthRecvMk; dsimp only
              rw [(hFinProps _).1]
              exact hInv.ideal_msgKeys
        · refine ⟨?_, fun x hx => ?_⟩
          · simp only [map_bind]
            congr 1; funext rk1
            cases hR : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              dsimp only; simp [hFinNone]
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact (finishAuthRecvUnmatchedRedProb_evalPrfMkReal P idx mkSeedStar msg prep
                s.drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
                hInv.sentChal_imp hFinProps).1
          · simp only [MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨rk1, _, hx⟩
            revert x hx
            cases hR : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
              subst hx; exact hInvNone
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              intro x hx
              obtain ⟨hS', hId', hCa'⟩ := (finishAuthRecvUnmatchedRedProb_evalPrfMkReal P idx
                                            mkSeedStar msg prep
                s.drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
                hInv.sentChal_imp hFinProps).2 x hx
              exact ⟨hS', hId' ▸ hInv.ideal_msgKeys, hCa' ▸ hInv.cache_msgKeys⟩
      | none =>
        dsimp only [Option.map]
        refine ⟨?_, fun x hx => ?_⟩
        · simp only [map_bind]
          congr 1; funext drKey
          congr 1; funext rk1
          cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only; simp [hFinNone]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (finishAuthRecvUnmatchedRedProb_evalPrfMkReal P idx mkSeedStar msg prep
              drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
              hInv.sentChal_imp hFinProps).1
        · simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩
          revert x hx
          cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvNone
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            intro x hx
            obtain ⟨hS', hId', hCa'⟩ := (finishAuthRecvUnmatchedRedProb_evalPrfMkReal P idx
                                          mkSeedStar msg prep
              drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
              hInv.sentChal_imp hFinProps).2 x hx
            exact ⟨hS', hId' ▸ hInv.ideal_msgKeys, hCa' ▸ hInv.cache_msgKeys⟩
    · refine ⟨?_, fun x hx => ?_⟩
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          dsimp only; simp [hFinNone]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only
          simp [restorePreparedAuthRecvMk, restoreAuthFixedMkAtIdx]
      · simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
        revert x hx
        cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hInvNone
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                    authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                      (hFinProps _).2 (Nat.le_succ _)⟩,
                  ?_, hInv.cache_msgKeys⟩
          rw [(hFinProps _).1]
          exact hInv.ideal_msgKeys
theorem authMkSendRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hWF : WellFormedPrimitivesδ P)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkTrue S P idx mkSeedStar ((hst, sentChal), cache)) :
    ((fun (resp, ((hst', _), _)) => (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst')) <$>
      authMkSendRedProb S P idx (evalPrfMkReal P mkSeedStar) sid u bundle m0 m1 hst sentChal cache)
        =
      authMkSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) sid u bundle m0 m1
        (restoreAuthFixedMkAtIdx idx mkSeedStar hst) ∧
    (∀ x ∈ support (authMkSendRedProb S P idx (evalPrfMkReal P mkSeedStar) sid u bundle m0 m1 hst
                     sentChal cache),
      InvMkTrue S P idx mkSeedStar x.2) := by
  have hEq :
      ((fun (resp, ((hst', _), _)) => (resp, restoreAuthFixedMkAtIdx idx mkSeedStar hst')) <$>
        authMkSendRedProb S P idx (evalPrfMkReal P mkSeedStar) sid u bundle m0 m1 hst sentChal
          cache) =
        authMkSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
          (fun s => decide (s < idx)) sid u bundle m0 m1
          (restoreAuthFixedMkAtIdx idx mkSeedStar hst) := by
    unfold authMkSendRedProb authMkSendWith finishAuthSendAfterMk evalPrfMkReal
    rw [prepareAuthSendMk_restoreAuthFixedMkAtIdx, bind_map_left, map_bind]
    refine bind_congr_of_support (prepareAuthSendMk S P sid u bundle m0 m1 hst) _ _
      (fun prep hPrep => ?_)
    have hP := support_prepareAuthSendMk_full_props P sid u bundle m0 m1 hst prep hPrep
    cases prep with
    | done resp hst' =>
      simp [PreparedAuthSend.mapState]
    | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
        pqRatchetMsg msgPlain =>
      dsimp only [PreparedAuthSend.mapState]
      cases hIdx : (sessionSlotIndex sid == idx)
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases hLt : decide (sessionSlotIndex sid < idx)
        · simp only [Bool.false_eq_true, ↓reduceIte, map_bind]
          congr 1; funext mkSeed
          congr 1; funext ck1_1
          simp [finishAuthSendMk_restoreAuthFixedMkAtIdx_ne P idx mkSeedStar sid hIdx]
        · simp only [↓reduceIte, map_bind]
          congr 1; funext ck1_1
          congr 1; funext deriveMessageKeys
          simp [finishAuthSendMk_restoreAuthFixedMkAtIdx_ne P idx mkSeedStar sid hIdx]
      · obtain ⟨_, hSC⟩ := sentChal_false_of_send_idealMk (hst := hst) (sentChal := sentChal)
          hInv.sentChal_imp hSend hP.1 hIdx
        have hLtF : decide (sessionSlotIndex sid < idx) = false := decide_lt_of_beq_true hIdx
        simp only [hSC, hLtF, Bool.not_false, Bool.true_and, ↓reduceIte, Bool.false_eq_true,
                    pure_bind, map_bind]
        congr 1; funext ck1_1
        simp [finishAuthSendMk_restoreAuthFixedMkAtIdx_eq P idx mkSeedStar sid hIdx,
          deriveMsgKeysEff_eq hWF mkSeedStar (hP.2 hWF)]
  refine ⟨hEq, fun x hx => ?_⟩
  have hFiredMono : authSlotFired S idx hst = true → authSlotFired S idx x.2.1.1 = true := by
    intro hF
    have hFRest : authSlotFired S idx (restoreAuthFixedMkAtIdx idx mkSeedStar hst) = true := by
      simpa using hF
    have hMemMap : (x.1, restoreAuthFixedMkAtIdx idx mkSeedStar x.2.1.1) ∈
        support (authMkSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
          (fun s => decide (s < idx)) sid u bundle m0 m1
          (restoreAuthFixedMkAtIdx idx mkSeedStar hst)) := by
      rw [← hEq]
      simp only [support_map, Set.mem_image]
      exact ⟨x, hx, rfl⟩
    have hF' := authMkSendWith_slotFired_mono S P idx _ _ sid u bundle m0 m1
      (restoreAuthFixedMkAtIdx idx mkSeedStar hst) hFRest _ hMemMap
    simpa using hF'
  unfold authMkSendRedProb evalPrfMkReal at hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hPrep, hx⟩
  have hP := support_prepareAuthSendMk_full_props P sid u bundle m0 m1 hst prep hPrep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, hFiredMono (hInv.sentChal_imp hS).2⟩,
           hP.1 ▸ hInv.ideal_msgKeys,
           hP.2.1 ▸ hInv.cache_msgKeys⟩
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
      pqRatchetMsg msgPlain =>
    dsimp only at hx
    cases hIdx : (sessionSlotIndex sid == idx)
    · rw [hIdx] at hx
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hx
      cases hLt : decide (sessionSlotIndex sid < idx)
      · rw [hLt] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        obtain ⟨hMC, _, _, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal? bundle m0
          m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlain
          hst (P.deriveMsgKeys mkSeed spqrSalt?)
        refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, hFiredMono (hInv.sentChal_imp hS).2⟩,
                ?_, hMC ▸ hInv.cache_msgKeys⟩
        rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
        · rw [hIdEq]; exact hInv.ideal_msgKeys
        · rw [hIdCons]
          intro s hs hsIdx
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsSid, hIdx] at hsIdx; cases hsIdx
          · exact hInv.ideal_msgKeys s hs' hsIdx
      · rw [hLt] at hx
        simp only [↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        obtain ⟨hMC, _, _, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal? bundle m0
          m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain
          hst deriveMessageKeys
        refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, hFiredMono (hInv.sentChal_imp hS).2⟩,
                ?_, hMC ▸ hInv.cache_msgKeys⟩
        rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
        · rw [hIdEq]; exact hInv.ideal_msgKeys
        · rw [hIdCons]
          intro s hs hsIdx
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsSid, hIdx] at hsIdx; cases hsIdx
          · exact hInv.ideal_msgKeys s hs' hsIdx
    · obtain ⟨_, hSC⟩ := sentChal_false_of_send_idealMk (hst := hst) (sentChal := sentChal)
        hInv.sentChal_imp hSend hP.1 hIdx
      rw [hSC, hIdx] at hx
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, rfl⟩
      obtain ⟨hMC, _, _, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal? bundle m0
        m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain
        hst (deriveMsgKeysEff P mkSeedStar spqrSalt?)
      have hSlot : sendSlotIndex? sid = some idx := by
        rw [sendSlotIndex?_of_isSendSessionId hSend, beq_iff_eq.mp hIdx]
      refine ⟨fun _ => ⟨sendSlotIndex?_lt hSlot,
                authSlotFired_finishAuthSendMk_self P idx sid uEntry peerPrincipal? bundle m0 m1
                  ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg
                    msgPlain
                  hst (deriveMsgKeysEff P mkSeedStar spqrSalt?) hSlot⟩,
              ?_, hMC ▸ hInv.cache_msgKeys⟩
      rcases hId with hIdEq | ⟨s0, _, _, hsSalt, hsMk, hIdCons⟩
      · rw [hIdEq]; exact hInv.ideal_msgKeys
      · rw [hIdCons]
        intro s hs hsIdx
        rcases List.mem_cons.mp hs with rfl | hs'
        · rw [hsMk, hsSalt]
        · exact hInv.ideal_msgKeys s hs' hsIdx
theorem authMkStepRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hWF : WellFormedPrimitivesδ P)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkTrue S P idx mkSeedStar st) :
    ((prfMkAuthImpl S P idx mkSeedStar q).run (restoreAuthFixedMkAtIdx idx mkSeedStar st.1.1) =
      Prod.map id (fun ((hst', _), _) => restoreAuthFixedMkAtIdx idx mkSeedStar hst') <$>
        ((authMkRedProbImpl S P idx (evalPrfMkReal P mkSeedStar) q).run st)) ∧
    (∀ x ∈ support ((authMkRedProbImpl S P idx (evalPrfMkReal P mkSeedStar) q).run st),
      InvMkTrue S P idx mkSeedStar x.2) := by
  rcases st with ⟨⟨hst, sentChal⟩, cache⟩
  dsimp only [prfMkAuthImpl, authMkRedProbImpl, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSendRedProb_evalPrfMkReal P idx mkSeedStar (.sendOPK u i)
        trivial hWF
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSendRedProb_evalPrfMkReal P idx mkSeedStar (.sendNoOPK u i)
        trivial hWF
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | recvOPK k j o msg =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    change (authMkRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (prepareAuthHybridRecvOPK true P k j o msg (restoreAuthMkAtIdx idx mkSeedStar
                                                     hst.toAuthHybridState))
        (restoreAuthFixedMkAtIdx idx mkSeedStar hst) = _) ∧ _
    rw [prepareAuthHybridRecvOPK_restoreAuthMkAtIdx]
    obtain ⟨hEq, hSupp⟩ := authMkRecvRedProb_evalPrfMkReal P idx mkSeedStar msg
      (hWF := hWF)
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst sentChal cache hInv
      (prepareAuthHybridRecvOPK_props P k j o msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]
      simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | recvNoOPK k j l msg =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    change (authMkRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (prepareAuthHybridRecvNoOPK true P k j l msg (restoreAuthMkAtIdx idx mkSeedStar
                                                       hst.toAuthHybridState))
        (restoreAuthFixedMkAtIdx idx mkSeedStar hst) = _) ∧ _
    rw [prepareAuthHybridRecvNoOPK_restoreAuthMkAtIdx]
    obtain ⟨hEq, hSupp⟩ := authMkRecvRedProb_evalPrfMkReal P idx mkSeedStar msg
      (hWF := hWF)
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst sentChal cache hInv
      (prepareAuthHybridRecvNoOPK_props P k j l msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]
      simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _ 
          | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · rw [authCkOtherStep_restoreAuthFixedMkAtIdx]
      simp [Prod.map, map_eq_bind_pure_comp]
      rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, ?_⟩,
              hOther.1 ▸ hInv.ideal_msgKeys, hOther.2.2.1 ▸ hInv.cache_msgKeys⟩
      exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
        hOther.2.1 (by dsimp only; rw [hOther.2.2.2])
theorem evalDist_prfMsgKeysWorld_true_at_idx (S : Setup) (P : Primitives) (idx : Nat)
    (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[(do
        let mkSeedStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkRedProbImpl S P idx (evalPrfMkReal P mkSeedStar)
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkCutoffExp S P idx A] := by
  rw [← evalDist_preSample_authMk_eq_cutoff S P idx A]
  refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun mkSeedStar _ => ?_)
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hInit : AuthHybridStateFixed.empty S secb =
      restoreAuthFixedMkAtIdx idx mkSeedStar (AuthHybridStateFixed.empty S secb) := rfl
  congr 1
  symm
  rw [hInit]
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => restoreAuthFixedMkAtIdx idx mkSeedStar hst) (InvMkTrue S P idx mkSeedStar)
    (authMkRedProbImpl S P idx (evalPrfMkReal P mkSeedStar)) (prfMkAuthImpl S P idx mkSeedStar)
    (fun q st hInv => authMkStepRedProb_evalPrfMkReal P idx mkSeedStar q hWF st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), []) (invMkTrue_empty S P idx mkSeedStar secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState) (fun _ _ => rfl)
structure InvMkFalse (S : Setup) (idx : Nat)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache) : Prop where
  sentChal_imp : st.1.2 = true → idx < S.N_send_tot ∧ authSlotFired S idx st.1.1 = true
  unfired_cache_nil : authSlotFired S idx st.1.1 = false → st.2 = []
  ideal_send : ∀ s ∈ st.1.1.toAuthHybridState.idealSessions,
    IsSendSessionId S s.sid ∧ st.1.1.toAuthHybridState.base.usedSendSessions.contains s.sid = true
  ideal_unique : ∀ s1 ∈ st.1.1.toAuthHybridState.idealSessions,
    ∀ s2 ∈ st.1.1.toAuthHybridState.idealSessions,
    (sessionSlotIndex s1.sid == idx) = true → (sessionSlotIndex s2.sid == idx) = true → s1 = s2
  cache_sub_mkSaltCache : ∀ s ∈ st.1.1.toAuthHybridState.idealSessions,
    (sessionSlotIndex s.sid == idx) = true →
    ∀ salt? : Option Bytes, sameSaltKey salt? s.spqrSalt? = false →
    st.1.1.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid salt?) = none →
    st.2.find? (fun (s', _) => s' == effectiveHkdfSaltBytes salt?) = none
theorem invMkFalse_empty (S : Setup) (idx : Nat) (secb : Bool) :
    InvMkFalse S idx ((AuthHybridStateFixed.empty S secb, false), []) where
  sentChal_imp h := by cases h
  unfired_cache_nil _ := rfl
  ideal_send _ hs := by cases hs
  ideal_unique _ hs := by cases hs
  cache_sub_mkSaltCache _ hs := by cases hs
theorem sessionSlotIndex_ne_of_ideal_fresh {S : Setup} {hst : AuthHybridStateFixed S}
    {s : IdealAuthSession S} {sid : SessionId S}
    (hIdeal : IsSendSessionId S s.sid ∧ hst.toAuthHybridState.base.usedSendSessions.contains s.sid =
      true)
    (hSend : IsSendSessionId S sid)
    (hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = false) :
    sessionSlotIndex s.sid ≠ sessionSlotIndex sid := by
  intro hEq
  have h1 : sendSlotIndex? s.sid = some (sessionSlotIndex sid) := by
    rw [sendSlotIndex?_of_isSendSessionId hIdeal.1, hEq]
  have h2 : sendSlotIndex? sid = some (sessionSlotIndex sid) :=
    sendSlotIndex?_of_isSendSessionId hSend
  have hSid : s.sid = sid := sendSlotIndex?_inj h1 h2
  rw [hSid, hCont] at hIdeal
  cases hIdeal.2
theorem authSlotFired_of_ideal_slot {S : Setup} {idx : Nat} {hst : AuthHybridStateFixed S}
    {s : IdealAuthSession S}
    (hIdeal : IsSendSessionId S s.sid ∧ hst.toAuthHybridState.base.usedSendSessions.contains s.sid =
      true)
    (hIdx : (sessionSlotIndex s.sid == idx) = true) :
    authSlotFired S idx hst = true := by
  have hEq : sessionSlotIndex s.sid = idx := beq_iff_eq.mp hIdx
  have hSlot : sendSlotIndex? s.sid = some idx := by
    rw [sendSlotIndex?_of_isSendSessionId hIdeal.1, hEq]
  have hlt : idx < S.N_send_tot := sendSlotIndex?_lt hSlot
  unfold authSlotFired
  simp only [hlt, ↓reduceIte, List.any_eq_true]
  exact ⟨s.sid, List.contains_iff_mem.mp hIdeal.2, beq_iff_eq.mpr hSlot⟩
theorem matchedSameEphMkRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (cache : PrfMkCache)
    (hCacheSub : (sessionSlotIndex s.sid == idx) = true →
      ∀ salt? : Option Bytes, sameSaltKey salt? s.spqrSalt? = false →
      mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid salt?) = none →
      cache.find? (fun (s', _) => s' == effectiveHkdfSaltBytes salt?) = none) :
    (Prod.fst <$>
      matchedSameEphMkRedProb S P idx evalPrfMkIdeal s spqrSalt? recvCount mkSaltCache cache) =
      matchedSameEphMkWith P (fun slot => decide (slot < idx + 1)) s spqrSalt? recvCount mkSaltCache
        ∧
    (∀ x ∈ support (matchedSameEphMkRedProb S P idx evalPrfMkIdeal s spqrSalt? recvCount mkSaltCache
                     cache),
      ((sessionSlotIndex s.sid == idx) = false → x.2 = cache ∧
        ∀ s1 : IdealAuthSession S, (sessionSlotIndex s1.sid == idx) = true →
          ∀ salt? : Option Bytes,
          x.1.2.find? (fun (k, _) => mkSaltKeyMatch k s1.sid salt?) =
            mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s1.sid salt?)) ∧
      ((sessionSlotIndex s.sid == idx) = true →
        ∀ salt? : Option Bytes, sameSaltKey salt? s.spqrSalt? = false →
        x.1.2.find? (fun (k, _) => mkSaltKeyMatch k s.sid salt?) = none →
        x.2.find? (fun (s', _) => s' == effectiveHkdfSaltBytes salt?) = none)) := by
  unfold matchedSameEphMkRedProb matchedSameEphMkWith evalPrfMkIdeal
  dsimp only
  cases hIdx : (sessionSlotIndex s.sid == idx)
  · simp only [decide_lt_succ_of_beq_false hIdx, Bool.false_eq_true, ↓reduceIte]
    cases hLt : decide (sessionSlotIndex s.sid < idx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨fun _ => ⟨rfl, fun _ _ _ => rfl⟩, False.elim⟩
    · simp only [↓reduceIte]
      cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some entry =>
          rcases entry with ⟨k, rc, mk⟩
          dsimp only
          refine ⟨by simp, fun x hx => ?_⟩
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨fun _ => ⟨rfl, fun _ _ _ => rfl⟩, False.elim⟩
        | none =>
          dsimp only
          refine ⟨by simp, fun x hx => ?_⟩
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨mk, _, rfl⟩
          refine ⟨fun _ => ⟨rfl, fun s1 hs1 salt? => ?_⟩, False.elim⟩
          have hPairNe : mkSaltKeyMatch (s.sid, spqrSalt?) s1.sid salt? = false := by
            apply mkSaltKeyMatch_of_sid_ne
            intro hSidEq
            dsimp only at hSidEq
            rw [← hSidEq] at hs1
            exact Bool.noConfusion (hIdx.symm.trans hs1)
          rw [List.find?_cons]
          dsimp only
          rw [hPairNe]
      · simp only [↓reduceIte]
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨fun _ => ⟨rfl, fun _ _ _ => rfl⟩, False.elim⟩
  · simp only [decide_lt_succ_of_beq_true hIdx, ↓reduceIte]
    cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some entry =>
        rcases entry with ⟨k, rc, mk⟩
        dsimp only
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨fun h => Bool.noConfusion h, fun _ => hCacheSub hIdx⟩
      | none =>
        have hCacheNone : cache.find? (fun (s', _) => s' == effectiveHkdfSaltBytes spqrSalt?) = none :=
          hCacheSub hIdx spqrSalt? hSameSalt hFind
        rw [hCacheNone]
        dsimp only
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
                    Set.mem_singleton_iff] at hx
        rcases hx with ⟨mk, _, rfl⟩
        refine ⟨fun h => Bool.noConfusion h, fun _ salt? hSaltNe hFindCons => ?_⟩
        have hHead : mkSaltKeyMatch (s.sid, spqrSalt?) s.sid salt? =
            (effectiveHkdfSaltBytes spqrSalt? == effectiveHkdfSaltBytes salt?) := by
          simp [mkSaltKeyMatch, sameSaltKey]
        rw [List.find?_cons] at hFindCons ⊢
        dsimp only at hFindCons ⊢
        rw [hHead] at hFindCons
        cases hb : (effectiveHkdfSaltBytes spqrSalt? == effectiveHkdfSaltBytes salt?)
        · rw [hb] at hFindCons
          exact hCacheSub hIdx salt? hSaltNe hFindCons
        · rw [hb] at hFindCons; cases hFindCons
    · simp only [↓reduceIte]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨fun h => Bool.noConfusion h, fun _ => hCacheSub hIdx⟩
theorem finishAuthRecvUnmatchedRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkFalse S idx ((hst, sentChal), cache))
    (hPrep : ∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
                     (prep.finish res?).2.base.usedSendSessions =
                       hst.toAuthHybridState.base.usedSendSessions) :
    (Prod.fst <$>
      finishAuthRecvUnmatchedRedProb S P idx evalPrfMkIdeal msg prep
        drKey rk1 spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1)
        hst.mkSaltCache sentChal cache) =
      finishAuthRecvUnmatchedAfterMk P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) msg prep
        drKey rk1 spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1)
        hst.mkSaltCache ∧
    (∀ x ∈ support (finishAuthRecvUnmatchedRedProb S P idx evalPrfMkIdeal msg prep
        drKey rk1 spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1)
        hst.mkSaltCache sentChal cache),
      InvMkFalse S idx ((x.1.2, sentChal), x.2)) := by
  unfold finishAuthRecvUnmatchedRedProb finishAuthRecvUnmatchedAfterMk evalPrfMkIdeal
  dsimp only
  cases hIdx : (S.N_send_tot + hst.recvCount == idx)
  · simp only [decide_lt_succ_of_beq_false hIdx, Bool.false_eq_true, ↓reduceIte]
    cases hLt : decide (S.N_send_tot + hst.recvCount < idx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp [map_bind], fun x hx => ?_⟩
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
      unfold finishAuthRecvMk
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                  (hPrep _).2 (Nat.le_succ _)⟩,
              fun hNF => hInv.unfired_cache_nil
                (authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le
                (hPrep _).2 (Nat.le_succ _) hNF),
              ?_, (hPrep _).1 ▸ hInv.ideal_unique, (hPrep _).1 ▸ hInv.cache_sub_mkSaltCache⟩
      dsimp only
      rw [(hPrep _).1, (hPrep _).2]
      exact hInv.ideal_send
    · simp only [↓reduceIte]
      refine ⟨by simp [map_bind], fun x hx => ?_⟩
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      unfold finishAuthRecvMk
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                  (hPrep _).2 (Nat.le_succ _)⟩,
              fun hNF => hInv.unfired_cache_nil
                (authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le
                (hPrep _).2 (Nat.le_succ _) hNF),
              ?_, (hPrep _).1 ▸ hInv.ideal_unique, (hPrep _).1 ▸ hInv.cache_sub_mkSaltCache⟩
      dsimp only
      rw [(hPrep _).1, (hPrep _).2]
      exact hInv.ideal_send
  · obtain ⟨hNF, hSC⟩ := sentChal_false_of_recv_slot (hst := hst) (sentChal := sentChal)
      hInv.sentChal_imp hIdx
    have hCacheNil : cache = [] := hInv.unfired_cache_nil hNF
    simp only [decide_lt_succ_of_beq_true hIdx, hCacheNil, ↓reduceIte, hSC, Bool.not_false,
                List.find?_nil, bind_assoc, pure_bind]
    refine ⟨by simp [map_bind], fun x hx => ?_⟩
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
    have hFired' : authSlotFired S idx
        (finishAuthRecvMk P msg prep drKey rk1 ck1_1 (hst.recvCount + 1) hst.mkSaltCache deriveMessageKeys).2
          = true :=
      authSlotFired_finishAuthRecvMk_self P idx msg prep drKey rk1 ck1_1 hst hst.mkSaltCache
        deriveMessageKeys (beq_iff_eq.mp hIdx)
    refine ⟨(by intro hS; cases hS),
            (by intro hF; rw [hFired'] at hF; cases hF),
            ?_, ?_, ?_⟩
    · unfold finishAuthRecvMk; dsimp only
      rw [(hPrep _).1, (hPrep _).2]
      exact hInv.ideal_send
    · unfold finishAuthRecvMk; dsimp only
      rw [(hPrep _).1]
      exact hInv.ideal_unique
    · unfold finishAuthRecvMk; dsimp only
      rw [(hPrep _).1]
      intro s hs hsIdx
      have hFiredOld := authSlotFired_of_ideal_slot (hInv.ideal_send s hs) hsIdx
      rw [hNF] at hFiredOld; cases hFiredOld
theorem authMkRecvRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkFalse S idx ((hst, sentChal), cache)) (hPrepProps : ∀ prep, prep? = some prep →
      (∀ s, prep.matchedSess? = some s → s ∈ hst.toAuthHybridState.idealSessions) ∧
      (∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
               (prep.finish res?).2.base.usedSendSessions =
                 hst.toAuthHybridState.base.usedSendSessions)) :
    (Prod.fst <$>
      authMkRecvRedProb S P idx evalPrfMkIdeal msg prep? hst sentChal cache) =
      authMkRecvWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) msg prep? hst ∧
    (∀ x ∈ support (authMkRecvRedProb S P idx evalPrfMkIdeal msg prep? hst sentChal cache),
      InvMkFalse S idx ((x.1.2, sentChal), x.2)) := by
  cases hP : prep? with
  | none =>
    unfold authMkRecvRedProb authMkRecvWith
    dsimp only
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    have hUsedEq : ({ hst with recvCount := hst.recvCount + 1 } : AuthHybridStateFixed
                     S).toAuthHybridState.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions := rfl
    have hRCLe : hst.recvCount ≤ ({ hst with recvCount := hst.recvCount + 1 } : AuthHybridStateFixed
                                   S).recvCount :=
      Nat.le_succ hst.recvCount
    exact ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
             authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2 hUsedEq
               hRCLe⟩,
           fun hNF => hInv.unfired_cache_nil
             (authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le hUsedEq hRCLe hNF),
           hInv.ideal_send, hInv.ideal_unique, hInv.cache_sub_mkSaltCache⟩
  | some prep =>
    obtain ⟨hMatchMem, hFinProps⟩ := hPrepProps prep hP
    unfold authMkRecvRedProb authMkRecvWith
    dsimp only
    have hInvNone : InvMkFalse S idx
        (({ toAuthHybridState := (prep.finish none).2,
            recvCount := hst.recvCount + 1,
            mkSaltCache := hst.mkSaltCache }, sentChal), cache) := by
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                  (hFinProps none).2 (Nat.le_succ _)⟩,
              fun hNF => hInv.unfired_cache_nil
                (authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le
                (hFinProps none).2 (Nat.le_succ _) hNF),
              ?_, (hFinProps none).1 ▸ hInv.ideal_unique, (hFinProps none).1 ▸
                hInv.cache_sub_mkSaltCache⟩
      dsimp only
      rw [(hFinProps none).1, (hFinProps none).2]
      exact hInv.ideal_send
    split
    · cases hMS : prep.matchedSess? with
      | some s =>
        have hsMem : s ∈ hst.toAuthHybridState.idealSessions := hMatchMem s hMS
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            refine ⟨by simp, fun x hx => ?_⟩
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvNone
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            obtain ⟨hEqM, hSuppM⟩ := matchedSameEphMkRedProb_evalPrfMkIdeal P idx s spqrSalt?
              hst.recvCount hst.mkSaltCache cache (hInv.cache_sub_mkSaltCache s hsMem)
            refine ⟨?_, fun x hx => ?_⟩
            · trans ((fun (deriveMessageKeys, mkSaltCache') =>
                  finishAuthRecvMk P msg prep s.drKey s.rk1 s.ck1_1 (hst.recvCount + 1) mkSaltCache'
                    deriveMessageKeys) <$>
                matchedSameEphMkWith P (fun slot => decide (slot < idx + 1)) s spqrSalt?
                  hst.recvCount hst.mkSaltCache)
              · rw [← hEqM, Functor.map_map, bind_pure_comp, Functor.map_map]
              · unfold matchedSameEphMkWith
                split
                · split
                  · simp
                  · cases List.find? (fun (x : (SessionId S × Option Bytes) × ℕ × MessageKeys) =>
                        match x with | (k, _) => mkSaltKeyMatch k s.sid spqrSalt?)
                        hst.mkSaltCache with
                    | none => simp
                    | some entry => rcases entry with ⟨_, _, _⟩; simp
                · simp
            · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨⟨⟨mk, mkSaltCache'⟩, cache'⟩, hMemM, rfl⟩
              obtain ⟨hIfNe, hIfEq⟩ := hSuppM _ hMemM
              dsimp only at hIfNe hIfEq
              unfold finishAuthRecvMk
              refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                        authSlotFired_of_usedSendSessions_eq_and_recvCount_le
                          (hInv.sentChal_imp hS).2
                          (hFinProps _).2 (Nat.le_succ _)⟩,
                      fun hNF => ?_,
                      ?_, (hFinProps _).1 ▸ hInv.ideal_unique, ?_⟩
              · have hNF0 : authSlotFired S idx hst = false :=
                  authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le (hFinProps _).2
                    (Nat.le_succ _) hNF
                have hIdxF : (sessionSlotIndex s.sid == idx) = false := by
                  cases hB : (sessionSlotIndex s.sid == idx)
                  · rfl
                  · have := authSlotFired_of_ideal_slot (hInv.ideal_send s hsMem) hB
                    rw [hNF0] at this; cases this
                rw [(hIfNe hIdxF).1]
                exact hInv.unfired_cache_nil hNF0
              · dsimp only
                rw [(hFinProps _).1, (hFinProps _).2]
                exact hInv.ideal_send
              · dsimp only
                rw [(hFinProps _).1]
                intro s1 hs1 hs1Idx salt? hSaltNe hFindNone
                cases hIdx : (sessionSlotIndex s.sid == idx)
                · obtain ⟨hCEq, hFEq⟩ := hIfNe hIdx
                  rw [hCEq]
                  rw [hFEq s1 hs1Idx salt?] at hFindNone
                  exact hInv.cache_sub_mkSaltCache s1 hs1 hs1Idx salt? hSaltNe hFindNone
                · have hs1Eq : s1 = s := hInv.ideal_unique s1 hs1 s hsMem hs1Idx hIdx
                  subst hs1Eq
                  exact hIfEq hIdx salt? hSaltNe hFindNone
        · refine ⟨?_, fun x hx => ?_⟩
          · simp only [map_bind]
            congr 1; funext rk1
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => dsimp only; simp
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact (finishAuthRecvUnmatchedRedProb_evalPrfMkIdeal P idx msg prep
                s.drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).1
          · simp only [MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨rk1, _, hx⟩
            revert x hx
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
              subst hx; exact hInvNone
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              intro x hx
              exact (finishAuthRecvUnmatchedRedProb_evalPrfMkIdeal P idx msg prep
                s.drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).2 x hx
      | none =>
        dsimp only [Option.map]
        refine ⟨?_, fun x hx => ?_⟩
        · simp only [map_bind]
          congr 1; funext drKey
          congr 1; funext rk1
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; simp
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (finishAuthRecvUnmatchedRedProb_evalPrfMkIdeal P idx msg prep
              drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).1
        · simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩
          revert x hx
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvNone
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            intro x hx
            exact (finishAuthRecvUnmatchedRedProb_evalPrfMkIdeal P idx msg prep
              drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).2 x hx
    · refine ⟨?_, fun x hx => ?_⟩
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => dsimp only; simp
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only; simp
      · simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
        revert x hx
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hInvNone
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                    authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                      (hFinProps _).2 (Nat.le_succ _)⟩,
                  fun hNF => hInv.unfired_cache_nil
                    (authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le
                    (hFinProps _).2 (Nat.le_succ _) hNF),
                  ?_, (hFinProps _).1 ▸ hInv.ideal_unique, (hFinProps _).1 ▸
                    hInv.cache_sub_mkSaltCache⟩
          dsimp only
          rw [(hFinProps _).1, (hFinProps _).2]
          exact hInv.ideal_send
theorem authMkSendRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkFalse S idx ((hst, sentChal), cache)) :
    ((fun (resp, ((hst', _), _)) => (resp, hst')) <$>
      authMkSendRedProb S P idx evalPrfMkIdeal sid u bundle m0 m1 hst sentChal cache) =
      authMkSendWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) sid u bundle m0 m1 hst ∧
    (∀ x ∈ support (authMkSendRedProb S P idx evalPrfMkIdeal sid u bundle m0 m1 hst sentChal cache),
      InvMkFalse S idx x.2) := by
  have hEq :
      ((fun (resp, ((hst', _), _)) => (resp, hst')) <$>
        authMkSendRedProb S P idx evalPrfMkIdeal sid u bundle m0 m1 hst sentChal cache) =
        authMkSendWith S P (fun _ => sampleBytes32)
          (fun s => decide (s < idx + 1)) sid u bundle m0 m1 hst := by
    unfold authMkSendRedProb authMkSendWith finishAuthSendAfterMk evalPrfMkIdeal
    rw [map_bind]
    refine bind_congr_of_support (prepareAuthSendMk S P sid u bundle m0 m1 hst) _ _
      (fun prep hPrep => ?_)
    have hP := support_prepareAuthSendMk_full_props P sid u bundle m0 m1 hst prep hPrep
    cases prep with
    | done resp hst' =>
      simp
    | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
        pqRatchetMsg msgPlain =>
      dsimp only
      cases hIdx : (sessionSlotIndex sid == idx)
      · simp only [decide_lt_succ_of_beq_false hIdx, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases hLt : decide (sessionSlotIndex sid < idx) <;> simp [map_bind]
      · obtain ⟨hNF, hSC⟩ := sentChal_false_of_send_idealMk (hst := hst) (sentChal := sentChal)
          hInv.sentChal_imp hSend hP.1 hIdx
        have hCacheNil : cache = [] := hInv.unfired_cache_nil hNF
        simp only [decide_lt_succ_of_beq_true hIdx, hCacheNil, hSC, Bool.not_false, Bool.and_self,
          ↓reduceIte, List.find?_nil, bind_assoc, pure_bind]
        simp [map_bind]
  refine ⟨hEq, fun x hx => ?_⟩
  have hFiredMono : authSlotFired S idx hst = true → authSlotFired S idx x.2.1.1 = true := by
    intro hF
    have hMemMap : (x.1, x.2.1.1) ∈
        support (authMkSendWith S P (fun _ => sampleBytes32)
          (fun s => decide (s < idx + 1)) sid u bundle m0 m1 hst) := by
      rw [← hEq]
      simp only [support_map, Set.mem_image]
      exact ⟨x, hx, rfl⟩
    exact authMkSendWith_slotFired_mono S P idx _ _ sid u bundle m0 m1 hst hF _ hMemMap
  unfold authMkSendRedProb evalPrfMkIdeal at hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hPrep, hx⟩
  have hP := support_prepareAuthSendMk_full_props P sid u bundle m0 m1 hst prep hPrep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, hFiredMono (hInv.sentChal_imp hS).2⟩,
            fun hNF => ?_,
            ?_,
            hP.1 ▸ hInv.ideal_unique,
            by rw [hP.1, hP.2.1]; exact hInv.cache_sub_mkSaltCache⟩
    · have hNF0 : authSlotFired S idx hst = false := by
        cases hF : authSlotFired S idx hst
        · rfl
        · rw [hFiredMono hF] at hNF; cases hNF
      exact hInv.unfired_cache_nil hNF0
    · rw [hP.1]
      intro s hs
      exact ⟨(hInv.ideal_send s hs).1, hP.2.2.2 s.sid (hInv.ideal_send s hs).2⟩
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
      pqRatchetMsg msgPlain =>
    dsimp only at hx
    have hNewIdealNe : ∀ s ∈ hst.toAuthHybridState.idealSessions,
        sessionSlotIndex s.sid ≠ sessionSlotIndex sid :=
      fun s hs => sessionSlotIndex_ne_of_ideal_fresh (hInv.ideal_send s hs) hSend hP.1
    cases hIdx : (sessionSlotIndex sid == idx)
    · rw [hIdx] at hx
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hx
      have hBr : ∀ mkSeed ck1_1 deriveMessageKeys,
          InvMkFalse S idx
            (((finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
                ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg
                  msgPlain
                hst deriveMessageKeys).2, sentChal), cache) := by
        intro mkSeed ck1_1 deriveMessageKeys
        obtain ⟨hMC, _, hUsed, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal?
          bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlain
          hst deriveMessageKeys
        have hFMono' : authSlotFired S idx hst = true →
            authSlotFired S idx (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
              ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg
                msgPlain
              hst deriveMessageKeys).2 = true :=
          authSlotFired_finishAuthSendMk_mono P idx sid uEntry peerPrincipal? bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg
              msgPlain
            hst deriveMessageKeys
        refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, hFMono' (hInv.sentChal_imp hS).2⟩,
                fun hNF => ?_, ?_, ?_, ?_⟩
        · have hNF0 : authSlotFired S idx hst = false := by
            cases hF : authSlotFired S idx hst
            · rfl
            · rw [hFMono' hF] at hNF; cases hNF
          exact hInv.unfired_cache_nil hNF0
        · dsimp only
          rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
          · rw [hIdEq, hUsed]
            intro s hs
            exact ⟨(hInv.ideal_send s hs).1,
                   List.contains_iff_mem.mpr (List.mem_cons.mpr
                                               (Or.inr (List.contains_iff_mem.mp
                                                         (hInv.ideal_send s hs).2)))⟩
          · rw [hIdCons, hUsed]
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs'
            · exact ⟨hsSid ▸ hSend, List.contains_iff_mem.mpr (List.mem_cons.mpr (Or.inl hsSid))⟩
            · exact ⟨(hInv.ideal_send s hs').1,
                     List.contains_iff_mem.mpr (List.mem_cons.mpr
                                                 (Or.inr (List.contains_iff_mem.mp (hInv.ideal_send
                                                            s hs').2)))⟩
        · dsimp only
          rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
          · rw [hIdEq]; exact hInv.ideal_unique
          · rw [hIdCons]
            intro s1 hs1 s2 hs2 hs1Idx hs2Idx
            rcases List.mem_cons.mp hs1 with rfl | hs1'
            · rw [hsSid, hIdx] at hs1Idx; cases hs1Idx
            · rcases List.mem_cons.mp hs2 with rfl | hs2'
              · rw [hsSid, hIdx] at hs2Idx; cases hs2Idx
              · exact hInv.ideal_unique s1 hs1' s2 hs2' hs1Idx hs2Idx
        · dsimp only
          rw [hMC]
          rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
          · rw [hIdEq]; exact hInv.cache_sub_mkSaltCache
          · rw [hIdCons]
            intro s hs hsIdx
            rcases List.mem_cons.mp hs with rfl | hs'
            · rw [hsSid, hIdx] at hsIdx; cases hsIdx
            · exact hInv.cache_sub_mkSaltCache s hs' hsIdx
      cases hLt : decide (sessionSlotIndex sid < idx)
      · rw [hLt] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        exact hBr mkSeed ck1_1 (P.deriveMsgKeys mkSeed spqrSalt?)
      · rw [hLt] at hx
        simp only [↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        exact hBr [] ck1_1 deriveMessageKeys
    · obtain ⟨hNF, hSC⟩ := sentChal_false_of_send_idealMk (hst := hst) (sentChal := sentChal)
        hInv.sentChal_imp hSend hP.1 hIdx
      have hCacheNil : cache = [] := hInv.unfired_cache_nil hNF
      rw [hCacheNil, hSC, hIdx] at hx
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte, List.find?_nil,
        bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      obtain ⟨hMC, _, hUsed, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal? bundle
        m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain
        hst deriveMessageKeys
      have hSlot : sendSlotIndex? sid = some idx := by
        rw [sendSlotIndex?_of_isSendSessionId hSend, beq_iff_eq.mp hIdx]
      have hFired' : authSlotFired S idx
          (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain
            hst deriveMessageKeys).2 = true :=
        authSlotFired_finishAuthSendMk_self P idx sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain
          hst deriveMessageKeys hSlot
      have hOldNotIdx : ∀ s ∈ hst.toAuthHybridState.idealSessions,
          (sessionSlotIndex s.sid == idx) = false := by
        intro s hs
        apply beq_eq_false_iff_ne.mpr
        rw [← beq_iff_eq.mp hIdx]
        exact hNewIdealNe s hs
      refine ⟨fun _ => ⟨sendSlotIndex?_lt hSlot, hFired'⟩,
              (by intro hF; rw [hFired'] at hF; cases hF),
              ?_, ?_, ?_⟩
      · dsimp only
        rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
        · rw [hIdEq, hUsed]
          intro s hs
          exact ⟨(hInv.ideal_send s hs).1,
                 List.contains_iff_mem.mpr (List.mem_cons.mpr
                                             (Or.inr (List.contains_iff_mem.mp
                                                       (hInv.ideal_send s hs).2)))⟩
        · rw [hIdCons, hUsed]
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · exact ⟨hsSid ▸ hSend, List.contains_iff_mem.mpr (List.mem_cons.mpr (Or.inl hsSid))⟩
          · exact ⟨(hInv.ideal_send s hs').1,
                   List.contains_iff_mem.mpr (List.mem_cons.mpr
                                               (Or.inr (List.contains_iff_mem.mp
                                                         (hInv.ideal_send s hs').2)))⟩
      · dsimp only
        rcases hId with hIdEq | ⟨s0, _, _, _, _, hIdCons⟩
        · rw [hIdEq]; exact hInv.ideal_unique
        · rw [hIdCons]
          intro s1 hs1 s2 hs2 hs1Idx hs2Idx
          rcases List.mem_cons.mp hs1 with rfl | hs1'
          · rcases List.mem_cons.mp hs2 with rfl | hs2'
            · rfl
            · rw [hOldNotIdx s2 hs2'] at hs2Idx; cases hs2Idx
          · rw [hOldNotIdx s1 hs1'] at hs1Idx; cases hs1Idx
      · dsimp only
        rcases hId with hIdEq | ⟨s0, _, _, hsSalt, _, hIdCons⟩
        · rw [hIdEq]
          intro s hs hsIdx
          rw [hOldNotIdx s hs] at hsIdx; cases hsIdx
        · rw [hIdCons]
          intro s hs hsIdx salt? hSaltNe _
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsSalt] at hSaltNe
            have hNe : ¬ effectiveHkdfSaltBytes spqrSalt? = effectiveHkdfSaltBytes salt? := by
              intro h; simp [sameSaltKey, h] at hSaltNe
            simp [hNe]
          · rw [hOldNotIdx s hs'] at hsIdx; cases hsIdx
theorem authMkStepRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat) (q : AuthQuery S)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkFalse S idx st) : ((authMkCutoffImpl S P (idx + 1) q).run st.1.1 =
      Prod.map id (fun ((hst', _), _) => hst') <$>
        ((authMkRedProbImpl S P idx evalPrfMkIdeal q).run st)) ∧
    (∀ x ∈ support ((authMkRedProbImpl S P idx evalPrfMkIdeal q).run st),
      InvMkFalse S idx x.2) := by
  rcases st with ⟨⟨hst, sentChal⟩, cache⟩
  dsimp only [authMkCutoffImpl, authMkRedProbImpl, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSendRedProb_evalPrfMkIdeal P idx (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSendRedProb_evalPrfMkIdeal P idx (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | recvOPK k j o msg =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    obtain ⟨hEq, hSupp⟩ := authMkRecvRedProb_evalPrfMkIdeal P idx msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst sentChal cache hInv
      (prepareAuthHybridRecvOPK_props P k j o msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]
      simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | recvNoOPK k j l msg =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    obtain ⟨hEq, hSupp⟩ := authMkRecvRedProb_evalPrfMkIdeal P idx msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst sentChal cache hInv
      (prepareAuthHybridRecvNoOPK_props P k j l msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]
      simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _ 
          | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkStepWith authMkStepRedProb
    dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · simp [Prod.map, map_eq_bind_pure_comp]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      have hRCEq : hst.recvCount ≤ hst'.recvCount := by
        dsimp only at hOther; omega
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1,
                authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
                  hOther.2.1 hRCEq⟩,
              fun hNF => hInv.unfired_cache_nil
                (authSlotFired_false_of_usedSendSessions_eq_and_recvCount_le
                hOther.2.1 hRCEq hNF),
              ?_, hOther.1 ▸ hInv.ideal_unique,
              by dsimp only; rw [hOther.1, hOther.2.2.1]; exact hInv.cache_sub_mkSaltCache⟩
      dsimp only
      rw [hOther.1, hOther.2.1]
      exact hInv.ideal_send
theorem evalDist_prfMsgKeysWorld_false_at_idx (S : Setup) (P : Primitives) (idx : Nat)
    (A : AuthAdversary S) :
    𝒟[(do
        let _ ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkRedProbImpl S P idx evalPrfMkIdeal
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkCutoffExp S P (idx + 1) A] := by
  rw [evalDist_sampleBytes32_bind_const]
  unfold authMkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1
  symm
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => hst) (InvMkFalse S idx) (authMkRedProbImpl S P idx evalPrfMkIdeal)
    (authMkCutoffImpl S P (idx + 1))
    (fun q st hInv => authMkStepRedProb_evalPrfMkIdeal P idx q st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), []) (invMkFalse_empty S idx secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState) (fun _ _ => rfl)
/-! ## Creation-order `PrfMsgKeys` hybrid and `SlotM` bridge -/

theorem support_authCkOtherStep_slots {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ∀ x ∈ support (authCkOtherStep S P q hst), x.2.slots = hst.slots := by
  intro y hy
  unfold authCkOtherStep at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩; rfl

def finishAuthSendAfterMkSlots {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool) (sIdx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) :
    ProbComp (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt sIdx then do
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys ← sampleMessageKeys80
    pure (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys)
  else do
    let mkSeed ← sampMkAt sIdx
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    pure (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys)

def finishAuthSendAfterMkSlotsSlot {S : Setup} (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool) (sIdx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM Bytes (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt sIdx then
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys ← sampleMessageKeys80
      pure (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys))
  else do
    let mkSeed ← getRkAtSlot idx sIdx
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      pure (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys))

def authMkSlotsSendWith (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  match ← prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst with
  | .done resp hst' => pure (resp, hst')
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    let (sIdx, slots') := hst.slots.allocSend sid
    finishAuthSendAfterMkSlots P sampMkAt useIdealMkAt sIdx sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain
      { hst with slots := slots' }

def authMkSlotsSendSlot (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : SlotM Bytes (AuthResponse × AuthHybridStateFixed S) := do
  match ← (liftM (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst) :
      SlotM Bytes (PreparedAuthSend S)) with
  | .done resp hst' => pure (resp, hst')
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    let (sIdx, slots') := hst.slots.allocSend sid
    finishAuthSendAfterMkSlotsSlot P idx useIdealMkAt sIdx sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain
      { hst with slots := slots' }

def finishAuthRecvUnmatchedAfterMkSlots {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) :
    ProbComp (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt rSlot then do
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys ← sampleMessageKeys80
    pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
      deriveMessageKeys)
  else do
    let mkSeed ← sampMkAt rSlot
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
      deriveMessageKeys)

def finishAuthRecvUnmatchedAfterMkSlotsSlot {S : Setup} (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) :
    SlotM Bytes (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt rSlot then
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys ← sampleMessageKeys80
      pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
        deriveMessageKeys))
  else do
    let mkSeed ← getRkAtSlot idx rSlot
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      pure (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache slots'
        deriveMessageKeys))

def matchedSameEphMkSlotsWith {S : Setup} (P : Primitives) (useIdealMkAt : Nat → Bool)
    (s : IdealAuthSession S) (sIdx : Nat) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    ProbComp (MessageKeys × List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :=
  if useIdealMkAt sIdx then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      pure (s.deriveMessageKeys, mkSaltCache)
    else
      match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) => pure (mk, mkSaltCache)
      | none => do
        let mk ← sampleMessageKeys80
        pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
  else
    pure (P.deriveMsgKeys s.mkSeed spqrSalt?, mkSaltCache)

def authMkSlotsRecvWith (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let sIdx := hst.slots.lookupSendOrZero s.sid
            let (deriveMessageKeys, mkSaltCache') ←
              matchedSameEphMkSlotsWith P useIdealMkAt s sIdx spqrSalt? hst.recvCount hst.mkSaltCache
            pure (finishAuthRecvMkSlotsH3 P msg prep s.drKey s.rk1 s.ck1_1 recvCount'
              mkSaltCache' hst.slots deriveMessageKeys)
        else
          let rk1 ← sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            finishAuthRecvUnmatchedAfterMkSlots P sampMkAt useIdealMkAt msg prep s.drKey rk1
              spqrSalt? rSlot recvCount' hst.mkSaltCache slots'
      | none =>
        let drKey ← sampleDRKey96
        let rk1 ← sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache, slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          finishAuthRecvUnmatchedAfterMkSlots P sampMkAt useIdealMkAt msg prep drKey rk1
            spqrSalt? rSlot recvCount' hst.mkSaltCache slots'
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
        prep.dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                      mkSaltCache := hst.mkSaltCache, slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                      mkSaltCache := hst.mkSaltCache, slots := hst.slots })

def authMkSlotsRecvSlot (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : SlotM Bytes (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          liftM (show ProbComp (AuthResponse × AuthHybridStateFixed S) from do
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              let (resp, hst') := prep.finish none
              pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                            mkSaltCache := hst.mkSaltCache, slots := hst.slots })
            | some (_pqrStB, spqrSalt?) =>
              let sIdx := hst.slots.lookupSendOrZero s.sid
              let (deriveMessageKeys, mkSaltCache') ←
                matchedSameEphMkSlotsWith P useIdealMkAt s sIdx spqrSalt? hst.recvCount hst.mkSaltCache
              pure (finishAuthRecvMkSlotsH3 P msg prep s.drKey s.rk1 s.ck1_1 recvCount'
                mkSaltCache' hst.slots deriveMessageKeys))
        else
          let rk1 ← liftM sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            finishAuthRecvUnmatchedAfterMkSlotsSlot P idx useIdealMkAt msg prep s.drKey rk1
              spqrSalt? rSlot recvCount' hst.mkSaltCache slots'
      | none =>
        let drKey ← liftM sampleDRKey96
        let rk1 ← liftM sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache, slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          finishAuthRecvUnmatchedAfterMkSlotsSlot P idx useIdealMkAt msg prep drKey rk1
            spqrSalt? rSlot recvCount' hst.mkSaltCache slots'
    else
      liftM (do
        let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
          prep.dhRatchet
        let mkSeed := P.chainKdfSeed ck1_0
        let ck1_1 := P.chainKdfNext ck1_0
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache, slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
          let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
          let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
            (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
          let (resp, hst') := prep.finish res?
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache, slots := hst.slots }))

def authMkSlotsStepWith (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authMkSlotsSendWith S P sampMkAt useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authMkSlotsSendWith S P sampMkAt useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authMkSlotsRecvWith S P sampMkAt useIdealMkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authMkSlotsRecvWith S P sampMkAt useIdealMkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther => authCkOtherStep S P qOther hst

def authMkSlotsStepSlot (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM Bytes ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authMkSlotsSendSlot S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authMkSlotsSendSlot S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authMkSlotsRecvSlot S P idx useIdealMkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authMkSlotsRecvSlot S P idx useIdealMkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther => liftM (authCkOtherStep S P qOther hst)

def authMkSlotsCutoffImpl (S : Setup) (P : Primitives) (cutoff : Nat) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk
    (authMkSlotsStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff)) q)

def prfMkSlotsAuthImpl (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authMkSlotsStepWith S P
    (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
    (fun s => decide (s < idx)) q)

noncomputable def authMkSlotsPreSampleRun (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + prfMkSlotsAuthImpl S P idx mkSeedStar
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

noncomputable def authMkSlotsCutoffExp (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + authMkSlotsCutoffImpl S P cutoff
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

theorem authSlotStateWf_of_usedSend_sub {S : Setup} {hst hst' : AuthHybridStateFixed S}
    (hWf : AuthSlotStateWf S hst)
    (hSlots : hst'.slots = hst.slots)
    (hIdeal : hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions)
    (hRC : hst.recvCount ≤ hst'.recvCount)
    (hSub : ∀ sid, hst.toAuthHybridState.base.usedSendSessions.contains sid = true →
      hst'.toAuthHybridState.base.usedSendSessions.contains sid = true) :
    AuthSlotStateWf S hst' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sid k hk; rw [hSlots] at hk ⊢; exact hWf.send_lt sid k hk
  · intro rc k hk; rw [hSlots] at hk ⊢; exact hWf.recv_lt rc k hk
  · intro sid hF
    rw [hSlots]
    apply hWf.send_fresh sid
    cases hC : hst.toAuthHybridState.base.usedSendSessions.contains sid
    · rfl
    · exact absurd (hSub sid hC) (by rw [hF]; decide)
  · intro rc hle; rw [hSlots]; exact hWf.recv_fresh rc (Nat.le_trans hRC hle)
  · intro s hs
    rw [hIdeal] at hs
    obtain ⟨hU, k, hkLt, hkEq⟩ := hWf.ideal_send s hs
    exact ⟨hSub s.sid hU, k, hSlots ▸ hkLt, hSlots ▸ hkEq⟩
  · intro sid1 sid2 k h1 h2; rw [hSlots] at h1 h2; exact hWf.slot_inj sid1 sid2 k h1 h2

theorem authSlotStateWf_of_allocSend_finishSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes) (spqrSalt? : Option Bytes)
    (pqRatchetMsg msgPlain : Bytes) (hst : AuthHybridStateFixed S)
    (deriveMessageKeys : MessageKeys)
    (hWf : AuthSlotStateWf S hst)
    (hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid = false) :
    let hst' := (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
      deriveMessageKeys).2
    AuthSlotStateWf S hst' ∧ hst'.slots.nextSlot = hst.slots.nextSlot + 1 := by
  intro hst'
  have hNone : hst.slots.lookupSend sid = none := hWf.send_fresh sid hFresh
  obtain ⟨_, hNext, hRecvTbl, hLookup⟩ := allocSend_of_none hst.slots sid hSend hNone
  have hProps := finishAuthSendMk_full_props P sid uEntry peerPrincipal? bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
    spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
    deriveMessageKeys
  have hSlots' : hst'.slots = (hst.slots.allocSend sid).2 := rfl
  have hRC' : hst'.recvCount = hst.recvCount := rfl
  have hUsed' : hst'.toAuthHybridState.base.usedSendSessions =
      sid :: hst.toAuthHybridState.base.usedSendSessions := hProps.2.2.1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hSlots', hNext]⟩
  · intro sid' k hk
    rw [hSlots', hLookup] at hk
    rw [hSlots', hNext]
    by_cases hEq : sid' = sid
    · simp only [hEq, ↓reduceIte, Option.some.injEq] at hk; omega
    · simp only [hEq, ↓reduceIte] at hk
      have := hWf.send_lt sid' k hk; omega
  · intro rc k hk
    rw [hSlots', hRecvTbl] at hk
    rw [hSlots', hNext]
    have := hWf.recv_lt rc k hk; omega
  · intro sid' hF'
    rw [hUsed'] at hF'
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hF'
    have hNeSid : sid' ≠ sid := hF'.1
    simp only [hSlots', hLookup, hNeSid, ↓reduceIte]
    exact hWf.send_fresh sid' hF'.2
  · intro rc hle
    rw [hRC'] at hle
    rw [hSlots', hRecvTbl]
    exact hWf.recv_fresh rc hle
  · intro s hs
    have hCases : (s.sid = sid) ∨ s ∈ hst.toAuthHybridState.idealSessions := by
      rcases hProps.2.2.2 with hIdealEq | ⟨sNew, hSidNew, _, _, _, hIdealEq⟩
      · change s ∈ hst'.toAuthHybridState.idealSessions at hs
        have hIdEq : hst'.toAuthHybridState.idealSessions =
            hst.toAuthHybridState.idealSessions := hIdealEq
        exact Or.inr (hIdEq ▸ hs)
      · change s ∈ hst'.toAuthHybridState.idealSessions at hs
        have hIdEq : hst'.toAuthHybridState.idealSessions =
            sNew :: hst.toAuthHybridState.idealSessions := hIdealEq
        rw [hIdEq, List.mem_cons] at hs
        rcases hs with rfl | hsOld
        · exact Or.inl hSidNew
        · exact Or.inr hsOld
    rcases hCases with hSidEq | hsOld
    · refine ⟨?_, hst.slots.nextSlot, ?_, ?_⟩
      · rw [hUsed', hSidEq]; simp
      · rw [hSlots', hNext]; omega
      · simp only [hSlots', hSidEq, hLookup, ↓reduceIte]
    · obtain ⟨hUOld, k, hkLt, hkEq⟩ := hWf.ideal_send s hsOld
      have hNe : s.sid ≠ sid := by
        intro hEq; rw [hEq, hFresh] at hUOld; cases hUOld
      refine ⟨?_, k, ?_, ?_⟩
      · rw [hUsed', List.contains_cons, hUOld, Bool.or_true]
      · rw [hSlots', hNext]; omega
      · simp only [hSlots', hLookup, hNe, ↓reduceIte]; exact hkEq
  · intro sid1 sid2 k h1 h2
    rw [hSlots', hLookup] at h1 h2
    by_cases he1 : sid1 = sid <;> by_cases he2 : sid2 = sid
    · exact he1.trans he2.symm
    · simp only [he1, he2, ↓reduceIte, Option.some.injEq] at h1 h2
      subst h1; exact absurd (hWf.send_lt sid2 _ h2) (Nat.lt_irrefl _)
    · simp only [he1, he2, ↓reduceIte, Option.some.injEq] at h1 h2
      subst h2; exact absurd (hWf.send_lt sid1 _ h1) (Nat.lt_irrefl _)
    · simp only [he1, he2, ↓reduceIte] at h1 h2
      exact hWf.slot_inj sid1 sid2 k h1 h2

theorem authSlotStateWf_of_allocRecv {S : Setup} {hst hst' : AuthHybridStateFixed S}
    (hWf : AuthSlotStateWf S hst)
    (hSlots : hst'.slots = (hst.slots.allocRecv hst.recvCount).2)
    (hIdeal : hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions)
    (hUsed : hst'.toAuthHybridState.base.usedSendSessions =
      hst.toAuthHybridState.base.usedSendSessions)
    (hRC : hst'.recvCount = hst.recvCount + 1) :
    AuthSlotStateWf S hst' ∧ hst'.slots.nextSlot = hst.slots.nextSlot + 1 := by
  have hNone : hst.slots.recvTbl hst.recvCount = none := hWf.recv_fresh hst.recvCount (Nat.le_refl _)
  obtain ⟨_, hNext, hLookup, hRecvTbl⟩ := allocRecv_of_none (S := S) hst.slots hst.recvCount hNone
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hSlots, hNext]⟩
  · intro sid k hk
    rw [hSlots, hLookup] at hk; rw [hSlots, hNext]
    have := hWf.send_lt sid k hk; omega
  · intro rc k hk
    rw [hSlots, hRecvTbl] at hk; rw [hSlots, hNext]
    by_cases hEq : rc = hst.recvCount
    · simp only [hEq, ↓reduceIte, Option.some.injEq] at hk; omega
    · simp only [hEq, ↓reduceIte] at hk; have := hWf.recv_lt rc k hk; omega
  · intro sid hF
    rw [hUsed] at hF; rw [hSlots, hLookup]; exact hWf.send_fresh sid hF
  · intro rc hle
    rw [hRC] at hle
    have hNe : rc ≠ hst.recvCount := by omega
    simp only [hSlots, hRecvTbl, hNe, ↓reduceIte]
    exact hWf.recv_fresh rc (by omega)
  · intro s hs
    rw [hIdeal] at hs
    obtain ⟨hU, k, hkLt, hkEq⟩ := hWf.ideal_send s hs
    refine ⟨hUsed ▸ hU, k, ?_, ?_⟩
    · rw [hSlots, hNext]; omega
    · rw [hSlots, hLookup]; exact hkEq
  · intro sid1 sid2 k h1 h2
    rw [hSlots, hLookup] at h1 h2
    exact hWf.slot_inj sid1 sid2 k h1 h2

theorem prepareAuthSendMkSlotsH3_wf_and_fresh {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst) :
    ∀ p ∈ support (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst),
      match p with
      | .done _ hst' =>
        AuthSlotStateWf S hst' ∧ hst'.slots = hst.slots ∧
        hst'.recvCount = hst.recvCount ∧ hst'.mkSaltCache = hst.mkSaltCache ∧
        hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions
      | .idealMk _ _ _ _ _ _ _ _ _ _ spqrSalt? _ _ =>
        hst.toAuthHybridState.base.usedSendSessions.contains sid = false ∧
        (WellFormedPrimitivesδ P → SaltOK spqrSalt?) := by
  unfold prepareAuthSendMkSlotsH3
  intro p hp
  rw [support_map] at hp
  rcases hp with ⟨p0, hp0, rfl⟩
  have hFull := support_prepareAuthSendMk_full_props P sid u bundle m0 m1 hst p0 hp0
  cases p0 with
  | done resp hst0 =>
    dsimp only [PreparedAuthSend.mapState] at hFull ⊢
    rcases hFull with ⟨hId, hMC, hRC, hSub⟩
    exact ⟨authSlotStateWf_of_usedSend_sub hWf rfl hId (by dsimp only; omega) hSub,
      rfl, hRC, hMC, hId⟩
  | idealMk _ _ _ _ _ _ _ _ _ _ spqrSalt? _ _ =>
    exact hFull

theorem authMkSlotsSendWith_wf_and_nextSlot {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst) :
    ∀ x ∈ support (authMkSlotsSendWith S P sampMkAt useIdealMkAt sid u bundle m0 m1 hst),
      AuthSlotStateWf S x.2 ∧
      hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
      x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 ∧
      x.2.recvCount = hst.recvCount := by
  unfold authMkSlotsSendWith
  intro x hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hprep, hx⟩
  have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hWf prep hprep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact ⟨hP.1, by rw [hP.2.1], by rw [hP.2.1]; omega, hP.2.2.1⟩
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    dsimp only [finishAuthSendAfterMkSlots] at hx
    split at hx
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, mk, _, rfl⟩
      obtain ⟨hW', hN'⟩ := authSlotStateWf_of_allocSend_finishSend P sid hSend uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst mk hWf hP.1
      exact ⟨hW', by omega, by omega, rfl⟩
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
      obtain ⟨hW', hN'⟩ := authSlotStateWf_of_allocSend_finishSend P sid hSend uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst _ hWf hP.1
      exact ⟨hW', by omega, by omega, rfl⟩

theorem authMkSlotsRecvWith_wf_and_nextSlot {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst)
    (hPrep : ∀ prep, prep? = some prep → ∀ res?,
      (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
      (prep.finish res?).2.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions) :
    ∀ x ∈ support (authMkSlotsRecvWith S P sampMkAt useIdealMkAt msg prep? hst),
      AuthSlotStateWf S x.2 ∧
      hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
      x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 ∧
      x.2.recvCount = hst.recvCount + 1 := by
  unfold authMkSlotsRecvWith
  cases prep? with
  | none =>
    intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    refine ⟨authSlotStateWf_of_usedSend_sub hWf rfl rfl (by dsimp only; omega) (fun _ h => h),
      Nat.le_refl _, by dsimp only; omega, rfl⟩
  | some prep =>
    have hF := hPrep prep rfl
    have hUnchanged : ∀ res?,
        let hst' : AuthHybridStateFixed S :=
          { toAuthHybridState := (prep.finish res?).2, recvCount := hst.recvCount + 1,
            mkSaltCache := hst.mkSaltCache, slots := hst.slots }
        AuthSlotStateWf S hst' ∧ hst.slots.nextSlot ≤ hst'.slots.nextSlot ∧
        hst'.slots.nextSlot ≤ hst.slots.nextSlot + 1 ∧ hst'.recvCount = hst.recvCount + 1 := by
      intro res?
      exact ⟨authSlotStateWf_of_usedSend_sub hWf rfl (hF res?).1 (by dsimp only; omega)
        (fun sid h => by dsimp only; rw [(hF res?).2]; exact h),
        Nat.le_refl _, by dsimp only; omega, rfl⟩
    have hUnmatched : ∀ drKey rk1 spqrSalt?,
        ∀ x ∈ support (finishAuthRecvUnmatchedAfterMkSlots P sampMkAt useIdealMkAt msg prep
            drKey rk1 spqrSalt? (hst.slots.allocRecv hst.recvCount).1 (hst.recvCount + 1)
            hst.mkSaltCache (hst.slots.allocRecv hst.recvCount).2),
          AuthSlotStateWf S x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
          x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 ∧ x.2.recvCount = hst.recvCount + 1 := by
      intro drKey rk1 spqrSalt? x hx
      unfold finishAuthRecvUnmatchedAfterMkSlots at hx
      split at hx
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, mk, _, rfl⟩
        dsimp only [finishAuthRecvMkSlotsH3]
        obtain ⟨hW', hN'⟩ := @authSlotStateWf_of_allocRecv S hst
          { toAuthHybridState := (prep.finish _).2, recvCount := hst.recvCount + 1,
            mkSaltCache := hst.mkSaltCache, slots := (hst.slots.allocRecv hst.recvCount).2 }
          hWf rfl (hF _).1 (hF _).2 rfl
        exact ⟨hW', by dsimp only at hN' ⊢; omega, by dsimp only at hN' ⊢; omega, rfl⟩
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        dsimp only [finishAuthRecvMkSlotsH3]
        obtain ⟨hW', hN'⟩ := @authSlotStateWf_of_allocRecv S hst
          { toAuthHybridState := (prep.finish _).2, recvCount := hst.recvCount + 1,
            mkSaltCache := hst.mkSaltCache, slots := (hst.slots.allocRecv hst.recvCount).2 }
          hWf rfl (hF _).1 (hF _).2 rfl
        exact ⟨hW', by dsimp only at hN' ⊢; omega, by dsimp only at hN' ⊢; omega, rfl⟩
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only; split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact hUnchanged none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨y, _, rfl⟩
            dsimp only [finishAuthRecvMkSlotsH3, finishAuthRecvMk]
            exact ⟨authSlotStateWf_of_usedSend_sub hWf rfl (hF _).1 (by dsimp only; omega)
              (fun sid h => by rw [(hF _).2]; exact h),
              Nat.le_refl _, by omega, rfl⟩
        · intro x hx; simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨rk1, _, hx⟩; revert x hx
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact hUnchanged none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact hUnmatched s.drKey rk1 spqrSalt?
      | none =>
        dsimp only; intro x hx; simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨drKey, _, rk1, _, hx⟩; revert x hx
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
          exact hUnchanged none
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact hUnmatched drKey rk1 spqrSalt?
    · intro x hx; simp only [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩; revert x hx
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact hUnchanged none
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact hUnchanged _

theorem authMkSlotsStepWith_wf_and_bounds {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst) :
    ∀ x ∈ support (authMkSlotsStepWith S P sampMkAt useIdealMkAt q hst),
      AuthSlotStateWf S x.2 ∧
      hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
      x.2.slots.nextSlot ≤ hst.slots.nextSlot + (if isAuthSessQueryB (.inr q) then 1 else 0) ∧
      x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hS0 : isAuthSessQueryB (.inr (.sendOPK u i bundle m0 m1)) = true := rfl
    have hR0 : isAuthRecvQueryB (.inr (.sendOPK u i bundle m0 m1)) = false := rfl
    simp only [hS0, hR0, Bool.false_eq_true, ↓reduceIte]
    unfold authMkSlotsStepWith; dsimp only; split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨hWf, Nat.le_refl _, by dsimp only; omega, by dsimp only; omega⟩
    · intro x hx
      obtain ⟨hW, h1, h2, h3⟩ := authMkSlotsSendWith_wf_and_nextSlot P sampMkAt useIdealMkAt
        (.sendOPK u i) trivial u bundle m0 m1 hst hWf x hx
      exact ⟨hW, h1, h2, by omega⟩
  | sendNoOPK u i bundle m0 m1 =>
    have hS0 : isAuthSessQueryB (.inr (.sendNoOPK u i bundle m0 m1)) = true := rfl
    have hR0 : isAuthRecvQueryB (.inr (.sendNoOPK u i bundle m0 m1)) = false := rfl
    simp only [hS0, hR0, Bool.false_eq_true, ↓reduceIte]
    unfold authMkSlotsStepWith; dsimp only; split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨hWf, Nat.le_refl _, by dsimp only; omega, by dsimp only; omega⟩
    · intro x hx
      obtain ⟨hW, h1, h2, h3⟩ := authMkSlotsSendWith_wf_and_nextSlot P sampMkAt useIdealMkAt
        (.sendNoOPK u i) trivial u bundle m0 m1 hst hWf x hx
      exact ⟨hW, h1, h2, by omega⟩
  | recvOPK k j o msg =>
    have hS0 : isAuthSessQueryB (.inr (.recvOPK k j o msg)) = true := rfl
    have hR0 : isAuthRecvQueryB (.inr (.recvOPK k j o msg)) = true := rfl
    simp only [hS0, hR0, ↓reduceIte]
    unfold authMkSlotsStepWith; dsimp only
    intro x hx
    obtain ⟨hW, h1, h2, h3⟩ := authMkSlotsRecvWith_wf_and_nextSlot P sampMkAt useIdealMkAt
      msg _ hst hWf
      (fun prep hp => (prepareAuthHybridRecvOPK_props P k j o msg hst.toAuthHybridState prep hp).2)
      x hx
    exact ⟨hW, h1, h2, by omega⟩
  | recvNoOPK k j l msg =>
    have hS0 : isAuthSessQueryB (.inr (.recvNoOPK k j l msg)) = true := rfl
    have hR0 : isAuthRecvQueryB (.inr (.recvNoOPK k j l msg)) = true := rfl
    simp only [hS0, hR0, ↓reduceIte]
    unfold authMkSlotsStepWith; dsimp only
    intro x hx
    obtain ⟨hW, h1, h2, h3⟩ := authMkSlotsRecvWith_wf_and_nextSlot P sampMkAt useIdealMkAt
      msg _ hst hWf
      (fun prep hp =>
        (prepareAuthHybridRecvNoOPK_props P k j l msg hst.toAuthHybridState prep hp).2)
      x hx
    exact ⟨hW, h1, h2, by omega⟩
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkSlotsStepWith; dsimp only
    intro x hx
    have hO := support_authCkOtherStep_props P _ hst
      (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
      (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h) x hx
    have hSl := support_authCkOtherStep_slots P _ hst x hx
    refine ⟨authSlotStateWf_of_usedSend_sub hWf hSl hO.1 (by omega)
      (fun sid h => by rw [hO.2.1]; exact h),
      by rw [hSl], by rw [hSl]; exact Nat.le_add_right _ _,
      by rw [hO.2.2.2]; exact Nat.le_add_right _ _⟩

theorem authMkSlotsSendSlot_slotComp (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkSlotsSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst) := by
  unfold authMkSlotsSendSlot finishAuthSendAfterMkSlotsSlot
  refine (SlotM.SlotComp.liftComp sampleBytes32 _).bind (fun prep => ?_)
  cases prep with
  | done _ _ => exact SlotM.SlotComp.pure sampleBytes32 _
  | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    dsimp only; split
    · exact SlotM.SlotComp.liftComp sampleBytes32 _
    · exact slotComp_getRkAtSlot_bind_liftM idx _ _

theorem authMkSlotsRecvSlot_slotComp (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkSlotsRecvSlot S P idx useIdealMkAt msg prep? hst) := by
  unfold authMkSlotsRecvSlot finishAuthRecvUnmatchedAfterMkSlotsSlot
  cases prep? with
  | none => exact SlotM.SlotComp.pure sampleBytes32 _
  | some prep =>
    dsimp only; split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only; split
        · exact SlotM.SlotComp.liftComp sampleBytes32 _
        · refine (SlotM.SlotComp.liftComp sampleBytes32 _).bind (fun _ => ?_)
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => exact SlotM.SlotComp.pure sampleBytes32 _
          | some pqr =>
            rcases pqr with ⟨_, _⟩; dsimp only; split
            · exact SlotM.SlotComp.liftComp sampleBytes32 _
            · exact slotComp_getRkAtSlot_bind_liftM idx _ _
      | none =>
        dsimp only
        refine (SlotM.SlotComp.liftComp sampleBytes32 _).bind (fun drKey => ?_)
        refine (SlotM.SlotComp.liftComp sampleBytes32 _).bind (fun _ => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact SlotM.SlotComp.pure sampleBytes32 _
        | some pqr =>
          rcases pqr with ⟨_, _⟩; dsimp only; split
          · exact SlotM.SlotComp.liftComp sampleBytes32 _
          · exact slotComp_getRkAtSlot_bind_liftM idx _ _
    · exact SlotM.SlotComp.liftComp sampleBytes32 _

theorem authMkSlotsStepSlot_slotComp (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkSlotsStepSlot S P idx useIdealMkAt q hst) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot; dsimp only; split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authMkSlotsSendSlot_slotComp S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot; dsimp only; split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authMkSlotsSendSlot_slotComp S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | recvOPK k j o msg =>
    exact authMkSlotsRecvSlot_slotComp S P idx useIdealMkAt msg _ hst
  | recvNoOPK k j l msg =>
    exact authMkSlotsRecvSlot_slotComp S P idx useIdealMkAt msg _ hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact SlotM.SlotComp.liftComp sampleBytes32 _

theorem authMkSlotsSendSlot_run'_some (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool) (mkSeedStar : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authMkSlotsSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst).run' (some mkSeedStar) =
      authMkSlotsSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        useIdealMkAt sid u bundle m0 m1 hst := by
  unfold authMkSlotsSendSlot authMkSlotsSendWith finishAuthSendAfterMkSlotsSlot finishAuthSendAfterMkSlots
  rw [SlotM.run'_liftComp_bind]
  congr 1; funext prep
  cases prep with
  | done _ _ => simp [StateT.run'_eq]
  | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    dsimp only; split
    · exact SlotM.run'_liftComp _ (some mkSeedStar)
    · exact run'_getRkAtSlot_bind_liftM_some idx _ mkSeedStar _

theorem authMkSlotsRecvSlot_run'_some (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool) (mkSeedStar : Bytes)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authMkSlotsRecvSlot S P idx useIdealMkAt msg prep? hst).run' (some mkSeedStar) =
      authMkSlotsRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        useIdealMkAt msg prep? hst := by
  unfold authMkSlotsRecvSlot authMkSlotsRecvWith
    finishAuthRecvUnmatchedAfterMkSlotsSlot finishAuthRecvUnmatchedAfterMkSlots
  cases prep? with
  | none => simp [StateT.run'_eq]
  | some prep =>
    dsimp only; split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only; split
        · exact SlotM.run'_liftComp _ (some mkSeedStar)
        · rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [StateT.run'_eq]
          | some pqr =>
            rcases pqr with ⟨_, _⟩; dsimp only; split
            · exact SlotM.run'_liftComp _ (some mkSeedStar)
            · exact run'_getRkAtSlot_bind_liftM_some idx _ mkSeedStar _
      | none =>
        dsimp only
        rw [SlotM.run'_liftComp_bind]; congr 1; funext drKey
        rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [StateT.run'_eq]
        | some pqr =>
          rcases pqr with ⟨_, _⟩; dsimp only; split
          · exact SlotM.run'_liftComp _ (some mkSeedStar)
          · exact run'_getRkAtSlot_bind_liftM_some idx _ mkSeedStar _
    · exact SlotM.run'_liftComp _ (some mkSeedStar)

theorem authMkSlotsStepSlot_run'_some (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool) (mkSeedStar : Bytes)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkSlotsStepSlot S P idx useIdealMkAt q hst).run' (some mkSeedStar) =
      authMkSlotsStepWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        useIdealMkAt q hst := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot authMkSlotsStepWith; dsimp only; split
    · simp [StateT.run'_eq]
    · exact authMkSlotsSendSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendOPK u i)
        u bundle m0 m1 hst
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot authMkSlotsStepWith; dsimp only; split
    · simp [StateT.run'_eq]
    · exact authMkSlotsSendSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendNoOPK u i)
        u bundle m0 m1 hst
  | recvOPK k j o msg =>
    exact authMkSlotsRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  | recvNoOPK k j l msg =>
    exact authMkSlotsRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact SlotM.run'_liftComp _ (some mkSeedStar)

theorem authMkSlotsSendSlot_run'_none (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authMkSlotsSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst).run' none =
      authMkSlotsSendWith S P (fun _ => sampleBytes32) useIdealMkAt sid u bundle m0 m1 hst := by
  unfold authMkSlotsSendSlot authMkSlotsSendWith finishAuthSendAfterMkSlotsSlot finishAuthSendAfterMkSlots
  rw [SlotM.run'_liftComp_bind]
  congr 1; funext prep
  cases prep with
  | done _ _ => simp [StateT.run'_eq]
  | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    dsimp only; split
    · exact SlotM.run'_liftComp _ none
    · exact run'_getRkAtSlot_bind_liftM_none idx _ _

theorem authMkSlotsRecvSlot_run'_none (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authMkSlotsRecvSlot S P idx useIdealMkAt msg prep? hst).run' none =
      authMkSlotsRecvWith S P (fun _ => sampleBytes32) useIdealMkAt msg prep? hst := by
  unfold authMkSlotsRecvSlot authMkSlotsRecvWith
    finishAuthRecvUnmatchedAfterMkSlotsSlot finishAuthRecvUnmatchedAfterMkSlots
  cases prep? with
  | none => simp [StateT.run'_eq]
  | some prep =>
    dsimp only; split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only; split
        · exact SlotM.run'_liftComp _ none
        · rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [StateT.run'_eq]
          | some pqr =>
            rcases pqr with ⟨_, _⟩; dsimp only; split
            · exact SlotM.run'_liftComp _ none
            · exact run'_getRkAtSlot_bind_liftM_none idx _ _
      | none =>
        dsimp only
        rw [SlotM.run'_liftComp_bind]; congr 1; funext drKey
        rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [StateT.run'_eq]
        | some pqr =>
          rcases pqr with ⟨_, _⟩; dsimp only; split
          · exact SlotM.run'_liftComp _ none
          · exact run'_getRkAtSlot_bind_liftM_none idx _ _
    · exact SlotM.run'_liftComp _ none

theorem authMkSlotsStepSlot_run'_none (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkSlotsStepSlot S P idx useIdealMkAt q hst).run' none =
      authMkSlotsStepWith S P (fun _ => sampleBytes32) useIdealMkAt q hst := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot authMkSlotsStepWith; dsimp only; split
    · simp [StateT.run'_eq]
    · exact authMkSlotsSendSlot_run'_none S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot authMkSlotsStepWith; dsimp only; split
    · simp [StateT.run'_eq]
    · exact authMkSlotsSendSlot_run'_none S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | recvOPK k j o msg =>
    exact authMkSlotsRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  | recvNoOPK k j l msg =>
    exact authMkSlotsRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact SlotM.run'_liftComp _ none

theorem run_none_liftM_isSome_false {α : Type} (m : ProbComp α)
    (y : α × Option Bytes) (hy : y ∈ support ((liftM m : SlotM Bytes α).run none))
    (hSome : y.2.isSome = true) : False := by
  simp only [StateT.run_monadLift, monadLift_self, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨_, _, rfl⟩
  cases hSome

theorem run_none_getRkAtSlot_bind_liftM_fire {S : Setup} (idx slotIdx : Nat)
    (f : Bytes → ProbComp (AuthResponse × AuthHybridStateFixed S))
    (hFire : slotIdx = idx → ∀ rk, ∀ x ∈ support (f rk), authCreationSlotFired idx x.2 = true)
    (y : (AuthResponse × AuthHybridStateFixed S) × Option Bytes)
    (hy : y ∈ support ((getRkAtSlot idx slotIdx >>= fun rk => liftM (f rk)).run none))
    (hSome : y.2.isSome = true) :
    authCreationSlotFired idx y.1.2 = true := by
  unfold getRkAtSlot at hy
  by_cases hEq : (slotIdx == idx) = true
  · simp only [hEq, ↓reduceIte, StateT.run_bind, SlotM.getSlot_run_none, bind_assoc, pure_bind,
      StateT.run_monadLift, monadLift_self,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨rk, _, x, hx, rfl⟩
    rw [beq_iff_eq] at hEq
    exact hFire hEq rk x hx
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨rk, _, x, _, rfl⟩
    cases hSome

theorem authMkSlotsStepSlot_fire (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (y : ((authSpec S).Range q × AuthHybridStateFixed S) × Option Bytes)
    (hWf : AuthSlotStateWf S hst)
    (hy : y ∈ support ((authMkSlotsStepSlot S P idx useIdealMkAt q hst).run none))
    (hSome : y.2.isSome = true) :
    authCreationSlotFired idx y.1.2 = true := by
  have hSendCase : ∀ (sid : SessionId S) (hSend : IsSendSessionId S sid)
      (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes),
      ∀ z ∈ support ((authMkSlotsSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst).run none),
        z.2.isSome = true → authCreationSlotFired idx z.1.2 = true := by
    intro sid hSend u bundle m0 m1 z hz hzSome
    unfold authMkSlotsSendSlot finishAuthSendAfterMkSlotsSlot at hz
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨prep, _, hz⟩
    cases prep with
    | done _ _ =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; cases hzSome
    | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only at hz; split at hz
      · exact False.elim (run_none_liftM_isSome_false _ z hz hzSome)
      · refine run_none_getRkAtSlot_bind_liftM_fire idx (hst.slots.allocSend sid).1 _ ?_ z hz hzSome
        intro hEq rk x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, rfl⟩
        unfold authCreationSlotFired finishAuthSendMkSlotsH3
        dsimp only
        rw [decide_eq_true_eq, ← hEq]
        exact allocSend_lt_nextSlot hst.slots sid hSend hWf.send_lt
  have hRecvCase : ∀ (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)),
      ∀ z ∈ support ((authMkSlotsRecvSlot S P idx useIdealMkAt msg prep? hst).run none),
        z.2.isSome = true → authCreationSlotFired idx z.1.2 = true := by
    intro msg prep? z hz hzSome
    unfold authMkSlotsRecvSlot finishAuthRecvUnmatchedAfterMkSlotsSlot at hz
    cases prep? with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; cases hzSome
    | some prep =>
      dsimp only at hz; split at hz
      · cases hMS : prep.matchedSess? with
        | some s =>
          rw [hMS] at hz; dsimp only at hz; split at hz
          · exact False.elim (run_none_liftM_isSome_false _ z hz hzSome)
          · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
              MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rk1, _, hz⟩
            cases hSpqr : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              rw [hSpqr] at hz; dsimp only at hz
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; cases hzSome
            | some pqr =>
              rcases pqr with ⟨_, _⟩; rw [hSpqr] at hz; dsimp only at hz; split at hz
              · exact False.elim (run_none_liftM_isSome_false _ z hz hzSome)
              · refine run_none_getRkAtSlot_bind_liftM_fire idx
                  (hst.slots.allocRecv hst.recvCount).1 _ ?_ z hz hzSome
                intro hEq rk x hx
                simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
                rcases hx with ⟨ck1_1, _, rfl⟩
                unfold authCreationSlotFired finishAuthRecvMkSlotsH3
                dsimp only
                rw [decide_eq_true_eq, ← hEq]
                exact allocRecv_lt_nextSlot hst.slots hst.recvCount hWf.recv_lt
        | none =>
          rw [hMS] at hz; dsimp only at hz
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨drKey, _, rk1, _, hz⟩
          cases hSpqr : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            rw [hSpqr] at hz; dsimp only at hz
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; cases hzSome
          | some pqr =>
            rcases pqr with ⟨_, _⟩; rw [hSpqr] at hz; dsimp only at hz; split at hz
            · exact False.elim (run_none_liftM_isSome_false _ z hz hzSome)
            · refine run_none_getRkAtSlot_bind_liftM_fire idx
                (hst.slots.allocRecv hst.recvCount).1 _ ?_ z hz hzSome
              intro hEq rk x hx
              simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨ck1_1, _, rfl⟩
              unfold authCreationSlotFired finishAuthRecvMkSlotsH3
              dsimp only
              rw [decide_eq_true_eq, ← hEq]
              exact allocRecv_lt_nextSlot hst.slots hst.recvCount hWf.recv_lt
      · exact False.elim (run_none_liftM_isSome_false _ z hz hzSome)
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot at hy; dsimp only at hy; split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; cases hSome
    · exact hSendCase (.sendOPK u i) trivial u bundle m0 m1 y hy hSome
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepSlot at hy; dsimp only at hy; split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; cases hSome
    · exact hSendCase (.sendNoOPK u i) trivial u bundle m0 m1 y hy hSome
  | recvOPK k j o msg => exact hRecvCase msg _ y hy hSome
  | recvNoOPK k j l msg => exact hRecvCase msg _ y hy hSome
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact False.elim (run_none_liftM_isSome_false _ y hy hSome)

theorem authMkSlotsStepWith_after (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : AuthSlotStateWf S hst) (hFired : authCreationSlotFired idx hst = true) :
    (prfMkSlotsAuthImpl S P idx mkSeedStar q).run hst =
      (authMkSlotsCutoffImpl S P idx q).run hst ∧
    ∀ x ∈ support ((authMkSlotsCutoffImpl S P idx q).run hst),
      authCreationSlotFired idx x.2 = true := by
  have hLt : idx < hst.slots.nextSlot := by
    simpa [authCreationSlotFired] using hFired
  have hMono : ∀ x ∈ support (authMkSlotsStepWith S P (fun _ => sampleBytes32)
      (fun s => decide (s < idx)) q hst), authCreationSlotFired idx x.2 = true := by
    intro x hx
    have hStep := authMkSlotsStepWith_wf_and_bounds P (fun _ => sampleBytes32)
      (fun s => decide (s < idx)) q hst hWf x hx
    simp only [authCreationSlotFired, decide_eq_true_eq]
    exact Nat.lt_of_lt_of_le hLt hStep.2.1
  refine ⟨?_, hMono⟩
  dsimp only [prfMkSlotsAuthImpl, authMkSlotsCutoffImpl, StateT.run_mk]
  have hSendEq : ∀ (sid : SessionId S) (hSend : IsSendSessionId S sid)
      (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes),
      authMkSlotsSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) sid u bundle m0 m1 hst =
      authMkSlotsSendWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx)) sid u bundle m0 m1 hst := by
    intro sid hSend u bundle m0 m1
    unfold authMkSlotsSendWith
    refine bind_congr_of_support (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst) _ _
      (fun prep hprep => ?_)
    have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hWf prep hprep
    cases prep with
    | done _ _ => rfl
    | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only [finishAuthSendAfterMkSlots]
      have hNone : hst.slots.lookupSend sid = none := hWf.send_fresh sid hP.1
      have hSIdx : (hst.slots.allocSend sid).1 = hst.slots.nextSlot :=
        (allocSend_of_none hst.slots sid hSend hNone).1
      have hNe : ((hst.slots.allocSend sid).1 == idx) = false :=
        beq_false_of_ne (by omega)
      simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  have hRecvEq : ∀ (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)),
      authMkSlotsRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg prep? hst =
      authMkSlotsRecvWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx)) msg prep? hst := by
    intro msg prep?
    unfold authMkSlotsRecvWith finishAuthRecvUnmatchedAfterMkSlots
    have hRSlot : (hst.slots.allocRecv hst.recvCount).1 = hst.slots.nextSlot :=
      (allocRecv_of_none (S := S) hst.slots hst.recvCount
        (hWf.recv_fresh hst.recvCount (Nat.le_refl _))).1
    have hNe : ((hst.slots.allocRecv hst.recvCount).1 == idx) = false :=
      beq_false_of_ne (by omega)
    cases prep? with
    | none => rfl
    | some prep =>
      dsimp only
      simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith; dsimp only; split
    · rfl
    · exact hSendEq (.sendOPK u i) trivial u bundle m0 m1
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith; dsimp only; split
    · rfl
    · exact hSendEq (.sendNoOPK u i) trivial u bundle m0 m1
  | recvOPK k j o msg => exact hRecvEq msg _
  | recvNoOPK k j l msg => exact hRecvEq msg _
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets => rfl

theorem evalDist_preSample_authMkSlots_eq_cutoff (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[do
        let mkSeedStar ← sampleBytes32
        authMkSlotsPreSampleRun S P idx mkSeedStar A] =
      𝒟[authMkSlotsCutoffExp S P idx A] := by
  unfold authMkSlotsPreSampleRun authMkSlotsCutoffExp
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep_inv
    sampleBytes32
    (AuthSlotStateWf S)
    (authCreationSlotFired idx)
    (authMkSlotsCutoffImpl S P idx)
    (fun mkSeedStar => prfMkSlotsAuthImpl S P idx mkSeedStar)
    (authMkSlotsStepSlot S P idx (fun s => decide (s < idx)))
    (authMkSlotsStepSlot_slotComp S P idx (fun s => decide (s < idx)))
    (authMkSlotsStepSlot_run'_some S P idx (fun s => decide (s < idx)))
    (fun q hst g _ => by
      dsimp only [authMkSlotsCutoffImpl, StateT.run_mk]
      rw [authMkSlotsStepSlot_run'_none S P idx (fun s => decide (s < idx)) q hst])
    (fun mkSeedStar q hst hWf hFired =>
      authMkSlotsStepWith_after S P idx mkSeedStar q hst hWf hFired)
    (fun q hst y hWf hy hSome =>
      authMkSlotsStepSlot_fire S P idx (fun s => decide (s < idx)) q hst y hWf hy hSome)
    (fun q hst hWf x hx =>
      (authMkSlotsStepWith_wf_and_bounds P (fun _ => sampleBytes32) (fun s => decide (s < idx))
        q hst hWf x hx).1)
    (fun q hst hWf =>
      SlotM.wf_run_none_of_run'_eq _ _
        (authMkSlotsStepSlot_run'_none S P idx (fun s => decide (s < idx)) q hst)
        (fun x hx =>
          (authMkSlotsStepWith_wf_and_bounds P (fun _ => sampleBytes32) (fun s => decide (s < idx))
            q hst hWf x hx).1))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (authSlotStateWf_empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

def projMkSlots0 {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { hst with slots := {} }

private theorem map2_ite_eq_ite {α β γ : Type} (f : β → γ) (g : α → β) (c : Bool)
    (t1 e1 : ProbComp α) (t2 e2 : ProbComp γ)
    (ht : c = true → f <$> (g <$> t1) = t2) (he : c = false → f <$> (g <$> e1) = e2) :
    (f <$> (g <$> if c then t1 else e1)) = (if c then t2 else e2) := by
  cases hc : c
  · exact he hc
  · exact ht hc

private theorem map_ite_eq_map2_ite {α β : Type} (f : β → β) (g : α → β) (c : Bool)
    (t1 e1 : ProbComp α) (t2 e2 : ProbComp α)
    (ht : c = true → g <$> t1 = f <$> (g <$> t2))
    (he : c = false → g <$> e1 = f <$> (g <$> e2)) :
    (g <$> if c then t1 else e1) = (f <$> (g <$> if c then t2 else e2)) := by
  cases hc : c
  · exact he hc
  · exact ht hc

theorem prepareAuthSendMkSlotsH3_projMkSlots0 {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    PreparedAuthSend.mapState projMkSlots0 <$> prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst =
      prepareAuthSendMk S P sid u bundle m0 m1 (projMkSlots0 hst) := by
  unfold prepareAuthSendMkSlotsH3 prepareAuthSendMk finishAuthHybridSend
  dsimp only [projMkSlots0]
  refine map2_ite_eq_ite _ _ _ _ _ _ _
    (fun _ => by simp [PreparedAuthSend.mapState, projMkSlots0]) fun _ => ?_
  refine map2_ite_eq_ite _ _ _ _ _ _ _
    (fun _ => by simp [PreparedAuthSend.mapState, projMkSlots0]) fun _ => ?_
  refine map2_ite_eq_ite _ _ _ _ _ _ _
    (fun _ => by simp [PreparedAuthSend.mapState, projMkSlots0]) fun _ => ?_
  cases List.find? (fun x => x.1 == u.val) hst.toAuthHybridState.base.principals with
  | none => simp [PreparedAuthSend.mapState, projMkSlots0]
  | some uPair =>
    rcases uPair with ⟨_, uEntry⟩; dsimp only
    refine map2_ite_eq_ite _ _ _ _ _ _ _
      (fun _ => by simp [PreparedAuthSend.mapState, projMkSlots0]) fun _ => ?_
    refine map2_ite_eq_ite _ _ _ _ _ _ _
      (fun _ => by simp [PreparedAuthSend.mapState, projMkSlots0]) fun _ => ?_
    simp only [map_bind]
    congr 1; funext ekASk; congr 1; funext kemCoins
    congr 1; funext ephASk; congr 1; funext spqrCoins
    refine map2_ite_eq_ite _ _ _ _ _ _ _
      (fun _ => by simp [PreparedAuthSend.mapState, projMkSlots0]) fun _ => ?_
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => simp [PreparedAuthSend.mapState, projMkSlots0]
    | some pair =>
      rcases pair with ⟨ss, kemCt⟩; dsimp only
      refine map2_ite_eq_ite _ _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => simp [PreparedAuthSend.mapState, projMkSlots0]
        | some spqrVal =>
          rcases spqrVal with ⟨_, _, _⟩; simp [PreparedAuthSend.mapState]
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => simp [PreparedAuthSend.mapState, projMkSlots0]
        | some spqrVal =>
          rcases spqrVal with ⟨_, _, _⟩; simp [PreparedAuthSend.mapState, projMkSlots0]

theorem authCkOtherStep_projMkSlots0 {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id projMkSlots0 <$> authCkOtherStep S P q hst =
      authCkOtherStep S P q (projMkSlots0 hst) := by
  unfold authCkOtherStep projMkSlots0
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp [map_eq_bind_pure_comp, Prod.map]

theorem step_authMkSlots_zero_projMkSlots0 {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id projMkSlots0 <$>
      authMkSlotsStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) q hst =
    authMkStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) q (projMkSlots0 hst) := by
  have hFalse : ∀ s : Nat, decide (s < 0) = false := fun _ => by simp
  have hSend : ∀ sid u bundle m0 m1,
      Prod.map id projMkSlots0 <$>
        authMkSlotsSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0))
          sid u bundle m0 m1 hst =
      authMkSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0))
        sid u bundle m0 m1 (projMkSlots0 hst) := by
    intro sid u bundle m0 m1
    unfold authMkSlotsSendWith authMkSendWith
    rw [← prepareAuthSendMkSlotsH3_projMkSlots0 P sid u bundle m0 m1 hst, bind_map_left, map_bind]
    congr 1; funext prep
    cases prep with
    | done resp hst' => simp [PreparedAuthSend.mapState, Prod.map]
    | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only [PreparedAuthSend.mapState, finishAuthSendAfterMkSlots, finishAuthSendAfterMk]
      simp only [hFalse, Bool.false_eq_true, ↓reduceIte, map_bind]
      congr 1
  have hRecv : ∀ msg prep?,
      Prod.map id projMkSlots0 <$>
        authMkSlotsRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) msg prep? hst =
      authMkRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0))
        msg prep? (projMkSlots0 hst) := by
    intro msg prep?
    unfold authMkSlotsRecvWith authMkRecvWith matchedSameEphMkSlotsWith
      finishAuthRecvUnmatchedAfterMkSlots finishAuthRecvUnmatchedAfterMk
    have hRC : (projMkSlots0 hst).recvCount = hst.recvCount := rfl
    have hMC : (projMkSlots0 hst).mkSaltCache = hst.mkSaltCache := rfl
    rw [hRC, hMC]
    cases prep? with
    | none => simp [projMkSlots0, Prod.map]
    | some prep =>
      dsimp only
      simp only [hFalse, Bool.false_eq_true, ↓reduceIte]
      split
      · cases prep.matchedSess? with
        | some s =>
          dsimp only; split
          · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => simp [projMkSlots0, Prod.map]
            | some pqr =>
              rcases pqr with ⟨_, _⟩
              dsimp only
              simp only [pure_bind, map_pure]
              rfl
          · simp only [map_bind]; congr 1; funext rk1
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => simp [projMkSlots0, Prod.map]
            | some pqr =>
              rcases pqr with ⟨_, _⟩; dsimp only
              simp only [map_bind]
              congr 1
        | none =>
          dsimp only; simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [projMkSlots0, Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, _⟩; dsimp only
            simp only [map_bind]
            congr 1
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [projMkSlots0, Prod.map]
        | some pqr => rcases pqr with ⟨_, _⟩; simp [projMkSlots0, Prod.map]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkStepWith; dsimp only; split
    · simp [Prod.map]
    · exact hSend (.sendOPK u i) u bundle m0 m1
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkStepWith; dsimp only; split
    · simp [Prod.map]
    · exact hSend (.sendNoOPK u i) u bundle m0 m1
  | recvOPK k j o msg => exact hRecv msg _
  | recvNoOPK k j l msg => exact hRecv msg _
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact authCkOtherStep_projMkSlots0 P _ hst

theorem evalDist_authMkSlotsCutoffExp_zero_eq_g3_7 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkSlotsCutoffExp S P 0 A.1] = 𝒟[authFixedExpAtStage .g3_7 S P A.1] := by
  rw [← evalDist_authMkCutoffExp_zero_eq_g3_7 S P b A]
  unfold authMkSlotsCutoffExp authMkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1
  exact (simulateQ_proj_inv_obs
    projMkSlots0 (fun _ => True)
    (authMkSlotsCutoffImpl S P 0) (authMkCutoffImpl S P 0)
    (fun q hst _ => ⟨(step_authMkSlots_zero_projMkSlots0 P q hst).symm, fun _ _ => trivial⟩)
    A.1.run
    (AuthHybridStateFixed.empty S secb) trivial
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun _ _ => rfl)).symm

theorem sessionSlotIndex_lt_n_sess_tot_of_isSend {S : Setup} (sid : SessionId S)
    (hSend : IsSendSessionId S sid) :
    sessionSlotIndex sid < S.N_sess_tot := by
  have hk := sendSlotIndex?_lt (sendSlotIndex?_of_isSendSessionId hSend)
  unfold Setup.N_sess_tot; omega

theorem isSendSessionId_of_lookupSend_some {S : Setup} (ss : AuthSlotState)
    (sid : SessionId S) (k : Nat) (hk : ss.lookupSend sid = some k) :
    IsSendSessionId S sid := by
  cases sid <;> simp [AuthSlotState.lookupSend, IsSendSessionId] at hk ⊢

theorem simulateQ_proj_inv_bound2_eq
    {ι α : Type} {QSpec : OracleSpec.{0, 0} ι} {St1 St2 : Type}
    (proj : St1 → St2) (Inv : St1 → Prop)
    (cnt1 : St1 → Nat) (isQ1 : (unifSpec + QSpec).Domain → Bool)
    (cnt2 : St1 → Nat) (isQ2 : (unifSpec + QSpec).Domain → Bool)
    (N1 N2 : Nat)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hStep : ∀ q st1, Inv st1 →
      (isQ1 (.inr q) = true → cnt1 st1 < N1) →
      (isQ2 (.inr q) = true → cnt2 st1 < N2) →
      Prod.map id proj <$> (impl1 q).run st1 = (impl2 q).run (proj st1) ∧
      ∀ x ∈ support ((impl1 q).run st1),
        Inv x.2 ∧
        cnt1 x.2 ≤ cnt1 st1 + (if isQ1 (.inr q) then 1 else 0) ∧
        cnt2 x.2 ≤ cnt2 st1 + (if isQ2 (.inr q) then 1 else 0))
    (oa : OracleComp (unifSpec + QSpec) α)
    (n1 n2 : Nat)
    (hB1 : OracleComp.IsQueryBoundP oa (fun q => isQ1 q = true) n1)
    (hB2 : OracleComp.IsQueryBoundP oa (fun q => isQ2 q = true) n2)
    (st1 : St1) (hInv : Inv st1)
    (hC1 : cnt1 st1 + n1 ≤ N1) (hC2 : cnt2 st1 + n2 ≤ N2)
    (obs1 : α × St1 → ProbComp Bool) (obs2 : α × St2 → ProbComp Bool)
    (hObs : ∀ a s1, obs1 (a, s1) = obs2 (a, proj s1)) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    ((simulateQ full1 oa).run st1 >>= obs1) =
      ((simulateQ full2 oa).run (proj st1) >>= obs2) := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing st1 n1 n2 with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a st1
  | query_bind q mx ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hB1 hB2
    rcases q with uq | gq
    · rw [simulateQ_run_query_inl_local, simulateQ_run_query_inl_local, bind_assoc, bind_assoc]
      congr 1; funext u
      exact ih u _ _ (hB1.2 u) (hB2.2 u) st1 hInv
        (by split_ifs <;> omega) (by split_ifs <;> omega)
    · have hLt1 : isQ1 (.inr gq) = true → cnt1 st1 < N1 := by
        intro hq1
        rcases hB1.1 with hAbs | hp
        · exact False.elim (hAbs hq1)
        · omega
      have hLt2 : isQ2 (.inr gq) = true → cnt2 st1 < N2 := by
        intro hq2
        rcases hB2.1 with hAbs | hp
        · exact False.elim (hAbs hq2)
        · omega
      obtain ⟨hEq, hInvStep⟩ := hStep gq st1 hInv hLt1 hLt2
      rw [simulateQ_run_query_inr_local, simulateQ_run_query_inr_local,
          ← hEq, bind_map_left, bind_assoc, bind_assoc]
      refine bind_congr_of_support ((impl1 gq).run st1) _ _ (fun ⟨r, st1'⟩ hx => ?_)
      obtain ⟨hInv', hCnt1', hCnt2'⟩ := hInvStep (r, st1') hx
      have hC1' : cnt1 st1' + (if isQ1 (.inr gq) = true then n1 - 1 else n1) ≤ N1 := by
        cases hq1 : isQ1 (.inr gq)
        · simp only [hq1, Bool.false_eq_true, ↓reduceIte] at hCnt1' ⊢; omega
        · have := hLt1 hq1; rcases hB1.1 with hAbs | hp
          · exact False.elim (hAbs hq1)
          · simp only [hq1, ↓reduceIte] at hCnt1' ⊢; omega
      have hC2' : cnt2 st1' + (if isQ2 (.inr gq) = true then n2 - 1 else n2) ≤ N2 := by
        cases hq2 : isQ2 (.inr gq)
        · simp only [hq2, Bool.false_eq_true, ↓reduceIte] at hCnt2' ⊢; omega
        · have := hLt2 hq2; rcases hB2.1 with hAbs | hp
          · exact False.elim (hAbs hq2)
          · simp only [hq2, ↓reduceIte] at hCnt2' ⊢; omega
      exact ih r _ _ (hB1.2 r) (hB2.2 r) st1' hInv' hC1' hC2'

theorem step_authMkSlots_end_projMkSlots0 {S : Setup} (P : Primitives) (M : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst)
    (hSess : isAuthSessQueryB (.inr q) = true → hst.slots.nextSlot < M)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    Prod.map id projMkSlots0 <$>
      authMkSlotsStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < M)) q hst =
    authMkStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
      q (projMkSlots0 hst) := by
  have hSend : ∀ sid (hSendSid : IsSendSessionId S sid) u bundle m0 m1,
      hst.slots.nextSlot < M →
      Prod.map id projMkSlots0 <$>
        authMkSlotsSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < M))
          sid u bundle m0 m1 hst =
      authMkSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
        sid u bundle m0 m1 (projMkSlots0 hst) := by
    intro sid hSendSid u bundle m0 m1 hNextLt
    unfold authMkSlotsSendWith authMkSendWith
    rw [← prepareAuthSendMkSlotsH3_projMkSlots0 P sid u bundle m0 m1 hst, bind_map_left, map_bind]
    refine bind_congr_of_support (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst) _ _
      (fun prep hprep => ?_)
    have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hWf prep hprep
    cases prep with
    | done resp hst' => simp [PreparedAuthSend.mapState, Prod.map]
    | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only [PreparedAuthSend.mapState, finishAuthSendAfterMkSlots, finishAuthSendAfterMk]
      have hSIdx : (hst.slots.allocSend sid).1 = hst.slots.nextSlot :=
        (allocSend_of_none hst.slots sid hSendSid (hWf.send_fresh sid hP.1)).1
      have hT1 : decide ((hst.slots.allocSend sid).1 < M) = true := by
        rw [decide_eq_true_eq, hSIdx]; exact hNextLt
      have hT2 : decide (sessionSlotIndex sid < S.N_sess_tot) = true := by
        rw [decide_eq_true_eq]; exact sessionSlotIndex_lt_n_sess_tot_of_isSend sid hSendSid
      simp only [hT1, hT2, ↓reduceIte, map_bind]
      congr 1
  have hRecvCase : ∀ msg prep?,
      hst.slots.nextSlot < M →
      hst.recvCount < S.N_recv_tot →
      (∀ prep, prep? = some prep → ∀ s, prep.matchedSess? = some s →
        s ∈ hst.toAuthHybridState.idealSessions) →
      Prod.map id projMkSlots0 <$>
        authMkSlotsRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < M)) msg prep? hst =
      authMkRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
        msg prep? (projMkSlots0 hst) := by
    intro msg prep? hNextLt hRCLt hMatched
    unfold authMkSlotsRecvWith authMkRecvWith matchedSameEphMkSlotsWith
      finishAuthRecvUnmatchedAfterMkSlots finishAuthRecvUnmatchedAfterMk
    have hRC : (projMkSlots0 hst).recvCount = hst.recvCount := rfl
    have hMC : (projMkSlots0 hst).mkSaltCache = hst.mkSaltCache := rfl
    have hRSlot : (hst.slots.allocRecv hst.recvCount).1 = hst.slots.nextSlot :=
      (allocRecv_of_none (S := S) hst.slots hst.recvCount
        (hWf.recv_fresh hst.recvCount (Nat.le_refl _))).1
    have hR1 : decide ((hst.slots.allocRecv hst.recvCount).1 < M) = true := by
      rw [decide_eq_true_eq, hRSlot]; exact hNextLt
    have hR2 : decide (S.N_send_tot + hst.recvCount < S.N_sess_tot) = true := by
      rw [decide_eq_true_eq]; unfold Setup.N_sess_tot; omega
    rw [hRC, hMC]
    cases prep? with
    | none => simp [projMkSlots0, Prod.map]
    | some prep =>
      dsimp only
      split
      · cases hMS : prep.matchedSess? with
        | some s =>
          dsimp only; split
          · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => simp [projMkSlots0, Prod.map]
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              have hsMem : s ∈ hst.toAuthHybridState.idealSessions := hMatched prep rfl s hMS
              obtain ⟨_, k, hkLt, hkEq⟩ := hWf.ideal_send s hsMem
              have hSIdxEq : hst.slots.lookupSendOrZero s.sid = k := by
                simp [AuthSlotState.lookupSendOrZero, hkEq]
              have hS1 : decide (hst.slots.lookupSendOrZero s.sid < M) = true := by
                rw [decide_eq_true_eq, hSIdxEq]; omega
              have hS2 : decide (sessionSlotIndex s.sid < S.N_sess_tot) = true := by
                rw [decide_eq_true_eq]
                exact sessionSlotIndex_lt_n_sess_tot_of_isSend s.sid
                  (isSendSessionId_of_lookupSend_some hst.slots s.sid k hkEq)
              dsimp only [matchedSameEphMkWith]
              simp only [hS1, hS2, ↓reduceIte, map_bind, map_pure]
              split
              · rfl
              · cases hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
                | some _ => rfl
                | none => simp only [bind_assoc, pure_bind]; rfl
          · simp only [map_bind]; congr 1; funext rk1
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => simp [projMkSlots0, Prod.map]
            | some pqr =>
              rcases pqr with ⟨_, _⟩; dsimp only
              simp only [map_bind]
              congr 1
        | none =>
          dsimp only; simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [projMkSlots0, Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, _⟩; dsimp only
            simp only [map_bind]
            congr 1
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [projMkSlots0, Prod.map]
        | some pqr => rcases pqr with ⟨_, _⟩; simp [projMkSlots0, Prod.map]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkStepWith; dsimp only; split
    · simp [Prod.map]
    · exact hSend (.sendOPK u i) trivial u bundle m0 m1 (hSess rfl)
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkStepWith; dsimp only; split
    · simp [Prod.map]
    · exact hSend (.sendNoOPK u i) trivial u bundle m0 m1 (hSess rfl)
  | recvOPK k j o msg =>
    exact hRecvCase msg _ (hSess rfl) (hRecv rfl)
      (fun prep hp => (prepareAuthHybridRecvOPK_props P k j o msg hst.toAuthHybridState prep hp).1)
  | recvNoOPK k j l msg =>
    exact hRecvCase msg _ (hSess rfl) (hRecv rfl)
      (fun prep hp => (prepareAuthHybridRecvNoOPK_props P k j l msg hst.toAuthHybridState prep hp).1)
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact authCkOtherStep_projMkSlots0 P _ hst

theorem evalDist_authMkSlotsCutoffExp_end_eq_g3_8 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkSlotsCutoffExp S P (min b.q_total S.N_sess_tot) A.1] =
      𝒟[authFixedExpAtStage .g3_8 S P A.1] := by
  rw [← evalDist_authMkCutoffExp_end_eq_g3_8 S P b A]
  unfold authMkSlotsCutoffExp authMkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1
  have hBSess : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthSessQueryB q = true)
      (min b.q_total S.N_sess_tot) := isQueryBoundP_isAuthSessQueryB_min S b A
  have hBRecv : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot :=
    by simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact simulateQ_proj_inv_bound2_eq
    projMkSlots0
    (AuthSlotStateWf S)
    (fun hst => hst.slots.nextSlot) (isAuthSessQueryB (S := S))
    (fun hst => hst.recvCount) (isAuthRecvQueryB (S := S))
    (min b.q_total S.N_sess_tot) S.N_recv_tot
    (authMkSlotsCutoffImpl S P (min b.q_total S.N_sess_tot))
    (authMkCutoffImpl S P S.N_sess_tot)
    (fun q hst hWf hSess hRecv =>
      ⟨step_authMkSlots_end_projMkSlots0 P (min b.q_total S.N_sess_tot) q hst hWf hSess hRecv,
       fun x hx => by
         obtain ⟨hW, _, hN, hR⟩ := authMkSlotsStepWith_wf_and_bounds P (fun _ => sampleBytes32)
           (fun s => decide (s < min b.q_total S.N_sess_tot)) q hst hWf x hx
         exact ⟨hW, hN, hR⟩⟩)
    A.1.run
    (min b.q_total S.N_sess_tot) S.N_recv_tot
    hBSess hBRecv
    (AuthHybridStateFixed.empty S secb) (authSlotStateWf_empty S secb)
    (by simp [AuthHybridStateFixed.empty])
    (by simp [AuthHybridStateFixed.empty])
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun _ _ => rfl)

/-! ## Creation-order `PrfMsgKeys` invariants and `hop_G3_7_G3_8` -/

def restoreIdealMkSlotsAtIdx {S : Setup} (slots : AuthSlotState)
    (idx : Nat) (mkSeedStar : Bytes) (s : IdealAuthSession S) : IdealAuthSession S :=
  if slots.lookupSendOrZero s.sid == idx then { s with mkSeed := mkSeedStar } else s

def restoreAuthMkSlotsAtIdx {S : Setup} (slots : AuthSlotState)
    (idx : Nat) (mkSeedStar : Bytes) (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with idealSessions := hst.idealSessions.map (restoreIdealMkSlotsAtIdx slots idx mkSeedStar) }

def filterOutMkSaltCacheSlotsAtIdx {S : Setup} (slots : AuthSlotState) (idx : Nat)
    (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    List ((SessionId S × Option Bytes) × (Nat × MessageKeys)) :=
  c.filter (fun (k, _) => !(slots.lookupSendOrZero k.1 == idx))

def restoreAuthFixedSlotsMkAtIdx {S : Setup} (idx : Nat) (mkSeedStar : Bytes)
    (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { toAuthHybridState := restoreAuthMkSlotsAtIdx hst.slots idx mkSeedStar hst.toAuthHybridState
    recvCount := hst.recvCount
    mkSaltCache := filterOutMkSaltCacheSlotsAtIdx hst.slots idx hst.mkSaltCache
    slots := hst.slots }

def restorePreparedAuthRecvSlotsMk {S : Setup} (slots : AuthSlotState)
    (idx : Nat) (mkSeedStar : Bytes) (prep : PreparedAuthRecv S) : PreparedAuthRecv S :=
  { prep with
    hstDec := restoreAuthMkSlotsAtIdx slots idx mkSeedStar prep.hstDec
    matchedSess? := prep.matchedSess?.map (restoreIdealMkSlotsAtIdx slots idx mkSeedStar)
    finish := fun res? =>
      ((prep.finish res?).1, restoreAuthMkSlotsAtIdx slots idx mkSeedStar (prep.finish res?).2) }

theorem lookupSendOrZero_allocRecv_of_none {S : Setup} (ss : AuthSlotState) (rc : Nat)
    (hNone : ss.recvTbl rc = none) :
    (AuthSlotState.lookupSendOrZero (S := S) (ss.allocRecv rc).2) =
      AuthSlotState.lookupSendOrZero (S := S) ss := by
  have hL := (allocRecv_of_none (S := S) ss rc hNone).2.2.1
  funext sid
  simp [AuthSlotState.lookupSendOrZero, hL sid]

theorem lookupSendOrZero_allocSend_ne {S : Setup} (ss : AuthSlotState)
    (sid sid' : SessionId S) (hSend : IsSendSessionId S sid)
    (hNone : ss.lookupSend sid = none) (hNe : sid' ≠ sid) :
    (ss.allocSend sid).2.lookupSendOrZero sid' = ss.lookupSendOrZero sid' := by
  have hL := (allocSend_of_none ss sid hSend hNone).2.2.2 sid'
  simp only [AuthSlotState.lookupSendOrZero, hL, hNe, ↓reduceIte]

theorem lookupSendOrZero_allocSend_self {S : Setup} (ss : AuthSlotState)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hNone : ss.lookupSend sid = none) :
    (ss.allocSend sid).2.lookupSendOrZero sid = (ss.allocSend sid).1 := by
  obtain ⟨h1, _, _, hL⟩ := allocSend_of_none ss sid hSend hNone
  simp only [AuthSlotState.lookupSendOrZero, hL sid, ↓reduceIte, h1, Option.getD_some]

theorem find?_filterOutMkSaltCacheSlotsAtIdx_of_ne {S : Setup} (slots : AuthSlotState)
    (idx : Nat) (sid : SessionId S) (salt? : Option Bytes)
    (hNe : (slots.lookupSendOrZero sid == idx) = false) :
    ∀ (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))),
      (filterOutMkSaltCacheSlotsAtIdx slots idx c).find? (fun (k, _) => mkSaltKeyMatch k sid salt?) =
        c.find? (fun (k, _) => mkSaltKeyMatch k sid salt?)
  | [] => rfl
  | ((sid', salt'), v) :: rest => by
    unfold filterOutMkSaltCacheSlotsAtIdx
    rw [List.filter_cons]
    by_cases hEq : (!(slots.lookupSendOrZero sid' == idx)) = true
    · simp only [hEq, ↓reduceIte, List.find?]
      rw [← filterOutMkSaltCacheSlotsAtIdx,
        find?_filterOutMkSaltCacheSlotsAtIdx_of_ne slots idx sid salt? hNe rest]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      have hIdx' : (slots.lookupSendOrZero sid' == idx) = true := by revert hEq; simp
      have hne_pair : mkSaltKeyMatch (sid', salt') sid salt? = false := by
        have hSidNe : sid' ≠ sid := by
          rintro rfl
          rw [hNe] at hIdx'; cases hIdx'
        simp [mkSaltKeyMatch, hSidNe]
      rw [List.find?, hne_pair, ← filterOutMkSaltCacheSlotsAtIdx]
      exact find?_filterOutMkSaltCacheSlotsAtIdx_of_ne slots idx sid salt? hNe rest

theorem filterOutMkSaltCacheSlotsAtIdx_cons_of_ne {S : Setup} (slots : AuthSlotState)
    (idx : Nat) (sid : SessionId S) (salt? : Option Bytes) (v : Nat × MessageKeys)
    (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (hNe : (slots.lookupSendOrZero sid == idx) = false) :
    filterOutMkSaltCacheSlotsAtIdx slots idx (((sid, salt?), v) :: c) =
      ((sid, salt?), v) :: filterOutMkSaltCacheSlotsAtIdx slots idx c := by
  unfold filterOutMkSaltCacheSlotsAtIdx
  simp [hNe]

theorem filterOutMkSaltCacheSlotsAtIdx_cons_of_eq {S : Setup} (slots : AuthSlotState)
    (idx : Nat) (sid : SessionId S) (salt? : Option Bytes) (v : Nat × MessageKeys)
    (c : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (hEq : (slots.lookupSendOrZero sid == idx) = true) :
    filterOutMkSaltCacheSlotsAtIdx slots idx (((sid, salt?), v) :: c) =
      filterOutMkSaltCacheSlotsAtIdx slots idx c := by
  unfold filterOutMkSaltCacheSlotsAtIdx
  simp [hEq]

theorem matchIdealAuthHandshake_restoreIdealMkSlotsAtIdx {S : Setup} (P : Primitives)
    (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr
      (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s) =
      matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s := by
  unfold restoreIdealMkSlotsAtIdx; split <;> rfl

theorem find?_matchIdealAuthHandshake_restoreIdealMkSlotsAtIdx {S : Setup} (P : Primitives)
    (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (l : List (IdealAuthSession S)) :
    (l.map (restoreIdealMkSlotsAtIdx slots idx mkSeedStar)).find?
        (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr) =
      (l.find? (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr)).map
        (restoreIdealMkSlotsAtIdx slots idx mkSeedStar) := by
  induction l with
  | nil => rfl
  | cons s tl ih =>
    simp only [List.map_cons, List.find?_cons, matchIdealAuthHandshake_restoreIdealMkSlotsAtIdx]
    cases matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s
    · exact ih
    · rfl

theorem match_sameEph_map_restoreIdealMkSlotsAtIdx {S : Setup} (P : Primitives)
    (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (ms? : Option (IdealAuthSession S)) (ephAPk : Bytes) :
    (match ms?.map (restoreIdealMkSlotsAtIdx slots idx mkSeedStar) with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) =
    (match ms? with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) := by
  cases ms? with
  | none => rfl
  | some s => dsimp only [Option.map, restoreIdealMkSlotsAtIdx]; split <;> rfl

theorem finishAuthHybridRecvOPK_restoreAuthMkSlotsAtIdx {S : Setup}
    (checkAuth : Bool) (P : Primitives) (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg
      hstDec res?
    (x.1, restoreAuthMkSlotsAtIdx slots idx mkSeedStar x.2) =
      finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg
        (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hstDec) res? := by
  dsimp only [restoreAuthMkSlotsAtIdx]
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p => rcases p with ⟨_, senderEntry⟩; dsimp only; cases senderEntry.corrupted <;> rfl

theorem finishAuthHybridRecvNoOPK_restoreAuthMkSlotsAtIdx {S : Setup}
    (checkAuth : Bool) (P : Primitives) (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?
    (x.1, restoreAuthMkSlotsAtIdx slots idx mkSeedStar x.2) =
      finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg
        (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hstDec) res? := by
  dsimp only [restoreAuthMkSlotsAtIdx]
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p => rcases p with ⟨_, senderEntry⟩; dsimp only; cases senderEntry.corrupted <;> rfl

theorem prepareAuthHybridRecvOPK_restoreAuthMkSlotsAtIdx {S : Setup}
    (checkAuth : Bool) (P : Primitives) (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvOPK checkAuth P k j o msg (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst) =
      (prepareAuthHybridRecvOPK checkAuth P k j o msg hst).map
        (restorePreparedAuthRecvSlotsMk slots idx mkSeedStar) := by
  unfold prepareAuthHybridRecvOPK restorePreparedAuthRecvSlotsMk
  have hB : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).base = hst.base := rfl
  have hIK : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).initKemRecs = hst.initKemRecs := rfl
  have hRK : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).recvKemRecs = hst.recvKemRecs := rfl
  have hIS : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).idealSessions =
      hst.idealSessions.map (restoreIdealMkSlotsAtIdx slots idx mkSeedStar) := rfl
  dsimp only; rw [hB]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split; · rfl
    split
    · rfl
    · simp only [Option.map_some, hIK, hRK, hIS,
        find?_matchIdealAuthHandshake_restoreIdealMkSlotsAtIdx]
      congr 2
      · exact match_sameEph_map_restoreIdealMkSlotsAtIdx P slots idx mkSeedStar _ _
      · funext res?
        unfold finishAuthHybridRecvOPK restoreAuthMkSlotsAtIdx
        cases res? with
        | none => rfl
        | some r =>
          rcases r with ⟨_, _, _, _, _, _⟩; dsimp only
          cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
          | none => rfl
          | some p => rcases p with ⟨_, sE⟩; dsimp only; cases sE.corrupted <;> rfl
  · rfl

theorem prepareAuthHybridRecvNoOPK_restoreAuthMkSlotsAtIdx {S : Setup}
    (checkAuth : Bool) (P : Primitives) (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvNoOPK checkAuth P k j l msg (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst) =
      (prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst).map
        (restorePreparedAuthRecvSlotsMk slots idx mkSeedStar) := by
  unfold prepareAuthHybridRecvNoOPK restorePreparedAuthRecvSlotsMk
  have hB : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).base = hst.base := rfl
  have hIK : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).initKemRecs = hst.initKemRecs := rfl
  have hRK : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).recvKemRecs = hst.recvKemRecs := rfl
  have hIS : (restoreAuthMkSlotsAtIdx slots idx mkSeedStar hst).idealSessions =
      hst.idealSessions.map (restoreIdealMkSlotsAtIdx slots idx mkSeedStar) := rfl
  dsimp only; rw [hB]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split
    · rfl
    · simp only [Option.map_some, hIK, hRK, hIS,
        find?_matchIdealAuthHandshake_restoreIdealMkSlotsAtIdx]
      congr 2
      · exact match_sameEph_map_restoreIdealMkSlotsAtIdx P slots idx mkSeedStar _ _
      · funext res?
        unfold finishAuthHybridRecvNoOPK restoreAuthMkSlotsAtIdx
        cases res? with
        | none => rfl
        | some r =>
          rcases r with ⟨_, _, _, _, _, _⟩; dsimp only
          cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
          | none => rfl
          | some p => rcases p with ⟨_, sE⟩; dsimp only; cases sE.corrupted <;> rfl
  · rfl

theorem prepareAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) =
      PreparedAuthSend.mapState (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar) <$>
        prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst := by
  unfold prepareAuthSendMkSlotsH3 prepareAuthSendMk finishAuthHybridSend
  have hBase : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).toAuthHybridState.base =
      hst.toAuthHybridState.base := rfl
  have hIK : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).toAuthHybridState.initKemRecs =
      hst.toAuthHybridState.initKemRecs := rfl
  have hRK : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).toAuthHybridState.recvKemRecs =
      hst.toAuthHybridState.recvKemRecs := rfl
  have hRC : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).recvCount = hst.recvCount := rfl
  have hSl : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).slots = hst.slots := rfl
  dsimp only
  simp only [hBase, hIK, hRK, hRC, hSl]
  refine map_ite_eq_map2_ite _ _ _ _ _ _ _
    (fun _ => by simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]) fun _ => ?_
  refine map_ite_eq_map2_ite _ _ _ _ _ _ _
    (fun _ => by simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]) fun _ => ?_
  refine map_ite_eq_map2_ite _ _ _ _ _ _ _
    (fun _ => by simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]) fun _ => ?_
  cases List.find? (fun x => x.1 == u.val) hst.toAuthHybridState.base.principals with
  | none => simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]
  | some uPair =>
    rcases uPair with ⟨_, uEntry⟩; dsimp only
    refine map_ite_eq_map2_ite _ _ _ _ _ _ _
      (fun _ => by simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]) fun _ => ?_
    refine map_ite_eq_map2_ite _ _ _ _ _ _ _
      (fun _ => by simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]) fun _ => ?_
    simp only [map_bind]
    congr 1; funext ekASk; congr 1; funext kemCoins
    congr 1; funext ephASk; congr 1; funext spqrCoins
    refine map_ite_eq_map2_ite _ _ _ _ _ _ _
      (fun _ => by simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]) fun _ => ?_
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]
    | some pair =>
      rcases pair with ⟨ss, kemCt⟩; dsimp only
      refine map_ite_eq_map2_ite _ _ _ _ _ _ _ (fun _ => ?_) (fun hI => ?_)
      · simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]
        | some spqrVal =>
          rcases spqrVal with ⟨_, _, _⟩
          simp [PreparedAuthSend.mapState]
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx]
        | some spqrVal =>
          rcases spqrVal with ⟨_, _, _⟩
          simp [PreparedAuthSend.mapState, restoreAuthFixedSlotsMkAtIdx, restoreAuthMkSlotsAtIdx, hI]

theorem finishAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx_eq {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst)
    (hSaltSend : ∀ e ∈ hst.mkSaltCache, hst.toAuthHybridState.base.usedSendSessions.contains e.1.1 = true)
    (hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid = false)
    (hIdx : ((hst.slots.allocSend sid).1 == idx) = true)
    (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (deriveMessageKeys : MessageKeys) :
    finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeedStar ck1_1
      spqrSalt? pqRatchetMsg msgPlain
      { restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst with slots := (hst.slots.allocSend sid).2 }
      deriveMessageKeys =
    Prod.map id (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar)
      (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain
        { hst with slots := (hst.slots.allocSend sid).2 } deriveMessageKeys) := by
  have hNone : hst.slots.lookupSend sid = none := hWf.send_fresh sid hFresh
  have hMapEq :
      hst.toAuthHybridState.idealSessions.map (restoreIdealMkSlotsAtIdx hst.slots idx mkSeedStar) =
      hst.toAuthHybridState.idealSessions.map
        (restoreIdealMkSlotsAtIdx (hst.slots.allocSend sid).2 idx mkSeedStar) := by
    refine List.map_congr_left (fun s hs => ?_)
    have hU := (hWf.ideal_send s hs).1
    have hNe : s.sid ≠ sid := by intro h; rw [h, hFresh] at hU; cases hU
    simp only [restoreIdealMkSlotsAtIdx, lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe]
  have hFiltEq :
      filterOutMkSaltCacheSlotsAtIdx hst.slots idx hst.mkSaltCache =
      filterOutMkSaltCacheSlotsAtIdx (hst.slots.allocSend sid).2 idx hst.mkSaltCache := by
    unfold filterOutMkSaltCacheSlotsAtIdx
    refine List.filter_congr (fun e he => ?_)
    have hU := hSaltSend e he
    have hNe : e.1.1 ≠ sid := by intro h; rw [h, hFresh] at hU; cases hU
    simp only [lookupSendOrZero_allocSend_ne hst.slots sid e.1.1 hSend hNone hNe]
  have hSelf : ((hst.slots.allocSend sid).2.lookupSendOrZero sid == idx) = true := by
    rw [lookupSendOrZero_allocSend_self hst.slots sid hSend hNone]; exact hIdx
  unfold finishAuthSendMkSlotsH3 finishAuthSendMk finishAuthHybridSend
    restoreAuthFixedSlotsMkAtIdx restoreAuthMkSlotsAtIdx
  dsimp only [Prod.map, id]
  simp only [Prod.mk.injEq, AuthHybridStateFixed.mk.injEq, AuthHybridState.mk.injEq,
    true_and, and_true, hFiltEq]
  split_ifs
  · simp [restoreIdealMkSlotsAtIdx, hSelf, hMapEq]
  · exact hMapEq

theorem finishAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx_ne {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst)
    (hSaltSend : ∀ e ∈ hst.mkSaltCache, hst.toAuthHybridState.base.usedSendSessions.contains e.1.1 = true)
    (hFresh : hst.toAuthHybridState.base.usedSendSessions.contains sid = false)
    (hNeIdx : ((hst.slots.allocSend sid).1 == idx) = false)
    (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes) (spqrSalt? : Option Bytes)
    (pqRatchetMsg msgPlain : Bytes) (deriveMessageKeys : MessageKeys) :
    finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain
      { restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst with slots := (hst.slots.allocSend sid).2 }
      deriveMessageKeys =
    Prod.map id (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar)
      (finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain
        { hst with slots := (hst.slots.allocSend sid).2 } deriveMessageKeys) := by
  have hNone : hst.slots.lookupSend sid = none := hWf.send_fresh sid hFresh
  have hMapEq :
      hst.toAuthHybridState.idealSessions.map (restoreIdealMkSlotsAtIdx hst.slots idx mkSeedStar) =
      hst.toAuthHybridState.idealSessions.map
        (restoreIdealMkSlotsAtIdx (hst.slots.allocSend sid).2 idx mkSeedStar) := by
    refine List.map_congr_left (fun s hs => ?_)
    have hU := (hWf.ideal_send s hs).1
    have hNe : s.sid ≠ sid := by intro h; rw [h, hFresh] at hU; cases hU
    simp only [restoreIdealMkSlotsAtIdx, lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe]
  have hFiltEq :
      filterOutMkSaltCacheSlotsAtIdx hst.slots idx hst.mkSaltCache =
      filterOutMkSaltCacheSlotsAtIdx (hst.slots.allocSend sid).2 idx hst.mkSaltCache := by
    unfold filterOutMkSaltCacheSlotsAtIdx
    refine List.filter_congr (fun e he => ?_)
    have hU := hSaltSend e he
    have hNe : e.1.1 ≠ sid := by intro h; rw [h, hFresh] at hU; cases hU
    simp only [lookupSendOrZero_allocSend_ne hst.slots sid e.1.1 hSend hNone hNe]
  have hSelf : ((hst.slots.allocSend sid).2.lookupSendOrZero sid == idx) = false := by
    rw [lookupSendOrZero_allocSend_self hst.slots sid hSend hNone]; exact hNeIdx
  unfold finishAuthSendMkSlotsH3 finishAuthSendMk finishAuthHybridSend
    restoreAuthFixedSlotsMkAtIdx restoreAuthMkSlotsAtIdx
  dsimp only [Prod.map, id]
  simp only [Prod.mk.injEq, AuthHybridStateFixed.mk.injEq, AuthHybridState.mk.injEq,
    true_and, and_true, hFiltEq]
  split_ifs
  · simp [restoreIdealMkSlotsAtIdx, hSelf, hMapEq]
  · exact hMapEq

theorem finishAuthRecvMkSlotsH3_restorePreparedAuthRecvSlotsMk {S : Setup} (P : Primitives)
    (slots slots' : AuthSlotState)
    (hL : AuthSlotState.lookupSendOrZero (S := S) slots' =
      AuthSlotState.lookupSendOrZero (S := S) slots)
    (idx : Nat) (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) :
    finishAuthRecvMkSlotsH3 P msg (restorePreparedAuthRecvSlotsMk slots idx mkSeedStar prep)
      drKey rk1 ck1_1 recvCount' (filterOutMkSaltCacheSlotsAtIdx slots idx mkSaltCache')
      slots' deriveMessageKeys =
    Prod.map id (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar)
      (finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 recvCount'
        mkSaltCache' slots' deriveMessageKeys) := by
  unfold finishAuthRecvMkSlotsH3 finishAuthRecvMk restorePreparedAuthRecvSlotsMk
    restoreAuthFixedSlotsMkAtIdx restoreAuthMkSlotsAtIdx
    filterOutMkSaltCacheSlotsAtIdx restoreIdealMkSlotsAtIdx
  dsimp only [Prod.map, id]
  simp only [hL]

theorem authCkOtherStep_restoreAuthFixedSlotsMkAtIdx {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    authCkOtherStep S P q (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) =
      Prod.map id (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar) <$> authCkOtherStep S P q hst := by
  unfold authCkOtherStep restoreAuthFixedSlotsMkAtIdx restoreAuthMkSlotsAtIdx
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp [map_eq_bind_pure_comp, Prod.map]

structure InvMkSlotsTrue (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache) : Prop where
  wf : AuthSlotStateWf S st.1.1
  saltCache_send : ∀ e ∈ st.1.1.mkSaltCache,
    st.1.1.toAuthHybridState.base.usedSendSessions.contains e.1.1 = true
  sentChal_imp : st.1.2 = true → idx < st.1.1.slots.nextSlot
  ideal_msgKeys : ∀ s ∈ st.1.1.toAuthHybridState.idealSessions,
    (st.1.1.slots.lookupSendOrZero s.sid == idx) = true →
    s.deriveMessageKeys = deriveMsgKeysEff P mkSeedStar s.spqrSalt?
  cache_msgKeys : ∀ e ∈ st.1.1.mkSaltCache,
    (st.1.1.slots.lookupSendOrZero e.1.1 == idx) = true →
    e.2.2 = deriveMsgKeysEff P mkSeedStar e.1.2

theorem invMkSlotsTrue_empty (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes)
    (secb : Bool) :
    InvMkSlotsTrue S P idx mkSeedStar ((AuthHybridStateFixed.empty S secb, false), []) where
  wf := authSlotStateWf_empty S secb
  saltCache_send _ he := by cases he
  sentChal_imp h := by cases h
  ideal_msgKeys _ hs := by cases hs
  cache_msgKeys _ he := by cases he

theorem matchedSameEphMkSlotsRedProb_evalPrfMkReal {S : Setup} (P : Primitives)
    (slots : AuthSlotState) (idx : Nat) (mkSeedStar : Bytes)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (hWF : WellFormedPrimitivesδ P) (hSaltOK : SaltOK spqrSalt?)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (cache : PrfMkCache)
    (hsMsg : (slots.lookupSendOrZero s.sid == idx) = true →
      s.deriveMessageKeys = deriveMsgKeysEff P mkSeedStar s.spqrSalt?)
    (hCache : ∀ e ∈ mkSaltCache,
      (slots.lookupSendOrZero e.1.1 == idx) = true →
      e.2.2 = deriveMsgKeysEff P mkSeedStar e.1.2) :
    ((fun ((mk, mkSaltCache'), _) =>
        (mk, filterOutMkSaltCacheSlotsAtIdx slots idx mkSaltCache')) <$>
      matchedSameEphMkSlotsRedProb S P idx (evalPrfMkReal P mkSeedStar)
        s (slots.lookupSendOrZero s.sid) spqrSalt? recvCount mkSaltCache cache) =
      matchedSameEphMkSlotsWith P (fun slot => decide (slot < idx))
        (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s)
        (slots.lookupSendOrZero (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s).sid)
        spqrSalt? recvCount (filterOutMkSaltCacheSlotsAtIdx slots idx mkSaltCache) ∧
    (∀ x ∈ support (matchedSameEphMkSlotsRedProb S P idx (evalPrfMkReal P mkSeedStar)
        s (slots.lookupSendOrZero s.sid) spqrSalt? recvCount mkSaltCache cache),
      (∀ e ∈ x.1.2, e ∈ mkSaltCache ∨ e.1.1 = s.sid) ∧
      (∀ e ∈ x.1.2, (slots.lookupSendOrZero e.1.1 == idx) = true →
        e.2.2 = deriveMsgKeysEff P mkSeedStar e.1.2)) := by
  unfold matchedSameEphMkSlotsRedProb matchedSameEphMkSlotsWith evalPrfMkReal
  have hSid : (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s).sid = s.sid := by
    unfold restoreIdealMkSlotsAtIdx; split <;> rfl
  have hSalt : (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s).spqrSalt? = s.spqrSalt? := by
    unfold restoreIdealMkSlotsAtIdx; split <;> rfl
  have hMsg : (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s).deriveMessageKeys =
      s.deriveMessageKeys := by
    unfold restoreIdealMkSlotsAtIdx; split <;> rfl
  dsimp only
  simp only [hSid, hSalt, hMsg]
  cases hIdx : (slots.lookupSendOrZero s.sid == idx)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hLt : slots.lookupSendOrZero s.sid < idx
    · simp only [hLt, decide_true, ↓reduceIte]
      cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [find?_filterOutMkSaltCacheSlotsAtIdx_of_ne slots idx s.sid spqrSalt? hIdx mkSaltCache]
        cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some entry =>
          rcases entry with ⟨k, rc, mk⟩
          dsimp only
          refine ⟨by simp, fun x hx => ?_⟩
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact ⟨fun e he => Or.inl he, hCache⟩
        | none =>
          dsimp only
          refine ⟨?_, fun x hx => ?_⟩
          · simp [filterOutMkSaltCacheSlotsAtIdx_cons_of_ne slots idx s.sid spqrSalt? _ mkSaltCache hIdx]
          · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨mk, _, rfl⟩
            refine ⟨fun e he => ?_, fun e he hEIdx => ?_⟩
            · rcases List.mem_cons.mp he with rfl | he'
              · exact Or.inr rfl
              · exact Or.inl he'
            · rcases List.mem_cons.mp he with rfl | he'
              · dsimp only at hEIdx; rw [hIdx] at hEIdx; cases hEIdx
              · exact hCache e he' hEIdx
      · simp only [↓reduceIte]
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨fun e he => Or.inl he, hCache⟩
    · simp only [hLt, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hMk : (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s).mkSeed = s.mkSeed := by
        unfold restoreIdealMkSlotsAtIdx; simp [hIdx]
      rw [hMk]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨fun e he => Or.inl he, hCache⟩
  · have hLtF : decide (slots.lookupSendOrZero s.sid < idx) = false := decide_lt_of_beq_true hIdx
    have hMk : (restoreIdealMkSlotsAtIdx slots idx mkSeedStar s).mkSeed = mkSeedStar := by
      unfold restoreIdealMkSlotsAtIdx; simp [hIdx]
    simp only [↓reduceIte, hLtF, Bool.false_eq_true, hMk]
    cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some entry =>
        rcases entry with ⟨k, rc, mk⟩
        have hMem := List.mem_of_find?_eq_some hFind
        have hPred := List.find?_some hFind
        dsimp only at hPred
        obtain ⟨hKSid, hKSalt⟩ := mkSaltKeyMatch_sameSaltKey hPred
        have hMkEq : mk = P.deriveMsgKeys mkSeedStar spqrSalt? := by
          have hC := hCache (k, (rc, mk)) hMem (by dsimp only; rw [hKSid]; exact hIdx)
          dsimp only at hC
          rw [hC, deriveMsgKeysEff_congr P mkSeedStar hKSalt,
            deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
        subst hMkEq
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨fun e he => Or.inl he, hCache⟩
      | none =>
        dsimp only
        refine ⟨?_, fun x hx => ?_⟩
        · simp [filterOutMkSaltCacheSlotsAtIdx_cons_of_eq slots idx s.sid spqrSalt? _ mkSaltCache hIdx,
            deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
        · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hx
          subst hx
          refine ⟨fun e he => ?_, fun e he hEIdx => ?_⟩
          · rcases List.mem_cons.mp he with rfl | he'
            · exact Or.inr rfl
            · exact Or.inl he'
          · rcases List.mem_cons.mp he with rfl | he'
            · rfl
            · exact hCache e he' hEIdx
    · simp only [↓reduceIte]
      rw [hsMsg hIdx, ← deriveMsgKeysEff_congr P mkSeedStar hSameSalt,
        deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨fun e he => Or.inl he, hCache⟩

theorem finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkReal {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (hWF : WellFormedPrimitivesδ P) (hSaltOK : SaltOK spqrSalt?)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkSlotsTrue S P idx mkSeedStar ((hst, sentChal), cache))
    (hPrep : ∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
                     (prep.finish res?).2.base.usedSendSessions =
                       hst.toAuthHybridState.base.usedSendSessions) :
    let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
    ((fun ((resp, hst'), _) => (resp, restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst')) <$>
      finishAuthRecvUnmatchedSlotsRedProb S P idx (evalPrfMkReal P mkSeedStar) msg prep
        drKey rk1 spqrSalt? rSlot (hst.recvCount + 1)
        hst.mkSaltCache slots' sentChal cache) =
      finishAuthRecvUnmatchedAfterMkSlots P
        (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep)
        drKey rk1 spqrSalt? rSlot (hst.recvCount + 1)
        (filterOutMkSaltCacheSlotsAtIdx hst.slots idx hst.mkSaltCache) slots' ∧
    (∀ x ∈ support (finishAuthRecvUnmatchedSlotsRedProb S P idx (evalPrfMkReal P mkSeedStar)
        msg prep drKey rk1 spqrSalt? rSlot (hst.recvCount + 1)
        hst.mkSaltCache slots' sentChal cache),
      InvMkSlotsTrue S P idx mkSeedStar ((x.1.2, sentChal), x.2)) := by
  have hNone : hst.slots.recvTbl hst.recvCount = none :=
    hInv.wf.recv_fresh hst.recvCount (Nat.le_refl _)
  have hRSlot : (hst.slots.allocRecv hst.recvCount).1 = hst.slots.nextSlot :=
    (allocRecv_of_none (S := S) hst.slots hst.recvCount hNone).1
  have hL : AuthSlotState.lookupSendOrZero (S := S) (hst.slots.allocRecv hst.recvCount).2 =
      AuthSlotState.lookupSendOrZero (S := S) hst.slots :=
    lookupSendOrZero_allocRecv_of_none hst.slots hst.recvCount hNone
  have hInvPost : ∀ res? deriveMessageKeys sentChal' cache',
      (sentChal' = true → idx < hst.slots.nextSlot + 1) →
      InvMkSlotsTrue S P idx mkSeedStar
        (((finishAuthRecvMkSlotsH3 P msg prep drKey rk1 res? (hst.recvCount + 1) hst.mkSaltCache
            (hst.slots.allocRecv hst.recvCount).2 deriveMessageKeys).2, sentChal'), cache') := by
    intro ck1_1 deriveMessageKeys sentChal' cache' hSC'
    dsimp only [finishAuthRecvMkSlotsH3, finishAuthRecvMk]
    obtain ⟨hW', hN'⟩ := @authSlotStateWf_of_allocRecv S hst
      { toAuthHybridState := (prep.finish _).2, recvCount := hst.recvCount + 1,
        mkSaltCache := hst.mkSaltCache, slots := (hst.slots.allocRecv hst.recvCount).2 }
      hInv.wf rfl (hPrep _).1 (hPrep _).2 rfl
    refine ⟨hW', ?_, ?_, ?_, ?_⟩
    · intro e he; dsimp only at he ⊢; rw [(hPrep _).2]; exact hInv.saltCache_send e he
    · intro hS; have h1 := hSC' hS; dsimp only at hN' hS ⊢; omega
    · intro s hs hI; dsimp only at hs hI; rw [(hPrep _).1] at hs; rw [hL] at hI
      exact hInv.ideal_msgKeys s hs hI
    · intro e he hI; dsimp only at he hI; rw [hL] at hI
      exact hInv.cache_msgKeys e he hI
  unfold finishAuthRecvUnmatchedSlotsRedProb finishAuthRecvUnmatchedAfterMkSlots evalPrfMkReal
  dsimp only
  cases hIdx : ((hst.slots.allocRecv hst.recvCount).1 == idx)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hLt : decide ((hst.slots.allocRecv hst.recvCount).1 < idx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, fun x hx => ?_⟩
      · simp only [map_bind]
        congr 1; funext mkSeed; congr 1; funext ck1_1
        simp only [map_pure]
        rw [finishAuthRecvMkSlotsH3_restorePreparedAuthRecvSlotsMk P hst.slots _ hL]
        rfl
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        exact hInvPost ck1_1 _ sentChal cache (fun hS => by
          have h0 := hInv.sentChal_imp hS; dsimp only at h0; omega)
    · simp only [↓reduceIte]
      refine ⟨?_, fun x hx => ?_⟩
      · simp only [map_bind]
        congr 1; funext ck1_1; congr 1; funext deriveMessageKeys
        simp only [map_pure]
        rw [finishAuthRecvMkSlotsH3_restorePreparedAuthRecvSlotsMk P hst.slots _ hL]
        rfl
      · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        exact hInvPost ck1_1 _ sentChal cache (fun hS => by
          have h0 := hInv.sentChal_imp hS; dsimp only at h0; omega)
  · have hRSlot : (hst.slots.allocRecv hst.recvCount).1 = hst.slots.nextSlot :=
      (allocRecv_of_none (S := S) hst.slots hst.recvCount hNone).1
    have hSC : sentChal = false := by
      cases hB : sentChal
      · rfl
      · have hLt := hInv.sentChal_imp hB
        dsimp only at hLt
        have hEqIdx : (hst.slots.allocRecv hst.recvCount).1 = idx := beq_iff_eq.mp hIdx
        omega
    have hLtF : decide ((hst.slots.allocRecv hst.recvCount).1 < idx) = false :=
      decide_lt_of_beq_true hIdx
    simp only [↓reduceIte, hSC, Bool.not_false, hLtF, Bool.false_eq_true, pure_bind]
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [map_bind]
      congr 1; funext ck1_1
      simp only [map_pure, deriveMsgKeysEff_eq hWF mkSeedStar hSaltOK]
      rw [finishAuthRecvMkSlotsH3_restorePreparedAuthRecvSlotsMk P hst.slots _ hL]
      rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, rfl⟩
      exact hInvPost ck1_1 _ false cache (fun h => by cases h)

theorem authMkSlotsRecvRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hWF : WellFormedPrimitivesδ P)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkSlotsTrue S P idx mkSeedStar ((hst, sentChal), cache))
    (hPrepProps : ∀ prep, prep? = some prep →
      (∀ s, prep.matchedSess? = some s → s ∈ hst.toAuthHybridState.idealSessions) ∧
      (∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
               (prep.finish res?).2.base.usedSendSessions =
                 hst.toAuthHybridState.base.usedSendSessions)) :
    ((fun ((resp, hst'), _) => (resp, restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst')) <$>
      authMkSlotsRecvRedProb S P idx (evalPrfMkReal P mkSeedStar) msg prep? hst sentChal cache) =
      authMkSlotsRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (prep?.map (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar))
        (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) ∧
    (∀ x ∈ support (authMkSlotsRecvRedProb S P idx (evalPrfMkReal P mkSeedStar)
        msg prep? hst sentChal cache),
      InvMkSlotsTrue S P idx mkSeedStar ((x.1.2, sentChal), x.2)) := by
  cases hP : prep? with
  | none =>
    unfold authMkSlotsRecvRedProb authMkSlotsRecvWith restoreAuthFixedSlotsMkAtIdx
    dsimp only
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact ⟨authSlotStateWf_of_usedSend_sub hInv.wf rfl rfl (by dsimp only; omega) (fun _ h => h),
      hInv.saltCache_send, hInv.sentChal_imp, hInv.ideal_msgKeys, hInv.cache_msgKeys⟩
  | some prep =>
    obtain ⟨hMatchMem, hFinProps⟩ := hPrepProps prep hP
    unfold authMkSlotsRecvRedProb authMkSlotsRecvWith
    dsimp only [Option.map]
    have hMatch : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).matchedSess? =
        prep.matchedSess?.map (restoreIdealMkSlotsAtIdx hst.slots idx mkSeedStar) := rfl
    have hHon : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).isUncorruptedHonestSender =
        prep.isUncorruptedHonestSender := rfl
    have hEph : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).sameEph = prep.sameEph := rfl
    have hSec : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).secrets = prep.secrets := rfl
    have hDh : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).dhRatchet = prep.dhRatchet := rfl
    have hKE : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).kEntry = prep.kEntry := rfl
    have hRo : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).hstDec.base.roCache =
        prep.hstDec.base.roCache := rfl
    have hRootRo : (restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).hstDec.base.rootRoCache =
        prep.hstDec.base.rootRoCache := rfl
    have hRC : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).recvCount = hst.recvCount := rfl
    have hMC : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).mkSaltCache =
        filterOutMkSaltCacheSlotsAtIdx hst.slots idx hst.mkSaltCache := rfl
    have hSl : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).slots = hst.slots := rfl
    have hFinRes : ∀ res? : Option (DRKey × Bytes × Bytes × Bytes ×
        List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes))),
        ((prep.finish res?).1,
         restoreAuthFixedSlotsMkAtIdx idx mkSeedStar
           { toAuthHybridState := (prep.finish res?).2,
             recvCount := hst.recvCount + 1,
             mkSaltCache := hst.mkSaltCache,
             slots := hst.slots }) =
        (((restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).finish res?).1,
         { toAuthHybridState :=
             ((restorePreparedAuthRecvSlotsMk hst.slots idx mkSeedStar prep).finish res?).2,
           recvCount := hst.recvCount + 1,
           mkSaltCache := filterOutMkSaltCacheSlotsAtIdx hst.slots idx hst.mkSaltCache,
           slots := hst.slots }) := by
      intro res?
      simp [restorePreparedAuthRecvSlotsMk, restoreAuthFixedSlotsMkAtIdx]
    have hInvRes : ∀ res?,
        InvMkSlotsTrue S P idx mkSeedStar
          (({ toAuthHybridState := (prep.finish res?).2,
              recvCount := hst.recvCount + 1,
              mkSaltCache := hst.mkSaltCache,
              slots := hst.slots }, sentChal), cache) := by
      intro res?
      refine ⟨authSlotStateWf_of_usedSend_sub hInv.wf rfl (hFinProps res?).1
        (by dsimp only; omega) (fun sid h => by dsimp only; rw [(hFinProps res?).2]; exact h),
        fun e he => by dsimp only at he ⊢; rw [(hFinProps res?).2]; exact hInv.saltCache_send e he,
        hInv.sentChal_imp, ?_, hInv.cache_msgKeys⟩
      dsimp only; rw [(hFinProps res?).1]; exact hInv.ideal_msgKeys
    simp only [hMatch, hHon, hEph, hSec, hDh, hKE, hRo, hRootRo, hRC, hMC, hSl, Option.isSome_map]
    split
    · cases hMS : prep.matchedSess? with
      | some s =>
        have hsMem : s ∈ hst.toAuthHybridState.idealSessions := hMatchMem s hMS
        have hDr : (restoreIdealMkSlotsAtIdx hst.slots idx mkSeedStar s).drKey = s.drKey := by
          unfold restoreIdealMkSlotsAtIdx; split <;> rfl
        have hRk1 : (restoreIdealMkSlotsAtIdx hst.slots idx mkSeedStar s).rk1 = s.rk1 := by
          unfold restoreIdealMkSlotsAtIdx; split <;> rfl
        have hCk : (restoreIdealMkSlotsAtIdx hst.slots idx mkSeedStar s).ck1_1 = s.ck1_1 := by
          unfold restoreIdealMkSlotsAtIdx; split <;> rfl
        dsimp only [Option.map]
        rw [hDr, hRk1, hCk]
        split
        · cases hR : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            refine ⟨by simp [hFinRes none], fun x hx => ?_⟩
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvRes none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            obtain ⟨hEqM, hSuppM⟩ := matchedSameEphMkSlotsRedProb_evalPrfMkReal P hst.slots idx
              mkSeedStar s spqrSalt? hst.recvCount hWF (saltOK_of_spqrInitRecv hWF hR)
              hst.mkSaltCache cache (hInv.ideal_msgKeys s hsMem) hInv.cache_msgKeys
            refine ⟨?_, fun x hx => ?_⟩
            · simp only [map_bind, map_pure]
              rw [← hEqM, bind_map_left]
              congr 1
            · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨⟨⟨mk, mkSaltCache'⟩, cache'⟩, hMemM, rfl⟩
              obtain ⟨hSubM, hCacheM⟩ := hSuppM _ hMemM
              dsimp only [finishAuthRecvMkSlotsH3, finishAuthRecvMk]
              refine ⟨authSlotStateWf_of_usedSend_sub hInv.wf rfl (hFinProps _).1
                (by dsimp only; omega) (fun sid h => by dsimp only; rw [(hFinProps _).2]; exact h),
                ?_, hInv.sentChal_imp, ?_, hCacheM⟩
              · intro e he; dsimp only at he ⊢; rw [(hFinProps _).2]
                rcases hSubM e he with heOld | hSidS
                · exact hInv.saltCache_send e heOld
                · rw [hSidS]; exact (hInv.wf.ideal_send s hsMem).1
              · dsimp only; rw [(hFinProps _).1]; exact hInv.ideal_msgKeys
        · refine ⟨?_, fun x hx => ?_⟩
          · simp only [map_bind]; congr 1; funext rk1
            cases hR : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => dsimp only; simp [hFinRes none]
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkReal P idx mkSeedStar msg prep
                s.drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
                hInv hFinProps).1
          · simp only [MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨rk1, _, hx⟩; revert x hx
            cases hR : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
              subst hx; exact hInvRes none
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkReal P idx mkSeedStar msg prep
                s.drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
                hInv hFinProps).2
      | none =>
        dsimp only [Option.map]
        refine ⟨?_, fun x hx => ?_⟩
        · simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
          cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; simp [hFinRes none]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkReal P idx mkSeedStar msg prep
              drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
              hInv hFinProps).1
        · simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩; revert x hx
          cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvRes none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkReal P idx mkSeedStar msg prep
              drKey rk1 spqrSalt? hWF (saltOK_of_spqrInitRecv hWF hR) hst sentChal cache
              hInv hFinProps).2
    · refine ⟨?_, fun x hx => ?_⟩
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => dsimp only; simp [hFinRes none]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only; simp [hFinRes _]
      · simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
        revert x hx
        cases hR : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hInvRes none
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hInvRes _

theorem authMkSlotsSendRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hWF : WellFormedPrimitivesδ P)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkSlotsTrue S P idx mkSeedStar ((hst, sentChal), cache)) :
    ((fun (resp, ((hst', _), _)) => (resp, restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst')) <$>
      authMkSlotsSendRedProb S P idx (evalPrfMkReal P mkSeedStar) sid u bundle m0 m1
        hst sentChal cache) =
      authMkSlotsSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) sid u bundle m0 m1
        (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) ∧
    (∀ x ∈ support (authMkSlotsSendRedProb S P idx (evalPrfMkReal P mkSeedStar)
        sid u bundle m0 m1 hst sentChal cache),
      InvMkSlotsTrue S P idx mkSeedStar x.2) := by
  have hSl : (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst).slots = hst.slots := rfl
  have hEq :
      ((fun (resp, ((hst', _), _)) => (resp, restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst')) <$>
        authMkSlotsSendRedProb S P idx (evalPrfMkReal P mkSeedStar) sid u bundle m0 m1
          hst sentChal cache) =
      authMkSlotsSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) sid u bundle m0 m1
        (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) := by
    unfold authMkSlotsSendRedProb authMkSlotsSendWith finishAuthSendAfterMkSlots evalPrfMkReal
    rw [prepareAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx, bind_map_left, map_bind]
    refine bind_congr_of_support (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst) _ _
      (fun prep hPrep => ?_)
    have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hInv.wf prep hPrep
    cases prep with
    | done resp hst' => simp [PreparedAuthSend.mapState]
    | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
        pqRatchetMsg msgPlain =>
      dsimp only [PreparedAuthSend.mapState]
      rw [hSl]
      cases hIdx : ((hst.slots.allocSend sid).1 == idx)
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases hLt : decide ((hst.slots.allocSend sid).1 < idx)
        · simp only [Bool.false_eq_true, ↓reduceIte, map_bind]
          congr 1; funext mkSeed; congr 1; funext ck1_1
          simp only [map_pure]; congr 1
          exact (finishAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx_ne P idx mkSeedStar sid
            hSend hst hInv.wf hInv.saltCache_send hP.1 hIdx
            uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk
            drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlain _).symm
        · simp only [↓reduceIte, map_bind]
          congr 1; funext ck1_1; congr 1; funext deriveMessageKeys
          simp only [map_pure]; congr 1
          exact (finishAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx_ne P idx mkSeedStar sid
            hSend hst hInv.wf hInv.saltCache_send hP.1 hIdx
            uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk
            drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain _).symm
      · have hNone : hst.slots.lookupSend sid = none := hInv.wf.send_fresh sid hP.1
        have hSIdx : (hst.slots.allocSend sid).1 = hst.slots.nextSlot :=
          (allocSend_of_none hst.slots sid hSend hNone).1
        have hSC : sentChal = false := by
          cases hB : sentChal
          · rfl
          · have hLt := hInv.sentChal_imp hB
            dsimp only at hLt
            have hEqIdx : (hst.slots.allocSend sid).1 = idx := beq_iff_eq.mp hIdx
            omega
        have hLtF : decide ((hst.slots.allocSend sid).1 < idx) = false := decide_lt_of_beq_true hIdx
        simp only [hSC, hLtF, Bool.not_false, Bool.true_and, ↓reduceIte, Bool.false_eq_true,
          pure_bind, map_bind]
        congr 1; funext ck1_1
        simp only [map_pure, deriveMsgKeysEff_eq hWF mkSeedStar (hP.2 hWF)]; congr 1
        exact (finishAuthSendMkSlotsH3_restoreAuthFixedSlotsMkAtIdx_eq P idx mkSeedStar sid
          hSend hst hInv.wf hInv.saltCache_send hP.1 hIdx
          uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk
          drKey rk1 ck1_1 spqrSalt? pqRatchetMsg msgPlain _).symm
  refine ⟨hEq, fun x hx => ?_⟩
  unfold authMkSlotsSendRedProb evalPrfMkReal at hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hPrep, hx⟩
  have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hInv.wf prep hPrep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨hW', hSl', _, hMC', hId'⟩ := hP
    have hSub : ∀ sid0, hst.toAuthHybridState.base.usedSendSessions.contains sid0 = true →
        hst'.toAuthHybridState.base.usedSendSessions.contains sid0 = true := by
      unfold prepareAuthSendMkSlotsH3 at hPrep
      rw [support_map] at hPrep
      rcases hPrep with ⟨p0, hp0, heq⟩
      have hFP := support_prepareAuthSendMk_full_props P sid u bundle m0 m1 hst p0 hp0
      cases p0 with
      | idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ => cases heq
      | done _ s0 =>
        injection heq with _ hsEq; subst hsEq
        exact hFP.2.2.2
    refine ⟨hW', ?_, ?_, ?_, ?_⟩
    · intro e he; dsimp only at he ⊢; rw [hMC'] at he; exact hSub _ (hInv.saltCache_send e he)
    · intro hS; dsimp only at hS ⊢; rw [hSl']; exact hInv.sentChal_imp hS
    · intro s hs hI; dsimp only at hs hI; rw [hId'] at hs; rw [hSl'] at hI
      exact hInv.ideal_msgKeys s hs hI
    · intro e he hI; dsimp only at he hI; rw [hMC'] at he; rw [hSl'] at hI
      exact hInv.cache_msgKeys e he hI
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
      pqRatchetMsg msgPlain =>
    dsimp only at hx
    have hNone : hst.slots.lookupSend sid = none := hInv.wf.send_fresh sid hP.1
    have hPostNe : ∀ mkSeed ck1_1 deriveMessageKeys,
        ((hst.slots.allocSend sid).1 == idx) = false →
        InvMkSlotsTrue S P idx mkSeedStar
          (((finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
              ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
              spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
              deriveMessageKeys).2, sentChal), cache) := by
      intro mkSeed ck1_1 deriveMessageKeys hNeIdx
      obtain ⟨hW', hN'⟩ := authSlotStateWf_of_allocSend_finishSend P sid hSend uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys hInv.wf hP.1
      obtain ⟨hMC, _, hUsed, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
        deriveMessageKeys
      refine ⟨hW', ?_, ?_, ?_, ?_⟩
      · intro e he
        change e ∈ (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
          spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
          deriveMessageKeys).2.mkSaltCache at he
        rw [hMC] at he
        have hU := hInv.saltCache_send e he
        dsimp only [finishAuthSendMkSlotsH3]
        change (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
          spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
          deriveMessageKeys).2.toAuthHybridState.base.usedSendSessions.contains e.1.1 = true
        rw [hUsed, List.contains_cons, hU, Bool.or_true]
      · intro hS
        have h0 := hInv.sentChal_imp hS
        dsimp only at h0 hN' ⊢
        omega
      · intro s hs hI
        dsimp only [finishAuthSendMkSlotsH3] at hs hI
        rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
        · rw [hIdEq] at hs
          have hU := (hInv.wf.ideal_send s hs).1
          have hNe : s.sid ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
          rw [lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe] at hI
          exact hInv.ideal_msgKeys s hs hI
        · rw [hIdCons] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsSid, lookupSendOrZero_allocSend_self hst.slots sid hSend hNone, hNeIdx] at hI
            cases hI
          · have hU := (hInv.wf.ideal_send s hs').1
            have hNe : s.sid ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
            rw [lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe] at hI
            exact hInv.ideal_msgKeys s hs' hI
      · intro e he hI
        dsimp only [finishAuthSendMkSlotsH3] at he hI
        rw [hMC] at he
        have hU := hInv.saltCache_send e he
        have hNe : e.1.1 ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
        rw [lookupSendOrZero_allocSend_ne hst.slots sid e.1.1 hSend hNone hNe] at hI
        exact hInv.cache_msgKeys e he hI
    cases hIdx : ((hst.slots.allocSend sid).1 == idx)
    · rw [hIdx] at hx
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hx
      cases hLt : decide ((hst.slots.allocSend sid).1 < idx)
      · rw [hLt] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        exact hPostNe mkSeed ck1_1 _ hIdx
      · rw [hLt] at hx
        simp only [↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        exact hPostNe [] ck1_1 deriveMessageKeys hIdx
    · have hSIdx : (hst.slots.allocSend sid).1 = hst.slots.nextSlot :=
        (allocSend_of_none hst.slots sid hSend hNone).1
      have hSC : sentChal = false := by
        cases hB : sentChal
        · rfl
        · have hLt := hInv.sentChal_imp hB
          dsimp only at hLt
          have hEqIdx : (hst.slots.allocSend sid).1 = idx := beq_iff_eq.mp hIdx
          omega
      rw [hSC, hIdx] at hx
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, rfl⟩
      obtain ⟨hW', hN'⟩ := authSlotStateWf_of_allocSend_finishSend P sid hSend uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst (deriveMsgKeysEff P mkSeedStar spqrSalt?) hInv.wf hP.1
      obtain ⟨hMC, _, hUsed, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
        (deriveMsgKeysEff P mkSeedStar spqrSalt?)
      have hEqIdx : hst.slots.nextSlot = idx := by
        have := beq_iff_eq.mp hIdx; omega
      refine ⟨hW', ?_, ?_, ?_, ?_⟩
      · intro e he
        dsimp only [finishAuthSendMkSlotsH3] at he ⊢
        rw [hMC] at he
        have hU := hInv.saltCache_send e he
        rw [hUsed, List.contains_cons, hU, Bool.or_true]
      · intro _; dsimp only at hN' ⊢; omega
      · intro s hs hI
        dsimp only [finishAuthSendMkSlotsH3] at hs hI
        rcases hId with hIdEq | ⟨s0, _, _, hsSalt, hsMk, hIdCons⟩
        · rw [hIdEq] at hs
          have hU := (hInv.wf.ideal_send s hs).1
          have hNe : s.sid ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
          rw [lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe] at hI
          exact hInv.ideal_msgKeys s hs hI
        · rw [hIdCons] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsMk, hsSalt]
          · have hU := (hInv.wf.ideal_send s hs').1
            have hNe : s.sid ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
            rw [lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe] at hI
            exact hInv.ideal_msgKeys s hs' hI
      · intro e he hI
        dsimp only [finishAuthSendMkSlotsH3] at he hI
        rw [hMC] at he
        have hU := hInv.saltCache_send e he
        have hNe : e.1.1 ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
        rw [lookupSendOrZero_allocSend_ne hst.slots sid e.1.1 hSend hNone hNe] at hI
        exact hInv.cache_msgKeys e he hI

theorem authMkSlotsStepRedProb_evalPrfMkReal {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hWF : WellFormedPrimitivesδ P)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkSlotsTrue S P idx mkSeedStar st) :
    ((prfMkSlotsAuthImpl S P idx mkSeedStar q).run (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar st.1.1) =
      Prod.map id (fun ((hst', _), _) => restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst') <$>
        ((authMkSlotsRedProbImpl S P idx (evalPrfMkReal P mkSeedStar) q).run st)) ∧
    (∀ x ∈ support ((authMkSlotsRedProbImpl S P idx (evalPrfMkReal P mkSeedStar) q).run st),
      InvMkSlotsTrue S P idx mkSeedStar x.2) := by
  rcases st with ⟨⟨hst, sentChal⟩, cache⟩
  dsimp only [prfMkSlotsAuthImpl, authMkSlotsRedProbImpl, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only; split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSlotsSendRedProb_evalPrfMkReal P idx mkSeedStar
        (.sendOPK u i) trivial hWF u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only; split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSlotsSendRedProb_evalPrfMkReal P idx mkSeedStar
        (.sendNoOPK u i) trivial hWF u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | recvOPK k j o msg =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only
    change (authMkSlotsRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (prepareAuthHybridRecvOPK true P k j o msg
          (restoreAuthMkSlotsAtIdx hst.slots idx mkSeedStar hst.toAuthHybridState))
        (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) = _) ∧ _
    rw [prepareAuthHybridRecvOPK_restoreAuthMkSlotsAtIdx]
    obtain ⟨hEq, hSupp⟩ := authMkSlotsRecvRedProb_evalPrfMkReal P idx mkSeedStar msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hWF hst sentChal cache hInv
      (prepareAuthHybridRecvOPK_props P k j o msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]; simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | recvNoOPK k j l msg =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only
    change (authMkSlotsRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        (fun s => decide (s < idx)) msg
        (prepareAuthHybridRecvNoOPK true P k j l msg
          (restoreAuthMkSlotsAtIdx hst.slots idx mkSeedStar hst.toAuthHybridState))
        (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) = _) ∧ _
    rw [prepareAuthHybridRecvNoOPK_restoreAuthMkSlotsAtIdx]
    obtain ⟨hEq, hSupp⟩ := authMkSlotsRecvRedProb_evalPrfMkReal P idx mkSeedStar msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hWF hst sentChal cache hInv
      (prepareAuthHybridRecvNoOPK_props P k j l msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]; simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · rw [authCkOtherStep_restoreAuthFixedSlotsMkAtIdx]
      simp [Prod.map, map_eq_bind_pure_comp]; rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      have hSl := support_authCkOtherStep_slots P _ hst (resp, hst') hMem
      dsimp only at hOther hSl
      refine ⟨authSlotStateWf_of_usedSend_sub hInv.wf hSl hOther.1
        (by dsimp only; rw [hOther.2.2.2])
        (fun sid h => by rw [hOther.2.1]; exact h), ?_, ?_, ?_, ?_⟩
      · intro e he; dsimp only at he ⊢; rw [hOther.2.2.1] at he; rw [hOther.2.1]
        exact hInv.saltCache_send e he
      · intro hS; dsimp only at hS ⊢; rw [hSl]; exact hInv.sentChal_imp hS
      · intro s hs hI; dsimp only at hs hI; rw [hOther.1] at hs; rw [hSl] at hI
        exact hInv.ideal_msgKeys s hs hI
      · intro e he hI; dsimp only at he hI; rw [hOther.2.2.1] at he; rw [hSl] at hI
        exact hInv.cache_msgKeys e he hI

theorem evalDist_prfMsgKeysSlotsWorld_true_at_idx (S : Setup) (P : Primitives) (idx : Nat)
    (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[(do
        let mkSeedStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkSlotsRedProbImpl S P idx (evalPrfMkReal P mkSeedStar)
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkSlotsCutoffExp S P idx A] := by
  rw [← evalDist_preSample_authMkSlots_eq_cutoff S P idx A]
  refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun mkSeedStar _ => ?_)
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hInit : AuthHybridStateFixed.empty S secb =
      restoreAuthFixedSlotsMkAtIdx idx mkSeedStar (AuthHybridStateFixed.empty S secb) := rfl
  congr 1; symm; rw [hInit]
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst)
    (InvMkSlotsTrue S P idx mkSeedStar)
    (authMkSlotsRedProbImpl S P idx (evalPrfMkReal P mkSeedStar))
    (prfMkSlotsAuthImpl S P idx mkSeedStar)
    (fun q st hInv => authMkSlotsStepRedProb_evalPrfMkReal P idx mkSeedStar q hWF st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), [])
    (invMkSlotsTrue_empty S P idx mkSeedStar secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun _ _ => rfl)

structure InvMkSlotsFalse (S : Setup) (idx : Nat)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache) : Prop where
  wf : AuthSlotStateWf S st.1.1
  sentChal_imp : st.1.2 = true → idx < st.1.1.slots.nextSlot
  unfired_cache_nil : ¬ (idx < st.1.1.slots.nextSlot) → st.2 = []
  ideal_unique : ∀ s1 ∈ st.1.1.toAuthHybridState.idealSessions,
    ∀ s2 ∈ st.1.1.toAuthHybridState.idealSessions,
    (st.1.1.slots.lookupSendOrZero s1.sid == idx) = true →
    (st.1.1.slots.lookupSendOrZero s2.sid == idx) = true → s1 = s2
  cache_sub_mkSaltCache : ∀ s ∈ st.1.1.toAuthHybridState.idealSessions,
    (st.1.1.slots.lookupSendOrZero s.sid == idx) = true →
    ∀ salt? : Option Bytes, sameSaltKey salt? s.spqrSalt? = false →
    st.1.1.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid salt?) = none →
    st.2.find? (fun (s', _) => s' == effectiveHkdfSaltBytes salt?) = none

theorem invMkSlotsFalse_empty (S : Setup) (idx : Nat) (secb : Bool) :
    InvMkSlotsFalse S idx ((AuthHybridStateFixed.empty S secb, false), []) where
  wf := authSlotStateWf_empty S secb
  sentChal_imp h := by cases h
  unfired_cache_nil _ := rfl
  ideal_unique _ hs := by cases hs
  cache_sub_mkSaltCache _ hs := by cases hs

theorem matchedSameEphMkSlotsRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives)
    (slots : AuthSlotState) (idx : Nat)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (cache : PrfMkCache)
    (hCacheSub : (slots.lookupSendOrZero s.sid == idx) = true →
      ∀ salt? : Option Bytes, sameSaltKey salt? s.spqrSalt? = false →
      mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid salt?) = none →
      cache.find? (fun (s', _) => s' == effectiveHkdfSaltBytes salt?) = none) :
    (Prod.fst <$>
      matchedSameEphMkSlotsRedProb S P idx evalPrfMkIdeal
        s (slots.lookupSendOrZero s.sid) spqrSalt? recvCount mkSaltCache cache) =
      matchedSameEphMkSlotsWith P (fun slot => decide (slot < idx + 1))
        s (slots.lookupSendOrZero s.sid) spqrSalt? recvCount mkSaltCache ∧
    (∀ x ∈ support (matchedSameEphMkSlotsRedProb S P idx evalPrfMkIdeal
        s (slots.lookupSendOrZero s.sid) spqrSalt? recvCount mkSaltCache cache),
      ((slots.lookupSendOrZero s.sid == idx) = false → x.2 = cache ∧
        ∀ s1 : IdealAuthSession S, (slots.lookupSendOrZero s1.sid == idx) = true →
          ∀ salt? : Option Bytes,
          x.1.2.find? (fun (k, _) => mkSaltKeyMatch k s1.sid salt?) =
            mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s1.sid salt?)) ∧
      ((slots.lookupSendOrZero s.sid == idx) = true →
        ∀ salt? : Option Bytes, sameSaltKey salt? s.spqrSalt? = false →
        x.1.2.find? (fun (k, _) => mkSaltKeyMatch k s.sid salt?) = none →
        x.2.find? (fun (s', _) => s' == effectiveHkdfSaltBytes salt?) = none)) := by
  unfold matchedSameEphMkSlotsRedProb matchedSameEphMkSlotsWith evalPrfMkIdeal
  dsimp only
  cases hIdx : (slots.lookupSendOrZero s.sid == idx)
  · simp only [decide_lt_succ_of_beq_false hIdx, Bool.false_eq_true, ↓reduceIte]
    cases hLt : decide (slots.lookupSendOrZero s.sid < idx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨fun _ => ⟨rfl, fun _ _ _ => rfl⟩, False.elim⟩
    · simp only [↓reduceIte]
      cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | some entry =>
          rcases entry with ⟨k, rc, mk⟩
          dsimp only
          refine ⟨by simp, fun x hx => ?_⟩
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact ⟨fun _ => ⟨rfl, fun _ _ _ => rfl⟩, False.elim⟩
        | none =>
          dsimp only
          refine ⟨by simp, fun x hx => ?_⟩
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨mk, _, rfl⟩
          refine ⟨fun _ => ⟨rfl, fun s1 hs1 salt? => ?_⟩, False.elim⟩
          have hPairNe : mkSaltKeyMatch (s.sid, spqrSalt?) s1.sid salt? = false := by
            apply mkSaltKeyMatch_of_sid_ne
            intro hSidEq; dsimp only at hSidEq
            rw [← hSidEq] at hs1
            exact Bool.noConfusion (hIdx.symm.trans hs1)
          rw [List.find?_cons]; dsimp only; rw [hPairNe]
      · simp only [↓reduceIte]
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨fun _ => ⟨rfl, fun _ _ _ => rfl⟩, False.elim⟩
  · simp only [decide_lt_succ_of_beq_true hIdx, ↓reduceIte]
    cases hSameSalt : (sameSaltKey spqrSalt? s.spqrSalt?)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hFind : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some entry =>
        rcases entry with ⟨k, rc, mk⟩
        dsimp only
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨fun h => Bool.noConfusion h, fun _ => hCacheSub hIdx⟩
      | none =>
        have hCacheNone : cache.find? (fun (s', _) => s' == effectiveHkdfSaltBytes spqrSalt?) = none :=
          hCacheSub hIdx spqrSalt? hSameSalt hFind
        rw [hCacheNone]; dsimp only
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hx
        rcases hx with ⟨mk, _, rfl⟩
        refine ⟨fun h => Bool.noConfusion h, fun _ salt? hSaltNe hFindCons => ?_⟩
        have hHead : mkSaltKeyMatch (s.sid, spqrSalt?) s.sid salt? =
            (effectiveHkdfSaltBytes spqrSalt? == effectiveHkdfSaltBytes salt?) := by
          simp [mkSaltKeyMatch, sameSaltKey]
        rw [List.find?_cons] at hFindCons ⊢
        dsimp only at hFindCons ⊢
        rw [hHead] at hFindCons
        cases hb : (effectiveHkdfSaltBytes spqrSalt? == effectiveHkdfSaltBytes salt?)
        · rw [hb] at hFindCons; exact hCacheSub hIdx salt? hSaltNe hFindCons
        · rw [hb] at hFindCons; cases hFindCons
    · simp only [↓reduceIte]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨fun h => Bool.noConfusion h, fun _ => hCacheSub hIdx⟩

theorem finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives)
    (idx : Nat) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkSlotsFalse S idx ((hst, sentChal), cache))
    (hPrep : ∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
                     (prep.finish res?).2.base.usedSendSessions =
                       hst.toAuthHybridState.base.usedSendSessions) :
    let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
    (Prod.fst <$>
      finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrfMkIdeal msg prep
        drKey rk1 spqrSalt? rSlot (hst.recvCount + 1)
        hst.mkSaltCache slots' sentChal cache) =
      finishAuthRecvUnmatchedAfterMkSlots P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) msg prep
        drKey rk1 spqrSalt? rSlot (hst.recvCount + 1)
        hst.mkSaltCache slots' ∧
    (∀ x ∈ support (finishAuthRecvUnmatchedSlotsRedProb S P idx evalPrfMkIdeal
        msg prep drKey rk1 spqrSalt? rSlot (hst.recvCount + 1)
        hst.mkSaltCache slots' sentChal cache),
      InvMkSlotsFalse S idx ((x.1.2, sentChal), x.2)) := by
  have hNone : hst.slots.recvTbl hst.recvCount = none :=
    hInv.wf.recv_fresh hst.recvCount (Nat.le_refl _)
  have hRSlot : (hst.slots.allocRecv hst.recvCount).1 = hst.slots.nextSlot :=
    (allocRecv_of_none (S := S) hst.slots hst.recvCount hNone).1
  have hL : AuthSlotState.lookupSendOrZero (S := S) (hst.slots.allocRecv hst.recvCount).2 =
      AuthSlotState.lookupSendOrZero (S := S) hst.slots :=
    lookupSendOrZero_allocRecv_of_none hst.slots hst.recvCount hNone
  unfold finishAuthRecvUnmatchedSlotsRedProb finishAuthRecvUnmatchedAfterMkSlots evalPrfMkIdeal
  dsimp only
  cases hIdx : ((hst.slots.allocRecv hst.recvCount).1 == idx)
  · simp only [decide_lt_succ_of_beq_false hIdx, Bool.false_eq_true, ↓reduceIte]
    have hPostNe : ∀ ck1_1 deriveMessageKeys,
        InvMkSlotsFalse S idx
          (((finishAuthRecvMkSlotsH3 P msg prep drKey rk1 ck1_1 (hst.recvCount + 1)
              hst.mkSaltCache (hst.slots.allocRecv hst.recvCount).2 deriveMessageKeys).2,
            sentChal), cache) := by
      intro ck1_1 deriveMessageKeys
      dsimp only [finishAuthRecvMkSlotsH3, finishAuthRecvMk]
      obtain ⟨hW', hN'⟩ := @authSlotStateWf_of_allocRecv S hst
        { toAuthHybridState := (prep.finish _).2, recvCount := hst.recvCount + 1,
          mkSaltCache := hst.mkSaltCache, slots := (hst.slots.allocRecv hst.recvCount).2 }
        hInv.wf rfl (hPrep _).1 (hPrep _).2 rfl
      dsimp only at hN'
      have hNeNext : hst.slots.nextSlot ≠ idx := by
        intro hEq; rw [hRSlot, hEq, beq_self_eq_true] at hIdx; cases hIdx
      refine ⟨hW', ?_, ?_, ?_, ?_⟩
      · intro hS
        have h0 := hInv.sentChal_imp hS
        dsimp only at h0 ⊢
        omega
      · intro hNF
        have hUF := hInv.unfired_cache_nil
        dsimp only at hNF hUF
        exact hUF (by omega)
      · intro s1 hs1 s2 hs2 h1 h2
        dsimp only at hs1 hs2 h1 h2
        rw [(hPrep _).1] at hs1 hs2; rw [hL] at h1 h2
        exact hInv.ideal_unique s1 hs1 s2 hs2 h1 h2
      · intro s hs hI
        dsimp only at hs hI ⊢
        rw [(hPrep _).1] at hs; rw [hL] at hI
        exact hInv.cache_sub_mkSaltCache s hs hI
    cases hLt : decide ((hst.slots.allocRecv hst.recvCount).1 < idx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp [map_bind], fun x hx => ?_⟩
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
      exact hPostNe ck1_1 _
    · simp only [↓reduceIte]
      refine ⟨by simp [map_bind], fun x hx => ?_⟩
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      exact hPostNe ck1_1 deriveMessageKeys
  · have hEqIdx : hst.slots.nextSlot = idx := by
      have := beq_iff_eq.mp hIdx; omega
    have hSC : sentChal = false := by
      cases hB : sentChal
      · rfl
      · have h0 := hInv.sentChal_imp hB; dsimp only at h0; omega
    have hCacheNil : cache = [] := by
      have hUF := hInv.unfired_cache_nil; dsimp only at hUF; exact hUF (by omega)
    simp only [decide_lt_succ_of_beq_true hIdx, hCacheNil, ↓reduceIte, hSC, Bool.not_false,
      List.find?_nil, bind_assoc, pure_bind]
    refine ⟨by simp [map_bind], fun x hx => ?_⟩
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
    dsimp only [finishAuthRecvMkSlotsH3, finishAuthRecvMk]
    obtain ⟨hW', hN'⟩ := @authSlotStateWf_of_allocRecv S hst
      { toAuthHybridState := (prep.finish _).2, recvCount := hst.recvCount + 1,
        mkSaltCache := hst.mkSaltCache, slots := (hst.slots.allocRecv hst.recvCount).2 }
      hInv.wf rfl (hPrep _).1 (hPrep _).2 rfl
    dsimp only at hN'
    refine ⟨hW', (by intro hS; cases hS), (by intro hNF; dsimp only at hNF; omega), ?_, ?_⟩
    · intro s1 hs1 s2 hs2 h1 h2
      dsimp only at hs1 hs2 h1 h2
      rw [(hPrep _).1] at hs1 hs2; rw [hL] at h1 h2
      exact hInv.ideal_unique s1 hs1 s2 hs2 h1 h2
    · intro s hs hI
      dsimp only at hs hI
      rw [(hPrep _).1] at hs; rw [hL] at hI
      obtain ⟨_, k, hkLt, hkEq⟩ := hInv.wf.ideal_send s hs
      dsimp only at hkLt
      have hKIdx : k = idx := by
        simpa [AuthSlotState.lookupSendOrZero, hkEq] using beq_iff_eq.mp hI
      omega

theorem authMkSlotsRecvRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkSlotsFalse S idx ((hst, sentChal), cache))
    (hPrepProps : ∀ prep, prep? = some prep →
      (∀ s, prep.matchedSess? = some s → s ∈ hst.toAuthHybridState.idealSessions) ∧
      (∀ res?, (prep.finish res?).2.idealSessions = hst.toAuthHybridState.idealSessions ∧
               (prep.finish res?).2.base.usedSendSessions =
                 hst.toAuthHybridState.base.usedSendSessions)) :
    (Prod.fst <$>
      authMkSlotsRecvRedProb S P idx evalPrfMkIdeal msg prep? hst sentChal cache) =
      authMkSlotsRecvWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) msg prep? hst ∧
    (∀ x ∈ support (authMkSlotsRecvRedProb S P idx evalPrfMkIdeal msg prep? hst sentChal cache),
      InvMkSlotsFalse S idx ((x.1.2, sentChal), x.2)) := by
  cases hP : prep? with
  | none =>
    unfold authMkSlotsRecvRedProb authMkSlotsRecvWith; dsimp only
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact ⟨authSlotStateWf_of_usedSend_sub hInv.wf rfl rfl (by dsimp only; omega) (fun _ h => h),
      hInv.sentChal_imp, hInv.unfired_cache_nil, hInv.ideal_unique, hInv.cache_sub_mkSaltCache⟩
  | some prep =>
    obtain ⟨hMatchMem, hFinProps⟩ := hPrepProps prep hP
    unfold authMkSlotsRecvRedProb authMkSlotsRecvWith; dsimp only
    have hInvRes : ∀ res?,
        InvMkSlotsFalse S idx
          (({ toAuthHybridState := (prep.finish res?).2,
              recvCount := hst.recvCount + 1,
              mkSaltCache := hst.mkSaltCache,
              slots := hst.slots }, sentChal), cache) := by
      intro res?
      refine ⟨authSlotStateWf_of_usedSend_sub hInv.wf rfl (hFinProps res?).1
        (by dsimp only; omega) (fun sid h => by dsimp only; rw [(hFinProps res?).2]; exact h),
        hInv.sentChal_imp, hInv.unfired_cache_nil, ?_, ?_⟩
      · dsimp only; rw [(hFinProps res?).1]; exact hInv.ideal_unique
      · dsimp only; rw [(hFinProps res?).1]; exact hInv.cache_sub_mkSaltCache
    split
    · cases hMS : prep.matchedSess? with
      | some s =>
        have hsMem : s ∈ hst.toAuthHybridState.idealSessions := hMatchMem s hMS
        dsimp only; split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            refine ⟨by simp, fun x hx => ?_⟩
            simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvRes none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            obtain ⟨hEqM, hSuppM⟩ := matchedSameEphMkSlotsRedProb_evalPrfMkIdeal P hst.slots idx
              s spqrSalt? hst.recvCount hst.mkSaltCache cache (hInv.cache_sub_mkSaltCache s hsMem)
            refine ⟨?_, fun x hx => ?_⟩
            · simp only [map_bind, map_pure]
              rw [← hEqM, bind_map_left]
            · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨⟨⟨mk, mkSaltCache'⟩, cache'⟩, hMemM, rfl⟩
              obtain ⟨hIfNe, hIfEq⟩ := hSuppM _ hMemM
              dsimp only [finishAuthRecvMkSlotsH3, finishAuthRecvMk] at hIfNe hIfEq ⊢
              refine ⟨authSlotStateWf_of_usedSend_sub hInv.wf rfl (hFinProps _).1
                (by dsimp only; omega) (fun sid h => by dsimp only; rw [(hFinProps _).2]; exact h),
                hInv.sentChal_imp, ?_, ?_, ?_⟩
              · intro hNF
                dsimp only at hNF
                have hIdxF : (hst.slots.lookupSendOrZero s.sid == idx) = false := by
                  cases hB : (hst.slots.lookupSendOrZero s.sid == idx)
                  · rfl
                  · obtain ⟨_, k, hkLt, hkEq⟩ := hInv.wf.ideal_send s hsMem
                    dsimp only at hkLt
                    have hKIdx : k = idx := by
                      simpa [AuthSlotState.lookupSendOrZero, hkEq] using beq_iff_eq.mp hB
                    omega
                rw [(hIfNe hIdxF).1]
                exact hInv.unfired_cache_nil hNF
              · dsimp only; rw [(hFinProps _).1]; exact hInv.ideal_unique
              · dsimp only; rw [(hFinProps _).1]
                intro s1 hs1 hs1Idx salt? hSaltNe hFindNone
                cases hIdx : (hst.slots.lookupSendOrZero s.sid == idx)
                · obtain ⟨hCEq, hFEq⟩ := hIfNe hIdx
                  rw [hCEq]
                  rw [hFEq s1 hs1Idx salt?] at hFindNone
                  exact hInv.cache_sub_mkSaltCache s1 hs1 hs1Idx salt? hSaltNe hFindNone
                · have hs1Eq : s1 = s := hInv.ideal_unique s1 hs1 s hsMem hs1Idx hIdx
                  subst hs1Eq
                  exact hIfEq hIdx salt? hSaltNe hFindNone
        · refine ⟨?_, fun x hx => ?_⟩
          · simp only [map_bind]; congr 1; funext rk1
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => dsimp only; simp
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkIdeal P idx msg prep
                s.drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).1
          · simp only [MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨rk1, _, hx⟩; revert x hx
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
              subst hx; exact hInvRes none
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkIdeal P idx msg prep
                s.drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).2
      | none =>
        dsimp only [Option.map]
        refine ⟨?_, fun x hx => ?_⟩
        · simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; simp
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkIdeal P idx msg prep
              drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).1
        · simp only [MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩; revert x hx
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
            subst hx; exact hInvRes none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (finishAuthRecvUnmatchedSlotsRedProb_evalPrfMkIdeal P idx msg prep
              drKey rk1 spqrSalt? hst sentChal cache hInv hFinProps).2
    · refine ⟨?_, fun x hx => ?_⟩
      · simp only [map_bind]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => dsimp only; simp
        | some pqr => rcases pqr with ⟨_, _⟩; dsimp only; simp
      · simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
        revert x hx
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hInvRes none
        | some pqr =>
          rcases pqr with ⟨_, _⟩
          intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hInvRes _

theorem authMkSlotsSendRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (cache : PrfMkCache)
    (hInv : InvMkSlotsFalse S idx ((hst, sentChal), cache)) :
    ((fun (resp, ((hst', _), _)) => (resp, hst')) <$>
      authMkSlotsSendRedProb S P idx evalPrfMkIdeal sid u bundle m0 m1 hst sentChal cache) =
      authMkSlotsSendWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) sid u bundle m0 m1 hst ∧
    (∀ x ∈ support (authMkSlotsSendRedProb S P idx evalPrfMkIdeal
        sid u bundle m0 m1 hst sentChal cache),
      InvMkSlotsFalse S idx x.2) := by
  have hEq :
      ((fun (resp, ((hst', _), _)) => (resp, hst')) <$>
        authMkSlotsSendRedProb S P idx evalPrfMkIdeal sid u bundle m0 m1 hst sentChal cache) =
      authMkSlotsSendWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) sid u bundle m0 m1 hst := by
    unfold authMkSlotsSendRedProb authMkSlotsSendWith finishAuthSendAfterMkSlots evalPrfMkIdeal
    rw [map_bind]
    refine bind_congr_of_support (prepareAuthSendMkSlotsH3 S P sid u bundle m0 m1 hst) _ _
      (fun prep hPrep => ?_)
    have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hInv.wf prep hPrep
    cases prep with
    | done resp hst' => simp
    | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
        pqRatchetMsg msgPlain =>
      dsimp only
      have hNone : hst.slots.lookupSend sid = none := hInv.wf.send_fresh sid hP.1
      have hSIdx : (hst.slots.allocSend sid).1 = hst.slots.nextSlot :=
        (allocSend_of_none hst.slots sid hSend hNone).1
      cases hIdx : ((hst.slots.allocSend sid).1 == idx)
      · simp only [decide_lt_succ_of_beq_false hIdx, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases hLt : decide ((hst.slots.allocSend sid).1 < idx) <;> simp [map_bind]
      · have hEqIdx : hst.slots.nextSlot = idx := by
          have := beq_iff_eq.mp hIdx; omega
        have hSC : sentChal = false := by
          cases hB : sentChal
          · rfl
          · have h0 := hInv.sentChal_imp hB; dsimp only at h0; omega
        have hCacheNil : cache = [] := by
          have hUF := hInv.unfired_cache_nil; dsimp only at hUF; exact hUF (by omega)
        simp only [decide_lt_succ_of_beq_true hIdx, hCacheNil, hSC, Bool.not_false, Bool.and_self,
          ↓reduceIte, List.find?_nil, bind_assoc, pure_bind]
        simp [map_bind]
  refine ⟨hEq, fun x hx => ?_⟩
  unfold authMkSlotsSendRedProb evalPrfMkIdeal at hx
  simp only [MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨prep, hPrep, hx⟩
  have hP := prepareAuthSendMkSlotsH3_wf_and_fresh P sid u bundle m0 m1 hst hInv.wf prep hPrep
  cases prep with
  | done resp hst' =>
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨hW', hSl', _, hMC', hId'⟩ := hP
    refine ⟨hW', ?_, ?_, ?_, ?_⟩
    · intro hS; dsimp only at hS ⊢; rw [hSl']; exact hInv.sentChal_imp hS
    · intro hNF; dsimp only at hNF ⊢; rw [hSl'] at hNF; exact hInv.unfired_cache_nil hNF
    · intro s1 hs1 s2 hs2 h1 h2
      dsimp only at hs1 hs2 h1 h2; rw [hId'] at hs1 hs2; rw [hSl'] at h1 h2
      exact hInv.ideal_unique s1 hs1 s2 hs2 h1 h2
    · intro s hs hI
      dsimp only at hs hI ⊢; rw [hId'] at hs; rw [hSl'] at hI; rw [hMC']
      exact hInv.cache_sub_mkSaltCache s hs hI
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
      pqRatchetMsg msgPlain =>
    dsimp only at hx
    have hNone : hst.slots.lookupSend sid = none := hInv.wf.send_fresh sid hP.1
    have hSIdx : (hst.slots.allocSend sid).1 = hst.slots.nextSlot :=
      (allocSend_of_none hst.slots sid hSend hNone).1
    have hOldLookup : ∀ s ∈ hst.toAuthHybridState.idealSessions,
        (hst.slots.allocSend sid).2.lookupSendOrZero s.sid = hst.slots.lookupSendOrZero s.sid := by
      intro s hs
      have hU := (hInv.wf.ideal_send s hs).1
      have hNe : s.sid ≠ sid := by intro h; rw [h, hP.1] at hU; cases hU
      exact lookupSendOrZero_allocSend_ne hst.slots sid s.sid hSend hNone hNe
    have hPostNe : ∀ mkSeed ck1_1 deriveMessageKeys,
        ((hst.slots.allocSend sid).1 == idx) = false →
        InvMkSlotsFalse S idx
          (((finishAuthSendMkSlotsH3 P sid uEntry peerPrincipal? bundle m0 m1
              ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
              spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
              deriveMessageKeys).2, sentChal), cache) := by
      intro mkSeed ck1_1 deriveMessageKeys hNeIdx
      obtain ⟨hW', hN'⟩ := authSlotStateWf_of_allocSend_finishSend P sid hSend uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys hInv.wf hP.1
      obtain ⟨hMC, _, _, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
        deriveMessageKeys
      have hNeNext : hst.slots.nextSlot ≠ idx := by
        intro hEq; rw [hSIdx, hEq, beq_self_eq_true] at hNeIdx; cases hNeIdx
      refine ⟨hW', ?_, ?_, ?_, ?_⟩
      · intro hS
        have h0 := hInv.sentChal_imp hS
        dsimp only at h0 hN' ⊢
        omega
      · intro hNF
        have hUF := hInv.unfired_cache_nil
        dsimp only at hNF hUF hN'
        exact hUF (by omega)
      · intro s1 hs1 s2 hs2 h1 h2
        dsimp only [finishAuthSendMkSlotsH3] at hs1 hs2 h1 h2
        rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
        · rw [hIdEq] at hs1 hs2
          rw [hOldLookup s1 hs1] at h1; rw [hOldLookup s2 hs2] at h2
          exact hInv.ideal_unique s1 hs1 s2 hs2 h1 h2
        · rw [hIdCons] at hs1 hs2
          rcases List.mem_cons.mp hs1 with rfl | hs1'
          · rw [hsSid, lookupSendOrZero_allocSend_self hst.slots sid hSend hNone, hNeIdx] at h1
            cases h1
          · rcases List.mem_cons.mp hs2 with rfl | hs2'
            · rw [hsSid, lookupSendOrZero_allocSend_self hst.slots sid hSend hNone, hNeIdx] at h2
              cases h2
            · rw [hOldLookup s1 hs1'] at h1; rw [hOldLookup s2 hs2'] at h2
              exact hInv.ideal_unique s1 hs1' s2 hs2' h1 h2
      · intro s hs hI
        dsimp only [finishAuthSendMkSlotsH3] at hs hI ⊢
        rw [hMC]
        rcases hId with hIdEq | ⟨s0, hsSid, _, _, _, hIdCons⟩
        · rw [hIdEq] at hs; rw [hOldLookup s hs] at hI
          exact hInv.cache_sub_mkSaltCache s hs hI
        · rw [hIdCons] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsSid, lookupSendOrZero_allocSend_self hst.slots sid hSend hNone, hNeIdx] at hI
            cases hI
          · rw [hOldLookup s hs'] at hI
            exact hInv.cache_sub_mkSaltCache s hs' hI
    cases hIdx : ((hst.slots.allocSend sid).1 == idx)
    · rw [hIdx] at hx
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hx
      cases hLt : decide ((hst.slots.allocSend sid).1 < idx)
      · rw [hLt] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨mkSeed, _, ck1_1, _, rfl⟩
        exact hPostNe mkSeed ck1_1 _ hIdx
      · rw [hLt] at hx
        simp only [↓reduceIte, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
        exact hPostNe [] ck1_1 deriveMessageKeys hIdx
    · have hEqIdx : hst.slots.nextSlot = idx := by
        have := beq_iff_eq.mp hIdx; omega
      have hSC : sentChal = false := by
        cases hB : sentChal
        · rfl
        · have h0 := hInv.sentChal_imp hB; dsimp only at h0; omega
      have hCacheNil : cache = [] := by
        have hUF := hInv.unfired_cache_nil; dsimp only at hUF; exact hUF (by omega)
      rw [hSC, hIdx, hCacheNil] at hx
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte, List.find?_nil, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨ck1_1, _, deriveMessageKeys, _, rfl⟩
      obtain ⟨hW', hN'⟩ := authSlotStateWf_of_allocSend_finishSend P sid hSend uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys hInv.wf hP.1
      obtain ⟨hMC, _, _, hId⟩ := finishAuthSendMk_full_props P sid uEntry peerPrincipal?
        bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain { hst with slots := (hst.slots.allocSend sid).2 }
        deriveMessageKeys
      have hOldNotIdx : ∀ s ∈ hst.toAuthHybridState.idealSessions,
          ((hst.slots.allocSend sid).2.lookupSendOrZero s.sid == idx) = false := by
        intro s hs
        rw [hOldLookup s hs]
        obtain ⟨_, k, hkLt, hkEq⟩ := hInv.wf.ideal_send s hs
        dsimp only at hkLt
        have hEqK : hst.slots.lookupSendOrZero s.sid = k := by
          simp [AuthSlotState.lookupSendOrZero, hkEq]
        rw [hEqK]
        exact beq_false_of_ne (by omega)
      refine ⟨hW',
        (by intro _; dsimp only at hN' ⊢; omega),
        (by intro hNF; dsimp only at hN' hNF; omega), ?_, ?_⟩
      · intro s1 hs1 s2 hs2 h1 h2
        dsimp only [finishAuthSendMkSlotsH3] at hs1 hs2 h1 h2
        rcases hId with hIdEq | ⟨s0, _, _, _, _, hIdCons⟩
        · rw [hIdEq] at hs1
          rw [hOldNotIdx s1 hs1] at h1; cases h1
        · rw [hIdCons] at hs1 hs2
          rcases List.mem_cons.mp hs1 with rfl | hs1'
          · rcases List.mem_cons.mp hs2 with rfl | hs2'
            · rfl
            · rw [hOldNotIdx s2 hs2'] at h2; cases h2
          · rw [hOldNotIdx s1 hs1'] at h1; cases h1
      · intro s hs hI salt? hSaltNe _
        dsimp only [finishAuthSendMkSlotsH3] at hs hI ⊢
        rcases hId with hIdEq | ⟨s0, _, _, hsSalt, _, hIdCons⟩
        · rw [hIdEq] at hs; rw [hOldNotIdx s hs] at hI; cases hI
        · rw [hIdCons] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hsSalt] at hSaltNe
            have hNe : ¬ effectiveHkdfSaltBytes spqrSalt? = effectiveHkdfSaltBytes salt? := by
              intro h; simp [sameSaltKey, h] at hSaltNe
            simp [hNe]
          · rw [hOldNotIdx s hs'] at hI; cases hI

theorem authMkSlotsStepRedProb_evalPrfMkIdeal {S : Setup} (P : Primitives)
    (idx : Nat) (q : AuthQuery S)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkSlotsFalse S idx st) :
    ((authMkSlotsCutoffImpl S P (idx + 1) q).run st.1.1 =
      Prod.map id (fun ((hst', _), _) => hst') <$>
        ((authMkSlotsRedProbImpl S P idx evalPrfMkIdeal q).run st)) ∧
    (∀ x ∈ support ((authMkSlotsRedProbImpl S P idx evalPrfMkIdeal q).run st),
      InvMkSlotsFalse S idx x.2) := by
  rcases st with ⟨⟨hst, sentChal⟩, cache⟩
  dsimp only [authMkSlotsCutoffImpl, authMkSlotsRedProbImpl, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only; split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSlotsSendRedProb_evalPrfMkIdeal P idx (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only; split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSlotsSendRedProb_evalPrfMkIdeal P idx (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | recvOPK k j o msg =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only
    obtain ⟨hEq, hSupp⟩ := authMkSlotsRecvRedProb_evalPrfMkIdeal P idx msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst sentChal cache hInv
      (prepareAuthHybridRecvOPK_props P k j o msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]; simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | recvNoOPK k j l msg =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only
    obtain ⟨hEq, hSupp⟩ := authMkSlotsRecvRedProb_evalPrfMkIdeal P idx msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst sentChal cache hInv
      (prepareAuthHybridRecvNoOPK_props P k j l msg hst.toAuthHybridState)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [← hEq]; simp [Prod.map]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨⟨resp, hst'⟩, cache'⟩, hMem, rfl⟩
      exact hSupp _ hMem
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkSlotsStepWith authMkSlotsStepRedProb; dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · simp [Prod.map, map_eq_bind_pure_comp]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      have hSl := support_authCkOtherStep_slots P _ hst (resp, hst') hMem
      dsimp only at hOther hSl
      refine ⟨authSlotStateWf_of_usedSend_sub hInv.wf hSl hOther.1
        (by dsimp only; rw [hOther.2.2.2])
        (fun sid h => by rw [hOther.2.1]; exact h), ?_, ?_, ?_, ?_⟩
      · intro hS; dsimp only at hS ⊢; rw [hSl]; exact hInv.sentChal_imp hS
      · intro hNF; dsimp only at hNF ⊢; rw [hSl] at hNF; exact hInv.unfired_cache_nil hNF
      · intro s1 hs1 s2 hs2 h1 h2
        dsimp only at hs1 hs2 h1 h2; rw [hOther.1] at hs1 hs2; rw [hSl] at h1 h2
        exact hInv.ideal_unique s1 hs1 s2 hs2 h1 h2
      · intro s hs hI
        dsimp only at hs hI ⊢; rw [hOther.1] at hs; rw [hSl] at hI; rw [hOther.2.2.1]
        exact hInv.cache_sub_mkSaltCache s hs hI

theorem evalDist_prfMsgKeysSlotsWorld_false_at_idx (S : Setup) (P : Primitives) (idx : Nat)
    (A : AuthAdversary S) :
    𝒟[(do
        let _ ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkSlotsRedProbImpl S P idx evalPrfMkIdeal
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkSlotsCutoffExp S P (idx + 1) A] := by
  rw [evalDist_sampleBytes32_bind_const]
  unfold authMkSlotsCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1; symm
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => hst)
    (InvMkSlotsFalse S idx)
    (authMkSlotsRedProbImpl S P idx evalPrfMkIdeal)
    (authMkSlotsCutoffImpl S P (idx + 1))
    (fun q st hInv => authMkSlotsStepRedProb_evalPrfMkIdeal P idx q st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), [])
    (invMkSlotsFalse_empty S idx secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun _ _ => rfl)

theorem hop_G3_7_G3_8 (S : Setup) : AuthHopG3_7G3_8Stmt S (prfMsgKeysReductionAuthFixed S) := by
  intro P hP b A
  let M := min b.q_total S.N_sess_tot
  change |(𝒟[authFixedExpAtStage .g3_7 S P A.1].boolBias).toReal -
          (𝒟[authFixedExpAtStage .g3_8 S P A.1].boolBias).toReal| ≤
    2 * (S.N_sess_tot : ℝ) * (𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed S b A)].boolBias).toReal
  rw [← evalDist_authMkSlotsCutoffExp_zero_eq_g3_7 S P b A,
      ← evalDist_authMkSlotsCutoffExp_end_eq_g3_8 S P b A]
  let worldAt (ch : Bool) (idx : Nat) : ProbComp Bool := do
    let mkSeedStar ← sampleBytes32
    let impl := prfMsgKeysOracleImpl ch P mkSeedStar
    let fullImpl := (primBaseImpl P).liftTarget (StateT PrfMkCache ProbComp) + impl
    let res ← (simulateQ fullImpl (authMkReductionRun S idx A.1)).run []
    return res.1
  have hPrfEq :
      𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed S b A)] =
        𝒟[do
          let ch ← $ᵗ Bool
          let z ← if ch then (sampleIndexRange M >>= worldAt true)
                  else (sampleIndexRange M >>= worldAt false)
          return (ch == z)] := by
    unfold prfMsgKeysExp prfMsgKeysReductionAuthFixed
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun ch _ => ?_)
    simp only [simulateQ_prfMkFullImpl_embedUnifMk_bind, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap sampleBytes32 (sampleIndexRange M)]
    cases ch <;>
    · simp only [worldAt, ↓reduceIte, Bool.false_eq_true, bind_assoc, pure_bind]
      congr 1; congr 1; funext idx; congr 1; funext mkSeedStar; congr 1; funext res
      simp only [Bool.beq_comm]
  have hWorldTrue : ∀ idx, 𝒟[worldAt true idx] = 𝒟[authMkSlotsCutoffExp S P idx A.1] := by
    intro idx
    unfold worldAt
    rw [← evalDist_prfMsgKeysSlotsWorld_true_at_idx S P idx hP.toWellFormedPrimitivesδ A.1]
    refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun mkSeedStar _ => ?_)
    have hRed := simulateQ_authMkReductionRun_eq_redProb S P idx
      (prfMsgKeysOracleImpl true P mkSeedStar) ([] : PrfMkCache) A.1
    dsimp only at hRed
    have hEval : (fun s c =>
        ((prfMsgKeysOracleImpl true P mkSeedStar) (.derive (effectiveHkdfSaltBytes s))).run c) =
        evalPrfMkReal P mkSeedStar := by
      funext s c; exact prfMsgKeysOracleImpl_true_run P mkSeedStar s c
    rw [hEval] at hRed
    rw [hRed]
  have hWorldFalse : ∀ idx, 𝒟[worldAt false idx] = 𝒟[authMkSlotsCutoffExp S P (idx + 1) A.1] := by
    intro idx
    unfold worldAt
    rw [← evalDist_prfMsgKeysSlotsWorld_false_at_idx S P idx A.1]
    refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun mkSeedStar _ => ?_)
    have hRed := simulateQ_authMkReductionRun_eq_redProb S P idx
      (prfMsgKeysOracleImpl false P mkSeedStar) ([] : PrfMkCache) A.1
    dsimp only at hRed
    have hEval : (fun s c =>
        ((prfMsgKeysOracleImpl false P mkSeedStar) (.derive (effectiveHkdfSaltBytes s))).run c) =
        evalPrfMkIdeal := by
      funext s c; exact prfMsgKeysOracleImpl_false_run P mkSeedStar s c
    rw [hEval] at hRed
    rw [hRed]
  have hStep :
      |(𝒟[authMkSlotsCutoffExp S P 0 A.1].boolBias).toReal -
       (𝒟[authMkSlotsCutoffExp S P M A.1].boolBias).toReal| ≤
        2 * (M : ℝ) * (𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed S b A)].boolBias).toReal := by
    rw [hPrfEq]
    exact abs_sub_boolBias_le_two_mul_sampleIndexRange_coin_game M
      (fun k => authMkSlotsCutoffExp S P k A.1)
      (worldAt true)
      (worldAt false)
      (fun idx _ => congrArg (fun d => (d {true}).toReal) (hWorldTrue idx))
      (fun idx _ => congrArg (fun d => (d {true}).toReal) (hWorldFalse idx))
  refine le_trans hStep ?_
  have hM : (M : ℝ) ≤ (S.N_sess_tot : ℝ) := Nat.cast_le.mpr (Nat.min_le_right _ _)
  have hBiasNonneg :
      0 ≤ (𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed S b A)].boolBias).toReal :=
    ENNReal.toReal_nonneg
  nlinarith
end AuthSubHops1to3
export AuthSubHops1to3 (prfMsgKeysReductionAuthFixed prfMsgKeysReductionAuthFixed_queries prfMsgKeysReductionAuthFixed_prim_queries hop_G3_7_G3_8)
end SignalPqxdh.Security
