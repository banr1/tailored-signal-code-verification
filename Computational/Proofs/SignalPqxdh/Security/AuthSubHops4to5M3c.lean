/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3b
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3a
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic

/-!
# Multi-Key `INT-CTXT` Invariant and Send Coupling

Defines the coupling invariant `MuInv` between `pqxdhAuthForgeAllImpl` and
`aeadMuIntReductionAuth` and proves the initiator send coupling.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

theorem lookup_cons_ne {β : Type} (i j : Nat) (b : β) (l : List (Nat × β)) (h : i ≠ j) :
    ((j, b) :: l).lookup i = l.lookup i := by
  simp [List.lookup, beq_eq_false_iff_ne.mpr h]

theorem lookup_cons_self {β : Type} (i : Nat) (b : β) (l : List (Nat × β)) :
    ((i, b) :: l).lookup i = some b := by
  simp [List.lookup]

@[simp] theorem map_opk_x25519_getD_M3 (P : Primitives) (ekASk : Bytes)
    (opkB? : Option (KeyId × Bytes)) :
    opkB?.map (fun _ => P.x25519 ekASk (opkB?.map Prod.snd |>.getD [])) =
      opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk) := by
  cases opkB? <;> rfl

@[simp] theorem runMu_aeadEnc (P : Primitives) (mk : MessageKeys) (ad pt : Bytes)
    (st : AeadMuIntState) :
    @runMu Bytes P (primMuQ (.aeadEnc mk ad pt)) st = pure (P.aeadEnc mk ad pt, st) := by
  rw [runMu_primMuQ]; rfl

/-- Receive-side invariant mapping cached `(sid, salt)` keys to slots `N_send_tot + r0` with
    `r0 < recvCount` and leaving slots `≥ N_send_tot + recvCount` unfilled. -/
def MuRecvInv (S : Setup) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (keys : List (Nat × MessageKeys)) : Prop :=
  (∀ k r0 mk, (k, (r0, mk)) ∈ mkSaltCache →
    r0 < recvCount ∧ keys.lookup (S.N_send_tot + r0) = some mk) ∧
  (∀ r, recvCount ≤ r → keys.lookup (S.N_send_tot + r) = none)

structure MuInv (S : Setup) (P : Primitives)
    (hst hst6 : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes))) : Prop where
  hProj : hst6 = projectMuState P hst
  hValid : ValidAuthLengths S hst.toAuthHybridState
  hSess : ∀ s ∈ hst.toAuthHybridState.idealSessions,
    s.sid ∈ hst.toAuthHybridState.base.usedSendSessions ∧
    s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧
    initSessionSlotIdx s.sid < S.N_send_tot ∧
    keys.lookup (initSessionSlotIdx s.sid) = some s.deriveMessageKeys ∧
    chal.lookup (initSessionSlotIdx s.sid) = some (s.ad, s.aeadCt)
  hFresh : ∀ sid, IsSendSessionId S sid → sid ∉ hst.toAuthHybridState.base.usedSendSessions →
    keys.lookup (initSessionSlotIdx sid) = none ∧ chal.lookup (initSessionSlotIdx sid) = none
  hChalLt : ∀ i, S.N_send_tot ≤ i → chal.lookup i = none
  hRecv : MuRecvInv S hst.recvCount hst.mkSaltCache keys

theorem muInv_empty (S : Setup) (P : Primitives) (secb : Bool) :
    MuInv S P (AuthHybridStateFixed.empty S secb) (AuthHybridStateFixed.empty S secb) [] [] := by
  refine ⟨rfl, validAuthLengths_empty S secb, ?_, ?_, ?_, ?_⟩
  · intro _ h; cases h
  · intro _ _ _; exact ⟨rfl, rfl⟩
  · intro _ _; rfl
  · refine ⟨?_, ?_⟩
    · intro _ _ _ h; cases h
    · intro _ _; rfl

theorem MuInv.of_base_eq {S : Setup} {P : Primitives}
    {hst hst' hst6' : AuthHybridStateFixed S}
    {keys : List (Nat × MessageKeys)} {chal : List (Nat × (Bytes × Bytes))}
    (hInv : MuInv S P hst (projectMuState P hst) keys chal)
    (hProj' : hst6' = projectMuState P hst')
    (hValid' : ValidAuthLengths S hst'.toAuthHybridState)
    (hUsed : hst'.toAuthHybridState.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions)
    (hIdeal : hst'.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions)
    (hRc : hst'.recvCount = hst.recvCount)
    (hMc : hst'.mkSaltCache = hst.mkSaltCache) :
    MuInv S P hst' hst6' keys chal := by
  refine ⟨hProj', hValid', ?_, ?_, hInv.hChalLt, ?_⟩
  · rw [hIdeal, hUsed]; exact hInv.hSess
  · rw [hUsed]; exact hInv.hFresh
  · rw [hMc, hRc]; exact hInv.hRecv

theorem MuRecvInv.succ {S : Setup} {rc : Nat} {c : AuthMkSaltCache S}
    {keys : List (Nat × MessageKeys)} (h : MuRecvInv S rc c keys) :
    MuRecvInv S (rc + 1) c keys :=
  ⟨fun k r0 mk hm => ⟨Nat.lt_succ_of_lt (h.1 k r0 mk hm).1, (h.1 k r0 mk hm).2⟩,
   fun r hr => h.2 r (Nat.le_of_succ_le hr)⟩

theorem MuRecvInv.push_fresh {S : Setup} {rc : Nat} {c : AuthMkSaltCache S}
    {keys : List (Nat × MessageKeys)} (h : MuRecvInv S rc c keys) (mk : MessageKeys) :
    MuRecvInv S (rc + 1) c ((S.N_send_tot + rc, mk) :: keys) := by
  refine ⟨fun k r0 mk0 hm => ?_, fun r hr => ?_⟩
  · rcases h.1 k r0 mk0 hm with ⟨hLt, hL⟩
    refine ⟨Nat.lt_succ_of_lt hLt, ?_⟩
    rw [lookup_cons_ne _ _ _ _ (by omega)]; exact hL
  · rw [lookup_cons_ne _ _ _ _ (by omega)]; exact h.2 r (by omega)

theorem MuRecvInv.push_cache {S : Setup} {rc : Nat} {c : AuthMkSaltCache S}
    {keys : List (Nat × MessageKeys)} (h : MuRecvInv S rc c keys) (key : SessionId S × Option Bytes)
    (mk : MessageKeys) :
    MuRecvInv S (rc + 1) ((key, (rc, mk)) :: c) ((S.N_send_tot + rc, mk) :: keys) := by
  refine ⟨fun k r0 mk0 hm => ?_, (h.push_fresh mk).2⟩
  rcases List.mem_cons.mp hm with hHead | hTail
  · rcases Prod.mk.inj hHead with ⟨_, hPair⟩
    rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
    exact ⟨Nat.lt_succ_self _, lookup_cons_self _ _ _⟩
  · exact (h.push_fresh mk).1 k r0 mk0 hTail

theorem MuRecvInv.push_send {S : Setup} {rc : Nat} {c : AuthMkSaltCache S}
    {keys : List (Nat × MessageKeys)} (h : MuRecvInv S rc c keys) (i : Nat) (hi : i < S.N_send_tot)
    (mk : MessageKeys) :
    MuRecvInv S rc c ((i, mk) :: keys) := by
  refine ⟨fun k r0 mk0 hm => ?_, fun r hr => ?_⟩
  · rcases h.1 k r0 mk0 hm with ⟨hLt, hL⟩
    exact ⟨hLt, by rw [lookup_cons_ne _ _ _ _ (by omega)]; exact hL⟩
  · rw [lookup_cons_ne _ _ _ _ (by omega)]; exact h.2 r hr

theorem muInv_finishAuthSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hSidLt : initSessionSlotIdx sid < S.N_send_tot)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (p : AuthIntSendPrep S)
    (mk : MessageKeys) (hst : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hInv : MuInv S P hst (projectMuState P hst) keys chal)
    (hNotCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = false)
    (hProv : (p.spkHon, p.opkHon, p.pqspkHon) =
      checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
        hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle)
    (hIdealEq : p.isIdealSend = (p.isFreshPeer || (p.peerPrincipal?.isSome &&
      checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles bundle && p.pqspkHon))) :
    let aeadCt := P.aeadEnc mk p.ad p.msgPlain
    let (resp5, hst5') := finishAuthHybridSend P sid p.uEntry p.peerPrincipal? p.isFreshPeer
      bundle m0 m1 p.ekASk p.ekAPk p.ss p.kemCt p.ephASk p.ephAPk p.drKey p.rk1 p.ck1_0
      p.mkSeed p.ck1_1 p.spqrSalt? p.pqRatchetMsg mk p.ad aeadCt p.msgPlain
      p.roCache' p.rootRoCache' hst.toAuthHybridState
    let (resp6, hst6') := finishAuthIntSendPure sid bundle m0 m1 p
      (if p.isIdealSend then default else mk) aeadCt (projectMuState P hst)
    let keys' := if p.isIdealSend then (initSessionSlotIdx sid, mk) :: keys else keys
    let chal' := if p.isIdealSend then (initSessionSlotIdx sid, (p.ad, aeadCt)) :: chal else chal
    resp5 = resp6 ∧
    MuInv S P
      { toAuthHybridState := hst5', recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache }
      hst6' keys' chal' := by
  dsimp only
  have hSpk : p.spkHon = (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
      hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).1 :=
    Prod.ext_iff.mp hProv |>.1
  have hOpk : p.opkHon = (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
      hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).2.1 :=
    (Prod.ext_iff.mp (Prod.ext_iff.mp hProv).2).1
  have hPq : p.pqspkHon = (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
      hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).2.2 :=
    (Prod.ext_iff.mp (Prod.ext_iff.mp hProv).2).2
  have hNotMem : sid ∉ hst.toAuthHybridState.base.usedSendSessions := by
    intro hm; exact Bool.noConfusion (hNotCont.symm.trans (List.contains_iff_mem.mpr hm))
  have hNotAny : (hst.toAuthHybridState.base.usedSendSessions.any (fun s => s == sid)) = false := by
    rw [Bool.eq_false_iff]; intro hAny
    rcases List.any_eq_true.mp hAny with ⟨s, hs, hEq⟩
    exact hNotMem ((beq_iff_eq.mp hEq) ▸ hs)
  rcases hInv.hFresh sid hSend hNotMem with ⟨hKNone, hCNone⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold finishAuthIntSendPure finishAuthHybridSend projectMuState projectMuHybrid
      eraseAuthEvents maskMuSession
    dsimp only; rw [← hSpk, ← hOpk, ← hPq, ← hIdealEq]
    cases p.isIdealSend <;> simp only [↓reduceIte, Bool.false_eq_true, List.map_cons]
  · refine ⟨hInv.hValid.1, hInv.hValid.2.1, hInv.hValid.2.2.1,
      (validSessionIds_cons S sid _ hSend hInv.hValid.2.2.2.1 hNotAny).1, ?_⟩
    unfold finishAuthHybridSend; dsimp only
    have hLen := hInv.hValid.2.2.2.2
    split <;> (simp only [List.length_cons]; omega)
  · intro s hs
    unfold finishAuthHybridSend at hs; dsimp only at hs
    rw [← hPq, ← hIdealEq] at hs
    unfold finishAuthHybridSend; dsimp only
    by_cases hId : p.isIdealSend = true
    · simp only [hId, ↓reduceIte, List.mem_cons] at hs ⊢
      rcases hs with rfl | hsOld
      · exact ⟨Or.inl rfl, rfl, hSidLt, lookup_cons_self _ _ _, lookup_cons_self _ _ _⟩
      · rcases hInv.hSess s hsOld with ⟨hMemOld, hCt, hLt, hK, hC⟩
        have hNeSid : s.sid ≠ sid := fun hEq => hNotMem (hEq ▸ hMemOld)
        have hNeIdx : initSessionSlotIdx s.sid ≠ initSessionSlotIdx sid := fun hEq =>
          hNeSid (initSessionSlotIdx_inj_of_lt hEq hSidLt)
        refine ⟨Or.inr hMemOld, hCt, hLt, ?_, ?_⟩
        · rw [lookup_cons_ne _ _ _ _ hNeIdx]; exact hK
        · rw [lookup_cons_ne _ _ _ _ hNeIdx]; exact hC
    · simp only [hId, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      rcases hInv.hSess s hs with ⟨hMemOld, hCt, hLt, hK, hC⟩
      exact ⟨List.mem_cons_of_mem _ hMemOld, hCt, hLt, hK, hC⟩
  · intro sid' hSend' hNot'
    unfold finishAuthHybridSend at hNot'; dsimp only at hNot'
    have hNe : sid' ≠ sid := fun h => hNot' (h ▸ List.mem_cons_self)
    have hNot0 : sid' ∉ hst.toAuthHybridState.base.usedSendSessions := fun h =>
      hNot' (List.mem_cons_of_mem _ h)
    have hNeIdx : initSessionSlotIdx sid' ≠ initSessionSlotIdx sid := fun hEq =>
      hNe (initSessionSlotIdx_inj_of_lt hEq hSidLt)
    rcases hInv.hFresh sid' hSend' hNot0 with ⟨hK, hC⟩
    by_cases hId : p.isIdealSend = true
    · simp only [hId, ↓reduceIte]
      rw [lookup_cons_ne _ _ _ _ hNeIdx, lookup_cons_ne _ _ _ _ hNeIdx]; exact ⟨hK, hC⟩
    · simp only [hId, Bool.false_eq_true, ↓reduceIte]; exact ⟨hK, hC⟩
  · intro i hi
    by_cases hId : p.isIdealSend = true
    · simp only [hId, ↓reduceIte]
      rw [lookup_cons_ne _ _ _ _ (by omega)]; exact hInv.hChalLt i hi
    · simp only [hId, Bool.false_eq_true, ↓reduceIte]; exact hInv.hChalLt i hi
  · by_cases hId : p.isIdealSend = true
    · simp only [hId, ↓reduceIte]; exact hInv.hRecv.push_send _ hSidLt mk
    · simp only [hId, Bool.false_eq_true, ↓reduceIte]; exact hInv.hRecv

def isFreshPeerM3 (o : Option (Nat × PrincipalEntry)) : Bool :=
  match o with
  | some (_, pEntry) => !pEntry.corrupted
  | none => false

theorem not_isFreshPeerM3_eq
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (o : Option (Nat × PrincipalEntry))
    (hSome : ∀ a b,
      G (some (a, b)) (fun _ pEntry => !pEntry.corrupted) (fun _ => false) = !b.corrupted)
    (hNone : G none (fun _ pEntry => !pEntry.corrupted) (fun _ => false) = false) :
    (!(G o (fun _ pEntry => !pEntry.corrupted) (fun _ => false))) = !isFreshPeerM3 o := by
  rcases o with _ | ⟨a, b⟩
  · exact congrArg Bool.not hNone
  · exact congrArg Bool.not (hSome a b)

theorem or_isFreshPeerM3_eq
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (o : Option (Nat × PrincipalEntry)) (r : Bool)
    (hSome : ∀ a b,
      G (some (a, b)) (fun _ pEntry => !pEntry.corrupted) (fun _ => false) = !b.corrupted)
    (hNone : G none (fun _ pEntry => !pEntry.corrupted) (fun _ => false) = false) :
    (G o (fun _ pEntry => !pEntry.corrupted) (fun _ => false) || r) = (isFreshPeerM3 o || r) := by
  rcases o with _ | ⟨a, b⟩
  · exact congrArg (· || r) hNone
  · exact congrArg (· || r) (hSome a b)

theorem relProbDom_runAuthSend_mu {S : Setup} (P : Primitives)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hSidLt : initSessionSlotIdx sid < S.N_send_tot)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst hst6 : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hInv : MuInv S P hst hst6 keys chal) :
    RelProbDom
      (fun p5 p6 => p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p6 => p6.2.2.2)
      ((fun p : AuthResponse × AuthHybridState S => (p.1, ({
        toAuthHybridState := p.2, recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache },
            false))) <$>
        evalAuthHybridSendKosk .g3_8 true S P sid u bundle m0 m1 hst.toAuthHybridState)
      (runMu P (runAuthSendMuPrim S sid u bundle m0 m1 hst6) (keys, chal, false)) := by
  rcases hInv.hProj with rfl
  have hInv0 : MuInv S P
      { toAuthHybridState := hst.toAuthHybridState
        recvCount := hst.recvCount
        mkSaltCache := hst.mkSaltCache }
      (projectMuState P hst) keys chal :=
    hInv.of_base_eq rfl hInv.hValid rfl rfl rfl rfl
  rcases validAuthLengths_bounds S P hInv.hValid with ⟨hPrinLen, hSpkLen, hOpkLen, _⟩
  have hAdv := validAdvKeysPow8_map P hst.toAuthHybridState.base.advKeys
  unfold evalAuthHybridSendKosk runAuthSendMuPrim prepAuthIntSendPrim
  have hb_used : (projectMuState P hst).toAuthHybridState.base.usedSendSessions =
      hst.toAuthHybridState.base.usedSendSessions := rfl
  have hb_princ : (projectMuState P hst).toAuthHybridState.base.principals =
      hst.toAuthHybridState.base.principals := rfl
  have hb_spk : (projectMuState P hst).toAuthHybridState.base.spkBundles =
      hst.toAuthHybridState.base.spkBundles := rfl
  have hb_opk : (projectMuState P hst).toAuthHybridState.base.opkEntries =
      hst.toAuthHybridState.base.opkEntries := rfl
  have hb_adv : (projectMuState P hst).toAuthHybridState.base.advKeys =
      hst.toAuthHybridState.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) := rfl
  have hb_secb : (projectMuState P hst).toAuthHybridState.base.secb =
      hst.toAuthHybridState.base.secb := rfl
  have hb_ro : (projectMuState P hst).toAuthHybridState.base.roCache =
      hst.toAuthHybridState.base.roCache := rfl
  have hb_rro : (projectMuState P hst).toAuthHybridState.base.rootRoCache =
      hst.toAuthHybridState.base.rootRoCache := rfl
  dsimp only
  rw [runMu_embedPrimMu_bind, hb_used, hb_princ, hb_spk, hb_opk, hb_adv, hb_secb, hb_ro,
      hb_rro]
  have hFA : AuthHybridStage.g3_8.idealFreshAead = false := rfl
  have hMK : AuthHybridStage.g3_8.idealMsgKeys = true := rfl
  simp only [hFA, hMK, evalAuthHybridSendSchedule_g3_8, Bool.and_true]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, simulateQ_pure, pure_bind, runMu_pure, map_pure]
    exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.toAuthHybridState.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, simulateQ_pure, pure_bind, runMu_pure, map_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      have hNotCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = false :=
          Bool.eq_false_iff.mpr h2
      have hNotMem : sid ∉ hst.toAuthHybridState.base.usedSendSessions :=
        fun hm => Bool.noConfusion (hNotCont.symm.trans (List.contains_iff_mem.mpr hm))
      rcases hInv.hFresh sid hSend hNotMem with ⟨hKNone, hCNone⟩
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [simulateQ_pure, pure_bind, runMu_pure, map_pure]
        exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
      | some up =>
        rcases up with ⟨_, uEntry⟩
        rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P _ bundle.ikB hPrinLen, pure_bind]
        dsimp only
        rw [not_isFreshPeerM3_eq
              (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB),
            not_isFreshPeerM3_eq
              (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
        all_goals try (intros; rfl)
        by_cases h3 : (!isFreshPeerM3
            (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB) &&
            (m0 != m1)) = true
        · simp only [h3, ↓reduceIte, simulateQ_pure, pure_bind, runMu_pure, map_pure]
          exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          rw [simulateQ_bind,
              simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrinLen hSpkLen hOpkLen hAdv,
            koskBundleOk_map_advKeys, pure_bind]
          by_cases h4 : (!koskBundleOk P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles
              hst.toAuthHybridState.base.opkEntries hst.toAuthHybridState.base.advKeys bundle)
                  = true
          · simp only [h4, ↓reduceIte, simulateQ_pure, pure_bind, runMu_pure, map_pure]
            exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
          · simp only [h4, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
              map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
            refine RelProbDom.bind_same sampleScalar32 (fun ekASk =>
              RelProbDom.bind_same sampleCoins32 (fun kemCoins =>
              RelProbDom.bind_same sampleScalar32 (fun ephASk =>
              RelProbDom.bind_same sampleCoins32 (fun spqrCoins => ?_))))
            simp only [resolveSigPkPeer_findHonestPrincipal, sim_fg_sigVerify, pure_bind]
            by_cases h5 : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
                bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig &&
                P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h5, ↓reduceIte, simulateQ_pure, pure_bind, runMu_pure]
              exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
            · simp only [h5, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, sim_fg_kemEncaps,
                pure_bind]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                simp only [simulateQ_pure, pure_bind, runMu_pure]
                exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩
                simp only [simulateQ_bind, sim_fg_x25519Base, bind_assoc, pure_bind]
                rw [simulateQ_checkBundleProvenanceExactPrim S P _ _ _ bundle hPrinLen hOpkLen,
                    pure_bind]
                rcases hProv : checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
                  hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle
                      with ⟨spkHon, opkHon, pqspkHon⟩
                simp only [sim_fg_x25519, map_opk_x25519_getD_M3, pure_bind]
                rw [simulateQ_checkBundleSpkHonIdealPeerPrim S P _ _ bundle hSpkLen, pure_bind]
                rw [or_isFreshPeerM3_eq
                      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB),
                    or_isFreshPeerM3_eq
                      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)]
                all_goals try (intros; rfl)
                by_cases hIdeal : (isFreshPeerM3
                    (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB) ||
                    ((findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB).isSome
                        &&
                      checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
                          hst.toAuthHybridState.base.spkBundles bundle &&
                      pqspkHon)) = true
                · simp only [hIdeal, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
                    simulateQ_pure, sim_fg_spqrInitSend, bind_assoc, pure_bind]
                  refine RelProbDom.bind_same sampleDRKey96 (fun dk =>
                    RelProbDom.bind_same sampleBytes32 (fun r =>
                    RelProbDom.bind_same sampleBytes32 (fun c =>
                    RelProbDom.bind_same sampleBytes32 (fun ms =>
                    RelProbDom.bind_same sampleBytes32 (fun cn => ?_)))))
                  cases P.spqrInitSend dk.pqrKey spqrCoins with
                  | none =>
                    simp only [simulateQ_pure, pure_bind, runMu_pure]
                    exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
                  | some spqrTriple =>
                    rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    simp only [simulateQ_pure, pure_bind, ↓reduceIte, bind_assoc, runMu_bind,
                      runMu_encOnceMuQ_fresh P _ _ _ keys chal false hCNone hKNone, runMu_pure,
                      Option.getD_some]
                    refine RelProbDom.bind_same sampleMessageKeys80 (fun mk => ?_)
                    have hFin :=
                        muInv_finishAuthSend P sid hSend hSidLt bundle m0 m1
                      {
                        uEntry := uEntry, peerPrincipal? :=
                            findHonestPrincipal P hst.toAuthHybridState.base.principals
                                bundle.ikB,
                        isFreshPeer := isFreshPeerM3
                          (findHonestPrincipal P hst.toAuthHybridState.base.principals
                            bundle.ikB),
                        isIdealSend := true,
                        msgPlain := if isFreshPeerM3
                          (findHonestPrincipal P hst.toAuthHybridState.base.principals
                            bundle.ikB) =
                            true then
                              if hst.toAuthHybridState.base.secb = true then m1 else m0 else m0,
                        ekASk := ekASk, ekAPk := P.x25519Base ekASk, ss := ss, kemCt := kemCt,
                            ephASk := ephASk,
                        ephAPk := P.x25519Base ephASk, drKey := dk, roCache' :=
                            hst.toAuthHybridState.base.roCache, rk1 := r, ck1_0 := c,
                        rootRoCache' := hst.toAuthHybridState.base.rootRoCache, mkSeed := ms,
                            ck1_1 := cn,
                        spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
                        ad := firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk)
                            pqRatchetMsg,
                        spkHon := spkHon, opkHon := opkHon, pqspkHon := pqspkHon }
                      mk hst keys chal hInv hNotCont hProv.symm (by simp [hIdeal])
                    simp only [↓reduceIte] at hFin
                    revert hFin
                    rcases findHonestPrincipal P hst.toAuthHybridState.base.principals
                      bundle.ikB with _ | ⟨_, _⟩ <;>
                      exact fun hFin => RelProbDom.of_pure ⟨hFin.1, rfl, rfl, hFin.2⟩
                · simp only [hIdeal, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
                    simulateQ_embedUnif, simulateQ_pure, sim_fg_chainKdfSeed,
                    sim_fg_chainKdfNext, sim_fg_spqrInitSend, bind_assoc, pure_bind]
                  refine RelProbDom.bind_same (evalHkdfRoPure _ _) (fun dkPair => ?_)
                  rcases dkPair with ⟨dk, roCache'⟩
                  refine RelProbDom.bind_same (evalRootKdfRoPure _ _ _) (fun rkPair => ?_)
                  rcases rkPair with ⟨⟨r, c⟩, rootRoCache'⟩
                  cases P.spqrInitSend dk.pqrKey spqrCoins with
                  | none =>
                    simp only [simulateQ_pure, pure_bind, runMu_pure]
                    exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv0⟩
                  | some spqrTriple =>
                    rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    simp only [simulateQ_pure, pure_bind, ↓reduceIte,
                      runMu_bind, runMu_pure, runMu_deriveMsgKeys, runMu_aeadEnc, bind_assoc,
                      Bool.false_eq_true]
                    have hFin :=
                        muInv_finishAuthSend P sid hSend hSidLt bundle m0 m1
                      {
                        uEntry := uEntry, peerPrincipal? :=
                            findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB,
                        isFreshPeer := isFreshPeerM3
                          (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB),
                        isIdealSend := false,
                        msgPlain := if isFreshPeerM3
                          (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB) =
                            true then
                              if hst.toAuthHybridState.base.secb = true then m1 else m0 else m0,
                        ekASk := ekASk, ekAPk := P.x25519Base ekASk, ss := ss, kemCt := kemCt,
                            ephASk := ephASk,
                        ephAPk := P.x25519Base ephASk, drKey := dk, roCache' := roCache', rk1 := r,
                            ck1_0 := c,
                        rootRoCache' := rootRoCache', mkSeed := P.chainKdfSeed c, ck1_1 :=
                            P.chainKdfNext c,
                        spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
                        ad := firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg,
                        spkHon := spkHon, opkHon := opkHon, pqspkHon := pqspkHon }
                      (P.deriveMsgKeys (P.chainKdfSeed c) spqrSalt?)
                          hst keys chal hInv hNotCont hProv.symm (by simp [hIdeal])
                    simp only [Bool.false_eq_true, ↓reduceIte] at hFin
                    revert hFin
                    rcases findHonestPrincipal P hst.toAuthHybridState.base.principals
                      bundle.ikB with _ | ⟨_, _⟩ <;>
                      exact fun hFin => RelProbDom.of_pure ⟨hFin.1, rfl, rfl, hFin.2⟩

end SignalPqxdh.Security
