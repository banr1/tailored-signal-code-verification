/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3G
import Computational.Proofs.SignalPqxdh.Security.CollisionsC
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
namespace SignalPqxdh.Security.AuthSubHops1to3
def setSlotRkIdealSession {S : Setup} (idx : Nat) (rkStar : Bytes)
    (s : IdealAuthSession S) : IdealAuthSession S :=
  if sessionSlotIndex s.sid == idx then
    { s with drKey := { s.drKey with rootKey := rkStar } }
  else
    s
@[simp] theorem setSlotRkIdealSession_sid {S : Setup} (idx : Nat) (rkStar : Bytes)
    (s : IdealAuthSession S) :
    (setSlotRkIdealSession idx rkStar s).sid = s.sid := by
  unfold setSlotRkIdealSession; split <;> rfl
@[simp] theorem setSlotRkIdealSession_ephAPk {S : Setup} (idx : Nat) (rkStar : Bytes)
    (s : IdealAuthSession S) :
    (setSlotRkIdealSession idx rkStar s).ephAPk = s.ephAPk := by
  unfold setSlotRkIdealSession; split <;> rfl
@[simp] theorem setSlotRkIdealSession_pqrKey {S : Setup} (idx : Nat) (rkStar : Bytes)
    (s : IdealAuthSession S) :
    (setSlotRkIdealSession idx rkStar s).drKey.pqrKey = s.drKey.pqrKey := by
  unfold setSlotRkIdealSession; split <;> rfl
theorem setSlotRkIdealSession_eq_self_of_ne {S : Setup} {idx : Nat} {rkStar : Bytes}
    {s : IdealAuthSession S} (hNe : (sessionSlotIndex s.sid == idx) = false) :
    setSlotRkIdealSession idx rkStar s = s := by
  unfold setSlotRkIdealSession; simp [hNe]
theorem setSlotRkIdealSession_rootKey_of_eq {S : Setup} {idx : Nat} {rkStar : Bytes}
    {s : IdealAuthSession S} (hEq : (sessionSlotIndex s.sid == idx) = true) :
    (setSlotRkIdealSession idx rkStar s).drKey.rootKey = rkStar := by
  unfold setSlotRkIdealSession; simp [hEq]
@[simp] theorem matchIdealAuthHandshake_setSlotRkIdealSession {S : Setup} (P : Primitives)
    (idx : Nat) (rkStar : Bytes)
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr (setSlotRkIdealSession idx rkStar
        s) =
      matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr s := by
  unfold setSlotRkIdealSession
  split <;> rfl
theorem find?_matchIdealAuthHandshake_map_setSlotRkIdealSession {S : Setup} (P : Primitives)
    (idx : Nat) (rkStar : Bytes)
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (L : List (IdealAuthSession S)) :
    (L.map (setSlotRkIdealSession idx rkStar)).find?
        (matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr) =
      (L.find? (matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr)).map
        (setSlotRkIdealSession idx rkStar) := by
  induction L with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, List.find?_cons, matchIdealAuthHandshake_setSlotRkIdealSession]
    split
    · rfl
    · exact ih
def withRkAuth {S : Setup} (idx : Nat) (rkStar : Bytes) (c : List ((Bytes × Bytes) × (Bytes ×
    Bytes)))
    (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { hst with
    toAuthHybridState :=
      { hst.toAuthHybridState with
        base := { hst.toAuthHybridState.base with rootRoCache := c }
        idealSessions := hst.toAuthHybridState.idealSessions.map (setSlotRkIdealSession idx rkStar)
            } }
@[simp] theorem withRkAuth_hasWonAuth {S : Setup} (idx : Nat) (rkStar : Bytes)
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (hst : AuthHybridStateFixed S) :
    (withRkAuth idx rkStar c hst).toAuthHybridState.base.hasWonAuth =
      hst.toAuthHybridState.base.hasWonAuth := rfl
@[simp] theorem withRkAuth_finalize_eq {S : Setup} (P : Primitives) (secb b' : Bool)
    (idx : Nat) (rkStar : Bytes) (c : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridStateFixed S) :
    finalizeAuthFixed P secb b' (withRkAuth idx rkStar c hst).toAuthHybridState =
      finalizeAuthFixed P secb b' hst.toAuthHybridState := rfl
@[simp] theorem withRkAuth_authSlotFired_eq {S : Setup}
    (idx : Nat) (rkStar : Bytes) (c : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridStateFixed S) :
    authSlotFired S idx (withRkAuth idx rkStar c hst) = authSlotFired S idx hst := rfl
@[simp] theorem withRkAuth_hasKemPkCollisionAuth_eq {S : Setup}
    (idx : Nat) (rkStar : Bytes) (c : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridStateFixed S) :
    hasKemPkCollisionAuth (withRkAuth idx rkStar c hst).toAuthHybridState =
      hasKemPkCollisionAuth hst.toAuthHybridState := rfl
structure AuthRkStateWf {S : Setup} (P : Primitives) (hst : AuthHybridStateFixed S) : Prop where
  spk_wf : ∀ p ∈ hst.toAuthHybridState.base.spkBundles,
    p.2.spkSk.length = 32 ∧ p.2.spkPk = P.x25519Base p.2.spkSk
  ideal_wf : ∀ s ∈ hst.toAuthHybridState.idealSessions,
    hst.toAuthHybridState.base.usedSendSessions.contains s.sid = true ∧
    sendSlotIndex? s.sid = some (sessionSlotIndex s.sid) ∧
    s.ikAPk ∈ hst.toAuthHybridState.base.principals.map (fun (_, e) => e.ikAPk) ∧
    P.isCanonical s.ekAPk = true
def SlotSessionCacheInv {S : Setup} (P : Primitives) (rkStar : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst6 : AuthHybridStateFixed S) (s : IdealAuthSession S) : Prop :=
  (∃ ephASk : Bytes, s.ephAPk = P.x25519Base ephASk ∧ ∀ dh : Bytes,
      c5.find? (fun (inp, _) => inp == (rkStar, dh)) = if dh == P.x25519 ephASk s.peerSpkPk then
          some ((rkStar, dh), (s.rk1, s.ck1_0))
        else
          none) ∨
  (∃ k j bEntry, ((k, j), bEntry) ∈ hst6.toAuthHybridState.base.spkBundles ∧
    bEntry.pqspkPk = s.peerPqspkPk ∧
    (k, UInt32.ofNat j, UInt32.ofNat j, s.ekAPk) ∈ hst6.toAuthHybridState.base.seenKyberBaseKeys)
def AgreeOffRkAuth {S : Setup} (P : Primitives) (rkStar : Bytes) (idx : Nat)
    (s5 s6 : AuthHybridStateFixed S) : Prop :=
  ∃ c5 : List ((Bytes × Bytes) × (Bytes × Bytes)), s5 = withRkAuth idx rkStar c5 s6 ∧
    cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false ∧
    (authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache) ∧
    filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache ∧
    AuthRkStateWf P s6 ∧
    (∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s) ∧
    (∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2)
theorem AgreeOffRkAuth.empty {S : Setup} (P : Primitives) (rkStar : Bytes) (idx : Nat) (secb :
    Bool) :
    AgreeOffRkAuth P rkStar idx (AuthHybridStateFixed.empty S secb)
      (AuthHybridStateFixed.empty S secb) := by
  refine ⟨[], rfl, rfl, fun _ => rfl, rfl, {
      spk_wf := fun _ h => False.elim (List.not_mem_nil h)
      ideal_wf := fun _ h => False.elim (List.not_mem_nil h) },
    fun _ h => False.elim (List.not_mem_nil h),
    fun _ h => False.elim (List.not_mem_nil h)⟩
theorem AgreeOffRkAuth.noRk6 {S : Setup} {P : Primitives} {rkStar : Bytes} {idx : Nat}
    {s5 s6 : AuthHybridStateFixed S} (h : AgreeOffRkAuth P rkStar idx s5 s6) :
    cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false := by
  rcases h with ⟨_, _, hNoRk, _⟩; exact hNoRk
theorem AgreeOffRkAuth.finalize_eq {S : Setup} (P : Primitives) (secb b' : Bool)
    {rkStar : Bytes} {idx : Nat} {s5 s6 : AuthHybridStateFixed S}
    (h : AgreeOffRkAuth P rkStar idx s5 s6) :
    finalizeAuthFixed P secb b' s5.toAuthHybridState =
      finalizeAuthFixed P secb b' s6.toAuthHybridState := by
  rcases h with ⟨c5, rfl, _⟩; rfl
theorem AgreeOffRkAuth.hasKemPkCollisionAuth_eq {S : Setup} {P : Primitives}
    {rkStar : Bytes} {idx : Nat} {s5 s6 : AuthHybridStateFixed S}
    (h : AgreeOffRkAuth P rkStar idx s5 s6) :
    hasKemPkCollisionAuth s5.toAuthHybridState = hasKemPkCollisionAuth s6.toAuthHybridState := by
  rcases h with ⟨c5, rfl, _⟩; rfl
theorem dhRatchet_eq_iff_sameEph (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (spkSk spkPk ephASk ephAPk peerSpkPk msgEphAPk : Bytes)
    (hSpkLen : spkSk.length = 32) (hSpkPk : spkPk = P.x25519Base spkSk)
    (hEphPk : ephAPk = P.x25519Base ephASk)
    (hPeerSpk : P.pow8 spkPk = P.pow8 peerSpkPk)
    (hMsgEphLen : msgEphAPk.length = 32) :
    (P.x25519 spkSk msgEphAPk == P.x25519 ephASk peerSpkPk) = (P.pow8 msgEphAPk == P.pow8 ephAPk)
        := by
  have hComm : P.x25519 spkSk ephAPk = P.x25519 ephASk peerSpkPk := by
    have hPowBase : P.pow8 (P.x25519Base spkSk) = P.pow8 peerSpkPk := hSpkPk ▸ hPeerSpk
    rw [hEphPk, hP.x25519_comm spkSk ephASk]
    exact hP.x25519_pow8_congr ephASk (P.x25519Base spkSk) peerSpkPk
      (hP.x25519Base_len spkSk) (hP.pow8_base_len peerSpkPk spkSk hPowBase.symm) hPowBase
  rw [← hComm]
  exact Bool.eq_iff_iff.mpr (by
    rw [beq_iff_eq, beq_iff_eq]
    exact x25519_eq_iff_pow8_eq P hP spkSk msgEphAPk ephAPk hSpkLen hMsgEphLen
      (hEphPk ▸ hP.x25519Base_len ephASk))
theorem findHonestPrincipal_isSome_of_mem_honestIkPks (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (hdrIk ik : Bytes)
    (hMem : ik ∈ principals.map (fun (_, e) => e.ikAPk))
    (hPow : P.pow8 hdrIk = P.pow8 ik) :
    (findHonestPrincipal P principals hdrIk).isSome = true := by
  unfold findHonestPrincipal; rw [List.find?_isSome]
  rcases List.mem_map.mp hMem with ⟨⟨pIdx, pEntry⟩, hpMem, rfl⟩
  exact ⟨(pIdx, pEntry), hpMem, by simp [hPow]⟩
theorem find?_rk_eq_none_of_cacheHasRk_false (rkStar dh : Bytes) :
    ∀ (cache : List ((Bytes × Bytes) × (Bytes × Bytes))), cacheHasRk rkStar cache = false →
      cache.find? (fun (inp, _) => inp == (rkStar, dh)) = none
  | [], _ => rfl
  | ((rk', dh'), out) :: rest, h => by
    unfold cacheHasRk at h; simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hHead : (((rk', dh') == (rkStar, dh))) = false := by
      rw [beq_eq_false_iff_ne]
      intro hEq; rcases Prod.mk.inj hEq with ⟨rfl, _⟩
      have h1 := h.1
      simp at h1
    simp only [List.find?, hHead]
    exact find?_rk_eq_none_of_cacheHasRk_false rkStar dh rest h.2
theorem find?_cons_rk_self_of_cacheHasRk_false (rkStar dh0 : Bytes) (out0 : Bytes × Bytes)
    (cache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hNoRk : cacheHasRk rkStar cache = false) (dh : Bytes) :
    (((rkStar, dh0), out0) :: cache).find? (fun (inp, _) => inp == (rkStar, dh)) =
      if dh == dh0 then some ((rkStar, dh), out0) else none := by
  by_cases hEq : (dh == dh0) = true
  · have hdh : dh = dh0 := beq_iff_eq.mp hEq
    subst hdh
    simp
  · have hNe : dh0 ≠ dh := by
      intro h; subst h; exact hEq (beq_self_eq_true dh0)
    have hHead : (((rkStar, dh0) == (rkStar, dh))) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; exact hNe (Prod.mk.inj h).2
    simp only [List.find?, hHead, hEq, Bool.false_eq_true, ↓reduceIte]
    exact find?_rk_eq_none_of_cacheHasRk_false rkStar dh cache hNoRk
theorem SlotSessionCacheInv.preserved_of_find?_eq {S : Setup} {P : Primitives}
    {rkStar : Bytes} {c5 c5' : List ((Bytes × Bytes) × (Bytes × Bytes))}
    {hst6 hst6' : AuthHybridStateFixed S} {s : IdealAuthSession S}
    (hInv : SlotSessionCacheInv P rkStar c5 hst6 s)
    (hFind : ∀ dh, c5'.find? (fun (inp, _) => inp == (rkStar, dh)) =
      c5.find? (fun (inp, _) => inp == (rkStar, dh)))
    (hSpk : ∀ p ∈ hst6.toAuthHybridState.base.spkBundles, p ∈
        hst6'.toAuthHybridState.base.spkBundles)
    (hKyber : ∀ t ∈ hst6.toAuthHybridState.base.seenKyberBaseKeys,
      t ∈ hst6'.toAuthHybridState.base.seenKyberBaseKeys) :
    SlotSessionCacheInv P rkStar c5' hst6' s := by
  rcases hInv with ⟨ephASk, hPk, hC⟩ | ⟨k, j, bEntry, hMemB, hPq, hMemK⟩
  · refine Or.inl ⟨ephASk, hPk, fun dh => ?_⟩
    rw [hFind dh, hC dh]
  · exact Or.inr ⟨k, j, bEntry, hSpk _ hMemB, hPq, hKyber _ hMemK⟩
theorem authSlotFired_of_idealSession_slot_eq {S : Setup} {P : Primitives} {idx : Nat}
    {hst : AuthHybridStateFixed S} {s : IdealAuthSession S}
    (hWf : AuthRkStateWf P hst)
    (hsMem : s ∈ hst.toAuthHybridState.idealSessions)
    (hSlot : sessionSlotIndex s.sid = idx) :
    authSlotFired S idx hst = true := by
  have hSid := hWf.ideal_wf s hsMem
  have hLt : idx < S.N_send_tot := by
    rw [← hSlot]
    exact sendSlotIndex?_lt hSid.2.1
  unfold authSlotFired; simp only [hLt, ↓reduceIte, List.any_eq_true]
  exact ⟨s.sid, List.contains_iff_mem.mp hSid.1, by rw [hSid.2.1, hSlot]; simp⟩
theorem relProbUpToBad_evalRootKdfOrRo_ext (P : Primitives) (rkStar rk dh : Bytes)
    (cache5 cache6 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hFilter : filterOutRk rkStar cache5 = cache6)
    (hNoRk : cacheHasRk rkStar cache6 = false) :
    RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ filterOutRk rkStar y5.2 = y6.2 ∧
        cacheHasRk rkStar y6.2 = false ∧
        (cache5 = cache6 → y5.2 = y6.2) ∧
        (∀ dh0, y5.2.find? (fun (inp, _) => inp == (rkStar, dh0)) =
          cache5.find? (fun (inp, _) => inp == (rkStar, dh0))))
      (fun y6 => cacheHasRk rkStar y6.2)
      (evalRootKdfOrRo true P cache5 rk dh)
      (evalRootKdfOrRo true P cache6 rk dh) := by
  by_cases hEq : (rk == rkStar) = true
  · have hrk : rk = rkStar := beq_iff_eq.mp hEq
    subst hrk; exact RelProbUpToBad.bad6 _ _ (cacheHasRk_evalRootKdfOrRo_self P rk dh cache6)
  · have hEqF : (rk == rkStar) = false := Bool.eq_false_iff.mpr hEq
    have hfind : cache5.find? (fun (inp, _) => inp == (rk, dh)) =
        cache6.find? (fun (inp, _) => inp == (rk, dh)) := by
      rw [find?_eq_find?_filterOutRk rkStar rk dh hEqF cache5, hFilter]
    unfold evalRootKdfOrRo; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfind]
    cases cache6.find? (fun (inp, _) => inp == (rk, dh)) with
    | some p =>
      rcases p with ⟨_, out⟩
      exact RelProbUpToBad.of_pure ⟨rfl, hFilter, hNoRk, fun h => h, fun _ => rfl⟩
    | none =>
      refine RelProbUpToBad.bind_same sampleBytes32 (fun rk1 => ?_)
      refine RelProbUpToBad.bind_same sampleBytes32 (fun ck1 => ?_)
      apply RelProbUpToBad.of_pure
      have hne' : (rk != rkStar) = true := by
        rw [bne_iff_ne]; exact beq_eq_false_iff_ne.mp hEqF
      refine ⟨rfl, ?_, ?_, fun h => by rw [h], fun dh0 => ?_⟩
      · unfold filterOutRk at hFilter ⊢; simp [hne', hFilter]
      · unfold cacheHasRk at hNoRk ⊢; simp [hEqF, hNoRk]
      · have hHead : (((rk, dh) == (rkStar, dh0))) = false := by
          rw [beq_eq_false_iff_ne]
          intro h; exact (beq_eq_false_iff_ne.mp hEqF) (Prod.mk.inj h).1
        simp [List.find?, hHead]
theorem RelProbUpToBad.bind_const_left {β α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) {m5 m6 : ProbComp α}
    (h : RelProbUpToBad R bad m5 m6) :
    RelProbUpToBad R bad (mx >>= fun _ => m5) m6 := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_const]
    exact h.1 w5 w6 hw5 hw6 hle
  · rw [probExpect_bind, probExpect_const]
    exact h.2 w6 w5 hw6 hle
theorem RelProbUpToBad.map_left_of_support {α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp α) (g : α → α)
    (h : ∀ y ∈ support mx, R (g y) y) :
    RelProbUpToBad R bad (mx >>= fun y => pure (g y)) mx := by
  refine ⟨fun w5 w6 _ _ hle => ?_, fun w6 w5 _ hle => ?_⟩
  · rw [probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun y hy => by
      simp only [probExpect_pure]
      exact hle (g y) y (h y hy))
  · rw [probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun y hy => by
      simp only [probExpect_pure]
      exact hle (g y) y (h y hy))
theorem pqxdhAuthImpl_withRootRoCache {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (b0 : AuthState S) :
    (pqxdhAuthImpl true true S P q).run { b0 with rootRoCache := c } =
      ((pqxdhAuthImpl true true S P q).run b0 >>= fun x =>
        pure (x.1, { x.2 with rootRoCache := c })) := by
  cases q with
  | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
  | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
  | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
  | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
  | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
  | _ =>
    unfold pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, 
      pure_bind]
    repeat (first
      | rfl
      | (split; all_goals (try simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]))
      | (refine congrArg (Bind.bind _) (funext fun _ => ?_)))
theorem authCkOtherStep_withRkAuth {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (s6 : AuthHybridStateFixed S) :
    authCkOtherStep S P q (withRkAuth idx rkStar c s6) = (authCkOtherStep S P q s6 >>= fun x =>
        pure (x.1, withRkAuth idx rkStar c x.2)) := by
  unfold authCkOtherStep withRkAuth; dsimp only
  split; · simp
  rw [pqxdhAuthImpl_withRootRoCache P q hOther c s6.toAuthHybridState.base, bind_assoc, bind_assoc]
  refine congrArg (Bind.bind ((pqxdhAuthImpl true true S P q).run s6.toAuthHybridState.base))
    (funext fun ⟨resp, base'⟩ => ?_)
  simp only [pure_bind]
theorem pqxdhAuthImpl_other_preserves {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q) (st : AuthState S) :
    ∀ y ∈ support ((pqxdhAuthImpl true true S P q).run st), y.2.usedSendSessions =
        st.usedSendSessions ∧
      y.2.seenKyberBaseKeys = st.seenKyberBaseKeys ∧
      (∀ p ∈ st.spkBundles, p ∈ y.2.spkBundles) ∧
      (∀ ik ∈ st.principals.map (fun (_, e) => e.ikAPk),
        ik ∈ y.2.principals.map (fun (_, e) => e.ikAPk)) ∧
      ((∀ p ∈ st.spkBundles, p.2.spkSk.length = 32 ∧ p.2.spkPk = P.x25519Base p.2.spkSk) →
        ∀ p ∈ y.2.spkBundles, p.2.spkSk.length = 32 ∧ p.2.spkPk = P.x25519Base p.2.spkSk) := by
  cases q with
  | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
  | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
  | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
  | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
  | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
  | initPrin u =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨sec0, _, secSign, _, rfl⟩
      exact ⟨rfl, rfl, fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, fun h => h⟩
  | corruptIK u =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨rfl, rfl, fun _ h => h, fun ik hik => ?_, fun h => h⟩
      dsimp only; rcases List.mem_map.mp hik with ⟨⟨pIdx, pEntry⟩, hpMem, rfl⟩; rw [List.mem_map]
      refine ⟨if pIdx == u.val then (pIdx, { pEntry with corrupted := true }) else (pIdx, pEntry),
          ?_, by split <;> rfl⟩
      rw [List.mem_map]
      exact ⟨(pIdx, pEntry), hpMem, rfl⟩
  | genSPK u j =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · split at hy
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨spkSk, hSpkSk, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        refine ⟨rfl, rfl, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, fun hWf p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨length_of_mem_support_sampleScalar32_coll hSpkSk, rfl⟩
        · exact hWf p hp'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
  | genOPK u j o =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨opkSk, _, rfl⟩; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
  | registerKey sk =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
  | roQuery secrets =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, roCache'⟩, _, rfl⟩; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h =>
        h⟩
  | revealDhSecrets =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      ] at hy
    subst hy; exact ⟨rfl, rfl, fun _ h => h, fun _ h => h, fun h => h⟩
theorem authCkOtherStep_preserves_agree {S : Setup} (P : Primitives)
    (rkStar : Bytes) (idx : Nat) (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S)
    (hNoRk6 : cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false)
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hFilter : filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hCacheInv : ∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s)
    (hUniq : ∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2) :
    ∀ y ∈ support (authCkOtherStep S P q s6),
      AgreeOffRkAuth P rkStar idx (withRkAuth idx rkStar c5 y.2) y.2 := by
  intro y hy
  have hCacheEq := authCkOtherStep_preserves_rootRoCache P q hOther s6 y hy
  unfold authCkOtherStep at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ⟨c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩; dsimp only at hCacheEq
  obtain ⟨hUsedSend, hUsedKyber, hSpkSub, hPrinSub, hSpkWf⟩ :=
    pqxdhAuthImpl_other_preserves P q hOther s6.toAuthHybridState.base (resp, base') hbase
  refine ⟨c5, rfl, ?_, ?_, ?_, ?_, ?_, hUniq⟩
  · rw [hCacheEq]; exact hNoRk6
  · intro hNotFired
    have hFiredEq : authSlotFired S idx
        { s6 with toAuthHybridState := { s6.toAuthHybridState with base := base' } } =
        authSlotFired S idx s6 := by
      unfold authSlotFired; dsimp only; rw [hUsedSend]
    rw [hFiredEq] at hNotFired
    rw [hCacheEq]
    exact hSlot hNotFired
  · rw [hCacheEq]; exact hFilter
  · refine ⟨hSpkWf hWf.spk_wf, fun s hs => ?_⟩
    have hs0 := hWf.ideal_wf s hs
    dsimp only; rw [hUsedSend]; exact ⟨hs0.1, hs0.2.1, hPrinSub _ hs0.2.2.1, hs0.2.2.2⟩
  · intro s hs hSlotIdx
    exact (hCacheInv s hs hSlotIdx).preserved_of_find?_eq
      (fun _ => rfl) hSpkSub (by rw [hUsedKyber]; exact fun _ h => h)
theorem relProbUpToBad_authCkOtherStep {S : Setup} (P : Primitives)
    (rkStar : Bytes) (idx : Nat) (q : AuthQuery S)
    (s5 s6 : AuthHybridStateFixed S) (hAg : AgreeOffRkAuth P rkStar idx s5 s6)
    (hNotSendOPK : ∀ u i bundle m0 m1, q ≠ .sendOPK u i bundle m0 m1)
    (hNotSendNoOPK : ∀ u i bundle m0 m1, q ≠ .sendNoOPK u i bundle m0 m1)
    (hNotRecvOPK : ∀ k j o msg, q ≠ .recvOPK k j o msg)
    (hNotRecvNoOPK : ∀ k j l msg, q ≠ .recvNoOPK k j l msg) :
    RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuth P rkStar idx y5.2 y6.2)
      (fun y6 => cacheHasRk rkStar y6.2.toAuthHybridState.base.rootRoCache)
      (authCkOtherStep S P q s5)
      (authCkOtherStep S P q s6) := by
  rcases hAg with ⟨c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩
  by_cases hRo : ∃ rk dh, q = .roRootQuery rk dh
  · rcases hRo with ⟨rk, dh, rfl⟩
    rw [authCkOtherStep_roRootQuery_eq, authCkOtherStep_roRootQuery_eq]
    by_cases hWon : s6.toAuthHybridState.base.hasWonAuth = true
    · rw [withRkAuth_hasWonAuth, ite_eq_left hWon, ite_eq_left hWon]
      exact RelProbUpToBad.of_pure ⟨rfl, c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩
    rw [withRkAuth_hasWonAuth, ite_eq_right hWon, ite_eq_right hWon]
    dsimp only [withRkAuth]
    refine RelProbUpToBad.bind_rel (R1 := fun y5 y6 => y5.1 = y6.1 ∧ filterOutRk rkStar y5.2 = y6.2
        ∧
        cacheHasRk rkStar y6.2 = false ∧
        (c5 = s6.toAuthHybridState.base.rootRoCache → y5.2 = y6.2) ∧
        (∀ dh0, y5.2.find? (fun (inp, _) => inp == (rkStar, dh0)) =
          c5.find? (fun (inp, _) => inp == (rkStar, dh0))))
      (bad1 := fun y6 => cacheHasRk rkStar y6.2)
      (relProbUpToBad_evalRootKdfOrRo_ext P rkStar rk dh c5
        s6.toAuthHybridState.base.rootRoCache hFilter hNoRk6)
      (fun x6 hBad y6 hy6 => by
        simp only [support_pure, Set.mem_singleton_iff] at hy6
        subst hy6; exact hBad)
      (fun y5 y6 ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
    apply RelProbUpToBad.of_pure
    refine ⟨by rw [hOut], y5.2, rfl, hNoRk6', fun hNotFired => hEqImp (hSlot hNotFired),
      hFilter', ⟨hWf.spk_wf, hWf.ideal_wf⟩, fun s hs hSlotIdx => ?_, hUniq⟩
    exact (hCacheInv s hs hSlotIdx).preserved_of_find?_eq hFindEq (fun _ h => h) (fun _ h => h)
  · have hOther : IsAuthOtherNonRoRoot q :=
      ⟨hNotSendOPK, hNotSendNoOPK, hNotRecvOPK, hNotRecvNoOPK, fun rk dh h => hRo ⟨rk, dh, h⟩⟩
    rw [authCkOtherStep_withRkAuth P idx rkStar q hOther c5 s6]
    exact RelProbUpToBad.map_left_of_support (authCkOtherStep S P q s6)
      (fun y => (y.1, withRkAuth idx rkStar c5 y.2))
      (fun y hy => ⟨rfl, authCkOtherStep_preserves_agree P rkStar idx q hOther c5 s6
        hNoRk6 hSlot hFilter hWf hCacheInv hUniq y hy⟩)
theorem peerPrincipal_isSome_of_isIdealSend {peerPrincipal? : Option (Nat × PrincipalEntry)}
    {b1 b2 : Bool}
    (hIdeal : ((match peerPrincipal? with | some (_, pEntry) => !pEntry.corrupted | none => false)
        ||
      (peerPrincipal?.isSome && b1 && b2)) = true) :
    peerPrincipal?.isSome = true := by
  cases peerPrincipal? <;> simp_all
theorem authSlotFired_false_of_not_contains_sid {S : Setup} {idx : Nat} {sid : SessionId S}
    {hst : AuthHybridStateFixed S}
    (hSendSid : sendSlotIndex? sid = some idx)
    (hNotUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = false) :
    authSlotFired S idx hst = false := by
  by_contra hFired
  have hFiredT : authSlotFired S idx hst = true := Bool.eq_true_of_not_eq_false hFired
  have hContains := contains_sid_of_authSlotFired hFiredT hSendSid
  rw [hContains] at hNotUsed
  cases hNotUsed
theorem finishAuthHybridSend_preserves_agree_of_ne_or_not_ideal {S : Setup}
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (rkStar : Bytes) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ss kemCt ephASk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (c5 c5' c6' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S)
    (hSendSid : sendSlotIndex? sid = some (sessionSlotIndex sid))
    (hIkMem : uEntry.ikAPk ∈ s6.toAuthHybridState.base.principals.map (fun (_, e) => e.ikAPk))
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hCacheInv : ∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s)
    (hUniq : ∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2)
    (hNeOrNotIdeal : (sessionSlotIndex sid == idx) = false ∨ (isFreshPeer || (peerPrincipal?.isSome
        &&
        checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
            s6.toAuthHybridState.base.spkBundles bundle &&
        (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
          s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries bundle).2.2)) =
              false)
    (hFilter' : filterOutRk rkStar c5' = c6')
    (hNoRk6' : cacheHasRk rkStar c6' = false)
    (hEqImp : c5 = s6.toAuthHybridState.base.rootRoCache → c5' = c6')
    (hFindEq : ∀ dh0, c5'.find? (fun (inp, _) => inp == (rkStar, dh0)) =
      c5.find? (fun (inp, _) => inp == (rkStar, dh0))) :
    let r5 := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk (P.x25519Base ekASk) ss kemCt ephASk (P.x25519Base ephASk) drKey rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' c5'
      (withRkAuth idx rkStar c5 s6).toAuthHybridState
    let r6 := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk (P.x25519Base ekASk) ss kemCt ephASk (P.x25519Base ephASk) drKey rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' c6'
      s6.toAuthHybridState
    r5.1 = r6.1 ∧
    AgreeOffRkAuth P rkStar idx { toAuthHybridState := r5.2, recvCount := s6.recvCount }
      { toAuthHybridState := r6.2, recvCount := s6.recvCount } := by
  dsimp only
  refine ⟨rfl, c5', ?_, hNoRk6', ?_, hFilter', ?_, ?_, ?_⟩
  · unfold finishAuthHybridSend withRkAuth
    dsimp only; rcases hNeOrNotIdeal with hNe | hNotIdeal
    · cases hIC : (isFreshPeer || (peerPrincipal?.isSome &&
          checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
              s6.toAuthHybridState.base.spkBundles bundle &&
          (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
            s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries bundle).2.2))
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte, List.map_cons, setSlotRkIdealSession, hNe, Bool.false_eq_true]
    · simp only [hNotIdeal, Bool.false_eq_true, ↓reduceIte]
  · intro hNotFired'
    apply hEqImp (hSlot _)
    unfold authSlotFired at hNotFired' ⊢; dsimp only [finishAuthHybridSend] at hNotFired'
    split at hNotFired'
    · rename_i hLt
      simp only [hLt, ↓reduceIte, List.any_cons, Bool.or_eq_false_iff] at hNotFired' ⊢
      exact hNotFired'.2
    · rename_i hGe
      simp only [hGe, ↓reduceIte] at hNotFired' ⊢
      exact hNotFired'
  · refine ⟨hWf.spk_wf, fun s hs => ?_⟩
    dsimp only [finishAuthHybridSend] at hs ⊢
    cases hIC : (isFreshPeer || (peerPrincipal?.isSome &&
        checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
            s6.toAuthHybridState.base.spkBundles bundle &&
        (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
          s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries bundle).2.2))
    · simp only [hIC, Bool.false_eq_true, ↓reduceIte] at hs
      have hs0 := hWf.ideal_wf s hs
      simp only [List.contains_cons, hs0.1, Bool.or_true, true_and]
      exact hs0.2
    · simp only [hIC, ↓reduceIte] at hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · simp only [List.contains_cons, beq_self_eq_true, Bool.true_or, true_and]
        exact ⟨hSendSid, hIkMem, hP.canon_base ekASk⟩
      · have hs0 := hWf.ideal_wf s hs'
        simp only [List.contains_cons, hs0.1, Bool.or_true, true_and]
        exact hs0.2
  · intro s hs hSlotIdx
    dsimp only [finishAuthHybridSend] at hs
    have hsMem : s ∈ s6.toAuthHybridState.idealSessions := by
      rcases hNeOrNotIdeal with hNe | hNotIdeal
      · cases hIC : (isFreshPeer || (peerPrincipal?.isSome &&
            checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
                s6.toAuthHybridState.base.spkBundles bundle &&
            (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
              s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries
                  bundle).2.2))
        · simp only [hIC, Bool.false_eq_true, ↓reduceIte] at hs
          exact hs
        · simp only [hIC, ↓reduceIte] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · exfalso; exact (beq_eq_false_iff_ne.mp hNe) hSlotIdx
          · exact hs'
      · simp only [hNotIdeal, Bool.false_eq_true, ↓reduceIte] at hs
        exact hs
    exact (hCacheInv s hsMem hSlotIdx).preserved_of_find?_eq hFindEq (fun _ h => h) (fun _ h => h)
  · intro s1 hs1 s2 hs2 hSlot1 hSlot2
    dsimp only [finishAuthHybridSend] at hs1 hs2
    have hs1Mem : s1 ∈ s6.toAuthHybridState.idealSessions := by
      rcases hNeOrNotIdeal with hNe | hNotIdeal
      · cases hIC : (isFreshPeer || (peerPrincipal?.isSome &&
            checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
                s6.toAuthHybridState.base.spkBundles bundle &&
            (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
              s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries
                  bundle).2.2))
        · simp only [hIC, Bool.false_eq_true, ↓reduceIte] at hs1; exact hs1
        · simp only [hIC, ↓reduceIte] at hs1
          rcases List.mem_cons.mp hs1 with rfl | hs1'
          · exfalso; exact (beq_eq_false_iff_ne.mp hNe) hSlot1
          · exact hs1'
      · simp only [hNotIdeal, Bool.false_eq_true, ↓reduceIte] at hs1; exact hs1
    have hs2Mem : s2 ∈ s6.toAuthHybridState.idealSessions := by
      rcases hNeOrNotIdeal with hNe | hNotIdeal
      · cases hIC : (isFreshPeer || (peerPrincipal?.isSome &&
            checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
                s6.toAuthHybridState.base.spkBundles bundle &&
            (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
              s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries
                  bundle).2.2))
        · simp only [hIC, Bool.false_eq_true, ↓reduceIte] at hs2; exact hs2
        · simp only [hIC, ↓reduceIte] at hs2
          rcases List.mem_cons.mp hs2 with rfl | hs2'
          · exfalso; exact (beq_eq_false_iff_ne.mp hNe) hSlot2
          · exact hs2'
      · simp only [hNotIdeal, Bool.false_eq_true, ↓reduceIte] at hs2; exact hs2
    exact hUniq s1 hs1Mem s2 hs2Mem hSlot1 hSlot2
theorem finishAuthHybridSend_preserves_agree_of_slot_eq {S : Setup}
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (rkStar rk : Bytes) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ss kemCt ephASk ck pk : Bytes)
    (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S)
    (hSendSid : sendSlotIndex? sid = some (sessionSlotIndex sid))
    (hSlotEq : sessionSlotIndex sid = idx)
    (hNotUsed : s6.toAuthHybridState.base.usedSendSessions.contains sid = false)
    (hIkMem : uEntry.ikAPk ∈ s6.toAuthHybridState.base.principals.map (fun (_, e) => e.ikAPk))
    (hNoRk6 : cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false)
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hFilter : filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hPeerSome : peerPrincipal?.isSome = true)
    (hIdeal : (isFreshPeer || (peerPrincipal?.isSome &&
        checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
            s6.toAuthHybridState.base.spkBundles bundle &&
        (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
          s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries bundle).2.2)) =
              true) :
    let drKey5 : DRKey := { rootKey := rkStar, chainKey := ck, pqrKey := pk }
    let drKey6 : DRKey := { rootKey := rk, chainKey := ck, pqrKey := pk }
    let c5' := ((rkStar, P.x25519 ephASk bundle.spkB), (rk1, ck1_0)) :: c5
    let r5 := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk (P.x25519Base ekASk) ss kemCt ephASk (P.x25519Base ephASk) drKey5 rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain s6.toAuthHybridState.base.roCache c5'
      (withRkAuth idx rkStar c5 s6).toAuthHybridState
    let r6 := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk (P.x25519Base ekASk) ss kemCt ephASk (P.x25519Base ephASk) drKey6 rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain s6.toAuthHybridState.base.roCache
      s6.toAuthHybridState.base.rootRoCache
      s6.toAuthHybridState
    r5.1 = r6.1 ∧
    AgreeOffRkAuth P rkStar idx { toAuthHybridState := r5.2, recvCount := s6.recvCount }
      { toAuthHybridState := r6.2, recvCount := s6.recvCount } := by
  dsimp only
  have hSendSidIdx : sendSlotIndex? sid = some idx := hSlotEq ▸ hSendSid
  have hNotFired : authSlotFired S idx s6 = false :=
    authSlotFired_false_of_not_contains_sid hSendSidIdx hNotUsed
  have hc5Eq : c5 = s6.toAuthHybridState.base.rootRoCache := hSlot hNotFired
  have hNoRk5 : cacheHasRk rkStar c5 = false := hc5Eq ▸ hNoRk6
  have hNoExistingAtSlot : ∀ s ∈ s6.toAuthHybridState.idealSessions, sessionSlotIndex s.sid ≠ idx
      := by
    intro s hs hEq
    have hFired := authSlotFired_of_idealSession_slot_eq hWf hs hEq
    rw [hFired] at hNotFired
    cases hNotFired
  refine ⟨?_, ((rkStar, P.x25519 ephASk bundle.spkB), (rk1, ck1_0)) :: c5,
    ?_, hNoRk6, ?_, ?_, ?_, ?_, ?_⟩
  · unfold finishAuthHybridSend
    dsimp only; simp only [hPeerSome, ↓reduceIte]
  · unfold finishAuthHybridSend withRkAuth
    dsimp only
    have hSlotBeq : (sessionSlotIndex sid == idx) = true := beq_iff_eq.mpr hSlotEq
    simp only [hIdeal, ↓reduceIte, List.map_cons, setSlotRkIdealSession, hSlotBeq]
  · intro hNotFired'
    exfalso
    have hLt : idx < S.N_send_tot := sendSlotIndex?_lt hSendSidIdx
    unfold authSlotFired at hNotFired'; dsimp only [finishAuthHybridSend] at hNotFired'
    simp only [hLt, ↓reduceIte, List.any_cons, hSendSidIdx, beq_self_eq_true,
      Bool.true_or] at hNotFired'
    cases hNotFired'
  · unfold filterOutRk
    simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact hFilter
  · refine ⟨hWf.spk_wf, fun s hs => ?_⟩
    dsimp only [finishAuthHybridSend] at hs ⊢; simp only [hIdeal, ↓reduceIte] at hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · simp only [List.contains_cons, beq_self_eq_true, Bool.true_or, true_and]
      exact ⟨hSendSid, hIkMem, hP.canon_base ekASk⟩
    · have hs0 := hWf.ideal_wf s hs'
      simp only [List.contains_cons, hs0.1, Bool.or_true, true_and]
      exact hs0.2
  · intro s hs hSlotIdx
    dsimp only [finishAuthHybridSend] at hs; simp only [hIdeal, ↓reduceIte] at hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · refine Or.inl ⟨ephASk, rfl, fun dh => ?_⟩
      exact find?_cons_rk_self_of_cacheHasRk_false rkStar (P.x25519 ephASk bundle.spkB)
        (rk1, ck1_0) c5 hNoRk5 dh
    · exfalso; exact hNoExistingAtSlot s hs' hSlotIdx
  · intro s1 hs1 s2 hs2 hSlot1 hSlot2
    dsimp only [finishAuthHybridSend] at hs1 hs2; simp only [hIdeal, ↓reduceIte] at hs1 hs2
    rcases List.mem_cons.mp hs1 with rfl | hs1'
    · rcases List.mem_cons.mp hs2 with rfl | hs2'
      · rfl
      · exfalso; exact hNoExistingAtSlot s2 hs2' hSlot2
    · exfalso; exact hNoExistingAtSlot s1 hs1' hSlot1
theorem relProbUpToBad_authRkSendWith {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (rkStar : Bytes) (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hSendSid : sendSlotIndex? sid = some (sessionSlotIndex sid))
    (s5 s6 : AuthHybridStateFixed S) (hAg : AgreeOffRkAuth P rkStar idx s5 s6) :
    RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuth P rkStar idx y5.2 y6.2)
      (fun y6 => cacheHasRk rkStar y6.2.toAuthHybridState.base.rootRoCache)
      (authRkSendWith S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        (fun s => decide (s < idx)) sid u bundle m0 m1 s5)
      (authRkSendWith S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) sid u bundle m0 m1 s6) := by
  have hAg0 := hAg
  rcases hAg with ⟨c5, rfl, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩; unfold authRkSendWith
  dsimp only [withRkAuth]
  by_cases hWon : s6.toAuthHybridState.base.hasWonAuth = true
  · rw [ite_eq_left hWon, ite_eq_left hWon]
    exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
  rw [ite_eq_right hWon, ite_eq_right hWon]
  split
  · exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
  · split
    · exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
    · rename_i hNotUsedProp
      have hNotUsed : s6.toAuthHybridState.base.usedSendSessions.contains sid = false :=
        Bool.eq_false_iff.mpr hNotUsedProp
      cases hFindU : s6.toAuthHybridState.base.principals.find? (fun (i, _) => i == u.val) with
      | none => exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
      | some pU =>
        rcases pU with ⟨uIdx, uEntry⟩
        have hIkMem : uEntry.ikAPk ∈ s6.toAuthHybridState.base.principals.map (fun (_, e) =>
            e.ikAPk) := by
          rw [List.mem_map]
          exact ⟨(uIdx, uEntry), List.mem_of_find?_eq_some hFindU, rfl⟩
        dsimp only
        split
        · exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
        · split
          · exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
          · refine RelProbUpToBad.bind_same sampleScalar32 (fun ekASk => ?_)
            refine RelProbUpToBad.bind_same sampleCoins32 (fun kemCoins => ?_)
            refine RelProbUpToBad.bind_same sampleScalar32 (fun ephASk => ?_)
            refine RelProbUpToBad.bind_same sampleCoins32 (fun spqrCoins => ?_)
            split
            · exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
            · cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
              | some pKem =>
                rcases pKem with ⟨ss, kemCt⟩; dsimp only
                split
                · rename_i hIdeal
                  refine RelProbUpToBad.bind_same sampleBytes32 (fun ck => ?_)
                  refine RelProbUpToBad.bind_same sampleBytes32 (fun pk => ?_)
                  cases P.spqrInitSend pk spqrCoins with
                  | none => exact RelProbUpToBad.of_pure ⟨rfl, hAg0⟩
                  | some pSpqr =>
                    rcases pSpqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    by_cases hLt : sessionSlotIndex sid < idx
                    · have hNe : (sessionSlotIndex sid == idx) = false :=
                        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hLt)
                      have hLt1 : sessionSlotIndex sid < idx + 1 := Nat.lt_succ_of_lt hLt
                      simp only [hNe, Bool.false_eq_true, ↓reduceIte]
                      refine RelProbUpToBad.bind_same sampleBytes32 (fun rk => ?_)
                      unfold finishAuthSendAfterRk; dsimp only
                      simp only [decide_eq_true_eq.mpr hLt, decide_eq_true_eq.mpr hLt1,
                        ↓reduceIte, pure_bind]
                      refine RelProbUpToBad.bind_same sampleBytes32 (fun r => ?_)
                      refine RelProbUpToBad.bind_same sampleBytes32 (fun c => ?_)
                      apply RelProbUpToBad.of_pure
                      exact finishAuthHybridSend_preserves_agree_of_ne_or_not_ideal P hP rkStar idx
                        sid uEntry _ _ bundle m0 m1 ekASk ss kemCt ephASk
                        { rootKey := rk, chainKey := ck, pqrKey := pk } r c
                        (P.chainKdfSeed c) (P.chainKdfNext c) spqrSalt? pqRatchetMsg _ _ _ _
                        s6.toAuthHybridState.base.roCache c5 c5
                        s6.toAuthHybridState.base.rootRoCache s6 hSendSid hIkMem hSlot hWf
                        hCacheInv hUniq (Or.inl hNe) hFilter hNoRk6 (fun h => h) (fun _ => rfl)
                    · by_cases hEqSlot : sessionSlotIndex sid = idx
                      · have hBeq : (sessionSlotIndex sid == idx) = true := beq_iff_eq.mpr hEqSlot
                        have hLt1 : sessionSlotIndex sid < idx + 1 := by omega
                        have hSendSidIdx : sendSlotIndex? sid = some idx := hEqSlot ▸ hSendSid
                        have hNotFired : authSlotFired S idx s6 = false :=
                          authSlotFired_false_of_not_contains_sid hSendSidIdx hNotUsed
                        have hc5Eq : c5 = s6.toAuthHybridState.base.rootRoCache := hSlot hNotFired
                        have hNoRk5 : cacheHasRk rkStar c5 = false := hc5Eq ▸ hNoRk6
                        have hFindNone : c5.find? (fun (inp, _) =>
                            inp == (rkStar, P.x25519 ephASk bundle.spkB)) = none :=
                          find?_rk_eq_none_of_cacheHasRk_false rkStar (P.x25519 ephASk bundle.spkB)
                              c5 hNoRk5
                        simp only [hBeq, ↓reduceIte, pure_bind]
                        refine RelProbUpToBad.bind_right sampleBytes32 (fun rk => ?_)
                        unfold finishAuthSendAfterRk evalRootKdfOrRo; dsimp only
                        simp only [decide_eq_false_iff_not.mpr hLt, decide_eq_true_eq.mpr hLt1,
                          Bool.false_eq_true, Bool.not_true, ↓reduceIte, hFindNone,
                          bind_assoc, pure_bind]
                        refine RelProbUpToBad.bind_same sampleBytes32 (fun r => ?_)
                        refine RelProbUpToBad.bind_same sampleBytes32 (fun c => ?_)
                        apply RelProbUpToBad.of_pure
                        exact finishAuthHybridSend_preserves_agree_of_slot_eq P hP rkStar rk idx
                          sid uEntry _ _ bundle m0 m1 ekASk ss kemCt ephASk ck pk r c
                          (P.chainKdfSeed c) (P.chainKdfNext c) spqrSalt? pqRatchetMsg _ _ _ _
                          c5 s6 hSendSid hEqSlot hNotUsed hIkMem hNoRk6 hSlot hFilter hWf
                          (peerPrincipal_isSome_of_isIdealSend hIdeal) hIdeal
                      · have hNe : (sessionSlotIndex sid == idx) = false :=
                          beq_eq_false_iff_ne.mpr hEqSlot
                        have hNotLt1 : ¬ (sessionSlotIndex sid < idx + 1) := by omega
                        simp only [hNe, Bool.false_eq_true, ↓reduceIte]
                        refine RelProbUpToBad.bind_same sampleBytes32 (fun rk => ?_)
                        unfold finishAuthSendAfterRk; dsimp only
                        simp only [decide_eq_false_iff_not.mpr hLt, decide_eq_false_iff_not.mpr
                            hNotLt1,
                          Bool.false_eq_true, ↓reduceIte]
                        refine RelProbUpToBad.bind_rel (relProbUpToBad_evalRootKdfOrRo_ext P rkStar
                            rk
                            (P.x25519 ephASk bundle.spkB) c5 s6.toAuthHybridState.base.rootRoCache
                            hFilter hNoRk6)
                          (fun x6 hBad y6 hy6 => by
                            simp only [support_pure, Set.mem_singleton_iff] at hy6
                            subst hy6; exact hBad)
                          (fun y5_ro y6_ro ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
                        rcases y5_ro with ⟨⟨r5_rk1, r5_ck1⟩, c5'⟩
                        rcases y6_ro with ⟨⟨r6_rk1, r6_ck1⟩, c6'⟩
                        dsimp only at hOut hFilter' hNoRk6' hEqImp hFindEq
                        rcases Prod.mk.inj hOut with ⟨rfl, rfl⟩; apply RelProbUpToBad.of_pure
                        exact finishAuthHybridSend_preserves_agree_of_ne_or_not_ideal P hP rkStar
                            idx
                          sid uEntry _ _ bundle m0 m1 ekASk ss kemCt ephASk
                          { rootKey := rk, chainKey := ck, pqrKey := pk } r5_rk1 r5_ck1
                          (P.chainKdfSeed r5_ck1) (P.chainKdfNext r5_ck1) spqrSalt? pqRatchetMsg _
                              _ _ _
                          s6.toAuthHybridState.base.roCache c5 c5' c6' s6 hSendSid hIkMem hSlot hWf
                          hCacheInv hUniq (Or.inl hNe) hFilter' hNoRk6' hEqImp hFindEq
                · rename_i hNotIdealProp
                  have hNotIdeal : ((match findHonestPrincipal P
                      s6.toAuthHybridState.base.principals bundle.ikB with
                      | some (_, pEntry) => !pEntry.corrupted | none => false) ||
                    ((findHonestPrincipal P s6.toAuthHybridState.base.principals bundle.ikB).isSome
                        &&
                      checkBundleSpkHonIdeal P s6.toAuthHybridState.base.principals
                          s6.toAuthHybridState.base.spkBundles bundle &&
                      (checkBundleProvenanceExact P s6.toAuthHybridState.base.principals
                        s6.toAuthHybridState.base.spkBundles s6.toAuthHybridState.base.opkEntries
                            bundle).2.2)) = false :=
                    Bool.eq_false_iff.mpr hNotIdealProp
                  refine RelProbUpToBad.bind_same (evalHkdfOrRo true P
                      s6.toAuthHybridState.base.roCache _)
                    (fun ⟨drKey, roCache'⟩ => ?_)
                  dsimp only
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none =>
                    dsimp only; exact RelProbUpToBad.bind_const_left _
                      (RelProbUpToBad.bind_const_right _ (RelProbUpToBad.of_pure ⟨rfl, hAg0⟩))
                  | some pSpqr =>
                    rcases pSpqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    refine RelProbUpToBad.bind_rel
                      (relProbUpToBad_evalRootKdfOrRo_ext P rkStar drKey.rootKey
                        (P.x25519 ephASk bundle.spkB) c5 s6.toAuthHybridState.base.rootRoCache
                        hFilter hNoRk6)
                      (fun x6 hBad y6 hy6 => by
                        simp only [support_pure, Set.mem_singleton_iff] at hy6
                        subst hy6; exact hBad)
                      (fun y5_ro y6_ro ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
                    rcases y5_ro with ⟨⟨r5_rk1, r5_ck1⟩, c5'⟩; rcases y6_ro with ⟨⟨r6_rk1, r6_ck1⟩,
                        c6'⟩
                    dsimp only at hOut hFilter' hNoRk6' hEqImp hFindEq
                    rcases Prod.mk.inj hOut with ⟨rfl, rfl⟩; apply RelProbUpToBad.of_pure
                    exact finishAuthHybridSend_preserves_agree_of_ne_or_not_ideal P hP rkStar idx
                      sid uEntry _ _ bundle m0 m1 ekASk ss kemCt ephASk
                      drKey r5_rk1 r5_ck1
                      (P.chainKdfSeed r5_ck1) (P.chainKdfNext r5_ck1) spqrSalt? pqRatchetMsg _ _ _ _
                      roCache' c5 c5' c6' s6 hSendSid hIkMem hSlot hWf
                      hCacheInv hUniq (Or.inr hNotIdeal) hFilter' hNoRk6' hEqImp hFindEq
abbrev AuthRkTrackedState (S : Setup) :=
  AuthHybridStateFixed S × List ((Bytes × Bytes) × (Bytes × Bytes))
def badRkTracked {S : Setup} (rkStar : Bytes) (st : AuthRkTrackedState S) : Bool :=
  cacheHasRk rkStar st.1.toAuthHybridState.base.rootRoCache || cacheHasRk rkStar st.2
def AgreeOffRkAuthTracked {S : Setup} (P : Primitives) (rkStar : Bytes) (idx : Nat)
    (s5 s6 : AuthRkTrackedState S) : Prop :=
  AgreeOffRkAuth P rkStar idx s5.1 s6.1 ∧ cacheHasRk rkStar s6.2 = false
theorem AgreeOffRkAuthTracked.not_bad {S : Setup} {P : Primitives} {rkStar : Bytes} {idx : Nat}
    {s5 s6 : AuthRkTrackedState S} (h : AgreeOffRkAuthTracked P rkStar idx s5 s6) :
    badRkTracked rkStar s6 = false := by
  unfold badRkTracked; rw [h.1.noRk6, h.2]; rfl
def newRootRoEntry (c' c : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (extra : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    List ((Bytes × Bytes) × (Bytes × Bytes)) :=
  if c'.length > c.length then
    match c' with
    | e :: _ => e :: extra
    | [] => extra
  else
    extra
theorem evalRootKdfOrRo_StepCache {P : Primitives} {rk dh : Bytes}
    {c : List ((Bytes × Bytes) × (Bytes × Bytes))}
    {y : (Bytes × Bytes) × List ((Bytes × Bytes) × (Bytes × Bytes))}
    (hy : y ∈ support (evalRootKdfOrRo true P c rk dh)) :
    y.2 = c ∨ ∃ e, y.2 = e :: c := by
  unfold evalRootKdfOrRo at hy; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact Or.inl rfl
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨rk1, _, ck1, _, rfl⟩; exact Or.inr ⟨((rk, dh), (rk1, ck1)), rfl⟩
theorem newRootRoEntry_cacheHasRk (rkStar : Bytes)
    (c' c extra : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hc : c' = c ∨ ∃ e, c' = e :: c) :
    (cacheHasRk rkStar c || cacheHasRk rkStar (newRootRoEntry c' c extra)) =
      (cacheHasRk rkStar c' || cacheHasRk rkStar extra) := by
  rcases hc with rfl | ⟨e, rfl⟩
  · unfold newRootRoEntry
    simp
  · unfold newRootRoEntry
    simp only [List.length_cons, gt_iff_lt, Nat.lt_succ_self, ↓reduceIte]
    rcases e with ⟨⟨rk, dh⟩, out⟩; unfold cacheHasRk; simp only [List.any_cons]
    cases (rk == rkStar) <;> cases List.any c (fun x => x.1.1 == rkStar) <;>
      cases List.any extra (fun x => x.1.1 == rkStar) <;> rfl
theorem newRootRoEntry_length (c' c extra : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hc : c' = c ∨ ∃ e, c' = e :: c) :
    c.length + (newRootRoEntry c' c extra).length = c'.length + extra.length := by
  rcases hc with rfl | ⟨e, rfl⟩
  · unfold newRootRoEntry; simp
  · unfold newRootRoEntry
    simp only [List.length_cons, gt_iff_lt, Nat.lt_succ_self, ↓reduceIte]
    omega
def finishAuthRecvRkTracked {S : Setup} (P : Primitives) (msg : PreKeyMsg) (prep : PreparedAuthRecv
    S)
    (drKey : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (recvCount' : Nat)
    (extra : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    AuthResponse × AuthRkTrackedState S :=
  let (resp, hst') := finishAuthRecvRk P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount'
  let mkSeed := P.chainKdfSeed ck1_0
  let res? :=
    match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
    | none => none
    | some (_pqrStB, spqrSalt?) =>
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
      P.aeadDec deriveMessageKeys ad msg.aeadCt
  let extra' :=
    match res? with
    | some _ => extra
    | none => newRootRoEntry rootRoCache' prep.hstDec.base.rootRoCache extra
  (resp, (hst', extra'))
@[simp] theorem finishAuthRecvRkTracked_fst {S : Setup} (P : Primitives) (msg : PreKeyMsg)
    (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (recvCount' : Nat) (extra : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    (finishAuthRecvRkTracked P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount' extra).1 =
      (finishAuthRecvRk P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount').1 := rfl
@[simp] theorem finishAuthRecvRkTracked_snd_fst {S : Setup} (P : Primitives) (msg : PreKeyMsg)
    (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (recvCount' : Nat) (extra : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    (finishAuthRecvRkTracked P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount' extra).2.1
        =
      (finishAuthRecvRk P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount').2 := rfl
theorem checkAndMarkKyberUsed_eq_true (usedTriples : List (Nat × KeyId × KeyId × Bytes))
    (k : Nat) (pqspkId spkId : KeyId) (ekAPk : Bytes)
    (h : (checkAndMarkKyberBaseKeySeen usedTriples k pqspkId spkId ekAPk).1 = true) :
    (k, pqspkId, spkId, ekAPk) ∉ usedTriples ∧
    (checkAndMarkKyberBaseKeySeen usedTriples k pqspkId spkId ekAPk).2 =
      (k, pqspkId, spkId, ekAPk) :: usedTriples := by
  unfold checkAndMarkKyberBaseKeySeen at h ⊢; dsimp only at h ⊢
  split at h
  · contradiction
  · rename_i hNot
    simp only [hNot, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun hm => hNot (List.contains_iff_mem.mpr hm), trivial⟩
theorem mem_spkBundles_of_find?_eq_some (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (k j : Nat) (pIdx : Nat × Nat) (bEntry : SpkBundleEntry)
    (h : spkBundles.find? (fun (idx, _) => idx == (k, j)) = some (pIdx, bEntry)) :
    ((k, j), bEntry) ∈ spkBundles := by
  have hMem := List.mem_of_find?_eq_some h
  have hPred := List.find?_some h
  dsimp only at hPred; rw [beq_iff_eq] at hPred; subst hPred; exact hMem
theorem matchIdealAuthHandshake_eq_true {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S)
    (h : matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr s = true) :
    P.pow8 hdr.ikAPk = P.pow8 s.ikAPk ∧
    P.pow8 spkBPk = P.pow8 s.peerSpkPk ∧
    P.pow8 hdr.ekAPk = P.pow8 s.ekAPk ∧
    pqspkBPk = s.peerPqspkPk := by
  unfold matchIdealAuthHandshake at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.2, h.1.1.2, h.1.2⟩
theorem authSlotFired_false_of_succ_recvCount {S : Setup} (idx : Nat) (s6 s6' :
    AuthHybridStateFixed S)
    (hUsed : s6'.toAuthHybridState.base.usedSendSessions =
        s6.toAuthHybridState.base.usedSendSessions)
    (hRecv : s6.recvCount ≤ s6'.recvCount)
    (hF : authSlotFired S idx s6' = false) :
    authSlotFired S idx s6 = false := by
  unfold authSlotFired at hF ⊢; rw [hUsed] at hF
  split at hF <;> rename_i hlt
  · simp [hlt, hF]
  · simp only [hlt, ↓reduceIte, decide_eq_false_iff_not] at hF ⊢; omega
structure PreparedAuthRecvRel {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (prep5 prep6 : PreparedAuthRecv S) : Prop where
  kEntry_eq : prep5.kEntry = prep6.kEntry
  bEntry_eq : prep5.bEntry = prep6.bEntry
  opkPk?_eq : prep5.opkPk? = prep6.opkPk?
  secrets_eq : prep5.secrets = prep6.secrets
  dhRatchet_eq : prep5.dhRatchet = prep6.dhRatchet
  honest_eq : prep5.isUncorruptedHonestSender = prep6.isUncorruptedHonestSender
  matched_eq : prep5.matchedSess? = prep6.matchedSess?.map (setSlotRkIdealSession idx rkStar)
  sameEph_eq : prep5.sameEph = prep6.sameEph
  ephAPk_len : msg.ephAPk.length = 32
  roCache5_eq : prep5.hstDec.base.roCache = s6.toAuthHybridState.base.roCache
  roCache6_eq : prep6.hstDec.base.roCache = s6.toAuthHybridState.base.roCache
  rootRoCache5_eq : prep5.hstDec.base.rootRoCache = c5
  rootRoCache6_eq : prep6.hstDec.base.rootRoCache = s6.toAuthHybridState.base.rootRoCache
  honest_isSome : prep6.isUncorruptedHonestSender = true →
    (findHonestPrincipal P s6.toAuthHybridState.base.principals msg.hdr.ikAPk).isSome = true
  matched_wf : ∀ s, prep6.matchedSess? = some s → s ∈ s6.toAuthHybridState.idealSessions ∧
    matchIdealAuthHandshake P prep6.kEntry.ikAPk prep6.bEntry.spkPk prep6.opkPk?
      prep6.bEntry.pqspkPk msg.hdr s = true ∧
    prep6.sameEph = (P.pow8 msg.ephAPk == P.pow8 s.ephAPk)
  kyber_wf : ∃ kVal jVal, ((kVal, jVal), prep6.bEntry) ∈ s6.toAuthHybridState.base.spkBundles ∧
    msg.hdr.pqspkId = UInt32.ofNat jVal ∧
    msg.hdr.spkId = UInt32.ofNat jVal ∧
    prep6.dhRatchet = P.x25519 prep6.bEntry.spkSk msg.ephAPk ∧
    (kVal, msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) ∉
        s6.toAuthHybridState.base.seenKyberBaseKeys ∧
    P.isCanonical msg.hdr.ekAPk = true ∧
    (∀ drKey6 rk1 ck1_1 pt roCache' c6',
      (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2.base.seenKyberBaseKeys =
        (kVal, msg.hdr.pqspkId, msg.hdr.spkId, msg.hdr.ekAPk) ::
          s6.toAuthHybridState.base.seenKyberBaseKeys)
  finish_none : prep5.finish none = (.noneResp, prep5.hstDec) ∧
    prep6.finish none = (.noneResp, prep6.hstDec) ∧
    ({ toAuthHybridState := prep5.hstDec, recvCount := s6.recvCount + 1 } : AuthHybridStateFixed S)
        =
      withRkAuth idx rkStar c5 { toAuthHybridState := prep6.hstDec, recvCount := s6.recvCount + 1 }
          ∧
    prep6.hstDec.base = s6.toAuthHybridState.base ∧
    prep6.hstDec.idealSessions = s6.toAuthHybridState.idealSessions
  finish_some : ∀ drKey5 drKey6 rk1 ck1_1 pt roCache' c5' c6', (drKey5 = drKey6 ∨
      (findHonestPrincipal P s6.toAuthHybridState.base.principals msg.hdr.ikAPk).isSome = true) →
    (prep5.finish (some (drKey5, rk1, ck1_1, pt, roCache', c5'))).1 =
      (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).1 ∧
    ({ toAuthHybridState := (prep5.finish (some (drKey5, rk1, ck1_1, pt, roCache', c5'))).2,
       recvCount := s6.recvCount + 1 } : AuthHybridStateFixed S) =
      withRkAuth idx rkStar c5'
        { toAuthHybridState := (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2,
          recvCount := s6.recvCount + 1 } ∧
    (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2.base.rootRoCache = c6' ∧
    (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2.base.spkBundles =
      s6.toAuthHybridState.base.spkBundles ∧
    (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2.base.principals =
      s6.toAuthHybridState.base.principals ∧
    (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2.base.usedSendSessions =
      s6.toAuthHybridState.base.usedSendSessions ∧
    (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache', c6'))).2.idealSessions =
      s6.toAuthHybridState.idealSessions
theorem prepareAuthHybridRecvOPK_rel {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) :
    Option.Rel (PreparedAuthRecvRel P idx rkStar c5 s6 msg)
      (prepareAuthHybridRecvOPK true P k j o msg (withRkAuth idx rkStar c5 s6).toAuthHybridState)
      (prepareAuthHybridRecvOPK true P k j o msg s6.toAuthHybridState) := by
  unfold prepareAuthHybridRecvOPK; dsimp only [withRkAuth]
  split; · exact Option.Rel.none
  split
  · exact Option.Rel.none
  · rename_i hHdr
    have hSpkId : msg.hdr.spkId = UInt32.ofNat j.val := by
      by_contra hne; exact hHdr (by simp [beq_eq_false_iff_ne.mpr hne])
    have hPqspkId : msg.hdr.pqspkId = UInt32.ofNat j.val := by
      by_contra hne; exact hHdr (by simp [beq_eq_false_iff_ne.mpr hne])
    have hEphLen : msg.ephAPk.length = 32 := by
      by_contra hne; exact hHdr (by simp [beq_eq_false_iff_ne.mpr hne])
    split
    · exact Option.Rel.none
    · split
      · exact Option.Rel.none
      · cases hK : s6.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => exact Option.Rel.none
        | some pkEntry =>
          rcases pkEntry with ⟨_, kEntry⟩
          cases hB : s6.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val,
              j.val)) with
          | none => exact Option.Rel.none
          | some pbEntry =>
            rcases pbEntry with ⟨pIdx, bEntry⟩
            cases hO : s6.toAuthHybridState.base.opkEntries.find? (fun (idx, _) => idx == (k.val,
                j.val, o.val)) with
            | none => exact Option.Rel.none
            | some poEntry =>
              rcases poEntry with ⟨_, oEntry⟩; dsimp only
              split
              · exact Option.Rel.none
              · split
                · exact Option.Rel.none
                · rename_i hReplayCanon
                  have hReplayOk : (checkAndMarkKyberBaseKeySeen s6.toAuthHybridState.base.seenKyberBaseKeys
                      k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 = true := by
                    by_contra hne; exact hReplayCanon (by simp [Bool.eq_false_iff.mpr hne])
                  have hCanonEk : P.isCanonical msg.hdr.ekAPk = true := by
                    by_contra hne; exact hReplayCanon (by simp [Bool.eq_false_iff.mpr hne])
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => exact Option.Rel.none
                  | some ss =>
                    dsimp only; apply Option.Rel.some
                    have hFindMap := find?_matchIdealAuthHandshake_map_setSlotRkIdealSession P idx
                        rkStar
                      kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk) bEntry.pqspkPk msg.hdr
                      s6.toAuthHybridState.idealSessions
                    have hKyber := checkAndMarkKyberUsed_eq_true
                      s6.toAuthHybridState.base.seenKyberBaseKeys
                      k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk hReplayOk
                    refine {
                      kEntry_eq := rfl, bEntry_eq := rfl, opkPk?_eq := rfl, secrets_eq := rfl,
                      dhRatchet_eq := rfl, honest_eq := rfl, matched_eq := hFindMap,
                      sameEph_eq := by
                        dsimp only; rw [hFindMap]
                        cases List.find? _ s6.toAuthHybridState.idealSessions <;> simp
                            [setSlotRkIdealSession_ephAPk],
                      ephAPk_len := hEphLen,
                      roCache5_eq := rfl, roCache6_eq := rfl,
                      rootRoCache5_eq := rfl, rootRoCache6_eq := rfl,
                      honest_isSome := by
                        dsimp only
                        cases findHonestPrincipal P s6.toAuthHybridState.base.principals
                            msg.hdr.ikAPk <;> simp,
                      matched_wf := fun s hs => by
                        dsimp only at hs ⊢
                        exact ⟨List.mem_of_find?_eq_some hs, List.find?_some hs, by simp [hs]⟩,
                      kyber_wf := ⟨k.val, j.val,
                        mem_spkBundles_of_find?_eq_some _ k.val j.val pIdx bEntry hB,
                        hPqspkId, hSpkId, rfl, hKyber.1, hCanonEk,
                        fun drKey6 rk1 ck1_1 pt roCache' c6' => by
                          unfold finishAuthHybridRecvOPK; dsimp only
                          cases findHonestPrincipal P s6.toAuthHybridState.base.principals
                              msg.hdr.ikAPk with
                          | none => exact hKyber.2
                          | some p =>
                            rcases p with ⟨_, senderEntry⟩; dsimp only; split <;> exact hKyber.2⟩,
                      finish_none := ⟨rfl, rfl, rfl, rfl, rfl⟩,
                      finish_some := fun drKey5 drKey6 rk1 ck1_1 pt roCache' c5' c6' hDr => by
                        unfold finishAuthHybridRecvOPK; dsimp only
                        cases hF : findHonestPrincipal P s6.toAuthHybridState.base.principals
                            msg.hdr.ikAPk with
                        | none =>
                          rcases hDr with rfl | hSome
                          · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                          · simp [hF] at hSome
                        | some p =>
                          rcases p with ⟨_, senderEntry⟩
                          dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ }
theorem prepareAuthHybridRecvNoOPK_rel {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) :
    Option.Rel (PreparedAuthRecvRel P idx rkStar c5 s6 msg)
      (prepareAuthHybridRecvNoOPK true P k j l msg (withRkAuth idx rkStar c5 s6).toAuthHybridState)
      (prepareAuthHybridRecvNoOPK true P k j l msg s6.toAuthHybridState) := by
  unfold prepareAuthHybridRecvNoOPK; dsimp only [withRkAuth]
  split; · exact Option.Rel.none
  split
  · exact Option.Rel.none
  · rename_i hHdr
    have hSpkId : msg.hdr.spkId = UInt32.ofNat j.val := by
      by_contra hne; exact hHdr (by simp [beq_eq_false_iff_ne.mpr hne])
    have hPqspkId : msg.hdr.pqspkId = UInt32.ofNat j.val := by
      by_contra hne; exact hHdr (by simp [beq_eq_false_iff_ne.mpr hne])
    have hEphLen : msg.ephAPk.length = 32 := by
      by_contra hne; exact hHdr (by simp [beq_eq_false_iff_ne.mpr hne])
    split
    · exact Option.Rel.none
    · split
      · exact Option.Rel.none
      · cases hK : s6.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => exact Option.Rel.none
        | some pkEntry =>
          rcases pkEntry with ⟨_, kEntry⟩
          cases hB : s6.toAuthHybridState.base.spkBundles.find? (fun (idx, _) => idx == (k.val,
              j.val)) with
          | none => exact Option.Rel.none
          | some pbEntry =>
            rcases pbEntry with ⟨pIdx, bEntry⟩; dsimp only
            split
            · exact Option.Rel.none
            · rename_i hReplayCanon
              have hReplayOk : (checkAndMarkKyberBaseKeySeen s6.toAuthHybridState.base.seenKyberBaseKeys
                  k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 = true := by
                by_contra hne; exact hReplayCanon (by simp [Bool.eq_false_iff.mpr hne])
              have hCanonEk : P.isCanonical msg.hdr.ekAPk = true := by
                by_contra hne; exact hReplayCanon (by simp [Bool.eq_false_iff.mpr hne])
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => exact Option.Rel.none
              | some ss =>
                dsimp only; apply Option.Rel.some
                have hFindMap := find?_matchIdealAuthHandshake_map_setSlotRkIdealSession P idx
                    rkStar
                  kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr
                  s6.toAuthHybridState.idealSessions
                have hKyber := checkAndMarkKyberUsed_eq_true
                    s6.toAuthHybridState.base.seenKyberBaseKeys
                  k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk hReplayOk
                refine {
                  kEntry_eq := rfl, bEntry_eq := rfl, opkPk?_eq := rfl, secrets_eq := rfl,
                  dhRatchet_eq := rfl, honest_eq := rfl, matched_eq := hFindMap,
                  sameEph_eq := by
                    dsimp only; rw [hFindMap]
                    cases List.find? _ s6.toAuthHybridState.idealSessions <;> simp
                        [setSlotRkIdealSession_ephAPk],
                  ephAPk_len := hEphLen,
                  roCache5_eq := rfl, roCache6_eq := rfl,
                  rootRoCache5_eq := rfl, rootRoCache6_eq := rfl,
                  honest_isSome := by
                    dsimp only
                    cases findHonestPrincipal P s6.toAuthHybridState.base.principals msg.hdr.ikAPk
                        <;> simp,
                  matched_wf := fun s hs => by
                    dsimp only at hs ⊢
                    exact ⟨List.mem_of_find?_eq_some hs, List.find?_some hs, by simp [hs]⟩,
                  kyber_wf := ⟨k.val, j.val,
                    mem_spkBundles_of_find?_eq_some _ k.val j.val pIdx bEntry hB,
                    hPqspkId, hSpkId, rfl, hKyber.1, hCanonEk,
                    fun drKey6 rk1 ck1_1 pt roCache' c6' => by
                      unfold finishAuthHybridRecvNoOPK; dsimp only
                      cases findHonestPrincipal P s6.toAuthHybridState.base.principals
                          msg.hdr.ikAPk with
                      | none => exact hKyber.2
                      | some p =>
                        rcases p with ⟨_, senderEntry⟩; dsimp only; split <;> exact hKyber.2⟩,
                  finish_none := ⟨rfl, rfl, rfl, rfl, rfl⟩,
                  finish_some := fun drKey5 drKey6 rk1 ck1_1 pt roCache' c5' c6' hDr => by
                    unfold finishAuthHybridRecvNoOPK; dsimp only
                    cases hF : findHonestPrincipal P s6.toAuthHybridState.base.principals
                        msg.hdr.ikAPk with
                    | none =>
                      rcases hDr with rfl | hSome
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                      · simp [hF] at hSome
                    | some p =>
                      rcases p with ⟨_, senderEntry⟩
                      dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ }
theorem cacheHasRk_newRootRoEntry_eq_of_false (rkStar : Bytes)
    (c' c extra : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hNoRk : cacheHasRk rkStar c' = false) :
    cacheHasRk rkStar (newRootRoEntry c' c extra) = cacheHasRk rkStar extra := by
  unfold newRootRoEntry
  split
  · cases c' with
    | nil => rfl
    | cons e rest =>
      rcases e with ⟨⟨rk, dh⟩, out⟩; unfold cacheHasRk at hNoRk ⊢
      simp only [List.any_cons, Bool.or_eq_false_iff] at hNoRk
      simp [hNoRk.1]
  · rfl
theorem cacheHasRk_newRootRoEntry_of_empty (rkStar : Bytes)
    (c' c extra : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (h : cacheHasRk rkStar (newRootRoEntry c' c []) = true) :
    cacheHasRk rkStar (newRootRoEntry c' c extra) = true := by
  unfold newRootRoEntry at h ⊢
  split at h <;> rename_i hlt
  · simp only [hlt, ↓reduceIte]
    cases c' with
    | nil => cases h
    | cons e rest =>
      unfold cacheHasRk at h ⊢; simp only [List.any_cons, List.any_nil, Bool.or_false] at h
      simp [h]
  · cases h
theorem relProbUpToBad_evalRootKdfOrRo_recv (P : Primitives) (rkStar rk dh : Bytes)
    (cache5 cache6 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hFilter : filterOutRk rkStar cache5 = cache6)
    (hNoRk : cacheHasRk rkStar cache6 = false) :
    RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ filterOutRk rkStar y5.2 = y6.2 ∧
        cacheHasRk rkStar y6.2 = false ∧
        (cache5 = cache6 → y5.2 = y6.2) ∧
        (∀ dh0, y5.2.find? (fun (inp, _) => inp == (rkStar, dh0)) =
          cache5.find? (fun (inp, _) => inp == (rkStar, dh0))))
      (fun y6 => cacheHasRk rkStar y6.2 && cacheHasRk rkStar (newRootRoEntry y6.2 cache6 []))
      (evalRootKdfOrRo true P cache5 rk dh)
      (evalRootKdfOrRo true P cache6 rk dh) := by
  by_cases hEq : (rk == rkStar) = true
  · have hrk : rk = rkStar := beq_iff_eq.mp hEq
    subst hrk
    refine RelProbUpToBad.bad6 _ _ (fun y6 hy6 => ?_)
    have hNone := find?_rk_eq_none_of_cacheHasRk_false rk dh cache6 hNoRk
    unfold evalRootKdfOrRo at hy6; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNone,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy6
    rcases hy6 with ⟨r, _, c, _, rfl⟩; unfold newRootRoEntry cacheHasRk
    simp
  · have hEqF : (rk == rkStar) = false := Bool.eq_false_iff.mpr hEq
    have hfind : cache5.find? (fun (inp, _) => inp == (rk, dh)) =
        cache6.find? (fun (inp, _) => inp == (rk, dh)) := by
      rw [find?_eq_find?_filterOutRk rkStar rk dh hEqF cache5, hFilter]
    unfold evalRootKdfOrRo; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfind]
    cases cache6.find? (fun (inp, _) => inp == (rk, dh)) with
    | some p =>
      rcases p with ⟨_, out⟩
      exact RelProbUpToBad.of_pure ⟨rfl, hFilter, hNoRk, fun h => h, fun _ => rfl⟩
    | none =>
      refine RelProbUpToBad.bind_same sampleBytes32 (fun rk1 => ?_)
      refine RelProbUpToBad.bind_same sampleBytes32 (fun ck1 => ?_)
      apply RelProbUpToBad.of_pure
      have hne' : (rk != rkStar) = true := by
        rw [bne_iff_ne]; exact beq_eq_false_iff_ne.mp hEqF
      refine ⟨rfl, ?_, ?_, fun h => by rw [h], fun dh0 => ?_⟩
      · unfold filterOutRk at hFilter ⊢; simp [hne', hFilter]
      · unfold cacheHasRk at hNoRk ⊢; simp [hEqF, hNoRk]
      · have hHead : (((rk, dh) == (rkStar, dh0))) = false := by
          rw [beq_eq_false_iff_ne]
          intro h; exact (beq_eq_false_iff_ne.mp hEqF) (Prod.mk.inj h).1
        simp [List.find?, hHead]
theorem finishAuthRecvRkTracked_bad_of_ro {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (c5 c5' c6' extra6 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (prep5 prep6 : PreparedAuthRecv S)
    (drKey5 drKey6 : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (hRel : PreparedAuthRecvRel P idx rkStar c5 s6 msg prep5 prep6)
    (hDr : drKey5 = drKey6 ∨
      (findHonestPrincipal P s6.toAuthHybridState.base.principals msg.hdr.ikAPk).isSome = true)
    (hBad : (cacheHasRk rkStar c6' &&
      cacheHasRk rkStar (newRootRoEntry c6' s6.toAuthHybridState.base.rootRoCache [])) = true) :
    badRkTracked rkStar
      (finishAuthRecvRkTracked P msg prep6 drKey6 rk1 ck1_0 roCache' c6' (s6.recvCount + 1)
          extra6).2 = true := by
  simp only [Bool.and_eq_true] at hBad; rcases hBad with ⟨hBad1, hBad2⟩
  have hExtra := cacheHasRk_newRootRoEntry_of_empty rkStar c6'
      s6.toAuthHybridState.base.rootRoCache extra6 hBad2
  unfold finishAuthRecvRkTracked finishAuthRecvRk badRkTracked; rw [hRel.rootRoCache6_eq]
  rcases hRel.finish_none with ⟨_, h6None, _, hBase6, _⟩
  cases hSpqr : P.spqrInitRecv drKey6.pqrKey msg.pqRatchetMsg with
  | none => simp [h6None, hBase6, hExtra]
  | some pSpqr =>
    rcases pSpqr with ⟨_pqrStB, spqrSalt?⟩
    cases hDec : P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
        (firstMsgAD msg.hdr.ikAPk prep6.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
    | none => simp [hDec, h6None, hBase6, hExtra]
    | some pt =>
      rcases hRel.finish_some drKey5 drKey6 rk1 (P.chainKdfNext ck1_0) pt roCache' c5' c6' hDr
        with ⟨_, _, hRoot6, _, _, _, _⟩
      simp [hDec, hRoot6, hBad1]
theorem finishAuthRecvRkTracked_extra_noRk {S : Setup} (P : Primitives)
    (rkStar : Bytes) (c6' extra6 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (msg : PreKeyMsg) (prep6 : PreparedAuthRecv S)
    (drKey6 : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey)) (recvCount' : Nat)
    (hNoRk6' : cacheHasRk rkStar c6' = false)
    (hNoRkExtra : cacheHasRk rkStar extra6 = false) :
    cacheHasRk rkStar
      (finishAuthRecvRkTracked P msg prep6 drKey6 rk1 ck1_0 roCache' c6' recvCount' extra6).2.2 =
          false := by
  unfold finishAuthRecvRkTracked; dsimp only
  have hNew := cacheHasRk_newRootRoEntry_eq_of_false rkStar c6' prep6.hstDec.base.rootRoCache
      extra6 hNoRk6'
  rw [hNoRkExtra] at hNew
  split <;> [exact hNoRkExtra; exact hNew]
theorem agreeOffRkAuth_of_finish_none {S : Setup} (P : Primitives) (idx : Nat) (rkStar : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (prep5 prep6 : PreparedAuthRecv S)
    (hRel : PreparedAuthRecvRel P idx rkStar c5 s6 msg prep5 prep6)
    (hNoRk6 : cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false)
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hFilter : filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hCacheInv : ∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s)
    (hUniq : ∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2) :
    (prep5.finish none).1 = (prep6.finish none).1 ∧
    AgreeOffRkAuth P rkStar idx
      { toAuthHybridState := (prep5.finish none).2, recvCount := s6.recvCount + 1 }
      { toAuthHybridState := (prep6.finish none).2, recvCount := s6.recvCount + 1 } := by
  rcases hRel.finish_none with ⟨h5, h6, hWith, hBase6, hIdeal6⟩; rw [h5, h6]
  refine ⟨rfl, c5, hWith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [hBase6]; exact hNoRk6
  · intro hF
    have hF0 := authSlotFired_false_of_succ_recvCount idx s6
      { toAuthHybridState := prep6.hstDec, recvCount := s6.recvCount + 1 }
      (by dsimp only; rw [hBase6]) (by dsimp only; omega) hF
    dsimp only; rw [hBase6]; exact hSlot hF0
  · dsimp only; rw [hBase6]; exact hFilter
  · exact {
      spk_wf := by dsimp only; rw [hBase6]; exact hWf.spk_wf
      ideal_wf := by dsimp only; rw [hBase6, hIdeal6]; exact hWf.ideal_wf }
  · intro s hs hSlotS
    dsimp only at hs; rw [hIdeal6] at hs
    exact SlotSessionCacheInv.preserved_of_find?_eq (hCacheInv s hs hSlotS) (fun _ => rfl)
      (fun p hp => by dsimp only; rw [hBase6]; exact hp)
      (fun t ht => by dsimp only; rw [hBase6]; exact ht)
  · intro s1 hs1 s2 hs2 h1 h2
    dsimp only at hs1 hs2; rw [hIdeal6] at hs1 hs2; exact hUniq s1 hs1 s2 hs2 h1 h2
theorem finishAuthRecvRkTracked_preserves_agree_of_find?_eq {S : Setup} (P : Primitives)
    (idx : Nat) (rkStar : Bytes)
    (c5 c5' c6' extra5 extra6 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (prep5 prep6 : PreparedAuthRecv S)
    (drKey5 drKey6 : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (hRel : PreparedAuthRecvRel P idx rkStar c5 s6 msg prep5 prep6)
    (hNoRk6 : cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false)
    (hNoRkExtra : cacheHasRk rkStar extra6 = false)
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hFilter : filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hCacheInv : ∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s)
    (hUniq : ∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2)
    (hPqr : drKey5.pqrKey = drKey6.pqrKey)
    (hDr : drKey5 = drKey6 ∨
      (findHonestPrincipal P s6.toAuthHybridState.base.principals msg.hdr.ikAPk).isSome = true)
    (hFilter' : filterOutRk rkStar c5' = c6')
    (hNoRk6' : cacheHasRk rkStar c6' = false)
    (hSlot' : authSlotFired S idx s6 = false → c5' = c6')
    (hFindEq : ∀ dh0, c5'.find? (fun (inp, _) => inp == (rkStar, dh0)) =
      c5.find? (fun (inp, _) => inp == (rkStar, dh0))) :
    let y5 := finishAuthRecvRkTracked P msg prep5 drKey5 rk1 ck1_0 roCache' c5' (s6.recvCount + 1)
        extra5
    let y6 := finishAuthRecvRkTracked P msg prep6 drKey6 rk1 ck1_0 roCache' c6' (s6.recvCount + 1)
        extra6
    y5.1 = y6.1 ∧ AgreeOffRkAuthTracked P rkStar idx y5.2 y6.2 := by
  have hExtra' := finishAuthRecvRkTracked_extra_noRk P rkStar c6' extra6 msg
    prep6 drKey6 rk1 ck1_0 roCache' (s6.recvCount + 1) hNoRk6' hNoRkExtra
  have hCore :
      let r5 := finishAuthRecvRk P msg prep5 drKey5 rk1 ck1_0 roCache' c5' (s6.recvCount + 1)
      let r6 := finishAuthRecvRk P msg prep6 drKey6 rk1 ck1_0 roCache' c6' (s6.recvCount + 1)
      r5.1 = r6.1 ∧ AgreeOffRkAuth P rkStar idx r5.2 r6.2 := by
    unfold finishAuthRecvRk; dsimp only; rw [hPqr, hRel.kEntry_eq]
    cases P.spqrInitRecv drKey6.pqrKey msg.pqRatchetMsg with
    | none =>
      exact agreeOffRkAuth_of_finish_none P idx rkStar c5 s6 msg prep5 prep6
        hRel hNoRk6 hSlot hFilter hWf hCacheInv hUniq
    | some pSpqr =>
      rcases pSpqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
      cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
          (firstMsgAD msg.hdr.ikAPk prep6.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
      | none =>
        exact agreeOffRkAuth_of_finish_none P idx rkStar c5 s6 msg prep5 prep6
          hRel hNoRk6 hSlot hFilter hWf hCacheInv hUniq
      | some pt =>
        dsimp only
        rcases hRel.finish_some drKey5 drKey6 rk1 (P.chainKdfNext ck1_0) pt roCache' c5' c6' hDr
          with ⟨hResp, hWith, hRoot6, hSpk6, hPrin6, hUsed6, hIdeal6⟩
        rcases hRel.kyber_wf with ⟨kVal, jVal, _, _, _, _, _, _, hKyber6⟩
        refine ⟨hResp, c5', hWith, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only; rw [hRoot6]; exact hNoRk6'
        · intro hF
          have hF0 := authSlotFired_false_of_succ_recvCount idx s6
            { toAuthHybridState := (prep6.finish (some (drKey6, rk1, P.chainKdfNext ck1_0, pt,
                roCache', c6'))).2,
              recvCount := s6.recvCount + 1 }
            (by dsimp only; rw [hUsed6]) (by dsimp only; omega) hF
          dsimp only; rw [hRoot6]; exact hSlot' hF0
        · dsimp only; rw [hRoot6]; exact hFilter'
        · exact {
            spk_wf := by dsimp only; rw [hSpk6]; exact hWf.spk_wf
            ideal_wf := by dsimp only; rw [hUsed6, hPrin6, hIdeal6]; exact hWf.ideal_wf }
        · intro s hs hSlotS
          dsimp only at hs; rw [hIdeal6] at hs
          exact SlotSessionCacheInv.preserved_of_find?_eq (hCacheInv s hs hSlotS) hFindEq
            (fun p hp => by dsimp only; rw [hSpk6]; exact hp)
            (fun t ht => by
              dsimp only; rw [hKyber6 drKey6 rk1 (P.chainKdfNext ck1_0) pt roCache' c6']
              exact List.mem_cons_of_mem _ ht)
        · intro s1 hs1 s2 hs2 h1 h2
          dsimp only at hs1 hs2; rw [hIdeal6] at hs1 hs2; exact hUniq s1 hs1 s2 hs2 h1 h2
  exact ⟨hCore.1, hCore.2, hExtra'⟩
theorem finishAuthRecvRkTracked_preserves_agree_of_cons_rkStar {S : Setup} (P : Primitives)
    (idx : Nat) (rkStar : Bytes)
    (c5 extra5 extra6 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (prep5 prep6 : PreparedAuthRecv S)
    (drKey5 drKey6 : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (hRel : PreparedAuthRecvRel P idx rkStar c5 s6 msg prep5 prep6)
    (hNoRk6 : cacheHasRk rkStar s6.toAuthHybridState.base.rootRoCache = false)
    (hNoRkExtra : cacheHasRk rkStar extra6 = false)
    (hSlot : authSlotFired S idx s6 = false → c5 = s6.toAuthHybridState.base.rootRoCache)
    (hFilter : filterOutRk rkStar c5 = s6.toAuthHybridState.base.rootRoCache)
    (hWf : AuthRkStateWf P s6)
    (hCacheInv : ∀ s ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s.sid = idx → SlotSessionCacheInv P rkStar c5 s6 s)
    (hUniq : ∀ s1 ∈ s6.toAuthHybridState.idealSessions, ∀ s2 ∈ s6.toAuthHybridState.idealSessions,
      sessionSlotIndex s1.sid = idx → sessionSlotIndex s2.sid = idx → s1 = s2)
    (hPqr : drKey5.pqrKey = drKey6.pqrKey)
    (hHonest : (findHonestPrincipal P s6.toAuthHybridState.base.principals msg.hdr.ikAPk).isSome =
        true)
    (hFired' : ∀ s6' : AuthHybridStateFixed S,
      s6'.toAuthHybridState.base.usedSendSessions = s6.toAuthHybridState.base.usedSendSessions →
      s6'.recvCount = s6.recvCount + 1 →
      authSlotFired S idx s6' = true)
    (hCacheInv' : ∀ ck1_1 pt,
      let s6' : AuthHybridStateFixed S :=
        { toAuthHybridState := (prep6.finish (some (drKey6, rk1, ck1_1, pt, roCache',
            s6.toAuthHybridState.base.rootRoCache))).2,
          recvCount := s6.recvCount + 1 }
      ∀ s' ∈ s6.toAuthHybridState.idealSessions, sessionSlotIndex s'.sid = idx →
        SlotSessionCacheInv P rkStar (((rkStar, prep6.dhRatchet), (rk1, ck1_0)) :: c5) s6' s') :
    let y5 := finishAuthRecvRkTracked P msg prep5 drKey5 rk1 ck1_0 roCache'
      (((rkStar, prep6.dhRatchet), (rk1, ck1_0)) :: c5) (s6.recvCount + 1) extra5
    let y6 := finishAuthRecvRkTracked P msg prep6 drKey6 rk1 ck1_0 roCache'
      s6.toAuthHybridState.base.rootRoCache (s6.recvCount + 1) extra6
    y5.1 = y6.1 ∧ AgreeOffRkAuthTracked P rkStar idx y5.2 y6.2 := by
  have hExtra' := finishAuthRecvRkTracked_extra_noRk P rkStar s6.toAuthHybridState.base.rootRoCache
    extra6 msg prep6 drKey6 rk1 ck1_0 roCache' (s6.recvCount + 1) hNoRk6 hNoRkExtra
  have hCore :
      let r5 := finishAuthRecvRk P msg prep5 drKey5 rk1 ck1_0 roCache'
        (((rkStar, prep6.dhRatchet), (rk1, ck1_0)) :: c5) (s6.recvCount + 1)
      let r6 := finishAuthRecvRk P msg prep6 drKey6 rk1 ck1_0 roCache'
        s6.toAuthHybridState.base.rootRoCache (s6.recvCount + 1)
      r5.1 = r6.1 ∧ AgreeOffRkAuth P rkStar idx r5.2 r6.2 := by
    unfold finishAuthRecvRk; dsimp only; rw [hPqr, hRel.kEntry_eq]
    cases P.spqrInitRecv drKey6.pqrKey msg.pqRatchetMsg with
    | none =>
      exact agreeOffRkAuth_of_finish_none P idx rkStar c5 s6 msg prep5 prep6
        hRel hNoRk6 hSlot hFilter hWf hCacheInv hUniq
    | some pSpqr =>
      rcases pSpqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
      cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
          (firstMsgAD msg.hdr.ikAPk prep6.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
      | none =>
        exact agreeOffRkAuth_of_finish_none P idx rkStar c5 s6 msg prep5 prep6
          hRel hNoRk6 hSlot hFilter hWf hCacheInv hUniq
      | some pt =>
        dsimp only; rcases hRel.finish_some drKey5 drKey6 rk1 (P.chainKdfNext ck1_0) pt roCache'
          (((rkStar, prep6.dhRatchet), (rk1, ck1_0)) :: c5)
          s6.toAuthHybridState.base.rootRoCache (Or.inr hHonest)
          with ⟨hResp, hWith, hRoot6, hSpk6, hPrin6, hUsed6, hIdeal6⟩
        refine ⟨hResp, ((rkStar, prep6.dhRatchet), (rk1, ck1_0)) :: c5, hWith, ?_, ?_, ?_, ?_, ?_,
            ?_⟩
        · dsimp only; rw [hRoot6]; exact hNoRk6
        · intro hF
          have hT := hFired'
            { toAuthHybridState := (prep6.finish (some (drKey6, rk1, P.chainKdfNext ck1_0, pt,
                roCache',
                s6.toAuthHybridState.base.rootRoCache))).2,
              recvCount := s6.recvCount + 1 }
            (by dsimp only; rw [hUsed6]) rfl
          rw [hT] at hF; contradiction
        · dsimp only; rw [hRoot6]
          unfold filterOutRk
          simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          exact hFilter
        · exact {
            spk_wf := by dsimp only; rw [hSpk6]; exact hWf.spk_wf
            ideal_wf := by dsimp only; rw [hUsed6, hPrin6, hIdeal6]; exact hWf.ideal_wf }
        · intro s' hs' hSlotS
          dsimp only at hs'; rw [hIdeal6] at hs'
          exact hCacheInv' (P.chainKdfNext ck1_0) pt s' hs' hSlotS
        · intro s1 hs1 s2 hs2 h1 h2
          dsimp only at hs1 hs2; rw [hIdeal6] at hs1 hs2; exact hUniq s1 hs1 s2 hs2 h1 h2
  exact ⟨hCore.1, hCore.2, hExtra'⟩
theorem not_phaseB_of_matchedSess {S : Setup} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (idx : Nat) (rkStar : Bytes)
    (c5 : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (s6 : AuthHybridStateFixed S) (msg : PreKeyMsg)
    (prep5 prep6 : PreparedAuthRecv S) (s : IdealAuthSession S)
    (hRel : PreparedAuthRecvRel P idx rkStar c5 s6 msg prep5 prep6)
    (hWf : AuthRkStateWf P s6)
    (hKem : hasKemPkCollisionAuth s6.toAuthHybridState = false)
    (hMatch : prep6.matchedSess? = some s)
    (hPhaseB : ∃ k0 j0 bEntry0, ((k0, j0), bEntry0) ∈ s6.toAuthHybridState.base.spkBundles ∧
      bEntry0.pqspkPk = s.peerPqspkPk ∧
      (k0, UInt32.ofNat j0, UInt32.ofNat j0, s.ekAPk) ∈ s6.toAuthHybridState.base.seenKyberBaseKeys)
          :
    False := by
  rcases hPhaseB with ⟨k0, j0, bEntry0, hMemB0, hPq0, hMemK0⟩
  rcases hRel.matched_wf s hMatch with ⟨hsMem, hHandshake, _⟩
  rcases matchIdealAuthHandshake_eq_true P _ _ _ _ _ s hHandshake with ⟨_, _, hPowEk, hPqB⟩
  rcases hRel.kyber_wf with ⟨kVal, jVal, hMemB, hPqId, hSpkId, _, hNotMemK, hCanonMsg, _⟩
  have hCanonS : P.isCanonical s.ekAPk = true := (hWf.ideal_wf s hsMem).2.2.2
  have hEkEq : msg.hdr.ekAPk = s.ekAPk := hP.canon_pow8_inj msg.hdr.ekAPk s.ekAPk hCanonMsg hCanonS
      hPowEk
  have hNoDup : hasDuplicateBytes (s6.toAuthHybridState.base.spkBundles.map
        (fun (p : (Nat × Nat) × SpkBundleEntry) => p.2.pqspkPk)) = false := hKem
  have hPairEq := eq_of_mem_of_hasDuplicateBytes_map_false
    (fun (p : (Nat × Nat) × SpkBundleEntry) => p.2.pqspkPk) hNoDup
    hMemB hMemB0 (by dsimp only; rw [hPqB, hPq0])
  rcases Prod.mk.inj (Prod.mk.inj hPairEq).1 with ⟨rfl, rfl⟩; rw [hPqId, hSpkId, hEkEq] at hNotMemK
  exact hNotMemK hMemK0
def authRkRecvTracked (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (stT : AuthRkTrackedState S) : ProbComp (AuthResponse × AuthRkTrackedState S) := do
  let (hst, extra) := stT
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, ({ hst with recvCount := recvCount' }, extra))
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        let ((rk1, ck1_0), rootRoCache') ← if useIdealRkAt (sessionSlotIndex s.sid) then
            if prep.sameEph then
              pure ((s.rk1, s.ck1_0), st.rootRoCache)
            else do
              let r ← sampleBytes32
              let c ← sampleBytes32
              pure ((r, c), st.rootRoCache)
          else
            evalRootKdfOrRo true P st.rootRoCache s.drKey.rootKey prep.dhRatchet
        pure (finishAuthRecvRkTracked P msg prep s.drKey rk1 ck1_0 st.roCache rootRoCache'
            recvCount' extra)
      | none =>
        let rSlot := S.N_send_tot + hst.recvCount
        let rk ← sampRkAt rSlot
        let ck ← sampleBytes32
        let pk ← sampleBytes32
        let drKey : DRKey := { rootKey := rk, chainKey := ck, pqrKey := pk }
        let ((rk1, ck1_0), rootRoCache') ← if useIdealRkAt rSlot then do
            let r ← sampleBytes32
            let c ← sampleBytes32
            pure ((r, c), st.rootRoCache)
          else
            evalRootKdfOrRo true P st.rootRoCache rk prep.dhRatchet
        pure (finishAuthRecvRkTracked P msg prep drKey rk1 ck1_0 st.roCache rootRoCache' recvCount'
            extra)
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ←
        evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet
      pure (finishAuthRecvRkTracked P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount'
          extra)
theorem relProbUpToBad_authRkRecvTracked {S : Setup} (P : Primitives) (hP :
    CryptoWellFormedPrimitivesδ P)
    (rkStar : Bytes) (idx : Nat)
    (msg : PreKeyMsg) (prep5? prep6? : Option (PreparedAuthRecv S))
    (s5 s6 : AuthRkTrackedState S)
    (hAg : AgreeOffRkAuthTracked P rkStar idx s5 s6)
    (hKem : hasKemPkCollisionAuth s6.1.toAuthHybridState = false)
    (hRel? : Option.Rel (PreparedAuthRecvRel P idx rkStar
      s5.1.toAuthHybridState.base.rootRoCache s6.1 msg) prep5? prep6?) :
    RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuthTracked P rkStar idx y5.2 y6.2)
      (fun y6 => badRkTracked rkStar y6.2)
      (authRkRecvTracked S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        (fun s => decide (s < idx)) msg prep5? s5)
      (authRkRecvTracked S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) msg prep6? s6) := by
  rcases s5 with ⟨hst5, extra5⟩; rcases s6 with ⟨hst6, extra6⟩
  rcases hAg with ⟨⟨c5, h5Eq, hNoRk6, hSlot, hFilter, hWf, hCacheInv, hUniq⟩, hNoRkExtra⟩
  dsimp only at h5Eq hNoRkExtra hKem hRel?
  subst h5Eq
  have hRoot5 : (withRkAuth idx rkStar c5 hst6).toAuthHybridState.base.rootRoCache = c5 := rfl
  rw [hRoot5] at hRel?
  cases hRel? with
  | none =>
    unfold authRkRecvTracked; dsimp only; apply RelProbUpToBad.of_pure
    refine ⟨rfl, ⟨c5, rfl, hNoRk6, ?_, hFilter, ⟨hWf.spk_wf, hWf.ideal_wf⟩, hCacheInv, hUniq⟩,
        hNoRkExtra⟩
    intro hF; exact hSlot (authSlotFired_false_of_succ_recvCount idx hst6
      { hst6 with recvCount := hst6.recvCount + 1 } rfl (by dsimp only; omega) hF)
  | some hRel =>
    rename_i prep5 prep6; unfold authRkRecvTracked; dsimp only
    have hMatchSome : prep5.matchedSess?.isSome = prep6.matchedSess?.isSome := by
      rw [hRel.matched_eq, Option.isSome_map]
    rw [hMatchSome, hRel.honest_eq]
    split
    · rename_i hIdeal
      cases hMatch : prep6.matchedSess? with
      | some s =>
        have hMatch5 : prep5.matchedSess? = some (setSlotRkIdealSession idx rkStar s) := by
          rw [hRel.matched_eq, hMatch]; rfl
        rw [hMatch5]
        dsimp only; rw [setSlotRkIdealSession_sid, show (withRkAuth idx rkStar c5 hst6).recvCount =
            hst6.recvCount from rfl]
        rw [hRel.sameEph_eq, hRel.roCache5_eq, hRel.roCache6_eq,
            hRel.rootRoCache5_eq, hRel.rootRoCache6_eq, hRel.dhRatchet_eq]
        rcases hRel.matched_wf s hMatch with ⟨hsMem, hHandshake, hSameEphS⟩
        rcases matchIdealAuthHandshake_eq_true P _ _ _ _ _ s hHandshake with
          ⟨hPowIk, hPowSpk, hPowEk, hPqB⟩
        have hHonest : (findHonestPrincipal P hst6.toAuthHybridState.base.principals
            msg.hdr.ikAPk).isSome = true :=
          findHonestPrincipal_isSome_of_mem_honestIkPks P _ msg.hdr.ikAPk s.ikAPk
            (hWf.ideal_wf s hsMem).2.2.1 hPowIk
        by_cases hLt : sessionSlotIndex s.sid < idx
        · have hLt1 : sessionSlotIndex s.sid < idx + 1 := by omega
          have hNe : sessionSlotIndex s.sid ≠ idx := by omega
          rw [setSlotRkIdealSession_eq_self_of_ne (beq_eq_false_iff_ne.mpr hNe)]
          simp only [decide_eq_true_eq.mpr hLt, decide_eq_true_eq.mpr hLt1, ↓reduceIte]
          split
          · simp only [pure_bind]
            apply RelProbUpToBad.of_pure
            exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
              c5 c5 hst6.toAuthHybridState.base.rootRoCache extra5 extra6 hst6 msg
              prep5 prep6 s.drKey s.drKey s.rk1 s.ck1_0 hst6.toAuthHybridState.base.roCache
              hRel hNoRk6 hNoRkExtra hSlot hFilter hWf hCacheInv hUniq rfl (Or.inl rfl)
              hFilter hNoRk6 hSlot (fun _ => rfl)
          · simp only [pure_bind]
            refine RelProbUpToBad.bind_same sampleBytes32 (fun r => ?_)
            refine RelProbUpToBad.bind_same sampleBytes32 (fun c => ?_)
            apply RelProbUpToBad.of_pure
            exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
              c5 c5 hst6.toAuthHybridState.base.rootRoCache extra5 extra6 hst6 msg
              prep5 prep6 s.drKey s.drKey r c hst6.toAuthHybridState.base.roCache
              hRel hNoRk6 hNoRkExtra hSlot hFilter hWf hCacheInv hUniq rfl (Or.inl rfl)
              hFilter hNoRk6 hSlot (fun _ => rfl)
        · by_cases hEqSlot : sessionSlotIndex s.sid = idx
          · have hLt1 : sessionSlotIndex s.sid < idx + 1 := by omega
            simp only [decide_eq_false_iff_not.mpr hLt, decide_eq_true_eq.mpr hLt1,
              Bool.false_eq_true, ↓reduceIte]
            rcases hCacheInv s hsMem hEqSlot with ⟨ephASk, hEphPk, hFindC5⟩ | hPhaseB
            · rcases hRel.kyber_wf with ⟨kVal, jVal, hMemB, hPqId, hSpkId, hDhEq, _, hCanonMsg,
                hKyber6⟩
              have ⟨hSpkLen, hSpkPk⟩ := hWf.spk_wf _ hMemB
              have hDhBeq : (prep6.dhRatchet == P.x25519 ephASk s.peerSpkPk) = prep6.sameEph := by
                rw [hDhEq, dhRatchet_eq_iff_sameEph P hP prep6.bEntry.spkSk prep6.bEntry.spkPk
                  ephASk s.ephAPk s.peerSpkPk msg.ephAPk hSpkLen hSpkPk hEphPk hPowSpk
                  hRel.ephAPk_len, ← hSameEphS]
              have hFindDh := hFindC5 prep6.dhRatchet
              rw [hDhBeq] at hFindDh
              unfold evalRootKdfOrRo; dsimp only
              rw [setSlotRkIdealSession_rootKey_of_eq (beq_iff_eq.mpr hEqSlot)]
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hFindDh]
              cases hSame : prep6.sameEph
              · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
                refine RelProbUpToBad.bind_same sampleBytes32 (fun r => ?_)
                refine RelProbUpToBad.bind_same sampleBytes32 (fun c => ?_)
                apply RelProbUpToBad.of_pure
                exact finishAuthRecvRkTracked_preserves_agree_of_cons_rkStar P idx rkStar
                  c5 extra5 extra6 hst6 msg prep5 prep6 (setSlotRkIdealSession idx rkStar s).drKey
                  s.drKey r c hst6.toAuthHybridState.base.roCache hRel hNoRk6 hNoRkExtra
                  hSlot hFilter hWf hCacheInv hUniq (setSlotRkIdealSession_pqrKey idx rkStar s)
                      hHonest
                  (fun s6' hUsed' _ => by
                    have hFired0 := authSlotFired_of_idealSession_slot_eq hWf hsMem hEqSlot
                    have hLtSend : idx < S.N_send_tot :=
                      sendSlotIndex?_lt (hEqSlot ▸ (hWf.ideal_wf s hsMem).2.1)
                    unfold authSlotFired at hFired0 ⊢; simp only [hLtSend, ↓reduceIte] at hFired0 ⊢
                    rw [hUsed']; exact hFired0)
                  (fun ck1_1 pt s' hs' hSlotS' => by
                    have hsEq : s' = s := hUniq s' hs' s hsMem hSlotS' hEqSlot
                    subst hsEq
                    have hEkEq : msg.hdr.ekAPk = s'.ekAPk :=
                      hP.canon_pow8_inj msg.hdr.ekAPk s'.ekAPk hCanonMsg
                        (hWf.ideal_wf s' hsMem).2.2.2 hPowEk
                    have hSpkEq := (hRel.finish_some (setSlotRkIdealSession idx rkStar s').drKey
                        s'.drKey r ck1_1 pt hst6.toAuthHybridState.base.roCache c5
                            hst6.toAuthHybridState.base.rootRoCache (Or.inr hHonest)).2.2.2.1
                    refine Or.inr ⟨kVal, jVal, prep6.bEntry, by dsimp only; rw [hSpkEq]; exact
                        hMemB, hPqB, ?_⟩
                    dsimp only; rw [hKyber6 s'.drKey r ck1_1 pt hst6.toAuthHybridState.base.roCache
                      hst6.toAuthHybridState.base.rootRoCache, hPqId, hSpkId, hEkEq]
                    exact List.mem_cons_self)
              · simp only [↓reduceIte, pure_bind,
                  ]
                apply RelProbUpToBad.of_pure
                exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
                  c5 c5 hst6.toAuthHybridState.base.rootRoCache extra5 extra6 hst6 msg
                  prep5 prep6 (setSlotRkIdealSession idx rkStar s).drKey s.drKey s.rk1 s.ck1_0
                  hst6.toAuthHybridState.base.roCache hRel hNoRk6 hNoRkExtra hSlot hFilter
                  hWf hCacheInv hUniq (setSlotRkIdealSession_pqrKey idx rkStar s) (Or.inr hHonest)
                  hFilter hNoRk6 hSlot (fun _ => rfl)
            · exact False.elim (not_phaseB_of_matchedSess P hP idx rkStar c5 hst6 msg
                prep5 prep6 s hRel hWf hKem hMatch hPhaseB)
          · have hNotLt1 : ¬ (sessionSlotIndex s.sid < idx + 1) := by omega
            rw [setSlotRkIdealSession_eq_self_of_ne (beq_eq_false_iff_ne.mpr hEqSlot)]
            simp only [decide_eq_false_iff_not.mpr hLt, decide_eq_false_iff_not.mpr hNotLt1,
              Bool.false_eq_true, ↓reduceIte]
            refine RelProbUpToBad.bind_rel
              (relProbUpToBad_evalRootKdfOrRo_recv P rkStar s.drKey.rootKey prep6.dhRatchet
                c5 hst6.toAuthHybridState.base.rootRoCache hFilter hNoRk6)
              (fun b6 hBad y6 hy6 => by
                simp only [support_pure, Set.mem_singleton_iff] at hy6
                subst hy6
                exact finishAuthRecvRkTracked_bad_of_ro P idx rkStar c5 b6.2 b6.2 extra6 hst6 msg
                  prep5 prep6 s.drKey s.drKey b6.1.1 b6.1.2 hst6.toAuthHybridState.base.roCache
                  hRel (Or.inl rfl) hBad)
              (fun y5_ro y6_ro ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
            rcases y5_ro with ⟨⟨r5_rk1, r5_ck1⟩, c5'⟩; rcases y6_ro with ⟨⟨r6_rk1, r6_ck1⟩, c6'⟩
            dsimp only at hOut hFilter' hNoRk6' hEqImp hFindEq; rcases Prod.mk.inj hOut with ⟨rfl,
                rfl⟩
            apply RelProbUpToBad.of_pure
            exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
              c5 c5' c6' extra5 extra6 hst6 msg prep5 prep6 s.drKey s.drKey r5_rk1 r5_ck1
              hst6.toAuthHybridState.base.roCache hRel hNoRk6 hNoRkExtra hSlot hFilter hWf
              hCacheInv hUniq rfl (Or.inl rfl) hFilter' hNoRk6' (fun hF => hEqImp (hSlot hF))
                  hFindEq
      | none =>
        have hMatch5 : prep5.matchedSess? = none := by rw [hRel.matched_eq, hMatch]; rfl
        have hRecv5 : (withRkAuth idx rkStar c5 hst6).recvCount = hst6.recvCount := rfl
        rw [hMatch5, hRecv5]
        dsimp only; rw [hRel.roCache5_eq, hRel.roCache6_eq,
            hRel.rootRoCache5_eq, hRel.rootRoCache6_eq, hRel.dhRatchet_eq]
        have hHonestB : prep6.isUncorruptedHonestSender = true := by
          simp only [hMatch, Option.isSome_none, Bool.false_or] at hIdeal; exact hIdeal
        have hHonest := hRel.honest_isSome hHonestB
        by_cases hLt : S.N_send_tot + hst6.recvCount < idx
        · have hLt1 : S.N_send_tot + hst6.recvCount < idx + 1 := by omega
          have hNe : (S.N_send_tot + hst6.recvCount == idx) = false :=
            beq_eq_false_iff_ne.mpr (by omega)
          simp only [hNe, decide_eq_true_eq.mpr hLt, decide_eq_true_eq.mpr hLt1,
            Bool.false_eq_true, ↓reduceIte, pure_bind]
          refine RelProbUpToBad.bind_same sampleBytes32 (fun rk => ?_)
          refine RelProbUpToBad.bind_same sampleBytes32 (fun ck => ?_)
          refine RelProbUpToBad.bind_same sampleBytes32 (fun pk => ?_)
          refine RelProbUpToBad.bind_same sampleBytes32 (fun r => ?_)
          refine RelProbUpToBad.bind_same sampleBytes32 (fun c => ?_)
          apply RelProbUpToBad.of_pure
          exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
            c5 c5 hst6.toAuthHybridState.base.rootRoCache extra5 extra6 hst6 msg
            prep5 prep6 { rootKey := rk, chainKey := ck, pqrKey := pk }
            { rootKey := rk, chainKey := ck, pqrKey := pk } r c
            hst6.toAuthHybridState.base.roCache hRel hNoRk6 hNoRkExtra hSlot hFilter hWf
            hCacheInv hUniq rfl (Or.inl rfl) hFilter hNoRk6 hSlot (fun _ => rfl)
        · by_cases hEqSlot : S.N_send_tot + hst6.recvCount = idx
          · have hBeq : (S.N_send_tot + hst6.recvCount == idx) = true := beq_iff_eq.mpr hEqSlot
            have hLt1 : S.N_send_tot + hst6.recvCount < idx + 1 := by omega
            have hNotFired : authSlotFired S idx hst6 = false := by
              have hGe : ¬ (idx < S.N_send_tot) := by omega
              unfold authSlotFired; simp only [hGe, ↓reduceIte, decide_eq_false_iff_not]; omega
            have hc5Eq : c5 = hst6.toAuthHybridState.base.rootRoCache := hSlot hNotFired
            have hNoRk5 : cacheHasRk rkStar c5 = false := hc5Eq ▸ hNoRk6
            have hFindNone : c5.find? (fun (inp, _) => inp == (rkStar, prep6.dhRatchet)) = none :=
              find?_rk_eq_none_of_cacheHasRk_false rkStar prep6.dhRatchet c5 hNoRk5
            simp only [hBeq, decide_eq_false_iff_not.mpr hLt, decide_eq_true_eq.mpr hLt1,
              Bool.false_eq_true, ↓reduceIte, pure_bind]
            refine RelProbUpToBad.bind_right sampleBytes32 (fun rk => ?_)
            refine RelProbUpToBad.bind_same sampleBytes32 (fun ck => ?_)
            refine RelProbUpToBad.bind_same sampleBytes32 (fun pk => ?_)
            unfold evalRootKdfOrRo; dsimp only
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hFindNone, bind_assoc,
                pure_bind]
            refine RelProbUpToBad.bind_same sampleBytes32 (fun r => ?_)
            refine RelProbUpToBad.bind_same sampleBytes32 (fun c => ?_)
            apply RelProbUpToBad.of_pure
            exact finishAuthRecvRkTracked_preserves_agree_of_cons_rkStar P idx rkStar
              c5 extra5 extra6 hst6 msg prep5 prep6
              { rootKey := rkStar, chainKey := ck, pqrKey := pk }
              { rootKey := rk, chainKey := ck, pqrKey := pk } r c
              hst6.toAuthHybridState.base.roCache hRel hNoRk6 hNoRkExtra
              hSlot hFilter hWf hCacheInv hUniq rfl hHonest
              (fun s6' _ hRecv' => by
                have hGe : ¬ (idx < S.N_send_tot) := by omega
                unfold authSlotFired; simp only [hGe, ↓reduceIte, hRecv', decide_eq_true_eq]; omega)
              (fun _ _ s' hs' hSlotS' => by
                have hLtSend : idx < S.N_send_tot :=
                  sendSlotIndex?_lt (hSlotS' ▸ (hWf.ideal_wf s' hs').2.1)
                omega)
          · have hNe : (S.N_send_tot + hst6.recvCount == idx) = false :=
              beq_eq_false_iff_ne.mpr hEqSlot
            have hNotLt1 : ¬ (S.N_send_tot + hst6.recvCount < idx + 1) := by omega
            simp only [hNe, decide_eq_false_iff_not.mpr hLt, decide_eq_false_iff_not.mpr hNotLt1,
              Bool.false_eq_true, ↓reduceIte]
            refine RelProbUpToBad.bind_same sampleBytes32 (fun rk => ?_)
            refine RelProbUpToBad.bind_same sampleBytes32 (fun ck => ?_)
            refine RelProbUpToBad.bind_same sampleBytes32 (fun pk => ?_)
            refine RelProbUpToBad.bind_rel
              (relProbUpToBad_evalRootKdfOrRo_recv P rkStar rk prep6.dhRatchet
                c5 hst6.toAuthHybridState.base.rootRoCache hFilter hNoRk6)
              (fun b6 hBad y6 hy6 => by
                simp only [support_pure, Set.mem_singleton_iff] at hy6
                subst hy6
                exact finishAuthRecvRkTracked_bad_of_ro P idx rkStar c5 b6.2 b6.2 extra6 hst6 msg
                  prep5 prep6 { rootKey := rk, chainKey := ck, pqrKey := pk }
                  { rootKey := rk, chainKey := ck, pqrKey := pk } b6.1.1 b6.1.2
                  hst6.toAuthHybridState.base.roCache hRel (Or.inl rfl) hBad)
              (fun y5_ro y6_ro ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
            rcases y5_ro with ⟨⟨r5_rk1, r5_ck1⟩, c5'⟩; rcases y6_ro with ⟨⟨r6_rk1, r6_ck1⟩, c6'⟩
            dsimp only at hOut hFilter' hNoRk6' hEqImp hFindEq; rcases Prod.mk.inj hOut with ⟨rfl,
                rfl⟩
            apply RelProbUpToBad.of_pure
            exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
              c5 c5' c6' extra5 extra6 hst6 msg prep5 prep6
              { rootKey := rk, chainKey := ck, pqrKey := pk }
              { rootKey := rk, chainKey := ck, pqrKey := pk } r5_rk1 r5_ck1
              hst6.toAuthHybridState.base.roCache hRel hNoRk6 hNoRkExtra hSlot hFilter hWf
              hCacheInv hUniq rfl (Or.inl rfl) hFilter' hNoRk6' (fun hF => hEqImp (hSlot hF))
                  hFindEq
    · rw [hRel.roCache5_eq, hRel.roCache6_eq, hRel.secrets_eq,
          hRel.rootRoCache5_eq, hRel.rootRoCache6_eq, hRel.dhRatchet_eq]
      refine RelProbUpToBad.bind_same
        (evalHkdfOrRo true P hst6.toAuthHybridState.base.roCache prep6.secrets)
        (fun ⟨drKey, roCache'⟩ => ?_)
      dsimp only
      refine RelProbUpToBad.bind_rel
        (relProbUpToBad_evalRootKdfOrRo_recv P rkStar drKey.rootKey prep6.dhRatchet
          c5 hst6.toAuthHybridState.base.rootRoCache hFilter hNoRk6)
        (fun b6 hBad y6 hy6 => by
          simp only [support_pure, Set.mem_singleton_iff] at hy6
          subst hy6; exact finishAuthRecvRkTracked_bad_of_ro P idx rkStar c5 b6.2 b6.2 extra6 hst6
              msg
            prep5 prep6 drKey drKey b6.1.1 b6.1.2 roCache' hRel (Or.inl rfl) hBad)
        (fun y5_ro y6_ro ⟨hOut, hFilter', hNoRk6', hEqImp, hFindEq⟩ => ?_)
      rcases y5_ro with ⟨⟨r5_rk1, r5_ck1⟩, c5'⟩; rcases y6_ro with ⟨⟨r6_rk1, r6_ck1⟩, c6'⟩
      dsimp only at hOut hFilter' hNoRk6' hEqImp hFindEq; rcases Prod.mk.inj hOut with ⟨rfl, rfl⟩
      apply RelProbUpToBad.of_pure
      exact finishAuthRecvRkTracked_preserves_agree_of_find?_eq P idx rkStar
        c5 c5' c6' extra5 extra6 hst6 msg prep5 prep6 drKey drKey r5_rk1 r5_ck1
        roCache' hRel hNoRk6 hNoRkExtra hSlot hFilter hWf hCacheInv hUniq
        rfl (Or.inl rfl) hFilter' hNoRk6' (fun hF => hEqImp (hSlot hF)) hFindEq
end SignalPqxdh.Security.AuthSubHops1to3
