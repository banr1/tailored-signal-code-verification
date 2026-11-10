/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkShallow

/-!
# Leaf List-Length Bounds for the Shallow `PrfMsgKeys` Step

Proves `mkPre_leaves` and `MkCont.post_leaves`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl
open SignalPqxdh SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

theorem finishAuthSendMkPrim_bounded {S : Setup} {n : Nat} (sid : SessionId S)
    (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) (hB : AuthListsBounded n hst) :
    AllLeaves (fun p => AuthListsBounded (n + 1) p.2)
      (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt
        ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys) := by
  unfold finishAuthSendMkPrim
  refine AllLeaves.bind_const _ (fun aeadCt => ?_)
  refine AllLeaves.bind (finishAuthHybridSendPrim_bounded (hB := hB.toAuthHybridListsBounded)
    (hRo := Nat.le_trans hB.roCache_le (Nat.le_succ n))
    (hRoot := Nat.le_trans hB.rootRoCache_le (Nat.le_succ n)) ..) ?_
  intro p hp
  exact AllLeaves.pure ⟨hp, Nat.le_trans hB.mkSaltCache_le (Nat.le_succ n)⟩

private theorem finishAuthRecvMkSlotsPrim_bounded {S : Setup} {n : Nat} (msg : PreKeyMsg)
    (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState)
    (deriveMessageKeys : MessageKeys) (hP : PreparedRecvBounded n prep)
    (hc : mkSaltCache'.length ≤ n + 1) :
    AllLeaves (fun p => AuthListsBounded (n + 1) p.2)
      (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' slots'
        deriveMessageKeys) := by
  unfold finishAuthRecvMkSlotsPrim
  refine AllLeaves.bind_const _ (fun pt? => ?_)
  refine AllLeaves.bind (recvFinishTagRunPrim_bounded _ _ _ hP.tag_bounded ?_) ?_
  · intro drKey' rk1' ck1_1' pt' roCache' rootRoCache' h
    cases pt? with
    | none => cases h
    | some pt =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, h5, h6⟩ := h
      subst h5 h6
      exact ⟨Nat.le_trans hP.roCache_le (Nat.le_succ n),
        Nat.le_trans hP.rootRoCache_le (Nat.le_succ n)⟩
  · intro p hp
    exact AllLeaves.pure ⟨hp, hc⟩

theorem finishAuthRecvMkPrim_bounded {S : Setup} {n : Nat} (msg : PreKeyMsg)
    (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) (hP : PreparedRecvBounded n prep)
    (hc : mkSaltCache'.length ≤ n + 1) :
    AllLeaves (fun p => AuthListsBounded (n + 1) p.2)
      (finishAuthRecvMkPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' deriveMessageKeys) :=
  finishAuthRecvMkSlotsPrim_bounded msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' {}
    deriveMessageKeys hP hc

theorem MkCont.post_leaves {S : Setup} {n : Nat} (c : MkCont S) (mk : MessageKeys)
    (hc : c.Bounded n) :
    AllLeaves (fun p => AuthListsBounded (n + 1) p.2) (c.post mk) := by
  cases c with
  | send hst sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1
      ck1_1 spqrSalt? pqRatchetMsg msgPlain =>
    exact finishAuthSendMkPrim_bounded sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt
      ephASk ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain hst mk hc
  | recv msg prep drKey rk1 ck1_1 recvCount' cache slots ci? =>
    obtain ⟨hP, hC⟩ := hc
    refine finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP ?_
    cases ci? with
    | none => exact Nat.le_trans hC (Nat.le_succ n)
    | some p => simp; omega

def PrepSendOk {S : Setup} (n : Nat) : PreparedAuthSend S → Prop
  | .done _ hst' => AuthListsBounded (n + 1) hst'
  | .idealMk .. => True

theorem prepareAuthSendMkPrim_bounded {S : Setup} {n : Nat}
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hB : AuthListsBounded n hst) :
    AllLeaves (PrepSendOk n) (prepareAuthSendMkPrim S sid u bundle m0 m1 hst) := by
  have hB' : AuthListsBounded (n + 1) hst := hB.mono (Nat.le_succ n)
  have hD : ∀ r, PrepSendOk n (.done r hst) := fun _ => hB'
  unfold prepareAuthSendMkPrim
  dsimp only
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hD _)) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hD _)) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hD _)) (fun _ => ?_)
  cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact AllLeaves.pure (hD _)
  | some p =>
    rcases p with ⟨_, uEntry⟩
    refine AllLeaves.bind_const _ (fun peerPrincipal? => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hD _)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun koskOk => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hD _)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun ekASk => ?_)
    refine AllLeaves.bind_const _ (fun kemCoins => ?_)
    refine AllLeaves.bind_const _ (fun ephASk => ?_)
    refine AllLeaves.bind_const _ (fun spqrCoins => ?_)
    refine AllLeaves.bind_const _ (fun sigPkB => ?_)
    refine AllLeaves.bind_const _ (fun v1 => ?_)
    refine AllLeaves.bind_const _ (fun v2 => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hD _)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun enc? => ?_)
    rcases enc? with _ | ⟨ss, kemCt⟩
    · exact AllLeaves.pure (hD _)
    refine AllLeaves.bind_const _ (fun ekAPk => ?_)
    refine AllLeaves.bind_const _ (fun ephAPk => ?_)
    refine AllLeaves.bind_const _ (fun spkHonIdeal => ?_)
    refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · refine AllLeaves.bind_const _ (fun drKey => ?_)
      refine AllLeaves.bind_const _ (fun rk1 => ?_)
      refine AllLeaves.bind_const _ (fun r? => ?_)
      rcases r? with _ | ⟨_, _, _⟩
      · exact AllLeaves.pure (hD _)
      · exact AllLeaves.pure trivial
    · refine AllLeaves.bind_const _ (fun dh1 => ?_)
      refine AllLeaves.bind_const _ (fun dh2 => ?_)
      refine AllLeaves.bind_const _ (fun dh3 => ?_)
      refine AllLeaves.bind_const _ (fun dh4? => ?_)
      refine AllLeaves.bind (AllLeaves.embedUnif (evalHkdfRoPure_length_le _ _ hB.roCache_le)) ?_
      intro ⟨drKey, roCache'⟩ hRo
      refine AllLeaves.bind_const _ (fun dhRatchet => ?_)
      refine AllLeaves.bind
        (AllLeaves.embedUnif (evalRootKdfRoPure_length_le _ _ _ hB.rootRoCache_le)) ?_
      intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ hRoot
      refine AllLeaves.bind_const _ (fun mkSeed => ?_)
      refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
      refine AllLeaves.bind_const _ (fun r? => ?_)
      rcases r? with _ | ⟨_, spqrSalt?, pqRatchetMsg⟩
      · exact AllLeaves.pure (hD _)
      refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
      refine AllLeaves.bind_const _ (fun aeadCt => ?_)
      refine AllLeaves.bind (finishAuthHybridSendPrim_bounded (hB := hB.toAuthHybridListsBounded)
        (hRo := hRo) (hRoot := hRoot) ..) ?_
      intro p hp
      exact AllLeaves.pure ⟨hp, Nat.le_trans hB.mkSaltCache_le (Nat.le_succ n)⟩

def MkLeafOk {S : Setup} (n : Nat) (sc : Bool) (R : Prop) : MkPre S → Prop
  | .inl (_, hst') => AuthListsBounded (n + 1) hst'
  | .inr (_, c) => c.Bounded n ∧ (c.isSend = true → sc = false) ∧ (c.isSend = false → R)

theorem mkSendPre_leaves {S : Setup} {n : Nat} (R : Prop) (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sc : Bool) (hB : AuthListsBounded n hst) :
    AllLeaves (MkLeafOk n sc R) (mkSendPre S idx sid u bundle m0 m1 hst sc) := by
  unfold mkSendPre
  refine AllLeaves.bind (prepareAuthSendMkPrim_bounded sid u bundle m0 m1 hst hB) ?_
  intro prep hprep
  cases prep with
  | done resp hst' => exact AllLeaves.pure hprep
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
      pqRatchetMsg msgPlain =>
    dsimp only
    have hB' : AuthListsBounded n { hst with slots := (hst.slots.allocSend sid).2 } :=
      ⟨hB.toAuthHybridListsBounded, hB.mkSaltCache_le⟩
    refine AllLeaves.ite _ (fun hc => ?_) (fun _ => ?_)
    · refine AllLeaves.bind_const _ (fun ck1_1 => AllLeaves.pure ?_)
      refine ⟨hB', ⟨fun _ => ?_, fun h => by simp [MkCont.isSend] at h⟩⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact hc.1
    refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
      refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
      exact AllLeaves.bind
        (finishAuthSendMkPrim_bounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB')
        (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
    · refine AllLeaves.bind_const _ (fun mkSeed => ?_)
      refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
      refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
      exact AllLeaves.bind
        (finishAuthSendMkPrim_bounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB')
        (fun ⟨_, _⟩ hp => AllLeaves.pure hp)

private theorem mkUnmatchedSlotsPre_leaves {S : Setup} {n : Nat} {R : Prop} (hR : R) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat) (cache : AuthMkSaltCache S)
    (slots' : AuthSlotState)
    (sc : Bool) (hP : PreparedRecvBounded n prep) (hC : cache.length ≤ n) :
    AllLeaves (MkLeafOk n sc R)
      (mkUnmatchedSlotsPre S idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache slots' sc) := by
  have hC' : cache.length ≤ n + 1 := Nat.le_trans hC (Nat.le_succ n)
  unfold mkUnmatchedSlotsPre
  refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
    refine AllLeaves.ite _
      (fun _ => AllLeaves.pure ⟨⟨hP, hC⟩, ⟨fun h => by simp [MkCont.isSend] at h, fun _ => hR⟩⟩)
      (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
    exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots' _ hP hC')
      (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
  refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
    refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
    exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots' _ hP hC')
      (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
  · refine AllLeaves.bind_const _ (fun mkSeed => ?_)
    refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
    refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
    exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots' _ hP hC')
      (fun ⟨_, _⟩ hp => AllLeaves.pure hp)

theorem mkUnmatchedPre_leaves {S : Setup} {n : Nat} {R : Prop} (hR : R) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat) (cache : AuthMkSaltCache S)
    (sc : Bool) (hP : PreparedRecvBounded n prep) (hC : cache.length ≤ n) :
    AllLeaves (MkLeafOk n sc R)
      (mkUnmatchedPre S idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache sc) :=
  mkUnmatchedSlotsPre_leaves hR idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache {} sc hP hC

private theorem mkMatchedSameEphSlotsPre_leaves {S : Setup} {n : Nat} {R : Prop} (hR : R)
    (idx : Nat) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (s : IdealAuthSession S) (sIdx : Nat) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (cache : AuthMkSaltCache S) (slots : AuthSlotState) (sc : Bool)
    (hP : PreparedRecvBounded n prep) (hC : cache.length ≤ n) :
    AllLeaves (MkLeafOk n sc R)
      (mkMatchedSameEphSlotsPre S idx msg prep s sIdx spqrSalt? recvCount cache slots) := by
  have hC' : cache.length ≤ n + 1 := Nat.le_trans hC (Nat.le_succ n)
  unfold mkMatchedSameEphSlotsPre
  dsimp only
  refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP hC')
        (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
    · cases cache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some e =>
        rcases e with ⟨_, _, mk⟩
        exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP hC')
          (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
      | none =>
        exact AllLeaves.pure ⟨⟨hP, hC⟩, ⟨fun h => by simp [MkCont.isSend] at h, fun _ => hR⟩⟩
  refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP hC')
        (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
    · cases cache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some e =>
        rcases e with ⟨_, _, mk⟩
        exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP hC')
          (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
      | none =>
        refine AllLeaves.bind_const _ (fun mk => ?_)
        exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP
          (by simp; omega))
          (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
  · refine AllLeaves.bind_const _ (fun mk => ?_)
    exact AllLeaves.bind (finishAuthRecvMkSlotsPrim_bounded _ _ _ _ _ _ _ slots _ hP hC')
      (fun ⟨_, _⟩ hp => AllLeaves.pure hp)

theorem mkMatchedSameEphPre_leaves {S : Setup} {n : Nat} {R : Prop} (hR : R) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (cache : AuthMkSaltCache S) (sc : Bool) (hP : PreparedRecvBounded n prep)
    (hC : cache.length ≤ n) :
    AllLeaves (MkLeafOk n sc R)
      (mkMatchedSameEphPre S idx msg prep s spqrSalt? recvCount cache) :=
  mkMatchedSameEphSlotsPre_leaves hR idx msg prep s (sessionSlotIndex s.sid) spqrSalt? recvCount
    cache {} sc hP hC

theorem mkRecvPre_leaves {S : Setup} {n : Nat} {R : Prop} (hR : R) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sc : Bool) (hB : AuthListsBounded n hst)
    (hprep : ∀ prep, prep? = some prep → PreparedRecvBounded n prep) :
    AllLeaves (MkLeafOk n sc R) (mkRecvPre S idx msg prep? hst sc) := by
  have hMk : hst.mkSaltCache.length ≤ n + 1 := Nat.le_trans hB.mkSaltCache_le (Nat.le_succ n)
  unfold mkRecvPre
  cases prep? with
  | none => exact AllLeaves.pure ⟨(hB.mono (Nat.le_succ n)).toAuthHybridListsBounded, hMk⟩
  | some prep =>
    have hP := hprep prep rfl
    have hTagNone : AllLeaves (MkLeafOk n sc R) (do
        let (resp, hst') ← prep.finishTag.runPrim S true none
        return Sum.inl (resp, AuthHybridStateFixed.mk hst' (hst.recvCount + 1) hst.mkSaltCache
          hst.slots)) :=
      AllLeaves.bind (recvFinishTagRunPrim_bounded _ _ _ hP.tag_bounded
          (fun _ _ _ _ _ _ h => by cases h))
        (fun ⟨_, _⟩ hp => AllLeaves.pure ⟨hp, hMk⟩)
    dsimp only
    refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · cases prep.matchedSess? with
      | some s =>
        refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
        · refine AllLeaves.bind_const _ (fun r? => ?_)
          rcases r? with _ | ⟨_, spqrSalt?⟩
          · exact hTagNone
          · exact mkMatchedSameEphSlotsPre_leaves hR _ _ _ _ _ _ _ _ _ sc hP hB.mkSaltCache_le
        · refine AllLeaves.bind_const _ (fun rk1 => ?_)
          refine AllLeaves.bind_const _ (fun r? => ?_)
          rcases r? with _ | ⟨_, spqrSalt?⟩
          · exact hTagNone
          · exact mkUnmatchedSlotsPre_leaves hR _ _ _ _ _ _ _ _ _ _ sc hP hB.mkSaltCache_le
      | none =>
        refine AllLeaves.bind_const _ (fun drKey => ?_)
        refine AllLeaves.bind_const _ (fun rk1 => ?_)
        refine AllLeaves.bind_const _ (fun r? => ?_)
        rcases r? with _ | ⟨_, spqrSalt?⟩
        · exact hTagNone
        · exact mkUnmatchedSlotsPre_leaves hR _ _ _ _ _ _ _ _ _ _ sc hP hB.mkSaltCache_le
    · refine AllLeaves.bind (AllLeaves.embedUnif (evalHkdfRoPure_length_le _ _ hP.roCache_le)) ?_
      intro ⟨drKey, roCache'⟩ hRo
      refine AllLeaves.bind
        (AllLeaves.embedUnif (evalRootKdfRoPure_length_le _ _ _ hP.rootRoCache_le)) ?_
      intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ hRoot
      refine AllLeaves.bind_const _ (fun mkSeed => ?_)
      refine AllLeaves.bind_const _ (fun ck1_1 => ?_)
      refine AllLeaves.bind_const _ (fun r? => ?_)
      rcases r? with _ | ⟨_, spqrSalt?⟩
      · exact hTagNone
      refine AllLeaves.bind_const _ (fun deriveMessageKeys => ?_)
      refine AllLeaves.bind_const _ (fun pt? => ?_)
      refine AllLeaves.bind (recvFinishTagRunPrim_bounded _ _ _ hP.tag_bounded ?_)
        (fun ⟨_, _⟩ hp => AllLeaves.pure ⟨hp, hMk⟩)
      intro drKey' rk1' ck1_1' pt' roCache'' rootRoCache'' h
      cases pt? with
      | none => cases h
      | some pt =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, _, h5, h6⟩ := h
        subst h5 h6
        exact ⟨hRo, hRoot⟩

theorem mkPre_leaves {S : Setup} {n : Nat} (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (sc : Bool) (hB : AuthListsBounded n hst) :
    AllLeaves (fun (p : MkPre S) => match p with
        | .inl (_, hst') => AuthListsBounded (n + 1) hst'
        | .inr (_, c) => c.Bounded n ∧ (c.isSend = true → sc = false) ∧
            (c.isSend = false → isAuthRecvQuery (.inr q : Nat ⊕ AuthQuery S)))
      (mkPre S idx q hst sc) := by
  have hB' : AuthListsBounded (n + 1) hst := hB.mono (Nat.le_succ n)
  suffices h : AllLeaves (MkLeafOk n sc (isAuthRecvQuery (.inr q : Nat ⊕ AuthQuery S)))
      (mkPre S idx q hst sc) by
    refine AllLeaves.mono h ?_
    intro p hp
    rcases p with ⟨_, _⟩ | ⟨_, _⟩ <;> exact hp
  have hOther : ∀ q', AllLeaves (MkLeafOk n sc (isAuthRecvQuery (.inr q : Nat ⊕ AuthQuery S)))
      (Sum.inl <$> AuthSubHops1to3.stepAuthOtherPrim S q' hst) := by
    intro q'
    rw [map_eq_bind_pure_comp]
    exact AllLeaves.bind (stepAuthOtherPrim_bounded q' hst hB)
      (fun ⟨_, _⟩ hp => AllLeaves.pure hp)
  cases q with
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ => unfold mkPre; exact hOther _
  | sendOPK u i bundle m0 m1 =>
    unfold mkPre
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => mkSendPre_leaves (hB := hB) ..)
  | sendNoOPK u i bundle m0 m1 =>
    unfold mkPre
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => mkSendPre_leaves (hB := hB) ..)
  | recvOPK k j o msg =>
    unfold mkPre
    exact AllLeaves.bind
      (prepareAuthHybridRecvOPKPrim_bounded k j o msg _ hB.toAuthHybridListsBounded)
      (fun prep? hprep => mkRecvPre_leaves trivial idx msg prep? hst sc hB hprep)
  | recvNoOPK k j l msg =>
    unfold mkPre
    exact AllLeaves.bind
      (prepareAuthHybridRecvNoOPKPrim_bounded k j l msg _ hB.toAuthHybridListsBounded)
      (fun prep? hprep => mkRecvPre_leaves trivial idx msg prep? hst sc hB hprep)

end SignalPqxdh.Security.ReductionDsl.AuthPrf
