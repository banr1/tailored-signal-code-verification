/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `PrfChainKey` Sub-Hop (`G3.6` to `G3.7`)

Proves hybrid state validity and establishes the single-identity-key `PrfChainKey` sub-hop bound
`hop_G3_6_G3_7_1Key` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security

namespace AuthSubHops1to3

theorem simulateQ_authCkStepWithPrim1Key (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hV : ValidAuthHybrid S P hst) :
    simulateQ (primBaseImpl P) (authCkStepWithPrim1Key S sampAt q (cacheAuthAdvKeysFixed P hst)) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$> authCkSlotsStepWith1Key S P sampAtPure q hst :=
  simulateQ_authCkSlotsStepWithPrim1Key S P sampAt sampAtPure hSamp q hst hV

theorem authCkStepWith_validAuthHybrid1Key (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authCkStepWith1Key S P sampAt q hst), ValidAuthHybrid S P x.2 := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkStepWith1Key; dsimp only
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · exact authCkSendWith_validAuthHybrid S P sampAt (.sendOPK u i) trivial u bundle m0 m1 hst hV
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepWith1Key; dsimp only
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · exact authCkSendWith_validAuthHybrid S P sampAt (.sendNoOPK u i) trivial u bundle m0 m1 hst hV
  | recvOPK k j o msg =>
    unfold authCkStepWith1Key; dsimp only
    exact authCkRecvWith_validAuthHybrid S P sampAt msg _ hst hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg hst hV prep hPrep res? recvCount')
  | recvNoOPK k j l msg =>
    unfold authCkStepWith1Key; dsimp only
    exact authCkRecvWith_validAuthHybrid S P sampAt msg _ hst hV
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg hst hV prep hPrep res? recvCount')
  | initPrin u =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨secIKA0, _, rfl⟩
      exact ⟨⟨(validPrincipals_cons S u _ hst.toAuthHybridState.base.principals hVP hFresh).1,
        hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | corruptIK u =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_corr := validPrincipals_map_corrupted S P u.val
        hst.toAuthHybridState.base.principals hVP
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨h_corr.1, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | genSPK u j =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        intro x hx; simp at hx; subst hx
        exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        exact ⟨⟨hVP,
          (validSpkBundles_cons S u j _ hst.toAuthHybridState.base.spkBundles hVS hFresh).1,
          hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | genOPK u j o =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : hst.toAuthHybridState.base.opkEntries.any
      (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩
      exact ⟨⟨hVP, hVS,
        (validOpkEntries_cons S u j o _ hst.toAuthHybridState.base.opkEntries hVO hFresh).1,
        hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      intro x hx; simp at hx; subst hx
      exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hSessLe, hIdealLe, hSentOPKLe, hSentNoOPKLe, hVKem⟩
  | registerKey sk =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG registerAdvKey; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split <;> (intro x hx; simp at hx; subst hx; exact ⟨hV.validEc, hV.sess_le,
      hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩)
  | roQuery secrets =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩
  | roRootQuery rk dh =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    intro x hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact ⟨hV.validEc, hV.sess_le, hV.ideal_le, hV.sentOPK_le, hV.sentNoOPK_le, hV.validKem⟩
  | revealDhSecrets =>
    unfold authCkStepWith1Key authCkOtherStep1Key pqxdhAuthImpl1KeyG; dsimp only
    split; · intro x hx; simp at hx; subst hx; exact hV
    intro x hx; simp at hx; subst hx; exact hV

/-! ## Creation-order `PrfChainKey` hybrid -/

private theorem authCkSlotsStepWith_validAuthHybrid1Key (S : Setup) (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hV : ValidAuthHybrid S P hst) :
    ∀ x ∈ support (authCkSlotsStepWith1Key S P sampAt q hst), ValidAuthHybrid S P x.2 := by
  have hVP0 : ValidAuthHybrid S P (projSlots0 hst) := ⟨hV.1, hV.2, hV.3, hV.4, hV.5, hV.6⟩
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith1Key; dsimp only
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · intro x hx
      have hMem : Prod.map id projSlots0 x ∈
          support (Prod.map id projSlots0 <$>
            authCkSlotsSendWith S P sampAt (.sendOPK u i) u bundle m0 m1 hst) := by
        rw [support_map]; exact ⟨x, hx, rfl⟩
      rw [map_projSlots0_authCkSlotsSendWith S P sampAt
            (fun _ => sampAt (hst.slots.allocSend (.sendOPK u i)).1)
            (.sendOPK u i) u bundle m0 m1 hst (fun _ => rfl)] at hMem
      have hVPx := authCkSendWith_validAuthHybrid S P _ (.sendOPK u i) trivial u bundle m0 m1
        (projSlots0 hst) hVP0 (Prod.map id projSlots0 x) hMem
      exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith1Key; dsimp only
    split
    · intro x hx; simp at hx; subst hx; exact hV
    · intro x hx
      have hMem : Prod.map id projSlots0 x ∈
          support (Prod.map id projSlots0 <$>
            authCkSlotsSendWith S P sampAt (.sendNoOPK u i) u bundle m0 m1 hst) := by
        rw [support_map]; exact ⟨x, hx, rfl⟩
      rw [map_projSlots0_authCkSlotsSendWith S P sampAt
            (fun _ => sampAt (hst.slots.allocSend (.sendNoOPK u i)).1)
            (.sendNoOPK u i) u bundle m0 m1 hst (fun _ => rfl)] at hMem
      have hVPx := authCkSendWith_validAuthHybrid S P _ (.sendNoOPK u i) trivial u bundle m0 m1
        (projSlots0 hst) hVP0 (Prod.map id projSlots0 x) hMem
      exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  | recvOPK k j o msg =>
    unfold authCkSlotsStepWith1Key; dsimp only
    intro x hx
    have hMem : Prod.map id projSlots0 x ∈
        support (Prod.map id projSlots0 <$>
          authCkRecvWithSlots S P sampAt msg
            (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst) := by
      rw [support_map]; exact ⟨x, hx, rfl⟩
    rw [map_projSlots0_authCkSlotsRecvWith S P sampAt
          (fun _ => sampAt (hst.slots.allocRecv hst.recvCount).1)
          msg _ hst rfl] at hMem
    have hVPx := authCkRecvWith_validAuthHybrid S P _ msg _ (projSlots0 hst) hVP0
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvOPK_validAuthHybrid P k j o msg (projSlots0 hst) hVP0 prep hPrep res? recvCount')
      (Prod.map id projSlots0 x) hMem
    exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  | recvNoOPK k j l msg =>
    unfold authCkSlotsStepWith1Key; dsimp only
    intro x hx
    have hMem : Prod.map id projSlots0 x ∈
        support (Prod.map id projSlots0 <$>
          authCkRecvWithSlots S P sampAt msg
            (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst) := by
      rw [support_map]; exact ⟨x, hx, rfl⟩
    rw [map_projSlots0_authCkSlotsRecvWith S P sampAt
          (fun _ => sampAt (hst.slots.allocRecv hst.recvCount).1)
          msg _ hst rfl] at hMem
    have hVPx := authCkRecvWith_validAuthHybrid S P _ msg _ (projSlots0 hst) hVP0
      (fun prep hPrep res? recvCount' =>
        prepareAuthHybridRecvNoOPK_validAuthHybrid P k j l msg (projSlots0 hst) hVP0 prep hPrep res? recvCount')
      (Prod.map id projSlots0 x) hMem
    exact ⟨hVPx.1, hVPx.2, hVPx.3, hVPx.4, hVPx.5, hVPx.6⟩
  | initPrin u => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.initPrin u) hst hV
  | corruptIK u => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.corruptIK u) hst hV
  | genSPK u j => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.genSPK u j) hst hV
  | genOPK u j o => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.genOPK u j o) hst hV
  | registerKey sk => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.registerKey sk) hst hV
  | roQuery secrets => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.roQuery secrets) hst hV
  | roRootQuery rk dh => exact authCkStepWith_validAuthHybrid1Key S P sampAt (.roRootQuery rk dh) hst hV
  | revealDhSecrets => exact authCkStepWith_validAuthHybrid1Key S P sampAt .revealDhSecrets hst hV

theorem simulateQ_authCkPreSampleRunPrim1Key (S : Setup) (P : Primitives)
    (idx : Nat) (p : Bytes × Bytes) (A : AuthAdversary S) :
    simulateQ (primBaseImpl P) (authCkPreSampleRunPrim1Key S idx p A) =
      authCkSlotsPreSampleRun1Key S P idx p A := by
  unfold authCkPreSampleRunPrim1Key authCkSlotsPreSampleRun1Key
  simp only [simulateQ_bind, simulateQ_embedUnif]
  congr 1; funext secb
  rw [simulateQ_runWithPrimStep]
  have hInit : cacheAuthAdvKeysFixed P (AuthHybridStateFixed.empty S secb) =
      AuthHybridStateFixed.empty S secb := rfl
  conv_lhs => rw [← hInit]
  exact simulateQ_proj_inv_obs
    (cacheAuthAdvKeysFixed P)
    (ValidAuthHybrid S P)
    (fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith1Key S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst))
    (fun q => StateT.mk (fun hst =>
      simulateQ (primBaseImpl P) (authCkStepWithPrim1Key S (sampAtCkPrim idx p) q hst)))
    (fun q hst hV =>
      ⟨simulateQ_authCkSlotsStepWithPrim1Key S P (sampAtCkPrim idx p)
        (fun s => if s == idx then pure p else sampCkPair P (s < idx))
        (simulateQ_sampAtCkPrim P idx p) q hst hV,
       authCkSlotsStepWith_validAuthHybrid1Key S P
        (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst hV⟩)
    A.run
    (AuthHybridStateFixed.empty S secb)
    (validAuthHybrid_empty S P secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
    (fun y => simulateQ (primBaseImpl P) (finalizeAuthFixedPrim S secb y.1 y.2.toAuthHybridState))
    (fun x hVx => by
      have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P x.2) :=
        (validAuthHybrid_cacheAuthAdvKeysFixed P x.2).mpr hVx
      rw [simulateQ_finalizeAuthFixedPrim S P secb x.1
            (cacheAuthAdvKeysFixed P x.2).toAuthHybridState
            hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hVC.sessions_le hVC.validKem]
      exact finalizeAuthFixed_cacheAuthAdvKeys P secb x.1 x.2.toAuthHybridState)

private theorem simulateQ_authCkSlotsPreSampleRunPrim1Key (S : Setup) (P : Primitives)
    (idx : Nat) (p : Bytes × Bytes) (A : AuthAdversary S) :
    simulateQ (primBaseImpl P) (authCkPreSampleRunPrim1Key S idx p A) =
      authCkSlotsPreSampleRun1Key S P idx p A :=
  simulateQ_authCkPreSampleRunPrim1Key S P idx p A

private def CkSlotsFireAt (S : Setup) {κ : Type} (idx : Nat)
    (mx : SlotM κ (AuthResponse × AuthHybridStateFixed S)) : Prop :=
  ∀ y ∈ support (mx.run none), y.2.isSome = true → authCreationSlotFired idx y.1.2 = true

private theorem CkSlotsFireAt.pure {S : Setup} {κ : Type} (idx : Nat)
    (x : AuthResponse × AuthHybridStateFixed S) :
    CkSlotsFireAt S (κ := κ) idx (pure x) := by
  intro y hy hSome; simp [StateT.run_pure] at hy; subst hy; cases hSome

private theorem CkSlotsFireAt.liftComp {S : Setup} {κ : Type} (idx : Nat)
    (c : ProbComp (AuthResponse × AuthHybridStateFixed S)) :
    CkSlotsFireAt S (κ := κ) idx (liftM c) := by
  intro y hy hSome
  simp only [StateT.run_monadLift, monadLift_self, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hy
  rcases hy with ⟨_, _, rfl⟩; cases hSome

private theorem CkSlotsFireAt.liftComp_bind {S : Setup} {κ α : Type} (idx : Nat)
    (c : ProbComp α) {f : α → SlotM κ (AuthResponse × AuthHybridStateFixed S)}
    (hf : ∀ a, CkSlotsFireAt S idx (f a)) :
    CkSlotsFireAt S idx ((liftM c : SlotM κ α) >>= f) := by
  intro y hy hSome
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, _, hy'⟩; exact hf a y hy' hSome

private theorem CkSlotsFireAt.getCkAtSlot_bind_pure {S : Setup} (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (P : Primitives) (slotIdx : Nat)
    (f : Bytes × Bytes → AuthResponse × AuthHybridStateFixed S)
    (hLt : ∀ p, slotIdx < (f p).2.slots.nextSlot) :
    CkSlotsFireAt S idx (getCkAtSlot idx samp P slotIdx >>= fun p => Pure.pure (f p)) := by
  intro y hy hSome
  unfold getCkAtSlot at hy
  by_cases hEq : (slotIdx == idx) = true
  · simp only [hEq, ↓reduceIte, StateT.run_bind, SlotM.getSlot_run_none, bind_assoc, pure_bind,
      StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨p, _, rfl⟩; rw [beq_iff_eq] at hEq
    simp only [authCreationSlotFired, decide_eq_true_eq]; have := hLt p; omega
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind, StateT.run_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩; cases hSome

private theorem CkSlotsFireAt.ite {S : Setup} (idx : Nat) (c : Bool)
    (t e : SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S))
    (ht : CkSlotsFireAt S idx t) (he : CkSlotsFireAt S idx e) :
    CkSlotsFireAt S idx (if c then t else e) := by cases c <;> assumption

private theorem authCkSlotsStepSlot_fire1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : CkSlotsWf hst) :
    CkSlotsFireAt S idx (authCkSlotsStepSlot1Key S P idx samp q hst) := by
  have hSend : ∀ sid, IsSendSessionId S sid → ∀ u bundle m0 m1,
      CkSlotsFireAt S idx (authCkSlotsSendSlot S P idx samp sid u bundle m0 m1 hst) := by
    intro sid hSid u bundle m0 m1; unfold authCkSlotsSendSlot; dsimp only
    refine CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) ?_
    refine CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) ?_
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte]; exact CkSlotsFireAt.pure idx _
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      have hAlloc := allocSend_of_none hst.slots sid hSid (hWf.send_fresh sid (Bool.eq_false_iff.mpr hUsed))
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact CkSlotsFireAt.pure idx _
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩; dsimp only
        refine CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) ?_
        refine CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) ?_
        refine CkSlotsFireAt.liftComp_bind idx _ (fun ekASk => ?_)
        refine CkSlotsFireAt.liftComp_bind idx _ (fun kemCoins => ?_)
        refine CkSlotsFireAt.liftComp_bind idx _ (fun ephASk => ?_)
        refine CkSlotsFireAt.liftComp_bind idx _ (fun spqrCoins => ?_)
        refine CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) ?_
        cases P.kemEncaps bundle.pqspkB kemCoins with
        | none => exact CkSlotsFireAt.pure idx _
        | some pair =>
          rcases pair with ⟨ss, kemCt⟩; dsimp only
          refine CkSlotsFireAt.ite idx _ _ _ ?_ ?_
          · refine CkSlotsFireAt.liftComp_bind idx _ (fun drKey => ?_)
            refine CkSlotsFireAt.liftComp_bind idx _ (fun rk1 => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact CkSlotsFireAt.pure idx _
            | some spqrVal =>
              rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
              exact CkSlotsFireAt.getCkAtSlot_bind_pure idx samp P _ _
                (fun _ => by dsimp only [finishAuthSendCkSlots]; omega)
          · refine CkSlotsFireAt.liftComp_bind idx _ (fun ⟨drKey, roCache'⟩ => ?_)
            refine CkSlotsFireAt.liftComp_bind idx _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact CkSlotsFireAt.pure idx _
            | some spqrVal => rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; exact CkSlotsFireAt.pure idx _
  have hRecv : ∀ msg prep?, CkSlotsFireAt S idx (authCkSlotsRecvSlot S P idx samp msg prep? hst) := by
    intro msg prep?
    have hAlloc := allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh hst.recvCount (Nat.le_refl _))
    unfold authCkSlotsRecvSlot
    cases prep? with
    | none => exact CkSlotsFireAt.pure idx _
    | some prep =>
      dsimp only
      refine CkSlotsFireAt.ite idx _ _ _ ?_ ?_
      · cases prep.matchedSess? with
        | some s =>
          dsimp only
          refine CkSlotsFireAt.ite idx _ _ _ ?_ ?_
          · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact CkSlotsFireAt.pure idx _
            | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact CkSlotsFireAt.pure idx _
          · refine CkSlotsFireAt.liftComp_bind idx _ (fun rk1 => ?_)
            cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => exact CkSlotsFireAt.pure idx _
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              exact CkSlotsFireAt.getCkAtSlot_bind_pure idx samp P _ _
                (fun _ => by dsimp only [finishAuthRecvCkSlots]; omega)
        | none =>
          refine CkSlotsFireAt.liftComp_bind idx _ (fun drKey => ?_)
          refine CkSlotsFireAt.liftComp_bind idx _ (fun rk1 => ?_)
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => exact CkSlotsFireAt.pure idx _
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact CkSlotsFireAt.getCkAtSlot_bind_pure idx samp P _ _
              (fun _ => by dsimp only [finishAuthRecvCkSlots]; omega)
      · refine CkSlotsFireAt.liftComp_bind idx _ (fun ⟨drKey, roCache'⟩ => ?_)
        refine CkSlotsFireAt.liftComp_bind idx _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact CkSlotsFireAt.pure idx _
        | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; exact CkSlotsFireAt.pure idx _
  cases q <;> unfold authCkSlotsStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    exact CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) (hSend (.sendOPK u i) trivial u bundle m0 m1)
  case sendNoOPK u i bundle m0 m1 =>
    exact CkSlotsFireAt.ite idx _ _ _ (CkSlotsFireAt.pure idx _) (hSend (.sendNoOPK u i) trivial u bundle m0 m1)
  case recvOPK k j o msg => exact hRecv msg _
  case recvNoOPK k j l msg => exact hRecv msg _
  all_goals exact CkSlotsFireAt.liftComp idx _

private theorem contains_cons_eq_false {S : Setup} {sid sid' : SessionId S} {l : List (SessionId S)}
    (h : (sid :: l).contains sid' = false) : sid' ≠ sid ∧ l.contains sid' = false := by
  refine ⟨fun hEq => ?_, Bool.eq_false_iff.mpr fun hMem => ?_⟩
  · subst hEq
    have hc : (sid' :: l).contains sid' = true := List.contains_iff_mem.mpr (List.mem_cons_self ..)
    rw [h] at hc; cases hc
  · have hc : (sid :: l).contains sid' = true :=
      List.contains_iff_mem.mpr (List.mem_cons_of_mem sid (List.contains_iff_mem.mp hMem))
    rw [h] at hc; cases hc

private theorem forall_sup_pure {α : Type} (a : α) (Q : α → Prop) (ha : Q a) :
    ∀ x ∈ support (pure a : ProbComp α), Q x := by
  intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact ha

private theorem forall_sup_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (Q : β → Prop) (hf : ∀ a, ∀ y ∈ support (f a), Q y) :
    ∀ y ∈ support (mx >>= f), Q y := by
  intro y hy; simp only [MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, _, hy'⟩; exact hf a y hy'

private theorem forall_sup_ite {α : Type} (c : Bool) (t e : ProbComp α) (Q : α → Prop)
    (ht : ∀ x ∈ support t, Q x) (he : ∀ x ∈ support e, Q x) :
    ∀ x ∈ support (if c then t else e), Q x := by
  cases c <;> [exact he; exact ht]

private theorem support_authCkSlotsStepWith1Key_wf {S : Setup} (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes)) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : CkSlotsWf hst) :
    ∀ x ∈ support (authCkSlotsStepWith1Key S P sampAt q hst),
      CkSlotsWf x.2 ∧
      hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
      x.2.slots.nextSlot ≤ hst.slots.nextSlot + (if isAuthSessQueryB (Sum.inr q) then 1 else 0) := by
  have hStay : CkSlotsWf hst ∧ hst.slots.nextSlot ≤ hst.slots.nextSlot ∧
      hst.slots.nextSlot ≤ hst.slots.nextSlot + 1 :=
    ⟨hWf, Nat.le_refl _, Nat.le_succ _⟩
  have hSendWf : ∀ sid (hSend : IsSendSessionId S sid) u bundle m0 m1,
      ∀ x ∈ support (authCkSlotsSendWith S P sampAt sid u bundle m0 m1 hst),
        CkSlotsWf x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
        x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 := by
    intro sid hSend u bundle m0 m1
    unfold authCkSlotsSendWith; dsimp only
    refine forall_sup_ite _ _ _ _ (forall_sup_pure _ _ hStay) ?_
    refine forall_sup_ite _ _ _ _ (forall_sup_pure _ _ hStay) ?_
    by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hUsed, ↓reduceIte]; exact forall_sup_pure _ _ hStay
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      have hUsedF : hst.toAuthHybridState.base.usedSendSessions.contains sid = false :=
        Bool.eq_false_iff.mpr hUsed
      obtain ⟨_, hNext, hRecvTbl, hLookup⟩ :=
        allocSend_of_none hst.slots sid hSend (hWf.send_fresh sid hUsedF)
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact forall_sup_pure _ _ hStay
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩; dsimp only
        refine forall_sup_ite _ _ _ _ (forall_sup_pure _ _ hStay) ?_
        refine forall_sup_ite _ _ _ _ (forall_sup_pure _ _ hStay) ?_
        refine forall_sup_bind _ _ _ (fun ekASk => ?_)
        refine forall_sup_bind _ _ _ (fun kemCoins => ?_)
        refine forall_sup_bind _ _ _ (fun ephASk => ?_)
        refine forall_sup_bind _ _ _ (fun spqrCoins => ?_)
        refine forall_sup_ite _ _ _ _ (forall_sup_pure _ _ hStay) ?_
        cases P.kemEncaps bundle.pqspkB kemCoins with
        | none => exact forall_sup_pure _ _ hStay
        | some pair =>
          rcases pair with ⟨ss, kemCt⟩; dsimp only
          refine forall_sup_ite _ _ _ _ ?_ ?_
          · refine forall_sup_bind _ _ _ (fun drKey => ?_)
            refine forall_sup_bind _ _ _ (fun rk1 => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact forall_sup_pure _ _ hStay
            | some spqrVal =>
              rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
              refine forall_sup_bind _ _ _ (fun p => forall_sup_pure _ _ ?_)
              refine ⟨⟨fun sid' hCont => ?_, fun rc hRc => ?_⟩, ?_, ?_⟩
              · unfold finishAuthSendCkSlots finishAuthSendCk finishAuthHybridSend at hCont ⊢
                dsimp only at hCont ⊢
                obtain ⟨hne, hCont0⟩ := contains_cons_eq_false hCont
                rw [hLookup sid']; simp only [hne, ↓reduceIte]
                exact hWf.send_fresh sid' hCont0
              · unfold finishAuthSendCkSlots finishAuthSendCk at hRc ⊢
                dsimp only at hRc ⊢
                rw [hRecvTbl]; exact hWf.recv_fresh rc hRc
              · simp [finishAuthSendCkSlots, hNext]
              · simp [finishAuthSendCkSlots, hNext]
          · refine forall_sup_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
            refine forall_sup_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
            cases P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => exact forall_sup_pure _ _ hStay
            | some spqrVal =>
              rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
              refine forall_sup_pure _ _ ⟨⟨fun sid' hCont => ?_, fun rc hRc => hWf.recv_fresh rc hRc⟩,
                Nat.le_refl _, Nat.le_succ _⟩
              unfold finishAuthHybridSend at hCont; dsimp only at hCont
              exact hWf.send_fresh sid' (contains_cons_eq_false hCont).2
  have hRecvWf : ∀ msg (prep? : Option (PreparedAuthRecv S))
      (hUsedEq : ∀ prep res?, prep? = some prep →
        (prep.finish res?).2.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions),
      ∀ x ∈ support (authCkRecvWithSlots S P sampAt msg prep? hst),
        CkSlotsWf x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
        x.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 := by
    intro msg prep? hUsedEq x hx
    unfold authCkRecvWithSlots at hx
    cases prep? with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨⟨hWf.send_fresh, fun rc hRc => hWf.recv_fresh rc (Nat.le_of_succ_le hRc)⟩,
             Nat.le_refl _, Nat.le_succ _⟩
    | some prep =>
      dsimp only at hx
      have hAlloc : ∀ drKey rk1 spqrSalt? p,
          let slots' := (hst.slots.allocRecv hst.recvCount).2
          let y := finishAuthRecvCkSlots P msg prep drKey rk1 spqrSalt? (hst.recvCount + 1) p slots'
          CkSlotsWf y.2 ∧ hst.slots.nextSlot ≤ y.2.slots.nextSlot ∧
          y.2.slots.nextSlot ≤ hst.slots.nextSlot + 1 := by
        intro drKey rk1 spqrSalt? p
        obtain ⟨_, hNext, hLookup, hRecvTbl⟩ :=
          allocRecv_of_none (S := S) hst.slots hst.recvCount (hWf.recv_fresh hst.recvCount (Nat.le_refl _))
        refine ⟨⟨fun sid' hCont => ?_, fun rc hRc => ?_⟩, ?_, ?_⟩
        · unfold finishAuthRecvCkSlots finishAuthRecvCk at hCont ⊢
          dsimp only at hCont ⊢
          rw [hUsedEq prep _ rfl] at hCont
          rw [hLookup sid']; exact hWf.send_fresh sid' hCont
        · unfold finishAuthRecvCkSlots finishAuthRecvCk at hRc ⊢
          dsimp only at hRc ⊢
          have hNeRc : rc ≠ hst.recvCount := by omega
          rw [hRecvTbl rc]
          simp only [hNeRc, ↓reduceIte]
          exact hWf.recv_fresh rc (Nat.le_of_succ_le hRc)
        · simp [finishAuthRecvCkSlots, hNext]
        · simp [finishAuthRecvCkSlots, hNext]
      have hKeep : ∀ res?,
          let (resp, hst') := prep.finish res?
          let z : AuthHybridStateFixed S :=
            { toAuthHybridState := hst', recvCount := hst.recvCount + 1, slots := hst.slots }
          CkSlotsWf z ∧ hst.slots.nextSlot ≤ z.slots.nextSlot ∧
          z.slots.nextSlot ≤ hst.slots.nextSlot + 1 := by
        intro res?
        refine ⟨⟨fun sid' hCont => ?_, fun rc hRc => hWf.recv_fresh rc (Nat.le_of_succ_le hRc)⟩,
                Nat.le_refl _, Nat.le_succ _⟩
        dsimp only at hCont
        rw [hUsedEq prep res? rfl] at hCont
        exact hWf.send_fresh sid' hCont
      split at hx
      · cases hMatch : prep.matchedSess? with
        | some s =>
          simp only [hMatch] at hx; split at hx
          · cases hSpqr : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              simp only [hSpqr, support_pure, Set.mem_singleton_iff] at hx; subst hx
              exact hKeep none
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              simp only [hSpqr, support_pure, Set.mem_singleton_iff] at hx; subst hx
              exact hKeep _
          · simp only [MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨rk1, _, hx⟩
            cases hSpqr : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              simp only [hSpqr, support_pure, Set.mem_singleton_iff] at hx; subst hx
              exact hKeep none
            | some pqr =>
              rcases pqr with ⟨_, spqrSalt?⟩
              simp only [hSpqr, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨p, _, rfl⟩; exact hAlloc s.drKey rk1 spqrSalt? p
        | none =>
          simp only [hMatch, MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨drKey, _, rk1, _, hx⟩
          cases hSpqr : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            simp only [hSpqr, support_pure, Set.mem_singleton_iff] at hx; subst hx
            exact hKeep none
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            simp only [hSpqr, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨p, _, rfl⟩; exact hAlloc drKey rk1 spqrSalt? p
      · simp only [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
        cases hSpqr : P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          simp only [hSpqr, support_pure, Set.mem_singleton_iff] at hx; subst hx
          exact hKeep none
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          simp only [hSpqr, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hKeep _
  have hPres : ∀ q' : AuthQuery S,
      isAuthSessQueryB (Sum.inr q') = false →
      ∀ x ∈ support (authCkOtherStep1Key S P q' hst),
        CkSlotsWf x.2 ∧ hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
        x.2.slots.nextSlot ≤ hst.slots.nextSlot := by
    intro q' hNotSess x hx
    have hUsedPres : PreservesAt AuthState.usedSendSessions hst.toAuthHybridState.base
        (pqxdhAuthImpl1KeyG true true S P q') := by
      cases q' with
      | sendOPK _ _ _ _ _ => cases hNotSess
      | sendNoOPK _ _ _ _ _ => cases hNotSess
      | recvOPK _ _ _ _ => cases hNotSess
      | recvNoOPK _ _ _ _ => cases hNotSess
      | _ =>
        unfold pqxdhAuthImpl1KeyG; dsimp only
        repeat (first
          | with_reducible apply PreservesAt.pure
          | with_reducible apply PreservesAt.get_bind
          | (with_reducible apply PreservesAt.liftM_bind; intro _)
          | ((with_reducible apply PreservesAt.set_bind); rfl)
          | split)
    unfold authCkOtherStep1Key at hx
    split at hx
    · simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨hWf, Nat.le_refl _, Nat.le_refl _⟩
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, base'⟩, hbase, rfl⟩
      have hUEq : base'.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions :=
        hUsedPres (resp, base') hbase
      exact ⟨⟨fun sid' hCont => hWf.send_fresh sid' (by simpa [hUEq] using hCont), hWf.recv_fresh⟩,
             Nat.le_refl _, Nat.le_refl _⟩
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith1Key; dsimp only [isAuthSessQueryB, ↓reduceIte]
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hStay
    · exact hSendWf (.sendOPK u i) trivial u bundle m0 m1
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkSlotsStepWith1Key; dsimp only [isAuthSessQueryB, ↓reduceIte]
    split
    · intro x hx; simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hStay
    · exact hSendWf (.sendNoOPK u i) trivial u bundle m0 m1
  | recvOPK k j o msg =>
    unfold authCkSlotsStepWith1Key; dsimp only [isAuthSessQueryB, ↓reduceIte]
    exact hRecvWf msg _ (fun prep res? hPrep =>
      prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg hst.toAuthHybridState hPrep res?)
  | recvNoOPK k j l msg =>
    unfold authCkSlotsStepWith1Key; dsimp only [isAuthSessQueryB, ↓reduceIte]
    exact hRecvWf msg _ (fun prep res? hPrep =>
      prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg hst.toAuthHybridState hPrep res?)
  | initPrin u => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.initPrin u) rfl
  | corruptIK u => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.corruptIK u) rfl
  | genSPK u j => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.genSPK u j) rfl
  | genOPK u j o => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.genOPK u j o) rfl
  | registerKey sk => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.registerKey sk) rfl
  | roQuery s => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.roQuery s) rfl
  | roRootQuery rk dh => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres (.roRootQuery rk dh) rfl
  | revealDhSecrets => simpa [authCkSlotsStepWith1Key, isAuthSessQueryB] using hPres .revealDhSecrets rfl

private theorem authCkSlotsSendWith_congr_slot {S : Setup} (P : Primitives)
    (sampAt1 sampAt2 : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hEq : hst.toAuthHybridState.base.usedSendSessions.contains sid = false →
      sampAt1 (hst.slots.allocSend sid).1 = sampAt2 (hst.slots.allocSend sid).1) :
    authCkSlotsSendWith S P sampAt1 sid u bundle m0 m1 hst =
      authCkSlotsSendWith S P sampAt2 sid u bundle m0 m1 hst := by
  by_cases hU : hst.toAuthHybridState.base.usedSendSessions.contains sid = false
  · unfold authCkSlotsSendWith
    simp only [hEq hU]
  · have hUT : hst.toAuthHybridState.base.usedSendSessions.contains sid = true := by
      cases h : hst.toAuthHybridState.base.usedSendSessions.contains sid <;> simp_all
    unfold authCkSlotsSendWith
    simp only [hUT, ↓reduceIte]

private theorem authCkRecvWithSlots_congr_slot {S : Setup} (P : Primitives)
    (sampAt1 sampAt2 : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S)
    (hEq : sampAt1 (hst.slots.allocRecv hst.recvCount).1 =
      sampAt2 (hst.slots.allocRecv hst.recvCount).1) :
    authCkRecvWithSlots S P sampAt1 msg prep? hst =
      authCkRecvWithSlots S P sampAt2 msg prep? hst := by
  unfold authCkRecvWithSlots
  cases prep? with
  | none => rfl
  | some prep =>
    dsimp only
    simp only [hEq]

private theorem authCkSlotsStepWith_after1Key (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (k : Bytes × Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : CkSlotsWf hst) (hFired : authCreationSlotFired idx hst = true) :
    authCkSlotsStepWith1Key S P (fun s => if s == idx then pure k else sampCkPair P (s < idx)) q hst =
      authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst ∧
    ∀ x ∈ support
      (authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst),
      authCreationSlotFired idx x.2 = true := by
  have hIdxLt : idx < hst.slots.nextSlot := by
    simpa [authCreationSlotFired, decide_eq_true_eq] using hFired
  refine ⟨?_, fun x hx => ?_⟩
  · cases q <;> unfold authCkSlotsStepWith1Key <;> dsimp only
    case sendOPK u i bundle m0 m1 =>
      split; · rfl
      refine authCkSlotsSendWith_congr_slot P _ _ (.sendOPK u i) u bundle m0 m1 hst (fun hFresh => ?_)
      obtain ⟨hS1, _, _, _⟩ := allocSend_of_none hst.slots (.sendOPK u i) trivial (hWf.send_fresh _ hFresh)
      have hne : (hst.slots.allocSend (.sendOPK u i)).1 ≠ idx := by omega
      simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, lt_cutoff_bool_eq b hne]
    case sendNoOPK u i bundle m0 m1 =>
      split; · rfl
      refine authCkSlotsSendWith_congr_slot P _ _ (.sendNoOPK u i) u bundle m0 m1 hst (fun hFresh => ?_)
      obtain ⟨hS1, _, _, _⟩ := allocSend_of_none hst.slots (.sendNoOPK u i) trivial (hWf.send_fresh _ hFresh)
      have hne : (hst.slots.allocSend (.sendNoOPK u i)).1 ≠ idx := by omega
      simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, lt_cutoff_bool_eq b hne]
    case recvOPK k' j o msg =>
      refine authCkRecvWithSlots_congr_slot P _ _ msg _ hst ?_
      obtain ⟨hR1, _, _, _⟩ := allocRecv_of_none (S := S) hst.slots hst.recvCount
        (hWf.recv_fresh hst.recvCount (Nat.le_refl _))
      have hne : (hst.slots.allocRecv hst.recvCount).1 ≠ idx := by omega
      simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, lt_cutoff_bool_eq b hne]
    case recvNoOPK k' j l msg =>
      refine authCkRecvWithSlots_congr_slot P _ _ msg _ hst ?_
      obtain ⟨hR1, _, _, _⟩ := allocRecv_of_none (S := S) hst.slots hst.recvCount
        (hWf.recv_fresh hst.recvCount (Nat.le_refl _))
      have hne : (hst.slots.allocRecv hst.recvCount).1 ≠ idx := by omega
      simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte, lt_cutoff_bool_eq b hne]
  · have hMono := (support_authCkSlotsStepWith1Key_wf P _ q hst hWf x hx).2.1
    simpa [authCreationSlotFired, decide_eq_true_eq] using Nat.lt_of_lt_of_le hIdxLt hMono

private theorem evalDist_preSample_authCkSlots_eq_cutoff1Key (S : Setup) (P : Primitives)
    (idx : Nat) (b : Bool) (A : AuthAdversary S) :
    𝒟[sampCkPair P (!b) >>= fun p => authCkSlotsPreSampleRun1Key S P idx p A] =
      𝒟[authCkSlotsCutoffExp1Key S P (if b then idx else idx + 1) A] := by
  unfold authCkSlotsPreSampleRun1Key authCkSlotsCutoffExp1Key
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep_inv
    (sampCkPair P (!b))
    CkSlotsWf
    (authCreationSlotFired idx)
    (fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst))
    (fun p q => StateT.mk (fun hst =>
      authCkSlotsStepWith1Key S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst))
    (authCkSlotsStepSlot1Key S P idx (sampCkPair P (!b)))
    (authCkSlotsStepSlot_slotComp1Key S P idx (sampCkPair P (!b)))
    (authCkSlotsStepSlot_run'_some1Key S P idx (sampCkPair P (!b)))
    (fun q hst g _ => by
      dsimp only [StateT.run_mk]
      rw [authCkSlotsStepSlot_run'_none_eq1Key S P idx b q hst])
    (fun p q hst hWf hFired => authCkSlotsStepWith_after1Key S P idx b p q hst hWf hFired)
    (fun q hst y hWf hy hSome => authCkSlotsStepSlot_fire1Key S P idx (sampCkPair P (!b)) q hst hWf y hy hSome)
    (fun q hst hWf x hx => (support_authCkSlotsStepWith1Key_wf P _ q hst hWf x hx).1)
    (fun q hst hWf => SlotM.wf_run_none_of_run'_eq _ _
      (authCkSlotsStepSlot_run'_none_eq1Key S P idx b q hst)
      (fun x hx => (support_authCkSlotsStepWith1Key_wf P _ q hst hWf x hx).1))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (ckSlotsWf_empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

private theorem evalDist_authCkSlotsCutoffExp_zero_eq_g3_6_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[authCkSlotsCutoffExp1Key S P 0 A] = 𝒟[authFixedExpAtStage1Key .g3_6 S P A] := by
  rw [← evalDist_authCkCutoffExp_zero_eq_g3_6_1Key S P A]
  unfold authCkSlotsCutoffExp1Key authCkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_proj_inv
    (projSlots0 (S := S))
    (fun _ => True)
    (fun q => StateT.mk (fun hst => authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < 0)) q hst))
    (fun q => StateT.mk (fun hst => authCkStepWith1Key S P (fun s => sampCkPair P (s < 0)) q hst))
    (fun q hst _ => ⟨fun k => by
      dsimp only [StateT.run_mk]
      have hMap : Prod.map id projSlots0 <$>
          authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < 0)) q hst =
          authCkStepWith1Key S P (fun s => sampCkPair P (s < 0)) q (projSlots0 hst) := by
        cases q <;> unfold authCkSlotsStepWith1Key authCkStepWith1Key <;> dsimp only
        case sendOPK u i bundle m0 m1 =>
          split; · simp [Prod.map]
          exact map_projSlots0_authCkSlotsSendWith S P _ _ (.sendOPK u i) u bundle m0 m1 hst (fun _ => by simp)
        case sendNoOPK u i bundle m0 m1 =>
          split; · simp [Prod.map]
          exact map_projSlots0_authCkSlotsSendWith S P _ _ (.sendNoOPK u i) u bundle m0 m1 hst (fun _ => by simp)
        case recvOPK k' j o msg =>
          exact map_projSlots0_authCkSlotsRecvWith S P _ _ msg _ hst (by simp)
        case recvNoOPK k' j l msg =>
          exact map_projSlots0_authCkSlotsRecvWith S P _ _ msg _ hst (by simp)
        all_goals exact map_projSlots0_authCkOtherStep1Key S P _ hst
      rw [← hMap, bind_map_left]; rfl, fun _ _ => trivial⟩)
    A.run
    (AuthHybridStateFixed.empty S secb)
    trivial
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

private theorem evalDist_authCkSlotsCutoffExp_min_eq_g3_7_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authCkSlotsCutoffExp1Key S P (min b.q_total S.N_sess_tot) A.1] =
      𝒟[authFixedExpAtStage1Key .g3_7 S P A.1] := by
  unfold authCkSlotsCutoffExp1Key authFixedExpAtStage1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  let implAllTrue : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst => authCkStepWith1Key S P (fun _ => sampCkPair P true) q hst)
  let fullAllTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + implAllTrue
  have h1 :
      𝒟[(simulateQ
          ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
            fun q => StateT.mk (fun hst =>
              authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < min b.q_total S.N_sess_tot)) q hst))
          A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
        fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] =
      𝒟[(simulateQ fullAllTrue A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
        fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] :=
    evalDist_simulateQ_proj_inv_bound
      (projSlots0 (S := S))
      CkSlotsWf
      (fun hst => hst.slots.nextSlot)
      (isAuthSessQueryB (S := S))
      (fun _ => rfl)
      (min b.q_total S.N_sess_tot)
      (fun q => StateT.mk (fun hst =>
        authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < min b.q_total S.N_sess_tot)) q hst))
      implAllTrue
      (fun q hst hWf hLt => ⟨fun k => by
        dsimp only [StateT.run_mk, implAllTrue]
        have hMap : Prod.map id projSlots0 <$>
            authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < min b.q_total S.N_sess_tot)) q hst =
            authCkStepWith1Key S P (fun _ => sampCkPair P true) q (projSlots0 hst) := by
          cases q <;> unfold authCkSlotsStepWith1Key authCkStepWith1Key <;> dsimp only
          case sendOPK u i bundle m0 m1 =>
            split; · simp [Prod.map]
            refine map_projSlots0_authCkSlotsSendWith S P _ _ (.sendOPK u i) u bundle m0 m1 hst (fun hNotUsed => ?_)
            have hFresh : hst.toAuthHybridState.base.usedSendSessions.contains (.sendOPK u i) = false :=
              Bool.eq_false_iff.mpr hNotUsed
            obtain ⟨hS1, _, _, _⟩ := allocSend_of_none hst.slots (.sendOPK u i) trivial (hWf.send_fresh _ hFresh)
            have hSlotLt : (hst.slots.allocSend (.sendOPK u i)).1 < min b.q_total S.N_sess_tot :=
              hS1 ▸ hLt rfl
            simp [hSlotLt]
          case sendNoOPK u i bundle m0 m1 =>
            split; · simp [Prod.map]
            refine map_projSlots0_authCkSlotsSendWith S P _ _ (.sendNoOPK u i) u bundle m0 m1 hst (fun hNotUsed => ?_)
            have hFresh : hst.toAuthHybridState.base.usedSendSessions.contains (.sendNoOPK u i) = false :=
              Bool.eq_false_iff.mpr hNotUsed
            obtain ⟨hS1, _, _, _⟩ := allocSend_of_none hst.slots (.sendNoOPK u i) trivial (hWf.send_fresh _ hFresh)
            have hSlotLt : (hst.slots.allocSend (.sendNoOPK u i)).1 < min b.q_total S.N_sess_tot :=
              hS1 ▸ hLt rfl
            simp [hSlotLt]
          case recvOPK k' j o msg =>
            refine map_projSlots0_authCkSlotsRecvWith S P _ _ msg _ hst ?_
            obtain ⟨hR1, _, _, _⟩ := allocRecv_of_none (S := S) hst.slots hst.recvCount
              (hWf.recv_fresh hst.recvCount (Nat.le_refl _))
            have hSlotLt : (hst.slots.allocRecv hst.recvCount).1 < min b.q_total S.N_sess_tot :=
              hR1 ▸ hLt rfl
            simp [hSlotLt]
          case recvNoOPK k' j l msg =>
            refine map_projSlots0_authCkSlotsRecvWith S P _ _ msg _ hst ?_
            obtain ⟨hR1, _, _, _⟩ := allocRecv_of_none (S := S) hst.slots hst.recvCount
              (hWf.recv_fresh hst.recvCount (Nat.le_refl _))
            have hSlotLt : (hst.slots.allocRecv hst.recvCount).1 < min b.q_total S.N_sess_tot :=
              hR1 ▸ hLt rfl
            simp [hSlotLt]
          all_goals exact map_projSlots0_authCkOtherStep1Key S P _ hst
        rw [← hMap, bind_map_left]; rfl,
        fun x hx =>
          let hw := support_authCkSlotsStepWith1Key_wf P _ q hst hWf x hx
          ⟨hw.1, hw.2.2⟩⟩)
      A.1.run
      (min b.q_total S.N_sess_tot)
      (isQueryBoundP_isAuthSessQueryB_min S b A)
      (AuthHybridStateFixed.empty S secb)
      (ckSlotsWf_empty S secb)
      (by simp [AuthHybridStateFixed.empty])
      (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
  have hBoundRecv :
      OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  have h2 :
      𝒟[(simulateQ
          ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S) ProbComp) +
            pqxdhAuthHybridFixedImpl1Key .g3_7 true true S P)
          A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
        fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] =
      𝒟[(simulateQ fullAllTrue A.1.run).run (AuthHybridStateFixed.empty S secb) >>=
        fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState] :=
    evalDist_simulateQ_proj_inv_bound
      (eraseAuthFixedCk1_0 (S := S))
      (fun _ => True)
      (fun hst => hst.recvCount)
      (isAuthRecvQueryB (S := S))
      (fun _ => rfl)
      S.N_recv_tot
      (pqxdhAuthHybridFixedImpl1Key .g3_7 true true S P)
      implAllTrue
      (fun q hst hInv hLt =>
        let ⟨hDist, hSupp⟩ := step_g3_7_eq_authCkStepWith_end1Key P q hst hInv hLt
        ⟨fun k => by
          rw [hDist k]
          dsimp only [StateT.run_mk, implAllTrue]
          have hEqStep :
              authCkStepWith1Key S P (fun s => sampCkPair P (s < S.N_sess_tot)) q (eraseAuthFixedCk1_0 hst) =
              authCkStepWith1Key S P (fun _ => sampCkPair P true) q (eraseAuthFixedCk1_0 hst) := by
            cases q <;> unfold authCkStepWith1Key <;> dsimp only
            case sendOPK u i bundle m0 m1 =>
              split; · rfl
              apply authCkSendWith_congr_slot
              have hSLt : sessionSlotIndex (.sendOPK u i : SessionId S) < S.N_send_tot :=
                sendSlotIndex?_lt (sid := (.sendOPK u i : SessionId S)) rfl
              have hTot : sessionSlotIndex (.sendOPK u i : SessionId S) < S.N_sess_tot := by
                unfold Setup.N_sess_tot; omega
              simp [hTot]
            case sendNoOPK u i bundle m0 m1 =>
              split; · rfl
              apply authCkSendWith_congr_slot
              have hSLt : sessionSlotIndex (.sendNoOPK u i : SessionId S) < S.N_send_tot :=
                sendSlotIndex?_lt (sid := (.sendNoOPK u i : SessionId S)) rfl
              have hTot : sessionSlotIndex (.sendNoOPK u i : SessionId S) < S.N_sess_tot := by
                unfold Setup.N_sess_tot; omega
              simp [hTot]
            case recvOPK k' j o msg =>
              apply authCkRecvWith_congr_slot
              have hRLt := hLt rfl
              have hTot : S.N_send_tot + (eraseAuthFixedCk1_0 hst).recvCount < S.N_sess_tot := by
                change S.N_send_tot + hst.recvCount < S.N_sess_tot
                unfold Setup.N_sess_tot; omega
              simp [hTot]
            case recvNoOPK k' j l msg =>
              apply authCkRecvWith_congr_slot
              have hRLt := hLt rfl
              have hTot : S.N_send_tot + (eraseAuthFixedCk1_0 hst).recvCount < S.N_sess_tot := by
                change S.N_send_tot + hst.recvCount < S.N_sess_tot
                unfold Setup.N_sess_tot; omega
              simp [hTot]
          rw [hEqStep],
          hSupp⟩)
      A.1.run
      S.N_recv_tot
      hBoundRecv
      (AuthHybridStateFixed.empty S secb)
      trivial
      (by simp [AuthHybridStateFixed.empty])
      (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
  exact h1.trans h2.symm

theorem hop_G3_6_G3_7_1Key (S : Setup) : AuthHopG3_6G3_7Stmt1Key S (prfCkReductionAuthFixed1Key S) := by
  intro P _hP b A
  change |(𝒟[authFixedExpAtStage1Key .g3_6 S P A.1].boolBias).toReal -
          (𝒟[authFixedExpAtStage1Key .g3_7 S P A.1].boolBias).toReal| ≤
    2 * (S.N_sess_tot : ℝ) * (𝒟[prfCkExp P (prfCkReductionAuthFixed1Key S b A)].boolBias).toReal
  rw [← evalDist_authCkSlotsCutoffExp_zero_eq_g3_6_1Key S P A.1,
      ← evalDist_authCkSlotsCutoffExp_min_eq_g3_7_1Key S P b A]
  let M := min b.q_total S.N_sess_tot
  have hPrfEq :
      𝒟[prfCkExp P (prfCkReductionAuthFixed1Key S b A)] =
        𝒟[do
          let ch ← $ᵗ Bool
          let z ← if ch then (sampleIndexRange M >>= fun idx =>
                    sampCkPair P false >>= fun p => authCkSlotsPreSampleRun1Key S P idx p A.1)
                  else (sampleIndexRange M >>= fun idx =>
                    sampCkPair P true >>= fun p => authCkSlotsPreSampleRun1Key S P idx p A.1)
          return (ch == z)] := by
    rw [prfCkExp_eq_sampCkPair]
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun ch _ => ?_)
    unfold prfCkReductionAuthFixed1Key
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_authCkSlotsPreSampleRunPrim1Key, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap (sampCkPair P (!ch)) (sampleIndexRange M)]
    cases ch <;> simp only [Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true,
      Bool.beq_comm]
  have hBoundM :
      |(𝒟[authCkSlotsCutoffExp1Key S P 0 A.1].boolBias).toReal -
        (𝒟[authCkSlotsCutoffExp1Key S P M A.1].boolBias).toReal| ≤
      2 * (M : ℝ) * (𝒟[prfCkExp P (prfCkReductionAuthFixed1Key S b A)].boolBias).toReal := by
    rw [hPrfEq]
    exact abs_sub_boolBias_le_two_mul_sampleIndexRange_coin_game
      M
      (fun k => authCkSlotsCutoffExp1Key S P k A.1)
      (fun idx => sampCkPair P false >>= fun p => authCkSlotsPreSampleRun1Key S P idx p A.1)
      (fun idx => sampCkPair P true >>= fun p => authCkSlotsPreSampleRun1Key S P idx p A.1)
      (fun idx _ => by
        have h := evalDist_preSample_authCkSlots_eq_cutoff1Key S P idx true A.1
        simp only [Bool.not_true, ↓reduceIte] at h
        rw [h])
      (fun idx _ => by
        have h := evalDist_preSample_authCkSlots_eq_cutoff1Key S P idx false A.1
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h
        rw [h])
  refine le_trans hBoundM (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
  have hMLe : (M : ℝ) ≤ (S.N_sess_tot : ℝ) := by exact_mod_cast Nat.min_le_right b.q_total S.N_sess_tot
  linarith

end AuthSubHops1to3

end SignalPqxdh.Security
