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
public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3E
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `PrfMsgKeys` Sub-Hop (`G3.7` to `G3.8`)

Connects the single-slot `PrfMsgKeys` reduction worlds to cutoff experiments and proves the
single-identity-key sub-hop bound `hop_G3_7_G3_8_1Key` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
open OracleSpec OracleComp MeasureTheory ENNReal BigOperators
namespace SignalPqxdh.Security
open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
namespace AuthSubHops1to3

theorem support_authCkOtherStep_props1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hNoSendOPK : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (hNoSendNoOPK : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1)
    (hNoRecvOPK : ∀ k j o m, q ≠ .recvOPK k j o m)
    (hNoRecvNoOPK : ∀ k j l m, q ≠ .recvNoOPK k j l m) :
    ∀ x ∈ support (authCkOtherStep1Key S P q hst),
      x.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
      x.2.toAuthHybridState.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions ∧
      x.2.mkSaltCache = hst.mkSaltCache ∧
      x.2.recvCount = hst.recvCount := by
  have hPres : PreservesAt AuthState.usedSendSessions hst.toAuthHybridState.base
      (pqxdhAuthImpl1KeyG true true S P q) := by
    cases q with
    | sendOPK u i b m0 m1 => exact False.elim (hNoSendOPK u i b m0 m1 rfl)
    | sendNoOPK u i b m0 m1 => exact False.elim (hNoSendNoOPK u i b m0 m1 rfl)
    | recvOPK k j o msg => exact False.elim (hNoRecvOPK k j o msg rfl)
    | recvNoOPK k j l msg => exact False.elim (hNoRecvNoOPK k j l msg rfl)
    | _ =>
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
  intro y hy
  unfold authCkOtherStep1Key at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩
  exact ⟨rfl, hPres (resp, base') hbase, rfl, rfl⟩

theorem authMkStepRedProb_evalPrfMkReal1Key {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hWF : WellFormedPrimitivesδ P)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkTrue S P idx mkSeedStar st) :
    ((prfMkAuthImpl1Key S P idx mkSeedStar q).run (restoreAuthFixedMkAtIdx idx mkSeedStar st.1.1) =
      Prod.map id (fun ((hst', _), _) => restoreAuthFixedMkAtIdx idx mkSeedStar hst') <$>
        ((authMkRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar) q).run st)) ∧
    (∀ x ∈ support ((authMkRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar) q).run st),
      InvMkTrue S P idx mkSeedStar x.2) := by
  rcases st with ⟨⟨hst, sentChal⟩, cache⟩
  dsimp only [prfMkAuthImpl1Key, authMkRedProbImpl1Key, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepWith1Key authMkStepRedProb1Key
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
    unfold authMkStepWith1Key authMkStepRedProb1Key
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
    unfold authMkStepWith1Key authMkStepRedProb1Key
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
    unfold authMkStepWith1Key authMkStepRedProb1Key
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
    unfold authMkStepWith1Key authMkStepRedProb1Key
    dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · rw [authCkOtherStep_restoreAuthFixedMkAtIdx1Key]
      simp [Prod.map, map_eq_bind_pure_comp]
      rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props1Key P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      refine ⟨fun hS => ⟨(hInv.sentChal_imp hS).1, ?_⟩,
              hOther.1 ▸ hInv.ideal_msgKeys, hOther.2.2.1 ▸ hInv.cache_msgKeys⟩
      exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le (hInv.sentChal_imp hS).2
        hOther.2.1 (by dsimp only; rw [hOther.2.2.2])
theorem evalDist_prfMsgKeysWorld_true_at_idx1Key (S : Setup) (P : Primitives) (idx : Nat)
    (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[(do
        let mkSeedStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar)
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkCutoffExp1Key S P idx A] := by
  rw [← evalDist_preSample_authMk_eq_cutoff1Key S P idx A]
  refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun mkSeedStar _ => ?_)
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hInit : AuthHybridStateFixed.empty S secb =
      restoreAuthFixedMkAtIdx idx mkSeedStar (AuthHybridStateFixed.empty S secb) := rfl
  congr 1
  symm
  rw [hInit]
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => restoreAuthFixedMkAtIdx idx mkSeedStar hst) (InvMkTrue S P idx mkSeedStar)
    (authMkRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar)) (prfMkAuthImpl1Key S P idx mkSeedStar)
    (fun q st hInv => authMkStepRedProb_evalPrfMkReal1Key P idx mkSeedStar q hWF st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), []) (invMkTrue_empty S P idx mkSeedStar secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState) (fun _ _ => rfl)

theorem authMkStepRedProb_evalPrfMkIdeal1Key {S : Setup} (P : Primitives) (idx : Nat) (q : AuthQuery S)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkFalse S idx st) : ((authMkCutoffImpl1Key S P (idx + 1) q).run st.1.1 =
      Prod.map id (fun ((hst', _), _) => hst') <$>
        ((authMkRedProbImpl1Key S P idx evalPrfMkIdeal q).run st)) ∧
    (∀ x ∈ support ((authMkRedProbImpl1Key S P idx evalPrfMkIdeal q).run st),
      InvMkFalse S idx x.2) := by
  rcases st with ⟨⟨hst, sentChal⟩, cache⟩
  dsimp only [authMkCutoffImpl1Key, authMkRedProbImpl1Key, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authMkStepWith1Key authMkStepRedProb1Key
    dsimp only
    split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSendRedProb_evalPrfMkIdeal P idx (.sendOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepWith1Key authMkStepRedProb1Key
    dsimp only
    split
    · refine ⟨by simp [Prod.map], fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv
    · obtain ⟨hEq, hSupp⟩ := authMkSendRedProb_evalPrfMkIdeal P idx (.sendNoOPK u i) trivial
        u bundle m0 m1 hst sentChal cache hInv
      exact ⟨hEq.symm, hSupp⟩
  | recvOPK k j o msg =>
    unfold authMkStepWith1Key authMkStepRedProb1Key
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
    unfold authMkStepWith1Key authMkStepRedProb1Key
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
    unfold authMkStepWith1Key authMkStepRedProb1Key
    dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · simp [Prod.map, map_eq_bind_pure_comp]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props1Key P _ hst
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
theorem evalDist_prfMsgKeysWorld_false_at_idx1Key (S : Setup) (P : Primitives) (idx : Nat)
    (A : AuthAdversary S) :
    𝒟[(do
        let _ ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkRedProbImpl1Key S P idx evalPrfMkIdeal
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkCutoffExp1Key S P (idx + 1) A] := by
  rw [evalDist_sampleBytes32_bind_const]
  unfold authMkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1
  symm
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => hst) (InvMkFalse S idx) (authMkRedProbImpl1Key S P idx evalPrfMkIdeal)
    (authMkCutoffImpl1Key S P (idx + 1))
    (fun q st hInv => authMkStepRedProb_evalPrfMkIdeal1Key P idx q st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), []) (invMkFalse_empty S idx secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState) (fun _ _ => rfl)

/-! ## Creation-order `PrfMsgKeys` hybrid -/

private theorem support_authCkOtherStep_slots1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ∀ x ∈ support (authCkOtherStep1Key S P q hst), x.2.slots = hst.slots := by
  intro y hy
  unfold authCkOtherStep1Key at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩; rfl

private def authMkSlotsStepWith1Key (S : Setup) (P : Primitives)
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
  | qOther => authCkOtherStep1Key S P qOther hst

private def authMkSlotsStepSlot1Key (S : Setup) (P : Primitives)
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
  | qOther => liftM (authCkOtherStep1Key S P qOther hst)

private def authMkSlotsCutoffImpl1Key (S : Setup) (P : Primitives) (cutoff : Nat) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk
    (authMkSlotsStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff)) q)

private def prfMkSlotsAuthImpl1Key (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authMkSlotsStepWith1Key S P
    (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
    (fun s => decide (s < idx)) q)

private noncomputable def authMkSlotsPreSampleRun1Key (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + prfMkSlotsAuthImpl1Key S P idx mkSeedStar
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

private noncomputable def authMkSlotsCutoffExp1Key (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + authMkSlotsCutoffImpl1Key S P cutoff
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

private theorem authMkSlotsStepWith_wf_and_bounds1Key {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst) :
    ∀ x ∈ support (authMkSlotsStepWith1Key S P sampMkAt useIdealMkAt q hst),
      AuthSlotStateWf S x.2 ∧
      hst.slots.nextSlot ≤ x.2.slots.nextSlot ∧
      x.2.slots.nextSlot ≤ hst.slots.nextSlot + (if isAuthSessQueryB (.inr q) then 1 else 0) ∧
      x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepWith_wf_and_bounds P sampMkAt useIdealMkAt (.sendOPK u i bundle m0 m1) hst hWf
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepWith_wf_and_bounds P sampMkAt useIdealMkAt (.sendNoOPK u i bundle m0 m1) hst hWf
  | recvOPK k j o msg =>
    exact authMkSlotsStepWith_wf_and_bounds P sampMkAt useIdealMkAt (.recvOPK k j o msg) hst hWf
  | recvNoOPK k j l msg =>
    exact authMkSlotsStepWith_wf_and_bounds P sampMkAt useIdealMkAt (.recvNoOPK k j l msg) hst hWf
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkSlotsStepWith1Key
    dsimp only [isAuthSessQueryB, isAuthRecvQueryB]
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro x hx
    have hO := support_authCkOtherStep_props1Key P _ hst
      (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
      (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h) x hx
    have hSl := support_authCkOtherStep_slots1Key P _ hst x hx
    refine ⟨authSlotStateWf_of_usedSend_sub hWf hSl hO.1 (by omega)
      (fun sid h => by rw [hO.2.1]; exact h),
      by rw [hSl], by rw [hSl]; omega, by omega⟩

private theorem authMkSlotsStepSlot_slotComp1Key (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkSlotsStepSlot1Key S P idx useIdealMkAt q hst) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_slotComp S P idx useIdealMkAt (.sendOPK u i bundle m0 m1) hst
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_slotComp S P idx useIdealMkAt (.sendNoOPK u i bundle m0 m1) hst
  | recvOPK k j o msg =>
    exact authMkSlotsStepSlot_slotComp S P idx useIdealMkAt (.recvOPK k j o msg) hst
  | recvNoOPK k j l msg =>
    exact authMkSlotsStepSlot_slotComp S P idx useIdealMkAt (.recvNoOPK k j l msg) hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact SlotM.SlotComp.liftComp sampleBytes32 _

private theorem authMkSlotsStepSlot_run'_some1Key (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool) (mkSeedStar : Bytes)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkSlotsStepSlot1Key S P idx useIdealMkAt q hst).run' (some mkSeedStar) =
      authMkSlotsStepWith1Key S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32)
        useIdealMkAt q hst := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendOPK u i bundle m0 m1) hst
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendNoOPK u i bundle m0 m1) hst
  | recvOPK k j o msg =>
    exact authMkSlotsRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  | recvNoOPK k j l msg =>
    exact authMkSlotsRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact SlotM.run'_liftComp _ (some mkSeedStar)

private theorem authMkSlotsStepSlot_run'_none1Key (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkSlotsStepSlot1Key S P idx useIdealMkAt q hst).run' none =
      authMkSlotsStepWith1Key S P (fun _ => sampleBytes32) useIdealMkAt q hst := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_run'_none S P idx useIdealMkAt (.sendOPK u i bundle m0 m1) hst
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_run'_none S P idx useIdealMkAt (.sendNoOPK u i bundle m0 m1) hst
  | recvOPK k j o msg =>
    exact authMkSlotsRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  | recvNoOPK k j l msg =>
    exact authMkSlotsRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact SlotM.run'_liftComp _ none

private theorem authMkSlotsStepSlot_fire1Key (S : Setup) (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (y : ((authSpec S).Range q × AuthHybridStateFixed S) × Option Bytes)
    (hWf : AuthSlotStateWf S hst)
    (hy : y ∈ support ((authMkSlotsStepSlot1Key S P idx useIdealMkAt q hst).run none))
    (hSome : y.2.isSome = true) :
    authCreationSlotFired idx y.1.2 = true := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_fire S P idx useIdealMkAt (.sendOPK u i bundle m0 m1) hst y hWf hy hSome
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepSlot_fire S P idx useIdealMkAt (.sendNoOPK u i bundle m0 m1) hst y hWf hy hSome
  | recvOPK k j o msg =>
    exact authMkSlotsStepSlot_fire S P idx useIdealMkAt (.recvOPK k j o msg) hst y hWf hy hSome
  | recvNoOPK k j l msg =>
    exact authMkSlotsStepSlot_fire S P idx useIdealMkAt (.recvNoOPK k j l msg) hst y hWf hy hSome
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    exact False.elim (run_none_liftM_isSome_false _ y hy hSome)

private theorem authMkSlotsStepWith_after1Key (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWf : AuthSlotStateWf S hst) (hFired : authCreationSlotFired idx hst = true) :
    (prfMkSlotsAuthImpl1Key S P idx mkSeedStar q).run hst =
      (authMkSlotsCutoffImpl1Key S P idx q).run hst ∧
    ∀ x ∈ support ((authMkSlotsCutoffImpl1Key S P idx q).run hst),
      authCreationSlotFired idx x.2 = true := by
  have hLt : idx < hst.slots.nextSlot := by
    simpa [authCreationSlotFired] using hFired
  have hMono : ∀ x ∈ support (authMkSlotsStepWith1Key S P (fun _ => sampleBytes32)
      (fun s => decide (s < idx)) q hst), authCreationSlotFired idx x.2 = true := by
    intro x hx
    have hStep := authMkSlotsStepWith_wf_and_bounds1Key P (fun _ => sampleBytes32)
      (fun s => decide (s < idx)) q hst hWf x hx
    simp only [authCreationSlotFired, decide_eq_true_eq]
    exact Nat.lt_of_lt_of_le hLt hStep.2.1
  refine ⟨?_, hMono⟩
  dsimp only [prfMkSlotsAuthImpl1Key, authMkSlotsCutoffImpl1Key, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact (authMkSlotsStepWith_after S P idx mkSeedStar (.sendOPK u i bundle m0 m1) hst hWf hFired).1
  | sendNoOPK u i bundle m0 m1 =>
    exact (authMkSlotsStepWith_after S P idx mkSeedStar (.sendNoOPK u i bundle m0 m1) hst hWf hFired).1
  | recvOPK k j o msg =>
    exact (authMkSlotsStepWith_after S P idx mkSeedStar (.recvOPK k j o msg) hst hWf hFired).1
  | recvNoOPK k j l msg =>
    exact (authMkSlotsStepWith_after S P idx mkSeedStar (.recvNoOPK k j l msg) hst hWf hFired).1
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets => rfl

private theorem evalDist_preSample_authMkSlots_eq_cutoff1Key (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[do
        let mkSeedStar ← sampleBytes32
        authMkSlotsPreSampleRun1Key S P idx mkSeedStar A] =
      𝒟[authMkSlotsCutoffExp1Key S P idx A] := by
  unfold authMkSlotsPreSampleRun1Key authMkSlotsCutoffExp1Key
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep_inv
    sampleBytes32
    (AuthSlotStateWf S)
    (authCreationSlotFired idx)
    (authMkSlotsCutoffImpl1Key S P idx)
    (fun mkSeedStar => prfMkSlotsAuthImpl1Key S P idx mkSeedStar)
    (authMkSlotsStepSlot1Key S P idx (fun s => decide (s < idx)))
    (authMkSlotsStepSlot_slotComp1Key S P idx (fun s => decide (s < idx)))
    (authMkSlotsStepSlot_run'_some1Key S P idx (fun s => decide (s < idx)))
    (fun q hst g _ => by
      dsimp only [authMkSlotsCutoffImpl1Key, StateT.run_mk]
      rw [authMkSlotsStepSlot_run'_none1Key S P idx (fun s => decide (s < idx)) q hst])
    (fun mkSeedStar q hst hWf hFired =>
      authMkSlotsStepWith_after1Key S P idx mkSeedStar q hst hWf hFired)
    (fun q hst y hWf hy hSome =>
      authMkSlotsStepSlot_fire1Key S P idx (fun s => decide (s < idx)) q hst y hWf hy hSome)
    (fun q hst hWf x hx =>
      (authMkSlotsStepWith_wf_and_bounds1Key P (fun _ => sampleBytes32) (fun s => decide (s < idx))
        q hst hWf x hx).1)
    (fun q hst hWf =>
      SlotM.wf_run_none_of_run'_eq _ _
        (authMkSlotsStepSlot_run'_none1Key S P idx (fun s => decide (s < idx)) q hst)
        (fun x hx =>
          (authMkSlotsStepWith_wf_and_bounds1Key P (fun _ => sampleBytes32) (fun s => decide (s < idx))
            q hst hWf x hx).1))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (authSlotStateWf_empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

private theorem step_authMkSlots_zero_projMkSlots0_1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id projMkSlots0 <$>
      authMkSlotsStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) q hst =
    authMkStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) q (projMkSlots0 hst) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact step_authMkSlots_zero_projMkSlots0 P (.sendOPK u i bundle m0 m1) hst
  | sendNoOPK u i bundle m0 m1 =>
    exact step_authMkSlots_zero_projMkSlots0 P (.sendNoOPK u i bundle m0 m1) hst
  | recvOPK k j o msg =>
    exact step_authMkSlots_zero_projMkSlots0 P (.recvOPK k j o msg) hst
  | recvNoOPK k j l msg =>
    exact step_authMkSlots_zero_projMkSlots0 P (.recvNoOPK k j l msg) hst
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkSlotsStepWith1Key authMkStepWith1Key authCkOtherStep1Key projMkSlots0
    dsimp only
    cases hst.toAuthHybridState.base.hasWonAuth <;> simp [Prod.map, map_eq_bind_pure_comp]

private theorem evalDist_authMkSlotsCutoffExp_zero_eq_g3_7_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkSlotsCutoffExp1Key S P 0 A.1] = 𝒟[authFixedExpAtStage1Key .g3_7 S P A.1] := by
  rw [← evalDist_authMkCutoffExp_zero_eq_g3_7_1Key S P b A]
  unfold authMkSlotsCutoffExp1Key authMkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1
  exact (simulateQ_proj_inv_obs
    projMkSlots0 (fun _ => True)
    (authMkSlotsCutoffImpl1Key S P 0) (authMkCutoffImpl1Key S P 0)
    (fun q hst _ => ⟨(step_authMkSlots_zero_projMkSlots0_1Key P q hst).symm, fun _ _ => trivial⟩)
    A.1.run
    (AuthHybridStateFixed.empty S secb) trivial
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun _ _ => rfl)).symm

private theorem step_authMkSlots_end_projMkSlots0_1Key {S : Setup} (P : Primitives) (M : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hWf : AuthSlotStateWf S hst)
    (hSess : isAuthSessQueryB (.inr q) = true → hst.slots.nextSlot < M)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    Prod.map id projMkSlots0 <$>
      authMkSlotsStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < M)) q hst =
    authMkStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
      q (projMkSlots0 hst) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact step_authMkSlots_end_projMkSlots0 P M (.sendOPK u i bundle m0 m1) hst hWf hSess hRecv
  | sendNoOPK u i bundle m0 m1 =>
    exact step_authMkSlots_end_projMkSlots0 P M (.sendNoOPK u i bundle m0 m1) hst hWf hSess hRecv
  | recvOPK k j o msg =>
    exact step_authMkSlots_end_projMkSlots0 P M (.recvOPK k j o msg) hst hWf hSess hRecv
  | recvNoOPK k j l msg =>
    exact step_authMkSlots_end_projMkSlots0 P M (.recvNoOPK k j l msg) hst hWf hSess hRecv
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    unfold authMkSlotsStepWith1Key authMkStepWith1Key authCkOtherStep1Key projMkSlots0
    dsimp only
    cases hst.toAuthHybridState.base.hasWonAuth <;> simp [Prod.map, map_eq_bind_pure_comp]

private theorem evalDist_authMkSlotsCutoffExp_end_eq_g3_8_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkSlotsCutoffExp1Key S P (min b.q_total S.N_sess_tot) A.1] =
      𝒟[authFixedExpAtStage1Key .g3_8 S P A.1] := by
  rw [← evalDist_authMkCutoffExp_end_eq_g3_8_1Key S P b A]
  unfold authMkSlotsCutoffExp1Key authMkCutoffExp1Key
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
    (authMkSlotsCutoffImpl1Key S P (min b.q_total S.N_sess_tot))
    (authMkCutoffImpl1Key S P S.N_sess_tot)
    (fun q hst hWf hSess hRecv =>
      ⟨step_authMkSlots_end_projMkSlots0_1Key P (min b.q_total S.N_sess_tot) q hst hWf hSess hRecv,
       fun x hx => by
         obtain ⟨hW, _, hN, hR⟩ := authMkSlotsStepWith_wf_and_bounds1Key P (fun _ => sampleBytes32)
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

private theorem authCkOtherStep_restoreAuthFixedSlotsMkAtIdx1Key {S : Setup} (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    authCkOtherStep1Key S P q (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst) =
      Prod.map id (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar) <$> authCkOtherStep1Key S P q hst := by
  unfold authCkOtherStep1Key restoreAuthFixedSlotsMkAtIdx restoreAuthMkSlotsAtIdx
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp [map_eq_bind_pure_comp, Prod.map]

private theorem authMkSlotsStepRedProb_evalPrfMkReal1Key {S : Setup} (P : Primitives) (idx : Nat)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hWF : WellFormedPrimitivesδ P)
    (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkSlotsTrue S P idx mkSeedStar st) :
    ((prfMkSlotsAuthImpl1Key S P idx mkSeedStar q).run
        (restoreAuthFixedSlotsMkAtIdx idx mkSeedStar st.1.1) =
      Prod.map id (fun ((hst', _), _) => restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst') <$>
        ((authMkSlotsRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar) q).run st)) ∧
    (∀ x ∈ support ((authMkSlotsRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar) q).run st),
      InvMkSlotsTrue S P idx mkSeedStar x.2) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepRedProb_evalPrfMkReal P idx mkSeedStar (.sendOPK u i bundle m0 m1) hWF st hInv
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepRedProb_evalPrfMkReal P idx mkSeedStar (.sendNoOPK u i bundle m0 m1) hWF st hInv
  | recvOPK k j o msg =>
    exact authMkSlotsStepRedProb_evalPrfMkReal P idx mkSeedStar (.recvOPK k j o msg) hWF st hInv
  | recvNoOPK k j l msg =>
    exact authMkSlotsStepRedProb_evalPrfMkReal P idx mkSeedStar (.recvNoOPK k j l msg) hWF st hInv
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    rcases st with ⟨⟨hst, sentChal⟩, cache⟩
    dsimp only [prfMkSlotsAuthImpl1Key, authMkSlotsRedProbImpl1Key, StateT.run_mk]
    unfold authMkSlotsStepWith1Key authMkSlotsStepRedProb1Key
    dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · rw [authCkOtherStep_restoreAuthFixedSlotsMkAtIdx1Key]
      simp [Prod.map, map_eq_bind_pure_comp]
      rfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props1Key P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      have hSl := support_authCkOtherStep_slots1Key P _ hst (resp, hst') hMem
      dsimp only at hOther hSl
      have hRCEq : hst.recvCount ≤ hst'.recvCount := by rw [hOther.2.2.2]
      exact
        { wf := authSlotStateWf_of_usedSend_sub (hst := hst) (hst' := hst') hInv.wf hSl hOther.1 hRCEq
                  (fun sid0 h0 => by rw [hOther.2.1]; exact h0)
          saltCache_send := by dsimp only; rw [hOther.2.1, hOther.2.2.1]; exact hInv.saltCache_send
          sentChal_imp := fun hS => by dsimp only; rw [hSl]; exact hInv.sentChal_imp hS
          ideal_msgKeys := by dsimp only; rw [hSl, hOther.1]; exact hInv.ideal_msgKeys
          cache_msgKeys := by dsimp only; rw [hSl, hOther.2.2.1]; exact hInv.cache_msgKeys }

private theorem evalDist_prfMsgKeysSlotsWorld_true_at_idx1Key (S : Setup) (P : Primitives)
    (idx : Nat) (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    𝒟[(do
        let mkSeedStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkSlotsRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar)
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkSlotsCutoffExp1Key S P idx A] := by
  rw [← evalDist_preSample_authMkSlots_eq_cutoff1Key S P idx A]
  refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun mkSeedStar _ => ?_)
  unfold authMkSlotsPreSampleRun1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hInit : AuthHybridStateFixed.empty S secb =
      restoreAuthFixedSlotsMkAtIdx idx mkSeedStar (AuthHybridStateFixed.empty S secb) := rfl
  congr 1
  symm
  rw [hInit]
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => restoreAuthFixedSlotsMkAtIdx idx mkSeedStar hst)
    (InvMkSlotsTrue S P idx mkSeedStar)
    (authMkSlotsRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar))
    (prfMkSlotsAuthImpl1Key S P idx mkSeedStar)
    (fun q st hInv => authMkSlotsStepRedProb_evalPrfMkReal1Key P idx mkSeedStar q hWF st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), []) (invMkSlotsTrue_empty S P idx mkSeedStar secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState) (fun _ _ => rfl)

private theorem authMkSlotsStepRedProb_evalPrfMkIdeal1Key {S : Setup} (P : Primitives) (idx : Nat)
    (q : AuthQuery S) (st : (AuthHybridStateFixed S × Bool) × PrfMkCache)
    (hInv : InvMkSlotsFalse S idx st) :
    ((authMkSlotsCutoffImpl1Key S P (idx + 1) q).run st.1.1 =
      Prod.map id (fun ((hst', _), _) => hst') <$>
        ((authMkSlotsRedProbImpl1Key S P idx evalPrfMkIdeal q).run st)) ∧
    (∀ x ∈ support ((authMkSlotsRedProbImpl1Key S P idx evalPrfMkIdeal q).run st),
      InvMkSlotsFalse S idx x.2) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact authMkSlotsStepRedProb_evalPrfMkIdeal P idx (.sendOPK u i bundle m0 m1) st hInv
  | sendNoOPK u i bundle m0 m1 =>
    exact authMkSlotsStepRedProb_evalPrfMkIdeal P idx (.sendNoOPK u i bundle m0 m1) st hInv
  | recvOPK k j o msg =>
    exact authMkSlotsStepRedProb_evalPrfMkIdeal P idx (.recvOPK k j o msg) st hInv
  | recvNoOPK k j l msg =>
    exact authMkSlotsStepRedProb_evalPrfMkIdeal P idx (.recvNoOPK k j l msg) st hInv
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    rcases st with ⟨⟨hst, sentChal⟩, cache⟩
    dsimp only [authMkSlotsCutoffImpl1Key, authMkSlotsRedProbImpl1Key, StateT.run_mk]
    unfold authMkSlotsStepWith1Key authMkSlotsStepRedProb1Key
    dsimp only
    refine ⟨?_, fun x hx => ?_⟩
    · simp [Prod.map, map_eq_bind_pure_comp]
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨resp, hst'⟩, hMem, rfl⟩
      have hOther := support_authCkOtherStep_props1Key P _ hst
        (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
        (by intro _ _ _ _ h; cases h) (by intro _ _ _ _ h; cases h)
        (resp, hst') hMem
      have hSl := support_authCkOtherStep_slots1Key P _ hst (resp, hst') hMem
      dsimp only at hOther hSl
      have hRCEq : hst.recvCount ≤ hst'.recvCount := by rw [hOther.2.2.2]
      exact
        { wf := authSlotStateWf_of_usedSend_sub (hst := hst) (hst' := hst') hInv.wf hSl hOther.1 hRCEq
                  (fun sid0 h0 => by rw [hOther.2.1]; exact h0)
          sentChal_imp := fun hS => by dsimp only; rw [hSl]; exact hInv.sentChal_imp hS
          unfired_cache_nil := fun hLe => by dsimp only at hLe; rw [hSl] at hLe; exact hInv.unfired_cache_nil hLe
          ideal_unique := by dsimp only; rw [hSl, hOther.1]; exact hInv.ideal_unique
          cache_sub_mkSaltCache := by dsimp only; rw [hSl, hOther.1, hOther.2.2.1]; exact hInv.cache_sub_mkSaltCache }

private theorem evalDist_prfMsgKeysSlotsWorld_false_at_idx1Key (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[(do
        let _ ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkSlotsRedProbImpl1Key S P idx evalPrfMkIdeal
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState : ProbComp Bool)] =
      𝒟[authMkSlotsCutoffExp1Key S P (idx + 1) A] := by
  rw [evalDist_sampleBytes32_bind_const]
  unfold authMkSlotsCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  congr 1
  symm
  exact simulateQ_proj_inv_obs
    (fun ((hst, _), _) => hst) (InvMkSlotsFalse S idx)
    (authMkSlotsRedProbImpl1Key S P idx evalPrfMkIdeal)
    (authMkSlotsCutoffImpl1Key S P (idx + 1))
    (fun q st hInv => authMkSlotsStepRedProb_evalPrfMkIdeal1Key P idx q st hInv)
    A.run
    ((AuthHybridStateFixed.empty S secb, false), []) (invMkSlotsFalse_empty S idx secb)
    (fun (b', ((finalSt, _), _)) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState) (fun _ _ => rfl)

theorem hop_G3_7_G3_8_1Key (S : Setup) :
    AuthHopG3_7G3_8Stmt1Key S (prfMsgKeysReductionAuthFixed1Key S) := by
  intro P hP b A
  change |(𝒟[authFixedExpAtStage1Key .g3_7 S P A.1].boolBias).toReal -
          (𝒟[authFixedExpAtStage1Key .g3_8 S P A.1].boolBias).toReal| ≤
    2 * (S.N_sess_tot : ℝ) *
      (𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed1Key S b A)].boolBias).toReal
  let M := min b.q_total S.N_sess_tot
  rw [← evalDist_authMkSlotsCutoffExp_zero_eq_g3_7_1Key S P b A,
      ← evalDist_authMkSlotsCutoffExp_end_eq_g3_8_1Key S P b A]
  have hPrfEq :
      𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed1Key S b A)] =
        𝒟[do
          let ch ← $ᵗ Bool
          let z ← if ch then
                    (RoKem.sampleIndexRange M >>= fun idx => do
                      let mkSeedStar ← sampleBytes32
                      let secb ← $ᵗ Bool
                      let initSt := AuthHybridStateFixed.empty S secb
                      let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
                        (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
                        authMkSlotsRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar)
                      let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.1.run).run
                        ((initSt, false), [])
                      finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
                  else
                    (RoKem.sampleIndexRange M >>= fun idx => do
                      let _ ← sampleBytes32
                      let secb ← $ᵗ Bool
                      let initSt := AuthHybridStateFixed.empty S secb
                      let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
                        (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
                        authMkSlotsRedProbImpl1Key S P idx evalPrfMkIdeal
                      let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.1.run).run
                        ((initSt, false), [])
                      finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
          return (ch == z)] := by
    unfold prfMsgKeysExp prfMsgKeysReductionAuthFixed1Key
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun ch _ => ?_)
    dsimp only
    have hSim : ∀ mkSeed : Bytes,
        ((simulateQ ((primBaseImpl P).liftTarget
            (StateT PrfMkCache ProbComp) +
            prfMsgKeysOracleImpl ch P mkSeed)
          (embedUnifMk (RoKem.sampleIndexRange M) >>= fun idx =>
            authMkReductionRun1Key S idx A.1)).run [] >>= fun (b', _) => pure (b' == ch)) =
        (RoKem.sampleIndexRange M >>= fun idx => do
          let secb ← $ᵗ Bool
          let initSt := AuthHybridStateFixed.empty S secb
          let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
            authMkSlotsRedProbImpl1Key S P idx (fun s c =>
              ((prfMsgKeysOracleImpl ch P mkSeed)
                (.derive (effectiveHkdfSaltBytes s))).run c)
          let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.1.run).run ((initSt, false), [])
          let z ← finalizeAuthFixed P secb b' finalSt.toAuthHybridState
          return (ch == z)) := by
      intro mkSeed
      rw [simulateQ_prfMkFullImpl_embedUnifMk_bind, bind_assoc]
      congr 1; funext idx
      have hRun := simulateQ_authMkReductionRun_eq_redProb1Key S P idx
        (prfMsgKeysOracleImpl ch P mkSeed) ([] : PrfMkCache) A.1
      dsimp only at hRun
      have hRunBind := congrArg (fun m => m >>= fun z => pure (ch == z)) hRun
      simp only [bind_assoc, pure_bind, Bool.beq_comm] at hRunBind ⊢
      exact hRunBind
    cases ch
    · simp only [Bool.false_eq_true, ↓reduceIte]
      trans 𝒟[sampleBytes32 >>= fun mkSeed =>
        ((simulateQ ((primBaseImpl P).liftTarget
            (StateT PrfMkCache ProbComp) +
            prfMsgKeysOracleImpl false P mkSeed)
          (embedUnifMk (RoKem.sampleIndexRange M) >>= fun idx =>
            authMkReductionRun1Key S idx A.1)).run [] >>= fun (b', _) => pure (b' == false))]
      · rfl
      · simp only [hSim, prfMsgKeysOracleImpl_false_run]
        rw [OracleComp.evalDist_bind_bind_swap]
        simp only [bind_assoc]
    · simp only [↓reduceIte]
      trans 𝒟[sampleBytes32 >>= fun mkSeed =>
        ((simulateQ ((primBaseImpl P).liftTarget
            (StateT PrfMkCache ProbComp) +
            prfMsgKeysOracleImpl true P mkSeed)
          (embedUnifMk (RoKem.sampleIndexRange M) >>= fun idx =>
            authMkReductionRun1Key S idx A.1)).run [] >>= fun (b', _) => pure (b' == true))]
      · rfl
      · simp only [hSim, prfMsgKeysOracleImpl_true_run]
        rw [OracleComp.evalDist_bind_bind_swap]
        simp only [bind_assoc]
  have hBoundM :
      |(𝒟[authMkSlotsCutoffExp1Key S P 0 A.1].boolBias).toReal -
        (𝒟[authMkSlotsCutoffExp1Key S P M A.1].boolBias).toReal| ≤
      2 * (M : ℝ) *
        (𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed1Key S b A)].boolBias).toReal := by
    rw [hPrfEq]
    exact abs_sub_boolBias_le_two_mul_sampleIndexRange_coin_game
      M
      (fun k => authMkSlotsCutoffExp1Key S P k A.1)
      (fun idx => do
        let mkSeedStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkSlotsRedProbImpl1Key S P idx (evalPrfMkReal P mkSeedStar)
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.1.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
      (fun idx => do
        let _ ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullRed := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((AuthHybridStateFixed S × Bool) × PrfMkCache) ProbComp) +
          authMkSlotsRedProbImpl1Key S P idx evalPrfMkIdeal
        let (b', ((finalSt, _), _)) ← (simulateQ fullRed A.1.run).run ((initSt, false), [])
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
      (fun idx _ => by
        rw [evalDist_prfMsgKeysSlotsWorld_true_at_idx1Key S P idx hP.toWellFormedPrimitivesδ A.1])
      (fun idx _ => by rw [evalDist_prfMsgKeysSlotsWorld_false_at_idx1Key S P idx A.1])
  have hMle : (M : ℝ) ≤ (S.N_sess_tot : ℝ) := Nat.cast_le.mpr (Nat.min_le_right _ _)
  have hBiasNN :
      0 ≤ (𝒟[prfMsgKeysExp P (prfMsgKeysReductionAuthFixed1Key S b A)].boolBias).toReal :=
    ENNReal.toReal_nonneg
  nlinarith
end AuthSubHops1to3

end SignalPqxdh.Security
