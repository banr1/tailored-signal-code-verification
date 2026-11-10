/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `PrfMsgKeys` `SlotM` Bridge and `G3.7` Endpoint

Defines the single-identity-key `PrfMsgKeys` cutoff experiments over `pqxdhAuthImpl1KeyG`, proves
the `SlotM` pre-sampling bridge, and matches cutoff `0` with stage `.g3_7`.
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

def authMkStepWith1Key (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authMkSendWith S P sampMkAt useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authMkSendWith S P sampMkAt useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authMkRecvWith S P sampMkAt useIdealMkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authMkRecvWith S P sampMkAt useIdealMkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep1Key S P qOther hst
def authMkStepSlot1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM Bytes ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authMkSendSlot S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authMkSendSlot S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authMkRecvSlot S P idx useIdealMkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authMkRecvSlot S P idx useIdealMkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep1Key S P qOther hst)

theorem authMkStepSlot_slotComp1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkStepSlot1Key S P idx useIdealMkAt q hst) := by
  cases q <;> unfold authMkStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authMkSendSlot_slotComp S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authMkSendSlot_slotComp S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authMkRecvSlot_slotComp S P idx useIdealMkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_slotComp S P idx useIdealMkAt msg _ hst
  all_goals
    exact SlotM.SlotComp.liftComp sampleBytes32 _

theorem authMkStepSlot_run'_some1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkStepSlot1Key S P idx useIdealMkAt q hst).run' (some mkSeedStar) =
      authMkStepWith1Key S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt
        q hst := by
  cases q <;> unfold authMkStepSlot1Key authMkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendOPK u i) u bundle m0 m1
        hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendNoOPK u i) u bundle m0 m1
        hst
  case recvOPK k j o msg =>
    exact authMkRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authMkStepSlot_run'_none1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkStepSlot1Key S P idx useIdealMkAt q hst).run' none =
      authMkStepWith1Key S P (fun _ => sampleBytes32) useIdealMkAt q hst := by
  cases q <;> unfold authMkStepSlot1Key authMkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_none S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_none S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authMkRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authMkStepSlot_fire1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authMkStepSlot1Key S P idx useIdealMkAt q hst) := by
  cases q <;> unfold authMkStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authMkSendSlot_fire S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst rfl
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authMkSendSlot_fire S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst rfl
  case recvOPK k j o msg =>
    exact authMkRecvSlot_fire S P idx useIdealMkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_fire S P idx useIdealMkAt msg _ hst
  all_goals
    exact SlotFireAtAuth.liftComp idx _

theorem authMkStepWith_slotFired_mono1Key (S : Setup) (P : Primitives) (idx : Nat)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authMkStepWith1Key S P sampMkAt useIdealMkAt q hst) := by
  cases q <;> unfold authMkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authMkSendWith_slotFired_mono S P idx sampMkAt useIdealMkAt (.sendOPK u i) u bundle m0
        m1 hst hFired
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authMkSendWith_slotFired_mono S P idx sampMkAt useIdealMkAt (.sendNoOPK u i) u bundle m0
        m1 hst hFired
  case recvOPK k j o msg =>
    exact authMkRecvWith_slotFired_mono S P idx sampMkAt useIdealMkAt msg _ hst
      (fun prep hPrep res? => prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg
        hst.toAuthHybridState hPrep res?)
      hFired
  case recvNoOPK k j l msg =>
    exact authMkRecvWith_slotFired_mono S P idx sampMkAt useIdealMkAt msg _ hst
      (fun prep hPrep res? => prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg
        hst.toAuthHybridState hPrep res?)
      hFired
  all_goals
    exact authCkOtherStep_slotFired_mono1Key S P idx _ hst
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) hFired

theorem authMkStepWith_after1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authMkStepWith1Key S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt q
      hst =
      authMkStepWith1Key S P (fun _ => sampleBytes32) useIdealMkAt q hst ∧
    ∀ x ∈ support (authMkStepWith1Key S P (fun _ => sampleBytes32) useIdealMkAt q hst),
      authSlotFired S idx x.2 = true := by
  refine ⟨?_, authMkStepWith_slotFired_mono1Key S P idx _ useIdealMkAt q hst hFired⟩
  have hSendEq : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 :
    Bytes),
      sendSlotIndex? sid = some (sessionSlotIndex sid) →
      authMkSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt
        sid u bundle m0 m1 hst =
        authMkSendWith S P (fun _ => sampleBytes32) useIdealMkAt sid u bundle m0 m1 hst := by
    intro sid u bundle m0 m1 hSend
    by_cases hEq : (sessionSlotIndex sid == idx) = true
    · rw [beq_iff_eq] at hEq
      have hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true :=
        contains_sid_of_authSlotFired hFired (hEq ▸ hSend)
      unfold authMkSendWith
      rw [prepareAuthSendMk_of_usedSendSessions_contains P sid u bundle m0 m1 hst hCont]
      rfl
    · apply authMkSendWith_congr_slot
      simp only [hEq, Bool.false_eq_true, ↓reduceIte]
  cases q
  case sendOPK u i bundle m0 m1 =>
    unfold authMkStepWith1Key; dsimp only
    split
    · rfl
    · exact hSendEq (.sendOPK u i) u bundle m0 m1 rfl
  case sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepWith1Key; dsimp only
    split
    · rfl
    · exact hSendEq (.sendNoOPK u i) u bundle m0 m1 rfl
  case recvOPK k' j o msg =>
    unfold authMkStepWith1Key; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authMkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  case recvNoOPK k' j l msg =>
    unfold authMkStepWith1Key; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authMkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl
def authMkCutoffImpl1Key (S : Setup) (P : Primitives) (cutoff : Nat) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authMkStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff)) q)
def prfMkAuthImpl1Key (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authMkStepWith1Key S P (fun s => if s == idx then pure mkSeedStar else
    sampleBytes32)
    (fun s => decide (s < idx)) q)
noncomputable def authMkPreSampleRun1Key (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + prfMkAuthImpl1Key S P idx mkSeedStar
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState
noncomputable def authMkCutoffExp1Key (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + authMkCutoffImpl1Key S P cutoff
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState
theorem evalDist_preSample_authMk_eq_cutoff1Key (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[do
        let mkSeedStar ← sampleBytes32
        authMkPreSampleRun1Key S P idx mkSeedStar A] =
      𝒟[authMkCutoffExp1Key S P idx A] := by
  unfold authMkPreSampleRun1Key authMkCutoffExp1Key
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep
    sampleBytes32
    (authSlotFired S idx) (authMkCutoffImpl1Key S P idx)
    (fun mkSeedStar => prfMkAuthImpl1Key S P idx mkSeedStar)
    (authMkStepSlot1Key S P idx (fun s => decide (s < idx)))
    (authMkStepSlot_slotComp1Key S P idx (fun s => decide (s < idx)))
    (authMkStepSlot_run'_some1Key S P idx (fun s => decide (s < idx))) (fun q hst g => by
      dsimp only [authMkCutoffImpl1Key, StateT.run_mk]
      rw [authMkStepSlot_run'_none1Key S P idx (fun s => decide (s < idx)) q hst])
    (fun mkSeedStar q hst hFired => authMkStepWith_after1Key S P idx (fun s => decide (s < idx))
      mkSeedStar q hst hFired)
    (authMkStepSlot_fire1Key S P idx (fun s => decide (s < idx)))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp

theorem step_authCk_end_eq_authMkStepWith_zero1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = [])
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(StateT.mk (fun hst => authCkStepWith1Key S P (fun s => sampCkPair P (s < S.N_sess_tot)) q
        hst)).run hst >>= k] =
        𝒟[(authMkCutoffImpl1Key S P 0 q).run hst >>= k]) ∧
    (∀ x ∈ support ((StateT.mk (fun hst => authCkStepWith1Key S P (fun s => sampCkPair P (s <
      S.N_sess_tot)) q hst)).run hst),
      x.2.mkSaltCache = [] ∧ x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1
        else 0)) := by
  dsimp only [authMkCutoffImpl1Key, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key, authMkStepWith1Key]
    rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
      simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
    · refine ⟨evalDist_authCkSendWith_end_eq_authMkSendWith_zero P (.sendOPK u i) u bundle m0 m1 hst
        hCache hSid,
        fun x hx => ?_⟩
      obtain ⟨hC, hCnt⟩ := support_authCkSendWith_inv P _ (.sendOPK u i) u bundle m0 m1 hst hCache x
        hx
      exact ⟨hC, by omega⟩
    · refine ⟨fun _ => trivial, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; dsimp only; exact ⟨hCache, by omega⟩
  | sendNoOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key, authMkStepWith1Key]
    rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
      simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
    · refine ⟨evalDist_authCkSendWith_end_eq_authMkSendWith_zero P (.sendNoOPK u i) u bundle m0 m1
        hst hCache hSid,
        fun x hx => ?_⟩
      obtain ⟨hC, hCnt⟩ := support_authCkSendWith_inv P _ (.sendNoOPK u i) u bundle m0 m1 hst hCache
        x hx
      exact ⟨hC, by omega⟩
    · refine ⟨fun _ => trivial, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; dsimp only; exact ⟨hCache, by omega⟩
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith1Key, authMkStepWith1Key]
    refine ⟨evalDist_authCkRecvWith_end_eq_authMkRecvWith_zero P msg _ hst hCache hLt,
      fun x hx => ?_⟩
    obtain ⟨hC, hCnt⟩ := support_authCkRecvWith_inv P _ msg _ hst hCache x hx
    exact ⟨hC, by omega⟩
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith1Key, authMkStepWith1Key]
    refine ⟨evalDist_authCkRecvWith_end_eq_authMkRecvWith_zero P msg _ hst hCache hLt,
      fun x hx => ?_⟩
    obtain ⟨hC, hCnt⟩ := support_authCkRecvWith_inv P _ msg _ hst hCache x hx
    exact ⟨hC, by omega⟩
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key, authMkStepWith1Key]
    refine ⟨fun _ => trivial, fun x hx => ?_⟩
    unfold authCkOtherStep1Key at hx; split at hx
    · simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; dsimp only
      exact ⟨hCache, by omega⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, base'⟩, _, rfl⟩
    dsimp only
    exact ⟨hCache, by omega⟩
theorem evalDist_authMkCutoffExp_zero_eq_g3_7_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkCutoffExp1Key S P 0 A.1] = 𝒟[authFixedExpAtStage1Key .g3_7 S P A.1] := by
  rw [← evalDist_authCkCutoffExp_end_eq_g3_7_1Key S P b A]
  symm
  unfold authCkCutoffExp1Key authMkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot
    := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (id : AuthHybridStateFixed S → AuthHybridStateFixed S) (fun hst => hst.mkSaltCache = [])
    (fun hst => hst.recvCount) (isAuthRecvQueryB (S := S)) (fun _ => rfl)
    S.N_recv_tot
    (fun q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => sampCkPair P (s < S.N_sess_tot)) q hst))
    (authMkCutoffImpl1Key S P 0)
    (fun q hst hCache hRecv => step_authCk_end_eq_authMkStepWith_zero1Key P q hst hCache hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb)
    rfl
    (by simp [AuthHybridStateFixed.empty])
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
end SignalPqxdh.Security.AuthSubHops1to3
