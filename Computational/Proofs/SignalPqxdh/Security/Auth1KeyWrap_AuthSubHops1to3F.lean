/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `SlotM` Bridge for `RootKdfRO` (`G3.5` to `G3.6`)

Defines the single-identity-key `RootKdfRO` cutoff oracle and experiment over `pqxdhAuthImpl1KeyG`,
and proves the `SlotM` pre-sampling equivalence `evalDist_preSample_authRk_eq_cutoff1Key`.
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

def authRkStepWith1Key (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authRkSendWith S P sampRkAt useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authRkSendWith S P sampRkAt useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authRkRecvWith S P sampRkAt useIdealRkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authRkRecvWith S P sampRkAt useIdealRkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep1Key S P qOther hst

def authRkStepSlot1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM Bytes ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authRkSendSlot S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authRkSendSlot S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authRkRecvSlot S P idx useIdealRkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authRkRecvSlot S P idx useIdealRkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep1Key S P qOther hst)

theorem authRkStepSlot_slotComp1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authRkStepSlot1Key S P idx useIdealRkAt q hst) := by
  cases q <;> unfold authRkStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authRkSendSlot_slotComp S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authRkSendSlot_slotComp S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authRkRecvSlot_slotComp S P idx useIdealRkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_slotComp S P idx useIdealRkAt msg _ hst
  all_goals
    exact SlotM.SlotComp.liftComp sampleBytes32 _

theorem authRkStepSlot_run'_some1Key (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (rkStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authRkStepSlot1Key S P idx useIdealRkAt q hst).run' (some rkStar) =
      authRkStepWith1Key S P (fun s => if s == idx then pure rkStar else sampleBytes32) useIdealRkAt
        q hst := by
  cases q <;> unfold authRkStepSlot1Key authRkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_some S P idx useIdealRkAt rkStar (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_some S P idx useIdealRkAt rkStar (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authRkRecvSlot_run'_some S P idx useIdealRkAt rkStar msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_run'_some S P idx useIdealRkAt rkStar msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authRkStepSlot_run'_none1Key (S : Setup) (P : Primitives) (idx : Nat)
    (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authRkStepSlot1Key S P idx useIdealRkAt q hst).run' none =
      authRkStepWith1Key S P (fun _ => sampleBytes32) useIdealRkAt q hst := by
  cases q <;> unfold authRkStepSlot1Key authRkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_none S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authRkSendSlot_run'_none S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authRkRecvSlot_run'_none S P idx useIdealRkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_run'_none S P idx useIdealRkAt msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authRkStepSlot_fire1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authRkStepSlot1Key S P idx useIdealRkAt q hst) := by
  cases q <;> unfold authRkStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authRkSendSlot_fire S P idx useIdealRkAt (.sendOPK u i) u bundle m0 m1 hst rfl
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authRkSendSlot_fire S P idx useIdealRkAt (.sendNoOPK u i) u bundle m0 m1 hst rfl
  case recvOPK k j o msg =>
    exact authRkRecvSlot_fire S P idx useIdealRkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authRkRecvSlot_fire S P idx useIdealRkAt msg _ hst
  all_goals
    exact SlotFireAtAuth.liftComp idx _

theorem authRkStepWith_slotFired_mono1Key (S : Setup) (P : Primitives) (idx : Nat)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authRkStepWith1Key S P sampRkAt useIdealRkAt q hst) := by
  cases q <;> unfold authRkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authRkSendWith_slotFired_mono S P idx sampRkAt useIdealRkAt
        (.sendOPK u i) u bundle m0 m1 hst hFired
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authRkSendWith_slotFired_mono S P idx sampRkAt useIdealRkAt
        (.sendNoOPK u i) u bundle m0 m1 hst hFired
  case recvOPK k j o msg =>
    exact authRkRecvWith_slotFired_mono S P idx sampRkAt useIdealRkAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg
          hst.toAuthHybridState hPrep res?)
      hFired
  case recvNoOPK k j l msg =>
    exact authRkRecvWith_slotFired_mono S P idx sampRkAt useIdealRkAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg
          hst.toAuthHybridState hPrep res?)
      hFired
  all_goals
    exact authCkOtherStep_slotFired_mono1Key S P idx _ hst
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) hFired

theorem authRkStepWith_after1Key (S : Setup) (P : Primitives) (idx : Nat) (useIdealRkAt : Nat → Bool)
    (rkStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authRkStepWith1Key S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        useIdealRkAt q hst =
      authRkStepWith1Key S P (fun _ => sampleBytes32) useIdealRkAt q hst ∧
    ∀ x ∈ support (authRkStepWith1Key S P (fun _ => sampleBytes32) useIdealRkAt q hst),
      authSlotFired S idx x.2 = true := by
  refine ⟨?_, authRkStepWith_slotFired_mono1Key S P idx _ useIdealRkAt q hst hFired⟩
  have hSendEq : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
      (m0 m1 : Bytes), sendSlotIndex? sid = some (sessionSlotIndex sid) →
      authRkSendWith S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        useIdealRkAt sid u bundle m0 m1 hst =
        authRkSendWith S P (fun _ => sampleBytes32) useIdealRkAt sid u bundle m0 m1 hst := by
    intro sid u bundle m0 m1 hSend
    by_cases hEq : (sessionSlotIndex sid == idx) = true
    · rw [beq_iff_eq] at hEq
      have hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true :=
        contains_sid_of_authSlotFired hFired (hEq ▸ hSend)
      unfold authRkSendWith
      simp only [hCont, ↓reduceIte]
    · apply authRkSendWith_congr_slot
      simp only [hEq, Bool.false_eq_true, ↓reduceIte]
  cases q
  case sendOPK u i bundle m0 m1 =>
    unfold authRkStepWith1Key; dsimp only
    split
    · rfl
    · exact hSendEq (.sendOPK u i) u bundle m0 m1 rfl
  case sendNoOPK u i bundle m0 m1 =>
    unfold authRkStepWith1Key; dsimp only
    split
    · rfl
    · exact hSendEq (.sendNoOPK u i) u bundle m0 m1 rfl
  case recvOPK k' j o msg =>
    unfold authRkStepWith1Key; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authRkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  case recvNoOPK k' j l msg =>
    unfold authRkStepWith1Key; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authRkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

def authRkCutoffImpl1Key (S : Setup) (P : Primitives) (cutoff : Nat) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authRkStepWith1Key S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff)) q)

def rootRoAuthImpl1Key (S : Setup) (P : Primitives) (idx : Nat) (rkStar : Bytes) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authRkStepWith1Key S P (fun s => if s == idx then pure rkStar else sampleBytes32)
    (fun s => decide (s < idx)) q)

noncomputable def authRkCutoffExp1Key (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + authRkCutoffImpl1Key S P cutoff
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

noncomputable def authRkCutoffAdv1Key (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[authRkCutoffExp1Key S P cutoff A].boolBias).toReal

/-- Pre-sampling `rkStar` at slot `idx` in `rootRoAuthImpl1Key` matches `authRkCutoffExp1Key`. -/
theorem evalDist_preSample_authRk_eq_cutoff1Key (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[do
        let rkStar ← sampleBytes32
        let secb ← $ᵗ Bool
        let initSt := AuthHybridStateFixed.empty S secb
        let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthHybridStateFixed S) ProbComp) + rootRoAuthImpl1Key S P idx rkStar
        let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
        finalizeAuthFixed P secb b' finalSt.toAuthHybridState] =
      𝒟[authRkCutoffExp1Key S P idx A] := by
  unfold authRkCutoffExp1Key
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep
    sampleBytes32
    (authSlotFired S idx)
    (authRkCutoffImpl1Key S P idx)
    (fun rkStar => rootRoAuthImpl1Key S P idx rkStar)
    (authRkStepSlot1Key S P idx (fun s => decide (s < idx)))
    (authRkStepSlot_slotComp1Key S P idx (fun s => decide (s < idx)))
    (authRkStepSlot_run'_some1Key S P idx (fun s => decide (s < idx)))
    (fun q hst g => by
      dsimp only [authRkCutoffImpl1Key, StateT.run_mk]
      rw [authRkStepSlot_run'_none1Key S P idx (fun s => decide (s < idx)) q hst])
    (fun rkStar q hst hFired =>
      authRkStepWith_after1Key S P idx (fun s => decide (s < idx)) rkStar q hst hFired)
    (authRkStepSlot_fire1Key S P idx (fun s => decide (s < idx)))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

end SignalPqxdh.Security.AuthSubHops1to3
