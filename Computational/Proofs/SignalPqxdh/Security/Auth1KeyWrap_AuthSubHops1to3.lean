/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.GameHop.Swap
public import Computational.Proofs.GameHop.StateSim
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `SlotM` Bridge for `PrfChainKey` (`G3.6` to `G3.7`)

Defines the single-identity-key `PrfChainKey` slot-indexed query steps and cutoff experiments over
`pqxdhAuthImpl1KeyG`, and proves the `SlotM` pre-sampling bridge `evalDist_preSample_authCk_eq_cutoff1Key`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory
open OracleComp OracleSpec
open SignalPqxdh Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

namespace AuthSubHops1to3

namespace SlotM

namespace SlotComp

end SlotComp

variable {κ : Type}

end SlotM

end AuthSubHops1to3

open AuthSubHops1to3

def authCkOtherStep1Key (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  if hst.toAuthHybridState.base.hasWonAuth then
    pure (.noneResp, hst)
  else
    let (resp, base') ← (pqxdhAuthImpl1KeyG true true S P q).run hst.toAuthHybridState.base
    pure (resp, { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })

def authCkStepWith1Key (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendWith S P sampAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendWith S P sampAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkRecvWith S P sampAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkRecvWith S P sampAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep1Key S P qOther hst

def authCkStepSlot1Key (S : Setup) (P : Primitives) (idx : Nat) (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendSlot S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendSlot S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkRecvSlot S P idx samp msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkRecvSlot S P idx samp msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep1Key S P qOther hst)

theorem authCkStepSlot_slotComp1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkStepSlot1Key S P idx samp q hst) := by
  cases q <;> unfold authCkStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure samp _
    · exact authCkSendSlot_slotComp S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure samp _
    · exact authCkSendSlot_slotComp S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authCkRecvSlot_slotComp S P idx samp msg _ hst
  case recvNoOPK k j l msg =>
    exact authCkRecvSlot_slotComp S P idx samp msg _ hst
  all_goals
    exact SlotM.SlotComp.liftComp samp _

theorem authCkStepSlot_run'_some1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkStepSlot1Key S P idx samp q hst).run' (some k) =
      authCkStepWith1Key S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx))
        q hst := by
  cases q <;> unfold authCkStepSlot1Key authCkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_some S P idx samp k (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_some S P idx samp k (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k' j o msg =>
    exact authCkRecvSlot_run'_some S P idx samp k msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkRecvSlot_run'_some S P idx samp k msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authCkStepSlot_run'_none_eq1Key (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkStepSlot1Key S P idx (sampCkPair P (!b)) q hst).run' none =
      authCkStepWith1Key S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1)))
        q hst := by
  cases q <;> unfold authCkStepSlot1Key authCkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_none S P idx b (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_none S P idx b (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k' j o msg =>
    exact authCkRecvSlot_run'_none S P idx b msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkRecvSlot_run'_none S P idx b msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authCkStepSlot_fire1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authCkStepSlot1Key S P idx samp q hst) := by
  cases q <;> unfold authCkStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authCkSendSlot_fire S P idx samp (.sendOPK u i) u bundle m0 m1 hst rfl
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authCkSendSlot_fire S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst rfl
  case recvOPK k j o msg =>
    exact authCkRecvSlot_fire S P idx samp msg _ hst
  case recvNoOPK k j l msg =>
    exact authCkRecvSlot_fire S P idx samp msg _ hst
  all_goals
    exact SlotFireAtAuth.liftComp idx _

theorem authCkOtherStep_slotFired_mono1Key (S : Setup) (P : Primitives) (idx : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hNotSend1 : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (hNotSend2 : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1)
    (hNotRecv1 : ∀ k j o msg, q ≠ .recvOPK k j o msg)
    (hNotRecv2 : ∀ k j l msg, q ≠ .recvNoOPK k j l msg)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authCkOtherStep1Key S P q hst) := by
  have hPres : PreservesAt AuthState.usedSendSessions hst.toAuthHybridState.base
      (pqxdhAuthImpl1KeyG true true S P q) := by
    cases q with
    | sendOPK u i b m0 m1 => exact False.elim (hNotSend1 u i b m0 m1 rfl)
    | sendNoOPK u i b m0 m1 => exact False.elim (hNotSend2 u i b m0 m1 rfl)
    | recvOPK k j o msg => exact False.elim (hNotRecv1 k j o msg rfl)
    | recvNoOPK k j l msg => exact False.elim (hNotRecv2 k j l msg rfl)
    | _ =>
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
  unfold authCkOtherStep1Key
  split
  · exact AuthSlotFiredAt.pure hFired
  · intro y hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩
    exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired
      (hPres (resp, base') hbase) le_rfl

theorem authCkStepWith_slotFired_mono1Key (S : Setup) (P : Primitives) (idx : Nat)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authCkStepWith1Key S P sampAt q hst) := by
  cases q <;> unfold authCkStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authCkSendWith_slotFired_mono S P idx sampAt (.sendOPK u i) u bundle m0 m1 hst hFired
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authCkSendWith_slotFired_mono S P idx sampAt (.sendNoOPK u i) u bundle m0 m1 hst hFired
  case recvOPK k j o msg =>
    exact authCkRecvWith_slotFired_mono S P idx sampAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg hst.toAuthHybridState hPrep res?)
      hFired
  case recvNoOPK k j l msg =>
    exact authCkRecvWith_slotFired_mono S P idx sampAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg
          hst.toAuthHybridState hPrep res?)
      hFired
  all_goals
    exact authCkOtherStep_slotFired_mono1Key S P idx _ hst
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) hFired

theorem authCkStepWith_after1Key (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (k : Bytes × Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authCkStepWith1Key S P (fun s => if s == idx then pure k else sampCkPair P (s < idx)) q hst =
      authCkStepWith1Key S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst ∧
    ∀ x ∈ support
      (authCkStepWith1Key S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst),
      authSlotFired S idx x.2 = true := by
  refine ⟨?_, authCkStepWith_slotFired_mono1Key S P idx _ q hst hFired⟩
  have hSendEq :
      ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes),
      sendSlotIndex? sid = some (sessionSlotIndex sid) →
      authCkSendWith S P (fun s => if s == idx then pure k else sampCkPair P (s < idx))
          sid u bundle m0 m1 hst =
        authCkSendWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1)))
          sid u bundle m0 m1 hst := by
    intro sid u bundle m0 m1 hSend
    by_cases hEq : (sessionSlotIndex sid == idx) = true
    · rw [beq_iff_eq] at hEq
      have hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true :=
        contains_sid_of_authSlotFired hFired (hEq ▸ hSend)
      unfold authCkSendWith
      simp only [hCont, ↓reduceIte]
    · have hne : sessionSlotIndex sid ≠ idx := by
        intro h; exact hEq (beq_iff_eq.mpr h)
      have hlt := lt_cutoff_bool_eq b hne
      apply authCkSendWith_congr_slot
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, hlt]
  cases q
  case sendOPK u i bundle m0 m1 =>
    unfold authCkStepWith1Key; dsimp only
    split
    · rfl
    · exact hSendEq (.sendOPK u i) u bundle m0 m1 rfl
  case sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepWith1Key; dsimp only
    split
    · rfl
    · exact hSendEq (.sendNoOPK u i) u bundle m0 m1 rfl
  case recvOPK k' j o msg =>
    unfold authCkStepWith1Key; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    have hlt := lt_cutoff_bool_eq b hne
    apply authCkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte, hlt]
  case recvNoOPK k' j l msg =>
    unfold authCkStepWith1Key; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    have hlt := lt_cutoff_bool_eq b hne
    apply authCkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte, hlt]
  all_goals rfl

noncomputable def authCkPreSampleRun1Key (S : Setup) (P : Primitives) (idx : Nat)
    (p : Bytes × Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

noncomputable def authCkCutoffExp1Key (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => sampCkPair P (s < cutoff)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

/-- Pre-sampling slot `idx` in `authCkPreSampleRun1Key` matches the lazy cutoff experiment `authCkCutoffExp1Key`. -/
theorem evalDist_preSample_authCk_eq_cutoff1Key (S : Setup) (P : Primitives)
    (idx : Nat) (b : Bool) (A : AuthAdversary S) :
    𝒟[sampCkPair P (!b) >>= fun p => authCkPreSampleRun1Key S P idx p A] =
      𝒟[authCkCutoffExp1Key S P (if b then idx else idx + 1) A] := by
  unfold authCkPreSampleRun1Key authCkCutoffExp1Key
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep
    (sampCkPair P (!b))
    (authSlotFired S idx)
    (fun q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst))
    (fun p q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst))
    (authCkStepSlot1Key S P idx (sampCkPair P (!b)))
    (authCkStepSlot_slotComp1Key S P idx (sampCkPair P (!b)))
    (authCkStepSlot_run'_some1Key S P idx (sampCkPair P (!b)))
    (fun q hst g => by
      dsimp only [StateT.run_mk]
      rw [authCkStepSlot_run'_none_eq1Key S P idx b q hst])
    (fun p q hst hFired => authCkStepWith_after1Key S P idx b p q hst hFired)
    (authCkStepSlot_fire1Key S P idx (sampCkPair P (!b)))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

end SignalPqxdh.Security
