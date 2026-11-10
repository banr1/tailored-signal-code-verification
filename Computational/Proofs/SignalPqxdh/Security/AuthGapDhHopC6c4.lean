/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c1
import VCVio.EvalDist.Monad.Basic

@[expose] public section
set_option autoImplicit false
open Classical SignalPqxdh SignalPqxdh.Security OracleSpec OracleComp MeasureTheory
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security
def runAuthSendLatchedSim (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthSendLatchedState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthSendLatchedState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthSendLatchedState S) ProbComp) +
    pqxdhAuthSendLatchedStageImpl stage S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)
@[simp]
theorem AuthSendLatchedState.toAuthAdvLatchedState_empty (S : Setup) (secb : Bool) :
    (AuthSendLatchedState.empty S secb).toAuthAdvLatchedState =
      AuthAdvLatchedState.empty S secb := rfl
@[simp]
theorem AuthSendLatchedState.toFg_empty (S : Setup) (secb : Bool) :
    (AuthSendLatchedState.empty S secb).toFg = AuthFgCutoffState.empty S secb := rfl
@[simp]
theorem AuthSendLatchedState.hyb_empty (S : Setup) (secb : Bool) :
    (AuthSendLatchedState.empty S secb).hyb = AuthHybridState.empty S secb := rfl
@[simp]
theorem AuthSendLatchedState.respEkCollLatched_empty (S : Setup) (secb : Bool) :
    (AuthSendLatchedState.empty S secb).respEkCollLatched = false := rfl
theorem map_toAuthAdvLatchedState_pqxdhAuthSendLatchedStageImpl
    (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (s : AuthSendLatchedState S) :
    Prod.map id AuthSendLatchedState.toAuthAdvLatchedState <$>
        ((pqxdhAuthSendLatchedStageImpl stage S P q).run s) =
      (pqxdhAuthAdvLatchedStageImpl stage S P q).run s.toAuthAdvLatchedState := by
  cases q <;>
    simp [pqxdhAuthSendLatchedStageImpl, wrapSendLatched, StateT.run_mk, Prod.map]
theorem map_toAuthAdvLatchedState_fullAuthSendLatchedStageImpl
    (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (s : AuthSendLatchedState S) :
    Prod.map id AuthSendLatchedState.toAuthAdvLatchedState <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthSendLatchedState S) ProbComp) +
        pqxdhAuthSendLatchedStageImpl stage S P) q).run s =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvLatchedState S) ProbComp) +
      pqxdhAuthAdvLatchedStageImpl stage S P) q).run s.toAuthAdvLatchedState := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_toAuthAdvLatchedState_pqxdhAuthSendLatchedStageImpl stage S P gq s
theorem simulateQ_map_toAuthAdvLatchedState_fullAuthSendLatchedStageImpl
    (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    {α : Type} (oa : OracleComp (unifSpec + authSpec S) α)
    (s : AuthSendLatchedState S) :
    let fullSend := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl stage S P
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvLatchedState S) ProbComp) + pqxdhAuthAdvLatchedStageImpl stage S P
    Prod.map id AuthSendLatchedState.toAuthAdvLatchedState <$> ((simulateQ fullSend oa).run s) =
      (simulateQ fullAdv oa).run s.toAuthAdvLatchedState :=
  _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthSendLatchedState.toAuthAdvLatchedState
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl stage S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvLatchedState S) ProbComp) + pqxdhAuthAdvLatchedStageImpl stage S P)
    (map_toAuthAdvLatchedState_fullAuthSendLatchedStageImpl stage S P)
    oa s
theorem mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthSendLatchedState S) (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    (y.1, y.2.toAuthAdvLatchedState) ∈
      support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s.toAuthAdvLatchedState) := by
  rw [← map_toAuthAdvLatchedState_pqxdhAuthSendLatchedStageImpl stage S P q s, support_map]
  exact ⟨y, hy, rfl⟩
theorem advRoLog_length_pqxdhAuthSendLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    y.2.adv.advRoLog.length = s.adv.advRoLog.length + authRoStepInc q :=
  advRoLog_length_pqxdhAuthAdvLatchedStageImpl stage P q s.toAuthAdvLatchedState
    (y.1, y.2.toAuthAdvLatchedState)
    (mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
      stage P q s y hy)
theorem respRecs_length_pqxdhAuthSendLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    y.2.adv.respRecs.length = s.adv.respRecs.length + authRecvStepInc q :=
  respRecs_length_pqxdhAuthAdvLatchedStageImpl stage P q s.toAuthAdvLatchedState
    (y.1, y.2.toAuthAdvLatchedState)
    (mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
      stage P q s y hy)
theorem validAuthHybridRunInv_pqxdhAuthSendLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hInv : ValidAuthHybridRunInv S P s.hyb)
    {y : AuthResponse × AuthSendLatchedState S}
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    ValidAuthHybridRunInv S P y.2.hyb :=
  validAuthHybridRunInv_pqxdhAuthAdvLatchedStageImpl stage P q s.toAuthAdvLatchedState hInv
    (mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
      stage P q s y hy)
theorem isAuthG3Abort_mono_pqxdhAuthSendLatchedStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hAb : isAuthG3Abort P s.hyb = true) (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    isAuthG3Abort P y.2.hyb = true :=
  isAuthG3Abort_mono_pqxdhAuthAdvLatchedStageImpl stage P q s.toAuthAdvLatchedState hAb
    (y.1, y.2.toAuthAdvLatchedState)
    (mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
      stage P q s y hy)
theorem evalDist_simulateQ_sendLatchedStage_eq_uniformBool_of_isAuthG3Abort
    (stage : AuthHybridStage) (S : Setup) (P : Primitives) (secb : Bool)
    (oa : OracleComp (unifSpec + authSpec S) Bool) (st : AuthSendLatchedState S)
    (hAbort : isAuthG3Abort P st.hyb = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl stage S P
    𝒟[(simulateQ full oa).run st >>= fun p => finalizeAuthKosk S P secb p.1 p.2.hyb] =
      𝒟[$ᵗ Bool] :=
  evalDist_simulateQ_eq_uniformBool_of_bad_preserved
    (fun s : AuthSendLatchedState S => isAuthG3Abort P s.hyb)
    (pqxdhAuthSendLatchedStageImpl stage S P)
    (fun q s hAb y hy => isAuthG3Abort_mono_pqxdhAuthSendLatchedStageImpl stage P q s hAb y hy)
    (fun p => finalizeAuthKosk S P secb p.1 p.2.hyb)
    (fun a s hAb => evalDist_finalizeAuthKosk_of_isAuthG3Abort P secb a s.hyb hAb)
    oa st hAbort
theorem evalDist_simulateQ_sendLatchedStage_eq_of_isAuthG3Abort_both
    (S : Setup) (P : Primitives) (secb : Bool) (oa35 oa3 : OracleComp (unifSpec + authSpec S) Bool)
    (s35 s3 : AuthSendLatchedState S) (hAb35 : isAuthG3Abort P s35.hyb = true)
    (hAb3 : isAuthG3Abort P s3.hyb = true) :
    let full35 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl .g3_5 S P
    let full3 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl .g3 S P
    𝒟[(simulateQ full35 oa35).run s35 >>= fun p => finalizeAuthKosk S P secb p.1 p.2.hyb] =
      𝒟[(simulateQ full3 oa3).run s3 >>= fun p => finalizeAuthKosk S P secb p.1 p.2.hyb] := by
  intro full35 full3
  rw [evalDist_simulateQ_sendLatchedStage_eq_uniformBool_of_isAuthG3Abort .g3_5 S P secb oa35 s35
        hAb35,
      evalDist_simulateQ_sendLatchedStage_eq_uniformBool_of_isAuthG3Abort .g3 S P secb oa3 s3 hAb3]
theorem authKoskExpAtStage_eq_sendLatchedStage (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage stage S P A =
    (do
      let secb ← $ᵗ Bool
      let initSt := AuthSendLatchedState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthSendLatchedState S) ProbComp) +
        pqxdhAuthSendLatchedStageImpl stage S P
      let (b', finalSt) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalSt.hyb) := by
  rw [authKoskExpAtStage_eq_advLatchedStage stage S P A]; congr 1; funext secb
  have hsim := congrArg
    (· >>= fun (p : Bool × AuthAdvLatchedState S) => finalizeAuthKosk S P secb p.1 p.2.hyb)
    (simulateQ_map_toAuthAdvLatchedState_fullAuthSendLatchedStageImpl stage S P A.run
      (AuthSendLatchedState.empty S secb))
  dsimp only [AuthSendLatchedState.toAuthAdvLatchedState_empty] at hsim
  rw [← hsim, map_eq_bind_pure_comp]
  simp [bind_assoc, Prod.map]
theorem evalDist_sampleScalar32_ec_coll_le (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (targetPk : Bytes) :
    𝒟[sampleScalar32 >>= fun ekASk =>
      pure (P.pow8 (P.x25519Base ekASk) == P.pow8 targetPk)] {true} ≤
      ENNReal.ofReal Pfixed_pk_ec := by
  rw [evalDist_bind_true_eq_probExpect]; exact probExpect_sampleScalar32_ec_coll_le P hP targetPk
theorem evalDist_sampleScalar32_latchRespEkCollAtSend_le (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) :
    ∀ (respRecs : List AuthRespRecord), 𝒟[sampleScalar32 >>= fun ekASk =>
        pure (latchRespEkCollAtSend P respRecs ekASk)] {true} ≤
        (respRecs.length : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec
  | [] => by simp [latchRespEkCollAtSend]
  | r :: rs => by
    have h_le :
        𝒟[sampleScalar32 >>= fun ekASk =>
          pure (latchRespEkCollAtSend P (r :: rs) ekASk)] {true} ≤
        𝒟[sampleScalar32 >>= fun ekASk =>
          pure (P.pow8 (P.x25519Base ekASk) == P.pow8 r.ekAPk)] {true} +
        𝒟[sampleScalar32 >>= fun ekASk =>
          pure (latchRespEkCollAtSend P rs ekASk)] {true} := by
      rw [evalDist_bind_true_eq_probExpect, evalDist_bind_true_eq_probExpect,
          evalDist_bind_true_eq_probExpect]
      let _ : MeasurableSpace Bytes := ⊤
      have _ : DiscreteMeasurableSpace Bytes := ⟨fun _ => trivial⟩
      unfold probExpect; rw [← MeasureTheory.lintegral_add_left Measurable.of_discrete]
      apply MeasureTheory.lintegral_mono; intro ekASk
      simp only [latchRespEkCollAtSend, List.any_cons]
      by_cases h1 : (P.pow8 (P.x25519Base ekASk) == P.pow8 r.ekAPk) = true
      · simp [h1]
      · simp [h1]
    calc 𝒟[sampleScalar32 >>= fun ekASk =>
          pure (latchRespEkCollAtSend P (r :: rs) ekASk)] {true}
        ≤ 𝒟[sampleScalar32 >>= fun ekASk =>
            pure (P.pow8 (P.x25519Base ekASk) == P.pow8 r.ekAPk)] {true} +
          𝒟[sampleScalar32 >>= fun ekASk =>
            pure (latchRespEkCollAtSend P rs ekASk)] {true} := h_le
      _ ≤ ENNReal.ofReal Pfixed_pk_ec +
          (rs.length : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec :=
        add_le_add (evalDist_sampleScalar32_ec_coll_le P hP r.ekAPk)
          (evalDist_sampleScalar32_latchRespEkCollAtSend_le P hP rs)
      _ = ((r :: rs).length : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
theorem evalDist_sampleScalar32_latchRespEkCollAtSend_le_of_length_le (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (respRecs : List AuthRespRecord) (maxRecv : ℕ)
    (hLen : respRecs.length ≤ maxRecv) :
    𝒟[sampleScalar32 >>= fun ekASk =>
      pure (latchRespEkCollAtSend P respRecs ekASk)] {true} ≤
      (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec :=
  le_trans (evalDist_sampleScalar32_latchRespEkCollAtSend_le P hP respRecs)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hLen) zero_le)
def authSendStepInc {S : Setup} : AuthQuery S → ℕ
  | .sendOPK _ _ _ _ _   => 1
  | .sendNoOPK _ _ _ _ _ => 1
  | _                    => 0
theorem authSendStepInc_eq_ite {S : Setup} (q : AuthQuery S) :
    authSendStepInc q = (if isAuthSendQuery (Sum.inr q) then 1 else 0) := by
  cases q <;> rfl
theorem authSendStepInc_add_fuel_eq_of_queryGuard {S : Setup} (gq : AuthQuery S)
    {fuelSend : ℕ}
    (hGuard : ¬isAuthSendQuery (Sum.inr gq) ∨ 0 < fuelSend) :
    authSendStepInc gq +
      (if isAuthSendQuery (Sum.inr gq) then fuelSend - 1 else fuelSend) = fuelSend := by
  rw [authSendStepInc_eq_ite]
  by_cases hPSend : isAuthSendQuery (Sum.inr gq)
  · rcases hGuard with hF | hPos
    · exact False.elim (hF hPSend)
    · simp only [hPSend, ↓reduceIte]; omega
  · simp only [hPSend, ↓reduceIte]; omega
@[simp]
theorem latchRespEkCollSendStep_true_right {S : Setup} (P : Primitives)
    (sPre sPost : AuthAdvLatchedState S) :
    latchRespEkCollSendStep P sPre sPost true = true := by
  unfold latchRespEkCollSendStep
  rfl
@[simp]
theorem latchRespEkCollSendStep_self {S : Setup} (P : Primitives)
    (s : AuthAdvLatchedState S) :
    latchRespEkCollSendStep P s s false = false := by
  unfold latchRespEkCollSendStep
  cases s.hyb.base.sessions <;> simp
theorem respEkCollLatched_mono_pqxdhAuthSendLatchedStageImpl {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (q : AuthQuery S)
    (s : AuthSendLatchedState S) (hBad : s.respEkCollLatched = true)
    (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    y.2.respEkCollLatched = true := by
  cases q <;>
    simp only [pqxdhAuthSendLatchedStageImpl, wrapSendLatched, StateT.run_mk,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy <;>
    rcases hy with ⟨p, _, rfl⟩ <;>
    simp [hBad]
theorem latchRespEkCollSendStep_finishAuthHybridSendPure_imp {S : Setup} (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk ephASk spqrCoins ss kemCt : Bytes)
    (s : AuthAdvLatchedState S) (drKey : DRKey) (roCache' : List (Bytes × DRKey))
    (rk1 ck1_0 : Bytes) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hTrue : latchRespEkCollSendStep P s
      (withLatchedHyb s (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
        ekASk ephASk spqrCoins ss kemCt s.hyb drKey roCache' rk1 ck1_0 rootRoCache').2)
      false = true) :
    latchRespEkCollAtSend P s.adv.respRecs ekASk = true := by
  unfold finishAuthHybridSendPure at hTrue
  cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
  | none =>
    rw [hSpqr] at hTrue; dsimp only at hTrue
    rw [withLatchedHyb_self, latchRespEkCollSendStep_self] at hTrue
    nomatch hTrue
  | some pqr =>
    rcases pqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
    rw [hSpqr] at hTrue; unfold latchRespEkCollSendStep mkSendSessEntry at hTrue
    dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb] at hTrue
    simpa using hTrue
theorem latchRespEkCollSendStep_of_mem_support_finishAuthHybridSendPost {S : Setup}
    (useRo : Bool) (P : Primitives) (sid : SessionId S)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (uEntry : PrincipalEntry)
    (ekASk ephASk spqrCoins ss kemCt : Bytes) (s : AuthAdvLatchedState S)
    (drKey : DRKey) (roCache' : List (Bytes × DRKey))
    {p : AuthResponse × AuthAdvLatchedState S}
    (hp : p ∈ support (finishAuthHybridSendPost useRo P sid bundle m0 m1 uEntry
      ekASk ephASk spqrCoins ss kemCt s drKey roCache'))
    (hTrue : latchRespEkCollSendStep P s p.2 false = true) :
    latchRespEkCollAtSend P s.adv.respRecs ekASk = true := by
  unfold finishAuthHybridSendPost at hp
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
  rcases hp with ⟨⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, rfl⟩
  exact latchRespEkCollSendStep_finishAuthHybridSendPure_imp P sid bundle m0 m1 uEntry
    ekASk ephASk spqrCoins ss kemCt s drKey roCache' rk1 ck1_0 rootRoCache' hTrue
theorem evalDist_bind_pure_le_of_support_imp {α : Type} (m : ProbComp α)
    (f : α → Bool) (b : Bool) (hImp : ∀ x ∈ support m, f x = true → b = true) :
    𝒟[m >>= fun x => pure (f x)] {true} ≤ 𝒟[(pure b : ProbComp Bool)] {true} := by
  rw [evalDist_bind_true_eq_probExpect, ← probExpect_const m (𝒟[(pure b : ProbComp Bool)] {true})]
  refine probExpect_mono_of_support m _ _ (fun x hx => ?_)
  cases hf : f x
  · simp
  · rw [hImp x hx hf]
theorem evalDist_bind_pure_eq_zero_of_support_false {α : Type} (m : ProbComp α)
    (f : α → Bool) (hFalse : ∀ x ∈ support m, f x = false) :
    𝒟[m >>= fun x => pure (f x)] {true} = 0 := by
  refine le_antisymm ?_ zero_le
  simpa using evalDist_bind_pure_le_of_support_imp m f false
    (fun x hx h => by rw [hFalse x hx] at h; exact h)
theorem evalDist_sampleScalar32_bind_le_of_support_imp {α : Type}
    (cont : Bytes → ProbComp α) (f : α → Bool) (g : Bytes → Bool)
    (hImp : ∀ ekASk ∈ support sampleScalar32, ∀ p ∈ support (cont ekASk),
      f p = true → g ekASk = true) :
    𝒟[(sampleScalar32 >>= cont) >>= fun p => pure (f p)] {true} ≤
      𝒟[sampleScalar32 >>= fun ekASk => pure (g ekASk)] {true} := by
  rw [evalDist_bind_true_eq_probExpect (sampleScalar32 >>= cont),
      evalDist_bind_true_eq_probExpect sampleScalar32, probExpect_bind]
  refine probExpect_mono_of_support sampleScalar32 _ _ (fun ekASk hek => ?_)
  rw [← evalDist_bind_true_eq_probExpect (cont ekASk)]
  exact evalDist_bind_pure_le_of_support_imp (cont ekASk) f (g ekASk) (hImp ekASk hek)
theorem evalDist_runAuthHybridSendLatched_latchRespEkCollSendStep_le {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s : AuthAdvLatchedState S)
    (hAead : stage.idealFreshAead = false := by rfl) (hRk : stage.idealRk = false := by rfl)
    (hCk : stage.idealCk = false := by rfl) (hMk : stage.idealMsgKeys = false := by rfl) :
    𝒟[runAuthHybridSendLatched stage S P sid u bundle m0 m1 s >>=
        fun p => pure (latchRespEkCollSendStep P s p.2 false)] {true} ≤
      𝒟[sampleScalar32 >>= fun ekASk =>
        pure (latchRespEkCollAtSend P s.adv.respRecs ekASk)] {true} := by
  have hRet :
      𝒟[(pure (.noneResp, s) : ProbComp (AuthResponse × AuthAdvLatchedState S)) >>=
          fun p => pure (latchRespEkCollSendStep P s p.2 false)] {true} ≤
        𝒟[sampleScalar32 >>= fun ekASk =>
          pure (latchRespEkCollAtSend P s.adv.respRecs ekASk)] {true} := by
    rw [evalDist_bind_pure_eq_zero_of_support_false]; · exact zero_le
    intro p hp; simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp
    exact latchRespEkCollSendStep_self P s
  rw [runAuthHybridSendLatched_eq stage P sid u bundle m0 m1 s hAead hRk hCk hMk]; dsimp only
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte]; exact hRet
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (s.hyb.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte]; exact hRet
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => dsimp only; exact hRet
      | some up =>
        rcases up with ⟨_, uEntry⟩; dsimp only
        cases findHonestPrincipal P s.hyb.base.principals bundle.ikB with
        | none =>
          dsimp only
          by_cases h3 : (!false && m0 != m1) = true
          · simp only [h3, ↓reduceIte]; exact hRet
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            by_cases h4 : (!koskBundleOk P s.hyb.base.principals s.hyb.base.spkBundles
                             s.hyb.base.opkEntries s.hyb.base.advKeys bundle) = true
            · simp only [h4, ↓reduceIte]; exact hRet
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]
              refine evalDist_sampleScalar32_bind_le_of_support_imp _ _ _
                (fun ekASk _ p hp hLatch => ?_)
              simp only [MonadAttach.mem_support_bind] at hp
              rcases hp with ⟨kemCoins, _, ephASk, _, spqrCoins, _, hp'⟩
              by_cases h5 : (!(P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeEC bundle.spkB) bundle.spkSig &&
                               P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp'
                subst hp'; rw [latchRespEkCollSendStep_self] at hLatch; nomatch hLatch
              · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hp'
                cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
                | none =>
                  simp only [hKem, support_pure, Set.mem_singleton_iff] at hp'
                  subst hp'; rw [latchRespEkCollSendStep_self] at hLatch; nomatch hLatch
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩
                  simp only [hKem, MonadAttach.mem_support_bind] at hp'
                  rcases hp' with ⟨⟨drKey, roCache'⟩, _, hpPost⟩
                  exact latchRespEkCollSendStep_of_mem_support_finishAuthHybridSendPost
                    true P sid bundle m0 m1 uEntry ekASk ephASk spqrCoins ss kemCt s
                    drKey roCache' hpPost hLatch
        | some fp =>
          rcases fp with ⟨_, pEntry⟩; dsimp only
          by_cases h3 : (!!pEntry.corrupted && m0 != m1) = true
          · simp only [h3, ↓reduceIte]; exact hRet
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            by_cases h4 : (!koskBundleOk P s.hyb.base.principals s.hyb.base.spkBundles
                             s.hyb.base.opkEntries s.hyb.base.advKeys bundle) = true
            · simp only [h4, ↓reduceIte]; exact hRet
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]
              refine evalDist_sampleScalar32_bind_le_of_support_imp _ _ _
                (fun ekASk _ p hp hLatch => ?_)
              simp only [MonadAttach.mem_support_bind] at hp
              rcases hp with ⟨kemCoins, _, ephASk, _, spqrCoins, _, hp'⟩
              by_cases h5 : (!(P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeEC bundle.spkB) bundle.spkSig &&
                               P.sigVerify (resolveSigPk P s.hyb.base.principals bundle.ikB)
                                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp'
                subst hp'; rw [latchRespEkCollSendStep_self] at hLatch; nomatch hLatch
              · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hp'
                cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
                | none =>
                  simp only [hKem, support_pure, Set.mem_singleton_iff] at hp'
                  subst hp'; rw [latchRespEkCollSendStep_self] at hLatch; nomatch hLatch
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩
                  simp only [hKem, MonadAttach.mem_support_bind] at hp'
                  rcases hp' with ⟨⟨drKey, roCache'⟩, _, hpPost⟩
                  exact latchRespEkCollSendStep_of_mem_support_finishAuthHybridSendPost
                    true P sid bundle m0 m1 uEntry ekASk ephASk spqrCoins ss kemCt s
                    drKey roCache' hpPost hLatch
theorem evalDist_pqxdhAuthSendLatchedStageImpl_respEkCollLatched_le {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRecv : ℕ) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hAead : stage.idealFreshAead = false := by rfl) (hRk : stage.idealRk = false := by rfl)
    (hCk : stage.idealCk = false := by rfl) (hMk : stage.idealMsgKeys = false := by rfl)
    (hFalse : s.respEkCollLatched = false) (hRecvLen : s.adv.respRecs.length ≤ maxRecv) :
    𝒟[((pqxdhAuthSendLatchedStageImpl stage S P q).run s) >>=
        fun y => pure y.2.respEkCollLatched] {true} ≤
      (authSendStepInc q : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [authSendStepInc, Nat.cast_one, one_mul]
    refine le_trans ?_
      (evalDist_sampleScalar32_latchRespEkCollAtSend_le_of_length_le P hP
        s.adv.respRecs maxRecv hRecvLen)
    unfold pqxdhAuthSendLatchedStageImpl pqxdhAuthAdvLatchedStageImpl
      pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl wrapSendLatched
    simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind, hFalse,
      Bool.true_and]
    by_cases hWon : s.adv.hyb.base.hasWonAuth = true
    · simp [hWon]
    · simp only [hWon, Bool.false_eq_true, ↓reduceIte]
      by_cases hNone : bundle.opkB?.isNone = true
      · simp [hNone]
      · simp only [hNone, Bool.false_eq_true, ↓reduceIte]
        simpa [runAuthHybridSendLatched, withLatchedHyb, AuthAdvLatchedState.hyb, bind_assoc] using
          evalDist_runAuthHybridSendLatched_latchRespEkCollSendStep_le stage P
            (.sendOPK u i) u bundle m0 m1 s.toAuthAdvLatchedState hAead hRk hCk hMk
  | sendNoOPK u i bundle m0 m1 =>
    simp only [authSendStepInc, Nat.cast_one, one_mul]
    refine le_trans ?_
      (evalDist_sampleScalar32_latchRespEkCollAtSend_le_of_length_le P hP
        s.adv.respRecs maxRecv hRecvLen)
    unfold pqxdhAuthSendLatchedStageImpl pqxdhAuthAdvLatchedStageImpl
      pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl wrapSendLatched
    simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind, hFalse,
      Bool.true_and]
    by_cases hWon : s.adv.hyb.base.hasWonAuth = true
    · simp [hWon]
    · simp only [hWon, Bool.false_eq_true, ↓reduceIte]
      by_cases hSome : bundle.opkB?.isSome = true
      · simp [hSome]
      · simp only [hSome, Bool.false_eq_true, ↓reduceIte]
        simpa [runAuthHybridSendLatched, withLatchedHyb, AuthAdvLatchedState.hyb, bind_assoc] using
          evalDist_runAuthHybridSendLatched_latchRespEkCollSendStep_le stage P
            (.sendNoOPK u i) u bundle m0 m1 s.toAuthAdvLatchedState hAead hRk hCk hMk
  | _ =>
    rw [evalDist_bind_pure_eq_zero_of_support_false]
    · exact zero_le
    intro y hy
    simp only [pqxdhAuthSendLatchedStageImpl, StateT.run_mk, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩; exact hFalse
theorem evalDist_simulateQ_sendLatchedStage_respEkCollLatched_le {S : Setup} {α : Type}
    (stage : AuthHybridStage) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRecv : ℕ)
    (hAead : stage.idealFreshAead = false := by rfl) (hRk : stage.idealRk = false := by rfl)
    (hCk : stage.idealCk = false := by rfl) (hMk : stage.idealMsgKeys = false := by rfl)
    (oa : OracleComp (unifSpec + authSpec S) α) (fuelSend fuelRecv : ℕ)
    (hQbSend : IsQueryBoundP oa isAuthSendQuery fuelSend)
    (hQbRecv : IsQueryBoundP oa isAuthRecvQuery fuelRecv) (s : AuthSendLatchedState S)
    (hRecvBudget : s.adv.respRecs.length + fuelRecv ≤ maxRecv) :
    let fullSend := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl stage S P
    𝒟[(simulateQ fullSend oa).run s >>= fun p => pure p.2.respEkCollLatched] {true} ≤
      𝒟[(pure s.respEkCollLatched : ProbComp Bool)] {true} +
      (fuelSend : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
  intro fullSend
  induction oa using OracleComp.inductionOn generalizing s fuelSend fuelRecv with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact le_self_add
  | query_bind q mx ih =>
    by_cases hBad : s.respEkCollLatched = true
    · have hPureOne : 𝒟[(pure s.respEkCollLatched : ProbComp Bool)] {true} = 1 := by
        simp [hBad]
      rw [hPureOne]; exact le_trans MeasureTheory.prob_le_one le_self_add
    · have hFalse : s.respEkCollLatched = false := Bool.eq_false_iff.mpr hBad
      have hPureZero : 𝒟[(pure s.respEkCollLatched : ProbComp Bool)] {true} = 0 := by
        simp [hFalse]
      rw [hPureZero, zero_add]; rw [isQueryBoundP_query_bind_iff] at hQbSend hQbRecv
      rcases q with uq | gq
      · rcases hQbSend with ⟨_, hContSend⟩
        rcases hQbRecv with ⟨_, hContRecv⟩
        simp only [isAuthSendQuery, ↓reduceIte] at hContSend
        simp only [isAuthRecvQuery, ↓reduceIte] at hContRecv; dsimp only [fullSend]
        rw [simulateQ_run_query_inl, bind_assoc]
        let _ : MeasurableSpace ((unifSpec + authSpec S).Range (Sum.inl uq)) := ⊤
        have _ : DiscreteMeasurableSpace ((unifSpec + authSpec S).Range (Sum.inl uq)) :=
          ⟨fun _ => trivial⟩
        have hUnifEq :
            𝒟[(liftM (unifSpec.query uq) : ProbComp _) >>= fun u =>
              (simulateQ fullSend (mx u)).run s >>= fun p => pure p.2.respEkCollLatched]
              {true} =
            probExpect (liftM (unifSpec.query uq)) (fun u =>
              𝒟[(simulateQ fullSend (mx u)).run s >>=
                fun p => pure p.2.respEkCollLatched] {true}) := by
          unfold probExpect
          rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
                Measurable.of_discrete.aemeasurable]
        rw [hUnifEq]
        refine probExpect_const_le_of_support _ _ _ (fun u _ => ?_)
        have hIH := ih u fuelSend fuelRecv (hContSend u) (hContRecv u) s hRecvBudget
        rw [hPureZero, zero_add] at hIH; exact hIH
      · rcases hQbSend with ⟨hSendGuard, hContSend⟩
        rcases hQbRecv with ⟨hRecvGuard, hContRecv⟩
        have hRecv := authRecvStepInc_le_of_queryGuard gq hRecvGuard hRecvBudget
        have hRecvLen : s.adv.respRecs.length ≤ maxRecv := by
          have := hRecv.1; omega
        let fuelSend' := if isAuthSendQuery (Sum.inr gq) then fuelSend - 1 else fuelSend
        let fuelRecv' := if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv
        let mStep := ((pqxdhAuthSendLatchedStageImpl stage S P gq).run s)
        dsimp only [fullSend]; rw [simulateQ_run_query_inr, bind_assoc]
        have hBindEq :
            𝒟[mStep >>= fun y =>
              (simulateQ fullSend (mx y.1)).run y.2 >>= fun p => pure p.2.respEkCollLatched]
              {true} =
            probExpect mStep (fun y =>
              𝒟[(simulateQ fullSend (mx y.1)).run y.2 >>=
                fun p => pure p.2.respEkCollLatched] {true}) := by
          let _ : MeasurableSpace (AuthResponse × AuthSendLatchedState S) := ⊤
          have _ : DiscreteMeasurableSpace (AuthResponse × AuthSendLatchedState S) :=
            ⟨fun _ => trivial⟩
          unfold probExpect
          rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
                Measurable.of_discrete.aemeasurable]
        rw [hBindEq]
        calc probExpect mStep (fun y =>
              𝒟[(simulateQ fullSend (mx y.1)).run y.2 >>=
                fun p => pure p.2.respEkCollLatched] {true})
            ≤ probExpect mStep (fun y =>
                𝒟[(pure y.2.respEkCollLatched : ProbComp Bool)] {true} +
                (fuelSend' : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec) := by
              refine probExpect_mono_of_support mStep _ _ (fun y hy => ?_)
              have hRecvLen' := respRecs_length_pqxdhAuthSendLatchedStageImpl stage P gq s y hy
              exact ih y.1 fuelSend' fuelRecv' (hContSend y.1) (hContRecv y.1) y.2
                (by rw [hRecvLen']; exact hRecv.2)
          _ ≤ probExpect mStep (fun y =>
                𝒟[(pure y.2.respEkCollLatched : ProbComp Bool)] {true}) +
              probExpect mStep (fun _ =>
                (fuelSend' : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec) :=
              probExpect_add_le mStep _ _ _ (fun _ => le_rfl)
          _ = 𝒟[mStep >>= fun y => pure y.2.respEkCollLatched] {true} +
              (fuelSend' : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
              rw [← evalDist_bind_true_eq_probExpect, probExpect_const]
          _ ≤ (authSendStepInc gq : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec +
              (fuelSend' : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
              gcongr
              exact evalDist_pqxdhAuthSendLatchedStageImpl_respEkCollLatched_le stage P hP maxRecv
                gq s hAead hRk hCk hMk hFalse hRecvLen
          _ = (fuelSend : ℝ≥0∞) * (maxRecv : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
              rw [← add_mul, ← add_mul, ← Nat.cast_add,
                  authSendStepInc_add_fuel_eq_of_queryGuard gq hSendGuard]
theorem prob_respEkCollLatched_runAuthSendLatchedSim_le_ennreal (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (hAead : stage.idealFreshAead = false := by rfl) (hRk : stage.idealRk = false := by rfl)
    (hCk : stage.idealCk = false := by rfl) (hMk : stage.idealMsgKeys = false := by rfl) :
    𝒟[runAuthSendLatchedSim stage S P A.1 >>= fun x => pure x.2.2.respEkCollLatched] {true} ≤
      (S.N_send_tot : ℝ≥0∞) * (S.N_recv_tot : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
  unfold runAuthSendLatchedSim; simp only [bind_assoc, pure_bind]
  let fullSend := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl stage S P
  have hSecb : ∀ secb : Bool,
      𝒟[(simulateQ fullSend A.1.run).run (AuthSendLatchedState.empty S secb) >>=
          fun p => pure p.2.respEkCollLatched] {true} ≤
        (S.N_send_tot : ℝ≥0∞) * (S.N_recv_tot : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec := by
    intro secb
    have hSim := evalDist_simulateQ_sendLatchedStage_respEkCollLatched_le stage P hP S.N_recv_tot
      hAead hRk hCk hMk A.1.run S.N_send_tot S.N_recv_tot
      (QueryBounded.auth_send A.2) (QueryBounded.auth_recv A.2) (AuthSendLatchedState.empty S secb)
      (by simp [AuthSendLatchedState.empty, AuthAdvLatchedState.empty, AuthAdvCutoffState.empty])
    have hZero :
        𝒟[(pure (AuthSendLatchedState.empty S secb).respEkCollLatched : ProbComp Bool)]
          {true} = 0 := by simp
    rw [hZero, zero_add] at hSim; exact hSim
  let _ : MeasurableSpace Bool := ⊤
  have _ : DiscreteMeasurableSpace Bool := ⟨fun _ => trivial⟩
  have hOuter :
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
        (simulateQ fullSend A.1.run).run (AuthSendLatchedState.empty S secb) >>=
          fun p => pure p.2.respEkCollLatched] {true} =
      probExpect ($ᵗ Bool) (fun secb =>
        𝒟[(simulateQ fullSend A.1.run).run (AuthSendLatchedState.empty S secb) >>=
          fun p => pure p.2.respEkCollLatched] {true}) := by
    unfold probExpect
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  rw [hOuter]; exact probExpect_const_le_of_support ($ᵗ Bool) _ _ (fun secb _ => hSecb secb)
theorem prob_respEkCollLatched_runAuthSendLatchedSim_le (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (hAead : stage.idealFreshAead = false := by rfl) (hRk : stage.idealRk = false := by rfl)
    (hCk : stage.idealCk = false := by rfl) (hMk : stage.idealMsgKeys = false := by rfl) :
    (𝒟[runAuthSendLatchedSim stage S P A.1 >>=
        fun x => pure x.2.2.respEkCollLatched] {true}).toReal ≤
      (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 := by
  have hEnn := prob_respEkCollLatched_runAuthSendLatchedSim_le_ennreal stage S P hP b A
    hAead hRk hCk hMk
  have hRhs :
      (S.N_send_tot : ℝ≥0∞) * (S.N_recv_tot : ℝ≥0∞) * ENNReal.ofReal Pfixed_pk_ec =
      ENNReal.ofReal ((S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250) := by
    have hEqReal :
        (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 =
        (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) * Pfixed_pk_ec := by
      unfold Pfixed_pk_ec; ring
    rw [hEqReal, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hRhs] at hEnn
  have hReal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hEnn
  rwa [ENNReal.toReal_ofReal (by positivity)] at hReal
theorem prob_respEkCollLatched_runAuthSendLatchedSim_g3_le
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthSendLatchedSim .g3 S P A.1 >>=
        fun x => pure x.2.2.respEkCollLatched] {true}).toReal ≤
      (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 :=
  prob_respEkCollLatched_runAuthSendLatchedSim_le .g3 S P hP b A
theorem evalDist_bind_or_le_add {α : Type} (m : ProbComp α) (f g : α → Bool) :
    𝒟[m >>= fun x => pure (f x || g x)] {true} ≤
      𝒟[m >>= fun x => pure (f x)] {true} + 𝒟[m >>= fun x => pure (g x)] {true} := by
  rw [evalDist_bind_true_eq_probExpect, evalDist_bind_true_eq_probExpect,
      evalDist_bind_true_eq_probExpect]
  refine probExpect_add_le m _ _ _ (fun x => ?_)
  cases f x <;> cases g x <;> simp
theorem toReal_evalDist_bind_or_le_add {α : Type} (m : ProbComp α) (f g : α → Bool) :
    (𝒟[m >>= fun x => pure (f x || g x)] {true}).toReal ≤
      (𝒟[m >>= fun x => pure (f x)] {true}).toReal +
      (𝒟[m >>= fun x => pure (g x)] {true}).toReal := by
  have hLe := evalDist_bind_or_le_add m f g
  have hTop : 𝒟[m >>= fun x => pure (f x)] {true} + 𝒟[m >>= fun x => pure (g x)] {true} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hReal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) hTop).mpr hLe
  rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hReal
theorem badFg_or_respEkCollLatched_mono_pqxdhAuthSendLatchedStageImpl {S : Setup}
    (stage : AuthHybridStage) (P : Primitives) (maxRo maxRecv : ℕ)
    (badFg : AuthFgCutoffState S → Bool)
    (hBadMono : ∀ (q : AuthQuery S) (s : AuthAdvLatchedState S), ValidAuthHybridRunInv S P s.hyb →
      s.adv.advRoLog.length + authRoStepInc q ≤ maxRo →
      s.adv.respRecs.length + authRecvStepInc q ≤ maxRecv →
      badFg s.toFg = true →
      ∀ y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s), badFg y.2.toFg = true)
    (q : AuthQuery S) (s : AuthSendLatchedState S) (hRunInv : ValidAuthHybridRunInv S P s.hyb)
    (hRo : s.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecv : s.adv.respRecs.length + authRecvStepInc q ≤ maxRecv)
    (hBad : (badFg s.toFg || s.respEkCollLatched) = true)
    (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    (badFg y.2.toFg || y.2.respEkCollLatched) = true := by
  rcases Bool.or_eq_true_iff.mp hBad with hFg | hColl
  · have hyAdv :=
      mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
        stage P q s y hy
    exact Bool.or_eq_true_iff.mpr (Or.inl
      (hBadMono q s.toAuthAdvLatchedState hRunInv hRo hRecv hFg _ hyAdv))
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (respEkCollLatched_mono_pqxdhAuthSendLatchedStageImpl stage P q s hColl y hy))
private theorem find?_eq_some_of_nodup_map_c6c4 {α β : Type} [BEq β] [LawfulBEq β]
    (f : α → β) {l : List α} (hNodup : (l.map f).Nodup) {x : α} (hx : x ∈ l) :
    l.find? (fun y => f y == f x) = some x := by
  induction l with
  | nil => nomatch hx
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup; rcases List.mem_cons.mp hx with rfl | hTl
    · simp [List.find?]
    · have hNe : (f hd == f x) = false := by
        cases hBeq : (f hd == f x)
        · rfl
        · exact False.elim (hNodup.1 (beq_iff_eq.mp hBeq ▸ List.mem_map_of_mem hTl))
      simp only [List.find?_cons, hNe]; exact ih hNodup.2 hTl
private theorem find?_eraseSpkBundlesFg_eq (S : Setup) (bIdx : ℕ) (bKey : Nat × Nat) :
    ∀ (L : List ((Nat × Nat) × SpkBundleEntry)),
      (eraseSpkBundlesFg S bIdx L).find? (fun (idx, _) => idx == bKey) =
        (L.find? (fun (idx, _) => idx == bKey)).map
          (fun (k, b) => (k, eraseSpkBundleEntryFg S bIdx k b))
  | [] => rfl
  | (idx, b) :: tl => by
    unfold eraseSpkBundlesFg; simp only [List.map_cons, List.find?_cons]
    cases (idx == bKey)
    · exact find?_eraseSpkBundlesFg_eq S bIdx bKey tl
    · rfl
private theorem respAuthCand_mono_of_traceSub {S : Setup} (P : Primitives) (bIdx : ℕ)
    {st1 st2 : AuthState S} (hKS1 : ValidAuthKeyStoresFull S P st1)
    (hKS2 : ValidAuthKeyStoresFull S P st2) (hSub : AuthBaseTraceSub st1 st2)
    (bKey : Nat × Nat) (pk : Bytes)
    (hGuard : respAuthCandGuard S (eraseSpkBundlesFg S bIdx st1.spkBundles) bKey = true) :
    respAuthCandGuard S (eraseSpkBundlesFg S bIdx st2.spkBundles) bKey = true ∧
    respAuthCand S P (eraseSpkBundlesFg S bIdx st2.spkBundles) bKey pk =
      respAuthCand S P (eraseSpkBundlesFg S bIdx st1.spkBundles) bKey pk := by
  have hLen1 : (eraseSpkBundlesFg S bIdx st1.spkBundles).length ≤ S.N_dh := by
    unfold eraseSpkBundlesFg; rw [List.length_map]
    exact (validAuthKeyStoresFull_lengths_le S P st1 hKS1).2.1
  have hLen2 : (eraseSpkBundlesFg S bIdx st2.spkBundles).length ≤ S.N_dh := by
    unfold eraseSpkBundlesFg; rw [List.length_map]
    exact (validAuthKeyStoresFull_lengths_le S P st2 hKS2).2.1
  unfold respAuthCandGuard at hGuard ⊢
  unfold respAuthCand
  rw [List.take_of_length_le hLen1, find?_eraseSpkBundlesFg_eq] at hGuard ⊢
  rw [List.take_of_length_le hLen2, find?_eraseSpkBundlesFg_eq]
  cases hF1 : st1.spkBundles.find? (fun (idx, _) => idx == bKey) with
  | none => rw [hF1] at hGuard; nomatch hGuard
  | some p =>
    rcases p with ⟨idx, b⟩
    have hMem1 : (idx, b) ∈ st1.spkBundles := List.mem_of_find?_eq_some hF1
    have hIdxEq : idx = bKey :=
      beq_iff_eq.mp (List.find?_some
        (p := fun (x : (Nat × Nat) × SpkBundleEntry) => x.1 == bKey) hF1)
    subst idx
    have hMem2 : (bKey, b) ∈ st2.spkBundles := hSub.spkBundles_sub.subset hMem1
    have hNodup : (st2.spkBundles.map Prod.fst).Nodup := by
      have hN := hKS2.1.2.1.2
      rw [show st2.spkBundles.map (fun e => ecSpkSlotIdx S e.1) =
        (st2.spkBundles.map Prod.fst).map (ecSpkSlotIdx S) by rw [List.map_map]; rfl] at hN
      exact List.Nodup.of_map _ hN
    have hF2 : st2.spkBundles.find? (fun (idx, _) => idx == bKey) = some (bKey, b) :=
      find?_eq_some_of_nodup_map_c6c4 Prod.fst hNodup hMem2
    rw [hF1] at hGuard; rw [hF2]; exact ⟨hGuard, rfl⟩
private theorem lookupAuthSpkSkTake_nonEmpty_info {S : Setup} (P : Primitives) (bIdx : ℕ)
    {st : AuthState S} (hKS : ValidAuthKeyStoresFull S P st) (spkPk : Bytes)
    (hNonEmpty :
      (!(lookupAuthSpkSkTake S P (eraseSpkBundlesFg S bIdx st.spkBundles)
        (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) spkPk).isEmpty) = true) :
    P.pow8 (P.x25519Base (lookupAuthSpkSkTake S P (eraseSpkBundlesFg S bIdx st.spkBundles)
        (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) spkPk)) = P.pow8 spkPk ∧
    ((∃ kv ∈ st.spkBundles,
        (FgGapDh.spkBundleFlatIdxVal S kv.1 == bIdx) = false ∧ P.pow8 kv.2.spkPk = P.pow8 spkPk) ∨
      (∃ kv ∈ st.advKeys, P.pow8 kv.2 = P.pow8 spkPk)) := by
  have hLen : (eraseSpkBundlesFg S bIdx st.spkBundles).length ≤ S.N_dh := by
    unfold eraseSpkBundlesFg; rw [List.length_map]
    exact (validAuthKeyStoresFull_lengths_le S P st hKS).2.1
  revert hNonEmpty; unfold lookupAuthSpkSkTake; dsimp only; rw [List.take_of_length_le hLen]
  cases hF1 : (eraseSpkBundlesFg S bIdx st.spkBundles).find?
      (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == P.pow8 spkPk) with
  | some p =>
    rcases p with ⟨idx, b'⟩; dsimp only; intro _
    have hMemE := List.mem_of_find?_eq_some hF1
    have hPred := Bool.and_eq_true_iff.mp (List.find?_some
      (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
        !x.2.spkSk.isEmpty && P.pow8 x.2.spkPk == P.pow8 spkPk) hF1)
    unfold eraseSpkBundlesFg at hMemE; rcases List.mem_map.mp hMemE with ⟨⟨idx0, b0⟩, hMem0, hEq0⟩
    unfold eraseSpkBundleEntryFg at hEq0; dsimp only at hEq0
    cases hFlat : (FgGapDh.spkBundleFlatIdxVal S idx0 == bIdx)
    · simp only [hFlat, Bool.false_eq_true, ↓reduceIte] at hEq0
      injection hEq0 with hIdx hb; subst hIdx; subst hb
      have hbPk := (hKS.1.2.2.2.2.1 (idx0, b0) hMem0).2.1
      have hPow := beq_iff_eq.mp hPred.2
      exact ⟨by rw [← hbPk, hPow], Or.inl ⟨(idx0, b0), hMem0, hFlat, hPow⟩⟩
    · simp only [hFlat, ↓reduceIte] at hEq0
      injection hEq0 with _ hb; subst hb; nomatch hPred.1
  | none =>
    dsimp only
    cases hF2 : (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))).find?
        (fun (_, wPk) => wPk == P.pow8 spkPk) with
    | none => intro h; nomatch h
    | some p =>
      rcases p with ⟨sk, wPk⟩; dsimp only; intro _
      have hMemM := List.mem_of_find?_eq_some hF2
      have hPowW := beq_iff_eq.mp (List.find?_some
        (p := fun (x : Bytes × Bytes) => x.2 == P.pow8 spkPk) hF2)
      rcases List.mem_map.mp hMemM with ⟨⟨sk0, pk0⟩, hMemA, hEqA⟩
      injection hEqA with hsk hpk; subst hsk
      have hPk0 := (hKS.1.2.2.2.2.2.2 (sk0, pk0) hMemA).2
      have hPow0 : P.pow8 pk0 = P.pow8 spkPk := hpk.trans hPowW
      exact ⟨by rw [← hPk0, hPow0], Or.inr ⟨(sk0, pk0), hMemA, hPow0⟩⟩
private theorem lookupAuthSpkSkTake_nonEmpty_of_exists {S : Setup} (P : Primitives) (bIdx : ℕ)
    {st : AuthState S} (hKS : ValidAuthKeyStoresFull S P st) (spkPk : Bytes)
    (hEx :
      (∃ kv ∈ st.spkBundles,
        (FgGapDh.spkBundleFlatIdxVal S kv.1 == bIdx) = false ∧ P.pow8 kv.2.spkPk = P.pow8 spkPk) ∨
      (∃ kv ∈ st.advKeys, P.pow8 kv.2 = P.pow8 spkPk)) :
    (!(lookupAuthSpkSkTake S P (eraseSpkBundlesFg S bIdx st.spkBundles)
      (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) spkPk).isEmpty) = true := by
  have hLen : (eraseSpkBundlesFg S bIdx st.spkBundles).length ≤ S.N_dh := by
    unfold eraseSpkBundlesFg; rw [List.length_map]
    exact (validAuthKeyStoresFull_lengths_le S P st hKS).2.1
  unfold lookupAuthSpkSkTake; dsimp only; rw [List.take_of_length_le hLen]
  cases hF1 : (eraseSpkBundlesFg S bIdx st.spkBundles).find?
      (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == P.pow8 spkPk) with
  | some p =>
    rcases p with ⟨idx, b'⟩; dsimp only
    exact (Bool.and_eq_true_iff.mp (List.find?_some
      (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
        !x.2.spkSk.isEmpty && P.pow8 x.2.spkPk == P.pow8 spkPk) hF1)).1
  | none =>
    dsimp only; rcases hEx with ⟨⟨idx0, b0⟩, hMem0, hFlatF, hPow0⟩ | ⟨⟨sk0, pk0⟩, hMemA, hPowA⟩
    · exfalso
      have hMemE : (idx0, b0) ∈ eraseSpkBundlesFg S bIdx st.spkBundles := by
        unfold eraseSpkBundlesFg; refine List.mem_map.mpr ⟨(idx0, b0), hMem0, ?_⟩
        unfold eraseSpkBundleEntryFg; simp [hFlatF]
      have h32 : b0.spkSk.length = 32 := (hKS.1.2.2.2.2.1 (idx0, b0) hMem0).1
      have hNeEmpty : (!b0.spkSk.isEmpty) = true := by
        cases hSk : b0.spkSk with | nil => rw [hSk] at h32; contradiction | cons _ _ => rfl
      exact List.find?_eq_none.mp hF1 (idx0, b0) hMemE
        (Bool.and_eq_true_iff.mpr ⟨hNeEmpty, beq_iff_eq.mpr hPow0⟩)
    · cases hF2 : (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))).find?
          (fun (_, wPk) => wPk == P.pow8 spkPk) with
      | none =>
        exfalso
        exact List.find?_eq_none.mp hF2 (sk0, P.pow8 pk0)
          (List.mem_map.mpr ⟨(sk0, pk0), hMemA, rfl⟩) (beq_iff_eq.mpr hPowA)
      | some p =>
        rcases p with ⟨sk, wPk⟩; dsimp only
        rcases List.mem_map.mp (List.mem_of_find?_eq_some hF2) with ⟨⟨sk1, pk1⟩, hMem1, hEq1⟩
        injection hEq1 with hsk1 _; subst hsk1
        have h32 : sk1.length = 32 := (hKS.1.2.2.2.2.2.2 (sk1, pk1) hMem1).1
        cases hSk : sk1 with | nil => rw [hSk] at h32; contradiction | cons _ _ => rfl
private theorem initAuthDh1Cand_eq_of_guard {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (bIdx : ℕ)
    {st : AuthState S} (hKS : ValidAuthKeyStoresFull S P st)
    (s : AuthInitiatorEntry S) {senderEntry : PrincipalEntry} (hFindSender :
      st.principals.find? (fun (idx, _) => idx == sessionSenderIdx s.sid) =
        some (sessionSenderIdx s.sid, senderEntry))
    (hNonEmpty :
      (!(lookupAuthSpkSkTake S P (eraseSpkBundlesFg S bIdx st.spkBundles)
        (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s.peerSpkPk).isEmpty) = true) :
    initAuthDh1Cand S P st.principals (eraseSpkBundlesFg S bIdx st.spkBundles)
      (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s =
      P.x25519 senderEntry.secIKA0 s.peerSpkPk := by
  have hSenderMem : (sessionSenderIdx s.sid, senderEntry) ∈ st.principals :=
    List.mem_of_find?_eq_some hFindSender
  have hSenderIk := (hKS.1.2.2.2.1 (sessionSenderIdx s.sid, senderEntry) hSenderMem).2
  have hPowSk := (lookupAuthSpkSkTake_nonEmpty_info P bIdx hKS s.peerSpkPk hNonEmpty).1
  unfold initAuthDh1Cand lookupSenderIkPk; rw [hFindSender]; dsimp only
  rw [hSenderIk, hP.toWellFormedPrimitivesδ.x25519_comm _ senderEntry.secIKA0]
  exact hP.x25519_pow8_congr senderEntry.secIKA0 _ s.peerSpkPk
    (hP.x25519Base_len _) (hP.pow8_base_len s.peerSpkPk _ hPowSk.symm) hPowSk
private theorem initAuthDh1Cand_mono_of_traceSub {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (bIdx : ℕ)
    {st1 st2 : AuthState S} (hKS1 : ValidAuthKeyStoresFull S P st1)
    (hKS2 : ValidAuthKeyStoresFull S P st2) (hSub : AuthBaseTraceSub st1 st2)
    (s : AuthInitiatorEntry S) (hGuard :
      initAuthDh1CandGuard S P st1.principals (eraseSpkBundlesFg S bIdx st1.spkBundles)
        (st1.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s = true) :
    initAuthDh1CandGuard S P st2.principals (eraseSpkBundlesFg S bIdx st2.spkBundles)
      (st2.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s = true ∧
    initAuthDh1Cand S P st2.principals (eraseSpkBundlesFg S bIdx st2.spkBundles)
      (st2.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s =
      initAuthDh1Cand S P st1.principals (eraseSpkBundlesFg S bIdx st1.spkBundles)
        (st1.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s := by
  unfold initAuthDh1CandGuard at hGuard
  rcases Bool.and_eq_true_iff.mp hGuard with ⟨hNonEmpty1, hSome1⟩
  cases hFS1 : st1.principals.find? (fun (idx, _) => idx == sessionSenderIdx s.sid) with
  | none => rw [hFS1] at hSome1; nomatch hSome1
  | some p =>
    rcases p with ⟨idx, senderEntry1⟩
    have hMem1 : (idx, senderEntry1) ∈ st1.principals := List.mem_of_find?_eq_some hFS1
    have hIdxEq : idx = sessionSenderIdx s.sid :=
      beq_iff_eq.mp (List.find?_some
        (p := fun (x : Nat × PrincipalEntry) => x.1 == sessionSenderIdx s.sid) hFS1)
    subst hIdxEq; rcases hSub.exists_prin hMem1 with ⟨senderEntry2, hMem2, hSecEq, _⟩
    have hFS2 := find_principals_eq_some_of_mem hKS2.1.1 hMem2
    rcases (lookupAuthSpkSkTake_nonEmpty_info P bIdx hKS1 s.peerSpkPk hNonEmpty1).2 with
      ⟨kv, hKvMem, hFlat, hPow⟩ | ⟨kv, hKvMem, hPow⟩
    · have hNonEmpty2 := lookupAuthSpkSkTake_nonEmpty_of_exists P bIdx hKS2 s.peerSpkPk
        (Or.inl ⟨kv, hSub.spkBundles_sub.subset hKvMem, hFlat, hPow⟩)
      refine ⟨by unfold initAuthDh1CandGuard; rw [hNonEmpty2, hFS2]; rfl, ?_⟩
      rw [initAuthDh1Cand_eq_of_guard P hP bIdx hKS2 s hFS2 hNonEmpty2,
          initAuthDh1Cand_eq_of_guard P hP bIdx hKS1 s hFS1 hNonEmpty1, hSecEq]
    · have hNonEmpty2 := lookupAuthSpkSkTake_nonEmpty_of_exists P bIdx hKS2 s.peerSpkPk
        (Or.inr ⟨kv, hSub.advKeys_sub.subset hKvMem, hPow⟩)
      refine ⟨by unfold initAuthDh1CandGuard; rw [hNonEmpty2, hFS2]; rfl, ?_⟩
      rw [initAuthDh1Cand_eq_of_guard P hP bIdx hKS2 s hFS2 hNonEmpty2,
          initAuthDh1Cand_eq_of_guard P hP bIdx hKS1 s hFS1 hNonEmpty1, hSecEq]
private theorem badAuthFgDh1AtMono_of_traceSub {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen uIdx bIdx : ℕ)
    {st1 st2 : AuthState S} {advRoLog1 advRoLog2 : List Bytes}
    {respRecs1 respRecs2 : List AuthRespRecord}
    (hKS1 : ValidAuthKeyStoresFull S P st1) (hKS2 : ValidAuthKeyStoresFull S P st2)
    (hSub : AuthBaseTraceSub st1 st2)
    (hPrinPres : ∀ uEntry, (uIdx, uEntry) ∈ st1.principals → (uIdx, uEntry) ∈ st2.principals)
    (hRoSub : advRoLog1.Sublist advRoLog2) (hRoLen : advRoLog2.length ≤ maxLen)
    (hRespSub : respRecs1.Sublist respRecs2) (hRespLen : respRecs2.length ≤ S.N_sess_tot)
    (hBad : badAuthFgDh1AtMono P maxLen uIdx bIdx st1 advRoLog1 respRecs1 = true) :
    badAuthFgDh1AtMono P maxLen uIdx bIdx st2 advRoLog2 respRecs2 = true := by
  have hRoLen1 : advRoLog1.length ≤ maxLen := le_trans hRoSub.length_le hRoLen
  have hRespLen1 : respRecs1.length ≤ S.N_sess_tot := le_trans hRespSub.length_le hRespLen
  have hSessLen1 := (validAuthKeyStoresFull_lengths_le S P st1 hKS1).2.2.2
  have hSessLen2 := (validAuthKeyStoresFull_lengths_le S P st2 hKS2).2.2.2
  unfold badAuthFgDh1AtMono at hBad ⊢
  cases hFU1 : st1.principals.find? (fun (u, _) => u == uIdx) with
  | none => rw [hFU1] at hBad; nomatch hBad
  | some up =>
    rcases up with ⟨u0, uEntry⟩
    cases hFB1 : st1.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rw [hFU1, hFB1] at hBad; nomatch hBad
    | some bp =>
      rcases bp with ⟨⟨k0, j0⟩, bEntry⟩
      rw [hFU1, hFB1] at hBad; dsimp only at hBad
      cases beq_iff_eq.mp (List.find?_some
        (p := fun (x : Nat × PrincipalEntry) => x.1 == uIdx) hFU1)
      cases beq_iff_eq.mp (List.find?_some
        (p := fun (x : (Nat × Nat) × SpkBundleEntry) => spkBundleFlatIdxVal S x.1 == bIdx) hFB1)
      have hFU2 := find_principals_eq_some_of_mem hKS2.1.1
        (hPrinPres uEntry (List.mem_of_find?_eq_some hFU1))
      have hFB2 := find_spkBundles_flatIdx_eq_some_of_mem hKS2.1.2.1
        (hSub.spkBundles_sub.subset (List.mem_of_find?_eq_some hFB1))
      rw [hFU2, hFB2]; dsimp only
      rw [List.take_of_length_le hRoLen1, List.take_of_length_le hSessLen1,
          List.take_of_length_le hRespLen1] at hBad
      rw [List.take_of_length_le hRoLen, List.take_of_length_le hSessLen2,
          List.take_of_length_le hRespLen]
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hBad ⊢
      rcases hBad with ⟨hNotCorr, (⟨sec, hSec, hEq⟩ | ⟨s, hs, hG, hEq⟩) | ⟨r, hr, hG, hEq⟩⟩
      · exact ⟨hNotCorr, Or.inl (Or.inl ⟨sec, hRoSub.subset hSec, hEq⟩)⟩
      · rcases initAuthDh1Cand_mono_of_traceSub P hP (spkBundleFlatIdxVal S (k0, j0))
          hKS1 hKS2 hSub s hG with ⟨hG2, hCandEq⟩
        refine ⟨hNotCorr, Or.inl (Or.inr ⟨s, hSub.sessions_sub.subset hs, hG2, ?_⟩)⟩
        rw [beq_iff_eq] at hEq ⊢; rw [hCandEq, hEq]
      · rcases respAuthCand_mono_of_traceSub P (spkBundleFlatIdxVal S (k0, j0))
          hKS1 hKS2 hSub r.bKey r.ikAPk hG with ⟨hG2, hCandEq⟩
        refine ⟨hNotCorr, Or.inr ⟨r, hRespSub.subset hr, hG2, ?_⟩⟩
        rw [beq_iff_eq] at hEq ⊢; unfold respAuthDh1Cand at hEq ⊢; rw [hCandEq, hEq]
private theorem badAuthFgDh3AtMono_of_traceSub {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ)
    {st1 st2 : AuthState S} {advRoLog1 advRoLog2 : List Bytes}
    {respRecs1 respRecs2 : List AuthRespRecord}
    (hKS1 : ValidAuthKeyStoresFull S P st1) (hKS2 : ValidAuthKeyStoresFull S P st2)
    (hSub : AuthBaseTraceSub st1 st2)
    (hRoSub : advRoLog1.Sublist advRoLog2) (hRoLen : advRoLog2.length ≤ maxLen)
    (hRespSub : respRecs1.Sublist respRecs2) (hRespLen : respRecs2.length ≤ S.N_sess_tot)
    (hBad : badAuthFgDh3AtMono P maxLen sIdx bIdx st1 advRoLog1 respRecs1 = true) :
    badAuthFgDh3AtMono P maxLen sIdx bIdx st2 advRoLog2 respRecs2 = true := by
  have hRoLen1 : advRoLog1.length ≤ maxLen := le_trans hRoSub.length_le hRoLen
  have hRespLen1 : respRecs1.length ≤ S.N_sess_tot := le_trans hRespSub.length_le hRespLen
  have hSessLen1 := (validAuthKeyStoresFull_lengths_le S P st1 hKS1).2.2.2
  have hSessLen2 := (validAuthKeyStoresFull_lengths_le S P st2 hKS2).2.2.2
  unfold badAuthFgDh3AtMono at hBad ⊢
  cases hFS1 : st1.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rw [hFS1] at hBad; nomatch hBad
  | some s =>
    cases hFB1 : st1.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rw [hFS1, hFB1] at hBad; nomatch hBad
    | some bp =>
      rcases bp with ⟨⟨k0, j0⟩, bEntry⟩
      rw [hFS1, hFB1] at hBad; dsimp only at hBad
      cases beq_iff_eq.mp (List.find?_some
        (p := fun (x : AuthInitiatorEntry S) => initSessionSlotIdx x.sid == sIdx) hFS1)
      cases beq_iff_eq.mp (List.find?_some
        (p := fun (x : (Nat × Nat) × SpkBundleEntry) => spkBundleFlatIdxVal S x.1 == bIdx) hFB1)
      have hFS2 := find_sessions_slotIdx_eq_some_of_mem hKS2
        (hSub.sessions_sub.subset (List.mem_of_find?_eq_some hFS1))
      have hFB2 := find_spkBundles_flatIdx_eq_some_of_mem hKS2.1.2.1
        (hSub.spkBundles_sub.subset (List.mem_of_find?_eq_some hFB1))
      rw [hFS2, hFB2]; dsimp only
      rw [List.take_of_length_le hRoLen1, List.take_of_length_le hSessLen1,
          List.take_of_length_le hRespLen1] at hBad
      rw [List.take_of_length_le hRoLen, List.take_of_length_le hSessLen2,
          List.take_of_length_le hRespLen]
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hBad ⊢
      rcases hBad with ⟨hPow, (⟨sec, hSec, hEq⟩ | ⟨s', hs', hEq⟩) | ⟨r, hr, hG, hEq⟩⟩
      · exact ⟨hPow, Or.inl (Or.inl ⟨sec, hRoSub.subset hSec, hEq⟩)⟩
      · exact ⟨hPow, Or.inl (Or.inr ⟨s', hSub.sessions_sub.subset hs', hEq⟩)⟩
      · rcases respAuthCand_mono_of_traceSub P (spkBundleFlatIdxVal S (k0, j0))
          hKS1 hKS2 hSub r.bKey r.ekAPk hG with ⟨hG2, hCandEq⟩
        refine ⟨hPow, Or.inr ⟨r, hRespSub.subset hr, hG2, ?_⟩⟩
        rw [beq_iff_eq] at hEq ⊢; unfold respAuthDh3Cand at hEq ⊢; rw [hCandEq, hEq]
private theorem SatisfiesAt.set_bind_c6c4 {St R : Type} (Q : St → Prop) (st st' : St)
    (k : PUnit → StateT St ProbComp R) (hk : SatisfiesAt Q st' (k ())) :
    SatisfiesAt Q st (set st' >>= k) := hk
private theorem SatisfiesAt.ite_c6c4 {St R : Type} (Q : St → Prop) (st : St)
    (c : Prop) [Decidable c] {t e : StateT St ProbComp R}
    (ht : SatisfiesAt Q st t) (he : SatisfiesAt Q st e) :
    SatisfiesAt Q st (if c then t else e) := by split_ifs <;> assumption
private theorem SatisfiesAt.ite_bind1_c6c4 {St A B R : Type} {Q : St → Prop} {st : St}
    {c : Prop} [Decidable c] {d1 : ProbComp A} {g : A → B} {d2 : ProbComp B}
    {f : B → StateT St ProbComp R} (hk : ∀ x, SatisfiesAt Q st (f x)) :
    SatisfiesAt Q st (if c then (do let dk ← liftM d1; let x ← pure (g dk); f x)
                      else (do let x ← liftM d2; f x)) := by
  split_ifs <;> [ (apply SatisfiesAt.liftM_bind; intro dk; exact hk (g dk)) ;
    (apply SatisfiesAt.liftM_bind; intro x; exact hk x) ]
private theorem SatisfiesAt.ite_bind2_c6c4 {St A1 A2 B R : Type} {Q : St → Prop} {st : St}
    {c : Prop} [Decidable c] {d1 : ProbComp A1} {d2 : ProbComp A2} {g : A1 → A2 → B}
    {d3 : ProbComp B} {f : B → StateT St ProbComp R} (hk : ∀ x, SatisfiesAt Q st (f x)) :
    SatisfiesAt Q st (if c then
      (do let r ← liftM d1; let c' ← liftM d2; let x ← pure (g r c'); f x)
      else (do let x ← liftM d3; f x)) := by
  split_ifs
  · apply SatisfiesAt.liftM_bind; intro r; apply SatisfiesAt.liftM_bind; intro c'; exact hk (g r c')
  · apply SatisfiesAt.liftM_bind; intro x; exact hk x
private theorem SatisfiesAt.ite_bind3_c6c4 {St A1 A2 B R : Type} {Q : St → Prop} {st : St}
    {c : Prop} [Decidable c] {d1 : ProbComp A1} {d2 : ProbComp A2} {g : A1 → A2 → B} {v : B}
    {f : B → StateT St ProbComp R} (hk : ∀ x, SatisfiesAt Q st (f x)) :
    SatisfiesAt Q st (if c then
      (do let ms ← liftM d1; let cn ← liftM d2; let x ← pure (g ms cn); f x)
      else (do let x ← pure v; f x)) := by
  split_ifs
  · apply SatisfiesAt.liftM_bind; intro m; apply SatisfiesAt.liftM_bind; intro c; exact hk (g m c)
  · exact hk v
private theorem SatisfiesAt.ite_bind4_c6c4 {St A R : Type} {Q : St → Prop} {st : St}
    {c : Prop} [Decidable c] {d1 : ProbComp A} {v : A}
    {f : A → StateT St ProbComp R} (hk : ∀ x, SatisfiesAt Q st (f x)) :
    SatisfiesAt Q st (if c then (do let x ← liftM d1; f x) else (do let x ← pure v; f x)) := by
  split_ifs
  · apply SatisfiesAt.liftM_bind; intro x; exact hk x
  · exact hk v
private theorem SatisfiesAt.liftAuthBase_c6c4 {S : Setup} (Q : AuthHybridState S → Prop)
    (hst : AuthHybridState S) (m : StateT (AuthState S) ProbComp AuthResponse)
    (h : SatisfiesAt (fun b => Q { hst with base := b }) hst.base m) :
    SatisfiesAt Q hst (liftAuthBase m) := by
  unfold liftAuthBase; apply SatisfiesAt.get_bind; dsimp only; intro y hy
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind, support_bind, Set.mem_iUnion,
    mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩; exact h (resp, base') hp
private def PrinPres {S : Setup} (q : AuthQuery S) (hst s : AuthHybridState S) : Prop :=
  ∀ uIdx uEntry, (uIdx, uEntry) ∈ hst.base.principals →
    (∀ u : Fin S.N_id, q = .corruptIK u → uIdx ≠ u.val) →
    (uIdx, uEntry) ∈ s.base.principals
private theorem runAuthHybridSendKosk_prinPres {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives) (q : AuthQuery S) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridState S) :
    SatisfiesAt (PrinPres q hst) hst
      (runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1) := by
  have h0 : PrinPres q hst hst := fun _ _ h _ => h
  unfold runAuthHybridSendKosk; apply SatisfiesAt.get_bind; dsimp only
  iterate 2 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
  cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some ue =>
    rcases ue with ⟨_, uEntry⟩; dsimp only
    iterate 2 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
    iterate 4 (apply SatisfiesAt.liftM_bind; intro _)
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    cases P.kemEncaps bundle.pqspkB _ with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some ssCt =>
      rcases ssCt with ⟨ss, kemCt⟩; dsimp only
      apply SatisfiesAt.ite_bind1_c6c4; intro ⟨drKey, roCache'⟩
      apply SatisfiesAt.ite_bind2_c6c4; intro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      apply SatisfiesAt.ite_bind3_c6c4; intro ⟨mkSeed, ck1_1⟩
      cases P.spqrInitSend drKey.pqrKey _ with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some spqr =>
        rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
        apply SatisfiesAt.ite_bind4_c6c4; intro deriveMessageKeys; apply SatisfiesAt.set_bind_c6c4
        apply SatisfiesAt.ite_c6c4 <;> exact SatisfiesAt.pure _ _ _ h0
private theorem pqxdhAuthHybridKoskImpl_prinPres {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S) :
    SatisfiesAt (PrinPres q hst) hst (pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q) := by
  have h0 : PrinPres q hst hst := fun _ _ h _ => h
  have h0b : (fun b => PrinPres q hst { hst with base := b }) hst.base := h0
  unfold pqxdhAuthHybridKoskImpl; apply SatisfiesAt.get_bind; dsimp only
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    exact runAuthHybridSendKosk_prinPres stage useRo P _ (.sendOPK u i) u bundle m0 m1 hst
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    exact runAuthHybridSendKosk_prinPres stage useRo P _ (.sendNoOPK u i) u bundle m0 m1 hst
  | recvOPK k j o msg =>
    dsimp only; iterate 3 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
    cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some kp =>
      rcases kp with ⟨_, _⟩; dsimp only
      cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => exact SatisfiesAt.pure _ _ _ h0
        | some op =>
          rcases op with ⟨_, _⟩; dsimp only
          iterate 2 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
          cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => exact SatisfiesAt.pure _ _ _ h0
          | some _ =>
            dsimp only; apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.liftM_bind; intro sO
            cases sO with
            | none => exact SatisfiesAt.pure _ _ _ h0
            | some tup =>
              rcases tup with ⟨_, _, _, _, _, _⟩; dsimp only
              cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
              | none => exact SatisfiesAt.pure _ _ _ h0
              | some sp =>
                rcases sp with ⟨_, _⟩; dsimp only
                apply SatisfiesAt.ite_c6c4 <;> exact SatisfiesAt.pure _ _ _ h0
  | recvNoOPK k j l msg =>
    dsimp only; iterate 3 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
    cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some kp =>
      rcases kp with ⟨_, _⟩; dsimp only
      cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => exact SatisfiesAt.pure _ _ _ h0
        | some _ =>
          dsimp only; apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.liftM_bind; intro sO
          cases sO with
          | none => exact SatisfiesAt.pure _ _ _ h0
          | some tup =>
            rcases tup with ⟨_, _, _, _, _, _⟩; dsimp only
            cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none => exact SatisfiesAt.pure _ _ _ h0
            | some sp =>
              rcases sp with ⟨_, _⟩; dsimp only
              apply SatisfiesAt.ite_c6c4 <;> exact SatisfiesAt.pure _ _ _ h0
  | initPrin u =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl
    apply SatisfiesAt.get_bind; dsimp only; apply SatisfiesAt.ite_c6c4
    · exact SatisfiesAt.pure _ _ _ h0b
    iterate 2 (apply SatisfiesAt.liftM_bind; intro _)
    apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.pure
    intro _ _ hMem _; exact List.mem_cons_of_mem _ hMem
  | corruptIK u =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl
    apply SatisfiesAt.get_bind; dsimp only
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact SatisfiesAt.pure _ _ _ h0b
    | some ue =>
      rcases ue with ⟨_, _⟩; dsimp only; apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.pure
      intro uIdx uEntry hMem hNotCorr; dsimp only
      refine List.mem_map.mpr ⟨(uIdx, uEntry), hMem, ?_⟩
      simp [beq_eq_false_iff_ne.mpr (hNotCorr u rfl)]
  | genSPK u j =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl
    apply SatisfiesAt.get_bind; dsimp only; apply SatisfiesAt.ite_c6c4
    · exact SatisfiesAt.pure _ _ _ h0b
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact SatisfiesAt.pure _ _ _ h0b
    | some ue =>
      rcases ue with ⟨_, _⟩; dsimp only; iterate 2 (apply SatisfiesAt.liftM_bind; intro _)
      apply SatisfiesAt.liftM_bind; intro ⟨_, _⟩; apply SatisfiesAt.liftM_bind; intro _
      apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.pure; exact h0
  | genOPK u j o =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl; apply SatisfiesAt.get_bind
    dsimp only; apply SatisfiesAt.ite_c6c4; · exact SatisfiesAt.pure _ _ _ h0b
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.pure; exact h0
  | registerKey sk =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl; apply SatisfiesAt.get_bind
    dsimp only; cases registerAdvKey P hst.base.advKeys sk with
    | none => exact SatisfiesAt.pure _ _ _ h0b
    | some pa =>
      rcases pa with ⟨_, _⟩; apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.pure; exact h0
  | roQuery _ | roRootQuery _ _ =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl; apply SatisfiesAt.get_bind
    dsimp only; apply SatisfiesAt.ite_c6c4; · exact SatisfiesAt.pure _ _ _ h0b
    apply SatisfiesAt.liftM_bind; intro ⟨_, _⟩
    apply SatisfiesAt.set_bind_c6c4; apply SatisfiesAt.pure; exact h0
  | revealDhSecrets =>
    apply SatisfiesAt.liftAuthBase_c6c4; unfold pqxdhAuthImpl; apply SatisfiesAt.get_bind
    dsimp only; apply SatisfiesAt.ite_c6c4 <;> exact SatisfiesAt.pure _ _ _ h0b
private theorem badAuthFgAnyLatchedMono_step_of_kosk {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (stage : AuthHybridStage) (checkAuth : Bool) (q : AuthQuery S)
    (hst hst' : AuthFgCutoffState S) (h0 h' : AuthHybridState S) (resp : AuthResponse)
    (hBase0 : h0.base = hst.base) (hBase' : h'.base = hst'.base)
    (hKS : ValidAuthKeyStoresFull S P hst.base)
    (hh : (resp, h') ∈ support ((pqxdhAuthHybridKoskImpl stage true checkAuth S P q).run h0))
    (hRoSub : hst.advRoLog.Sublist hst'.advRoLog) (hRoLen : hst'.advRoLog.length ≤ maxRo)
    (hRespSub : hst.respRecs.Sublist hst'.respRecs)
    (hRespLen : hst'.respRecs.length ≤ S.N_sess_tot)
    (hLatchNonCorr : (∀ u, q ≠ .corruptIK u) → hst'.latchedDh1 = hst.latchedDh1)
    (hLatchCorr : ∀ u, q = .corruptIK u →
      hst'.latchedDh1 =
        latchDh1ForPrincipal S P u.val hst.base hst.advRoLog hst.respRecs hst.latchedDh1)
    (hBad : badAuthFgAnyLatchedMono P maxRo hst = true) :
    badAuthFgAnyLatchedMono P maxRo hst' = true := by
  have hKS' : ValidAuthKeyStoresFull S P hst'.base :=
    hBase' ▸ validAuthKeyStoresFull_pqxdhAuthHybridKoskImpl stage true checkAuth P q h0
      (hBase0 ▸ hKS) hh
  have hSub : AuthBaseTraceSub hst.base hst'.base := by
    rw [← hBase0, ← hBase']
    exact (authHybridTraceSub_pqxdhAuthHybridKoskImpl stage true checkAuth P q h0 hh).base_sub
  have hPrin : PrinPres q h0 h' :=
    pqxdhAuthHybridKoskImpl_prinPres stage true checkAuth P q h0 (resp, h') hh
  unfold badAuthFgAnyLatchedMono at hBad ⊢
  rcases Bool.or_eq_true_iff.mp hBad with hDh1 | hDh3
  · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
    rcases List.any_eq_true.mp hDh1 with ⟨uIdx, huRange, hB⟩
    rcases List.any_eq_true.mp hB with ⟨bIdx, hbRange, hAt⟩
    refine List.any_eq_true.mpr ⟨uIdx, huRange, List.any_eq_true.mpr ⟨bIdx, hbRange, ?_⟩⟩
    unfold badAuthFgDh1LatchedAtMono at hAt ⊢
    rcases Bool.or_eq_true_iff.mp hAt with hCont | hMono
    · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
      cases q with
      | corruptIK u =>
        rw [hLatchCorr u rfl]; exact contains_latchDh1ForPrincipal_of_contains P u.val
          hst.base hst.advRoLog hst.respRecs hst.latchedDh1 hCont
      | _ =>
        rw [hLatchNonCorr (by intro u h; nomatch h)]; exact hCont
    · cases q with
      | corruptIK u =>
        by_cases hEq : uIdx = u.val
        · subst hEq
          refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
          rw [hLatchCorr u rfl]
          exact contains_latchDh1ForPrincipal_of_badAuthFgDh1At P maxRo u.val bIdx
            (List.mem_range.mp hbRange) hst.base hst.advRoLog hst.respRecs hst.latchedDh1
            (badAuthFgDh1AtMono_imp_badAuthFgDh1At P maxRo u.val bIdx
              hst.base hst.advRoLog hst.respRecs hMono)
        · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
          refine badAuthFgDh1AtMono_of_traceSub P hP maxRo uIdx bIdx hKS hKS' hSub ?_
            hRoSub hRoLen hRespSub hRespLen hMono
          intro uEntry hMem; rw [← hBase']; exact hPrin uIdx uEntry (hBase0.symm ▸ hMem)
            (fun u' hQ => by injection hQ with hU; subst hU; exact hEq)
      | _ =>
        refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
        refine badAuthFgDh1AtMono_of_traceSub P hP maxRo uIdx bIdx hKS hKS' hSub ?_
          hRoSub hRoLen hRespSub hRespLen hMono
        intro uEntry hMem; rw [← hBase']
        exact hPrin uIdx uEntry (hBase0.symm ▸ hMem) (fun _ hQ => nomatch hQ)
  · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
    rcases List.any_eq_true.mp hDh3 with ⟨sIdx, hsRange, hB⟩
    rcases List.any_eq_true.mp hB with ⟨bIdx, hbRange, hAt⟩
    refine List.any_eq_true.mpr ⟨sIdx, hsRange, List.any_eq_true.mpr ⟨bIdx, hbRange, ?_⟩⟩
    exact badAuthFgDh3AtMono_of_traceSub P maxRo sIdx bIdx hKS hKS' hSub
      hRoSub hRoLen hRespSub hRespLen hAt
theorem badAuthFgAnyLatchedMono_mono_pqxdhAuthAdvLatchedStageImpl
    {S : Setup} (stage : AuthHybridStage) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (q : AuthQuery S) (s3 : AuthAdvLatchedState S)
    (hKS : ValidAuthKeyStoresFull S P s3.hyb.base)
    (hRo : s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecv : s3.adv.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot)
    (hBad : badAuthFgAnyLatchedMono P maxRo s3.toFg = true)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s3)) :
    badAuthFgAnyLatchedMono P maxRo y.2.toFg = true := by
  have hh := mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s3 hy
  have hyAdv := mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s3 y hy
  have hRoLen : y.2.toFg.advRoLog.length ≤ maxRo := by
    change y.2.adv.advRoLog.length ≤ maxRo
    rwa [advRoLog_length_pqxdhAuthAdvLatchedStageImpl stage P q s3 y hy]
  have hRecvLen : y.2.toFg.respRecs.length ≤ S.N_sess_tot := by
    change y.2.adv.respRecs.length ≤ S.N_sess_tot
    rw [respRecs_length_pqxdhAuthAdvLatchedStageImpl stage P q s3 y hy]
    unfold Setup.N_sess_tot; omega
  have hSubLists :
      s3.toFg.advRoLog.Sublist y.2.toFg.advRoLog ∧
      s3.toFg.respRecs.Sublist y.2.toFg.respRecs := by
    change s3.adv.advRoLog.Sublist y.2.adv.advRoLog ∧ s3.adv.respRecs.Sublist y.2.adv.respRecs
    unfold pqxdhAuthAdvStageImpl at hyAdv
    cases q <;> (
      simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hyAdv
      rcases hyAdv with ⟨⟨_, _⟩, _, hEq⟩
      rw [(Prod.mk.inj hEq).2]; exact ⟨by simp, by simp⟩)
  have hLatch :
      ((∀ u, q ≠ .corruptIK u) → y.2.toFg.latchedDh1 = s3.toFg.latchedDh1) ∧
      (∀ u, q = .corruptIK u →
        y.2.toFg.latchedDh1 =
          latchDh1ForPrincipal S P u.val s3.toFg.base s3.toFg.advRoLog
            s3.toFg.respRecs s3.toFg.latchedDh1) := by
    change ((∀ u, q ≠ .corruptIK u) → y.2.latchedDh1 = s3.latchedDh1) ∧
      (∀ u, q = .corruptIK u →
        y.2.latchedDh1 =
          latchDh1ForPrincipal S P u.val s3.adv.hyb.base s3.adv.advRoLog
            s3.adv.respRecs s3.latchedDh1)
    unfold pqxdhAuthAdvLatchedStageImpl at hy
    cases q with
    | corruptIK u =>
      simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hy
      rcases hy with ⟨⟨_, _⟩, _, rfl⟩
      exact ⟨fun h => False.elim (h u rfl), fun u' hQ => by injection hQ with hU; subst hU; rfl⟩
    | _ =>
      simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hy
      rcases hy with ⟨⟨_, _⟩, _, rfl⟩
      exact ⟨fun _ => rfl, fun _ hQ => nomatch hQ⟩
  exact badAuthFgAnyLatchedMono_step_of_kosk P hP maxRo stage true q s3.toFg y.2.toFg
    s3.hyb y.2.hyb y.1 rfl rfl hKS hh hSubLists.1 hRoLen hSubLists.2 hRecvLen
    hLatch.1 hLatch.2 hBad
theorem badAuthFgAnyLatchedMono_mono_advLatched_g3
    {S : Setup} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (q : AuthQuery S) (s3 : AuthAdvLatchedState S) (hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hRo : s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecv : s3.adv.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot)
    (hBad : badAuthFgAnyLatchedMono P maxRo s3.toFg = true)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3)) :
    badAuthFgAnyLatchedMono P maxRo y.2.toFg = true :=
  badAuthFgAnyLatchedMono_mono_pqxdhAuthAdvLatchedStageImpl .g3 P hP maxRo q s3
    hRunInv.1 hRo hRecv hBad y hy
theorem badAuthFgAnyLatchedMono_mono_pqxdhAuthFgLatchedImpl
    {S : Setup} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) (hKS : ValidAuthKeyStoresFull S P hst.base)
    (hRo : hst.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecv : hst.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot)
    (hBad : badAuthFgAnyLatchedMono P maxRo hst = true) (y : AuthResponse × AuthFgCutoffState S)
    (hy : y ∈ support ((pqxdhAuthFgLatchedImpl S P q).run hst)) :
    badAuthFgAnyLatchedMono P maxRo y.2 = true := by
  unfold pqxdhAuthFgLatchedImpl pqxdhAuthFgImpl at hy
  cases q with
  | corruptIK u =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRo hRecv
    simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, h'⟩, hh, rfl⟩
    exact badAuthFgAnyLatchedMono_step_of_kosk P hP maxRo .g3 false (.corruptIK u)
      hst _ (mkG3Hybrid hst.base) h' resp rfl rfl hKS hh
      (List.Sublist.refl _) hRo (List.Sublist.refl _)
      (by dsimp only; unfold Setup.N_sess_tot; omega) (fun h => False.elim (h u rfl))
      (fun u' hQ => by injection hQ with hU; subst hU; rfl) hBad
  | roQuery secrets =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRo hRecv
    simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, h'⟩, hh, rfl⟩
    exact badAuthFgAnyLatchedMono_step_of_kosk P hP maxRo .g3 false (.roQuery secrets)
      hst _ (mkG3Hybrid hst.base) h' resp rfl rfl hKS hh
      (List.sublist_cons_self _ _) (by simpa only [List.length_cons] using hRo)
      (List.Sublist.refl _) (by dsimp only; unfold Setup.N_sess_tot; omega)
      (fun _ => rfl) (fun _ hQ => nomatch hQ) hBad
  | recvOPK k j o msg | recvNoOPK k j o msg =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRo hRecv
    simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, h'⟩, hh, rfl⟩
    exact badAuthFgAnyLatchedMono_step_of_kosk P hP maxRo .g3 false _
      hst _ (mkG3Hybrid hst.base) h' resp rfl rfl hKS hh
      (List.Sublist.refl _) hRo (List.sublist_cons_self _ _)
      (by simp only [List.length_cons, Setup.N_sess_tot]; omega)
      (fun _ => rfl) (fun _ hQ => nomatch hQ) hBad
  | initPrin _ | genSPK _ _ | genOPK _ _ _ | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _
  | roRootQuery _ _ | revealDhSecrets | registerKey _ =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRo hRecv
    simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, h'⟩, hh, rfl⟩
    exact badAuthFgAnyLatchedMono_step_of_kosk P hP maxRo .g3 false _
      hst _ (mkG3Hybrid hst.base) h' resp rfl rfl hKS hh
      (List.Sublist.refl _) hRo (List.Sublist.refl _)
      (by dsimp only; unfold Setup.N_sess_tot; omega)
      (fun _ => rfl) (fun _ hQ => nomatch hQ) hBad
end Proofs.SignalPqxdh.Security
