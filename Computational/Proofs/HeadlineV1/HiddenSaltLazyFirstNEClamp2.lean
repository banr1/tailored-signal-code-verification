/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

namespace CryptoVerification.E2E

section CellClamp2

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)


private abbrev CellState (Pt : Type) (ℓ : ℕ) :=
  Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) ×
    SM.GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)

private abbrev CellEx (Pt : Type) (ℓ : ℕ) :=
  List (SimFig8C Pt) × CellState Pt ℓ

private def cellImplDF (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    QueryImpl
      (unifSpec +
        SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
      (StateT (CellState Pt ℓ) ProbComp) := fun q s => do
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let ((a, mir'), gs') ←
    (simulateQ
      (fullImplBaseDFCellTPaper fig (qep + 1) tL tStar
        SM.Construction.DeliverForge.sameHdrScheme (SM.Config.auth tStar))
      ((DeliverForge.simImplDF'Paper (2 + 1) (qep + 1) q).run s.1)).run s.2
  return (a, (mir', gs'))

omit [SampleableType PQC] in
private theorem cellImplDF_run (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (q : (unifSpec +
      SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)).Domain)
    (mir : Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (gs : SM.GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    (cellImplDF P Dh encPt encT lam qep tL tStar q).run (mir, gs) =
      (do
        let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let ((a, mir'), gs') ←
          (simulateQ
            (fullImplBaseDFCellTPaper fig (qep + 1) tL tStar
              SM.Construction.DeliverForge.sameHdrScheme (SM.Config.auth tStar))
            ((DeliverForge.simImplDF'Paper (2 + 1) (qep + 1) q).run mir)).run gs
        return (a, (mir', gs'))) := rfl

private def runCellDF (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) {α : Type}
    (oa : SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (ms₀ : CellState Pt ℓ) : ProbComp (α × CellState Pt ℓ) :=
  (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar) oa).run ms₀

private def deliverForgeCellSemHook (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    SemHook PQC Pt ℓ unifSpec (CellEx Pt ℓ) where
  sampleBv256 := ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  samplePqc := ($ᵗ PQC : ProbComp PQC)
  onSendCoins _ _ exs := pure (exs, exs)
  onTr Q m rc exs := do
    let ((res, ex'), s') ←
      runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onTr Q m rc exs.1) exs.2
    return (res, (ex', s'))
  onCh Q m₀ m₁ rc exs := do
    let ((res, ex'), s') ←
      runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onCh Q m₀ m₁ rc exs.1) exs.2
    return (res, (ex', s'))
  onDl Q c exs := do
    let ((res, ex'), s') ←
      runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onDl Q c exs.1) exs.2
    return (res, (ex', s'))
  onIj Q c exs := do
    let ((res, ex'), s') ←
      runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onIj Q c exs.1) exs.2
    return (res, (ex', s'))
  onCr Q exs := do
    let ((res, ex'), s') ←
      runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onCr Q exs.1) exs.2
    return (res, (ex', s'))
  onProbe Q c' exs :=
    runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC)).onProbe Q c' exs.1) exs.2
  onDeliverPost _ _ _ exs := pure exs

private theorem deliverForgeCellSemHookClampInv (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    SemHookClampInv B (fun m (exs : CellEx Pt ℓ) => CellGameClampInv B m exs.2.2)
      (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) where
  mono := fun hle h => h.mono hle
  onSendCoins_inv := by
    rintro m Q rq exs h y hy
    change y ∈ support (pure (exs, exs)) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ⟨h, h⟩
  onTr_inv := by
    rintro m Q msg rc ⟨ex, mir, gs⟩ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF,
      SM.Construction.DeliverForge.transmitQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩,
      rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem
    simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold DeliverForge.simTransmitDF'Paper SM.Construction.DeliverForge.transmitQueryDF
      fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, LibsignalSim.stateT_lift_run,
      query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      pure_bind, bind_assoc,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem
    dsimp only at h2
    have hgs : res₂ = res₁ ∧ gs₂ = gs₁ := by
      rcases res₁ with _ | c
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2
        exact ⟨h2.1.1, h2.2⟩
      · rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at h2
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at h2
          exact ⟨h2.1.1, h2.2⟩
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
          exact ⟨h2.1.1, h2.2⟩
    rw [hres, hgs.1, hgs₀, hgs.2]
    exact cellGameClampInv_transmitImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) (cellDelta tL tStar) B m (qep + 1)
      gs gs₁ Q msg none res₁ h hbase
  onCh_inv := by
    rintro m Q m₀ m₁ rc ⟨ex, mir, gs⟩ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF,
      SM.Construction.DeliverForge.challQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩,
      rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem
    simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold DeliverForge.simChallDF'Paper SM.Construction.DeliverForge.transmitQueryDF
      fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      exact ⟨h.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
    · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        exact ⟨h.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          LibsignalSim.stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          bind_assoc, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem
        dsimp only at h2
        have hgs : res₂ = res₁ ∧ gs₂ = gs₁ := by
          rcases res₁ with _ | c
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at h2
            exact ⟨h2.1.1, h2.2⟩
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
            exact ⟨h2.1.1, h2.2⟩
        rw [hres, hgs.1, hgs₀, hgs.2]
        exact cellGameClampInv_transmitImpl P Dh encPt encT lam
          (fun R => if R == Party.A then P.idA else P.idB) (cellDelta tL tStar) B m (qep + 1)
          gs gs₁ Q (if mir.b then m₁ else m₀) none res₁ h hbase
  onDl_inv := by
    rintro m Q c ⟨ex, mir, gs⟩ _ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF,
      SM.Construction.DeliverForge.deliverQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩,
      rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem
    simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold SM.Construction.DeliverForge.simDeliverDF
      SM.Construction.DeliverForge.deliverQueryDF
      fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, LibsignalSim.stateT_lift_run,
      query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      pure_bind, bind_assoc,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem
    dsimp only at h2
    obtain ⟨hfg', hacc⟩ := cellGameClampInv_deliverImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) B m (SM.Config.auth tStar)
      gs gs₁ Q c res₁ h hbase
    have hgs : gs₂ = gs₁ ∧ (∀ t i pm, res₂ = some (SM.RecvResult.accepted t i pm) →
        ∃ pm', res₁ = some (SM.RecvResult.accepted t i pm')) := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2
        exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2
        exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
      · rcases htr : mir.inTransit Q.other c with _ | r <;> simp only [htr] at h2
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at h2
          refine ⟨h2.2, fun t i pm hc => ?_⟩
          rw [h2.1.1] at hc; cases hc; exact ⟨pm', rfl⟩
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
          refine ⟨h2.2, fun t i pm hc => ?_⟩
          rw [h2.1.1] at hc; cases hc; exact ⟨pm', rfl⟩
    rw [hgs₀, hgs.1, hres]
    exact ⟨hfg', fun t i pm hc => by obtain ⟨pm', h1⟩ := hgs.2 t i pm hc; exact hacc t i pm' h1⟩
  onIj_inv := by
    rintro m Q c ⟨ex, mir, gs⟩ _ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF,
      SM.Construction.DeliverForge.injectQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩,
      rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem
    simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold SM.Construction.DeliverForge.simInjectDF
      SM.Construction.DeliverForge.injectQueryDF
      fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, LibsignalSim.stateT_lift_run,
      query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      pure_bind, bind_assoc,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, hres, _, hgs₀⟩ := hmem
    dsimp only at h2
    have hgs : res₂ = res₁ ∧ gs₂ = gs₁ := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2
        exact ⟨h2.1.1, h2.2⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2
        exact ⟨h2.1.1, h2.2⟩
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        exact ⟨h2.1.1, h2.2⟩
    rw [hres, hgs.1, hgs₀, hgs.2]
    exact cellGameClampInv_injectImplCellT P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) B m (qep + 1) tL tStar
      (SM.Config.auth tStar) gs gs₁ Q c res₁ h hbase
  onCr_inv := by
    rintro m Q ⟨ex, mir, gs⟩ h ⟨res, ex', mir', gs'⟩ hy
    dsimp only [deliverForgeCellSemHook, deliverForgeSemHook, runCellDF,
      SM.Construction.DeliverForge.corrQueryDF] at hy
    simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, mir₁, gs₁⟩, ⟨⟨res₂, mir₂, gs₂⟩, hmem, ⟨rfl, rfl, rfl⟩, rfl⟩,
      rfl, rfl, rfl, rfl⟩ := hy
    rw [cellImplDF_run] at hmem
    simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold DeliverForge.simCorrDFPaper SM.Construction.DeliverForge.corrQueryDF
      fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    cases hca : mir.corrAllowedPaper Q <;> simp only [hca] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      exact h.mono (Nat.le_succ m)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, LibsignalSim.stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        bind_assoc, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, _, _, hgs₀⟩ := hmem
      dsimp only at h2
      have hgs : gs₂ = gs₁ := by
        rcases res₁ with _ | st'
        · simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
          exact h2.2
        · simp only [Option.isSome, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
          exact h2.2
      rw [hgs₀, hgs]
      exact cellGameClampInv_corrImplShiftedPaper B m (cellShift tL tStar) gs gs₁ Q res₁ h hbase
  onProbe_inv := by
    rintro m Q c' ⟨ex, mir, gs⟩ h ⟨ex', mir', gs'⟩ hy
    unfold deliverForgeCellSemHook deliverForgeSemHook runCellDF at hy
    rcases hfind : ex.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c')
      with _ | c
    · simp only [hfind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hy
      rcases hy with ⟨rfl, rfl, rfl⟩
      exact h.mono (Nat.le_succ m)
    · simp only [hfind, SM.Construction.DeliverForge.deliverForgeQuery, query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hy
      obtain ⟨⟨res, mir₁, gs₁⟩, hmem, rfl, rfl, rfl⟩ := hy
      rw [cellImplDF_run] at hmem
      simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
        QueryImpl.add_apply_inr] at hmem
      unfold SM.Construction.DeliverForge.simDeliverForgeDF
        SM.Construction.DeliverForge.deliverForgeQuery
        fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
      simp only [StateT.run_bind, StateT.run_get, LibsignalSim.stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inr,
        pure_bind, bind_assoc,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₂⟩, h2, _, _, hgs₀⟩ := hmem
      dsimp only at h2
      have hgs : gs₂ = gs₁ := by
        rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at h2
          exact h2.2
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at h2
          exact h2.2
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
          exact h2.2
      rw [hgs₀, hgs]
      exact cellGameClampInv_deliverForgeBaseImplCellT P Dh encPt encT lam
        (fun R => if R == Party.A then P.idA else P.idB) B m (qep + 1) tL tStar
        (SM.Config.auth tStar) gs gs₁ Q c c' res₁ h hbase
  onDeliverPost_inv := by
    rintro m Q j? rr exs h exs' hy
    change exs' ∈ support (pure exs) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact h

private theorem runCellDF_onTr_none (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (ex ex' : List (SimFig8C Pt)) (s s' : CellState Pt ℓ)
    (hy : ((none, ex'), s') ∈
      support (runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onTr Q m rc ex) s)) :
    ex' = ex ∧ s' = s := by
  rcases s with ⟨mir, gs⟩; rcases s' with ⟨mir', gs'⟩
  dsimp only [deliverForgeSemHook, runCellDF, SM.Construction.DeliverForge.transmitQueryDF] at hy
  simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨⟨res, mir₁, gs₁⟩, hmem, ⟨rfl, rfl⟩, rfl, rfl⟩ := hy
  refine ⟨rfl, ?_⟩
  rw [cellImplDF_run] at hmem
  simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold DeliverForge.simTransmitDF'Paper SM.Construction.DeliverForge.transmitQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, LibsignalSim.stateT_lift_run,
    query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
    pure_bind, bind_assoc,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨⟨res₁, gs₂⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₃⟩, h2, hnone, hmir₀, hgs₀⟩ := hmem
  dsimp only at h2
  rcases res₁ with _ | c
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h2
    rw [hmir₀, h2.1.2, hgs₀, h2.2, transmitImpl_run_none_eq _ _ _ Q m none gs gs₂ hbase]
  · rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at h2
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h2
      rw [h2.1.1] at hnone; cases hnone
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
      rw [h2.1.1] at hnone; cases hnone

private theorem runCellDF_onCh_none (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (ex ex' : List (SimFig8C Pt)) (s s' : CellState Pt ℓ)
    (hy : ((none, ex'), s') ∈
      support (runCellDF P Dh encPt encT lam qep tL tStar
        ((deliverForgeSemHook (PQC := PQC)).onCh Q m₀ m₁ rc ex) s)) :
    ex' = ex ∧ s' = s := by
  rcases s with ⟨mir, gs⟩; rcases s' with ⟨mir', gs'⟩
  dsimp only [deliverForgeSemHook, runCellDF, SM.Construction.DeliverForge.challQueryDF] at hy
  simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨⟨res, mir₁, gs₁⟩, hmem, ⟨rfl, rfl⟩, rfl, rfl⟩ := hy
  refine ⟨rfl, ?_⟩
  rw [cellImplDF_run] at hmem
  simp only [DeliverForge.simImplDF'Paper, DeliverForge.simOraclesDF'Paper,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold DeliverForge.simChallDF'Paper SM.Construction.DeliverForge.transmitQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
  · simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl, rfl⟩; rfl
  · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl, rfl⟩; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, LibsignalSim.stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        bind_assoc, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨res₁, gs₂⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₃⟩, h2, hnone, hmir₀, hgs₀⟩ := hmem
      dsimp only at h2
      rcases res₁ with _ | c
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at h2
        rw [hmir₀, h2.1.2, hgs₀, h2.2,
          transmitImpl_run_none_eq _ _ _ Q (if mir.b then m₁ else m₀) none gs gs₂ hbase]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        rw [h2.1.1] at hnone; cases hnone

private def packCellDF {α : Type}
    (x : (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt))) × CellState Pt ℓ) :
    α × (LibsignalToModularSchemeSimState PQ Pt ℓ × CellEx Pt ℓ) :=
  (x.1.1, (x.1.2.1, (x.1.2.2, x.2)))

private theorem runCellDF_semFwdAnswerHook (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semFwdAnswerHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC))
        qep sC₀ ex₀ Q w isDel ci? Tpk pq' c') s₀ =
    semFwdAnswerHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep sC₀ (ex₀, s₀) Q w isDel ci? Tpk pq' c' := by
  unfold semFwdAnswerHook; dsimp only []
  split_ifs <;>
    simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind]

private theorem runCellDF_semResyncHook (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semResyncHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC))
        qep sC₀ ex₀ Q w ci? Tpk pq' c r) s₀ =
    semResyncHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep sC₀ (ex₀, s₀) Q w ci? Tpk pq' c r := by
  unfold semResyncHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · rfl
  · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind,
      StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨⟨res, ex₁⟩, s₁⟩ => ?_
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;> rfl

private theorem runCellDF_semFwdHook (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semFwdHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC))
        qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c') s₀ =
    semFwdHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep B sC₀ (ex₀, s₀) Q w isDel ci? Tpk pq' honestC c' := by
  unfold semFwdHook
  rcases honestC with _ | c
  · exact runCellDF_semFwdAnswerHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w isDel ci?
      Tpk pq' c'
  · dsimp only []
    split_ifs
    · rcases evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r
      · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, simulateQ_pure,
          StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def,
          bind_assoc, pure_bind]
      · exact runCellDF_semResyncHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w ci?
          Tpk pq' c r
    · exact runCellDF_semFwdAnswerHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w isDel ci?
        Tpk pq' c'

private theorem runCellDF_semFwdEvictHook (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semFwdEvictHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC))
        qep sC₀ ex₀ Q w isDel Tpk pq' c') s₀ =
    semFwdEvictHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep sC₀ (ex₀, s₀) Q w isDel Tpk pq' c' := by
  unfold semFwdEvictHook
  split_ifs
  · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind]
  · exact runCellDF_semFwdAnswerHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q w isDel none
      Tpk pq' c'

private theorem runCellDF_semRecvHook (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semRecvHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := PQC))
        qep B sC₀ ex₀ Q w isDel) s₀ =
    semRecvHook P Dh encPt encT decT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep B sC₀ (ex₀, s₀) Q w isDel := by
  unfold semRecvHook; dsimp only []
  cases href :
    (sC₀.base.stopped || sC₀.base.mir.win ||
      (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome || !(sC₀.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩
    · rfl
    · dsimp only []
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC₀.base.honest)).map fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC₀.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · rfl
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC₀.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact runCellDF_semFwdHook P Dh encPt encT lam qep B tL tStar _ ex₀ s₀ Q w isDel
                    none pk pq' _ _
                · simp only [↓reduceIte]
                  exact runCellDF_semFwdEvictHook P Dh encPt encT lam qep tL tStar _ ex₀ s₀ Q w
                    isDel pk pq' _
            · rfl
          · rfl
        · rfl
      · cases h5 :
          ((sC₀.base.chains Q).getD ci
            { key := none, epoch := 0, last := 0, skipped := [] }).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact runCellDF_semFwdHook P Dh encPt encT lam qep B tL tStar sC₀ ex₀ s₀ Q w isDel
            (some ci) pk pq' _ _
        · rfl
  · rfl

private theorem runCellDF_semCorrHook (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ) (Q : Party) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semCorrHook P Dh encT (deliverForgeSemHook (PQC := PQC)) sC₀ ex₀ Q) s₀ =
    semCorrHook P Dh encT (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      sC₀ (ex₀, s₀) Q := by
  unfold semCorrHook; dsimp only []
  cases href : (sC₀.base.stopped || sC₀.base.mir.win || !sC₀.base.mir.corrAllowed Q ||
    inReceiveOnlyEpoch sC₀.base.mir Q || !noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)
  · simp only [Bool.false_eq_true, ↓reduceIte, deliverForgeCellSemHook, runCellDF, packCellDF,
      simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind]
    refine bind_congr fun ⟨⟨res, ex₁⟩, s₁⟩ => ?_
    rcases res with _ | fig8st <;> rfl
  · rfl

omit [SampleableType PQC] in
private theorem runCellDF_bind (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) {α β : Type}
    (x : SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (f : α → SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) β)
    (s₀ : CellState Pt ℓ) :
    runCellDF P Dh encPt encT lam qep tL tStar (x >>= f) s₀ =
      (runCellDF P Dh encPt encT lam qep tL tStar x s₀ >>= fun ⟨a, s'⟩ =>
        runCellDF P Dh encPt encT lam qep tL tStar (f a) s') := by
  dsimp only [runCellDF]
  rw [simulateQ_bind, StateT.run_bind]

omit [SampleableType PQC] in
private theorem cellImplDF_inl (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (n : unifSpec.Domain) (s : CellState Pt ℓ) :
    cellImplDF P Dh encPt encT lam qep tL tStar (.inl n) s =
      (query (spec := unifSpec) n >>= fun r => pure (r, s)) := by
  rcases s with ⟨mir, gs⟩
  unfold cellImplDF DeliverForge.simImplDF'Paper DeliverForge.simCoinsDF
    fullImplBaseDFCellTPaper
  simp

omit [SampleableType PQC] in
private theorem cellImplDF_liftM_probComp (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) {α : Type}
    (p : ProbComp α) (s₀ : CellState Pt ℓ) :
    (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
      (liftM p : SM.Construction.DeliverForge.AdversaryCompDF
        (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)).run s₀ =
      (p >>= fun a => pure (a, s₀)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
      (query (spec := unifSpec +
        SM.specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) (.inl t) >>=
        fun u => liftM (mx u))).run s₀ =
      ((query (spec := unifSpec) t >>= mx) >>= fun a => pure (a, s₀))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change (cellImplDF P Dh encPt encT lam qep tL tStar (.inl t) s₀ >>=
      fun ⟨u, s₁⟩ => (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
        (liftM (mx u))).run s₁) = _
    rw [cellImplDF_inl]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private theorem runCellDF_semSendHook (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semSendHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC))
        qep sC₀ ex₀ Q m₀ chal r) s₀ =
    semSendHook P Dh encPt encT lam (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep sC₀ (ex₀, s₀) Q m₀ chal r := by
  unfold semSendHook; dsimp only []
  cases h1 : (sC₀.base.stopped || sC₀.base.mir.win || !noBobSendInEpoch0 sC₀.base.mir Q)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · rfl
    · dsimp only []
      cases h2 : (chal.isSome && !s₁.safeCh 3 Q)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hcoins :
            runCellDF P Dh encPt encT lam qep tL tStar
              (semDrawSendCoins (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) r) s₀ =
            (·, s₀) <$>
              semDrawSendCoins
                (deliverForgeCellSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)
                  P Dh encPt encT lam qep tL tStar) r := by
          rcases r with _ | rq <;>
            simp only [semDrawSendCoins, deliverForgeSemHook, deliverForgeCellSemHook, runCellDF,
              simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
              cellImplDF_liftM_probComp, map_eq_bind_pure_comp, Function.comp_def,
              bind_assoc, pure_bind]
        have hstep : ∀ (rq : PQC) (rc : Option (BitVec 256)),
            packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
              ((deliverForgeSemHook (PQC := PQC)).onSendCoins Q rq ex₀ >>= fun ⟨exOk, exFail⟩ =>
                match mkPub (P := P) sC₀.base Q rq
                    (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
                      BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with
                | none => pure (none, sC₀, exFail)
                | some (pq', pub) =>
                  (match chal with
                   | none => (deliverForgeSemHook (PQC := PQC)).onTr Q (pub, m₀) rc exOk
                   | some m₁ =>
                     (deliverForgeSemHook (PQC := PQC)).onCh Q (pub, m₀) (pub, m₁) rc exOk) >>=
                    fun ⟨res, ex₂⟩ =>
                      match res with
                      | none => pure (none, sC₀, exFail)
                      | some c =>
                        let sC' := scPostSendPure P Dh encPt encT lam sC₀ s₁ Q m₀ chal.isSome pq'
                          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
                            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) c
                        pure (some (toWire c), sC', ex₂)) s₀ =
            ((deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar).onSendCoins Q rq
                (ex₀, s₀) >>=
              fun ⟨exOk, exFail⟩ =>
                match mkPub (P := P) sC₀.base Q rq
                    (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
                      BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with
                | none => pure (none, sC₀, exFail)
                | some (pq', pub) =>
                  (match chal with
                   | none => (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar).onTr Q
                       (pub, m₀) rc exOk
                   | some m₁ => (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar).onCh Q
                       (pub, m₀) (pub, m₁) rc exOk) >>=
                    fun ⟨res, ex₂⟩ =>
                      match res with
                      | none => pure (none, sC₀, exFail)
                      | some c =>
                        let sC' := scPostSendPure P Dh encPt encT lam sC₀ s₁ Q m₀ chal.isSome pq'
                          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
                            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) c
                        pure (some (toWire c), sC', ex₂)) := by
          intro rq rc
          change packCellDF <$>
              runCellDF P Dh encPt encT lam qep tL tStar (pure (ex₀, ex₀) >>= _) s₀ =
            (pure ((ex₀, s₀), (ex₀, s₀)) >>= _)
          rw [pure_bind, pure_bind]
          rcases mkPub P sC₀.base Q rq
              (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
                BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩
          · rfl
          · dsimp only []
            rcases chal with _ | m₁
            · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind,
                StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
              refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ex₂⟩, s₂⟩ hmem => ?_
              rcases res with _ | c
              · obtain ⟨_, rfl⟩ := runCellDF_onTr_none P Dh encPt encT lam qep tL tStar Q
                  (pub, m₀) rc ex₀ ex₂ s₀ s₂ hmem
                rfl
              · rfl
            · simp only [deliverForgeCellSemHook, runCellDF, packCellDF, simulateQ_bind,
                StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
              refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ex₂⟩, s₂⟩ hmem => ?_
              rcases res with _ | c
              · obtain ⟨_, rfl⟩ := runCellDF_onCh_none P Dh encPt encT lam qep tL tStar Q
                  (pub, m₀) (pub, m₁) rc ex₀ ex₂ s₀ s₂ hmem
                rfl
              · rfl
        rw [runCellDF_bind, hcoins]
        simp only [map_bind, bind_map_left]
        exact bind_congr fun ⟨rq, rc⟩ => hstep rq rc
      · rfl
  · rfl

private theorem runCellDF_semHandleHook (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : CellState Pt ℓ) :
    packCellDF <$> runCellDF P Dh encPt encT lam qep tL tStar
      (semHandleHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := PQC))
        qep B t sC₀ ex₀) s₀ =
    semHandleHook P Dh encPt encT decT lam
      (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar)
      qep B t sC₀ (ex₀, s₀) := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact runCellDF_semSendHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q m₀ none r
  · exact runCellDF_semSendHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q m₀ (some m₁) r
  · unfold semHandleHook
    have hpost₁ : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDeliverPost =
        fun _ _ _ ex => pure ex := rfl
    have hpost₂ :
        (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar
          (PQC := PQC) (ℓ := ℓ)).onDeliverPost =
        fun _ _ _ ex => pure ex := rfl
    rw [hpost₁, hpost₂]
    simp only [pure_bind, Prod.mk.eta, bind_pure]
    exact runCellDF_semRecvHook P Dh encPt encT decT lam qep B tL tStar sC₀ ex₀ s₀ Q w true
  · exact runCellDF_semRecvHook P Dh encPt encT decT lam qep B tL tStar sC₀ ex₀ s₀ Q w false
  · exact runCellDF_semCorrHook P Dh encPt encT lam qep tL tStar sC₀ ex₀ s₀ Q

private theorem runCellDF_simDeliverForgeOracle_inl (qep B : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (n : unifSpec.Domain) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (s : CellState Pt ℓ) :
    runCellDF P Dh encPt encT lam qep tL tStar
      ((simDeliverForgeOracle P Dh encPt encT decT lam qep B (.inl n)).run (sC, ex)) s =
    (query (spec := unifSpec) n >>= fun r => pure ((r, (sC, ex)), s)) := by
  change (cellImplDF P Dh encPt encT lam qep tL tStar (.inl n) s >>=
    fun ⟨r, s₁⟩ => pure ((r, (sC, ex)), s₁)) = _
  rw [cellImplDF_inl]
  simp only [bind_assoc, pure_bind]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runDFM_bind {α β : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ) α)
    (f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ) β)
    (s₁ : LibsignalToModularSchemeSimState PQ Pt ℓ) (s₂ : List (SimFig8C Pt)) :
    runDFM (m >>= f) s₁ s₂ =
      (runDFM m s₁ s₂ >>= fun ⟨a, s₁', s₂'⟩ => runDFM (f a) s₁' s₂') := by
  simp only [runDFM, StateT.run_bind, bind_assoc, pure_bind]

private theorem simulateQ_runCellDF_simDeliverForgeOracle_eq (qep B : ℕ) (tL : Option ℕ)
    (tStar : ℕ) (h232 : 2 ^ 32 ≤ B) {α : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) α)
    (m : ℕ)
    (hm : oa.IsQueryBoundP
      (isGameQuery (G := SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (s : CellState Pt ℓ)
    (hInv : SimBaseClampInv B m sC.base ∧ CellGameClampInv B m s.2) :
    runCellDF P Dh encPt encT lam qep tL tStar
        ((simulateQ (simDeliverForgeOracle P Dh encPt encT decT lam qep B) oa).run (sC, ex)) s =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runCellDF P Dh encPt encT lam qep tL tStar
        (runDFM (simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
          (fig := fig) (fs := fs)
          (H := CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeHook Pt ℓ)
          Dh) oa) sC ex) s := by
  dsimp only []
  induction oa using OracleComp.inductionOn generalizing m sC ex s with
  | pure a => rfl
  | query_bind qy u ih =>
    rw [isQueryBoundP_query_bind_iff] at hm
    rcases hm with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, runDFM_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      liftM, monadLift, MonadLift.monadLift]
    rcases qy with n | t
    · simp only [isGameQuery, ↓reduceIte] at hu
      have hinl := simDeliverForgeOracle_inl_eq P Dh encPt encT decT lam qep B n sC ex
      dsimp only [] at hinl
      simp only [runCellDF, simulateQ_bind, StateT.run_bind]
      rw [← hinl]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, sC', ex'⟩, s'⟩ hmem => ?_
      change ((r, (sC', ex')), s') ∈ support
        (runCellDF P Dh encPt encT lam qep tL tStar
          ((simDeliverForgeOracle P Dh encPt encT decT lam qep B (.inl n)).run (sC, ex)) s) at hmem
      rw [runCellDF_simDeliverForgeOracle_inl] at hmem
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, ⟨_, rfl, rfl⟩, rfl⟩ := hmem
      exact ih r m (hu r) _ _ _ hInv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hu
      have hm_pos : 0 < m := hq0.resolve_left (by decide)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hStep := semHandleHook_deliverForge_eq P Dh encPt encT decT lam qep B t sC ex
        (by omega) (fun Q => by have := hInv.1.hep Q; omega)
        (fun Q g hg => by have := hInv.1.hch Q g hg; omega)
        (fun _ => Or.inl h232)
      dsimp only [] at hStep
      simp only [runCellDF, simulateQ_bind, StateT.run_bind]
      change ((simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
          (semHandleHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := PQC))
            qep B t sC ex)).run s >>= _) = _
      rw [← hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, sC', ex'⟩, s'⟩ hmem => ?_
      have hmem' : (r, (sC', (ex', s'))) ∈
          support (semHandleHook P Dh encPt encT decT lam
            (deliverForgeCellSemHook P Dh encPt encT lam qep tL tStar) qep B t sC (ex, s)) := by
        rw [← runCellDF_semHandleHook, support_map]
        exact ⟨((r, (sC', ex')), s'), hmem, rfl⟩
      have hInv' := semHandleHook_preserves_clampInv P Dh encPt encT decT lam
        (deliverForgeCellSemHookClampInv P Dh encPt encT lam qep B tL tStar)
        m' qep h232 t sC (ex, s) hInv.1 hInv.2 (r, (sC', (ex', s'))) hmem'
      exact ih r m' (by simpa using hu r) sC' ex' s' hInv'

omit [SampleableType PQC] in
private theorem simulateQ_fullImplBaseDFCellTPaper_simImplDF'Paper_eq_runCellDF
    (qep : ℕ) (tL : Option ℕ) (tStar : ℕ) {α : Type}
    (oa : SM.Construction.DeliverForge.AdversaryCompDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (mir : Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (gs : SM.GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (simulateQ
      (fullImplBaseDFCellTPaper fig (qep + 1) tL tStar
        SM.Construction.DeliverForge.sameHdrScheme (SM.Config.auth tStar))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1)) oa).run mir)).run gs =
    (runCellDF P Dh encPt encT lam qep tL tStar oa (mir, gs) >>=
      fun ⟨a, mir', gs'⟩ => pure ((a, mir'), gs')) := by
  dsimp only [runCellDF]
  induction oa using OracleComp.inductionOn generalizing mir gs with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind q u ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      liftM, monadLift, MonadLift.monadLift]
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, cellImplDF_run]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun ⟨⟨a, mir'⟩, gs'⟩ => ih a mir' gs'

omit [SampleableType PQC] in
private theorem runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF
    (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (oa : SM.Construction.DeliverForge.AdversaryDF
      (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL tStar
      SM.Construction.DeliverForge.sameHdrScheme (SM.Config.auth tStar) false
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) oa) =
    (do
      let k ← ($ᵗ (Ratchet.RootKey × BitVec 256) : ProbComp (Ratchet.RootKey × BitVec 256))
      let b ← ($ᵗ Bool : ProbComp Bool)
      let mir₀ : Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) := { st := fun _ => (), b := b }
      let gs₀ := SM.initState fig k false
      let (u, _, gs') ← runCellDF P Dh encPt encT lam qep tL tStar oa (mir₀, gs₀)
      return (u, gs')) := by
  dsimp only [runBaseDFCellTPaper, DeliverForge.challSimDF'Paper]
  refine bind_congr fun k => ?_
  rw [simulateQ_bind]
  change (StateT.lift ($ᵗ Bool : ProbComp Bool) >>= fun b =>
    simulateQ _ ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1)) oa).run'
      { st := fun _ => (), b := b })).run _ = _
  simp only [StateT.run_bind, LibsignalSim.stateT_lift_run, StateT.run'_eq,
    map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure,
    StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [simulateQ_fullImplBaseDFCellTPaper_simImplDF'Paper_eq_runCellDF]
  simp only [bind_assoc, pure_bind]

private theorem runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClamp_eq
    (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL t
        SM.Construction.DeliverForge.sameHdrScheme (SM.Config.auth t) false
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep (2 ^ 32) A)) =
      runBaseDFCellTPaper fig (qep + 1) tL t
        SM.Construction.DeliverForge.sameHdrScheme (SM.Config.auth t) false
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) := by
  subst hid
  dsimp only []
  have hqB : q + 3 ≤ 2 ^ 32 := by omega
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  rw [runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF,
    runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  rw [simDeliverForge_eq_bind_runDFM P Dh encPt encT decT lam qep _ rfl A]
  unfold simDeliverForgeClamp
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def,
    runCellDF_bind, bind_assoc]
  simp only [runCellDF, cellImplDF_liftM_probComp, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
  let mir₀ : Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) := { st := fun _ => (), b := b }
  let gs₀ := SM.initState fig k false
  let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  have hSim := simulateQ_runCellDF_simDeliverForgeOracle_eq P Dh encPt encT decT lam
    qep (2 ^ 32) tL t (Nat.le_refl _) A q hq' sC₀ [] (mir₀, gs₀)
    ⟨simBaseClampInv_init (2 ^ 32) q _ _ hqB,
     cellGameClampInv_init P Dh encPt encT lam idOf0 (2 ^ 32) q k false hqB⟩
  unfold runCellDF at hSim
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rw [hSim]

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClamp_eq
    (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (q : ℕ) (hq : SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        SM.Construction.DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep (2 ^ 32) A)) =
      DeliverForge.forgeGuessedAdvantageCellPaper fig (qep + 1)
        SM.Construction.DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) := by
  dsimp only []
  rw [forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper,
    runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClamp_eq
      P Dh encPt encT decT lam qep tL t idOf hid A q hq hq32,
    ← forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper]

end CellClamp2

end CryptoVerification.E2E
