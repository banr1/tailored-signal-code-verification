/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedPrefixStage2
import Computational.Proofs.CryptoGames.FSAEAD.CellForgery
import Computational.Proofs.GameHop.GlobalHybrid
import Computational.Proofs.GameHop.StateSim
import VCVio.EvalDist.Monad.Basic

/-!
# Parametric Session-Tracked Prefix Telescope and Query Bounds

**Checked by Lean.** Proves the Stage-2 SM query bound, Stage-2 `simulateQ`/`eval2` commutation,
and `qStart`-step prefix-hybrid telescope for `bhPrefixRedWithSessionTracked` over an arbitrary
`SessionHaltTracker`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedPrefix

open MeasureTheory (Measure)
open Computational.Proofs.GameHop.GlobalHybrid (slotStepOut slotStepWRed slotStepY0 slotStepY1
  slotStep_bool_le_false slotStep_bool_le_true)
open Computational.Proofs.GameHop.StateSim (isQueryBoundP_congr_pred)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoGames.SM (Adversary ConfigR GameState MakesAtMostQueries initState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open ReductionDsl (Mid isGameQuery)
open CryptoVerification.E2E.Signed (evalDist_bind_apply_eq_add evalDist_bind_apply_lintegral)
open CryptoVerification.E2E (BHE2EDrvState BHPrefixCtx BHTargetQuery BHTargetResp
  BhShallowTwoStageRed Bytes SampledSessionKey allTestedSessionsFresh bhDrvKiQueryOk
  bhE2EDrvWon bhE2EMirror bhFwdU bhLiftP bhNoOpkRespPromoted bhShallowCheckExtSm bhShallowFinishPrefix
  bhShallowImplOfHandle bhShallowRunFuel bhShallowRunFuel_query_inl
  bhShallowRunFuel_query_inr_succ bhTargetGameSpec bhTargetQenc bhTargetRdec
  boolDist_le_iSup_flip_of_beq_not_le configRefuseEarlyBobCorr
  evalDist_bind_congr_prob_of_support evalDist_bind_fst_or_not_fst evalDist_bind_mono_of_imp
  evalDist_bind_mono_prob evalDist_bind_mono_prob_of_support paramsIdsWithSpqr
  prob_bind_congr_of_support sessionSchemeFixedSpk stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker bhClassifyTarget
  bhClassifyTargetOnly bhComposedPostObs bhComposedPostObsSessionTracked
  bhE2EDrvImplGenWithSessionTracked bhE2EExpWithKiSessionTracked bhE2ELocalStartSessionTracked
  bhMkKeyBitConst bhPrefixExactFullExpWithSessionTracked bhPrefixHandlePostWithSessionTracked
  bhPrefixHybExpWithSessionTracked bhPrefixLazyFullExpWithSessionTracked
  bhPrefixRedWithSessionTracked bhShallowStepPostLocalSessionTracked gameRSessionTracked
  oracleImplRSessionTracked runRSessionTracked stateT_run_lift stateT_run_liftM)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixEndpoints (
  bhE2ELocalStartGenWithSessionTracked_const_eq bhPrefixExactFullExpWithSessionTracked_false_eq
  bhPrefixExactFullExpWithSessionTracked_true_eq
  boolBias_bhE2EExpWithKiSessionTracked_false_eq_boolDist_prefixHyb_endpoints)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixFactor (ExtState bhPlugExt
  bhPlugExtSessionTracked bhPrefixExtExpWithSessionTracked bhPrefixExtPairExpWithSessionTracked
  bhPrefixLazyFullExpWithSessionTracked_eq_bind_bhPrefixExtExpWithSessionTracked
  bhPrefixPlugContWithSessionTracked simulateQ_bhE2EDrvImplGenWithSessionTracked_with_b)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixStage2 (BHMidEval1PropsSessionTracked
  BHPrefixPlugInv BHPrefixPlugInvSessionTracked bhE2EDrvWon_bhPlugExt
  bhE2ELocalStartSessionTracked_false_bhPlugExtSessionTracked bhE2EMirror_bhPlugExt
  bhPrefixHandlePostWithSessionTracked_plugExt_sm_bind_eq bhPrefixPlugInvSessionTracked_with_b
  bhPrefixPlugInv_bhE2EMirror implExtSessionTracked
  mem_support_bhStage1ToProb_eval1_withSessionTracked_props
  simulateQ_implExtSessionTracked_bhFwdU_run simulateQ_implExtSessionTracked_bhLiftP_run)

attribute [local irreducible] spqrV1SessionUniformCoins

/-! ## Stage-2 SM query bounds -/

/-- Predicate selecting SM oracle queries inside `unifSpec + SM.spec`. -/
abbrev isSmTargetQuery (ℓ : ℕ) :
    (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidablePredIsSmTargetQuery (ℓ : ℕ) : DecidablePred (isSmTargetQuery ℓ)
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

private theorem bhShallowRunFuel_queryBound_of_step_le
    {ι κ Q R St : Type} {T : OracleSpec ι} {G : OracleSpec κ}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    {p : κ → Bool} {P_tgt : (unifSpec + T).Domain → Prop} [DecidablePred P_tgt]
    (hU : ∀ n, (bhFwdU (G := T) n).IsQueryBoundP P_tgt 0)
    (hstep : ∀ t s, (h s (qenc t)).IsQueryBoundP P_tgt (if p t then 1 else 0))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP
        (fun x => (match x with | .inl _ => false | .inr t => p t) = true) q →
      ∀ (fuel : ℕ) (s : St),
        (bhShallowRunFuel qenc rdec h dflt oa fuel s).IsQueryBoundP P_tgt q := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel s; simp [bhShallowRunFuel]
  | query_bind t mx ih =>
    intro q hq fuel s
    rw [isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl n =>
      simpa [bhShallowRunFuel] using isQueryBoundP_bind (hU n)
        (fun u _ => ih u (q := q) ((hq.2 u).mono (by simp)) fuel s)
    | inr g =>
      cases fuel with
      | zero => simp [bhShallowRunFuel]
      | succ f =>
        simp only [bhShallowRunFuel_query_inr_succ]
        by_cases hpg : p g = true
        · have hpos : 0 < q := hq.1.resolve_left (by simp [hpg])
          have hh : (h s (qenc g)).IsQueryBoundP P_tgt 1 := by
            simpa [hpg] using hstep g s
          exact (isQueryBoundP_bind hh
            (fun res _ => ih (rdec g res.1) (q := q - 1)
              ((hq.2 _).mono (by simp [hpg])) f res.2)).mono
            (by omega)
        · have hh : (h s (qenc g)).IsQueryBoundP P_tgt 0 := by
            simpa [hpg] using hstep g s
          exact (isQueryBoundP_bind hh
            (fun res _ => ih (rdec g res.1) (q := q)
              ((hq.2 _).mono (by simp [hpg])) f res.2)).mono
            (by omega)

private theorem isQueryBoundP_paused_of_mem_support_simulateQ_shallow_run1
    {ι κ Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {T : OracleSpec ι} {G : OracleSpec κ}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    {P_src : (unifSpec + G).Domain → Prop} [DecidablePred P_src]
    (impl : QueryImpl (unifSpec + T) ProbComp)
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP P_src q →
      ∀ (fuel : ℕ) (s : σ) (t : κ) (c : ch) (p : π)
        (s' : σ) (cont : G t → OracleComp (unifSpec + G) α),
        Mid.paused t c p s' cont ∈ support (simulateQ impl (Red.run1 dflt oa fuel s)) →
        ∀ v, (cont v).IsQueryBoundP P_src q := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel s t c p s' cont hmem
    simp [BhShallowTwoStageRed.run1_pure, simulateQ_pure] at hmem
  | query_bind q_oa mx ih =>
    intro q hq fuel s t c p s' cont hmem
    rw [isQueryBoundP_query_bind_iff] at hq
    have hmx : ∀ u, (mx u).IsQueryBoundP P_src q := fun u =>
      (hq.2 u).mono (by split_ifs <;> omega)
    cases q_oa with
    | inl n =>
      simp only [BhShallowTwoStageRed.run1_query_inl, simulateQ_bind, support_bind,
        Set.mem_iUnion] at hmem
      rcases hmem with ⟨u, _, hmem⟩
      exact ih u (hmx u) fuel s t c p s' cont hmem
    | inr g =>
      cases fuel with
      | zero =>
        simp [BhShallowTwoStageRed.run1, construct_query_bind, simulateQ_pure] at hmem
      | succ f =>
        simp only [BhShallowTwoStageRed.run1_query_inr_succ, simulateQ_bind, support_bind,
          Set.mem_iUnion] at hmem
        rcases hmem with ⟨res, _, hmem⟩
        rcases res with ⟨v, s₁⟩ | ⟨c₁, p₁, s₁⟩
        · exact ih (Red.rdec g v) (hmx _) f s₁ t c p s' cont hmem
        · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Mid.paused.injEq] at hmem
          rcases hmem with ⟨rfl, _, _, _, hcont⟩
          cases hcont
          exact hmx

private theorem isQueryBoundP_paused_of_mem_support_simulateQ_shallow_eval1
    {ι κ Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {T : OracleSpec ι} {G : OracleSpec κ}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    {P_src : (unifSpec + G).Domain → Prop} [DecidablePred P_src]
    (impl : QueryImpl (unifSpec + T) ProbComp)
    (A : aIn → OracleComp (unifSpec + G) aOut)
    (x : rIn) (fuel : ℕ) (dflt : aOut) (q : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP P_src q)
    (c0 : ch) (t : κ) (c : ch) (p : π)
    (s' : σ) (cont : G t → OracleComp (unifSpec + G) aOut)
    (hmem : (c0, Mid.paused t c p s' cont) ∈ support (simulateQ impl (Red.eval1 A x fuel dflt))) :
    ∀ v, (cont v).IsQueryBoundP P_src q := by
  unfold BhShallowTwoStageRed.eval1 at hmem
  simp only [simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
  rcases hmem with ⟨⟨a, s⟩, _, m, hm, hfin⟩
  cases m with
  | done b s₁ =>
    simp only [simulateQ_bind, simulateQ_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false] at hfin
    rcases hfin with ⟨_, _, hfalse⟩
    exact False.elim hfalse
  | paused t₁ c₁ p₁ s₁ cont₁ =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
    rcases hfin with ⟨_, hmid⟩
    rw [← hmid] at hm
    exact isQueryBoundP_paused_of_mem_support_simulateQ_shallow_run1 Red impl dflt (hA a)
      fuel s t c p s' cont hm

private theorem isQueryBoundP_bhFwdU_sm {ℓ : ℕ} (n : ℕ) :
    (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      n).IsQueryBoundP (isSmTargetQuery ℓ) 0 :=
  (isQueryBoundP_query_iff
    (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (isSmTargetQuery ℓ) (Sum.inl n) 0).2 (by simp [isSmTargetQuery])

private theorem isQueryBoundP_bhLiftP_sm {ℓ : ℕ} {α : Type} (p : ProbComp α) :
    (bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      p).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
  unfold bhLiftP
  induction p using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n mx ih =>
    rw [simulateQ_query_bind]
    exact (isQueryBoundP_bind (isQueryBoundP_bhFwdU_sm n) (fun u _ => ih u)).mono (by omega)

theorem isQueryBoundP_bhPrefixHandlePostWithSessionTracked_eval {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (s : BHE2EDrvState S ℓ × List τ) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k s
      (bhTargetQenc t)).IsQueryBoundP (isSmTargetQuery ℓ)
      (if bhClassifyTargetOnly (fun _ => false) (fun _ => false) (fun i => i == k) t then 1
       else 0) := by
  rcases t with (kq | ⟨sid⟩) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc,
      bhPrefixHandlePostWithSessionTracked]
    exact isQueryBoundP_bhLiftP_sm _
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc,
      bhPrefixHandlePostWithSessionTracked]
    exact isQueryBoundP_bhLiftP_sm _
  · simp only [bhClassifyTargetOnly, bhTargetQenc, bhPrefixHandlePostWithSessionTracked]
    by_cases hp : (i == k) = true
    · simp only [hp, ↓reduceIte]
      cases bhShallowCheckExtSm k s.1 i sq with
      | inl _ => exact (isQueryBoundP_bhLiftP_sm _).mono (Nat.zero_le 1)
      | inr sq' =>
        dsimp only
        have hq1 :
            (liftM
              ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512)
                Bytes).query (.inr sq')) :
              OracleComp
                (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                _).IsQueryBoundP (isSmTargetQuery ℓ) 1 :=
          (isQueryBoundP_query_iff (isSmTargetQuery ℓ) (Sum.inr sq') 1).2 (fun _ => Nat.zero_lt_one)
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind hq1 (fun _ _ => isQueryBoundP_pure (isSmTargetQuery ℓ) _ 0)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hne : (i != k) = true := by
        rw [bne_iff_ne]
        exact beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hp)
      have hcheck : bhShallowCheckExtSm k s.1 i sq = .inl (.inr (none, none, none)) := by
        simp [bhShallowCheckExtSm, hne]
      rw [hcheck]
      exact isQueryBoundP_bhLiftP_sm _

/-- Stage-2 SM query bound for `bhPrefixRedWithSessionTracked` on an arbitrary target adversary `B_A`. -/
theorem bhPrefixRedWithSessionTracked_makesAtMostQueries_of_B {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (k q_k : ℕ)
    (hB : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      q_k)
    (qTot : ℕ)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx)
    (ho : o ∈ support (stageOneAsProbComp
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B_A) () qTot
        false)))
    (flip : Bool) :
    MakesAtMostQueries
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false)
      q_k := by
  have hfin : ∀ (s_out : BHE2EDrvState S ℓ × List τ) (b_out : Bool),
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).finish s_out b_out
        flip).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    intro s_out b_out
    dsimp only [bhPrefixRedWithSessionTracked]
    exact isQueryBoundP_bhLiftP_sm _
  unfold MakesAtMostQueries
  refine isQueryBoundP_congr_pred (p := isSmTargetQuery ℓ) (by rintro (_ | _) <;> simp [isSmTargetQuery]) ?_
  rcases o with ⟨c0, m⟩
  dsimp only
  cases m with
  | done b_out s_out =>
    simp only [BhShallowTwoStageRed.eval2, pure_bind]
    exact (hfin s_out b_out).mono (Nat.zero_le _)
  | paused t c p s_p cont =>
    have hcont : ∀ v,
        (cont v).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
          q_k :=
      isQueryBoundP_paused_of_mem_support_simulateQ_shallow_eval1
        (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k)
        _ (fun _ => B_A) () qTot false q_k (fun _ => hB)
        c0 t c p s_p cont ho
    have hres :
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).resume s_p p flip).IsQueryBoundP
          (isSmTargetQuery ℓ) 0 := by
      dsimp only [bhPrefixRedWithSessionTracked]
      exact isQueryBoundP_pure (isSmTargetQuery ℓ) _ 0
    simp only [BhShallowTwoStageRed.eval2]
    exact (isQueryBoundP_bind hres
      (fun ⟨v, s₁⟩ _ =>
        isQueryBoundP_bind
          (bhShallowRunFuel_queryBound_of_step_le
            bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)
            isQueryBoundP_bhFwdU_sm
            (fun t' s' => isQueryBoundP_bhPrefixHandlePostWithSessionTracked_eval T P ki C K qep
              decT encT k s' t')
            false
            (q := q_k)
            (isQueryBoundP_congr_pred (by rintro (_ | _) <;> simp [isSmTargetQuery])
              (hcont (bhTargetRdec t v)))
            qTot s₁)
          (fun ⟨b_out, s_out⟩ _ => hfin s_out b_out))).mono (by omega)

/-! ## Stage-2 `simulateQ` and `eval2` commutation -/

@[local simp]
theorem bhComposedPostObs_with_b {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives)
    (b' : Bool) (σ : BHE2EDrvState S ℓ) (b0 : Bool) :
    bhComposedPostObs P (b', { σ with b := b0 }) = bhComposedPostObs P (b', σ) := rfl

@[local simp]
theorem bhComposedPostObsSessionTracked_with_b {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (b' : Bool) (σH : BHE2EDrvState S ℓ × List τ) (b0 : Bool) :
    bhComposedPostObsSessionTracked P (b', ({ σH.1 with b := b0 }, σH.2)) =
      bhComposedPostObsSessionTracked P (b', σH) := rfl

set_option maxHeartbeats 800000 in
theorem bhPrefixHandlePostWithSessionTracked_plugExt_step_bind_eq {τ α : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH)
    (k1 : (((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q ×
        (BHE2EDrvState S ℓ × List τ)) × ExtState ℓ) × τ → ProbComp α)
    (k2 : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q ×
        (BHE2EDrvState S ℓ × List τ) → ProbComp α)
    (hk : ∀ r σH' gs_ext' tr_ext', BHPrefixPlugInvSessionTracked k idA idB s σH' →
      gs_ext'.b = gs_ext.b →
      k1 (((r, σH'), gs_ext'), tr_ext') =
        k2 (r, bhPlugExtSessionTracked k gs_ext' tr_ext' σH')) :
    (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT idA idB s)
        ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k) q).run σH)).run
          gs_ext).run tr_ext >>= k1) =
    ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false) q).run
        (bhPlugExtSessionTracked k gs_ext tr_ext σH) >>= k2) := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
          idA idB s)
        (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n >>=
          fun u => pure (u, σH))).run gs_ext).run tr_ext >>= k1) =
      (((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, bhPlugExtSessionTracked k gs_ext tr_ext σH)) >>= k2)
    rw [simulateQ_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_implExtSessionTracked_bhFwdU_run]
    simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    exact bind_congr fun u => hk u σH gs_ext tr_ext h rfl
  · let isRef (kq' : SignalPqxdh.KeyIndQuery S) : Bool :=
      match kq' with | .corruptIK u => bhNoOpkRespPromoted σH.1.instMeta u | _ => false
    have hL :
        ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
            idA idB s)
          ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)
            (.inr (.inl (.inl kq)))).run σH)).run gs_ext).run tr_ext =
        (if !bhDrvKiQueryOk P σH.1.toModelDriverBase kq then
          pure (((.noneResp, σH), gs_ext), tr_ext)
        else if isRef kq then
          pure (((.noneResp, σH), gs_ext), tr_ext)
        else
          (ki kq).run σH.1.st >>= fun (kr, st') =>
            pure (((kr, (bhE2EMirror { σH.1 with st := st' } kq kr, σH.2)), gs_ext), tr_ext)) := by
      simp only [bhShallowImplOfHandle, bhPrefixHandlePostWithSessionTracked, bhTargetQenc,
        bhTargetRdec, bhShallowStepPostLocalSessionTracked, StateT.run_mk, simulateQ_bind,
        StateT.run_bind, simulateQ_implExtSessionTracked_bhLiftP_run, simulateQ_pure,
        StateT.run_pure, bind_assoc, pure_bind, isRef]
      cases kq <;> (dsimp only; split_ifs <;> simp only [bhTargetRdec, bind_assoc, pure_bind])
    have hR :
        (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false)
          (.inr (.inl (.inl kq)))).run (bhPlugExtSessionTracked k gs_ext tr_ext σH) =
        (if !bhDrvKiQueryOk P σH.1.toModelDriverBase kq then
          pure (.noneResp, bhPlugExtSessionTracked k gs_ext tr_ext σH)
        else if isRef kq then
          pure (.noneResp, bhPlugExtSessionTracked k gs_ext tr_ext σH)
        else
          (ki kq).run σH.1.st >>= fun (kr, st') =>
            pure (kr, bhPlugExtSessionTracked k gs_ext tr_ext
              (bhE2EMirror { σH.1 with st := st' } kq kr, σH.2))) := by
      dsimp only [bhE2EDrvImplGenWithSessionTracked, bhPlugExtSessionTracked, isRef]
      rw [StateT.run_bind, StateT.run_get, pure_bind]
      have hBase : (bhPlugExt gs_ext σH.1).toModelDriverBase = σH.1.toModelDriverBase := rfl
      have hMeta : (bhPlugExt gs_ext σH.1).instMeta = σH.1.instMeta := rfl
      have hSt : (bhPlugExt gs_ext σH.1).st = σH.1.st := rfl
      cases kq <;>
        (dsimp only
         try rw [hBase]
         try rw [hMeta]
         split_ifs <;> first
           | rfl
           | (try rw [hSt]
              simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
                bind_assoc, pure_bind]
              refine bind_congr fun ⟨kr, st'⟩ => ?_
              exact congrArg (fun x => pure (kr, x, σH.2.set k tr_ext))
                (bhE2EMirror_bhPlugExt gs_ext { σH.1 with st := st' } _ kr)))
    rw [hL, hR]
    split_ifs
    · simp only [pure_bind]
      exact hk .noneResp σH gs_ext tr_ext h rfl
    · simp only [pure_bind]
      exact hk .noneResp σH gs_ext tr_ext h rfl
    · simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr, st'⟩ => ?_
      have hinsts : (bhE2EMirror { σH.1 with st := st' } kq kr).insts = σH.1.insts := by
        cases kq <;> cases kr <;> rfl
      exact hk kr (bhE2EMirror { σH.1 with st := st' } kq kr, σH.2) gs_ext tr_ext
        ⟨bhPrefixPlugInv_bhE2EMirror h.plug st' kq kr, by rw [hinsts]; exact h.tracks_len⟩ rfl
  · have hL :
        ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
            idA idB s)
          ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)
            (.inr (.inl (.inr ⟨sid⟩)))).run σH)).run gs_ext).run tr_ext =
        (bhE2ELocalStartSessionTracked T.init ki C K (some false) σH sid >>= fun (idx?, σH1) =>
          pure (((idx?, σH1), gs_ext), tr_ext)) := by
      simp only [bhShallowImplOfHandle, bhPrefixHandlePostWithSessionTracked, bhTargetQenc,
        bhTargetRdec, bhShallowStepPostLocalSessionTracked, StateT.run_mk, simulateQ_bind,
        StateT.run_bind, simulateQ_implExtSessionTracked_bhLiftP_run, simulateQ_pure,
        StateT.run_pure, bind_assoc, pure_bind]
    have hR :
        (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false)
          (.inr (.inl (.inr ⟨sid⟩)))).run (bhPlugExtSessionTracked k gs_ext tr_ext σH) =
        bhE2ELocalStartSessionTracked T.init ki C K (some false)
          (bhPlugExtSessionTracked k gs_ext tr_ext σH) sid := by
      dsimp only [bhE2EDrvImplGenWithSessionTracked]
      simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, Prod.mk.eta, bind_pure, bhE2ELocalStartGenWithSessionTracked_const_eq]
    obtain ⟨hStartEq, hStartInv⟩ :=
      bhE2ELocalStartSessionTracked_false_bhPlugExtSessionTracked T.init ki C K σH gs_ext tr_ext h
        sid
    rw [hL, hR, hStartEq]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine prob_bind_congr_of_support _ _ _ (fun ⟨idx?, σH1⟩ hp => ?_)
    exact hk idx? σH1 gs_ext tr_ext (hStartInv (idx?, σH1) hp) rfl
  · exact bhPrefixHandlePostWithSessionTracked_plugExt_sm_bind_eq T ki P C K qep decT encT k
      idA idB s i sq σH gs_ext tr_ext h k1 k2 hk

theorem bhShallowRunFuel_eq_simulateQ_with
    {κ ι Q R St : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) q →
      ∀ {fuel : ℕ}, q ≤ fuel → ∀ (s : St),
        bhShallowRunFuel qenc rdec h dflt oa fuel s =
          (simulateQ (bhShallowImplOfHandle qenc rdec h) oa).run s := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel _ s
    simp [bhShallowRunFuel, simulateQ_pure]
  | query_bind q mx ih =>
    intro qB hq fuel hfuel s
    rw [isQueryBoundP_query_bind_iff] at hq
    cases q with
    | inl n =>
      rw [run_simulateQ_query_bind]
      simp only [bhShallowRunFuel_query_inl, bhShallowImplOfHandle, StateT.run_mk, bind_assoc,
        pure_bind]
      refine bind_congr fun u => ih u (hq.2 u) hfuel s
    | inr t =>
      have hpos : 0 < qB := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hle : m ≤ f := by omega
      rw [run_simulateQ_query_bind]
      simp only [bhShallowRunFuel_query_inr_succ, bhShallowImplOfHandle, StateT.run_mk,
        bind_assoc, pure_bind]
      refine bind_congr fun p => ih (rdec t p.1) (hqm _) hle p.2

theorem bhPrefixHandlePostWithSessionTracked_plugExt_simulateQ_bind_eq {τ α β : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (mx : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH)
    (k1 : ((α × (BHE2EDrvState S ℓ × List τ)) × ExtState ℓ) × τ → ProbComp β)
    (k2 : α × (BHE2EDrvState S ℓ × List τ) → ProbComp β)
    (hk : ∀ r σH' gs_ext' tr_ext', BHPrefixPlugInvSessionTracked k idA idB s σH' →
      gs_ext'.b = gs_ext.b →
      k1 (((r, σH'), gs_ext'), tr_ext') =
        k2 (r, bhPlugExtSessionTracked k gs_ext' tr_ext' σH')) :
    (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
          idA idB s)
        ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)) mx).run σH)).run
          gs_ext).run tr_ext >>= k1) =
    ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false))
        mx).run (bhPlugExtSessionTracked k gs_ext tr_ext σH) >>= k2) := by
  induction mx using OracleComp.inductionOn generalizing σH gs_ext tr_ext with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk x σH gs_ext tr_ext h rfl
  | query_bind q m ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    exact bhPrefixHandlePostWithSessionTracked_plugExt_step_bind_eq T ki P C K qep decT encT k
      idA idB s q σH gs_ext tr_ext h _ _ (fun u σH' gs_ext' tr_ext' h' hb' =>
        ih u σH' gs_ext' tr_ext' h' (fun r σH'' gs_ext'' tr_ext'' h'' hb'' =>
          hk r σH'' gs_ext'' tr_ext'' h'' (hb''.trans hb')))

/-- Post-observation in the plugged world when `σ.insts.any (·.gs.isNone) = true`. -/
def bhComposedPostObsPlug {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (b_k : Bool) :
    (Bool × BHE2EDrvState S ℓ) × ExtState ℓ → ProbComp Bool :=
  fun ⟨⟨b', σ⟩, gs_ext⟩ =>
    if !allTestedSessionsFresh P σ.st then do
      let coin ← ($ᵗ Bool : ProbComp Bool)
      return coin
    else
      let w1 := bhE2EDrvWon σ true || ((b_k == true) && gs_ext.win)
      let w0 := bhE2EDrvWon σ false || ((b_k == false) && gs_ext.win)
      return (if w1 then true else if w0 then false else b')

theorem bhComposedPostObsSessionTracked_bhPlugExtSessionTracked_eq {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (b_k : Bool) {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256}
    (b' : Bool) (σH' : BHE2EDrvState S ℓ × List τ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH') (hb : gs_ext.b = b_k) :
    bhComposedPostObsPlug P b_k ((b', σH'.1), gs_ext) =
      bhComposedPostObsSessionTracked P (b', bhPlugExtSessionTracked k gs_ext tr_ext σH') := by
  unfold bhComposedPostObsPlug bhComposedPostObsSessionTracked bhComposedPostObs
    bhPlugExtSessionTracked
  have hAny : σH'.1.insts.any (fun d => d.gs.isNone) = true := h.plug.any_isNone_true
  have hSt : (bhPlugExt gs_ext σH'.1).st = σH'.1.st := rfl
  simp [bhE2EDrvWon_bhPlugExt, hAny, hb, hSt]

/-- Post-processing in `bhPrefixRedWithSessionTracked` Stage 2 when `σ.paused = true`. -/
def bhPrefixRedPost {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (flip b' : Bool)
    (σ : BHE2EDrvState S ℓ) : ProbComp Bool :=
  if !allTestedSessionsFresh P σ.st then do
    let coin ← ($ᵗ Bool : ProbComp Bool)
    return (coin ^^ flip)
  else
    let out := if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b'
    pure (out ^^ flip)

theorem bhPrefixHandlePostWithSessionTracked_plugExt_simulateQ_postObs_bind_eq {τ β : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (mx : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (σH : BHE2EDrvState S ℓ × List τ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH)
    (f : Bool → ProbComp β) :
    (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
          idA idB s)
        ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)) mx).run σH)).run
          gs_ext).run tr_ext >>=
      fun x => bhComposedPostObsPlug P gs_ext.b ((x.1.1.1, x.1.1.2.1), x.1.2) >>= f) =
    ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false))
        mx).run (bhPlugExtSessionTracked k gs_ext tr_ext σH) >>=
      fun x => bhComposedPostObsSessionTracked P x >>= f) :=
  bhPrefixHandlePostWithSessionTracked_plugExt_simulateQ_bind_eq T ki P C K qep decT encT k
    idA idB s mx σH gs_ext tr_ext h
    (fun x => bhComposedPostObsPlug P gs_ext.b ((x.1.1.1, x.1.1.2.1), x.1.2) >>= f)
    (fun x => bhComposedPostObsSessionTracked P x >>= f)
    (fun b' σH' gs_ext' tr_ext' h' hb' => by
      rw [bhComposedPostObsSessionTracked_bhPlugExtSessionTracked_eq P gs_ext.b b' σH' gs_ext'
        tr_ext' h' hb'])

theorem simulateQ_implExtSessionTracked_bhPrefixRedWithSessionTracked_eval2_paused {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256) (k qTot : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (c : BHPrefixCtx) (p : Option ℕ)
    (σH_p : BHE2EDrvState S ℓ × List τ)
    (cont : (bhTargetGameSpec S ℓ (BitVec 512)).Range t →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hInv : BHPrefixPlugInvSessionTracked k idA idB s σH_p)
    (hQ : ∀ v, (cont v).IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    (flip : Bool) (gs0 : ExtState ℓ) (tr0 : τ) :
    let v := bhTargetRdec t (.inl (.inr p))
    ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
        idA idB s)
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2
        (.paused t c p σH_p cont) flip qTot false)).run gs0).run tr0 =
    (do
      let (((b', σH'), gs_ext), tr_ext) ←
        (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
            idA idB s)
          ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k))
            (cont v)).run ({ σH_p.1 with b := flip }, σH_p.2))).run gs0).run tr0)
      let w ← bhPrefixRedPost P flip b' σH'.1
      return ((w, gs_ext), tr_ext)) := by
  intro v
  change ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
        idA idB s)
      (bhShallowRunFuel bhTargetQenc bhTargetRdec
        (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k) false (cont v) qTot
        ({ σH_p.1 with b := flip }, σH_p.2) >>= fun p0 =>
        (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).finish p0.2 p0.1 flip)).run
        gs0).run tr0 = _
  rw [bhShallowRunFuel_eq_simulateQ_with bhTargetQenc bhTargetRdec
      (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k) false (hQ v) le_rfl
      ({ σH_p.1 with b := flip }, σH_p.2)]
  simp only [simulateQ_bind, StateT.run_bind]
  refine prob_bind_congr_of_support _ _ _ (fun x hmem => ?_)
  rcases x with ⟨⟨⟨b', σH'⟩, gs_ext⟩, tr_ext⟩
  have hInv_flip : BHPrefixPlugInvSessionTracked k idA idB s ({ σH_p.1 with b := flip }, σH_p.2) :=
    bhPrefixPlugInvSessionTracked_with_b hInv flip
  have hpaused' : σH'.1.paused = true := by
    have hPres : ∀ {α : Type} (mx : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
        (σH0 : BHE2EDrvState S ℓ × List τ) (gs_0 : ExtState ℓ) (tr_0 : τ),
        BHPrefixPlugInvSessionTracked k idA idB s σH0 →
        ∀ x ∈ support (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep
            decT encT idA idB s)
          ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)) mx).run
            σH0)).run gs_0).run tr_0),
        x.1.1.2.1.paused = true := by
      intro α mx σH0 gs_0 tr_0 hInv0
      have h0 := bhPrefixHandlePostWithSessionTracked_plugExt_simulateQ_bind_eq T ki P C K qep
        decT encT k idA idB s mx σH0 gs_0 tr_0 hInv0
        (fun x => pure x.1.1.2.1.paused)
        (fun _ => pure true)
        (fun _ σH'' _ _ h'' _ => by rw [h''.plug.paused_true])
      intro x hx
      have h1 : ∀ y ∈ support ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
          (bhMkKeyBitConst false)) mx).run (bhPlugExtSessionTracked k gs_0 tr_0 σH0) >>=
          fun _ => pure true),
          y = true := by
        intro y hy
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
        rcases hy with ⟨_, _, rfl⟩; rfl
      have h2 : x.1.1.2.1.paused ∈ support
          ((((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
              idA idB s)
            ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
              (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)) mx).run
              σH0)).run gs_0).run tr_0) >>= fun z => pure z.1.1.2.1.paused) := by
        rw [support_bind]
        exact Set.mem_iUnion₂.mpr ⟨x, hx, by simp⟩
      rw [h0] at h2
      exact h1 _ h2
    exact hPres (cont v) ({ σH_p.1 with b := flip }, σH_p.2) gs0 tr0 hInv_flip
      (((b', σH'), gs_ext), tr_ext) hmem
  dsimp only [bhPrefixRedWithSessionTracked, bhShallowFinishPrefix]
  rw [simulateQ_implExtSessionTracked_bhLiftP_run]
  unfold bhPrefixRedPost
  simp only [hpaused', Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-! ## Session-tracked prefix telescope -/

private theorem evalDist_bind_pure_false_apply_true {α : Type} (c : ProbComp α) :
    𝒟[c >>= fun _ => (pure false : ProbComp Bool)] {true} = 0 := by
  rw [evalDist_bind_apply_lintegral]; simp

/-- Mixture bias decomposition for `Prod.fst <$> gameRSessionTracked` into `boolDist` between
fixed-bit `runRSessionTracked` endpoints. -/
theorem boolBias_mix_gameRSessionTracked_eq {α Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (oa : ProbComp α) (sm : α → SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (R : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => Prod.fst <$> gameRSessionTracked T (sm o) Δ qep cfg (R o)].boolBias =
      𝒟[oa >>= fun o => runRSessionTracked T (sm o) Δ qep cfg true (R o) >>=
          fun p => pure (p.1.1 || p.1.2.win)].boolDist
        𝒟[oa >>= fun o => runRSessionTracked T (sm o) Δ qep cfg false (R o) >>=
          fun p => pure (p.1.1 && !p.1.2.win)] := by
  have hg : ∀ o, Prod.fst <$> gameRSessionTracked T (sm o) Δ qep cfg (R o) = (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then
          (runRSessionTracked T (sm o) Δ qep cfg true (R o) >>=
            fun p => pure (p.1.1 || p.1.2.win))
        else
          (runRSessionTracked T (sm o) Δ qep cfg false (R o) >>=
            fun p => pure (p.1.1 && !p.1.2.win))
      return (b == z)) := by
    intro o
    unfold gameRSessionTracked runRSessionTracked
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, StateT.run_bind,
      StateT.run_pure]
    refine bind_congr fun b => ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr fun _k => bind_congr fun ⟨⟨w, gs⟩, _tr⟩ => ?_
      cases w <;> cases gs.win <;> rfl
    · simp only [↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr fun _k => bind_congr fun ⟨⟨w, gs⟩, _tr⟩ => ?_
      cases w <;> cases gs.win <;> rfl
  simp only [hg]
  rw [OracleComp.evalDist_bind_bind_swap oa ($ᵗ Bool), ← evalDist_boolBias_bind_uniformBool]
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]

theorem evalDist_bhPrefixExtPairExpWithSessionTracked_not_fst_eq {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (flip : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx) :
    𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k true o] {true} =
    𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k false o] {true} := by
  rcases o with ⟨ctx, m⟩
  cases m with
  | done b' σH' => rfl
  | paused t c p σH_p cont =>
    unfold bhPrefixExtPairExpWithSessionTracked
    have h (b_k : Bool) :
        ((fun p0 : Bool × Bool => !p0.1 && (p0.2 == !flip)) <$>
          (bhPrefixPlugContWithSessionTracked T ki P C K qep decT encT k b_k
            (ctx, .paused t c p σH_p cont) >>=
            fun x => bhComposedPostObsSessionTracked P x >>= fun y => pure (true, y))) =
        ((bhPrefixPlugContWithSessionTracked T ki P C K qep decT encT k b_k
            (ctx, .paused t c p σH_p cont) >>=
            bhComposedPostObsSessionTracked P) >>= fun _ => pure false) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_and]
    dsimp only
    rw [h true, h false, evalDist_bind_pure_false_apply_true, evalDist_bind_pure_false_apply_true]

set_option maxHeartbeats 800000 in
theorem evalDist_bhPrefixExtPairExpWithSessionTracked_fst_true_le_runRSessionTracked
    {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (flip : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx)
    (ho : o ∈ support (stageOneAsProbComp
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot
        false))) :
    𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k true o] {true} ≤
    𝒟[runRSessionTracked T
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
          ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) true
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1.1 || p.1.2.win)] {true} := by
  have hprops :=
    mem_support_bhStage1ToProb_eval1_withSessionTracked_props T P ki C K qep decT encT k qTot B hQ
      ho
  rcases o with ⟨ctx, m⟩
  cases m with
  | done b' σH' =>
    unfold bhPrefixExtPairExpWithSessionTracked
    have h :
        ((fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
          (bhPrefixPlugContWithSessionTracked T ki P C K qep decT encT k true
            (ctx, .done b' σH') >>= fun x =>
            bhComposedPostObsSessionTracked P x >>= fun y => pure (false, y))) =
        ((bhPrefixPlugContWithSessionTracked T ki P C K qep decT encT k true
            (ctx, .done b' σH') >>= bhComposedPostObsSessionTracked P) >>= fun _ => pure false) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Bool.false_and]
    dsimp only
    rw [h, evalDist_bind_pure_false_apply_true]
    exact zero_le
  | paused t c p σH_p cont =>
    change ctx = c ∧ BHPrefixPlugInvSessionTracked k ctx.idA ctx.idB ctx.spkCoins σH_p ∧ _ at hprops
    rcases hprops with ⟨rfl, hInv, hQ_cont⟩
    unfold runRSessionTracked bhPrefixExtPairExpWithSessionTracked bhPrefixPlugContWithSessionTracked
    dsimp only
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob ($ᵗ SampledSessionKey) _ _ (fun k_fresh => ?_)
    let spqr := spqrV1SessionUniformCoins C.F K
    let gs0 := initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr ctx.idA ctx.idB) ℓ ctx.spkCoins).sendPart
      k_fresh true
    let tr0 := T.init k_fresh
    let v := bhTargetRdec t (.inl (.inr p))
    have hPlugB :
        bhPlugExtSessionTracked k gs0 tr0 ({ σH_p.1 with b := flip }, σH_p.2) =
          ({ (bhPlugExtSessionTracked k gs0 tr0 σH_p).1 with b := flip },
            (bhPlugExtSessionTracked k gs0 tr0 σH_p).2) := rfl
    have hWithB :
        ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst false)) (cont v)).run (bhPlugExtSessionTracked k gs0 tr0 σH_p) >>=
          fun x => bhComposedPostObsSessionTracked P x >>= fun y => pure (true && (y == !flip))) =
        ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst false)) (cont v)).run
          (bhPlugExtSessionTracked k gs0 tr0 ({ σH_p.1 with b := flip }, σH_p.2)) >>=
          fun x => bhComposedPostObsSessionTracked P x >>= fun y => pure (true && (y == !flip))) := by
      symm
      rw [hPlugB, simulateQ_bhE2EDrvImplGenWithSessionTracked_with_b]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        bhComposedPostObsSessionTracked_with_b, Prod.mk.eta]
    change 𝒟[((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst false)) (cont v)).run (bhPlugExtSessionTracked k gs0 tr0 σH_p) >>=
          fun x => bhComposedPostObsSessionTracked P x >>=
            fun y => pure (true && (y == !flip)))] {true} ≤
      𝒟[((simulateQ (implExtSessionTracked T C spqr qep decT encT ctx.idA ctx.idB ctx.spkCoins)
          ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2
            (.paused t ctx p σH_p cont) flip qTot false)).run gs0).run tr0 >>=
          fun p0 => pure (p0.1.1 || p0.1.2.win)] {true}
    rw [hWithB,
      simulateQ_implExtSessionTracked_bhPrefixRedWithSessionTracked_eval2_paused T ki P C K qep
        decT encT ctx.idA ctx.idB ctx.spkCoins k qTot t ctx p σH_p cont hInv hQ_cont flip gs0 tr0,
      ← bhPrefixHandlePostWithSessionTracked_plugExt_simulateQ_postObs_bind_eq T ki P C K qep
        decT encT k ctx.idA ctx.idB ctx.spkCoins (cont v) ({ σH_p.1 with b := flip }, σH_p.2)
        gs0 tr0 (bhPrefixPlugInvSessionTracked_with_b hInv flip)]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob_of_support _ _ _ (fun x _ => ?_)
    rcases x with ⟨⟨⟨b', σH'⟩, gs_ext⟩, _tr_ext⟩
    have hb0 : gs0.b = true := rfl
    unfold bhComposedPostObsPlug bhPrefixRedPost
    simp only [hb0, beq_self_eq_true, Bool.true_and]
    have hbf : (true == false) = false := rfl
    simp only [hbf, Bool.false_and, Bool.or_false]
    by_cases hC : allTestedSessionsFresh P σH'.1.st = true
    · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      have hle := slotStep_bool_le_true true true false (bhE2EDrvWon σH'.1 true)
        (bhE2EDrvWon σH'.1 false) gs_ext.win b' flip
      unfold slotStepY1 slotStepWRed slotStepOut at hle
      simpa using evalDist_bind_mono_of_imp (pure ()) (fun _ => _) (fun _ => _) (fun _ => hle)
    · have hNC : (!allTestedSessionsFresh P σH'.1.st) = true := by
        cases hc : allTestedSessionsFresh P σH'.1.st <;> simp_all
      simp only [hNC, ↓reduceIte, bind_assoc, pure_bind]
      refine evalDist_bind_mono_of_imp ($ᵗ Bool) _ _ (fun coin => ?_)
      have hle := slotStep_bool_le_true true false coin (bhE2EDrvWon σH'.1 true)
        (bhE2EDrvWon σH'.1 false) gs_ext.win b' flip
      unfold slotStepY1 slotStepWRed at hle
      simpa using hle

set_option maxHeartbeats 800000 in
theorem evalDist_runRSessionTracked_le_bhPrefixExtPairExpWithSessionTracked_fst_false
    {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (flip : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx)
    (ho : o ∈ support (stageOneAsProbComp
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot
        false))) :
    𝒟[runRSessionTracked T
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
          ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) false
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1.1 && !p.1.2.win)] {true} ≤
    𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k false o] {true} := by
  have hprops :=
    mem_support_bhStage1ToProb_eval1_withSessionTracked_props T P ki C K qep decT encT k qTot B hQ
      ho
  rcases o with ⟨ctx, m⟩
  cases m with
  | done b' σH' =>
    have hpaused : σH'.1.paused = false := hprops
    unfold runRSessionTracked
    change 𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= fun k_fresh =>
        let gs0 := initState
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) ctx.idA ctx.idB)
            ℓ ctx.spkCoins).sendPart k_fresh false
        let tr0 := T.init k_fresh
        ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
            ctx.idA ctx.idB ctx.spkCoins)
          (bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
            (bhShallowFinishPrefix P σH'.1 b' flip))).run gs0).run tr0 >>=
          fun p => pure (p.1.1 && !p.1.2.win)] {true} ≤ _
    have hDone : ∀ k_fresh : SampledSessionKey,
        (let gs0 := initState
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) ctx.idA ctx.idB)
            ℓ ctx.spkCoins).sendPart k_fresh false
         let tr0 := T.init k_fresh
         ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
            ctx.idA ctx.idB ctx.spkCoins)
          (bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
            (bhShallowFinishPrefix P σH'.1 b' flip))).run gs0).run tr0 >>=
          fun p => pure (p.1.1 && !p.1.2.win)) =
        pure false := by
      intro k_fresh
      dsimp only [bhShallowFinishPrefix]
      rw [simulateQ_implExtSessionTracked_bhLiftP_run]
      simp [hpaused]
    simp only [hDone, evalDist_bind_pure_false_apply_true]
    exact zero_le
  | paused t c p σH_p cont =>
    change ctx = c ∧ BHPrefixPlugInvSessionTracked k ctx.idA ctx.idB ctx.spkCoins σH_p ∧ _ at hprops
    rcases hprops with ⟨rfl, hInv, hQ_cont⟩
    unfold runRSessionTracked bhPrefixExtPairExpWithSessionTracked bhPrefixPlugContWithSessionTracked
    dsimp only
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob ($ᵗ SampledSessionKey) _ _ (fun k_fresh => ?_)
    let spqr := spqrV1SessionUniformCoins C.F K
    let gs0 := initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr ctx.idA ctx.idB) ℓ ctx.spkCoins).sendPart
      k_fresh false
    let tr0 := T.init k_fresh
    let v := bhTargetRdec t (.inl (.inr p))
    have hPlugB :
        bhPlugExtSessionTracked k gs0 tr0 ({ σH_p.1 with b := flip }, σH_p.2) =
          ({ (bhPlugExtSessionTracked k gs0 tr0 σH_p).1 with b := flip },
            (bhPlugExtSessionTracked k gs0 tr0 σH_p).2) := rfl
    have hWithB :
        ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst false)) (cont v)).run (bhPlugExtSessionTracked k gs0 tr0 σH_p) >>=
          fun x => bhComposedPostObsSessionTracked P x >>= fun y => pure (true && (y == !flip))) =
        ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst false)) (cont v)).run
          (bhPlugExtSessionTracked k gs0 tr0 ({ σH_p.1 with b := flip }, σH_p.2)) >>=
          fun x => bhComposedPostObsSessionTracked P x >>= fun y => pure (true && (y == !flip))) := by
      symm
      rw [hPlugB, simulateQ_bhE2EDrvImplGenWithSessionTracked_with_b]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        bhComposedPostObsSessionTracked_with_b, Prod.mk.eta]
    change 𝒟[((simulateQ (implExtSessionTracked T C spqr qep decT encT ctx.idA ctx.idB ctx.spkCoins)
          ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2
            (.paused t ctx p σH_p cont) flip qTot false)).run gs0).run tr0 >>=
          fun p0 => pure (p0.1.1 && !p0.1.2.win)] {true} ≤
      𝒟[((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst false)) (cont v)).run (bhPlugExtSessionTracked k gs0 tr0 σH_p) >>=
          fun x => bhComposedPostObsSessionTracked P x >>=
            fun y => pure (true && (y == !flip)))] {true}
    rw [hWithB,
      simulateQ_implExtSessionTracked_bhPrefixRedWithSessionTracked_eval2_paused T ki P C K qep
        decT encT ctx.idA ctx.idB ctx.spkCoins k qTot t ctx p σH_p cont hInv hQ_cont flip gs0 tr0,
      ← bhPrefixHandlePostWithSessionTracked_plugExt_simulateQ_postObs_bind_eq T ki P C K qep
        decT encT k ctx.idA ctx.idB ctx.spkCoins (cont v) ({ σH_p.1 with b := flip }, σH_p.2)
        gs0 tr0 (bhPrefixPlugInvSessionTracked_with_b hInv flip)]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob_of_support _ _ _ (fun x _ => ?_)
    rcases x with ⟨⟨⟨b', σH'⟩, gs_ext⟩, _tr_ext⟩
    have hb0 : gs0.b = false := rfl
    unfold bhComposedPostObsPlug bhPrefixRedPost
    simp only [hb0, beq_self_eq_true, Bool.true_and]
    have hbf : (false == true) = false := rfl
    simp only [hbf, Bool.false_and, Bool.or_false]
    by_cases hC : allTestedSessionsFresh P σH'.1.st = true
    · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      have hle := slotStep_bool_le_false true true false (bhE2EDrvWon σH'.1 true)
        (bhE2EDrvWon σH'.1 false) gs_ext.win b' flip
      unfold slotStepY0 slotStepWRed slotStepOut at hle
      simpa using evalDist_bind_mono_of_imp (pure ()) (fun _ => _) (fun _ => _) (fun _ => hle)
    · have hNC : (!allTestedSessionsFresh P σH'.1.st) = true := by
        cases hc : allTestedSessionsFresh P σH'.1.st <;> simp_all
      simp only [hNC, ↓reduceIte, bind_assoc, pure_bind]
      refine evalDist_bind_mono_of_imp ($ᵗ Bool) _ _ (fun coin => ?_)
      have hle := slotStep_bool_le_false true false coin (bhE2EDrvWon σH'.1 true)
        (bhE2EDrvWon σH'.1 false) gs_ext.win b' flip
      unfold slotStepY0 slotStepWRed at hle
      simpa using hle

/-- Single-step `boolDist` bound for `bhPrefixHybExpWithSessionTracked` under `hLazyEq`. -/
theorem boolDist_bhPrefixHybExpWithSessionTracked_step_le_of_lazyEq {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hLazyEq : ∀ b_k,
      𝒟[bhPrefixLazyFullExpWithSessionTracked T S ki P C K qep decT encT k b_k B] =
        𝒟[bhPrefixExactFullExpWithSessionTracked T S ki P C K qep decT encT k b_k B])
    (hQTot : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    𝒟[bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT (k + 1) B].boolDist
        𝒟[bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT k B] ≤
      ⨆ flip : Bool,
        𝒟[stageOneAsProbComp
            ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot
              false) >>=
          fun o =>
            Prod.fst <$>
              gameRSessionTracked T
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot
                  false)].boolBias := by
  rw [← bhPrefixExactFullExpWithSessionTracked_true_eq,
    ← bhPrefixExactFullExpWithSessionTracked_false_eq,
    ← hLazyEq true, ← hLazyEq false,
    bhPrefixLazyFullExpWithSessionTracked_eq_bind_bhPrefixExtExpWithSessionTracked T S ki P C K
      qep decT encT k qTot true B hQTot,
    bhPrefixLazyFullExpWithSessionTracked_eq_bind_bhPrefixExtExpWithSessionTracked T S ki P C K
      qep decT encT k qTot false B hQTot]
  refine boolDist_le_iSup_flip_of_beq_not_le _ _ _ (fun flip => ?_)
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  let oa :=
    stageOneAsProbComp
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false)
  have hdec : ∀ b : Bool,
      𝒟[oa >>= fun o => bhPrefixExtExpWithSessionTracked T S ki P C K qep decT encT k b o >>=
          fun x => pure (x == !flip)] {true} =
        𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k b o] {true} +
        𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k b o] {true} :=
    fun b => evalDist_bind_apply_eq_add _ _ _ _ true fun o => by
      unfold bhPrefixExtExpWithSessionTracked
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      exact evalDist_bind_fst_or_not_fst _ flip
  have h0 :
      𝒟[oa >>= fun o => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
          bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k true o] {true} =
        𝒟[oa >>= fun o => (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
          bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k false o] {true} :=
    evalDist_bind_congr_prob_of_support _ _ _ fun o _ =>
      evalDist_bhPrefixExtPairExpWithSessionTracked_not_fst_eq T S ki P C K qep decT encT k flip o
  have h1 :
      𝒟[oa >>= fun o => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
          bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k true o] {true} ≤
        𝒟[oa >>= fun o => runRSessionTracked T
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
              o.1.idA o.1.idB) ℓ o.1.spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) true
            ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot
              false) >>= fun p => pure (p.1.1 || p.1.2.win)] {true} :=
    evalDist_bind_mono_prob_of_support _ _ _ fun o ho =>
      evalDist_bhPrefixExtPairExpWithSessionTracked_fst_true_le_runRSessionTracked T S ki P C K qep
        decT encT k qTot flip B hQTot o ho
  have h2 :
      𝒟[oa >>= fun o => runRSessionTracked T
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
              o.1.idA o.1.idB) ℓ o.1.spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) false
            ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot
              false) >>= fun p => pure (p.1.1 && !p.1.2.win)] {true} ≤
        𝒟[oa >>= fun o => (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
          bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k false o] {true} :=
    evalDist_bind_mono_prob_of_support _ _ _ fun o ho =>
      evalDist_runRSessionTracked_le_bhPrefixExtPairExpWithSessionTracked_fst_false T S ki P C K
        qep decT encT k qTot flip B hQTot o ho
  have h3 := Measure.apply_true_le_add_boolDist
    𝒟[oa >>= fun o => runRSessionTracked T
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
          o.1.idA o.1.idB) ℓ o.1.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) true
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1.1 || p.1.2.win)]
    𝒟[oa >>= fun o => runRSessionTracked T
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
          o.1.idA o.1.idB) ℓ o.1.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) false
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1.1 && !p.1.2.win)]
  have hb := boolBias_mix_gameRSessionTracked_eq T oa
    (fun o =>
      sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
        ℓ o.1.spkCoins)
    (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
    (fun o => (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false)
  beta_reduce at hb
  simp only [map_eq_bind_pure_comp, Function.comp_def] at hb
  change 𝒟[oa >>= fun o => bhPrefixExtExpWithSessionTracked T S ki P C K qep decT encT k true o >>=
      fun x => pure (x == !flip)] {true} ≤
    𝒟[oa >>= fun o => bhPrefixExtExpWithSessionTracked T S ki P C K qep decT encT k false o >>=
      fun x => pure (x == !flip)] {true} +
    𝒟[oa >>= fun o => gameRSessionTracked T
        (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
          o.1.idA o.1.idB) ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun x => pure x.1].boolBias
  rw [hb, hdec true, hdec false, h0]
  exact (add_le_add (h1.trans (h3.trans (add_le_add h2 le_rfl))) le_rfl).trans_eq (by ac_rfl)

/-- Bounds the boolean bias of `bhE2EExpWithKiSessionTracked` at `secb = false` under `hLazyEq` by
the `qStart`-step sum of session-tracked mixture biases. -/
theorem boolBias_bhE2EExpWithKiSessionTracked_false_le_sum_prefix_steps_of_lazyEq
    {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart qTot : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hLazyEq : ∀ k < qStart, ∀ b_k,
      𝒟[bhPrefixLazyFullExpWithSessionTracked T S ki P C K qep decT encT k b_k B] =
        𝒟[bhPrefixExactFullExpWithSessionTracked T S ki P C K qep decT encT k b_k B])
    (hQStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart)
    (hQTot : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    𝒟[bhE2EExpWithKiSessionTracked T false S P ki C K qep decT encT B].boolBias ≤
      ∑ k ∈ Finset.range qStart,
        ⨆ flip : Bool,
          𝒟[stageOneAsProbComp
              ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) ()
                qTot false) >>=
            fun o =>
              Prod.fst <$>
                gameRSessionTracked T
                  (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                    ℓ o.1.spkCoins)
                  (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                  ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2 o.2 flip qTot
                    false)].boolBias := by
  rw [boolBias_bhE2EExpWithKiSessionTracked_false_eq_boolDist_prefixHyb_endpoints T S ki P C K qep
      decT encT qStart B hQStart,
    Measure.boolDist_comm]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT k B]) qStart).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Measure.boolDist_comm]
  exact boolDist_bhPrefixHybExpWithSessionTracked_step_le_of_lazyEq T S ki P C K qep decT encT k
    qTot B (hLazyEq k (Finset.mem_range.mp hk)) hQTot

end Computational.Proofs.LibsignalCli.MainHaltedPrefix
