/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhStepEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhGrow
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Evaluation Equivalence for the One-Key `Auth` Gap-DH Program

**Checked by Lean.** Proves that evaluating `fgAuth1KeyGapDhProg S b.q_total` against a bounded
`Auth` adversary induces the same output distribution as `fgAuth1KeyGapDhAdv4 S b A`
(`fgAuth1KeyGapDhProg_eval_eq`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open SignalPqxdh.Security.FgGapDh1Key Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open OracleSpec OracleComp
open scoped ENNReal

theorem a1gHandleDsl_eval (S : Setup) (K : Nat) (st : FgAuth1KeySimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st.sim) (qv : AuthQuery S) :
    (a1gHandleDsl S K).eval (.cons (a1gStToVal (paVal U V useDh1 t sIdx) st)
        (.cons (authQueryToVal qv) .nil)) =
      (fun r => (authRespToVal r.1, a1gStToVal (paVal U V useDh1 t sIdx) r.2)) <$>
        fgAuth1KeyStepHalt useDh1 t sIdx S K U V qv st :=
  a1gStepC_eval S K _ st U V useDh1 t sIdx _ _ qv rfl rfl hB

theorem a1gInitDsl_eval (S : Setup) (U V : Bytes) :
    (a1gInitDsl S).eval (.cons (U, V) .nil) =
      (unifGdhSign (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) >>= fun p =>
        unifGdhSign ($ᵗ Bool) >>= fun secb =>
          pure ((), a1gStToVal (paVal U V (decide (p.1 < S.N_id))
            (if p.1 < S.N_id then p.1 else p.1 - S.N_id) p.2)
            (FgAuth1KeySimState.empty S secb))) := by
  simp only [a1gInitDsl, bindV, v, Comp.eval, liftGdhComp_eval, Expr.eval,
    Ext.refl_wk, Env.get_vz]
  rw [fgInitDsl_eval]
  simp only [unifGdhSign, liftGdhToSign_bind, liftGdhToSign_pure, bind_assoc, pure_bind,
    a1gStToVal, FgAuth1KeySimState.empty]

theorem a1gFinishDsl_eval (S : Setup) (K : Nat) (st : FgAuth1KeySimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st.sim) (a : Bool) :
    (a1gFinishDsl S K).eval (.cons (a1gStToVal (paVal U V useDh1 t sIdx) st) (.cons a .nil)) =
      liftGdhToSign (extractCdhFromAuthSimState S useDh1 K U V st.sim) := by
  simp only [a1gFinishDsl, letV, Comp.eval_letC, renameComp_eval, pullEnv_twoVarRen,
    liftGdhComp_eval, Expr.eval, Env.get_vz, Env.get_vs, a1gStToVal]
  rw [← fgFinishDsl_eval S K st.sim U V useDh1 t sIdx hB a]

theorem a1gRun_eq (S : Setup) (K : Nat) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (A : OracleComp (unifSpec + authSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) K) (secb : Bool) :
    ((simulateQ (handlerImpl (C := authCodec S) (a1gHandleDsl S K)) A).run
        (a1gStToVal (paVal U V useDh1 t sIdx) (FgAuth1KeySimState.empty S secb)) >>=
        fun p => (a1gFinishDsl S K).eval (.cons p.2 (.cons p.1 .nil))) =
      (runWithGdhSignStep (fgAuth1KeyStepHalt useDh1 t sIdx S K U V) A
          (FgAuth1KeySimState.empty S secb) >>= fun p =>
        liftGdhToSign (extractCdhFromAuthSimState S useDh1 K U V p.2.sim)) := by
  refine simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind
    (C := authCodec S) (σ := a1gStTy) (a1gHandleDsl S K) (fgAuth1KeyStepHalt useDh1 t sIdx S K U V)
    (a1gStToVal (paVal U V useDh1 t sIdx)) (fun k st => AgInv K k st.sim)
    (fun k st h => AgInv.mono K k st.sim h)
    (fun k q st h => ?_)
    (fun k q st h x hx => fgAuth1KeyStepHalt_agInv useDh1 t sIdx K k U V q st h x hx)
    _ _ (fun a st h => ?_) A K hA _ (AgInv.empty S K secb)
  · dsimp only [authCodec]
    rw [a1gHandleDsl_eval S K st U V useDh1 t sIdx (AgInv.bnd K (k + 1) st.sim h) q]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
      agValToAuthResp_authRespToVal]
  · exact a1gFinishDsl_eval S K st U V useDh1 t sIdx (AgInv.bnd K 0 st.sim h) a

theorem a1g2HandleDsl_eval (S : Setup) (K : Nat) {k : Nat} (st : FgAuth1KeySimState S)
    (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat) (hI : AgInv2 K (k + 1) st) (qv : AuthQuery S) :
    (a1g2HandleDsl S K).eval (.cons (a1g2StToVal S K (pa2Val S U V useDh1 t sIdx) st)
        (.cons (authQueryToVal qv) .nil)) =
      (fun r => (authRespToVal r.1, a1g2StToVal S K (pa2Val S U V useDh1 t sIdx) r.2)) <$>
        fgAuth1KeyStepHalt useDh1 t sIdx S K U V qv st :=
  a1gStep2C_eval S K _ st U V useDh1 t sIdx _ _ qv rfl rfl hI

private theorem fgFinish2Dsl_eval (S : Setup) (K : Nat) (st : FgAuthSimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hB : AgBnd K st) (hresp : st.respRecs.length ≤ K) (a : Bool) :
    (fgFinish2Dsl S K).eval (.cons (pa2Val S U V useDh1 t sIdx, fgSimToVal st) (.cons a .nil)) =
      extractCdhFromAuthSimState S useDh1 K U V st := by
  simp only [fgFinish2Dsl, letV, Comp.eval_letC, Expr.eval, Env.get_vz, Env.get_vs]
  exact fgExtract2C_eval S K _ U V useDh1 t sIdx st _ _ rfl rfl hB hresp

theorem a1g2FinishDsl_eval (S : Setup) (K : Nat) (st : FgAuth1KeySimState S) (U V : Bytes)
    (useDh1 : Bool) (t sIdx : Nat) (hI : AgInv2 K 0 st) (a : Bool) :
    (a1g2FinishDsl S K).eval
        (.cons (a1g2StToVal S K (pa2Val S U V useDh1 t sIdx) st) (.cons a .nil)) =
      liftGdhToSign (extractCdhFromAuthSimState S useDh1 K U V st.sim) := by
  simp only [a1g2FinishDsl, letV, Comp.eval_letC, renameComp_eval, pullEnv_twoVarRen,
    liftGdhComp_eval, Expr.eval, Env.get_vz, Env.get_vs, a1g2StToVal]
  have hresp : st.sim.respRecs.length ≤ K := by have := hI.2.1; omega
  rw [fgFinish2Dsl_eval S K st.sim U V useDh1 t sIdx hI.bnd hresp a]

theorem a1g2Run_eq (S : Setup) (K : Nat) (U V : Bytes) (useDh1 : Bool) (t sIdx : Nat)
    (A : OracleComp (unifSpec + authSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) K) (secb : Bool) :
    ((simulateQ (handlerImpl (C := authCodec S) (a1g2HandleDsl S K)) A).run
        (a1g2StToVal S K (pa2Val S U V useDh1 t sIdx) (FgAuth1KeySimState.empty S secb)) >>=
        fun p => (a1g2FinishDsl S K).eval (.cons p.2 (.cons p.1 .nil))) =
      (runWithGdhSignStep (fgAuth1KeyStepHalt useDh1 t sIdx S K U V) A
          (FgAuth1KeySimState.empty S secb) >>= fun p =>
        liftGdhToSign (extractCdhFromAuthSimState S useDh1 K U V p.2.sim)) := by
  refine simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind
    (C := authCodec S) (σ := a1g2StTy) (a1g2HandleDsl S K)
    (fgAuth1KeyStepHalt useDh1 t sIdx S K U V)
    (a1g2StToVal S K (pa2Val S U V useDh1 t sIdx)) (fun k st => AgInv2 K k st)
    (fun k st h => AgInv2.mono K k st h)
    (fun k q st h => ?_)
    (fun k q st h x hx => fgAuth1KeyStepHalt_agInv2 useDh1 t sIdx K k U V q st h x hx)
    _ _ (fun a st h => ?_) A K hA _ (AgInv2.empty S K secb)
  · dsimp only [authCodec]
    rw [a1g2HandleDsl_eval S K st U V useDh1 t sIdx h q]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
      agValToAuthResp_authRespToVal]
  · exact a1g2FinishDsl_eval S K st U V useDh1 t sIdx h a

noncomputable def bernoulliRatioProb (A B : Nat) : ProbComp Bool :=
  if A = 0 then pure false
  else if B = 0 then pure true
  else if A ≤ B then do
    let x ← sampleIndexRange (A + B)
    let y1 ← sampleIndexRange A
    let y2 ← sampleIndexRange A
    pure (decide (x < y1 + y2 + 1))
  else do
    let x ← sampleIndexRange (A + B)
    let y1 ← sampleIndexRange B
    let y2 ← sampleIndexRange B
    pure (!decide (x < y1 + y2 + 1))

noncomputable def sampleSpkPair2Prob (S : Setup) : ProbComp (Option (Nat × Nat)) :=
  if S.N_spk_tot = 0 then pure none
  else do
    let uS ← sampleIndexRange S.N_id
    let jS ← sampleIndexRange S.N_recv
    pure (some (uS, jS))

noncomputable def sampleRole2Prob (S : Setup) : ProbComp a1gRole2Ty.denote :=
  if S.N_id = 0 then
    pure (.inr (.inl (0, 0)))
  else do
    let uT ← sampleIndexRange S.N_id
    let w ← sampleIndexRange (1 + S.N_send_opk + S.N_send_no_opk)
    if (w == 0) = true then
      pure (.inl uT)
    else if S.N_send_opk_tot = 0 then
      if S.N_send_no_opk_tot = 0 then
        pure (.inr (.inl (0, 0)))
      else do
        let iT ← sampleIndexRange S.N_send_no_opk
        pure (.inr (.inr (uT, iT)))
    else if S.N_send_no_opk_tot = 0 then do
      let iT ← sampleIndexRange S.N_send_opk
      pure (.inr (.inl (uT, iT)))
    else do
      let useOpk ← bernoulliRatioProb S.N_send_opk S.N_send_no_opk
      if useOpk = true then do
        let iT ← sampleIndexRange S.N_send_opk
        pure (.inr (.inl (uT, iT)))
      else do
        let iT ← sampleIndexRange S.N_send_no_opk
        pure (.inr (.inr (uT, iT)))

private theorem fgSampleIndexRange_eq (N : ℕ) :
    FgGapDh.sampleIndexRange N = sampleIndexRange N := by
  unfold FgGapDh.sampleIndexRange sampleIndexRange; rfl

private theorem bernoulliRatioC_eval (A B : Nat) {Δ : List (Ty pqSig)} (env : Env Δ) :
    (bernoulliRatioC A B).eval env = unifGdh (bernoulliRatioProb A B) := by
  unfold bernoulliRatioC bernoulliRatioProb
  split_ifs
  · simp [Comp.eval, Expr.eval, unifGdh, FgGapDh.embedUnif, embedPrim_pure]
  · simp [Comp.eval, Expr.eval, unifGdh, FgGapDh.embedUnif, embedPrim_pure]
  · simp only [bindV, v, eval_sampleIndexC, fgSampleIndexRange_eq, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
      liftComp_bind, liftComp_pure, agEmbedPrim_eq, embedPrim_bind, embedPrim_pure]
    refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
    simp
  · simp only [bindV, v, eval_sampleIndexC, fgSampleIndexRange_eq, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
      liftComp_bind, liftComp_pure, agEmbedPrim_eq, embedPrim_bind, embedPrim_pure]
    refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
    simp

private theorem sampleSpkPair2C_eval (S : Setup) {Δ : List (Ty pqSig)} (env : Env Δ) :
    (sampleSpkPair2C S).eval env = unifGdh (sampleSpkPair2Prob S) := by
  unfold sampleSpkPair2C sampleSpkPair2Prob
  by_cases h0 : S.N_spk_tot = 0
  · simp [h0, Comp.eval, Expr.eval, unifGdh, FgGapDh.embedUnif]
  · simp only [h0, ↓reduceIte, bindV, v, eval_sampleIndexC, fgSampleIndexRange_eq, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
      liftComp_bind, liftComp_pure, agEmbedPrim_eq, embedPrim_bind, embedPrim_pure]

private theorem sampleRole2C_eval (S : Setup) {Δ : List (Ty pqSig)} (env : Env Δ) :
    (sampleRole2C S).eval env = unifGdh (sampleRole2Prob S) := by
  unfold sampleRole2C sampleRole2Prob
  by_cases hId : S.N_id = 0
  · simp [hId, Comp.eval, Expr.eval, unifGdh, FgGapDh.embedUnif]
  · simp only [hId, ↓reduceIte, bindV, v, eval_natEq, eval_sampleIndexC, fgSampleIndexRange_eq,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz,
      unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
      liftComp_bind, agEmbedPrim_eq, embedPrim_bind]
    refine bind_congr fun uT => bind_congr fun w => ?_
    by_cases hw : (w == 0) = true
    · simp [hw, embedPrim_pure]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;>
        simp only [bernoulliRatioC_eval, eval_sampleIndexC, fgSampleIndexRange_eq,
          Comp.eval, Expr.eval, Env.get_vs, Env.get_vz,
          unifGdh, FgGapDh.embedUnif, _root_.SignalPqxdh.Security.embedUnif,
          liftComp_bind, liftComp_pure, agEmbedPrim_eq, embedPrim_bind, embedPrim_pure]
      refine bind_congr fun useOpk => ?_
      cases useOpk <;>
        simp only [Bool.false_eq_true, ↓reduceIte,
          liftComp_bind, liftComp_pure, embedPrim_bind, embedPrim_pure]

private theorem fgInit2Dsl_eval (S : Setup) (U V : Bytes) :
    (fgInit2Dsl S).eval (.cons (U, V) .nil) =
      (unifGdh (sampleRole2Prob S) >>= fun role =>
        unifGdh (sampleSpkPair2Prob S) >>= fun spk =>
          unifGdh ($ᵗ Bool) >>= fun secb =>
            pure ((), ((U, (V, (role, spk))),
              fgSimToVal (FgAuthSimState.empty S secb)))) := by
  simp only [fgInit2Dsl, bindV, v, emptySimE, emptyAuthStE, fsMk, stMk,
    sampleRole2C_eval, sampleSpkPair2C_eval, eval_sampleBoolC, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
  rfl

theorem a1g2InitDsl_eval (S : Setup) (K : Nat) (U V : Bytes) :
    (a1g2InitDsl S K).eval (.cons (U, V) .nil) =
      (unifGdhSign (sampleRole2Prob S) >>= fun role =>
        unifGdhSign (sampleSpkPair2Prob S) >>= fun spk =>
          unifGdhSign ($ᵗ Bool) >>= fun secb =>
            pure ((), a1g2StToVal S K (U, (V, (role, spk)))
              (FgAuth1KeySimState.empty S secb))) := by
  simp only [a1g2InitDsl, bindV, v, Comp.eval, liftGdhComp_eval, Expr.eval,
    Ext.refl_wk, Env.get_vz]
  rw [fgInit2Dsl_eval]
  simp only [unifGdhSign, liftGdhToSign_bind, liftGdhToSign_pure, bind_assoc, pure_bind,
    a1g2StToVal, a1gClampedSigB, FgAuth1KeySimState.empty, Nat.sub_self, Nat.sub_zero]

private theorem mem_support_sampleIndexRange_lt {N x : ℕ} (hN : 0 < N)
    (hx : x ∈ support (sampleIndexRange N)) : x < N := by
  simp only [sampleIndexRange, hN, ↓reduceDIte, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨i, _, rfl⟩
  exact i.isLt

theorem sampleSpkPair2Prob_mem_support (S : Setup) {spk : Option (Nat × Nat)}
    (h : spk ∈ support (sampleSpkPair2Prob S)) :
    ∃ sIdx, spk = paSpkOpt S sIdx := by
  unfold sampleSpkPair2Prob at h
  by_cases h0 : S.N_spk_tot = 0
  · simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff] at h
    exact ⟨0, by simp [h, paSpkOpt, h0]⟩
  · simp only [h0, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at h
    rcases h with ⟨uS, huS, jS, hjS, rfl⟩
    have hPos : 0 < S.N_id * S.N_recv := Nat.pos_of_ne_zero h0
    have hu : uS < S.N_id := mem_support_sampleIndexRange_lt (Nat.pos_of_mul_pos_right hPos) huS
    have hj : jS < S.N_recv := mem_support_sampleIndexRange_lt (Nat.pos_of_mul_pos_left hPos) hjS
    have hlt : uS * S.N_recv + jS < S.N_spk_tot := by
      change uS * S.N_recv + jS < S.N_id * S.N_recv; nlinarith
    refine ⟨uS * S.N_recv + jS, ?_⟩
    have hdiv : (uS * S.N_recv + jS) / S.N_recv = uS := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (uS * S.N_recv + jS) % S.N_recv = jS := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp [paSpkOpt, hlt, hdiv, hmod]

theorem sampleRole2Prob_mem_support (S : Setup) {role : a1gRole2Ty.denote}
    (h : role ∈ support (sampleRole2Prob S)) :
    ∃ useDh1 t, role = pa2RoleVal S useDh1 t := by
  unfold sampleRole2Prob at h
  by_cases hId : S.N_id = 0
  · simp only [hId, ↓reduceIte, support_pure, Set.mem_singleton_iff] at h
    have hOpk0 : S.N_send_opk_tot = 0 := by simp [Setup.N_send_opk_tot, hId]
    have hTot0 : S.N_send_tot = 0 := by simp [Setup.N_send_tot, Setup.N_send_no_opk_tot, hOpk0, hId]
    exact ⟨false, 0, by simp [h, pa2RoleVal, hOpk0, hTot0, hId]⟩
  · simp only [hId, ↓reduceIte, MonadAttach.mem_support_bind] at h
    rcases h with ⟨uT, huT, w, hw, hRest⟩
    have hu : uT < S.N_id := mem_support_sampleIndexRange_lt (Nat.pos_of_ne_zero hId) huT
    by_cases hw0 : (w == 0) = true
    · simp only [hw0, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hRest
      exact ⟨true, uT, by simp [hRest, pa2RoleVal]⟩
    · simp only [hw0, Bool.false_eq_true, ↓reduceIte] at hRest
      have hwNe : w ≠ 0 := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hw0)
      have hwLt : w < 1 + S.N_send_opk + S.N_send_no_opk :=
        mem_support_sampleIndexRange_lt (by omega) hw
      have mkOpk : ∀ {iT : ℕ}, iT < S.N_send_opk →
          ∃ useDh1 t, (Sum.inr (Sum.inl (uT, iT)) : a1gRole2Ty.denote) = pa2RoleVal S useDh1 t := by
        intro iT hi
        have hlt : uT * S.N_send_opk + iT < S.N_send_opk_tot := by
          change uT * S.N_send_opk + iT < S.N_id * S.N_send_opk; nlinarith
        have hdiv : (uT * S.N_send_opk + iT) / S.N_send_opk = uT := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
        have hmod : (uT * S.N_send_opk + iT) % S.N_send_opk = iT := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
        exact ⟨false, uT * S.N_send_opk + iT, by simp [pa2RoleVal, hlt, hdiv, hmod]⟩
      have mkNoOpk : ∀ {iT : ℕ}, iT < S.N_send_no_opk →
          ∃ useDh1 t, (Sum.inr (Sum.inr (uT, iT)) : a1gRole2Ty.denote) = pa2RoleVal S useDh1 t := by
        intro iT hi
        let r := uT * S.N_send_no_opk + iT
        have hr : r < S.N_send_no_opk_tot := by
          change uT * S.N_send_no_opk + iT < S.N_id * S.N_send_no_opk; nlinarith
        have hge : ¬ (S.N_send_opk_tot + r < S.N_send_opk_tot) := by omega
        have hlt2 : S.N_send_opk_tot + r < S.N_send_tot := by
          unfold Setup.N_send_tot; omega
        have hdiv : r / S.N_send_no_opk = uT := by
          dsimp only [r]
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
        have hmod : r % S.N_send_no_opk = iT := by
          dsimp only [r]
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
        exact ⟨false, S.N_send_opk_tot + r,
          by simp [pa2RoleVal, hge, hlt2, hdiv, hmod]⟩
      by_cases hOpk0 : S.N_send_opk_tot = 0
      · by_cases hNoOpk0 : S.N_send_no_opk_tot = 0
        · have hA0 : S.N_send_opk = 0 := (Nat.mul_eq_zero.mp hOpk0).resolve_left hId
          have hB0 : S.N_send_no_opk = 0 := (Nat.mul_eq_zero.mp hNoOpk0).resolve_left hId
          omega
        · simp only [hOpk0, hNoOpk0, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff] at hRest
          rcases hRest with ⟨iT, hiT, rfl⟩
          have hBPos : 0 < S.N_send_no_opk :=
            Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hNoOpk0)
          exact mkNoOpk (mem_support_sampleIndexRange_lt hBPos hiT)
      · by_cases hNoOpk0 : S.N_send_no_opk_tot = 0
        · simp only [hOpk0, hNoOpk0, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff] at hRest
          rcases hRest with ⟨iT, hiT, rfl⟩
          have hAPos : 0 < S.N_send_opk :=
            Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hOpk0)
          exact mkOpk (mem_support_sampleIndexRange_lt hAPos hiT)
        · simp only [hOpk0, hNoOpk0, ↓reduceIte, MonadAttach.mem_support_bind] at hRest
          rcases hRest with ⟨useOpk, _, hBr⟩
          have hAPos : 0 < S.N_send_opk :=
            Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hOpk0)
          have hBPos : 0 < S.N_send_no_opk :=
            Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hNoOpk0)
          cases useOpk
          · simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind, support_pure,
              Set.mem_singleton_iff] at hBr
            rcases hBr with ⟨iT, hiT, rfl⟩
            exact mkNoOpk (mem_support_sampleIndexRange_lt hBPos hiT)
          · simp only [↓reduceIte, MonadAttach.mem_support_bind, support_pure,
              Set.mem_singleton_iff] at hBr
            rcases hBr with ⟨iT, hiT, rfl⟩
            exact mkOpk (mem_support_sampleIndexRange_lt hAPos hiT)

private theorem simulateQ_unifGdhSign {α : Type}
    (primImpl0 : QueryImpl primSpec ProbComp)
    (chalImpl : QueryImpl sigAndDdhSpec ProbComp) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl) (unifGdhSign mx) = mx := by
  unfold unifGdhSign unifGdh FgGapDh.embedUnif
  rw [agEmbedPrim_eq]
  unfold _root_.SignalPqxdh.Security.embedPrim
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp [liftGdhToSign_pure]
  | query_bind k cont ih =>
    simp
    exact bind_congr ih

scoped instance instMeasurableSpaceListUInt8 : MeasurableSpace (List UInt8) := ⊤
scoped instance instMeasurableSpaceBytes : MeasurableSpace Bytes := ⊤
scoped instance instMeasurableSpaceB32Denote : MeasurableSpace (B 32).denote := ⊤
scoped instance instDiscreteMeasurableSpaceListUInt8 : DiscreteMeasurableSpace (List UInt8) :=
  ⟨fun _ => trivial⟩
scoped instance instDiscreteMeasurableSpaceBytes : DiscreteMeasurableSpace Bytes :=
  ⟨fun _ => trivial⟩
scoped instance instDiscreteMeasurableSpaceB32Denote : DiscreteMeasurableSpace (B 32).denote :=
  ⟨fun _ => trivial⟩

section DistHelpers

local instance instMeasurableSpaceFinLocal (N : ℕ) : MeasurableSpace (Fin N) := ⊤

private theorem evalDist_sampleIndexRange_bind_bytes {N : ℕ} (hN : 0 < N)
    (g : ℕ → ProbComp Bytes) (z : Bytes) :
    𝒟[sampleIndexRange N >>= g] {z} =
      ∑ k ∈ Finset.range N, 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹ := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton z)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹) N

private theorem mul_evalDist_sampleIndexRange_bytes {N : ℕ} (hN : 0 < N)
    (f : ℕ → ProbComp Bytes) (z : Bytes) :
    (N : ℝ≥0∞) * 𝒟[sampleIndexRange N >>= f] {z} =
      ∑ i ∈ Finset.range N, 𝒟[f i] {z} := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [evalDist_sampleIndexRange_bind_bytes hN, ← Finset.sum_mul,
    ← mul_assoc, mul_comm (N : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, mul_one]

private theorem sum_range_mul_div_mod_ennreal' (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (M * N), g (k / N) (k % N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, g i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hPos : 0 < N := by omega
    rw [Nat.add_comm (m * N) j, Nat.add_mul_div_right j m hPos, Nat.div_eq_of_lt hj,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem sum_range_lt_split' (c K : ℕ) (hc : c ≤ K) (a b : ℝ≥0∞) :
    (∑ y ∈ Finset.range K, if y < c then a else b) =
      (c : ℝ≥0∞) * a + ((K - c : ℕ) : ℝ≥0∞) * b := by
  have hK : K = c + (K - c) := (Nat.add_sub_of_le hc).symm
  conv_lhs => rw [hK]
  rw [Finset.sum_range_add]
  congr 1
  · trans (∑ _y ∈ Finset.range c, a)
    · refine Finset.sum_congr rfl fun y hy => ?_
      simp [Finset.mem_range.mp hy]
    · simp
  · trans (∑ _y ∈ Finset.range (K - c), b)
    · refine Finset.sum_congr rfl fun y _ => ?_
      have hge : ¬ (c + y < c) := by omega
      simp [hge]
    · simp

private theorem sum_range_odd' (m : ℕ) :
    ∑ x ∈ Finset.range m, (2 * x + 1) = m * m := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem sum_range_sq_add_one (m : ℕ) :
    (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (y1 + y2 + 1)) = m * m * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib, ih]
    have hCombine : (∑ x ∈ Finset.range k, (x + k + 1)) + ∑ x ∈ Finset.range k, (k + x + 1) =
        (∑ x ∈ Finset.range k, (2 * x + 1)) + ∑ _x ∈ Finset.range k, (2 * k + 1) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      omega
    have h1 := sum_range_odd' k
    have h2 : ∑ _x ∈ Finset.range k, (2 * k + 1) = k * (2 * k + 1) := by simp
    nlinarith

private theorem sum_range_sq_sub_add_one (m K : ℕ) (h : m + m ≤ K) :
    (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (K - (y1 + y2 + 1))) = m * m * (K - m) := by
  have hAdd : (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (K - (y1 + y2 + 1))) +
      (∑ y1 ∈ Finset.range m, ∑ y2 ∈ Finset.range m, (y1 + y2 + 1)) = m * m * K := by
    rw [← Finset.sum_add_distrib]
    trans (∑ _y1 ∈ Finset.range m, m * K)
    · refine Finset.sum_congr rfl fun y1 hy1 => ?_
      rw [← Finset.sum_add_distrib]
      have hy1' : y1 < m := Finset.mem_range.mp hy1
      trans (∑ _y2 ∈ Finset.range m, K)
      · refine Finset.sum_congr rfl fun y2 hy2 => ?_
        have hy2' : y2 < m := Finset.mem_range.mp hy2
        omega
      · simp
    · simp [Nat.mul_assoc]
  rw [sum_range_sq_add_one] at hAdd
  have hmK : m ≤ K := by omega
  zify [hmK] at hAdd ⊢
  nlinarith

private theorem evalDist_bernoulliCube_scaled {M K : ℕ} (hM : 0 < M) (hMK : M + M ≤ K)
    (pT pF : ProbComp Bytes) (z : Bytes) :
    (K : ℝ≥0∞) * 𝒟[sampleIndexRange K >>= fun x =>
        sampleIndexRange M >>= fun y1 => sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
      (M : ℝ≥0∞) * 𝒟[pT] {z} + ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hK : 0 < K := by omega
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  have hSwap : (sampleIndexRange K >>= fun x =>
      sampleIndexRange M >>= fun y1 => sampleIndexRange M >>= fun y2 =>
        if decide (x < y1 + y2 + 1) = true then pT else pF) = _ := rfl
  rw [mul_evalDist_sampleIndexRange_bytes hK]
  have hInner : ∀ x ∈ Finset.range K,
      𝒟[sampleIndexRange M >>= fun y1 => sampleIndexRange M >>= fun y2 =>
          if decide (x < y1 + y2 + 1) = true then pT else pF] {z} =
        ∑ y1 ∈ Finset.range M,
          (∑ y2 ∈ Finset.range M,
            (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
            (M : ℝ≥0∞)⁻¹ := by
    intro x _
    rw [evalDist_sampleIndexRange_bind_bytes hM]
    refine Finset.sum_congr rfl fun y1 _ => congrArg (· * (M : ℝ≥0∞)⁻¹) ?_
    rw [evalDist_sampleIndexRange_bind_bytes hM]
    refine Finset.sum_congr rfl fun y2 _ => ?_
    by_cases hlt : x < y1 + y2 + 1 <;> simp [hlt]
  rw [Finset.sum_congr rfl hInner, Finset.sum_comm]
  have hSwap2 : (∑ y1 ∈ Finset.range M, ∑ x ∈ Finset.range K,
      (∑ y2 ∈ Finset.range M,
        (if x < y1 + y2 + 1 then 𝒟[pT] {z} else 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
        (M : ℝ≥0∞)⁻¹) =
      ∑ y1 ∈ Finset.range M,
        (∑ y2 ∈ Finset.range M,
          (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
            ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z}) * (M : ℝ≥0∞)⁻¹) *
          (M : ℝ≥0∞)⁻¹ := by
    refine Finset.sum_congr rfl fun y1 hy1 => ?_
    have hy1' : y1 < M := Finset.mem_range.mp hy1
    simp_rw [← Finset.sum_mul]
    congr 1
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y2 hy2 => ?_
    have hy2' : y2 < M := Finset.mem_range.mp hy2
    exact sum_range_lt_split' (y1 + y2 + 1) K (by omega) _ _
  rw [hSwap2]
  simp_rw [← Finset.sum_mul]
  have hSplit : (∑ y1 ∈ Finset.range M, ∑ y2 ∈ Finset.range M,
      (((y1 + y2 + 1 : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
        ((K - (y1 + y2 + 1) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z})) =
      ((M * M * M : ℕ) : ℝ≥0∞) * 𝒟[pT] {z} +
        ((M * M * (K - M) : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum]
    rw [sum_range_sq_add_one M, sum_range_sq_sub_add_one M K hMK]
  rw [hSplit]
  have hCancel : ∀ c : ℝ≥0∞,
      ((M : ℝ≥0∞) * (M : ℝ≥0∞) * c) * (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = c := by
    intro c
    rw [mul_comm ((M : ℝ≥0∞) * (M : ℝ≥0∞)) c, mul_assoc c,
      mul_assoc (M : ℝ≥0∞) (M : ℝ≥0∞) (M : ℝ≥0∞)⁻¹,
      ENNReal.mul_inv_cancel hM0 hMtop, mul_one, mul_assoc c,
      ENNReal.mul_inv_cancel hM0 hMtop, mul_one]
  simp only [Nat.cast_mul, add_mul]
  have hL : (M : ℝ≥0∞) * (M : ℝ≥0∞) * (M : ℝ≥0∞) * 𝒟[pT] {z} *
      (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = (M : ℝ≥0∞) * 𝒟[pT] {z} := by
    rw [mul_assoc ((M : ℝ≥0∞) * (M : ℝ≥0∞)) (M : ℝ≥0∞) (𝒟[pT] {z})]
    exact hCancel _
  have hR : (M : ℝ≥0∞) * (M : ℝ≥0∞) * ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} *
      (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞)⁻¹ = ((K - M : ℕ) : ℝ≥0∞) * 𝒟[pF] {z} := by
    rw [mul_assoc ((M : ℝ≥0∞) * (M : ℝ≥0∞)) (((K - M : ℕ) : ℝ≥0∞)) (𝒟[pF] {z})]
    exact hCancel _
  rw [hL, hR]

private theorem evalDist_bernoulliRatioProb_scaled {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (pT pF : ProbComp Bytes) (z : Bytes) :
    ((A + B : ℕ) : ℝ≥0∞) * 𝒟[bernoulliRatioProb A B >>= fun u =>
        if u = true then pT else pF] {z} =
      (A : ℝ≥0∞) * 𝒟[pT] {z} + (B : ℝ≥0∞) * 𝒟[pF] {z} := by
  have hA0 : A ≠ 0 := Nat.ne_of_gt hA
  have hB0 : B ≠ 0 := Nat.ne_of_gt hB
  unfold bernoulliRatioProb
  simp only [hA0, hB0, ↓reduceIte]
  by_cases hAB : A ≤ B
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    rw [evalDist_bernoulliCube_scaled hA (by omega), Nat.add_sub_cancel_left]
  · simp only [hAB, ↓reduceIte, bind_assoc, pure_bind]
    have hRew : (sampleIndexRange (A + B) >>= fun x =>
        sampleIndexRange B >>= fun y1 => sampleIndexRange B >>= fun y2 =>
          if (!decide (x < y1 + y2 + 1)) = true then pT else pF) =
        (sampleIndexRange (A + B) >>= fun x =>
          sampleIndexRange B >>= fun y1 => sampleIndexRange B >>= fun y2 =>
            if decide (x < y1 + y2 + 1) = true then pF else pT) := by
      refine bind_congr fun x => bind_congr fun y1 => bind_congr fun y2 => ?_
      cases decide (x < y1 + y2 + 1) <;> rfl
    rw [hRew, evalDist_bernoulliCube_scaled hB (by omega), Nat.add_sub_cancel_right, add_comm]

private theorem evalDist_sampleSpkPair2Prob_bind (S : Setup)
    (g : Option (Nat × Nat) → ProbComp Bytes) (z : Bytes) :
    𝒟[sampleSpkPair2Prob S >>= g] {z} =
      𝒟[sampleIndexRange S.N_spk_tot >>= fun sIdx => g (paSpkOpt S sIdx)] {z} := by
  unfold sampleSpkPair2Prob
  by_cases h0 : S.N_spk_tot = 0
  · simp [h0, sampleIndexRange, paSpkOpt]
  · simp only [h0, ↓reduceIte, bind_assoc, pure_bind]
    have hPos : 0 < S.N_id * S.N_recv := Nat.pos_of_ne_zero h0
    have hM : 0 < S.N_id := Nat.pos_of_mul_pos_right hPos
    have hN : 0 < S.N_recv := Nat.pos_of_mul_pos_left hPos
    change _ = 𝒟[sampleIndexRange (S.N_id * S.N_recv) >>= fun sIdx => g (paSpkOpt S sIdx)] {z}
    rw [evalDist_sampleIndexRange_bind_bytes hPos, evalDist_sampleIndexRange_bind_bytes hM]
    have hRew : ∑ sIdx ∈ Finset.range (S.N_id * S.N_recv),
        𝒟[g (paSpkOpt S sIdx)] {z} * ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞)⁻¹ =
        ∑ sIdx ∈ Finset.range (S.N_id * S.N_recv),
        𝒟[g (some (sIdx / S.N_recv, sIdx % S.N_recv))] {z} * ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl fun sIdx hs => ?_
      have hslt : sIdx < S.N_spk_tot := Finset.mem_range.mp hs
      simp [paSpkOpt, hslt]
    rw [hRew, sum_range_mul_div_mod_ennreal' S.N_id S.N_recv
      (fun u j => 𝒟[g (some (u, j))] {z} * ((S.N_id * S.N_recv : ℕ) : ℝ≥0∞)⁻¹)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [evalDist_sampleIndexRange_bind_bytes hN, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)))
      (.inl (ENNReal.natCast_ne_top S.N_id)), mul_assoc, mul_comm (S.N_id : ℝ≥0∞)⁻¹]

private def role2OfFlat (S : Setup) (flatIdx : Nat) : a1gRole2Ty.denote :=
  pa2RoleVal S (decide (flatIdx < S.N_id))
    (if flatIdx < S.N_id then flatIdx else flatIdx - S.N_id)

private theorem evalDist_sampleRole2Prob_bind (S : Setup)
    (g : a1gRole2Ty.denote → ProbComp Bytes) (z : Bytes) :
    𝒟[sampleRole2Prob S >>= g] {z} =
      𝒟[sampleIndexRange (S.N_id + S.N_send_tot) >>= fun idx => g (role2OfFlat S idx)] {z} := by
  unfold sampleRole2Prob
  by_cases hId : S.N_id = 0
  · have hOpk0 : S.N_send_opk_tot = 0 := by simp [Setup.N_send_opk_tot, hId]
    have hSend0 : S.N_send_tot = 0 := by
      simp [Setup.N_send_tot, Setup.N_send_no_opk_tot, hOpk0, hId]
    simp [hId, hOpk0, hSend0, sampleIndexRange, role2OfFlat, pa2RoleVal]
  · simp only [hId, ↓reduceIte, bind_assoc]
    have hPosId : 0 < S.N_id := Nat.pos_of_ne_zero hId
    let A := S.N_send_opk
    let B := S.N_send_no_opk
    let W := 1 + A + B
    have hPosW : 0 < W := by omega
    have hTotEq : S.N_id + S.N_send_tot = S.N_id + (S.N_id * A + S.N_id * B) := rfl
    have hTotMul : S.N_id + S.N_send_tot = S.N_id * W := by
      dsimp only [W, A, B]; rw [hTotEq]; ring
    have hPosTot : 0 < S.N_id + S.N_send_tot := by rw [hTotMul]; exact Nat.mul_pos hPosId hPosW
    rw [evalDist_sampleIndexRange_bind_bytes hPosId,
      evalDist_sampleIndexRange_bind_bytes hPosTot]
    have hInv : ((S.N_id + S.N_send_tot : ℕ) : ℝ≥0∞)⁻¹ =
        (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      rw [hTotMul, Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr hId))
        (.inl (ENNReal.natCast_ne_top S.N_id)), mul_comm]
    simp_rw [hInv, ← mul_assoc]
    conv_rhs => rw [hTotEq]
    rw [Finset.sum_range_add, Finset.sum_range_add]
    have hB1 : ∑ idx ∈ Finset.range S.N_id,
        𝒟[g (role2OfFlat S idx)] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
        ∑ uT ∈ Finset.range S.N_id,
          𝒟[g (.inl uT)] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl fun uT hu => ?_
      simp [role2OfFlat, pa2RoleVal, Finset.mem_range.mp hu]
    have hB2 : ∑ t ∈ Finset.range (S.N_id * A),
        𝒟[g (role2OfFlat S (S.N_id + t))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
        ∑ uT ∈ Finset.range S.N_id,
          (∑ i ∈ Finset.range A, 𝒟[g (.inr (.inl (uT, i)))] {z}) *
            (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      have hSub : ∑ t ∈ Finset.range (S.N_id * A),
          𝒟[g (role2OfFlat S (S.N_id + t))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
          ∑ t ∈ Finset.range (S.N_id * A),
            𝒟[g (.inr (.inl (t / A, t % A)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hlt : t < S.N_send_opk_tot := Finset.mem_range.mp ht
        have hge : ¬ (S.N_id + t < S.N_id) := by omega
        simp [role2OfFlat, pa2RoleVal, hge, hlt]; rfl
      rw [hSub, sum_range_mul_div_mod_ennreal' S.N_id A
        (fun uT i => 𝒟[g (.inr (.inl (uT, i)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹)]
      refine Finset.sum_congr rfl fun uT _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
    have hB3 : ∑ r ∈ Finset.range (S.N_id * B),
        𝒟[g (role2OfFlat S (S.N_id + (S.N_id * A + r)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
        ∑ uT ∈ Finset.range S.N_id,
          (∑ i ∈ Finset.range B, 𝒟[g (.inr (.inr (uT, i)))] {z}) *
            (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
      have hSub : ∑ r ∈ Finset.range (S.N_id * B),
          𝒟[g (role2OfFlat S (S.N_id + (S.N_id * A + r)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ =
          ∑ r ∈ Finset.range (S.N_id * B),
            𝒟[g (.inr (.inr (r / B, r % B)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hlt : r < S.N_send_no_opk_tot := Finset.mem_range.mp hr
        have hge1 : ¬ (S.N_id + (S.N_id * A + r) < S.N_id) := by omega
        have hsub1 : S.N_id + (S.N_id * A + r) - S.N_id = S.N_send_opk_tot + r := by
          change S.N_id + (S.N_send_opk_tot + r) - S.N_id = _; omega
        have hge2 : ¬ (S.N_send_opk_tot + r < S.N_send_opk_tot) := by omega
        have hlt2 : S.N_send_opk_tot + r < S.N_send_tot := by
          unfold Setup.N_send_tot; omega
        simp [role2OfFlat, pa2RoleVal, hge1, hsub1, hge2, hlt2]; rfl
      rw [hSub, sum_range_mul_div_mod_ennreal' S.N_id B
        (fun uT i => 𝒟[g (.inr (.inr (uT, i)))] {z} * (W : ℝ≥0∞)⁻¹ * (S.N_id : ℝ≥0∞)⁻¹)]
      refine Finset.sum_congr rfl fun uT _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [hB1, hB2, hB3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun uT _ => ?_
    rw [evalDist_sampleIndexRange_bind_bytes hPosW]
    have hW : W = (A + B) + 1 := by dsimp only [W]; omega
    conv_lhs => arg 1; arg 1; rw [hW]
    rw [Finset.sum_range_succ']
    simp only [beq_self_eq_true, ↓reduceIte, pure_bind, Nat.succ_ne_zero, beq_iff_eq,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hBr : ((A + B : ℕ) : ℝ≥0∞) * 𝒟[(if S.N_send_opk_tot = 0 then
          if S.N_send_no_opk_tot = 0 then pure (.inr (.inl (0, 0)))
          else sampleIndexRange B >>= fun iT => pure (.inr (.inr (uT, iT)))
        else if S.N_send_no_opk_tot = 0 then
          sampleIndexRange A >>= fun iT => pure (.inr (.inl (uT, iT)))
        else bernoulliRatioProb A B >>= fun useOpk =>
          if useOpk = true then sampleIndexRange A >>= fun iT => pure (.inr (.inl (uT, iT)))
          else sampleIndexRange B >>= fun iT => pure (.inr (.inr (uT, iT)))) >>= g] {z} =
        (∑ i ∈ Finset.range A, 𝒟[g (.inr (.inl (uT, i)))] {z}) +
          (∑ i ∈ Finset.range B, 𝒟[g (.inr (.inr (uT, i)))] {z}) := by
      by_cases hOpk0 : S.N_send_opk_tot = 0
      · have hA0 : A = 0 := (Nat.mul_eq_zero.mp hOpk0).resolve_left hId
        by_cases hNoOpk0 : S.N_send_no_opk_tot = 0
        · have hB0 : B = 0 := (Nat.mul_eq_zero.mp hNoOpk0).resolve_left hId
          simp [hOpk0, hNoOpk0, hA0, hB0]
        · have hBPos : 0 < B := Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hNoOpk0)
          simp only [hOpk0, hNoOpk0, ↓reduceIte, hA0, bind_assoc, pure_bind,
            Finset.range_zero, Finset.sum_empty, zero_add]
          exact mul_evalDist_sampleIndexRange_bytes hBPos _ z
      · have hAPos : 0 < A := Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hOpk0)
        by_cases hNoOpk0 : S.N_send_no_opk_tot = 0
        · have hB0 : B = 0 := (Nat.mul_eq_zero.mp hNoOpk0).resolve_left hId
          simp only [hOpk0, hNoOpk0, ↓reduceIte, hB0, bind_assoc, pure_bind,
            Finset.range_zero, Finset.sum_empty, add_zero]
          exact mul_evalDist_sampleIndexRange_bytes hAPos _ z
        · have hBPos : 0 < B := Nat.pos_of_mul_pos_left (Nat.pos_of_ne_zero hNoOpk0)
          simp only [hOpk0, hNoOpk0, ↓reduceIte]
          have hBind : ((bernoulliRatioProb A B >>= fun useOpk =>
              if useOpk = true then sampleIndexRange A >>= fun iT => pure (.inr (.inl (uT, iT)))
              else sampleIndexRange B >>= fun iT => pure (.inr (.inr (uT, iT)))) >>= g) =
              (bernoulliRatioProb A B >>= fun useOpk =>
                if useOpk = true then sampleIndexRange A >>= fun iT => g (.inr (.inl (uT, iT)))
                else sampleIndexRange B >>= fun iT => g (.inr (.inr (uT, iT)))) := by
            rw [bind_assoc]
            refine bind_congr fun useOpk => ?_
            cases useOpk <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          rw [hBind, evalDist_bernoulliRatioProb_scaled hAPos hBPos,
            mul_evalDist_sampleIndexRange_bytes hAPos, mul_evalDist_sampleIndexRange_bytes hBPos]
    rw [← mul_assoc (((A + B : ℕ) : ℝ≥0∞)), hBr]
    ring

end DistHelpers

/-- Evaluating `fgAuth1KeyGapDhProg` against a bounded `Auth` adversary induces the same output
    distribution as `fgAuth1KeyGapDhAdv4` under any primitive and challenger implementations. -/
theorem fgAuth1KeyGapDhProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes)
    (primImpl0 : QueryImpl primSpec ProbComp)
    (chalImpl : QueryImpl sigAndDdhSpec ProbComp) :
    𝒟[simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl)
        ((fgAuth1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V))] =
      𝒟[simulateQ ((QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl)
        ((fgAuth1KeyGapDhAdv4 S b A).run U V)] := by
  let impl := (QueryImpl.ofLift unifSpec ProbComp + primImpl0) + chalImpl
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1
    funext q; cases q <;> rfl
  let runAt (role : a1gRole2Ty.denote) (spk : Option (Nat × Nat)) : ProbComp Bytes :=
    ($ᵗ Bool) >>= fun secb =>
      simulateQ impl
        (((simulateQ (handlerImpl (C := authCodec S) (a1g2HandleDsl S b.q_total)) A.1.run).run
            (a1g2StToVal S b.q_total (U, (V, (role, spk))) (FgAuth1KeySimState.empty S secb))) >>=
          fun p => (a1g2FinishDsl S b.q_total).eval (.cons p.2 (.cons p.1 .nil)))
  have hDsl : simulateQ impl ((fgAuth1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)) =
      (sampleRole2Prob S >>= fun role => sampleSpkPair2Prob S >>= fun spk => runAt role spk) := by
    unfold CostedReduction.eval CostedReduction.impl
    dsimp only [fgAuth1KeyGapDhProg]
    rw [a1g2InitDsl_eval]
    simp only [bind_assoc, pure_bind]
    rw [simulateQ_bind, simulateQ_unifGdhSign]
    refine bind_congr fun role => ?_
    rw [simulateQ_bind, simulateQ_unifGdhSign]
    refine bind_congr fun spk => ?_
    rw [simulateQ_bind, simulateQ_unifGdhSign]; rfl
  have hSh : simulateQ impl ((fgAuth1KeyGapDhAdv4 S b A).run U V) =
      (sampleIndexRange (S.N_id + S.N_send_tot) >>= fun flatIdx =>
        sampleIndexRange S.N_spk_tot >>= fun bIdx =>
          runAt (role2OfFlat S flatIdx) (paSpkOpt S bIdx)) := by
    dsimp only [fgAuth1KeyGapDhAdv4]
    rw [simulateQ_bind, simulateQ_unifGdhSign]
    simp only [sampleIndexRange2, bind_assoc, pure_bind]
    refine bind_congr fun flatIdx => bind_congr fun bIdx => ?_
    by_cases h : flatIdx < S.N_id
    · simp only [h, decide_true, ↓reduceIte, role2OfFlat, fgAuth1KeyGapDhRunAt]
      rw [simulateQ_bind, simulateQ_unifGdhSign]
      refine bind_congr fun secb => congrArg (simulateQ impl) ?_
      exact (a1g2Run_eq S b.q_total U V true flatIdx bIdx A.1.run hA secb).symm
    · simp only [h, decide_false, ↓reduceIte, role2OfFlat, fgAuth1KeyGapDhRunAt]
      rw [simulateQ_bind, simulateQ_unifGdhSign]
      refine bind_congr fun secb => congrArg (simulateQ impl) ?_
      exact (a1g2Run_eq S b.q_total U V false (flatIdx - S.N_id) bIdx A.1.run hA secb).symm
  rw [hDsl, hSh]
  refine MeasureTheory.Measure.ext_of_singleton fun w => ?_
  rw [evalDist_sampleRole2Prob_bind S (fun role => sampleSpkPair2Prob S >>= fun spk => runAt role spk) w]
  by_cases hTot0 : S.N_id + S.N_send_tot = 0
  · simp only [hTot0, sampleIndexRange, lt_self_iff_false, ↓reduceDIte, pure_bind]
    exact evalDist_sampleSpkPair2Prob_bind S (fun spk => runAt (role2OfFlat S 0) spk) w
  · have hPos : 0 < S.N_id + S.N_send_tot := Nat.pos_of_ne_zero hTot0
    rw [evalDist_sampleIndexRange_bind_bytes hPos, evalDist_sampleIndexRange_bind_bytes hPos]
    refine Finset.sum_congr rfl fun flatIdx _ => ?_
    exact congrArg (· * _)
      (evalDist_sampleSpkPair2Prob_bind S (fun spk => runAt (role2OfFlat S flatIdx) spk) w)

end SignalPqxdh.Security.ReductionDsl.AuthHs
