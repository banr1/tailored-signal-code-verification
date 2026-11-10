/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval
import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyPre
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhSessionSplit

/-!
# Cost and Query Bounds for `fgKeyInd1KeyGapDhDslAdv`

**Checked by Lean.** Packages the one-key `KeyInd` `ReductionDsl` reduction as a `GapDhWithSignAdv`
(`fgKeyInd1KeyGapDhDslAdv`) and establishes its step-cost bound, semantic query-budget compliance,
advantage equality with `fgKeyInd1KeyGapDhAdv4`, and the imperfect-correctness `G3 -> G3.5` bound.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

open SignalPqxdh.Security.ReductionDsl.KeyInd
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

/-- The `ReductionDsl` program instantiated at `K = b.q_total` for one-key `KeyInd` `GapDhWithSign`. -/
abbrev fgKeyInd1KeyGapDhDslProg (S : Setup) (b : QueryBudget) :=
  fgKeyInd1KeyGapDh2Prog S b.q_total

/-- The `ReductionDsl` one-key `KeyInd` reduction packaged as a `GapDhWithSignAdv`. -/
def fgKeyInd1KeyGapDhDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := (fgKeyInd1KeyGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

/-- Step-cost bound for `fgKeyInd1KeyGapDhProg` against `stepCostBudget`. -/
theorem fgKeyInd1KeyGapDhProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b :=
  (fgKeyInd1KeyGapDhProg_totalCost_le S b).trans (securityStepCostBudget_le_legacy S b)

/-- Declared query budgets of `fgKeyInd1KeyGapDhDslAdv` satisfy `KeyIndReductionQueryBounds`. -/
theorem fgKeyInd1KeyGapDhDslAdv_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyInd1KeyGapDhDslAdv S b A).q_ddh ≤ gdhQueryBudget S b ∧
    (fgKeyInd1KeyGapDhDslAdv S b A).q_sig ≤ 2 * min S.N_spk_tot S.N_recv ∧
    (fgKeyInd1KeyGapDhDslAdv S b A).q_prim ≤ primQueryBudget S b :=
  ⟨le_rfl, le_rfl, gdhPrimQueryBudget_le_primQueryBudget S b⟩

section TupleKeyedSyntactic

private theorem tk_bernoulliRatioGdhC_ddh {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries wDdhGdh wsZero = 0 := by
  unfold bernoulliRatioGdhC; split_ifs <;> simp [bindV_queries, gPrim_queries_wDdhGdh, Comp.queries]

private theorem tk_bernoulliRatioGdhC_prim {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries wPrimGdh wsZero = 0 := by
  unfold bernoulliRatioGdhC; split_ifs <;> simp [bindV_queries, gPrim_queries_wPrimGdh, sIndex_queries, Comp.queries]

private theorem tk_chooseArm2C_ddh {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT} (A B : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries wDdhGdh wsZero = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries wDdhGdh wsZero = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) A B c1 c2).queries wDdhGdh wsZero = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [bindV_queries, Comp.queries, tk_bernoulliRatioGdhC_ddh, h1, h2]

private theorem tk_chooseArm2C_prim {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT} (A B : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries wPrimGdh wsZero = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries wPrimGdh wsZero = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) A B c1 c2).queries wPrimGdh wsZero = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [bindV_queries, Comp.queries, tk_bernoulliRatioGdhC_prim, h1, h2]

private theorem tk_initParams1Key2C_ddh (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1Key2C S (Δ := Δ) uv).queries wDdhGdh wsZero = 0 := by
  have hp : ∀ {Δ' : List PT}, (samplePrin2C S (Δ := Δ')).queries wDdhGdh wsZero = 0 := by
    intro Δ'; unfold samplePrin2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wDdhGdh, Comp.queries]
  have hs : ∀ {Δ' : List PT}, (sampleSpkPair2C S (Δ := Δ')).queries wDdhGdh wsZero = 0 := by
    intro Δ'; unfold sampleSpkPair2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wDdhGdh, Comp.queries]
  have ho : ∀ {Δ' : List PT}, (sampleOpkTriple2C S (Δ := Δ')).queries wDdhGdh wsZero = 0 := by
    intro Δ'; unfold sampleOpkTriple2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wDdhGdh, Comp.queries]
  have hso : ∀ {Δ' : List PT}, (sampleSendOpkTarget2C S (Δ := Δ')).queries wDdhGdh wsZero = 0 := by
    intro Δ'; unfold sampleSendOpkTarget2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wDdhGdh, Comp.queries]
  have hsno : ∀ {Δ' : List PT}, (sampleSendNoOpkTarget2C S (Δ := Δ')).queries wDdhGdh wsZero = 0 := by
    intro Δ'; unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wDdhGdh, Comp.queries]
  have hst : ∀ {Δ' : List PT}, (sampleSendTarget2C S (Δ := Δ')).queries wDdhGdh wsZero = 0 := by
    intro Δ'; unfold sampleSendTarget2C; split_ifs
    · rfl
    · exact tk_chooseArm2C_ddh (Γ₁ := Δ') _ _ _ _ (fun {_} [_] => hso) (fun {_} [_] => hsno)
  unfold initParams1Key2C
  split_ifs
  · rfl
  · refine tk_chooseArm2C_ddh _ _ _ _ ?_ ?_
    · intro Δ' _; refine tk_chooseArm2C_ddh _ _ _ _ ?_ ?_ <;> (intro Δ'' _; simp [bindV_queries, Comp.queries, hp, hs, hst])
    · intro Δ' _; refine tk_chooseArm2C_ddh _ _ _ _ ?_ ?_ <;> (intro Δ'' _; simp [bindV_queries, Comp.queries, hp, hst, hso, ho])

private theorem tk_initParams1Key2C_prim (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1Key2C S (Δ := Δ) uv).queries wPrimGdh wsZero = 0 := by
  have hp : ∀ {Δ' : List PT}, (samplePrin2C S (Δ := Δ')).queries wPrimGdh wsZero = 0 := by
    intro Δ'; unfold samplePrin2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wPrimGdh, sIndex_queries, Comp.queries]
  have hs : ∀ {Δ' : List PT}, (sampleSpkPair2C S (Δ := Δ')).queries wPrimGdh wsZero = 0 := by
    intro Δ'; unfold sampleSpkPair2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wPrimGdh, sIndex_queries, Comp.queries]
  have ho : ∀ {Δ' : List PT}, (sampleOpkTriple2C S (Δ := Δ')).queries wPrimGdh wsZero = 0 := by
    intro Δ'; unfold sampleOpkTriple2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wPrimGdh, sIndex_queries, Comp.queries]
  have hso : ∀ {Δ' : List PT}, (sampleSendOpkTarget2C S (Δ := Δ')).queries wPrimGdh wsZero = 0 := by
    intro Δ'; unfold sampleSendOpkTarget2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wPrimGdh, sIndex_queries, Comp.queries]
  have hsno : ∀ {Δ' : List PT}, (sampleSendNoOpkTarget2C S (Δ := Δ')).queries wPrimGdh wsZero = 0 := by
    intro Δ'; unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [bindV_queries, gPrim_queries_wPrimGdh, sIndex_queries, Comp.queries]
  have hst : ∀ {Δ' : List PT}, (sampleSendTarget2C S (Δ := Δ')).queries wPrimGdh wsZero = 0 := by
    intro Δ'; unfold sampleSendTarget2C; split_ifs
    · rfl
    · exact tk_chooseArm2C_prim (Γ₁ := Δ') _ _ _ _ (fun {_} [_] => hso) (fun {_} [_] => hsno)
  unfold initParams1Key2C
  split_ifs
  · rfl
  · refine tk_chooseArm2C_prim _ _ _ _ ?_ ?_
    · intro Δ' _; refine tk_chooseArm2C_prim _ _ _ _ ?_ ?_ <;> (intro Δ'' _; simp [bindV_queries, Comp.queries, hp, hs, hst])
    · intro Δ' _; refine tk_chooseArm2C_prim _ _ _ _ ?_ ?_ <;> (intro Δ'' _; simp [bindV_queries, Comp.queries, hp, hst, hso, ho])

theorem fgKeyInd1KeyGapDh2Prog_init_queries_sig (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).init.queries wSig1Key wsZero1Key = 0 := by
  simp [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, bindV_queries, liftGdhComp_queries_sig, Comp.queries]

theorem fgKeyInd1KeyGapDh2Prog_init_queries_ddh (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).init.queries wDdh1Key wsZero1Key = 0 := by
  simp [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base,
    letV_queries, bindV_queries, liftGdhComp_queries_ddh, tk_initParams1Key2C_ddh,
    gPrim_queries_wDdhGdh, Comp.queries]

theorem fgKeyInd1KeyGapDh2Prog_init_queries_prim (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).init.queries wPrim1Key wsZero1Key = 0 := by
  simp [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base,
    letV_queries, bindV_queries, liftGdhComp_queries_prim, tk_initParams1Key2C_prim,
    gPrim_queries_wPrimGdh, sBool_queries, Comp.queries]

private theorem tk_wrapBase2_ddh {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries wDdhGdh wsZero = (gPrim c).queries wDdhGdh wsZero := by
  simp [wrapBase2, bindV_queries, Comp.queries]

private theorem tk_wrapSim2_ddh {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries wDdhGdh wsZero = c.queries wDdhGdh wsZero := by
  simp [wrapSim2, bindV_queries, Comp.queries]

private theorem tk_wrapBase2_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queriesUB wPrimGdh wsZero = (gPrim c).queriesUB wPrimGdh wsZero := by
  simp [wrapBase2, bindV_queriesUB, Comp.queriesUB]

private theorem tk_wrapSim2_primUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimGdh wsZero := by
  simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]

private theorem tk_wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem tk_wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

private theorem tk_gdhHandle2_ddh (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wDdhGdh wsZero = 4 * K := by
  simp [gdhHandle2, initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B,
    finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB, roParsedC, roRawFallbackC,
    registerGdhB, tk_wrapBase2_ddh, tk_wrapSim2_ddh, Comp.queries]

private theorem tk_gdhFinish2_ddh (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries wDdhGdh wsZero = K + min K S.N_dh + min K S.N_sess_tot := by
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV_queries, bindV_queries, caseOptV_queries,
    findMV_queries, mapMV_queries, foldMV_queries, ddhQ_queries_wDdhGdh,
    gPrim_queries_wDdhGdh, Comp.queries, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero, Nat.zero_add, Nat.max_zero, max_self]
  omega

private theorem tk_gdhHandle2_prim_le (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wPrimGdh wsZero ≤ 153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh wsZero (gdhHandle2 S K)
  have hUB : (gdhHandle2 S K).queriesUB wPrimGdh wsZero =
      153 + 72 * min K S.N_dh + 16 * min K S.N_sess_tot := by
    simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
      initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
      testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
      tk_wrapBase2_primUB, tk_wrapSim2_primUB,
      letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
      gPrim_queriesUB_wPrimGdh, koskBundleOkPowsC_primUB, koskSenderOkPowsC_primUB,
      resolveSigPkC_primUB, lookupSpkSkC_primUB, honestPeerC_primUB, checkProvC_primUB,
      findHonestC_primUB, chooseInitRandC_primUB, chooseRespRandC_primUB,
      computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, fgPatchC_primUB,
      sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
      qX25519_queriesUB, qX25519Base_queriesUB, qIsCanonical_queriesUB, qPow8_queriesUB,
      qSigPkGen_queriesUB, qSigSign_queriesUB, qSigVerify_queriesUB,
      qKemKeyGen_queriesUB, qKemEncaps_queriesUB, qKemDecaps_queriesUB,
      Comp.queriesUB]
    ring
  rw [hUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

private theorem tk_gdhFinish2_prim_le (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries wPrimGdh wsZero ≤ 3 * S.N_dh + S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh wsZero (gdhFinish2 S K)
  have hUB : (gdhFinish2 S K).queriesUB wPrimGdh wsZero =
      3 * min K S.N_dh + min K S.N_sess_tot := by
    simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
      initDh1CandC, respDh1CandC, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB,
      findMV_queriesUB, mapMV_queriesUB, foldMV_queriesUB,
      ddhQ_queriesUB_wPrimGdh, gPrim_queriesUB_wPrimGdh,
      qPow8_queriesUB, qX25519_queriesUB, Comp.queriesUB]
    ring
  rw [hUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

private theorem tk_callGdhHandle2_sig (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle2 S K st1 q).queries wSig1Key wsZero1Key = 0 := by
  simp [callGdhHandle2, letV_queries, bindV_queries, renameComp_queries,
    liftGdhComp_queries_sig, Comp.queries]

private theorem tk_callGdhHandle2_ddh (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle2 S K st1 q).queries wDdh1Key wsZero1Key = 4 * K := by
  simp [callGdhHandle2, letV_queries, bindV_queries, renameComp_queries,
    liftGdhComp_queries_ddh, tk_gdhHandle2_ddh, Comp.queries]

private theorem tk_callGdhHandle2_prim_le (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle2 S K st1 q).queries wPrim1Key wsZero1Key ≤
      153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  simp only [callGdhHandle2, letV_queries, bindV_queries, renameComp_queries,
    liftGdhComp_queries_prim, Comp.queries, Nat.add_zero]
  exact tk_gdhHandle2_prim_le S K

private theorem tk_gdh1KeyHandle2_sig (S : Setup) (K : Nat) :
    (gdh1KeyHandle2 S K).queries wSig1Key wsZero1Key = 2 := by
  simp [gdh1KeyHandle2, initPrin1Key2B, genSpk1Key2B, tk_callGdhHandle2_sig,
    letV_queries, bindV_queries, caseOptV_queries, caseSumV_queries,
    liftGdhComp_queries_sig, sigChalQ_dsl_queries_sig, Comp.queries]

private theorem tk_gdh1KeyHandle2_ddh (S : Setup) (K : Nat) :
    (gdh1KeyHandle2 S K).queries wDdh1Key wsZero1Key = 4 * K := by
  simp [gdh1KeyHandle2, initPrin1Key2B, genSpk1Key2B, tk_callGdhHandle2_ddh,
    letV_queries, bindV_queries, caseOptV_queries, caseSumV_queries,
    liftGdhComp_queries_ddh, gPrim_queries_wDdhGdh, sigChalQ_dsl_queries_ddh, Comp.queries]

private theorem tk_gdh1KeyHandle2_prim_le (S : Setup) (K : Nat) :
    (gdh1KeyHandle2 S K).queries wPrim1Key wsZero1Key ≤
      153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have hIp : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st1 : Var Γ₁ gdh1KeyState2Ty) (u : Var Γ₂ .nat),
      (initPrin1Key2B K (Δ := Δ) st1 u).queries wPrim1Key wsZero1Key ≤ 1 := by
    intro Γ₁ Γ₂ Δ _ _ st1 u
    simp [initPrin1Key2B, letV_queries, bindV_queries, liftGdhComp_queries_prim,
      gPrim_queries_wPrimGdh, sBytes32_queries, qX25519Base_queries, Comp.queries]
  have hGs : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy)
      (x : Var Δ (.prod .nat .nat)),
      (genSpk1Key2B S K st1 q x).queries wPrim1Key wsZero1Key ≤
        153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
    intro Δ st1 q x
    have hc := tk_callGdhHandle2_prim_le S K st1 q
    simp only [genSpk1Key2B, letV_queries, bindV_queries, caseOptV_queries,
      liftGdhComp_queries_prim, gPrim_queries_wPrimGdh, sigChalQ_dsl_queries_prim,
      sBytes32_queries, sRandom64_queries, qX25519Base_queries, qKemKeyGen_queries,
      Comp.queries]
    omega
  unfold gdh1KeyHandle2
  simp only [caseSumV_queries]
  exact max_le ((hIp _ _).trans (by omega))
    (max_le (tk_callGdhHandle2_prim_le S K _ _)
      (max_le (hGs _ _ _) (tk_callGdhHandle2_prim_le S K _ _)))

private theorem tk_gdh1KeyFinish2_sig (S : Setup) (K : Nat) :
    (gdh1KeyFinish2 S K).queries wSig1Key wsZero1Key = 0 := by
  simp [gdh1KeyFinish2, letV_queries, renameComp_queries, liftGdhComp_queries_sig]

private theorem tk_gdh1KeyFinish2_ddh (S : Setup) (K : Nat) :
    (gdh1KeyFinish2 S K).queries wDdh1Key wsZero1Key = K + min K S.N_dh + min K S.N_sess_tot := by
  simp [gdh1KeyFinish2, letV_queries, renameComp_queries, liftGdhComp_queries_ddh, tk_gdhFinish2_ddh]

private theorem tk_gdh1KeyFinish2_prim_le (S : Setup) (K : Nat) :
    (gdh1KeyFinish2 S K).queries wPrim1Key wsZero1Key ≤ 3 * S.N_dh + S.N_sess_tot := by
  simp only [gdh1KeyFinish2, letV_queries, renameComp_queries, liftGdhComp_queries_prim]
  exact tk_gdhFinish2_prim_le S K

theorem fgKeyInd1KeyGapDh2Prog_totalSigQueries_eq (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q = 2 * q := by
  change (fgKeyInd1KeyGapDh2Prog S K).totalQueries wSig1Key wsZero1Key q = 2 * q
  simp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDh2Prog_init_queries_sig]
  change 0 + q * (gdh1KeyHandle2 S K).queries wSig1Key wsZero1Key +
    (gdh1KeyFinish2 S K).queries wSig1Key wsZero1Key = _
  rw [tk_gdh1KeyHandle2_sig, tk_gdh1KeyFinish2_sig]
  ring

theorem fgKeyInd1KeyGapDh2Prog_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDh2Prog S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  rw [fgKeyInd1KeyGapDh2Prog_totalSigQueries_eq]

theorem fgKeyInd1KeyGapDh2Prog_totalDdhQueries_eq (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q =
      4 * q * K + K + min K S.N_dh + min K S.N_sess_tot := by
  change (fgKeyInd1KeyGapDh2Prog S K).totalQueries wDdh1Key wsZero1Key q = _
  simp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDh2Prog_init_queries_ddh]
  change 0 + q * (gdh1KeyHandle2 S K).queries wDdh1Key wsZero1Key +
    (gdh1KeyFinish2 S K).queries wDdh1Key wsZero1Key = _
  rw [tk_gdh1KeyHandle2_ddh, tk_gdh1KeyFinish2_ddh]
  ring

theorem fgKeyInd1KeyGapDh2Prog_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDh2Prog S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  rw [fgKeyInd1KeyGapDh2Prog_totalDdhQueries_eq, ← fgKeyIndGapDhProg_totalChalQueries_eq]
  exact fgKeyIndGapDhProg_totalChalQueries_le S b

theorem fgKeyInd1KeyGapDh2Prog_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDh2Prog S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  have hp : (fgKeyInd1KeyGapDh2Prog S b.q_total).totalQueries wPrim1Key wsZero1Key b.q_total ≤
      b.q_total * (153 + 72 * S.N_dh + 16 * S.N_sess_tot) + 3 * S.N_dh + S.N_sess_tot := by
    simp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDh2Prog_init_queries_prim]
    have hH := Nat.mul_le_mul_left b.q_total (tk_gdh1KeyHandle2_prim_le S b.q_total)
    have hF := tk_gdh1KeyFinish2_prim_le S b.q_total
    change 0 + b.q_total * (gdh1KeyHandle2 S b.q_total).queries wPrim1Key wsZero1Key +
      (gdh1KeyFinish2 S b.q_total).queries wPrim1Key wsZero1Key ≤ _
    omega
  change (fgKeyInd1KeyGapDh2Prog S b.q_total).totalQueries wPrim1Key wsZero1Key b.q_total ≤ _
  unfold primQueryBudget
  nlinarith

private theorem tk_bernoulliRatioGdhC_costUB_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).costUB ≤
      if A = 0 ∨ B = 0 then 2 else 3 * bits (A + B) + 25 := by
  unfold bernoulliRatioGdhC
  by_cases hA : A = 0
  · simp [hA, Comp.costUB, Expr.costUB]
  by_cases hB : B = 0
  · simp [hA, hB, Comp.costUB, Expr.costUB]
  simp only [hA, hB, or_self, ↓reduceIte]
  split_ifs
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : bits A ≤ bits (A + B) := bits_mono (by omega)
    omega
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : bits B ≤ bits (A + B) := bits_mono (by omega)
    omega

private theorem tk_chooseArm2C_costUB_le {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT} (A B : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    {M1 M2 : Nat} (_hN : A + B ≠ 0)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).costUB ≤ M1)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).costUB ≤ M2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) A B c1 c2).costUB ≤
      3 * bits (A + B) + M1 + M2 + 30 := by
  rw [chooseArm2C]
  by_cases hw1 : A = 0
  · simp only [hw1, ↓reduceIte]; exact h2.trans (by omega)
  · by_cases hw2 : B = 0
    · simp only [hw1, hw2, ↓reduceIte]; exact h1.trans (by omega)
    · simp only [hw1, hw2, ↓reduceIte, bindV_costUB, v_costUB, Comp.costUB]
      have hb := tk_bernoulliRatioGdhC_costUB_le (Δ := Δ) A B
      simp only [hw1, hw2, or_self, ↓reduceIte] at hb
      have hc1 := h1 (Δ' := .bool :: Δ); have hc2 := h2 (Δ' := .bool :: Δ); omega

private theorem tk_coordSamplers2_costUB_le (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).costUB ≤ bits S.N_dh + 10 ∧
    (sampleSpkPair2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 15 ∧
    (sampleOpkTriple2C S (Δ := Δ)).costUB ≤ 3 * bits S.N_dh + 20 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 20 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 20 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C; split_ifs
    · simp [Comp.costUB, Expr.costUB]
    · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega); omega
  · unfold sampleSpkPair2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_recv) (b := S.N_dh) (by omega); omega
  · unfold sampleOpkTriple2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hSpk : 0 < S.N_spk_tot := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_opk_tot, hc])
      have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => Nat.ne_of_gt hSpk (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      have hO : S.N_opk ≤ S.N_opk_tot := Nat.le_mul_of_pos_left _ hSpk
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_recv) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_opk) (b := S.N_dh) (by omega); omega
  · unfold sampleSendOpkTarget2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_opk_tot, hc])
      have hS : S.N_send_opk ≤ S.N_send_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_send_opk) (b := S.N_dh) (by omega); omega
  · unfold sampleSendNoOpkTarget2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_no_opk_tot, hc])
      have hS : S.N_send_no_opk ≤ S.N_send_no_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_send_no_opk_tot) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_send_no_opk) (b := S.N_dh) (by omega); omega

private theorem tk_sampleSendTarget2C_costUB_le (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).costUB ≤ 7 * bits S.N_dh + 70 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  unfold sampleSendTarget2C; split_ifs with h0
  · simp [Comp.costUB, Expr.costUB]
  · have hb := tk_chooseArm2C_costUB_le (Γ₁ := Δ) (Δ := Δ) S.N_send_opk_tot S.N_send_no_opk_tot
      _ _ (by omega) (fun {Δ'} [_] => (tk_coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (tk_coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.2)
    have bm : bits (S.N_send_opk_tot + S.N_send_no_opk_tot) ≤ bits S.N_dh := bits_mono (by omega)
    omega

private theorem tk_fgKeyInd1KeyGapDh2Prog_init_cost_le (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).init.cost ≤ 45 * bits S.N_dh + K + 650 := by
  refine le_trans (fgKeyInd1KeyGapDh2Prog S K).init.cost_le_costUB ?_
  have hfg : fgTotalIndexCount S =
      S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsq : ∀ x, x ≤ S.N_dh * S.N_dh → bits x ≤ 2 * bits S.N_dh + 1 := fun x hx =>
    le_trans (bits_mono hx) (by have hm := bits_mul S.N_dh S.N_dh; omega)
  have hInitP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams1Key2C S (Δ := Δ) uv).costUB ≤ 45 * bits S.N_dh + 480 := by
    intro Γ₁ Δ _ uv; unfold initParams1Key2C; split_ifs with h0
    · simp only [pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_0, bits_3]; omega
    · refine (tk_chooseArm2C_costUB_le _ _ _ _
        (M1 := 18 * bits S.N_dh + 210) (M2 := 19 * bits S.N_dh + 220) (by omega) ?_ ?_).trans ?_
      · intro Δ₁ _
        by_cases hAC : S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot = 0
        · have hA0 : S.N_id * S.N_spk_tot = 0 := by omega
          simp only [chooseArm2C, hA0, ↓reduceIte, bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_1]
          have h1 := tk_sampleSendTarget2C_costUB_le S (Δ := Δ₁)
          have h2 := (tk_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₁)).2.1; omega
        · refine (tk_chooseArm2C_costUB_le _ _ _ _
            (M1 := 3 * bits S.N_dh + 55) (M2 := 9 * bits S.N_dh + 115) hAC ?_ ?_).trans ?_
          · intro Δ₂ _; simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_0]
            have h1 := (tk_coordSamplers2_costUB_le S (Δ := Δ₂)).1
            have h2 := (tk_coordSamplers2_costUB_le S (Δ := .opt .nat :: Δ₂)).2.1; omega
          · intro Δ₂ _; simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_1]
            have h1 := tk_sampleSendTarget2C_costUB_le S (Δ := Δ₂)
            have h2 := (tk_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₂)).2.1; omega
          · have bsum := hsq (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (by nlinarith); omega
      · intro Δ₁ _
        by_cases hBD : S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot = 0
        · have hB0 : S.N_send_tot * S.N_id = 0 := by omega
          simp only [chooseArm2C, hB0, ↓reduceIte, bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_3]
          have h1 := (tk_coordSamplers2_costUB_le S (Δ := Δ₁)).2.2.2.1
          have h2 := (tk_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₁)).2.2.1; omega
        · refine (tk_chooseArm2C_costUB_le _ _ _ _
            (M1 := 8 * bits S.N_dh + 110) (M2 := 5 * bits S.N_dh + 70) hBD ?_ ?_).trans ?_
          · intro Δ₂ _; simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_2]
            have h1 := tk_sampleSendTarget2C_costUB_le S (Δ := Δ₂)
            have h2 := (tk_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₂)).1; omega
          · intro Δ₂ _; simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_3]
            have h1 := (tk_coordSamplers2_costUB_le S (Δ := Δ₂)).2.2.2.1
            have h2 := (tk_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₂)).2.2.1; omega
          · have bsum := hsq (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot)
              (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)]); omega
      · have bsum := hsq
          (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
            (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot))
          (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)]); omega
  simp only [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base, emptySimE, smMk, emptyStE, stMk,
    letV_costUB, bindV_costUB, liftGdhComp_costUB, gPrim_costUB, sBool_costUB, v_costUB, Comp.costUB, Expr.costUB]
  have hp := hInitP (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
  have hbK : bits (min K (min S.N_spk_tot S.N_recv)) ≤ K + 1 :=
    (bits_mono (Nat.min_le_left _ _)).trans (bits_le_succ K)
  omega

private theorem tk_gdh1KeyHandle2_cost_le_min (S : Setup) (K : Nat) :
    (gdh1KeyHandle2 S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62050 := by
  have hCall : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy),
      (callGdhHandle2 S K st1 q).cost ≤
        28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62020 := by
    intro Δ st1 q
    have hEq : (callGdhHandle2 S K st1 q).cost = (gdhHandle2 S K).cost + 14 := by
      simp only [callGdhHandle2, letV, bindV, v, Comp.cost, Expr.cost,
        renameComp_cost, liftGdhComp_cost]; omega
    have hH := gdhHandle2_cost_le_min S K; omega
  have hIp : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st1 : Var Γ₁ gdh1KeyState2Ty) (u : Var Γ₂ .nat),
      (initPrin1Key2B K (Δ := Δ) st1 u).cost ≤ 7 * K + 450 := by
    intro Γ₁ Γ₂ Δ _ _ st1 u
    refine le_trans (initPrin1Key2B K (Δ := Δ) st1 u).cost_le_costUB ?_
    simp only [initPrin1Key2B, stPrin, stUpd, stSecb, stSpks, stOpks, stSess, stResps,
      stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peMk, smUpd, smMk,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      KeyInd.pa2Up, KeyInd.pa2PrinTarget, rNone, rInitPrin, natEq,
      letV_costUB, bindV_costUB, eCaseOpt_costUB, eAny_costUB, liftGdhComp_costUB, gPrim_costUB,
      sBytes32_costUB, qX25519Base_costUB, litB_costUB, v_costUB,
      Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]; omega
  have hGs : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy)
      (x : Var Δ (.prod .nat .nat)),
      (genSpk1Key2B S K st1 q x).cost ≤
        28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62040 := by
    intro Δ st1 q x
    let arm : Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyState2Ty) :=
      let pa := Expr.fst (.fst (v st1))
      letV pa fun paV => letV (.snd (.fst (v st1))) fun sm => letV (smBase (v sm)) fun bSt =>
      letV (.snd (v st1)) fun sigB =>
      .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x)) (.ret (.pair rNone (v st1)))
        (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
          (.ret (.pair rNone (v st1))) fun ue =>
          .ite (natEq (v sigB) (.nat 0)) (.ret (.pair rNone (v st1)))
            (letV (eCaseOpt (KeyInd.pa2SpkTarget (v paV)) (.bool false) fun sp => nat2Eq (v x) (v sp)) fun isT =>
             bindV (liftGdhComp (gPrim sBytes32)) fun spkSkRaw =>
             bindV (liftGdhComp (gPrim (qX25519Base (v spkSkRaw)))) fun spkPkRaw =>
             letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
             letV (.ite (v isT) (KeyInd.pa2V (v paV)) (v spkPkRaw)) fun spkPk =>
             bindV (sigChalQ_dsl 33 (encEC (v spkPk))) fun spkSig =>
             bindV (liftGdhComp (gPrim sRandom64)) fun seed =>
             bindV (liftGdhComp (gPrim (qKemKeyGen (v seed)))) fun kp =>
             bindV (sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun pqSig =>
             let jId := u32OfNat (.snd (v x))
             let bE := sbMk (v spkSk) (v spkPk) (v spkSig) (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
             let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig) .none jId (.fst (v kp)) (v pqSig)
             let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
             let sm' := smUpd (v sm) (base := bSt')
             .ret (.pair (rBundle buOut) (.pair (.pair (v paV) sm') (.sub (v sigB) (.nat 1))))))
    have hArm : arm.cost ≤ 20 * K + 9000 := by
      refine le_trans arm.cost_le_costUB ?_
      simp only [arm, stPrin, stSpks, stUpd, stSecb, stOpks, stSess, stResps,
        stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peIkAPk, sbMk, buMk, smUpd, smMk,
        smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        KeyInd.pa2V, KeyInd.pa2SpkTarget, rNone, rBundle, natEq, nat2Eq, encEC_costUB, encKEM_costUB,
        letV_costUB, bindV_costUB, caseOptV_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB,
        liftGdhComp_costUB, gPrim_costUB, sigChalQ_dsl_costUB, sBytes32_costUB, sRandom64_costUB,
        qX25519Base_costUB, qKemKeyGen_costUB, litB_costUB, u32OfNat_costUB, v_costUB,
        Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]; omega
    have hEq : genSpk1Key2B S K st1 q x =
        .ite (eCaseOpt (KeyInd.pa2PrinTarget (.fst (.fst (v st1)))) (.bool false) fun uT => natEq (.fst (v x)) (v uT))
          arm (callGdhHandle2 S K st1 q) := rfl
    rw [hEq]; have hc := hCall st1 q
    simp only [Comp.cost, eCaseOpt, KeyInd.pa2PrinTarget, natEq, v, Expr.cost]; omega
  have hSub : ∀ {a b m : Nat}, a ≤ m → b ≤ m → 1 + max a b + 1 ≤ m + 2 := by omega
  let M := 28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62040
  unfold gdh1KeyHandle2
  simp only [caseSumV, v, Comp.cost, Expr.cost]
  refine (hSub (m := M + 4) ((hIp _ _).trans (by dsimp [M]; omega)) ?_).trans (by dsimp [M]; omega)
  refine hSub (m := M + 2) ((hCall _ _).trans (by dsimp [M]; omega)) ?_
  exact hSub (m := M) (hGs _ _ _) ((hCall _ _).trans (by dsimp [M]; omega))

private theorem tk_gdh1KeyFinish2_cost_le_min (S : Setup) (K : Nat) :
    (gdh1KeyFinish2 S K).cost ≤
      69 * (min K S.N_dh) ^ 2 + 69 * K * min K S.N_dh +
        66 * min K S.N_dh * min K S.N_sess_tot +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot + 2132 * K + 420 := by
  have hF : (gdhFinish2 S K).cost ≤
      69 * (min K S.N_dh) ^ 2 + 69 * K * min K S.N_dh +
        66 * min K S.N_dh * min K S.N_sess_tot +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot + 2132 * K + 409 := by
    refine le_trans (gdhFinish2 S K).cost_le_costUB ?_
    simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC_costUB, findMapStep2C,
      initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
      smBase_costUB, smLog_costUB, smPows_costUB, KeyInd.pa2U, KeyInd.pa2V, KeyInd.pa2Mode,
      natEq, letV_costUB, bindV_costUB, caseOptV_costUB, findMV_costUB, foldMV_costUB,
      eCaseOpt_costUB, eMap_costUB, ddhQ_costUB, litB_costUB, v_costUB,
      Comp.costUB, Expr.costUB, List.length_replicate, PNat.val_ofNat,
      bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
    have h : 69 * (min K S.N_dh) ^ 2 = 69 * (min K S.N_dh * min K S.N_dh) := by ring
    nlinarith
  have hEq : (gdh1KeyFinish2 S K).cost = (gdhFinish2 S K).cost + 4 := by
    simp only [gdh1KeyFinish2, letV, v, Comp.cost, Expr.cost, renameComp_cost, liftGdhComp_cost]; omega
  omega

private theorem fgKeyInd1KeyGapDh2Prog_totalCost_clamped_le (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).totalCost q ≤
      q * (28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62082) +
        69 * (min K S.N_dh) ^ 2 + 69 * K * min K S.N_dh +
        66 * min K S.N_dh * min K S.N_sess_tot +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot +
        45 * bits S.N_dh + 2133 * K + 1070 := by
  have hI := tk_fgKeyInd1KeyGapDh2Prog_init_cost_le S K
  have hH := tk_gdh1KeyHandle2_cost_le_min S K
  have hF := tk_gdh1KeyFinish2_cost_le_min S K
  have hH32 : (gdh1KeyHandle2 S K).cost + 32 ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62082 := by
    have := Nat.add_le_add_right hH 32
    clear hI hH hF
    omega
  have hmax : max 1 ((gdh1KeyHandle2 S K).cost + 32) ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62082 :=
    max_le (by omega) hH32
  have hq := Nat.mul_le_mul_left q hmax
  have hSum := Nat.add_le_add (Nat.add_le_add hI hq) hF
  clear hI hH hF hH32 hmax hq
  refine le_trans ?_ (le_trans hSum ?_)
  · exact le_rfl
  · omega

theorem fgKeyInd1KeyGapDh2Prog_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDh2Prog S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine (fgKeyInd1KeyGapDh2Prog_totalCost_clamped_le S b.q_total b.q_total).trans ?_
  have hbits : bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits]
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hdiff :
      2 ^ 16 * (q + 1) * (q + 1) + 2 ^ 15 * (q + 1) * (md + ms) +
        2 ^ 10 * (q + 1) * (ld + ls) + 2 ^ 11 * md ^ 2 + 2 ^ 8 * md * ms =
      (q * (28015 * q + 27165 * md + 14742 * ms + 62082) +
        69 * md ^ 2 + 69 * q * md + 66 * md * ms + 423 * md + 263 * ms +
        45 * (ld + 1) + 2133 * q + 1070) +
      (37521 * q ^ 2 + 66857 * q + 64421 + 5534 * q * md + 32345 * md +
        18026 * q * ms + 32505 * ms + 1024 * q * ld + 979 * ld +
        1024 * q * ls + 1024 * ls + 1979 * md ^ 2 + 190 * md * ms) := by ring
  omega

theorem fgKeyInd1KeyGapDh2Prog_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDh2Prog S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b :=
  (fgKeyInd1KeyGapDh2Prog_totalCost_le S b).trans (securityStepCostBudget_le_legacy S b)

end TupleKeyedSyntactic

section BilinearDdh

set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle Env.get Ext.wk
  CostedReduction.σ fgKeyInd1KeyGapDhProg

private def Ddh1KeyStep {α : Type} (m : ℕ) (Q : α → Prop)
    (oa : OracleComp (PrimBaseSpec + sigAndDdhOracle.spec) α) : Prop :=
  oa.IsQueryBoundP (fun q => isDdhChalQuery q = true) m ∧ ∀ x ∈ support oa, Q x

private theorem liftGdhToSign_isQueryBoundP_ddh {α : Type}
    (m : OracleComp GdhSimSpec α) :
    ∀ {n : ℕ}, m.IsQueryBoundP (fun q => q.isRight = true) n →
      (liftGdhToSign m).IsQueryBoundP (fun q => isDdhChalQuery q = true) n := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    intro n _
    exact isQueryBoundP_pure _ a n
  | query_bind q r ih =>
    intro n hm
    rw [isQueryBoundP_query_bind_iff] at hm
    rcases q with bq | dq
    · change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
        fun u => liftGdhToSign (r u)).IsQueryBoundP (fun q => isDdhChalQuery q = true) n
      rw [isQueryBoundP_query_bind_iff]
      simp only [isDdhChalQuery, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Or.inl (by decide), fun u => ih u (by simpa using hm.2 u)⟩
    · have hn : 0 < n := hm.1.resolve_left (by simp)
      change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
        fun u => liftGdhToSign (r u)).IsQueryBoundP (fun q => isDdhChalQuery q = true) n
      rw [isQueryBoundP_query_bind_iff]
      simp only [isDdhChalQuery, ↓reduceIte]
      exact ⟨Or.inr hn, fun u => ih u (by simpa using hm.2 u)⟩

private theorem hwDdh1Key : ∀ (g : pqSigAndDdhIface.Tag) (x : (pqSigAndDdhIface.dom g).denote),
    isDdhChalQuery (pqSigAndDdhIface.enc g x) = true → 1 ≤ wDdh1Key g := by
  intro g x hx
  cases g with
  | inl t => simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
  | inr t =>
    cases t with
    | inl m => simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
    | inr u => rcases u with ⟨⟩; decide

private theorem hUDdh1Key : ∀ n : ℕ,
    (pqSigAndDdhIface.fwdU n).IsQueryBoundP (fun q => isDdhChalQuery q = true) 0 := by
  intro n
  change IsQueryBoundP
    (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
    (fun q => isDdhChalQuery q = true) 0
  rw [isQueryBoundP_query_iff]
  simp [isDdhChalQuery]

private theorem callGdhHandle_ddhStep (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) (env : Env Δ)
    (s : gdhStateTy.denote) (qv : keyIndQueryTy.denote)
    (hst : (env.get st1).1 = s) (hq : env.get q = qv)
    {m : ℕ} {Q : (Ty.prod keyIndRespTy gdhStateTy).denote → Prop}
    (h : DdhStep m Q ((gdhHandle S K).eval (.cons s (.cons qv .nil)))) :
    Ddh1KeyStep m (fun p => Q (p.1, p.2.1)) ((callGdhHandle S K st1 q).eval env) := by
  have hEval : (callGdhHandle S K st1 q).eval env =
      (liftGdhToSign ((gdhHandle S K).eval (.cons s (.cons qv .nil))) >>=
        fun res => pure (res.1, (res.2, (env.get st1).2))) := by
    unfold callGdhHandle
    simp only [letV_eval, bindV, Comp.eval, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ', renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval, hst, hq]
  rw [hEval]
  refine ⟨(isQueryBoundP_bind (n := m) (m := 0) (liftGdhToSign_isQueryBoundP_ddh _ h.1)
    fun res _ => isQueryBoundP_pure _ _ 0).mono (by omega), fun p hp => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨res, hres, rfl⟩ := hp
  exact h.2 res (mem_support_liftGdhToSign hres)

private theorem gdh1KeyHandle_ddhStep_of_inr3 (S : Setup) (K : Nat)
    (st1 : gdh1KeyStateTy.denote) (gq : KeyIndQuery S)
    {rest : _} (hq : (keyIndCodec S).qenc gq = .inr (.inr (.inr rest)))
    {m : ℕ} {Q : (Ty.prod keyIndRespTy gdhStateTy).denote → Prop}
    (h : DdhStep m Q ((gdhHandle S K).eval (.cons st1.1 (.cons ((keyIndCodec S).qenc gq) .nil)))) :
    Ddh1KeyStep m (fun p => Q (p.1, p.2.1))
      ((gdh1KeyHandle S K).eval (.cons st1 (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  dsimp only [keyIndCodec] at hq h ⊢
  simp only [gdh1KeyHandle, caseSumV, Comp.eval, v, Expr.eval,
    Ext.refl_wk', Env.get_zero', Env.get_succ', hq]
  exact callGdhHandle_ddhStep S K _ _ _ st1.1 (keyIndQenc gq)
    (by simp only [Env.get_zero', Env.get_succ'])
    (by simp only [Env.get_zero', Env.get_succ', hq]) h

private theorem initPrin1KeyB_ddhStep (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) (env : Env Δ)
    (s : gdh1KeyStateTy.denote) (hst : env.get (Ext.wk st1) = s) :
    Ddh1KeyStep 0 (fun p => p.2.1.2.2.1 = s.1.2.2.1)
      ((initPrin1KeyB K st1 u).eval env) := by
  refine ⟨?_, fun p hp => ?_⟩
  · have hq := Comp.queryBound_eval (fun q => isDdhChalQuery q = true) wDdh1Key wsZero1Key
      hwDdh1Key hUDdh1Key (initPrin1KeyB K st1 u) env
    rwa [initPrin1KeyB_queries_ddh] at hq
  · unfold initPrin1KeyB at hp
    simp only [letV_eval, bindV, Comp.eval] at hp
    split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', hst]
    · simp only [mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hp
      obtain ⟨sk0, _, pk0, _, rfl⟩ := hp
      simp [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ', hst]

private theorem genSpk1KeyB_ddhStep (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy)
    (x : Var Δ (.prod .nat .nat)) (env : Env Δ)
    (s : gdh1KeyStateTy.denote) (gq : KeyIndQuery S)
    (hst : env.get st1 = s) (hq : env.get q = (keyIndCodec S).qenc gq)
    (hR : isRoQ gq = false) (hS : isSessQ gq = false) :
    Ddh1KeyStep 0 (fun p => p.2.1.2.2.1 = s.1.2.2.1)
      ((genSpk1KeyB S K st1 q x).eval env) := by
  unfold genSpk1KeyB
  simp only [Comp.eval]
  split
  · refine ⟨?_, fun p hp => ?_⟩
    · refine (Comp.queryBound_eval (fun q => isDdhChalQuery q = true) wDdh1Key wsZero1Key
        hwDdh1Key hUDdh1Key _ env).mono ?_
      simp [Comp.queries]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [letV_eval, caseOptV, bindV, Comp.eval] at hp
      split at hp
      · simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', hst]
      · split at hp
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', hst]
        · split at hp
          · simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp
            simp [v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_succ', hst]
          · simp only [mem_support_bind_iff, support_pure,
              Set.mem_singleton_iff] at hp
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := hp
            simp [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
              Env.get_zero', Env.get_succ', hst]
  · exact callGdhHandle_ddhStep S K st1 q env s.1 ((keyIndCodec S).qenc gq)
      (congrArg Prod.fst hst) hq (gdhHandle_ddhStep_other S K s.1 gq hR hS)

private theorem gdh1KeyHandle_ddhStep_ro (S : Setup) (K : Nat)
    (st1 : gdh1KeyStateTy.denote) (gq : KeyIndQuery S) (hR : isRoQ gq = true) :
    Ddh1KeyStep (4 * fgSDone st1.1.2.2.1)
      (fun p => fgRDone p.2.1.2.2.1 ≤ fgRDone st1.1.2.2.1 + 1 ∧
        fgSDone p.2.1.2.2.1 = fgSDone st1.1.2.2.1)
      ((gdh1KeyHandle S K).eval (.cons st1 (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq with
  | roQuery _ =>
    exact gdh1KeyHandle_ddhStep_of_inr3 S K st1 _ rfl (gdhHandle_ddhStep_ro S K st1.1 _ hR)
  | _ => simp [isRoQ] at hR

private theorem gdh1KeyHandle_ddhStep_sess (S : Setup) (K : Nat)
    (st1 : gdh1KeyStateTy.denote) (gq : KeyIndQuery S) (hS : isSessQ gq = true) :
    Ddh1KeyStep (4 * (fgRDone st1.1.2.2.1 + fgSDone st1.1.2.2.1))
      (fun p =>
        let r := fgRDone st1.1.2.2.1
        let s := fgSDone st1.1.2.2.1
        (fgRDone p.2.1.2.2.1 = r ∧ fgSDone p.2.1.2.2.1 = s) ∨
        (fgRDone p.2.1.2.2.1 = r + 1 ∧ fgSDone p.2.1.2.2.1 = s) ∨
        (fgRDone p.2.1.2.2.1 = r ∧ fgSDone p.2.1.2.2.1 = s + 1))
      ((gdh1KeyHandle S K).eval (.cons st1 (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq with
  | initiateOPK _ _ _ | initiateNoOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ =>
    exact gdh1KeyHandle_ddhStep_of_inr3 S K st1 _ rfl (gdhHandle_ddhStep_sess S K st1.1 _ hS)
  | _ => simp [isSessQ] at hS

private theorem gdh1KeyHandle_ddhStep_other (S : Setup) (K : Nat)
    (st1 : gdh1KeyStateTy.denote) (gq : KeyIndQuery S)
    (hR : isRoQ gq = false) (hS : isSessQ gq = false) :
    Ddh1KeyStep 0 (fun p => p.2.1.2.2.1 = st1.1.2.2.1)
      ((gdh1KeyHandle S K).eval (.cons st1 (.cons ((keyIndCodec S).qenc gq) .nil))) := by
  cases gq with
  | initPrin u =>
    dsimp only [keyIndCodec]
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact initPrin1KeyB_ddhStep K _ _ _ st1
      (by simp only [Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'])
  | corruptIK u =>
    have hSub := gdhHandle_ddhStep_other S K st1.1 (.corruptIK u) hR hS
    dsimp only [keyIndCodec] at hSub ⊢
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact callGdhHandle_ddhStep S K _ _ _ st1.1 (keyIndQenc (.corruptIK u))
      (by simp only [Env.get_zero', Env.get_succ'])
      (by simp only [Env.get_zero', Env.get_succ', keyIndQenc]) hSub
  | genSPK u j =>
    dsimp only [keyIndCodec]
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV, Comp.eval, v, Expr.eval,
      Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact genSpk1KeyB_ddhStep S K _ _ _ _ st1 (.genSPK u j)
      (by simp only [Env.get_zero', Env.get_succ'])
      (by simp only [Env.get_zero', Env.get_succ', keyIndCodec, keyIndQenc]) hR hS
  | _ =>
    exact gdh1KeyHandle_ddhStep_of_inr3 S K st1 _ rfl (gdhHandle_ddhStep_other S K st1.1 _ hR hS)

private theorem simulateQ_handlerImpl_ddhPhi_1Key {S : Setup} {σ : PT} {α : Type}
    (fgLOf : σ.denote → List fgPatchEntryTy.denote)
    (h : Comp pqxdhOps pqSigAndDdhIface [σ, (keyIndCodec S).Q] (.prod (keyIndCodec S).R σ))
    (hStepRo : ∀ st gq, isRoQ gq = true →
      Ddh1KeyStep (4 * fgSDone (fgLOf st))
        (fun p => fgRDone (fgLOf p.2) ≤ fgRDone (fgLOf st) + 1 ∧ fgSDone (fgLOf p.2) = fgSDone (fgLOf st))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepSess : ∀ st gq, isSessQ gq = true →
      Ddh1KeyStep (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
        (fun p =>
          let r := fgRDone (fgLOf st)
          let s := fgSDone (fgLOf st)
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r + 1 ∧ fgSDone (fgLOf p.2) = s) ∨
          (fgRDone (fgLOf p.2) = r ∧ fgSDone (fgLOf p.2) = s + 1))
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (hStepOther : ∀ st gq, isRoQ gq = false → isSessQ gq = false →
      Ddh1KeyStep 0 (fun p => fgLOf p.2 = fgLOf st)
        (h.eval (.cons st (.cons ((keyIndCodec S).qenc gq) .nil))))
    (oa : OracleComp (unifSpec + keyIndSpec S) α) :
    ∀ (r_rem s_rem : ℕ) (st : σ.denote),
      oa.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_rem →
      oa.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_rem →
      ((simulateQ (handlerImpl (C := keyIndCodec S) h) oa).run st).IsQueryBoundP
        (fun q => isDdhChalQuery q = true)
        (fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r_rem s_rem st _ _
    simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro r_rem s_rem st hRo hSess
    rw [isQueryBoundP_query_bind_iff] at hRo hSess
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases t with uq | gq
    · have hStep0 : (((handlerImpl (C := keyIndCodec S) h) (.inl uq)).run st).IsQueryBoundP
          (fun q => isDdhChalQuery q = true) 0 := by
        have hb := isQueryBoundP_bind (n := 0) (m := 0) (hUDdh1Key uq)
          (fun u _ => isQueryBoundP_pure
            (fun q : (PrimBaseSpec + sigAndDdhOracle.spec).Domain => isDdhChalQuery q = true)
            (u, st) 0)
        simpa [handlerImpl] using hb
      refine (isQueryBoundP_bind (n := 0)
        (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
        hStep0 fun x hx => ?_).mono (by omega)
      have hst : x.2 = st := by
        simp only [handlerImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨_, _, rfl⟩ := hx; rfl
      rw [← hst]
      exact ih x.1 r_rem s_rem x.2
        (by simpa [onGame] using hRo.2 x.1)
        (by simpa [onGame] using hSess.2 x.1)
    · cases hR : isRoQ gq
      · cases hS : isSessQ gq
        · have hs := hStepOther st gq hR hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => isDdhChalQuery q = true) 0 := by
            have hb := isQueryBoundP_bind (n := 0) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            simpa [handlerImpl] using hb
          refine (isQueryBoundP_bind (n := 0)
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st)) r_rem s_rem)
            hRun fun x hx => ?_).mono (by omega)
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          have hEq := hs.2 p hp
          have hCont := ih ((keyIndCodec S).rdec gq p.1) r_rem s_rem p.2
            (by simpa [onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
          rwa [hEq] at hCont
        · have hPos : 0 < s_rem := hSess.1.resolve_left (by simp [onGame, hS])
          obtain ⟨s', rfl⟩ : ∃ s', s_rem = s' + 1 := ⟨s_rem - 1, by omega⟩
          have hs := hStepSess st gq hS
          have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
              (fun q => isDdhChalQuery q = true) (4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) := by
            have hb := isQueryBoundP_bind (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st))) (m := 0) hs.1
              (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
            simpa [handlerImpl] using hb
          refine (isQueryBoundP_bind
            (n := 4 * (fgRDone (fgLOf st) + fgSDone (fgLOf st)))
            (m := fgDdhPhi (fgRDone (fgLOf st)) (fgSDone (fgLOf st) + 1) r_rem s')
            hRun fun x hx => ?_).mono (by rw [fgDdhPhi_sess_step])
          simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact (ih ((keyIndCodec S).rdec gq p.1) r_rem s' p.2
            (by simpa [onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
            (by simpa [onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))).mono
            (fgDdhPhi_le_sess_inc (hs.2 p hp) r_rem s')
      · have hS : isSessQ gq = false := by cases gq <;> simp_all [isRoQ, isSessQ]
        have hPos : 0 < r_rem := hRo.1.resolve_left (by simp [onGame, hR])
        obtain ⟨r', rfl⟩ : ∃ r', r_rem = r' + 1 := ⟨r_rem - 1, by omega⟩
        have hs := hStepRo st gq hR
        have hRun : (((handlerImpl (C := keyIndCodec S) h) (.inr gq)).run st).IsQueryBoundP
            (fun q => isDdhChalQuery q = true) (4 * fgSDone (fgLOf st)) := by
          have hb := isQueryBoundP_bind (n := 4 * fgSDone (fgLOf st)) (m := 0) hs.1
            (fun p _ => isQueryBoundP_pure _ ((keyIndCodec S).rdec gq p.1, p.2) 0)
          simpa [handlerImpl] using hb
        refine (isQueryBoundP_bind
          (n := 4 * fgSDone (fgLOf st))
          (m := fgDdhPhi (fgRDone (fgLOf st) + 1) (fgSDone (fgLOf st)) r' s_rem)
          hRun fun x hx => ?_).mono (by rw [fgDdhPhi_ro_step])
        simp only [handlerImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨hr_le, hs_eq⟩ := hs.2 p hp
        have hCont := ih ((keyIndCodec S).rdec gq p.1) r' s_rem p.2
          (by simpa [onGame, hR] using hRo.2 ((keyIndCodec S).rdec gq p.1))
          (by simpa [onGame, hS] using hSess.2 ((keyIndCodec S).rdec gq p.1))
        rw [hs_eq] at hCont
        exact hCont.mono (fgDdhPhi_mono hr_le le_rfl le_rfl)

private theorem fgKeyInd1KeyGapDhProg_chalBounded_bilinear (S : Setup) (K r_max s_max : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hRo : ∀ a, (A a).IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) r_max)
    (hSess : ∀ a, (A a).IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) s_max)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      (4 * r_max * s_max + 2 * s_max * (s_max - 1) + K + min K S.N_dh + min K S.N_sess_tot) := by
  have hInitQ : (((fgKeyInd1KeyGapDhProg S K).init).eval (.cons (U, V) .nil)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) 0 := by
    have hq := Comp.queryBound_eval (fun q => isDdhChalQuery q = true) wDdh1Key wsZero1Key
      hwDdh1Key hUDdh1Key (fgKeyInd1KeyGapDhProg S K).init (.cons (U, V) .nil)
    rwa [fgKeyInd1KeyGapDhProg_init_queries_ddh] at hq
  have hInitSupp : ∀ as ∈ support (((fgKeyInd1KeyGapDhProg S K).init).eval (.cons (U, V) .nil)),
      as.2.1.2.2.1 = [] := by
    have hInitEval : (((fgKeyInd1KeyGapDhProg S K).init).eval (.cons (U, V) .nil) :
        OracleComp GdhSignSimSpec (Unit × gdh1KeyStateTy.denote)) =
        (unifGdhSign (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) >>= fun idx =>
          unifGdhSign ($ᵗ Bool) >>= fun secb =>
            pure ((), sim1KeyStateToVal (params1KeyFlatVal S U V idx)
              (FgKeyInd1KeySimState.empty S secb))) := by
      simp only [fgKeyInd1KeyGapDhProg, initAdv4_1Key, initAdv4_1KeyBase,
        bindV, letV_eval, Comp.eval, liftGdhComp_eval, gPrim_eval,
        sIndex_eval, sBool_eval, initParams1KeyFlat_eval, emptySimE_eval (S := S),
        v, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
        liftGdhToSign_bind, liftGdhToSign_pure, unifGdhSign, unifGdh,
        FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq,
        sim1KeyStateToVal, FgKeyInd1KeySimState.empty,
        bind_assoc, pure_bind]
    intro as has
    change as ∈ support (((fgKeyInd1KeyGapDhProg S K).init).eval (.cons (U, V) .nil) :
      OracleComp GdhSignSimSpec (Unit × gdh1KeyStateTy.denote)) at has
    rw [hInitEval] at has
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at has
    obtain ⟨idx, _, secb, _, rfl⟩ := has
    rfl
  unfold CostedReduction.eval CostedReduction.impl
  refine (isQueryBoundP_bind (n := 0)
    (m := 4 * r_max * s_max + 2 * s_max * (s_max - 1) + (K + min K S.N_dh + min K S.N_sess_tot))
    hInitQ fun as has => ?_).mono (by omega)
  have hEmpty := hInitSupp as has
  have hSim := simulateQ_handlerImpl_ddhPhi_1Key (fun s : gdh1KeyStateTy.denote => s.1.2.2.1)
    (gdh1KeyHandle S K) (gdh1KeyHandle_ddhStep_ro S K) (gdh1KeyHandle_ddhStep_sess S K)
    (gdh1KeyHandle_ddhStep_other S K) (A as.1) r_max s_max as.2 (hRo as.1) (hSess as.1)
  rw [hEmpty, show fgRDone [] = 0 from rfl, show fgSDone [] = 0 from rfl,
    fgDdhPhi_zero_done] at hSim
  refine isQueryBoundP_bind
    (n := 4 * r_max * s_max + 2 * s_max * (s_max - 1))
    (m := K + min K S.N_dh + min K S.N_sess_tot)
    hSim fun bs _ => ?_
  have hFin := Comp.queryBound_eval (fun q => isDdhChalQuery q = true) wDdh1Key wsZero1Key
    hwDdh1Key hUDdh1Key (gdh1KeyFinish S K) (.cons bs.2 (.cons bs.1 .nil))
  rwa [gdh1KeyFinish_queries_ddh] at hFin

private theorem fgKeyInd1KeyGapDhProg_chalBounded_gdhQueryBudget (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (gdhQueryBudget S b) := by
  obtain ⟨hRoRaw, hSend, hRecv, hTotRaw, hOnRaw⟩ := A.2
  have hTot : A.1.run.IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    convert hTotRaw using 1
    funext q; cases q
    · exact propext ⟨False.elim, Bool.noConfusion⟩
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  let M_ro := min b.q_ro b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  by_cases hLe : 4 * b.q_total ^ 2 ≤ 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)
  · refine (fgKeyInd1KeyGapDhProg_ddhBounded S b.q_total b.q_total (fun _ => A.1.run)
      (fun _ => hTot) U V).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * b.q_total * b.q_total + b.q_total + min b.q_total S.N_dh + min b.q_total S.N_sess_tot ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [Nat.min_eq_left hLe]
    have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    nlinarith
  · have hMin : min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) =
        4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) :=
      Nat.min_eq_right (Nat.le_of_not_le hLe)
    have hRoOn : A.1.run.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) b.q_ro := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRoRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [onGame, isRoQ, isKeyIndRoQuery]
    have hSessOn : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) S.N_sess_tot := by
      refine isQueryBoundP_or_add (p₁ := isKeyIndSendQuery) (p₂ := isKeyIndRecvQuery) ?_ hSend hRecv
      intro t ht
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [onGame, isSessQ, isKeyIndSendQuery, isKeyIndRecvQuery]
    have hSessQOn : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) b.q_on := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hOnRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [onGame, isSessQ, isKeyIndOnlineQuery]
    have hRoM : A.1.run.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isRoQ t = true)) M_ro := by
      by_cases h1 : b.q_ro ≤ b.q_total
      · simpa [M_ro, Nat.min_eq_left h1] using hRoOn
      · simpa [M_ro, Nat.min_eq_right (Nat.le_of_not_le h1)] using isQueryBoundP_of_imp
          (fun t (ht : onGame (G := keyIndSpec S) (fun t => isRoQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessOnTot : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) (min b.q_on b.q_total) := by
      by_cases hOn : b.q_on ≤ b.q_total
      · simpa [Nat.min_eq_left hOn] using hSessQOn
      · simpa [Nat.min_eq_right (Nat.le_of_not_le hOn)] using isQueryBoundP_of_imp
          (fun t (ht : onGame (G := keyIndSpec S) (fun t => isSessQ t = true) t) => by
            cases t with | inl _ => exact ht.elim | inr _ => trivial) hTot
    have hSessM : A.1.run.IsQueryBoundP (onGame (G := keyIndSpec S) (fun t => isSessQ t = true)) M_sess := by
      by_cases h2 : min b.q_on b.q_total ≤ S.N_sess_tot
      · simpa [M_sess, Nat.min_eq_left h2] using hSessOnTot
      · simpa [M_sess, Nat.min_eq_right (Nat.le_of_not_le h2)] using hSessOn
    refine (fgKeyInd1KeyGapDhProg_chalBounded_bilinear S b.q_total M_ro M_sess
      (fun _ => A.1.run) (fun _ => hRoM) (fun _ => hSessM) U V).mono ?_
    unfold gdhQueryBudget
    dsimp only
    change 4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1) + b.q_total +
        min b.q_total S.N_dh + min b.q_total S.N_sess_tot ≤
      min (4 * b.q_total ^ 2) (4 * M_ro * M_sess + 2 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [hMin]
    have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
    omega

end BilinearDdh

/-- `fgKeyInd1KeyGapDhDslAdv` satisfies its declared DDH, signing, and primitive query bounds. -/
theorem fgKeyInd1KeyGapDhDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyInd1KeyGapDhDslAdv S b A).Bounded := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    obtain ⟨_, _, _, h, _⟩ := A.2
    convert h using 1
    funext q; cases q <;> rfl
  refine ⟨fun U V => ?_, fun U V => ?_, fun U V => ?_⟩
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval.fgKeyInd1KeyGapDh2Prog_queryBound_of_flatProg
      S b.q_total A.1.run hA U V (fun q => isDdhChalQuery q = true)
      (fun _ => by simp [isDdhChalQuery]) (gdhQueryBudget S b)
      (fgKeyInd1KeyGapDhProg_chalBounded_gdhQueryBudget S b A U V)
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval.fgKeyInd1KeyGapDh2Prog_transfer_queryBound
      S b.q_total A.1.run hA U V (fun q => isSigChalQuery q = true)
      (fun _ => by simp [isSigChalQuery]) (2 * min S.N_spk_tot S.N_recv)
      (fun idx _ => Proofs.SignalPqxdh.Security.FgGapDh1Key.isQueryBoundP_fgKeyInd1KeyGapDhRunAtFlat_sig idx S b A U V)
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval.fgKeyInd1KeyGapDh2Prog_queryBound_of_flatProg
      S b.q_total A.1.run hA U V (fun q => isPrimQuery q = true)
      (fun _ => by simp [isPrimQuery]) (gdhPrimQueryBudget S b)
      (fgKeyInd1KeyGapDhProg_primBounded_gdhPrimQueryBudget S b.q_total b A U V)

theorem fgKeyInd1KeyGapDhProg_evalDist_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgKeyInd1KeyGapDhDslAdv S b A)] =
      𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A)] :=
  Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval.fgKeyInd1KeyGapDh2Prog_evalDist_gapDhWithSignExp_eq
    P isValidDhTriple pow8 S b A

/-- Advantage equality between `fgKeyInd1KeyGapDhDslAdv` and `fgKeyInd1KeyGapDhAdv4`. -/
theorem fgKeyInd1KeyGapDhProg_gapDhWithSign_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSign P isValidDhTriple pow8 (fgKeyInd1KeyGapDhDslAdv S b A) =
      GapDhWithSign P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A) := by
  simp only [GapDhWithSign, fgKeyInd1KeyGapDhProg_evalDist_eq]

theorem fgKeyInd1KeyGapDhProg_gapDhWithSignReal_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSignReal P isValidDhTriple pow8 (fgKeyInd1KeyGapDhDslAdv S b A) =
      GapDhWithSignReal P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A) :=
  congrArg ENNReal.toReal
    (fgKeyInd1KeyGapDhProg_gapDhWithSign_eq P isValidDhTriple pow8 S b A)

/-- Imperfect-correctness `G3 -> G3.5` `GapDhWithSign` advantage bound over
    `fgKeyInd1KeyGapDhDslAdv`. -/
theorem keyIndAdvG3_1Key_le_gapDhWithSignδ_dsl
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    Proofs.SignalPqxdh.Security.keyIndAdvG3_1Key S P A.1 ≤
      2 * (((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
            (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
            (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
            GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhDslAdv S b A)) +
      kemDecapsFailureTermReal S δ := by
  rw [fgKeyInd1KeyGapDhProg_gapDhWithSignReal_eq]
  exact Proofs.SignalPqxdh.Security.keyIndAdvG3_1Key_le_gapDhWithSignδ S P hP δ hδ b A

end SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
