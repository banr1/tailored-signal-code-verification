/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhFinish

/-!
# Key-Management Arms and `init`/`finish` Simulation for `Auth` Gap-DH and EUF-CMA

**Checked by Lean.** Proves the `FgArmSim` obligations for key-management and corruption queries
(`initPrin`, `corruptIK`, `genSPK`, `genOPK`, `revealDhSecrets`, `registerKey`), together with the
`init` and `finish` simulation obligations for `a1g2KindProg` and `a1s2KindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimMisc

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Expr Comp Env pqAtomicSig pqAtomicOps PB drKeyT mapML
  Expr.eval_litBytes Expr.eval_bytesBeq Expr.eval_bytesTakeK Expr.eval_bytesDrop
  Expr.eval_bytesLen Expr.eval_u32OfNat)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (embedTy embedVal projVal
  embedVal_projVal projVal_embedVal embedEnv embedCtx exprRename exprRename_eval compRename
  compRename_eval mapExpr mapExpr_eval mapComp mapComp_eval comp_queries_zero_of_zero
  tlAuthSigDdh liftAuth1Stage authQenc_eq)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery Bytes)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface B authQenc)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec)
open _root_.SignalPqxdh.Security (liftGdhToSign)
open _root_.SignalPqxdh.Security.ReductionDsl (drKeyTy authStateTy fgPatchEntryTy authQueryTy
  authRespTy authSessionEntryTy eval_sampleBytes32 eval_sampleRandom64 eval_queryPrim
  eval_sampleBytes32C eval_sampleRandom64C eval_queryPrimC embedPrim_pure embedPrim_bind embedPrim_map)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (Ext v bindV letV caseOptV caseSumV
  findMV mapMV foldMV eAny eFind eMap eCaseOpt eCaseSum fgSimTy rootEntryTy respRecTy
  a1gParams2Ty gs2Ty a1g2StTy a1sStTy emptyAuthStE stPrin stSpks stOpks stSess stAdv stUpd
  seEkASk sePeerSpk seSid sbSpkSk sbSpkPk sbMk peSecIKA0 peIkAPk peSecIKAsign peMk peUpd oeMk buMk
  natEq nat2Eq nat3Eq encEC encKEM encEC_eval encKEM_eval Env.get_vz Env.get_vs Ext.step_wk
  Ext.refl_wk eval_queryDdh queryPrimC_x25519_eval queryPrimC_pow8_eval eval_natEq
  onBaseF corruptB genOpkB rs aNone aPk aCorr aInitPrin aBundle fsBase fsL fsRootL fsRaw fsLog
  fsResp fsPows fsMk fsUpd emptySimE zero32 slice32 bytesEmpty pa2U pa2V pa2Role pa2TS pa2Dh1
  a1sFg a1sMk a1sDummyPa a1gPre2C fgStep2C a1gInitPrin2C a1gGenSpk2C fgGenSpk2C fgRegisterC
  findMap2C logScan2C respCand2C initDh1Cand2C fgExtract2C fgInit2Dsl fgFinish2Dsl
  a1g2InitDsl a1g2FinishDsl fgAuth1KeyGapDhProg a1sInit2Dsl a1sFinishDsl sigAuth1KeyProg sigAuth1KeyDslProg)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp liftGdhComp_eval
  liftGdhToSign_bind liftGdhToSign_pure mem_support_liftGdhToSign sigChalQ_dsl sigChalQ_dsl_eval
  renameComp renameComp_eval twoVarRen pullEnv pullEnv_twoVarRen)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (avlEmptyE dfltB192E dfltPair32E dfltDrKeyE dfltPbytesPair32E)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (take_min_left_of_length_le roEntriesOf ShadowRelB192 ShadowRelPair32 RoCacheRelB192)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels emptyRoAvlE wk1 liftExpr1 corruptKB genOpkKB aNoneAtomicE)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv AuthBaseValOnlineBounded AuthBaseAtomOnlineBounded)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (fgAuthShadowAuxTy a1g2ShadowStTy a1s2ShadowStTy auxFgSess auxFgCtr auxFgRoAvl auxFgRootSess
   auxFgRootCtr auxFgRootRoAvl auxRawAvl fgAuxMkE emptyFgRoAvlE emptyFgRootRoAvlE
   emptyFgAuthShadowAuxE liftCs1 liftGdh1 a1gInitPrin2LegC fgCorruptLegC a1gGenSpk2LegC
   fgGenOpkLegC fgRegisterLegC fgExtract2K fgCoreArm_initPrin fgCoreArm_corrupt fgCoreArm_genSPK
   fgCoreArm_genOPK fgCoreArm_revealDh fgCoreArm_registerKey
   a1g2KindInit a1g2KindFinish a1g2KindProg a1s2KindInit a1s2KindFinish a1s2KindProg)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (forgetGdh forgetSig gdhOldAtomicProg sigOldAtomicProg legacyCoreArmComp
   FgTableShadow RootTableShadow FgSimShadowInv GdhAuthInv SigAuthInv AuthSigDdhSpec
   legacyCoreArmEval armEval_initPrin armEval_corruptIK armEval_genSPK armEval_genOPK
   armEval_revealDhSecrets armEval_registerKey FgArmSim)

private theorem mapComp_auth_eval {Γ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps pqSigAndDdhIface Γ out) (ρ : Env Γ) :
    ((mapComp tlAuthSigDdh c : Comp pqAtomicOps pqAuthSigAndDdhIface (embedCtx Γ) (embedTy out)).eval
      (embedEnv ρ) : OracleComp AuthSigDdhSpec (embedTy out).denote) =
      (embedVal out <$> c.eval ρ : OracleComp AuthSigDdhSpec (embedTy out).denote) :=
  mapComp_eval tlAuthSigDdh c (comp_queries_zero_of_zero (fun _ => rfl) c) ρ

private theorem liftExpr1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftExpr1 e argE).eval ρ = embedVal out (e.eval (.cons (projVal a (argE.eval ρ)) .nil)) := by
  simp only [liftExpr1, Expr.eval]
  rw [exprRename_eval (mapExpr e) wk1 (.cons (argE.eval ρ) .nil) (.cons (argE.eval ρ) ρ)
    (fun {x} v => by cases v with | zero => rfl | succ w => nomatch w)]
  have hArg : (Env.cons (argE.eval ρ) .nil : Env [embedTy a]) =
      embedEnv (.cons (projVal a (argE.eval ρ)) .nil) := by simp [embedEnv, embedVal_projVal]
  rw [hArg, mapExpr_eval]

private theorem liftCs1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    ((liftCs1 c argE).eval ρ : OracleComp AuthSigDdhSpec (embedTy out).denote) =
      (embedVal out <$> c.eval (.cons (projVal a (argE.eval ρ)) .nil) :
        OracleComp AuthSigDdhSpec (embedTy out).denote) := by
  simp only [liftCs1, Comp.eval, pure_bind]
  erw [compRename_eval (mapComp tlAuthSigDdh c) wk1 (.cons (argE.eval ρ) .nil) (.cons (argE.eval ρ) ρ)
    (fun {x} w => by cases w with | zero => rfl | succ u => nomatch u)]
  have hArg : (Env.cons (argE.eval ρ) .nil : Env [embedTy a]) =
      embedEnv (.cons (projVal a (argE.eval ρ)) .nil) := by simp [embedEnv, embedVal_projVal]
  erw [hArg, mapComp_eval tlAuthSigDdh c (comp_queries_zero_of_zero (fun _ => rfl) c)]; rfl

private theorem liftGdh1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    ((liftGdh1 c argE).eval ρ : OracleComp AuthSigDdhSpec (embedTy out).denote) =
      (embedVal out <$> liftGdhToSign (c.eval (.cons (projVal a (argE.eval ρ)) .nil)) :
        OracleComp AuthSigDdhSpec (embedTy out).denote) := by
  rw [liftGdh1, liftCs1_eval, liftGdhComp_eval]

private theorem fgSimShadowInv_empty (S : Setup) (b : QueryBudget)
    {Γ : List (Ty pqSig)} (secbE : Expr pqxdhOps Γ .bool) (env : Env Γ)
    {Γ' : List (Ty pqAtomicSig)} (ρ : Env Γ') :
    FgSimShadowInv S b 0 (embedVal fgSimTy ((emptySimE secbE).eval env))
      ((emptyFgAuthShadowAuxE (Γ := Γ')).eval ρ) where
  counter_inv := AuthCounterInv.zero b
  base_online := by
    change AuthBaseAtomOnlineBounded 0 (embedVal authStateTy ((emptyAuthStE secbE).eval env))
    rw [AuthBaseAtomOnlineBounded.iff_embedVal]
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  pows_len := Nat.zero_le _; resp_len := Nat.zero_le _; log_len := Nat.zero_le _
  fg_shadow := ⟨[], ShadowRelB192.empty (drKeyT (ℓ := 0) (Pt := Empty)) (0 + 0)
    (AuthKindFuels.ofBudget S b).K_cap (fun (e : (embedTy fgPatchEntryTy).denote) => e.2.2.2.2.2)
    (.pair dfltDrKeyE (.nat 0)) ρ, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ h => nomatch h⟩
  root_shadow := ⟨[], ShadowRelPair32.empty (.prod (PB 32) (PB 32)) (0 + 0)
    (AuthKindFuels.ofBudget S b).K_cap (fun (e : (embedTy rootEntryTy).denote) => e.2.2)
    (.pair dfltPbytesPair32E (.nat 0)) ρ, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ h => nomatch h⟩
  raw_rel := RoCacheRelB192.empty (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total
    (AuthKindFuels.ofBudget S b).K_cap dfltDrKeyE ρ
  raw_len := Nat.zero_le _

private theorem mapML_support_length {ι : Type} {T : OracleSpec ι} {α β : Type} (f : α → OracleComp T β) :
    ∀ (xs : List α) {ys : List β}, ys ∈ support (mapML f xs) → ys.length = xs.length
  | [], _, h => by simp only [mapML, mem_support_pure_iff] at h; simp [h]
  | _ :: xs, _, h => by
    simp only [mapML, mem_support_bind_iff, mem_support_pure_iff] at h
    rcases h with ⟨_, _, _, hys', rfl⟩; simp [mapML_support_length f xs hys']

/-! ## `init` and `finish` Simulation Obligations -/

theorem a1g2KindProg_init_sim (S : Setup) (b : QueryBudget) (uv : (Ty.prod (PB 32) (PB 32)).denote) :
    Prod.map id forgetGdh <$> (a1g2KindProg S b).init.eval (.cons uv .nil) =
      (gdhOldAtomicProg S b).init.eval (.cons uv .nil) ∧
    ∀ p ∈ support ((a1g2KindProg S b).init.eval (.cons uv .nil)), GdhAuthInv S b 0 p.2 := by
  refine ⟨by simp [a1g2KindProg, a1g2KindInit, gdhOldAtomicProg, liftAuth1Stage,
    fgAuth1KeyGapDhProg, forgetGdh, Comp.eval, Expr.eval, Expr.v0, Env.get], ?_⟩
  intro p hp
  have hEnv : (Env.cons uv .nil : Env (embedCtx [.prod (B 32) (B 32)])) =
      embedEnv (.cons (projVal (.prod (B 32) (B 32)) uv) .nil) := by simp [embedEnv, embedVal_projVal]
  have hMap : ((mapComp tlAuthSigDdh (a1g2InitDsl S b.q_total) :
        Comp pqAtomicOps pqAuthSigAndDdhIface [.prod (PB 32) (PB 32)] _).eval (.cons uv .nil)) =
      (embedVal (.prod .unit a1g2StTy) <$> (a1g2InitDsl S b.q_total).eval
        (.cons (projVal (.prod (B 32) (B 32)) uv) .nil) : OracleComp AuthSigDdhSpec _) := by
    rw [hEnv, mapComp_auth_eval]
  rw [show (a1g2KindProg S b).init = a1g2KindInit S b from rfl] at hp
  simp only [a1g2KindInit, Comp.eval, mem_support_bind_iff, mem_support_pure_iff] at hp
  rcases hp with ⟨r₀, hr₀, rfl⟩
  have hr₀' : r₀ ∈ support (embedVal (.prod .unit a1g2StTy) <$>
      (a1g2InitDsl S b.q_total).eval (.cons (projVal (.prod (B 32) (B 32)) uv) .nil)) := hMap ▸ hr₀
  simp only [map_eq_bind_pure_comp, Function.comp_apply, a1g2InitDsl, bindV, Comp.eval,
    liftGdhComp_eval, mem_support_bind_iff, mem_support_pure_iff] at hr₀'
  rcases hr₀' with ⟨_, ⟨r₁, hr₁, rfl⟩, rfl⟩
  simp only [fgInit2Dsl, bindV, Comp.eval, liftGdhToSign_bind, liftGdhToSign_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr₁
  rcases hr₁ with ⟨role, _, spk?, _, secb, _, rfl⟩
  exact fgSimShadowInv_empty S b (Expr.var .zero)
    (.cons secb (.cons spk? (.cons role (.cons (projVal (.prod (B 32) (B 32)) uv) .nil)))) _

theorem a1s2KindProg_init_sim (S : Setup) (b : QueryBudget) (pk : (PB 32).denote) :
    Prod.map id forgetSig <$> (a1s2KindProg S b).init.eval (.cons pk .nil) =
      (sigOldAtomicProg S b).init.eval (.cons pk .nil) ∧
    ∀ p ∈ support ((a1s2KindProg S b).init.eval (.cons pk .nil)), SigAuthInv S b 0 p.2 := by
  refine ⟨by simp [a1s2KindProg, a1s2KindInit, sigOldAtomicProg, liftAuth1Stage,
    sigAuth1KeyDslProg, sigAuth1KeyProg, forgetSig, Comp.eval, Expr.eval, Expr.v0, Env.get], ?_⟩
  intro p hp
  have hEnv : (Env.cons pk .nil : Env (embedCtx [B 32])) =
      embedEnv (.cons (projVal (B 32) pk) .nil) := by simp [embedEnv, embedVal_projVal]
  have hMap : ((mapComp tlAuthSigDdh (a1sInit2Dsl S b.q_total) :
        Comp pqAtomicOps pqAuthSigAndDdhIface [PB 32] _).eval (.cons pk .nil)) =
      (embedVal (.prod .unit a1sStTy) <$> (a1sInit2Dsl S b.q_total).eval
        (.cons (projVal (B 32) pk) .nil) : OracleComp AuthSigDdhSpec _) := by
    rw [hEnv, mapComp_auth_eval]
  rw [show (a1s2KindProg S b).init = a1s2KindInit S b from rfl] at hp
  simp only [a1s2KindInit, Comp.eval, mem_support_bind_iff, mem_support_pure_iff] at hp
  rcases hp with ⟨r₀, hr₀, rfl⟩
  have hr₀' : r₀ ∈ support (embedVal (.prod .unit a1sStTy) <$>
      (a1sInit2Dsl S b.q_total).eval (.cons (projVal (B 32) pk) .nil)) := hMap ▸ hr₀
  simp only [map_eq_bind_pure_comp, Function.comp_apply, a1sInit2Dsl, bindV, letV, Comp.letC,
    Comp.eval, mem_support_bind_iff, mem_support_pure_iff] at hr₀'
  rcases hr₀' with ⟨_, ⟨k, _, secb, _, r, _, rfl⟩, rfl⟩
  exact fgSimShadowInv_empty S b (Expr.var (.succ .zero))
    (.cons r (.cons secb (.cons k (.cons (projVal (B 32) pk) .nil)))) _

theorem a1s2KindProg_finish_sim (S : Setup) (b : QueryBudget) (c : Fin 4 → ℕ)
    (s' : a1s2ShadowStTy.denote) (bOut : Bool) :
    (∀ j, c j ≤ authSimBounds b j) → SigAuthInv S b c s' →
    (a1s2KindProg S b).finish.eval (.cons s' (.cons bOut .nil)) =
      (sigOldAtomicProg S b).finish.eval (.cons (forgetSig s') (.cons bOut .nil)) := by
  intro _ _
  have hEnv : (Env.cons (forgetSig s') (.cons bOut .nil) : Env (embedCtx [a1sStTy, .bool])) =
      embedEnv (.cons (projVal a1sStTy s'.1) (.cons bOut .nil)) := by
    simp [forgetSig, embedEnv, embedVal_projVal]; rfl
  have hRhs : (sigOldAtomicProg S b).finish.eval (.cons (forgetSig s') (.cons bOut .nil)) =
      (embedVal (.prod (B 1569) (B 64)) <$> a1sFinishDsl.eval
        (.cons (projVal a1sStTy s'.1) (.cons bOut .nil)) : OracleComp AuthSigDdhSpec _) := by
    change ((mapComp tlAuthSigDdh a1sFinishDsl :
        Comp pqAtomicOps pqAuthSigAndDdhIface (embedCtx [a1sStTy, .bool]) _).eval
      (.cons (forgetSig s') (.cons bOut .nil))) = _
    rw [hEnv, mapComp_auth_eval]
  rw [hRhs]; simp only [a1s2KindProg, a1s2KindFinish, a1sFinishDsl, Comp.eval, liftExpr1_eval]; rfl

private theorem logScan2C_fuel_eq (K₁ K₂ : ℕ) {Γ₁ Γ₂ Δ₁ Γ₁' Γ₂' Δ₂ : List (Ty pqSig)}
    (pa₁ : Var Γ₁ a1gParams2Ty) (sim₁ : Var Γ₂ fgSimTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁]
    (pa₂ : Var Γ₁' a1gParams2Ty) (sim₂ : Var Γ₂' fgSimTy) [h₁' : Ext Γ₁' Δ₂] [h₂' : Ext Γ₂' Δ₂]
    (off : ℕ) (env₁ : Env Δ₁) (env₂ : Env Δ₂) (hpa : env₁.get (h₁.wk pa₁) = env₂.get (h₁'.wk pa₂))
    (hsim : env₁.get (h₂.wk sim₁) = env₂.get (h₂'.wk sim₂))
    (h₁_le : (env₁.get (h₂.wk sim₁)).2.2.2.2.1.length ≤ K₁)
    (h₂_le : (env₁.get (h₂.wk sim₁)).2.2.2.2.1.length ≤ K₂) :
    (logScan2C K₁ pa₁ sim₁ off).eval env₁ = (logScan2C K₂ pa₂ sim₂ off).eval env₂ := by
  simp only [logScan2C, findMV, eMap, fsLog, slice32, pa2U, pa2V, v, eval_queryDdh, Comp.eval,
    Expr.eval_bytesTakeK, Expr.eval_bytesDrop, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_vs, Env.get_vz, hpa, ← hsim]
  rw [List.take_of_length_le h₁_le, List.take_of_length_le h₂_le,
    List.take_of_length_le (by simp [List.length_map]; exact h₁_le),
    List.take_of_length_le (by simp [List.length_map]; exact h₂_le)]

private theorem respCand2C_fuel_eq (S : Setup) (K₁ K₂ : ℕ) {Γ₁ Γ₂ Δ₁ Γ₁' Γ₂' Δ₂ : List (Ty pqSig)}
    (sim₁ : Var Γ₁ fgSimTy) (r₁ : Var Γ₂ respRecTy) [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁]
    (sim₂ : Var Γ₁' fgSimTy) (r₂ : Var Γ₂' respRecTy) [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂]
    (pk₁ : Expr pqxdhOps Δ₁ (B 32)) (pk₂ : Expr pqxdhOps Δ₂ (B 32)) (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hsim : env₁.get (Ext.wk sim₁) = env₂.get (Ext.wk sim₂)) (hr : env₁.get (Ext.wk r₁) = env₂.get (Ext.wk r₂))
    (hpk : pk₁.eval env₁ = pk₂.eval env₂) (h₁_le : (env₁.get (Ext.wk sim₁)).1.2.2.2.1.length ≤ K₁)
    (h₂_le : (env₁.get (Ext.wk sim₁)).1.2.2.2.1.length ≤ K₂) :
    (respCand2C S K₁ sim₁ r₁ pk₁).eval env₁ = (respCand2C S K₂ sim₂ r₂ pk₂).eval env₂ := by
  rw [respCand2C, respCand2C, queryPrimC_x25519_eval, queryPrimC_x25519_eval, hpk]
  suffices hSk : (eCaseOpt (eFind (min K₁ S.N_dh) (stSpks (fsBase (v sim₁)))
        fun e => nat2Eq (.fst (v e)) (.fst (v r₁))) (.litBytes 32 []) fun e => sbSpkSk (.snd (v e))).eval env₁ =
      (eCaseOpt (eFind (min K₂ S.N_dh) (stSpks (fsBase (v sim₂)))
        fun e => nat2Eq (.fst (v e)) (.fst (v r₂))) (.litBytes 32 []) fun e => sbSpkSk (.snd (v e))).eval env₂ by
    rw [hSk]
  simp only [eCaseOpt, eFind, fsBase, stSpks, sbSpkSk, nat2Eq, natEq, v, Expr.eval_litBytes,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hr, ← hsim]
  rw [take_min_left_of_length_le S.N_dh h₁_le, take_min_left_of_length_le S.N_dh h₂_le]; rfl

private theorem initDh1Cand2C_fuel_eq (S : Setup) (K₁ K₂ : ℕ) {Γ₁ Γ₂ Γ₃ Δ₁ Γ₁' Γ₂' Γ₃' Δ₂ : List (Ty pqSig)}
    (sim₁ : Var Γ₁ fgSimTy) (sp₁ : Var Γ₂ (.list (.prod (B 32) (B 32)))) (s₁ : Var Γ₃ authSessionEntryTy)
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₃ Δ₁] (sim₂ : Var Γ₁' fgSimTy) (sp₂ : Var Γ₂' (.list (.prod (B 32) (B 32))))
    (s₂ : Var Γ₃' authSessionEntryTy) [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂] [Ext Γ₃' Δ₂] (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hsim : env₁.get (Ext.wk sim₁) = env₂.get (Ext.wk sim₂)) (hsp : env₁.get (Ext.wk sp₁) = env₂.get (Ext.wk sp₂))
    (hs : env₁.get (Ext.wk s₁) = env₂.get (Ext.wk s₂))
    (hsp₁ : (env₁.get (Ext.wk sp₁)).length ≤ min K₁ S.N_dh) (hsp₂ : (env₁.get (Ext.wk sp₁)).length ≤ min K₂ S.N_dh)
    (hpw₁ : (env₁.get (Ext.wk sim₁)).2.2.2.2.2.2.length ≤ K₁) (hpw₂ : (env₁.get (Ext.wk sim₁)).2.2.2.2.2.2.length ≤ K₂)
    (hpr₁ : (env₁.get (Ext.wk sim₁)).1.2.2.1.length ≤ K₁) (hpr₂ : (env₁.get (Ext.wk sim₁)).1.2.2.1.length ≤ K₂) :
    (initDh1Cand2C S K₁ sim₁ sp₁ s₁).eval env₁ = (initDh1Cand2C S K₂ sim₂ sp₂ s₂).eval env₂ := by
  simp only [initDh1Cand2C, bindV, letV, Comp.letC, Comp.eval, pure_bind,
    queryPrimC_pow8_eval, queryPrimC_x25519_eval]
  have hPeer : (sePeerSpk (v s₁)).eval env₁ = (sePeerSpk (v s₂)).eval env₂ := by simp only [v, Expr.eval, hs]
  rw [hPeer]; congr 1; funext w
  have hSk : (eCaseOpt (eFind (min K₁ S.N_dh) (v sp₁) fun e =>
        .boolAnd (.boolNot (bytesEmpty (.fst (v e)))) (.bytesBeq (.snd (v e)) (v (.vz : Var ((B 32) :: Δ₁) (B 32)))))
      (eCaseOpt (eFind K₁ (fsPows (v sim₁)) fun e => .bytesBeq (.snd (v e)) (v (.vz : Var ((B 32) :: Δ₁) (B 32))))
        (.litBytes 32 []) fun e => .fst (v e)) fun e => .fst (v e)).eval (.cons w env₁) =
      (eCaseOpt (eFind (min K₂ S.N_dh) (v sp₂) fun e =>
        .boolAnd (.boolNot (bytesEmpty (.fst (v e)))) (.bytesBeq (.snd (v e)) (v (.vz : Var ((B 32) :: Δ₂) (B 32)))))
      (eCaseOpt (eFind K₂ (fsPows (v sim₂)) fun e => .bytesBeq (.snd (v e)) (v (.vz : Var ((B 32) :: Δ₂) (B 32))))
        (.litBytes 32 []) fun e => .fst (v e)) fun e => .fst (v e)).eval (.cons w env₂) := by
    simp only [eCaseOpt, eFind, bytesEmpty, fsPows, v, Expr.eval_litBytes, Expr.eval_bytesBeq, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, ← hsp, ← hsim,
      List.take_of_length_le hsp₁, List.take_of_length_le hsp₂, List.take_of_length_le hpw₁, List.take_of_length_le hpw₂]
  have hSid : ∀ (v₁ v₂ : (B 32).denote),
      (eCaseSum (seSid (v s₁)) (fun p => .fst (v p)) fun r => eCaseSum (v r) (fun p => .fst (v p))
        fun r => eCaseSum (v r) (fun p => .fst (v p)) fun p => .fst (v p)).eval (.cons v₁ (.cons w env₁)) =
      (eCaseSum (seSid (v s₂)) (fun p => .fst (v p)) fun r => eCaseSum (v r) (fun p => .fst (v p))
        fun r => eCaseSum (v r) (fun p => .fst (v p)) fun p => .fst (v p)).eval (.cons v₂ (.cons w env₂)) :=
    fun _ _ => by simp only [eCaseSum, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, hs]
  have hIk : ∀ (v₁ v₂ : (B 32).denote) (u₁ u₂ : ℕ), u₁ = u₂ →
      (eCaseOpt (eFind K₁ (stPrin (fsBase (v sim₁))) fun e =>
          natEq (.fst (v e)) (v (.vz : Var (.nat :: (B 32) :: (B 32) :: Δ₁) .nat)))
        (.litBytes 32 []) fun e => peIkAPk (.snd (v e))).eval
          (Env.cons (t := .nat) u₁ (Env.cons (t := B 32) v₁ (Env.cons (t := B 32) w env₁))) =
      (eCaseOpt (eFind K₂ (stPrin (fsBase (v sim₂))) fun e =>
          natEq (.fst (v e)) (v (.vz : Var (.nat :: (B 32) :: (B 32) :: Δ₂) .nat)))
        (.litBytes 32 []) fun e => peIkAPk (.snd (v e))).eval
          (Env.cons (t := .nat) u₂ (Env.cons (t := B 32) v₂ (Env.cons (t := B 32) w env₂))) := by
    intro _ _ _ _ hu; subst hu
    simp only [eCaseOpt, eFind, fsBase, stPrin, natEq, peIkAPk, v, Expr.eval_litBytes, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, ← hsim, List.take_of_length_le hpr₁, List.take_of_length_le hpr₂]
    rfl
  have hFst : ∀ {Δ : List (Ty pqSig)} (ik : (B 32).denote) (u : ℕ) (sk : (B 32).denote) (e : Env ((B 32) :: Δ)),
      (v (.vz : Var ((B 32) :: (B 32) :: Δ) (B 32))).eval
        (Env.cons (t := B 32) ik (Env.cons (t := .nat) u (Env.cons (t := B 32) sk e))) = sk := fun _ _ _ _ => rfl
  have hSnd : ∀ {Δ : List (Ty pqSig)} (ik : (B 32).denote) (u : ℕ) (sk : (B 32).denote) (e : Env ((B 32) :: Δ)),
      (v (.vz : Var ((B 32) :: .nat :: (B 32) :: (B 32) :: Δ) (B 32))).eval
        (Env.cons (t := B 32) ik (Env.cons (t := .nat) u (Env.cons (t := B 32) sk e))) = ik := fun _ _ _ _ => rfl
  rw [hFst, hSnd, hFst, hSnd, hSk, hIk _ _ _ _ (hSid _ _)]

private theorem findMap2C_congr {τ : Ty pqSig} (N₁ N₂ : ℕ) {Γ₁ Δ₁ Γ₁' Δ₂ : List (Ty pqSig)}
    (pa₁ : Var Γ₁ a1gParams2Ty) [Ext Γ₁ Δ₁] (pa₂ : Var Γ₁' a1gParams2Ty) [Ext Γ₁' Δ₂]
    (xs₁ : Expr pqxdhOps Δ₁ (.list τ)) (xs₂ : Expr pqxdhOps Δ₂ (.list τ))
    (f₁ : (x : Var (τ :: .opt (B 32) :: Δ₁) τ) → Comp pqxdhOps pqGapDhIface (τ :: .opt (B 32) :: Δ₁) (B 32))
    (f₂ : (x : Var (τ :: .opt (B 32) :: Δ₂) τ) → Comp pqxdhOps pqGapDhIface (τ :: .opt (B 32) :: Δ₂) (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂) (hpa : env₁.get (Ext.wk pa₁) = env₂.get (Ext.wk pa₂))
    (hxs : (xs₁.eval env₁).take N₁ = (xs₂.eval env₂).take N₂)
    (hf : ∀ x acc, (f₁ .vz).eval (.cons x (.cons acc env₁)) = (f₂ .vz).eval (.cons x (.cons acc env₂))) :
    (findMap2C pa₁ N₁ xs₁ f₁).eval env₁ = (findMap2C pa₂ N₂ xs₂ f₂).eval env₂ := by
  simp only [findMap2C, foldMV, caseOptV, bindV, eval_queryDdh, pa2U, pa2V,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, hpa, hxs]
  congr 1; funext x acc; cases acc with | some _ => rfl | none => rw [hf x none]; rfl

theorem a1g2KindProg_finish_sim (S : Setup) (b : QueryBudget) (c : Fin 4 → ℕ)
    (s' : a1g2ShadowStTy.denote) (bOut : Bool) :
    (∀ j, c j ≤ authSimBounds b j) → GdhAuthInv S b c s' →
    (a1g2KindProg S b).finish.eval (.cons s' (.cons bOut .nil)) =
      (gdhOldAtomicProg S b).finish.eval (.cons (forgetGdh s') (.cons bOut .nil)) := by
  intro _ hInv
  let F := AuthKindFuels.ofBudget S b
  let gst₀ : gs2Ty.denote := projVal gs2Ty s'.1.1
  let sim₀ := gst₀.2
  have hSimEmbed : embedVal fgSimTy sim₀ = s'.1.1.2 := embedVal_projVal fgSimTy s'.1.1.2
  have hb₀ : AuthBaseValOnlineBounded (c 0) sim₀.1 := by
    rw [← AuthBaseAtomOnlineBounded.iff_embedVal,
      show embedVal authStateTy sim₀.1 = s'.1.1.2.1 from embedVal_projVal authStateTy s'.1.1.2.1]
    exact hInv.base_online
  have hKon : c 0 ≤ F.K_on := by have := hInv.counter_inv.on_le; dsimp only [F, AuthKindFuels.ofBudget]; omega
  have hMon : c 0 ≤ F.M_on := by simpa only [F, AuthKindFuels.K_on_eq_M_on] using hKon
  have hQtotOn : F.M_on ≤ b.q_total := Nat.min_le_right _ _
  have hQtotKon : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hMoff : c 1 ≤ F.M_off := by have := hInv.counter_inv.ro_le; dsimp only [F, AuthKindFuels.ofBudget]; omega
  have hQtotOff : F.M_off ≤ b.q_total := Nat.min_le_right _ _
  have hLogLen : sim₀.2.2.2.2.1.length ≤ c 1 := by
    have hL := hInv.log_len; rw [← hSimEmbed] at hL; simpa only [fgSimTy, embedVal, List.length_map] using hL
  have hRespLen : sim₀.2.2.2.2.2.1.length ≤ c 0 := by
    have hR := hInv.resp_len; rw [← hSimEmbed] at hR; simpa only [fgSimTy, embedVal, List.length_map] using hR
  have hPowsLen : sim₀.2.2.2.2.2.2.length ≤ c 0 := by
    have hP := hInv.pows_len; rw [← hSimEmbed] at hP; simpa only [fgSimTy, embedVal, List.length_map] using hP
  have hEnv : (Env.cons (forgetGdh s') (.cons bOut .nil) : Env (embedCtx [a1g2StTy, .bool])) =
      embedEnv (.cons (projVal a1g2StTy s'.1) (.cons bOut .nil)) := by
    simp [forgetGdh, embedEnv, embedVal_projVal]; rfl
  have hRhs : (gdhOldAtomicProg S b).finish.eval (.cons (forgetGdh s') (.cons bOut .nil)) =
      (embedVal (B 32) <$> (a1g2FinishDsl S b.q_total).eval
        (.cons (projVal a1g2StTy s'.1) (.cons bOut .nil)) : OracleComp AuthSigDdhSpec _) := by
    change ((mapComp tlAuthSigDdh (a1g2FinishDsl S b.q_total) :
        Comp pqAtomicOps pqAuthSigAndDdhIface (embedCtx [a1g2StTy, .bool]) _).eval
      (.cons (forgetGdh s') (.cons bOut .nil))) = _
    rw [hEnv, mapComp_auth_eval]
  have hLhs : (a1g2KindProg S b).finish.eval (.cons s' (.cons bOut .nil)) =
      (embedVal (B 32) <$> liftGdhToSign ((fgExtract2K S F).eval (.cons gst₀ .nil)) :
        OracleComp AuthSigDdhSpec _) :=
    liftGdh1_eval (Γ := [a1g2ShadowStTy, .bool]) (fgExtract2K S F) (.fst (.fst .v0)) (.cons s' (.cons bOut .nil))
  have hStep : (a1g2FinishDsl S b.q_total).eval (.cons (projVal a1g2StTy s'.1) (.cons bOut .nil)) =
      liftGdhToSign ((fgFinish2Dsl S b.q_total).eval (.cons gst₀ (.cons bOut .nil))) := by
    simp [a1g2FinishDsl, letV, Comp.letC, Comp.eval, renameComp_eval, pullEnv_twoVarRen,
      liftGdhComp_eval, Expr.eval, Var.vz, Var.vs, gst₀]; rfl
  suffices hCore : (fgExtract2K S F).eval (.cons gst₀ .nil) =
      (fgFinish2Dsl S b.q_total).eval (.cons gst₀ (.cons bOut .nil)) by rw [hLhs, hRhs, hStep, hCore]
  have hvz : ∀ {Γ : List (Ty pqSig)} {τ : Ty pqSig} (x : τ.denote) (e : Env Γ),
      (v (.vz : Var (τ :: Γ) τ)).eval (.cons x e) = x := fun _ _ => rfl
  simp only [fgExtract2K, fgFinish2Dsl, letV, Comp.letC, Comp.eval, pure_bind]
  rw [show ((v (.vz : Var [gs2Ty] gs2Ty)).fst.eval (.cons gst₀ .nil)) = gst₀.1 from rfl,
    show ((v (.vz : Var [gs2Ty] gs2Ty)).snd.eval (Env.cons (t := a1gParams2Ty) gst₀.1 (.cons gst₀ .nil))) = gst₀.2 from rfl,
    show ((Expr.var (.vz : Var [gs2Ty, .bool] gs2Ty)).fst.eval (.cons gst₀ (Env.cons (t := .bool) bOut .nil))) = gst₀.1 from rfl,
    show ((Expr.var (Var.vs (.vz : Var [gs2Ty, .bool] gs2Ty))).snd.eval
      (Env.cons (t := a1gParams2Ty) gst₀.1 (.cons gst₀ (Env.cons (t := .bool) bOut .nil)))) = gst₀.2 from rfl]
  simp only [fgExtract2C, bindV, caseOptV, Comp.eval, hvz]
  have hCond : (pa2Dh1 (v (.vz : Var [a1gParams2Ty, gs2Ty] a1gParams2Ty))).eval
      (Env.cons (t := fgSimTy) gst₀.2 (Env.cons (t := a1gParams2Ty) gst₀.1 (Env.cons (t := gs2Ty) gst₀ .nil))) =
      (pa2Dh1 (v (.vz : Var [a1gParams2Ty, gs2Ty, .bool] a1gParams2Ty))).eval
      (Env.cons (t := fgSimTy) gst₀.2 (Env.cons (t := a1gParams2Ty) gst₀.1
        (Env.cons (t := gs2Ty) gst₀ (Env.cons (t := .bool) bOut .nil)))) := by
    simp only [pa2Dh1, pa2Role, eCaseSum, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz]
  rw [hCond]
  have hBind : ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
      {x y : OracleComp spec α} {f g : α → OracleComp spec β},
      x = y → (∀ a, f a = g a) → (x >>= f) = (y >>= g) := by
    intro _ _ _ _ _ _ _ _ hxy hfg; subst hxy; exact congrArg (_ >>= ·) (funext hfg)
  have hMdh : F.M_dh = min F.M_on S.N_dh := rfl
  have hMsess : F.M_sess = min F.M_on S.N_sess_tot := rfl
  split_ifs
  · refine hBind (logScan2C_fuel_eq F.M_off b.q_total _ _ _ _ 32 _ _ rfl rfl
      (Nat.le_trans hLogLen hMoff) (Nat.le_trans hLogLen (Nat.le_trans hMoff hQtotOff))) fun fOpt => ?_
    cases fOpt with
    | some _ => rfl
    | none =>
      have hSpkEq : ∀ {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
          {oa ob : OracleComp spec α} {f g : α → OracleComp spec β}, oa = ob →
          (∀ a ∈ support oa, f a = g a) → (oa >>= f) = (ob >>= g) := by
        intro _ _ _ _ oa _ _ _ ho hfg; subst ho; exact bind_congr_of_forall_mem_support oa hfg
      refine hSpkEq ?_ fun spkPows hSpkPows => ?_
      · simp only [mapMV, fsBase, stSpks, sbSpkPk, sbSpkSk, queryPrimC_pow8_eval,
          Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v]
        change mapML _ (List.take F.M_dh sim₀.1.2.2.2.1) = mapML _ (List.take (min b.q_total S.N_dh) sim₀.1.2.2.2.1)
        rw [hMdh, take_min_left_of_length_le S.N_dh (Nat.le_trans hb₀.spkBundles_le hMon),
          take_min_left_of_length_le S.N_dh (Nat.le_trans hb₀.spkBundles_le (Nat.le_trans hMon hQtotOn))]
      have hSpkEqL : spkPows.length = (sim₀.1.2.2.2.1.take F.M_dh).length := mapML_support_length _ _ hSpkPows
      have hSpkPowsLen : spkPows.length ≤ S.N_dh := by rw [hSpkEqL, List.length_take, hMdh]; omega
      have hSpkBound : spkPows.length ≤ sim₀.1.2.2.2.1.length := by rw [hSpkEqL, List.length_take]; omega
      refine hBind (findMap2C_congr F.M_dh (min b.q_total S.N_dh) _ _ _ _ _ _ _ _ rfl
        (by simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v]
            change List.take F.M_dh sim₀.1.2.2.2.2.2.1 = List.take (min b.q_total S.N_dh) sim₀.1.2.2.2.2.2.1
            rw [hMdh, take_min_left_of_length_le S.N_dh (Nat.le_trans hb₀.sessions_le hMon),
              take_min_left_of_length_le S.N_dh (Nat.le_trans hb₀.sessions_le (Nat.le_trans hMon hQtotOn))])
        (fun _ _ => initDh1Cand2C_fuel_eq S F.K_on b.q_total _ _ _ _ _ _ _ _ rfl rfl rfl
          (Nat.le_min.mpr ⟨Nat.le_trans hSpkBound (Nat.le_trans hb₀.spkBundles_le hKon), hSpkPowsLen⟩)
          (Nat.le_min.mpr ⟨Nat.le_trans hSpkBound (Nat.le_trans hb₀.spkBundles_le (Nat.le_trans hKon hQtotKon)), hSpkPowsLen⟩)
          (Nat.le_trans hPowsLen hKon) (Nat.le_trans hPowsLen (Nat.le_trans hKon hQtotKon))
          (Nat.le_trans hb₀.principals_le hKon) (Nat.le_trans hb₀.principals_le (Nat.le_trans hKon hQtotKon))))
        fun f2Opt => ?_
      cases f2Opt with
      | some _ => rfl
      | none =>
        refine hBind (findMap2C_congr F.M_sess (min b.q_total S.N_sess_tot) _ _ _ _ _ _ _ _ rfl
          (by simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v]
              change List.take F.M_sess sim₀.2.2.2.2.2.1 = List.take (min b.q_total S.N_sess_tot) sim₀.2.2.2.2.2.1
              rw [hMsess, take_min_left_of_length_le S.N_sess_tot (Nat.le_trans hRespLen hMon),
                take_min_left_of_length_le S.N_sess_tot (Nat.le_trans hRespLen (Nat.le_trans hMon hQtotOn))])
          (fun _ _ => respCand2C_fuel_eq S F.K_on b.q_total _ _ _ _ _ _ _ _ rfl rfl rfl
            (Nat.le_trans hb₀.spkBundles_le hKon) (Nat.le_trans hb₀.spkBundles_le (Nat.le_trans hKon hQtotKon))))
          fun _ => rfl
  · refine hBind (logScan2C_fuel_eq F.M_off b.q_total _ _ _ _ 96 _ _ rfl rfl
      (Nat.le_trans hLogLen hMoff) (Nat.le_trans hLogLen (Nat.le_trans hMoff hQtotOff))) fun fOpt => ?_
    cases fOpt with
    | some _ => rfl
    | none =>
      refine hBind (findMap2C_congr F.M_dh (min b.q_total S.N_dh) _ _ _ _ _ _ _ _ rfl
        (by simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v]
            change List.take F.M_dh sim₀.1.2.2.2.2.2.1 = List.take (min b.q_total S.N_dh) sim₀.1.2.2.2.2.2.1
            rw [hMdh, take_min_left_of_length_le S.N_dh (Nat.le_trans hb₀.sessions_le hMon),
              take_min_left_of_length_le S.N_dh (Nat.le_trans hb₀.sessions_le (Nat.le_trans hMon hQtotOn))])
        (fun _ _ => by simp only [bytesEmpty, seEkASk, sePeerSpk, zero32, queryPrimC_x25519_eval,
          Comp.eval, Expr.eval_litBytes, Expr.eval_bytesBeq, Expr.eval, Ext.refl_wk, Env.get_vz, v]))
        fun f2Opt => ?_
      cases f2Opt with
      | some _ => rfl
      | none =>
        refine hBind (findMap2C_congr F.M_sess (min b.q_total S.N_sess_tot) _ _ _ _ _ _ _ _ rfl
          (by simp only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v]
              change List.take F.M_sess sim₀.2.2.2.2.2.1 = List.take (min b.q_total S.N_sess_tot) sim₀.2.2.2.2.2.1
              rw [hMsess, take_min_left_of_length_le S.N_sess_tot (Nat.le_trans hRespLen hMon),
                take_min_left_of_length_le S.N_sess_tot (Nat.le_trans hRespLen (Nat.le_trans hMon hQtotOn))])
          (fun _ _ => respCand2C_fuel_eq S F.K_on b.q_total _ _ _ _ _ _ _ _ rfl rfl rfl
            (Nat.le_trans hb₀.spkBundles_le hKon) (Nat.le_trans hb₀.spkBundles_le (Nat.le_trans hKon hQtotKon))))
          fun _ => rfl

/-! ## Misc `FgArmSim` Arm Obligations -/

private theorem legacyCoreArmEval_eq (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ) (t : AuthQuery S) :
    legacyCoreArmEval S b pa sim sigB t = embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
      (legacyCoreArmComp S b).eval
        (.cons (projVal a1gParams2Ty pa) (.cons (projVal fgSimTy sim) (.cons sigB (.cons (authQenc t) .nil)))) := by
  have hEnv : (Env.cons pa (.cons sim (.cons sigB (.cons ((authCodec S).qenc t) .nil))) :
      Env (embedCtx [a1gParams2Ty, fgSimTy, .nat, authQueryTy])) =
      embedEnv (.cons (projVal a1gParams2Ty pa)
        (.cons (projVal fgSimTy sim) (.cons sigB (.cons (authQenc t) .nil)))) := by
    rw [authQenc_eq]; simp only [embedEnv, embedVal_projVal]; rfl
  dsimp only [legacyCoreArmEval]; rw [hEnv, mapComp_auth_eval]; rfl

private theorem fgSimShadowInv_online_sim {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote}
    (t : AuthQuery S) (hOn : authSimPred S 0 t) (hNot1 : ¬ authSimPred S 1 t) (hNot2 : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j) (hInv : FgSimShadowInv S b c sim aux)
    (sim₀ : fgSimTy.denote) (hSim : embedVal fgSimTy sim₀ = sim)
    (base' : authStateTy.denote) (hb' : AuthBaseValOnlineBounded (c 0 + 1) base')
    (pows' : (Ty.list (.prod (B 32) (B 32))).denote) (hpows' : pows'.length ≤ c 0 + 1) :
    FgSimShadowInv S b (bumpPred (authSimPred S) c t)
      (embedVal fgSimTy
        (base', (sim₀.2.1, (sim₀.2.2.1, (sim₀.2.2.2.1, (sim₀.2.2.2.2.1, (sim₀.2.2.2.2.2.1, pows'))))))) aux := by
  have hbump0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp only [bumpPred, hOn, ↓reduceIte]
  have hbump1 : bumpPred (authSimPred S) c t 1 = c 1 := by simp only [bumpPred, hNot1, ↓reduceIte, Nat.add_zero]
  have hbump2 : bumpPred (authSimPred S) c t 2 = c 2 := by simp only [bumpPred, hNot2, ↓reduceIte, Nat.add_zero]
  have h21 : embedVal (.list fgPatchEntryTy) sim₀.2.1 = sim.2.1 := by rw [← hSim]; rfl
  have h221 : embedVal (.list rootEntryTy) sim₀.2.2.1 = sim.2.2.1 := by rw [← hSim]; rfl
  have h2221 : embedVal (.list (.prod (B 192) drKeyTy)) sim₀.2.2.2.1 = sim.2.2.2.1 := by rw [← hSim]; rfl
  have h22221 : embedVal (.list (B 192)) sim₀.2.2.2.2.1 = sim.2.2.2.2.1 := by rw [← hSim]; rfl
  have h222221 : embedVal (.list respRecTy) sim₀.2.2.2.2.2.1 = sim.2.2.2.2.2.1 := by rw [← hSim]; rfl
  refine { counter_inv := hInv.counter_inv.bump t hroom, base_online := ?_, pows_len := ?_,
           resp_len := ?_, log_len := ?_, fg_shadow := ?_, root_shadow := ?_, raw_rel := ?_, raw_len := ?_ }
  · change AuthBaseAtomOnlineBounded _ (embedVal authStateTy base')
    rw [hbump0, AuthBaseAtomOnlineBounded.iff_embedVal]; exact hb'
  · change (embedVal (.list (.prod (B 32) (B 32))) pows').length ≤ _
    rw [hbump0]; simpa only [embedVal, List.length_map] using hpows'
  · change (embedVal (.list respRecTy) sim₀.2.2.2.2.2.1).length ≤ _
    rw [h222221, hbump0]; exact Nat.le_trans hInv.resp_len (Nat.le_succ _)
  · change (embedVal (.list (B 192)) sim₀.2.2.2.2.1).length ≤ _; rw [h22221, hbump1]; exact hInv.log_len
  · change FgTableShadow S b _ _ (embedVal (.list fgPatchEntryTy) sim₀.2.1) _ _ _
    rw [h21, hbump0, hbump1]; obtain ⟨fgTagged, hRel, hSess, hRo, hTag, hV⟩ := hInv.fg_shadow
    exact ⟨fgTagged, hRel.mono_cap (by omega), by omega, by omega, by omega, hV⟩
  · change RootTableShadow S b _ _ (embedVal (.list rootEntryTy) sim₀.2.2.1) _ _ _
    rw [h221, hbump0, hbump2]; obtain ⟨rootTagged, hRel, hSess, hRo, hTag, hV⟩ := hInv.root_shadow
    exact ⟨rootTagged, hRel.mono_cap (by omega), by omega, by omega, by omega, hV⟩
  · change RoCacheRelB192 _ b.q_total _ (embedVal (.list (.prod (B 192) drKeyTy)) sim₀.2.2.2.1) _
    rw [h2221]; exact hInv.raw_rel
  · change (embedVal (.list (.prod (B 192) drKeyTy)) sim₀.2.2.2.1).length ≤ _
    rw [h2221, hbump1]; exact hInv.raw_len

private theorem inv_sim_bounds {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote}
    (hInv : FgSimShadowInv S b c sim aux) (sim₀ : fgSimTy.denote) (hSim : embedVal fgSimTy sim₀ = sim) :
    AuthBaseValOnlineBounded (c 0) sim₀.1 ∧ c 0 ≤ (AuthKindFuels.ofBudget S b).K_on ∧
    (AuthKindFuels.ofBudget S b).K_on ≤ b.q_total ∧ sim₀.2.2.2.2.2.2.length ≤ c 0 := by
  refine ⟨?_, by have := hInv.counter_inv.on_le; dsimp only [AuthKindFuels.ofBudget]; omega,
    AuthKindFuels.K_on_le_q_total S b, ?_⟩
  · rw [← AuthBaseAtomOnlineBounded.iff_embedVal, show embedVal authStateTy sim₀.1 = sim.1 by rw [← hSim]; rfl]
    exact hInv.base_online
  · have hP := hInv.pows_len; rw [← hSim] at hP; simpa only [fgSimTy, embedVal, List.length_map] using hP

private theorem liftGdhArm_eval {Γ : List (Ty pqAtomicSig)} {Arg : Ty pqSig}
    (legC : Comp pqxdhOps pqGapDhIface [Arg] (.prod authRespTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (argE : Expr pqAtomicOps (.prod .nat fgAuthShadowAuxTy :: Γ) (embedTy Arg)) (env : Env Γ) :
    (Comp.bind (.ret (.pair sigBE auxE)) (.bind (liftGdh1 legC argE)
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))).eval env =
    (fun rs => (embedVal authRespTy rs.1, ((embedVal fgSimTy rs.2, sigBE.eval env), auxE.eval env))) <$>
      liftGdhToSign (legC.eval (.cons (projVal Arg (argE.eval (.cons (sigBE.eval env, auxE.eval env) env))) .nil)) := by
  simp only [Comp.eval, Expr.eval, pure_bind]; rw [liftGdh1_eval]
  simp only [map_eq_bind_pure_comp]; erw [map_eq_bind_pure_comp, bind_assoc]; congr 1

private theorem liftGdhArm_fst_map {Γ : List (Ty pqAtomicSig)} {Arg : Ty pqSig}
    (legC : Comp pqxdhOps pqGapDhIface [Arg] (.prod authRespTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (argE : Expr pqAtomicOps (.prod .nat fgAuthShadowAuxTy :: Γ) (embedTy Arg)) (env : Env Γ) :
    (Prod.map id Prod.fst <$> (Comp.bind (.ret (.pair sigBE auxE)) (.bind (liftGdh1 legC argE)
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))).eval env :
      OracleComp AuthSigDdhSpec _) =
    (fun rs => embedVal (.prod authRespTy (.prod fgSimTy .nat)) (rs.1, (rs.2, sigBE.eval env))) <$>
      liftGdhToSign (legC.eval (.cons (projVal Arg (argE.eval (.cons (sigBE.eval env, auxE.eval env) env))) .nil)) := by
  rw [liftGdhArm_eval]; simp only [map_eq_bind_pure_comp]; erw [map_eq_bind_pure_comp, bind_assoc]; congr 1

private theorem mem_support_liftGdhArm {Γ : List (Ty pqAtomicSig)} {Arg : Ty pqSig}
    (legC : Comp pqxdhOps pqGapDhIface [Arg] (.prod authRespTy fgSimTy))
    (sigBE : Expr pqAtomicOps Γ .nat) (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (argE : Expr pqAtomicOps (.prod .nat fgAuthShadowAuxTy :: Γ) (embedTy Arg)) (env : Env Γ)
    {p : (embedTy authRespTy).denote × ((embedTy fgSimTy).denote × ℕ) × fgAuthShadowAuxTy.denote}
    (hp : p ∈ support (((Comp.bind (.ret (.pair sigBE auxE)) (.bind (liftGdh1 legC argE)
      (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.fst .v1)) (.snd .v1)))))).eval env :
      OracleComp AuthSigDdhSpec _))) :
    ∃ rs ∈ support (legC.eval (.cons (projVal Arg (argE.eval (.cons (sigBE.eval env, auxE.eval env) env))) .nil)),
      p = (embedVal authRespTy rs.1, ((embedVal fgSimTy rs.2, sigBE.eval env), auxE.eval env)) := by
  have hp' : p ∈ support ((fun rs => (embedVal authRespTy rs.1, ((embedVal fgSimTy rs.2, sigBE.eval env), auxE.eval env))) <$>
      liftGdhToSign (legC.eval (.cons (projVal Arg (argE.eval (.cons (sigBE.eval env, auxE.eval env) env))) .nil))) :=
    liftGdhArm_eval legC sigBE auxE argE env ▸ hp
  simp only [map_eq_bind_pure_comp, Function.comp_apply, mem_support_bind_iff, mem_support_pure_iff] at hp'
  rcases hp' with ⟨rs, hrs, rfl⟩; exact ⟨rs, mem_support_liftGdhToSign hrs, rfl⟩

theorem fgArmSim_initPrin (S : Setup) (b : QueryBudget) :
    FgArmSim S b AuthQuery.initPrin (armEval_initPrin S b) := by
  dsimp only [FgArmSim]; intro c pa sim sigB aux u _ hroom hInv; let F := AuthKindFuels.ofBudget S b
  suffices ∀ (sim₀ : fgSimTy.denote) (pa₀ : a1gParams2Ty.denote), embedVal fgSimTy sim₀ = sim →
      (((fun rs => embedVal (.prod authRespTy (.prod fgSimTy .nat)) (rs.1, (rs.2, sigB))) <$>
        liftGdhToSign ((a1gInitPrin2LegC F).eval (.cons (pa₀, (sim₀, u.val)) .nil)) :
        OracleComp SignalPqxdh.Security.GdhSignSimSpec _)) =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa₀ (.cons sim₀ (.cons sigB (.cons (authQenc (.initPrin u)) .nil)))) ∧
      ∀ rs ∈ support ((a1gInitPrin2LegC F).eval (.cons (pa₀, (sim₀, u.val)) .nil)),
        FgSimShadowInv S b (bumpPred (authSimPred S) c (.initPrin u)) (embedVal fgSimTy rs.2) aux by
    obtain ⟨hEq, hSup⟩ := this (projVal fgSimTy sim) (projVal a1gParams2Ty pa) (embedVal_projVal fgSimTy sim)
    have hTriple : projVal (.prod a1gParams2Ty (.prod fgSimTy .nat)) (pa, (sim, u.val)) =
      (projVal a1gParams2Ty pa, (projVal fgSimTy sim, u.val)) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [armEval_initPrin, fgCoreArm_initPrin]; rw [liftGdhArm_fst_map, legacyCoreArmEval_eq]
      simp only [exprRename, Expr.eval, Env.get]; rw [hTriple]; exact hEq
    · intro p hp; dsimp only [armEval_initPrin, fgCoreArm_initPrin] at hp
      obtain ⟨rs, hrs, rfl⟩ := mem_support_liftGdhArm (a1gInitPrin2LegC F) _ _ _ _ hp
      simp only [exprRename, Expr.eval, Env.get] at hrs ⊢; rw [hTriple] at hrs; exact hSup rs hrs
  intro sim₀ pa₀ hSim; obtain ⟨hb₀, hKon, hQtot, hPows₀⟩ := inv_sim_bounds hInv sim₀ hSim
  have hTake1 : List.take F.K_on sim₀.1.2.2.1 = sim₀.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.principals_le hKon)
  have hTake2 : List.take b.q_total sim₀.1.2.2.1 = sim₀.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.principals_le (Nat.le_trans hKon hQtot))
  refine ⟨?_, ?_⟩
  · simp only [a1gInitPrin2LegC, a1gInitPrin2C, legacyCoreArmComp, a1gPre2C, authQenc, aNone, aInitPrin,
      pa2Role, pa2U, peMk, fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stPrin, stUpd,
      eAny, eCaseSum, eval_natEq, Expr.eval_litBytes, eval_sampleBytes32C, eval_queryPrimC, letV, Comp.letC,
      bindV, caseSumV, liftGdhComp_eval, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs,
      Env.get_vz, v, pure_bind, map_eq_bind_pure_comp, bind_assoc]
    rw [hTake1, hTake2]; congr 1
  · intro out hrs'
    dsimp only [a1gInitPrin2LegC, a1gInitPrin2C, aNone, aInitPrin, pa2Role, pa2U, peMk, fsUpd, fsMk,
      fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stPrin, stUpd, eAny, eCaseSum] at hrs'
    simp only [letV, Comp.letC, bindV, eval_natEq, Expr.eval_litBytes, eval_sampleBytes32C, eval_queryPrimC,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind] at hrs'
    rw [hTake1] at hrs'
    cases hAny : List.any sim₀.1.2.2.1 (fun x => x.1 == u.val) with
    | true =>
      simp only [hAny, ↓reduceIte] at hrs'; erw [mem_support_pure_iff] at hrs'; rcases hrs' with ⟨rfl, rfl⟩
      simpa only [hSim] using hInv.bump_unchanged (AuthQuery.initPrin u) hroom
    | false =>
      simp only [hAny, Bool.false_eq_true, ↓reduceIte] at hrs'
      erw [mem_support_bind_iff] at hrs'; obtain ⟨s0, _, hrs'⟩ := hrs'
      erw [mem_support_bind_iff] at hrs'; obtain ⟨pk0, _, hrs'⟩ := hrs'
      erw [mem_support_pure_iff] at hrs'; rcases hrs' with ⟨rfl, rfl⟩
      refine fgSimShadowInv_online_sim (AuthQuery.initPrin u) trivial nofun nofun hroom hInv sim₀ hSim
        _ ?_ _ (Nat.le_trans hPows₀ (Nat.le_succ _))
      have hb1 := hb₀.mono (Nat.le_succ _)
      exact ⟨by simpa only [List.length_cons] using Nat.succ_le_succ hb₀.principals_le,
        hb1.spkBundles_le, hb1.opkEntries_le, hb1.sessions_le, hb1.usedSendSessions_le, hb1.usedRecvOPK_le,
        hb1.usedRecvNoOPK_le, hb1.seenKyberBaseKeys_le, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
        hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩

theorem fgArmSim_corruptIK (S : Setup) (b : QueryBudget) :
    FgArmSim S b AuthQuery.corruptIK (armEval_corruptIK S b) := by
  dsimp only [FgArmSim]; intro c pa sim sigB aux u _ hroom hInv; let F := AuthKindFuels.ofBudget S b
  suffices ∀ (sim₀ : fgSimTy.denote) (pa₀ : a1gParams2Ty.denote), embedVal fgSimTy sim₀ = sim →
      (((fun rs => embedVal (.prod authRespTy (.prod fgSimTy .nat)) (rs.1, (rs.2, sigB))) <$>
        liftGdhToSign ((fgCorruptLegC F).eval (.cons (sim₀, u.val) .nil)) :
        OracleComp SignalPqxdh.Security.GdhSignSimSpec _)) =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa₀ (.cons sim₀ (.cons sigB (.cons (authQenc (.corruptIK u)) .nil)))) ∧
      ∀ rs ∈ support ((fgCorruptLegC F).eval (.cons (sim₀, u.val) .nil)),
        FgSimShadowInv S b (bumpPred (authSimPred S) c (.corruptIK u)) (embedVal fgSimTy rs.2) aux by
    obtain ⟨hEq, hSup⟩ := this (projVal fgSimTy sim) (projVal a1gParams2Ty pa) (embedVal_projVal fgSimTy sim)
    have hPair : projVal (.prod fgSimTy .nat) (sim, u.val) = (projVal fgSimTy sim, u.val) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [armEval_corruptIK, fgCoreArm_corrupt]; rw [liftGdhArm_fst_map, legacyCoreArmEval_eq]
      simp only [exprRename, Expr.eval, Env.get]; rw [hPair]; exact hEq
    · intro p hp; dsimp only [armEval_corruptIK, fgCoreArm_corrupt] at hp
      obtain ⟨rs, hrs, rfl⟩ := mem_support_liftGdhArm (fgCorruptLegC F) _ _ _ _ hp
      simp only [exprRename, Expr.eval, Env.get] at hrs ⊢; rw [hPair] at hrs; exact hSup rs hrs
  intro sim₀ pa₀ hSim; obtain ⟨hb₀, hKon, hQtot, hPows₀⟩ := inv_sim_bounds hInv sim₀ hSim
  have hTake1 : List.take F.K_on sim₀.1.2.2.1 = sim₀.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.principals_le hKon)
  have hTake2 : List.take b.q_total sim₀.1.2.2.1 = sim₀.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.principals_le (Nat.le_trans hKon hQtot))
  refine ⟨?_, ?_⟩
  · simp only [fgCorruptLegC, legacyCoreArmComp, a1gPre2C, fgStep2C, onBaseF, corruptB, authQenc,
      rs, aNone, aCorr, fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows,
      stPrin, stUpd, peSecIKA0, peSecIKAsign, peUpd, eFind, eMap, eval_natEq,
      letV, Comp.letC, bindV, caseOptV, Comp.caseOptC, caseSumV, Comp.eval_liftChal, liftGdhComp_eval,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v,
      pure_bind, map_eq_bind_pure_comp, bind_assoc]
    rw [hTake1, hTake2]; congr 1
  · intro out hrs'
    dsimp only [fgCorruptLegC, onBaseF, corruptB, rs, aNone, aCorr, fsUpd, fsMk, fsBase,
      fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stPrin, stUpd, peSecIKA0, peSecIKAsign, peUpd, eFind, eMap] at hrs'
    simp only [letV, Comp.letC, bindV, caseOptV, Comp.caseOptC, Comp.eval_liftChal, eval_natEq,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind] at hrs'
    rw [hTake1] at hrs'
    cases hFind : List.find? (fun a => a.1 == u.val) sim₀.1.2.2.1 with
    | none =>
      simp only [hFind, embedPrim_pure, pure_bind, mem_support_pure_iff] at hrs'; rcases hrs' with ⟨rfl, rfl⟩
      simpa only [hSim] using hInv.bump_unchanged (AuthQuery.corruptIK u) hroom
    | some _ =>
      simp only [hFind, embedPrim_pure, pure_bind, mem_support_pure_iff] at hrs'; rcases hrs' with ⟨rfl, rfl⟩
      refine fgSimShadowInv_online_sim (AuthQuery.corruptIK u) trivial nofun nofun hroom hInv sim₀ hSim
        _ ?_ _ (Nat.le_trans hPows₀ (Nat.le_succ _))
      have hb1 := hb₀.mono (Nat.le_succ _)
      exact ⟨by simpa only [List.length_map] using Nat.le_trans hb₀.principals_le (Nat.le_succ _),
        hb1.spkBundles_le, hb1.opkEntries_le, hb1.sessions_le, hb1.usedSendSessions_le, hb1.usedRecvOPK_le,
        hb1.usedRecvNoOPK_le, hb1.seenKyberBaseKeys_le, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
        hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩

private theorem liftCsArm_eval {Γ : List (Ty pqAtomicSig)} {Arg : Ty pqSig}
    (legC : Comp pqxdhOps pqSigAndDdhIface [Arg] (.prod authRespTy (.prod fgSimTy .nat)))
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (argE : Expr pqAtomicOps (fgAuthShadowAuxTy :: Γ) (embedTy Arg)) (env : Env Γ) :
    (Comp.bind (.ret auxE) (.bind (liftCs1 legC argE)
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) .v1))))).eval env =
    (fun rsb => (embedVal authRespTy rsb.1, ((embedVal fgSimTy rsb.2.1, rsb.2.2), auxE.eval env))) <$>
      legC.eval (.cons (projVal Arg (argE.eval (.cons (auxE.eval env) env))) .nil) := by
  simp only [Comp.eval, Expr.eval, pure_bind]; rw [liftCs1_eval]
  simp only [map_eq_bind_pure_comp]; erw [map_eq_bind_pure_comp, bind_assoc]; congr 1

private theorem liftCsArm_fst_map {Γ : List (Ty pqAtomicSig)} {Arg : Ty pqSig}
    (legC : Comp pqxdhOps pqSigAndDdhIface [Arg] (.prod authRespTy (.prod fgSimTy .nat)))
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (argE : Expr pqAtomicOps (fgAuthShadowAuxTy :: Γ) (embedTy Arg)) (env : Env Γ) :
    (Prod.map id Prod.fst <$> (Comp.bind (.ret auxE) (.bind (liftCs1 legC argE)
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) .v1))))).eval env : OracleComp AuthSigDdhSpec _) =
    embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
      legC.eval (.cons (projVal Arg (argE.eval (.cons (auxE.eval env) env))) .nil) := by
  rw [liftCsArm_eval]; simp only [map_eq_bind_pure_comp]; erw [map_eq_bind_pure_comp, bind_assoc]; congr 1

private theorem mem_support_liftCsArm {Γ : List (Ty pqAtomicSig)} {Arg : Ty pqSig}
    (legC : Comp pqxdhOps pqSigAndDdhIface [Arg] (.prod authRespTy (.prod fgSimTy .nat)))
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (argE : Expr pqAtomicOps (fgAuthShadowAuxTy :: Γ) (embedTy Arg)) (env : Env Γ)
    {p : (embedTy authRespTy).denote × ((embedTy fgSimTy).denote × ℕ) × fgAuthShadowAuxTy.denote}
    (hp : p ∈ support (((Comp.bind (.ret auxE) (.bind (liftCs1 legC argE)
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) .v1))))).eval env : OracleComp AuthSigDdhSpec _))) :
    ∃ rsb ∈ support (legC.eval (.cons (projVal Arg (argE.eval (.cons (auxE.eval env) env))) .nil)),
      p = (embedVal authRespTy rsb.1, ((embedVal fgSimTy rsb.2.1, rsb.2.2), auxE.eval env)) := by
  have hp' : p ∈ support ((fun rsb => (embedVal authRespTy rsb.1, ((embedVal fgSimTy rsb.2.1, rsb.2.2), auxE.eval env))) <$>
      legC.eval (.cons (projVal Arg (argE.eval (.cons (auxE.eval env) env))) .nil)) :=
    liftCsArm_eval legC auxE argE env ▸ hp
  simp only [map_eq_bind_pure_comp] at hp'
  erw [mem_support_bind_iff] at hp'; obtain ⟨rsb, hrsb, hp'⟩ := hp'
  erw [mem_support_pure_iff] at hp'; exact ⟨rsb, hrsb, hp'⟩

theorem fgArmSim_genSPK (S : Setup) (b : QueryBudget) :
    FgArmSim S b (fun p => AuthQuery.genSPK p.1 p.2) (armEval_genSPK S b) := by
  dsimp only [FgArmSim]; intro c pa sim sigB aux p _ hroom hInv
  let F := AuthKindFuels.ofBudget S b; let x0 : ℕ × ℕ := (p.1.val, p.2.val)
  suffices ∀ (sim₀ : fgSimTy.denote) (pa₀ : a1gParams2Ty.denote), embedVal fgSimTy sim₀ = sim →
      (a1gGenSpk2LegC F).eval (.cons (pa₀, (sim₀, (sigB, x0))) .nil) =
        (legacyCoreArmComp S b).eval (.cons pa₀ (.cons sim₀ (.cons sigB (.cons (authQenc (.genSPK p.1 p.2)) .nil)))) ∧
      ∀ rsb ∈ support ((a1gGenSpk2LegC F).eval (.cons (pa₀, (sim₀, (sigB, x0))) .nil)),
        FgSimShadowInv S b (bumpPred (authSimPred S) c (.genSPK p.1 p.2)) (embedVal fgSimTy rsb.2.1) aux by
    obtain ⟨hEq, hSup⟩ := this (projVal fgSimTy sim) (projVal a1gParams2Ty pa) (embedVal_projVal fgSimTy sim)
    have hQuad : projVal (.prod a1gParams2Ty (.prod fgSimTy (.prod .nat (.prod .nat .nat))))
        (pa, (sim, (sigB, x0))) = (projVal a1gParams2Ty pa, (projVal fgSimTy sim, (sigB, x0))) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [armEval_genSPK, fgCoreArm_genSPK]; rw [liftCsArm_fst_map, legacyCoreArmEval_eq]
      simp only [exprRename, Expr.eval, Env.get]; rw [hQuad, hEq]
    · intro out hp; dsimp only [armEval_genSPK, fgCoreArm_genSPK] at hp
      obtain ⟨rsb, hrsb, rfl⟩ := mem_support_liftCsArm (a1gGenSpk2LegC F) _ _ _ hp
      simp only [exprRename, Expr.eval, Env.get] at hrsb ⊢; rw [hQuad] at hrsb; exact hSup rsb hrsb
  intro sim₀ ⟨U₀, V₀, role₀, ts₀⟩ hSim
  obtain ⟨hb₀, hKon, hQtot, hPows₀⟩ := inv_sim_bounds hInv sim₀ hSim
  have hSpk1 : List.take F.K_on sim₀.1.2.2.2.1 = sim₀.1.2.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.spkBundles_le hKon)
  have hSpk2 : List.take b.q_total sim₀.1.2.2.2.1 = sim₀.1.2.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.spkBundles_le (Nat.le_trans hKon hQtot))
  have hPrin1 : List.take F.K_on sim₀.1.2.2.1 = sim₀.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.principals_le hKon)
  have hPrin2 : List.take b.q_total sim₀.1.2.2.1 = sim₀.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.principals_le (Nat.le_trans hKon hQtot))
  have hSpkStep : ∀ spk', List.length spk' ≤ c 0 + 1 →
      FgSimShadowInv S b (bumpPred (authSimPred S) c (.genSPK p.1 p.2))
        (embedVal fgSimTy ((sim₀.1.1, sim₀.1.2.1, sim₀.1.2.2.1, spk', sim₀.1.2.2.2.2),
          (sim₀.2.1, (sim₀.2.2.1, (sim₀.2.2.2.1, (sim₀.2.2.2.2.1, (sim₀.2.2.2.2.2.1, sim₀.2.2.2.2.2.2))))))) aux := by
    intro spk' hSpkL
    refine fgSimShadowInv_online_sim (AuthQuery.genSPK p.1 p.2) trivial nofun nofun hroom hInv sim₀ hSim
      _ ?_ _ (Nat.le_trans hPows₀ (Nat.le_succ _))
    have hb1 := hb₀.mono (Nat.le_succ _)
    exact ⟨hb1.principals_le, hSpkL, hb1.opkEntries_le, hb1.sessions_le, hb1.usedSendSessions_le,
      hb1.usedRecvOPK_le, hb1.usedRecvNoOPK_le, hb1.seenKyberBaseKeys_le, hb1.sentOPKEvents_le,
      hb1.sentNoOPKEvents_le, hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩
  have hFgSup : ∀ {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} (role' : _)
      (paV : Var Γ₁ a1gParams2Ty) (simV : Var Γ₂ fgSimTy) (xV : Var Γ₃ (.prod .nat .nat))
      [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] (env : Env Δ),
      env.get (Ext.wk paV) = (U₀, (V₀, (role', ts₀))) → env.get (Ext.wk simV) = sim₀ → env.get (Ext.wk xV) = x0 →
      ∀ r ∈ support ((fgGenSpk2C F.K_on paV simV xV).eval env),
        FgSimShadowInv S b (bumpPred (authSimPred S) c (.genSPK p.1 p.2)) (embedVal fgSimTy r.2) aux := by
    intro _ _ _ _ _ paV simV xV _ _ _ env hPa hSimV hXV r hr
    simp only [fgGenSpk2C, x0, aNone, aBundle, buMk, sbMk, peIkAPk, peSecIKAsign, pa2TS, pa2V,
      fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stSpks, stPrin, stUpd,
      eAny, eFind, eCaseOpt, nat2Eq, eval_natEq, Expr.eval_litBytes, Expr.eval_u32OfNat, encEC_eval,
      encKEM_eval, eval_sampleBytes32C, eval_sampleRandom64C, eval_queryPrimC, letV, Comp.letC, bindV,
      caseOptV, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vs, Var.vz, Env.get, v,
      hPa, hSimV, hXV, pure_bind] at hr
    rw [hSpk1, hPrin1] at hr
    cases hAny : List.any sim₀.1.2.2.2.1 (fun e => (e.1.1 == p.1.val && e.1.2 == p.2.val)) with
    | true =>
      simp only [hAny, ↓reduceIte] at hr; erw [mem_support_pure_iff] at hr; rcases hr with ⟨rfl, rfl⟩
      simpa only [hSim] using hInv.bump_unchanged (AuthQuery.genSPK p.1 p.2) hroom
    | false =>
      simp only [hAny, Bool.false_eq_true, ↓reduceIte] at hr
      cases hFind : List.find? (fun a => a.1 == p.1.val) sim₀.1.2.2.1 with
      | none =>
        rw [hFind] at hr; erw [mem_support_pure_iff] at hr; rcases hr with ⟨rfl, rfl⟩
        simpa only [hSim] using hInv.bump_unchanged (AuthQuery.genSPK p.1 p.2) hroom
      | some _ =>
        rw [hFind] at hr; dsimp only at hr
        erw [mem_support_bind_iff] at hr; obtain ⟨skRaw, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨pkRaw, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨r1, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨sig1, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨seed, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨kp, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨r2, _, hr⟩ := hr
        erw [mem_support_bind_iff] at hr; obtain ⟨sig2, _, hr⟩ := hr
        erw [mem_support_pure_iff] at hr; rcases hr with ⟨rfl, rfl⟩
        exact hSpkStep _ (by simpa only [List.length_cons] using Nat.succ_le_succ hb₀.spkBundles_le)
  refine ⟨?_, ?_⟩
  · simp only [a1gGenSpk2LegC, legacyCoreArmComp, a1gPre2C, fgStep2C, authQenc, x0,
      pa2Role, eCaseSum, eval_natEq, letV, Comp.letC, bindV, caseSumV,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind]
    cases role₀ with
    | inr _ =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, Comp.eval, Expr.eval,
        Env.get_vs, Env.get_vz, liftGdhComp_eval]
      congr 1; congr 1
      simp only [fgGenSpk2C, aNone, aBundle, buMk, sbMk, peIkAPk, peSecIKAsign, pa2TS, pa2V,
        fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stSpks, stPrin, stUpd,
        eAny, eFind, eCaseOpt, nat2Eq, eval_natEq, Expr.eval_litBytes, Expr.eval_u32OfNat, encEC_eval,
        encKEM_eval, eval_sampleBytes32C, eval_sampleRandom64C, eval_queryPrimC, letV, Comp.letC, bindV,
        caseOptV, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind,
        hSpk1, hSpk2, hPrin1, hPrin2]; rfl
    | inl uT =>
      simp only
      by_cases hEqU : (p.1.val == uT) = true
      · simp only [hEqU, ↓reduceIte, bind_assoc, pure_bind, bind_pure]
        simp only [a1gGenSpk2C, aNone, aBundle, buMk, sbMk, peIkAPk, pa2TS, pa2V,
          fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stSpks, stPrin, stUpd,
          eAny, eFind, eCaseOpt, nat2Eq, eval_natEq, Expr.eval_litBytes, Expr.eval_u32OfNat,
          encEC_eval, encKEM_eval, eval_sampleBytes32C, eval_sampleRandom64C, eval_queryPrimC,
          sigChalQ_dsl_eval, letV, Comp.letC, bindV, caseOptV, Comp.eval, Expr.eval,
          Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind,
          hSpk1, hSpk2, hPrin1, hPrin2]; rfl
      · have hEqUf : (p.1.val == uT) = false := Bool.eq_false_iff.mpr hEqU
        simp only [hEqUf, Bool.false_eq_true, ↓reduceIte, pure_bind, Comp.eval, Expr.eval,
          Env.get_vs, Env.get_vz, liftGdhComp_eval]
        congr 1; congr 1
        simp only [fgGenSpk2C, aNone, aBundle, buMk, sbMk, peIkAPk, peSecIKAsign, pa2TS, pa2V,
          fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stSpks, stPrin, stUpd,
          eAny, eFind, eCaseOpt, nat2Eq, eval_natEq, Expr.eval_litBytes, Expr.eval_u32OfNat, encEC_eval,
          encKEM_eval, eval_sampleBytes32C, eval_sampleRandom64C, eval_queryPrimC, letV, Comp.letC, bindV,
          caseOptV, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind,
          hSpk1, hSpk2, hPrin1, hPrin2]; rfl
  · intro out hrsb
    simp only [a1gGenSpk2LegC, x0, pa2Role, eCaseSum, letV, Comp.letC, bindV, eval_natEq,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vs, Var.vz, Env.get, v, pure_bind] at hrsb
    cases role₀ with
    | inr _ =>
      simp only [Bool.false_eq_true, ↓reduceIte, liftGdhComp_eval] at hrsb
      erw [mem_support_bind_iff] at hrsb; obtain ⟨r, hr0, hrsb⟩ := hrsb
      erw [mem_support_pure_iff] at hrsb; rcases hrsb with ⟨rfl, rfl, rfl⟩
      exact hFgSup _ _ _ _ _ rfl rfl rfl r (mem_support_liftGdhToSign hr0)
    | inl uT =>
      simp only at hrsb
      by_cases hEqU : (p.1.val == uT) = true
      · simp only [hEqU, ↓reduceIte, a1gGenSpk2C, aNone, aBundle, buMk, sbMk, peIkAPk, pa2TS, pa2V,
          fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stSpks, stPrin, stUpd,
          eAny, eFind, eCaseOpt, nat2Eq, eval_natEq, Expr.eval_litBytes, Expr.eval_u32OfNat, encEC_eval,
          encKEM_eval, eval_sampleBytes32C, eval_sampleRandom64C, eval_queryPrimC, sigChalQ_dsl_eval,
          letV, Comp.letC, bindV, caseOptV, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
          Var.vs, Var.vz, Env.get, v, pure_bind] at hrsb
        rw [hSpk1, hPrin1] at hrsb
        cases hAny : List.any sim₀.1.2.2.2.1 (fun e => (e.1.1 == p.1.val && e.1.2 == p.2.val)) with
        | true =>
          simp only [hAny, ↓reduceIte] at hrsb; erw [mem_support_pure_iff] at hrsb; rcases hrsb with ⟨rfl, rfl, rfl⟩
          simpa only [hSim] using hInv.bump_unchanged (AuthQuery.genSPK p.1 p.2) hroom
        | false =>
          simp only [hAny, Bool.false_eq_true, ↓reduceIte] at hrsb
          cases hFind : List.find? (fun a => a.1 == p.1.val) sim₀.1.2.2.1 with
          | none =>
            rw [hFind] at hrsb; erw [mem_support_pure_iff] at hrsb; rcases hrsb with ⟨rfl, rfl, rfl⟩
            simpa only [hSim] using hInv.bump_unchanged (AuthQuery.genSPK p.1 p.2) hroom
          | some _ =>
            rw [hFind] at hrsb; dsimp only at hrsb
            cases hSigB : (sigB == 0) with
            | true =>
              simp only [hSigB, ↓reduceIte] at hrsb; erw [mem_support_pure_iff] at hrsb; rcases hrsb with ⟨rfl, rfl, rfl⟩
              simpa only [hSim] using hInv.bump_unchanged (AuthQuery.genSPK p.1 p.2) hroom
            | false =>
              simp only [hSigB, Bool.false_eq_true, ↓reduceIte] at hrsb
              erw [mem_support_bind_iff] at hrsb; obtain ⟨skRaw, _, hrsb⟩ := hrsb
              erw [mem_support_bind_iff] at hrsb; obtain ⟨pkRaw, _, hrsb⟩ := hrsb
              erw [mem_support_bind_iff] at hrsb; obtain ⟨sig1, _, hrsb⟩ := hrsb
              erw [mem_support_bind_iff] at hrsb; obtain ⟨seed, _, hrsb⟩ := hrsb
              erw [mem_support_bind_iff] at hrsb; obtain ⟨kp, _, hrsb⟩ := hrsb
              erw [mem_support_bind_iff] at hrsb; obtain ⟨sig2, _, hrsb⟩ := hrsb
              erw [mem_support_pure_iff] at hrsb; rcases hrsb with ⟨rfl, rfl, rfl⟩
              exact hSpkStep _ (by simpa only [List.length_cons] using Nat.succ_le_succ hb₀.spkBundles_le)
      · simp only [hEqU, liftGdhComp_eval] at hrsb
        erw [mem_support_bind_iff] at hrsb; obtain ⟨r, hr0, hrsb⟩ := hrsb
        erw [mem_support_pure_iff] at hrsb; rcases hrsb with ⟨rfl, rfl, rfl⟩
        exact hFgSup _ _ _ _ _ rfl rfl rfl r (mem_support_liftGdhToSign hr0)

theorem fgArmSim_genOPK (S : Setup) (b : QueryBudget) :
    FgArmSim S b (fun p => AuthQuery.genOPK p.1 p.2.1 p.2.2) (armEval_genOPK S b) := by
  dsimp only [FgArmSim]; intro c pa sim sigB aux p _ hroom hInv
  let F := AuthKindFuels.ofBudget S b; let x0 : ℕ × ℕ × ℕ := (p.1.val, (p.2.1.val, p.2.2.val))
  suffices ∀ (sim₀ : fgSimTy.denote) (pa₀ : a1gParams2Ty.denote), embedVal fgSimTy sim₀ = sim →
      (((fun rs => embedVal (.prod authRespTy (.prod fgSimTy .nat)) (rs.1, (rs.2, sigB))) <$>
        liftGdhToSign ((fgGenOpkLegC F).eval (.cons (sim₀, x0) .nil)) :
        OracleComp SignalPqxdh.Security.GdhSignSimSpec _)) =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval
            (.cons pa₀ (.cons sim₀ (.cons sigB (.cons (authQenc (.genOPK p.1 p.2.1 p.2.2)) .nil)))) ∧
      ∀ rs ∈ support ((fgGenOpkLegC F).eval (.cons (sim₀, x0) .nil)),
        FgSimShadowInv S b (bumpPred (authSimPred S) c (.genOPK p.1 p.2.1 p.2.2)) (embedVal fgSimTy rs.2) aux by
    obtain ⟨hEq, hSup⟩ := this (projVal fgSimTy sim) (projVal a1gParams2Ty pa) (embedVal_projVal fgSimTy sim)
    have hPair : projVal (.prod fgSimTy (.prod .nat (.prod .nat .nat))) (sim, x0) = (projVal fgSimTy sim, x0) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [armEval_genOPK, fgCoreArm_genOPK]; rw [liftGdhArm_fst_map, legacyCoreArmEval_eq]
      simp only [exprRename, Expr.eval, Env.get]; rw [hPair]; exact hEq
    · intro q hq; dsimp only [armEval_genOPK, fgCoreArm_genOPK] at hq
      obtain ⟨rs, hrs, rfl⟩ := mem_support_liftGdhArm (fgGenOpkLegC F) _ _ _ _ hq
      simp only [exprRename, Expr.eval, Env.get] at hrs ⊢; rw [hPair] at hrs; exact hSup rs hrs
  intro sim₀ pa₀ hSim; obtain ⟨hb₀, hKon, hQtot, hPows₀⟩ := inv_sim_bounds hInv sim₀ hSim
  have hTake1 : List.take F.K_on sim₀.1.2.2.2.2.1 = sim₀.1.2.2.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.opkEntries_le hKon)
  have hTake2 : List.take b.q_total sim₀.1.2.2.2.2.1 = sim₀.1.2.2.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hb₀.opkEntries_le (Nat.le_trans hKon hQtot))
  refine ⟨?_, ?_⟩
  · simp only [fgGenOpkLegC, legacyCoreArmComp, a1gPre2C, fgStep2C, onBaseF, genOpkB, authQenc, x0,
      rs, aNone, aPk, fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stOpks, stUpd,
      oeMk, eAny, nat3Eq, nat2Eq, eval_natEq, eval_sampleBytes32, eval_queryPrim, letV, Comp.letC,
      bindV, caseSumV, Comp.eval_liftChal, liftGdhComp_eval, Comp.eval, Expr.eval, Ext.step_wk,
      Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind, map_eq_bind_pure_comp, bind_assoc]
    rw [hTake1, hTake2]; congr 1
  · intro out hrs'
    dsimp only [fgGenOpkLegC, onBaseF, genOpkB, rs, aNone, aPk, fsUpd, fsMk, fsBase,
      fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stOpks, stUpd, oeMk, eAny, nat3Eq, nat2Eq] at hrs'
    simp only [letV, Comp.letC, bindV, Comp.eval_liftChal, eval_natEq,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind] at hrs'
    rw [hTake1] at hrs'
    split_ifs at hrs' with hAny
    · simp only [embedPrim_pure, pure_bind, mem_support_pure_iff] at hrs'; rcases hrs' with ⟨rfl, rfl⟩
      simpa only [hSim] using hInv.bump_unchanged (AuthQuery.genOPK p.1 p.2.1 p.2.2) hroom
    · simp only [eval_sampleBytes32, eval_queryPrim, embedPrim_bind, embedPrim_pure, Expr.eval, Env.get_vz,
        map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc, mem_support_bind_iff, mem_support_pure_iff] at hrs'
      rcases hrs' with ⟨sk0, _, pk0, _, rfl, rfl⟩
      refine fgSimShadowInv_online_sim (AuthQuery.genOPK p.1 p.2.1 p.2.2) trivial nofun nofun hroom hInv sim₀ hSim
        _ ?_ _ (Nat.le_trans hPows₀ (Nat.le_succ _))
      have hb1 := hb₀.mono (Nat.le_succ _)
      exact ⟨hb1.principals_le, hb1.spkBundles_le,
        by simpa only [List.length_cons] using Nat.succ_le_succ hb₀.opkEntries_le,
        hb1.sessions_le, hb1.usedSendSessions_le, hb1.usedRecvOPK_le, hb1.usedRecvNoOPK_le,
        hb1.seenKyberBaseKeys_le, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
        hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩

theorem fgArmSim_revealDhSecrets (S : Setup) (b : QueryBudget) :
    FgArmSim S b (fun _ => AuthQuery.revealDhSecrets) (armEval_revealDhSecrets S b) := by
  dsimp only [FgArmSim]; intro c pa sim sigB aux _ _ hroom hInv; rw [legacyCoreArmEval_eq]
  refine ⟨?_, ?_⟩
  · simp only [armEval_revealDhSecrets, fgCoreArm_revealDh, aNoneAtomicE, legacyCoreArmComp, a1gPre2C,
      fgStep2C, aNone, authQenc, bindV, caseSumV, liftGdhComp_eval, liftGdhToSign_pure, Comp.eval,
      Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get, v, pure_bind, map_pure, Prod.map_apply, id_eq]
    change pure (Sum.inl (), (sim, sigB)) =
      pure (embedVal authRespTy (Sum.inl ()), (embedVal fgSimTy (projVal fgSimTy sim), sigB))
    rw [embedVal_projVal]; rfl
  · intro p hp
    simp only [armEval_revealDhSecrets, fgCoreArm_revealDh, aNoneAtomicE,
      Comp.eval, Expr.eval, Env.get, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hInv.bump_unchanged AuthQuery.revealDhSecrets hroom

theorem fgArmSim_registerKey (S : Setup) (b : QueryBudget) :
    FgArmSim S b AuthQuery.registerKey (armEval_registerKey S b) := by
  dsimp only [FgArmSim]; intro c pa sim sigB aux sk _ hroom hInv
  suffices ∀ (sim₀ : fgSimTy.denote) (pa₀ : a1gParams2Ty.denote), embedVal fgSimTy sim₀ = sim →
      (((fun rs => embedVal (.prod authRespTy (.prod fgSimTy .nat)) (rs.1, (rs.2, sigB))) <$>
        liftGdhToSign (fgRegisterLegC.eval (.cons (sim₀, sk) .nil)) :
        OracleComp SignalPqxdh.Security.GdhSignSimSpec _)) =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa₀ (.cons sim₀ (.cons sigB (.cons (authQenc (.registerKey sk)) .nil)))) ∧
      ∀ rs ∈ support (fgRegisterLegC.eval (.cons (sim₀, sk) .nil)),
        FgSimShadowInv S b (bumpPred (authSimPred S) c (.registerKey sk)) (embedVal fgSimTy rs.2) aux by
    obtain ⟨hEq, hSup⟩ := this (projVal fgSimTy sim) (projVal a1gParams2Ty pa) (embedVal_projVal fgSimTy sim)
    have hPair : projVal (.prod fgSimTy (B 32)) (sim, sk) = (projVal fgSimTy sim, sk) := rfl
    refine ⟨?_, ?_⟩
    · dsimp only [armEval_registerKey, fgCoreArm_registerKey]; rw [liftGdhArm_fst_map, legacyCoreArmEval_eq]
      simp only [exprRename, Expr.eval, Env.get]; rw [hPair]; exact hEq
    · intro p hp; dsimp only [armEval_registerKey, fgCoreArm_registerKey] at hp
      obtain ⟨rs, hrs, rfl⟩ := mem_support_liftGdhArm fgRegisterLegC _ _ _ _ hp
      simp only [exprRename, Expr.eval, Env.get] at hrs ⊢; rw [hPair] at hrs; exact hSup rs hrs
  intro sim₀ pa₀ hSim; obtain ⟨hb₀, _, _, hPows₀⟩ := inv_sim_bounds hInv sim₀ hSim
  refine ⟨?_, ?_⟩
  · simp only [fgRegisterLegC, legacyCoreArmComp, a1gPre2C, fgStep2C, fgRegisterC, authQenc, aNone, aPk,
      fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stUpd, stAdv, eval_natEq,
      Expr.eval_bytesLen, eval_queryPrimC, letV, Comp.letC, bindV, caseSumV, liftGdhComp_eval, Comp.eval,
      Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind, map_eq_bind_pure_comp, bind_assoc]
    congr 1
  · intro out hrs'
    simp only [fgRegisterLegC, letV, Comp.letC, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, pure_bind] at hrs'
    dsimp only [fgRegisterC] at hrs'
    simp only [bindV, eval_natEq, Expr.eval_bytesLen, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v] at hrs'
    split_ifs at hrs' with hLen
    · simp only [aNone, Expr.eval, mem_support_pure_iff] at hrs'; rcases hrs' with ⟨rfl, rfl⟩
      simpa only [Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz, v, hSim] using
        hInv.bump_unchanged (AuthQuery.registerKey sk) hroom
    · dsimp only [aPk, fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, stUpd, stAdv] at hrs'
      simp only [Comp.queryPrimC, Comp.eval, Expr.eval, Env.get_vs, Env.get_vz] at hrs'
      rcases hrs' with ⟨_, ⟨_, _, rfl⟩, _, ⟨_, _, rfl⟩, rfl, rfl⟩
      refine fgSimShadowInv_online_sim (AuthQuery.registerKey sk) trivial nofun nofun hroom hInv sim₀ hSim _ ?_ _
        (by simpa only [List.length_cons] using Nat.succ_le_succ hPows₀)
      have hb1 := hb₀.mono (Nat.le_succ _)
      exact ⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le, hb1.sessions_le,
        hb1.usedSendSessions_le, hb1.usedRecvOPK_le, hb1.usedRecvNoOPK_le, hb1.seenKyberBaseKeys_le,
        hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le, hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le,
        by simpa only [List.length_cons] using Nat.succ_le_succ hb₀.advKeys_le⟩

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimMisc
