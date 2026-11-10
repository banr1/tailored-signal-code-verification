/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSig
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySig
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# `Send` Arm and `SigSendCheck` Forgetful Simulation

Forgetful simulation proofs for the `.sendOPK` and `.sendNoOPK` arms (`fgArmSim_sendOPK`,
`fgArmSim_sendNoOPK`) and the signature pre-dispatch forgery check (`sigSendCheckK_sim`), shared
by `a1g2KindProg` and `a1s2KindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimSend

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Expr Comp Env pqAtomicSig pqAtomicOps bundleT bundleV)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred bind_congr_support)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedVal_projVal embedEnv
   exprRename exprRename_eval compRename compRename_eval
   mapExpr mapExpr_eval mapComp mapComp_eval comp_queries_zero_of_zero tlAuthSigDdh
   authQenc_eq)
open _root_.SignalPqxdh
  (Setup QueryBudget AuthQuery PreKeyBundleInput Bytes)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle B)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec)
open _root_.SignalPqxdh.Security (liftGdhToSign)
open _root_.SignalPqxdh.Security.ReductionDsl
  (authStateTy authSessionEntryTy sessionIdTy fgPosTy fgPatchEntryTy authQueryTy authRespTy
   preKeyBundleTy eval_sampleBytes32C eval_queryPrimC)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (liftBase)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
  (Ren renameComp renameComp_eval
   liftGdhComp liftGdhComp_eval liftGdhToSign_map mem_support_liftGdhToSign)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext v letV bindV caseOptV caseSumV findMV anyMV eAny eFind eCaseOpt eCaseSum
   Env.get_vz Env.get_vs eval_natEq
   mkSecretPosC_eval twoSideC_eval twoSideOptC_eval
   RSF patchKeyTy sendQTy fgSimTy rootEntryTy a1gParams2Ty a1sStTy a1sRS
   a1sG a1sTp a1sTpk a1sFg a1sMk a1sBase isSomeE natEq nat2Eq sidEq sendGuardE
   encEC encKEM buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
   sbSpkSk sbSpkPk sbPqspkPk oeOpkPk peSecIKA0 peIkAPk peIkSignPk peCorrupted
   pa2U pa2Role q4 twoSideC twoSideOptC mkSecretPosC firstMsgADE hdMk optFst optSnd seMk
   aNone aSendFresh aSendUnfresh
   stPrin stSpks stOpks stSess stUsedS stSecb stUpd
   fsBase fsPows fsL fsRootL fsUpd
   findHonestC isGameSpkC isGameOpkC resolveSigPkC honestPeerC extractC
   isAdvPowsC koskBundleOkPowsC lookupSpkSkC
   patchC rootPatchC fgSend2C fgStep2C a1gPre2C a1sSendCheckC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (findB_min_eval_eq anyB_min_eval_eq findM_min_eval_eq anyM_min_eval_eq)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels wk1 liftExpr1 liftExpr2 authSendQAtomicTy extractKC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv AuthBaseValOnlineBounded AuthBaseAtomOnlineBounded)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (seqFgEntryTy seqRootEntryTy sessAuxLegTy fgAuthShadowAuxTy
   a1s2ShadowStTy fgCoreOutTy
   auxFgSess auxFgCtr auxFgRoAvl auxFgRootSess auxFgRootCtr auxFgRootRoAvl auxRawAvl
   auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE auxFgRootRoAvlE auxRawAvlE
   fgAuxMkE auxSessSliceE auxPutSessSliceE
   liftCs1 liftGdh1 saFgSess saFgCtr saRootSess saRootCtr
   patchWithShadowC rootPatchWithShadowC fgSend2ShadowC a1sSendCheckLegC fgCoreArm_send)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (AuthSigDdhSpec FgTableShadow RootTableShadow FgSimShadowInv SigAuthInv
   patchWithShadowC_sim rootPatchWithShadowC_sim
   legacyCoreArmComp legacyCoreArmEval armEval_sendOPK armEval_sendNoOPK
   FgArmSim SigSendCheckSim)

private theorem liftCs1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftCs1 c argE).eval ρ =
      embedVal out <$> c.eval (.cons (projVal a (argE.eval ρ)) .nil) := by
  simp only [liftCs1, Comp.eval, pure_bind]
  refine (compRename_eval (mapComp tlAuthSigDdh c) wk1
    (embedEnv (.cons (projVal a (argE.eval ρ)) .nil)) (.cons (argE.eval ρ) ρ) ?_).trans ?_
  · intro _ vr
    cases vr with
    | zero => exact (embedVal_projVal a (argE.eval ρ)).symm
    | succ v' => nomatch v'
  · exact mapComp_eval tlAuthSigDdh c (comp_queries_zero_of_zero (fun _ => rfl) c) _

private theorem liftBase_eq_liftChal {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    liftBase (C := C) c = Comp.liftChal (C := C) c := by
  induction c <;> (simp only [liftBase, Comp.liftChal, *] <;> rfl)

private theorem queryPrim_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (tag : _root_.SignalPqxdh.LegacyCosted.PTag)
    (e₁ : Expr pqxdhOps Γ₁ (pqPrimIface.dom tag)) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ (pqPrimIface.dom tag)) (ρ₂ : Env Γ₂)
    (h : e₁.eval ρ₁ = e₂.eval ρ₂) :
    (Comp.queryPrim tag e₁).eval ρ₁ = (Comp.queryPrim tag e₂).eval ρ₂ := by
  simp only [Comp.queryPrim, Comp.eval]
  exact h ▸ rfl

private theorem bind_congr_eq {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {oa₁ oa₂ : OracleComp spec α} {f₁ f₂ : α → OracleComp spec β}
    (ha : oa₁ = oa₂) (hf : ∀ a ∈ support oa₂, f₁ a = f₂ a) :
    oa₁ >>= f₁ = oa₂ >>= f₂ := by
  rw [ha]; exact bind_congr_support oa₂ f₁ f₂ hf

private theorem liftGdh1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftGdh1 c argE).eval ρ =
      embedVal out <$> liftGdhToSign (c.eval (.cons (projVal a (argE.eval ρ)) .nil)) := by
  rw [liftGdh1, liftCs1_eval, liftGdhComp_eval]

private theorem embedVal_length {t : Ty pqSig} (l : List t.denote) :
    (embedVal (.list t) l).length = l.length := by
  change (l.map (embedVal t)).length = l.length
  exact List.length_map _

private theorem findHonestC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁.wk st₁) = Env.get ρ₂ (h₂.wk st₂))
    (hik : ik₁.eval ρ₁ = ik₂.eval ρ₂)
    (hPrin : (Env.get ρ₁ (h₁.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (findHonestC S (AuthKindFuels.ofBudget S b).K_on st₁ ik₁).eval ρ₁ =
      (findHonestC S b.q_total st₂ ik₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hMin : min F.K_on S.N_dh = min (min b.q_total S.N_dh) F.M_on :=
    Nat.min_right_comm b.q_total F.M_on S.N_dh
  simp only [findHonestC, letV, Comp.eval_letC, hik, findMV, Comp.findBoundedM]
  rw [hMin, findM_min_eval_eq (min b.q_total S.N_dh) F.M_on _ _ _
    (by simpa [stPrin, v, Expr.eval, Ext.step_wk, Env.get] using hPrin)]
  simp only [Comp.eval, v, Expr.eval, Ext.step_wk, Env.get, hst]
  rfl

private theorem honestPeerC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁.wk st₁) = Env.get ρ₂ (h₂.wk st₂))
    (hik : ik₁.eval ρ₁ = ik₂.eval ρ₂)
    (hPrin : (Env.get ρ₁ (h₁.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (honestPeerC S (AuthKindFuels.ofBudget S b).K_on st₁ ik₁).eval ρ₁ =
      (honestPeerC S b.q_total st₂ ik₂).eval ρ₂ := by
  simp only [honestPeerC, bindV, Comp.eval]
  rw [findHonestC_kon_eq S b st₁ ik₁ ρ₁ st₂ ik₂ ρ₂ hst hik hPrin]
  rfl

private theorem eAny_kon_eq {a : Ty pqSig} {Γ₁ Γ₂ : List (Ty pqSig)}
    (K M : ℕ) (xs₁ : Expr pqxdhOps Γ₁ (.list a))
    (p₁ : Var (a :: Γ₁) a → Expr pqxdhOps (a :: Γ₁) .bool) (ρ₁ : Env Γ₁)
    (xs₂ : Expr pqxdhOps Γ₂ (.list a))
    (p₂ : Var (a :: Γ₂) a → Expr pqxdhOps (a :: Γ₂) .bool) (ρ₂ : Env Γ₂)
    (hxs : xs₁.eval ρ₁ = xs₂.eval ρ₂)
    (hp : ∀ x, (p₁ .vz).eval (.cons x ρ₁) = (p₂ .vz).eval (.cons x ρ₂))
    (hlen : (xs₁.eval ρ₁).length ≤ M) :
    (eAny (min K M) xs₁ p₁).eval ρ₁ = (eAny K xs₂ p₂).eval ρ₂ := by
  rw [eAny, anyB_min_eval_eq K M _ _ ρ₁ hlen]
  simp only [eAny, Expr.eval, hxs]
  congr 1; funext x; exact hp x

private theorem eFind_kon_eq {a : Ty pqSig} {Γ₁ Γ₂ : List (Ty pqSig)}
    (K M : ℕ) (xs₁ : Expr pqxdhOps Γ₁ (.list a))
    (p₁ : Var (a :: Γ₁) a → Expr pqxdhOps (a :: Γ₁) .bool) (ρ₁ : Env Γ₁)
    (xs₂ : Expr pqxdhOps Γ₂ (.list a))
    (p₂ : Var (a :: Γ₂) a → Expr pqxdhOps (a :: Γ₂) .bool) (ρ₂ : Env Γ₂)
    (hxs : xs₁.eval ρ₁ = xs₂.eval ρ₂)
    (hp : ∀ x, (p₁ .vz).eval (.cons x ρ₁) = (p₂ .vz).eval (.cons x ρ₂))
    (hlen : (xs₁.eval ρ₁).length ≤ M) :
    (eFind (min K M) xs₁ p₁).eval ρ₁ = (eFind K xs₂ p₂).eval ρ₂ := by
  rw [eFind, findB_min_eval_eq K M _ _ ρ₁ hlen]
  simp only [eFind, Expr.eval, hxs]
  congr 1; funext x; exact hp x

private theorem list_take_kon_eq {α : Type} (S : Setup) (b : QueryBudget) (l : List α)
    (hl : l.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    l.take (AuthKindFuels.ofBudget S b).K_on = l.take b.q_total := by
  change l.take (min b.q_total (AuthKindFuels.ofBudget S b).M_on) = l.take b.q_total
  rw [← List.take_take, List.take_of_length_le hl]

private theorem extractC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ₁ Γ₁' Γ₂' Γ₃' Γ₄' Δ₂ : List (Ty pqSig)}
    (tp₁ : Var Γ₁ .nat) (tpk₁ : Var Γ₂ (B 32)) (st₁ : Var Γ₃ authStateTy) (bu₁ : Var Γ₄ preKeyBundleTy)
    [h₁₁ : Ext Γ₁ Δ₁] [h₁₂ : Ext Γ₂ Δ₁] [h₁₃ : Ext Γ₃ Δ₁] [h₁₄ : Ext Γ₄ Δ₁] (ρ₁ : Env Δ₁)
    (tp₂ : Var Γ₁' .nat) (tpk₂ : Var Γ₂' (B 32)) (st₂ : Var Γ₃' authStateTy) (bu₂ : Var Γ₄' preKeyBundleTy)
    [h₂₁ : Ext Γ₁' Δ₂] [h₂₂ : Ext Γ₂' Δ₂] [h₂₃ : Ext Γ₃' Δ₂] [h₂₄ : Ext Γ₄' Δ₂] (ρ₂ : Env Δ₂)
    (htp : Env.get ρ₁ (h₁₁.wk tp₁) = Env.get ρ₂ (h₂₁.wk tp₂))
    (htpk : Env.get ρ₁ (h₁₂.wk tpk₁) = Env.get ρ₂ (h₂₂.wk tpk₂))
    (hst : Env.get ρ₁ (h₁₃.wk st₁) = Env.get ρ₂ (h₂₃.wk st₂))
    (hbu : Env.get ρ₁ (h₁₄.wk bu₁) = Env.get ρ₂ (h₂₄.wk bu₂))
    (hPrin : (Env.get ρ₁ (h₁₃.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on)
    (hSpks : (Env.get ρ₁ (h₁₃.wk st₁)).2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (extractC S (AuthKindFuels.ofBudget S b).K_on tp₁ tpk₁ st₁ bu₁).eval ρ₁ =
      (extractC S b.q_total tp₂ tpk₂ st₂ bu₂).eval ρ₂ := by
  simp only [extractC, bindV, Comp.eval]
  apply bind_congr_eq
  · refine honestPeerC_kon_eq S b st₁ _ ρ₁ st₂ _ ρ₂ hst ?_ hPrin
    simp only [v, Expr.eval, hbu]
  · intro peer _
    apply bind_congr_eq
    · refine queryPrim_eval_congr _ _ _ _ _ ?_
      exact Prod.ext htpk (Prod.ext
        (congrArg (pqxdhOps.eval (Sum.inl (.cons _ 32))) (congrArg (fun b => b.2.2.1) hbu))
        (congrArg (fun b => b.2.2.2.1) hbu))
    · intro v1 _
      apply bind_congr_eq
      · refine queryPrim_eval_congr _ _ _ _ _ ?_
        exact Prod.ext htpk (Prod.ext
          (congrArg (pqxdhOps.eval (Sum.inl (.cons _ 1568))) (congrArg (fun b => b.2.2.2.2.2.2.1) hbu))
          (congrArg (fun b => b.2.2.2.2.2.2.2) hbu))
      · intro v2 _
        congr 1
        cases peer with
        | none => rfl
        | some k =>
          have hSpks₂ : (ρ₂.get (h₂₃.wk st₂)).2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on :=
            hst ▸ hSpks
          simp only [eCaseOpt, eAny, eval_natEq, Expr.bytesBeq, Expr.bytesWiden, Expr.bytesCons,
            sbSpkPk, sbPqspkPk, buSpkB, buPqspkB, buSpkSig, buPqspkSig, encEC, encKEM, stSpks,
            v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get,
            htp, hst, hbu, list_take_kon_eq S b _ hSpks₂]
          split
          · split
            · exact congrArg some (Prod.ext
                (congrArg (pqxdhOps.eval (Sum.inl (.widen 33 1536)))
                  (congrArg (pqxdhOps.eval (Sum.inl (.cons _ 32)))
                    (congrArg (fun b => b.2.2.1) hbu))) rfl)
            · split
              · exact congrArg some (Prod.ext
                  (congrArg (pqxdhOps.eval (Sum.inl (.cons _ 1568)))
                    (congrArg (fun b => b.2.2.2.2.2.2.1) hbu)) rfl)
              · rfl
          · rfl

private theorem isAdvPowsC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (pows₁ : Var Γ₁ (.list (.prod (B 32) (B 32)))) [h₁ : Ext Γ₁ Δ₁]
    (pk₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (pows₂ : Var Γ₂ (.list (.prod (B 32) (B 32)))) [h₂ : Ext Γ₂ Δ₂]
    (pk₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hpows : Env.get ρ₁ (h₁.wk pows₁) = Env.get ρ₂ (h₂.wk pows₂))
    (hpk : pk₁.eval ρ₁ = pk₂.eval ρ₂)
    (hPowsLen : (Env.get ρ₁ (h₁.wk pows₁)).length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (isAdvPowsC (AuthKindFuels.ofBudget S b).K_on pows₁ pk₁).eval ρ₁ =
      (isAdvPowsC b.q_total pows₂ pk₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hKon : F.K_on = min b.q_total F.M_on := rfl
  simp only [isAdvPowsC, bindV, Comp.eval]
  rw [queryPrim_eval_congr .pow8 pk₁ ρ₁ pk₂ ρ₂ hpk]
  apply bind_congr_support; intro w _
  congr 1
  rw [eAny, hKon, anyB_min_eval_eq b.q_total F.M_on _ _ (.cons w ρ₁)
    (by simpa [v, Expr.eval, Ext.step_wk, Env.get] using hPowsLen)]
  simp [eAny, Expr.eval, v, Ext.step_wk, Ext.refl_wk, hpows]

private theorem isGameSpkC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (pk₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (pk₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁.wk st₁) = Env.get ρ₂ (h₂.wk st₂))
    (hpk : pk₁.eval ρ₁ = pk₂.eval ρ₂)
    (hSpks : (Env.get ρ₁ (h₁.wk st₁)).2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (isGameSpkC S (AuthKindFuels.ofBudget S b).K_on st₁ pk₁).eval ρ₁ =
      (isGameSpkC S b.q_total st₂ pk₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hMin : min F.K_on S.N_dh = min (min b.q_total S.N_dh) F.M_on :=
    Nat.min_right_comm b.q_total F.M_on S.N_dh
  simp only [isGameSpkC, letV, Comp.eval_letC, hpk, anyMV, Comp.anyBoundedM]
  rw [hMin, anyM_min_eval_eq (min b.q_total S.N_dh) F.M_on _ _ _
    (by simpa [stSpks, v, Expr.eval, Ext.step_wk, Env.get] using hSpks)]
  simp only [Comp.eval, v, Expr.eval, Ext.step_wk, Env.get, hst]
  rfl

private theorem isGameOpkC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (pk₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (pk₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁.wk st₁) = Env.get ρ₂ (h₂.wk st₂))
    (hpk : pk₁.eval ρ₁ = pk₂.eval ρ₂)
    (hOpks : (Env.get ρ₁ (h₁.wk st₁)).2.2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (isGameOpkC S (AuthKindFuels.ofBudget S b).K_on st₁ pk₁).eval ρ₁ =
      (isGameOpkC S b.q_total st₂ pk₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hMin : min F.K_on S.N_dh = min (min b.q_total S.N_dh) F.M_on :=
    Nat.min_right_comm b.q_total F.M_on S.N_dh
  simp only [isGameOpkC, letV, Comp.eval_letC, hpk, anyMV, Comp.anyBoundedM]
  rw [hMin, anyM_min_eval_eq (min b.q_total S.N_dh) F.M_on _ _ _
    (by simpa [stOpks, v, Expr.eval, Ext.step_wk, Env.get] using hOpks)]
  simp only [Comp.eval, v, Expr.eval, Ext.step_wk, Env.get, hst]
  rfl

private theorem koskBundleOkPowsC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Γ₃ Δ₁ Γ₁' Γ₂' Γ₃' Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) (pows₁ : Var Γ₂ (.list (.prod (B 32) (B 32)))) (bu₁ : Var Γ₃ preKeyBundleTy)
    [h₁₁ : Ext Γ₁ Δ₁] [h₁₂ : Ext Γ₂ Δ₁] [h₁₃ : Ext Γ₃ Δ₁] (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₁' authStateTy) (pows₂ : Var Γ₂' (.list (.prod (B 32) (B 32)))) (bu₂ : Var Γ₃' preKeyBundleTy)
    [h₂₁ : Ext Γ₁' Δ₂] [h₂₂ : Ext Γ₂' Δ₂] [h₂₃ : Ext Γ₃' Δ₂] (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁₁.wk st₁) = Env.get ρ₂ (h₂₁.wk st₂))
    (hpows : Env.get ρ₁ (h₁₂.wk pows₁) = Env.get ρ₂ (h₂₂.wk pows₂))
    (hbu : Env.get ρ₁ (h₁₃.wk bu₁) = Env.get ρ₂ (h₂₃.wk bu₂))
    (hPrin : (Env.get ρ₁ (h₁₁.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on)
    (hSpks : (Env.get ρ₁ (h₁₁.wk st₁)).2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on)
    (hOpks : (Env.get ρ₁ (h₁₁.wk st₁)).2.2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on)
    (hPowsLen : (Env.get ρ₁ (h₁₂.wk pows₁)).length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (koskBundleOkPowsC S (AuthKindFuels.ofBudget S b).K_on st₁ pows₁ bu₁).eval ρ₁ =
      (koskBundleOkPowsC S b.q_total st₂ pows₂ bu₂).eval ρ₂ := by
  simp only [koskBundleOkPowsC, bindV, caseOptV, Comp.caseOptC, Comp.eval]
  rw [findHonestC_kon_eq S b st₁ (buIkB (v bu₁)) ρ₁ st₂ (buIkB (v bu₂)) ρ₂
    hst (by simp [v, Expr.eval, hbu]) hPrin]
  apply bind_congr_support; intro f _
  rw [isAdvPowsC_kon_eq S b pows₁ (buIkB (v bu₁)) (.cons f ρ₁) pows₂ (buIkB (v bu₂)) (.cons f ρ₂)
    (by simpa [Ext.step_wk, Env.get] using hpows)
    (by simp [v, Expr.eval, Ext.step_wk, hbu])
    (by simpa [Ext.step_wk, Env.get] using hPowsLen)]
  apply bind_congr_support; intro idA _
  rw [isGameSpkC_kon_eq S b st₁ (buSpkB (v bu₁)) (.cons idA (.cons f ρ₁))
    st₂ (buSpkB (v bu₂)) (.cons idA (.cons f ρ₂))
    (by simpa [Ext.step_wk, Env.get] using hst)
    (by simp [v, Expr.eval, Ext.step_wk, hbu])
    (by simpa [Ext.step_wk, Env.get] using hSpks)]
  apply bind_congr_support; intro spkG _
  rw [isAdvPowsC_kon_eq S b pows₁ (buSpkB (v bu₁)) (.cons spkG (.cons idA (.cons f ρ₁)))
    pows₂ (buSpkB (v bu₂)) (.cons spkG (.cons idA (.cons f ρ₂)))
    (by simpa [Ext.step_wk, Env.get] using hpows)
    (by simp [v, Expr.eval, Ext.step_wk, hbu])
    (by simpa [Ext.step_wk, Env.get] using hPowsLen)]
  apply bind_congr_support; intro spkA _
  have hOpkEq : (buOpkB (v bu₁)).eval (.cons spkA (.cons spkG (.cons idA (.cons f ρ₁)))) =
      (buOpkB (v bu₂)).eval (.cons spkA (.cons spkG (.cons idA (.cons f ρ₂)))) := by
    simp [v, Expr.eval, Ext.step_wk, hbu]
  rw [hOpkEq]
  rcases (buOpkB (v bu₂)).eval (.cons spkA (.cons spkG (.cons idA (.cons f ρ₂)))) with _ | o
  · rfl
  · simp only []
    refine bind_congr_eq ?_ fun opkG _ => ?_
    · apply isGameOpkC_kon_eq S b
      · simpa [Ext.step_wk, Env.get] using hst
      · simp [v, Expr.eval, Ext.refl_wk]
      · simpa [Ext.step_wk, Env.get] using hOpks
    · refine bind_congr_eq ?_ fun _ _ => rfl
      apply isAdvPowsC_kon_eq S b
      · simpa [Ext.step_wk, Env.get] using hpows
      · simp [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      · simpa [Ext.step_wk, Env.get] using hPowsLen

private theorem resolveSigPkC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁.wk st₁) = Env.get ρ₂ (h₂.wk st₂))
    (hik : ik₁.eval ρ₁ = ik₂.eval ρ₂)
    (hPrin : (Env.get ρ₁ (h₁.wk st₁)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (resolveSigPkC S (AuthKindFuels.ofBudget S b).K_on st₁ ik₁).eval ρ₁ =
      (resolveSigPkC S b.q_total st₂ ik₂).eval ρ₂ := by
  simp only [resolveSigPkC, letV, bindV, Comp.eval_letC, Comp.eval, hik]
  refine bind_congr_eq ?_ fun _ _ => rfl
  apply findHonestC_kon_eq S b
  · simpa [Ext.step_wk, Env.get] using hst
  · simp [v, Expr.eval, Ext.refl_wk]
  · simpa [Ext.step_wk, Env.get] using hPrin

private theorem lookupSpkSkC_kon_eq (S : Setup) (b : QueryBudget)
    {Γ₁ Γ₂ Δ₁ Γ₁' Γ₂' Δ₂ : List (Ty pqSig)}
    (st₁ : Var Γ₁ authStateTy) (pows₁ : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [h₁₁ : Ext Γ₁ Δ₁] [h₁₂ : Ext Γ₂ Δ₁] (pk₁ : Expr pqxdhOps Δ₁ (B 32)) (ρ₁ : Env Δ₁)
    (st₂ : Var Γ₁' authStateTy) (pows₂ : Var Γ₂' (.list (.prod (B 32) (B 32))))
    [h₂₁ : Ext Γ₁' Δ₂] [h₂₂ : Ext Γ₂' Δ₂] (pk₂ : Expr pqxdhOps Δ₂ (B 32)) (ρ₂ : Env Δ₂)
    (hst : Env.get ρ₁ (h₁₁.wk st₁) = Env.get ρ₂ (h₂₁.wk st₂))
    (hpows : Env.get ρ₁ (h₁₂.wk pows₁) = Env.get ρ₂ (h₂₂.wk pows₂))
    (hpk : pk₁.eval ρ₁ = pk₂.eval ρ₂)
    (hSpks : (Env.get ρ₁ (h₁₁.wk st₁)).2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on)
    (hPowsLen : (Env.get ρ₁ (h₁₂.wk pows₁)).length ≤ (AuthKindFuels.ofBudget S b).M_on) :
    (lookupSpkSkC S (AuthKindFuels.ofBudget S b).K_on st₁ pows₁ pk₁).eval ρ₁ =
      (lookupSpkSkC S b.q_total st₂ pows₂ pk₂).eval ρ₂ := by
  let F := AuthKindFuels.ofBudget S b
  have hKon : F.K_on = min b.q_total F.M_on := rfl
  have hMin : min F.K_on S.N_dh = min (min b.q_total S.N_dh) F.M_on :=
    Nat.min_right_comm b.q_total F.M_on S.N_dh
  simp only [lookupSpkSkC, bindV, Comp.eval]
  refine bind_congr_eq (queryPrim_eval_congr .pow8 pk₁ ρ₁ pk₂ ρ₂ hpk) fun w _ => ?_
  refine bind_congr_eq ?_ fun f _ => ?_
  · simp only [findMV, Comp.findBoundedM]
    rw [hMin, findM_min_eval_eq (min b.q_total S.N_dh) F.M_on _ _ (.cons w ρ₁)
      (by simpa [stSpks, v, Expr.eval, Ext.step_wk, Env.get] using hSpks)]
    simp only [Comp.eval, v, Expr.eval, Ext.step_wk, Env.get, hst]
    congr 1
  · congr 1
    have hFindPows :
        (eFind F.K_on (v pows₁) fun e => .bytesBeq (.snd (v e)) (v (.vz : Var (B 32 :: Δ₁) (B 32)))).eval
          (.cons f (.cons w ρ₁)) =
        (eFind b.q_total (v pows₂) fun e => .bytesBeq (.snd (v e)) (v (.vz : Var (B 32 :: Δ₂) (B 32)))).eval
          (.cons f (.cons w ρ₂)) := by
      rw [eFind, hKon, findB_min_eval_eq b.q_total F.M_on _ _ (.cons f (.cons w ρ₁))
        (by simpa [v, Expr.eval, Ext.step_wk, Env.get] using hPowsLen)]
      simp [eFind, Expr.eval, v, Ext.step_wk, Ext.refl_wk, hpows]
    cases f with
    | some _ => rfl
    | none =>
      simp only [eCaseOpt, Expr.eval]
      rw [hFindPows]
      cases (eFind b.q_total (v pows₂) fun e => .bytesBeq (.snd (v e)) (v (.vz : Var (B 32 :: Δ₂) (B 32)))).eval
        (.cons (t := .opt _) none (.cons w ρ₂)) <;> rfl

private theorem queryPrimC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (g : _root_.SignalPqxdh.LegacyCosted.PTag)
    (e₁ : Expr pqxdhOps Γ₁ g.dom) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ g.dom) (ρ₂ : Env Γ₂)
    (h : e₁.eval ρ₁ = e₂.eval ρ₂) :
    (Comp.queryPrimC (C := gapDhDdhOracle) g e₁).eval ρ₁ =
      (Comp.queryPrimC (C := gapDhDdhOracle) g e₂).eval ρ₂ := by
  simp only [eval_queryPrimC]
  exact h ▸ rfl

private theorem twoSideC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (a₁ : Expr pqxdhOps Γ₁ _) (ρ₁ : Env Γ₁)
    (a₂ : Expr pqxdhOps Γ₂ _) (ρ₂ : Env Γ₂)
    (h : a₁.eval ρ₁ = a₂.eval ρ₂) :
    (twoSideC a₁).eval ρ₁ = (twoSideC a₂).eval ρ₂ := by
  rw [twoSideC_eval, twoSideC_eval, h]

private theorem twoSideOptC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (o₁ : Expr pqxdhOps Γ₁ _) (ρ₁ : Env Γ₁)
    (o₂ : Expr pqxdhOps Γ₂ _) (ρ₂ : Env Γ₂)
    (h : o₁.eval ρ₁ = o₂.eval ρ₂) :
    (twoSideOptC o₁).eval ρ₁ = (twoSideOptC o₂).eval ρ₂ := by
  rw [twoSideOptC_eval, twoSideOptC_eval, h]

private theorem mkSecretPosC_eval_congr {Γ₁ Γ₂ : List (Ty pqSig)}
    (z₁ : Expr pqxdhOps Γ₁ (B 32)) (ρ₁ : Env Γ₁)
    (z₂ : Expr pqxdhOps Γ₂ (B 32)) (ρ₂ : Env Γ₂)
    (h : z₁.eval ρ₁ = z₂.eval ρ₂) :
    (mkSecretPosC z₁).eval ρ₁ = (mkSecretPosC z₂).eval ρ₂ := by
  rw [mkSecretPosC_eval, mkSecretPosC_eval, h]

private theorem liftChal_gdh_congr {Γ₁ Γ₂ : List (Ty pqSig)} {t : Ty pqSig}
    (c₁ : Comp pqxdhOps pqPrimIface Γ₁ t) (ρ₁ : Env Γ₁)
    (c₂ : Comp pqxdhOps pqPrimIface Γ₂ t) (ρ₂ : Env Γ₂)
    (h : c₁.eval ρ₁ = c₂.eval ρ₂) :
    (Comp.liftChal (C := gapDhDdhOracle) c₁).eval ρ₁ =
      (Comp.liftChal (C := gapDhDdhOracle) c₂).eval ρ₂ := by
  simp only [Comp.eval_liftChal]
  exact congrArg _ h

private theorem eq_and_inv_retC {Γ₁ Γ₂ : List (Ty pqSig)} {t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ t₁) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ t₂) (ρ₂ : Env Γ₂)
    (heq : projB (e₁.eval ρ₁) = e₂.eval ρ₂)
    (hp : P (e₁.eval ρ₁)) :
    projB <$> (Comp.ret (I := pqGapDhIface) e₁).eval ρ₁ =
      (Comp.ret (I := pqGapDhIface) e₂).eval ρ₂ ∧
    ∀ b ∈ support ((Comp.ret (I := pqGapDhIface) e₁).eval ρ₁), P b := by
  refine ⟨by simp only [Comp.eval, map_pure, heq], fun b hb => ?_⟩
  simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hb
  exact hb ▸ hp

private theorem eq_and_inv_retC_val {Γ₁ Γ₂ : List (Ty pqSig)} {t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ t₁) (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ t₂) (ρ₂ : Env Γ₂)
    (v₁ : t₁.denote) (hv₁ : e₁.eval ρ₁ = v₁)
    (heq : projB v₁ = e₂.eval ρ₂)
    (hp : P v₁) :
    projB <$> (Comp.ret (I := pqGapDhIface) e₁).eval ρ₁ =
      (Comp.ret (I := pqGapDhIface) e₂).eval ρ₂ ∧
    ∀ b ∈ support ((Comp.ret (I := pqGapDhIface) e₁).eval ρ₁), P b := by
  refine ⟨by simp only [Comp.eval, map_pure, hv₁, heq], fun b hb => ?_⟩
  simp only [Comp.eval, support_pure, Set.mem_singleton_iff, hv₁] at hb
  exact hb ▸ hp

private theorem eq_and_inv_letV_l {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁) (c₂ : Comp pqxdhOps pqGapDhIface Γ₂ t₂) (ρ₂ : Env Γ₂)
    (val : a.denote) (hval : e₁.eval ρ₁ = val)
    (hk : projB <$> (k₁ .vz).eval (.cons val ρ₁) = c₂.eval ρ₂ ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = c₂.eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simpa only [letV, Comp.eval_letC, hval] using hk

private theorem eq_and_inv_letV {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ a) (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂)
    (ρ₂ : Env Γ₂)
    (he : e₁.eval ρ₁ = e₂.eval ρ₂)
    (hk : ∀ val : a.denote,
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = (letV e₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simp only [letV, Comp.eval_letC, he]
  exact hk (e₂.eval ρ₂)

private theorem eq_and_inv_letV_val {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (e₁ : Expr pqxdhOps Γ₁ a) (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁)
    (ρ₁ : Env Γ₁)
    (e₂ : Expr pqxdhOps Γ₂ a) (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂)
    (ρ₂ : Env Γ₂)
    (val : a.denote) (he₁ : e₁.eval ρ₁ = val) (he₂ : e₂.eval ρ₂ = val)
    (hk : projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (letV e₁ k₁).eval ρ₁ = (letV e₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((letV e₁ k₁).eval ρ₁), P b := by
  simpa only [letV, Comp.eval_letC, he₁, he₂] using hk

private theorem eq_and_inv_iteC {Γ₁ Γ₂ : List (Ty pqSig)} {t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (c₁ : Expr pqxdhOps Γ₁ .bool) (tr₁ fl₁ : Comp pqxdhOps pqGapDhIface Γ₁ t₁) (ρ₁ : Env Γ₁)
    (c₂ : Expr pqxdhOps Γ₂ .bool) (tr₂ fl₂ : Comp pqxdhOps pqGapDhIface Γ₂ t₂) (ρ₂ : Env Γ₂)
    (hc : c₁.eval ρ₁ = c₂.eval ρ₂)
    (ht : projB <$> tr₁.eval ρ₁ = tr₂.eval ρ₂ ∧ ∀ b ∈ support (tr₁.eval ρ₁), P b)
    (hf : projB <$> fl₁.eval ρ₁ = fl₂.eval ρ₂ ∧ ∀ b ∈ support (fl₁.eval ρ₁), P b) :
    projB <$> (Comp.iteC c₁ tr₁ fl₁).eval ρ₁ = (Comp.iteC c₂ tr₂ fl₂).eval ρ₂ ∧
      ∀ b ∈ support ((Comp.iteC c₁ tr₁ fl₁).eval ρ₁), P b := by
  simp only [Comp.eval, hc]
  cases c₂.eval ρ₂
  · simpa using hf
  · simpa using ht

private theorem eq_and_inv_caseOptV {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (o₁ : Expr pqxdhOps Γ₁ (.opt a)) (n₁ : Comp pqxdhOps pqGapDhIface Γ₁ t₁)
    (s₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (o₂ : Expr pqxdhOps Γ₂ (.opt a)) (n₂ : Comp pqxdhOps pqGapDhIface Γ₂ t₂)
    (s₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (ho : o₁.eval ρ₁ = o₂.eval ρ₂)
    (hn : projB <$> n₁.eval ρ₁ = n₂.eval ρ₂ ∧ ∀ b ∈ support (n₁.eval ρ₁), P b)
    (hs : ∀ val : a.denote,
      projB <$> (s₁ .vz).eval (.cons val ρ₁) = (s₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((s₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (caseOptV o₁ n₁ s₁).eval ρ₁ = (caseOptV o₂ n₂ s₂).eval ρ₂ ∧
      ∀ b ∈ support ((caseOptV o₁ n₁ s₁).eval ρ₁), P b := by
  simp only [caseOptV, Comp.eval, ho]
  cases o₂.eval ρ₂ with
  | none => simpa using hn
  | some val => simpa using hs val

private theorem eq_and_inv_bindV {Γ₁ Γ₂ : List (Ty pqSig)} {a t₁ t₂ : Ty pqSig}
    (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (m₁ : Comp pqxdhOps pqGapDhIface Γ₁ a)
    (k₁ : Var (a :: Γ₁) a → Comp pqxdhOps pqGapDhIface (a :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (m₂ : Comp pqxdhOps pqGapDhIface Γ₂ a)
    (k₂ : Var (a :: Γ₂) a → Comp pqxdhOps pqGapDhIface (a :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (hm : m₁.eval ρ₁ = m₂.eval ρ₂)
    (hk : ∀ val ∈ support (m₁.eval ρ₁),
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons val ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (bindV m₁ k₁).eval ρ₁ = (bindV m₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((bindV m₁ k₁).eval ρ₁), P b := by
  simp only [bindV, Comp.eval]
  refine ⟨?_, ?_⟩
  · rw [← hm, map_bind]
    exact bind_congr_support (m₁.eval ρ₁) _ _ fun val hval => (hk val hval).1
  · intro b hb
    rw [mem_support_bind_iff] at hb
    rcases hb with ⟨val, hval, hb⟩
    exact (hk val hval).2 b hb

private theorem map_eq_and_inv_bindV {Γ₁ Γ₂ : List (Ty pqSig)} {a₁ a₂ t₁ t₂ : Ty pqSig}
    (projA : a₁.denote → a₂.denote) (projB : t₁.denote → t₂.denote) (P : t₁.denote → Prop)
    (m₁ : Comp pqxdhOps pqGapDhIface Γ₁ a₁)
    (k₁ : Var (a₁ :: Γ₁) a₁ → Comp pqxdhOps pqGapDhIface (a₁ :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (m₂ : Comp pqxdhOps pqGapDhIface Γ₂ a₂)
    (k₂ : Var (a₂ :: Γ₂) a₂ → Comp pqxdhOps pqGapDhIface (a₂ :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (hm : projA <$> m₁.eval ρ₁ = m₂.eval ρ₂)
    (hk : ∀ val ∈ support (m₁.eval ρ₁),
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons (projA val) ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (bindV m₁ k₁).eval ρ₁ = (bindV m₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((bindV m₁ k₁).eval ρ₁), P b := by
  simp only [bindV, Comp.eval]
  refine ⟨?_, ?_⟩
  · rw [← hm, bind_map_left, map_bind]
    exact bind_congr_support (m₁.eval ρ₁) _ _ fun val hval => (hk val hval).1
  · intro b hb
    rw [mem_support_bind_iff] at hb
    rcases hb with ⟨val, hval, hb⟩
    exact (hk val hval).2 b hb

private theorem map_eq_and_inv_bindV_joint {Γ₁ Γ₂ : List (Ty pqSig)} {a₁ a₂ t₁ t₂ : Ty pqSig}
    (projA : a₁.denote → a₂.denote) (projB : t₁.denote → t₂.denote)
    (Q : a₁.denote → Prop) (P : t₁.denote → Prop)
    (m₁ : Comp pqxdhOps pqGapDhIface Γ₁ a₁)
    (k₁ : Var (a₁ :: Γ₁) a₁ → Comp pqxdhOps pqGapDhIface (a₁ :: Γ₁) t₁) (ρ₁ : Env Γ₁)
    (m₂ : Comp pqxdhOps pqGapDhIface Γ₂ a₂)
    (k₂ : Var (a₂ :: Γ₂) a₂ → Comp pqxdhOps pqGapDhIface (a₂ :: Γ₂) t₂) (ρ₂ : Env Γ₂)
    (hm : projA <$> m₁.eval ρ₁ = m₂.eval ρ₂ ∧ ∀ r ∈ support (m₁.eval ρ₁), Q r)
    (hk : ∀ val, Q val →
      projB <$> (k₁ .vz).eval (.cons val ρ₁) = (k₂ .vz).eval (.cons (projA val) ρ₂) ∧
      ∀ b ∈ support ((k₁ .vz).eval (.cons val ρ₁)), P b) :
    projB <$> (bindV m₁ k₁).eval ρ₁ = (bindV m₂ k₂).eval ρ₂ ∧
      ∀ b ∈ support ((bindV m₁ k₁).eval ρ₁), P b :=
  map_eq_and_inv_bindV projA projB P m₁ k₁ ρ₁ m₂ k₂ ρ₂ hm.1 fun val hval => hk val (hm.2 val hval)

theorem sigSendCheckK_sim (S : Setup) (b : QueryBudget) : SigSendCheckSim S b := by
  intro opk c s' u i bu m0 m1 t xVal hbound hroom hInv _hfg
  let F := AuthKindFuels.ofBudget S b
  let s_l := projVal a1sStTy s'.1
  let x_l := projVal sendQTy xVal
  have hs_emb : embedVal a1sStTy s_l = s'.1 := embedVal_projVal a1sStTy s'.1
  have hBaseAtom : AuthBaseAtomOnlineBounded (c 0) (embedVal authStateTy s_l.1.1.2.1) := by
    have : embedVal authStateTy s_l.1.1.2.1 = s'.1.1.1.2.1 :=
      congrArg (fun z : (embedTy a1sStTy).denote => z.1.1.2.1) hs_emb
    rw [this]; exact hInv.base_online
  have hBaseVal : AuthBaseValOnlineBounded F.M_on s_l.1.1.2.1 :=
    AuthBaseValOnlineBounded.mono (hbound 0)
      ((AuthBaseAtomOnlineBounded.iff_embedVal s_l.1.1.2.1).mp hBaseAtom)
  have hLHS :
      (liftCs1 (a1sSendCheckLegC S F) (.pair (.fst (.var (.succ .zero))) (.var .zero))).eval
        (.cons xVal (.cons s' (.cons ((authCodec S).qenc t) .nil))) =
      embedVal (.sum a1sRS .unit) <$>
        (a1sSendCheckLegC S F).eval (.cons (s_l, x_l) .nil) := by
    rw [liftCs1_eval]
    rfl
  have hLegEq :
      (a1sSendCheckLegC S F).eval (.cons (s_l, x_l) .nil) =
        (a1sSendCheckC (Δ := [a1sStTy, sendQTy]) S b.q_total
          (.zero : Var [a1sStTy, sendQTy] a1sStTy)
          (.succ .zero : Var [a1sStTy, sendQTy] sendQTy)).eval
          (.cons s_l (.cons x_l .nil)) := by
    simp only [a1sSendCheckLegC, a1sSendCheckC, extractKC, letV, bindV, Comp.iteC,
      Comp.eval_letC, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get,
      a1sTp, a1sTpk, a1sBase, fsBase, a1sG]
    simp only [liftBase_eq_liftChal, Comp.eval_liftChal]
    refine bind_congr_eq ?_ fun fg _ => by cases fg <;> rfl
    apply congrArg _root_.SignalPqxdh.Security.embedPrim
    exact extractC_kon_eq S b _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl
      hBaseVal.principals_le hBaseVal.spkBundles_le
  refine ⟨?_, ?_⟩
  · rw [hLHS, hLegEq]
    have hEnvR : Env.cons s'.1 (.cons xVal .nil) = embedEnv (.cons s_l (.cons x_l .nil)) := by
      change Env.cons s'.1 (.cons xVal .nil) =
        Env.cons (embedVal a1sStTy s_l) (.cons (embedVal sendQTy x_l) .nil)
      rw [hs_emb, embedVal_projVal sendQTy xVal]
    rw [hEnvR, mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
  · intro r hr
    rw [hLHS] at hr
    have hr' : Sum.inl r ∈ embedVal (.sum a1sRS .unit) ''
        support ((a1sSendCheckLegC S F).eval (.cons (s_l, x_l) .nil)) :=
      Eq.mp (congrArg (Sum.inl r ∈ ·)
        (support_map (embedVal (.sum a1sRS .unit))
          ((a1sSendCheckLegC S F).eval (.cons (s_l, x_l) .nil)))) hr
    rcases hr' with ⟨y, hy, hyEq⟩
    simp only [a1sSendCheckLegC, letV, bindV, Comp.iteC, Comp.eval_letC, Comp.eval,
      Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get,
      support_bind, Set.mem_iUnion] at hy
    rcases hy with ⟨fg, _, hfgBr⟩
    cases fg with
    | none =>
      simp only [isSomeE, Expr.eval, Env.get, Bool.false_eq_true, ↓reduceIte,
        support_pure, Set.mem_singleton_iff] at hfgBr
      subst hfgBr
      cases hyEq
    | some fval =>
      simp only [isSomeE, Expr.eval, Env.get, ↓reduceIte, support_pure,
        Set.mem_singleton_iff] at hfgBr
      subst hfgBr
      have hrEq : r = embedVal a1sRS _ := Sum.inl.inj hyEq.symm
      have hSimEq : r.2.1.1.2 = s'.1.1.1.2 := by
        have h1 : r.2.1 = embedVal _ s_l.1 := congrArg (fun p => p.2.1) hrEq
        have h2 : embedVal _ s_l.1 = s'.1.1 := congrArg Prod.fst hs_emb
        exact congrArg (fun g => g.1.2) (h1.trans h2)
      dsimp only [SigAuthInv]
      rw [hSimEq]
      exact FgSimShadowInv.bump_unchanged t hroom hInv

@[reducible] private def putSauxAtom (aux : fgAuthShadowAuxTy.denote)
    (s : (embedTy sessAuxLegTy).denote) : fgAuthShadowAuxTy.denote :=
  (s.1, (s.2.1, (auxFgRoAvl aux, (s.2.2.1, (s.2.2.2, (auxFgRootRoAvl aux, auxRawAvl aux))))))

private theorem putSauxAtom_self (aux : fgAuthShadowAuxTy.denote) :
    putSauxAtom aux (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux))) = aux := by
  rcases aux with ⟨_, _, _, _, _, _, _⟩
  rfl

private theorem fgSend_commit_inv {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote}
    {sim_l : fgSimTy.denote} {t : AuthQuery S}
    (hs_emb : embedVal fgSimTy sim_l = sim)
    (hon : authSimPred S 0 t) (hn1 : ¬ authSimPred S 1 t) (hn2 : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux)
    (se : authSessionEntryTy.denote) (sid : sessionIdTy.denote)
    (fgL' : (Ty.list fgPatchEntryTy).denote)
    (fgSess' : (Ty.list seqFgEntryTy).denote) (fgCtr' : ℕ)
    (rootL' : (Ty.list rootEntryTy).denote)
    (rootSess' : (Ty.list seqRootEntryTy).denote) (rootCtr' : ℕ)
    (hFG : FgTableShadow S b (c 0 + 1) (c 1)
      (embedVal (.list fgPatchEntryTy) fgL') (auxFgRoAvl aux)
      (embedVal (.list seqFgEntryTy) fgSess') fgCtr')
    (hRT : RootTableShadow S b (c 0 + 1) (c 2)
      (embedVal (.list rootEntryTy) rootL') (auxFgRootRoAvl aux)
      (embedVal (.list seqRootEntryTy) rootSess') rootCtr') :
    let st'_l : authStateTy.denote :=
      (sim_l.1.1, (sim_l.1.2.1, (sim_l.1.2.2.1, (sim_l.1.2.2.2.1,
        (sim_l.1.2.2.2.2.1, (se :: sim_l.1.2.2.2.2.2.1,
          (sid :: sim_l.1.2.2.2.2.2.2.1, sim_l.1.2.2.2.2.2.2.2)))))))
    let sim'_l : fgSimTy.denote :=
      (st'_l, (fgL', (rootL', sim_l.2.2.2)))
    let saux'_l : sessAuxLegTy.denote :=
      (fgSess', (fgCtr', (rootSess', rootCtr')))
    FgSimShadowInv S b (bumpPred (authSimPred S) c t)
      (embedVal fgSimTy sim'_l) (putSauxAtom aux (embedVal sessAuxLegTy saux'_l)) := by
  intro st'_l sim'_l saux'_l
  have hb0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, hon]
  have hb1 : bumpPred (authSimPred S) c t 1 = c 1 := by simp [bumpPred, hn1]
  have hb2 : bumpPred (authSimPred S) c t 2 = c 2 := by simp [bumpPred, hn2]
  have hBaseEq : embedVal authStateTy sim_l.1 = sim.1 := congrArg Prod.fst hs_emb
  have hBaseVal : AuthBaseValOnlineBounded (c 0) sim_l.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal sim_l.1).mp (hBaseEq ▸ hInv.base_online)
  have hBaseNew : AuthBaseValOnlineBounded (c 0 + 1) st'_l :=
    { principals_le        := Nat.le_succ_of_le hBaseVal.principals_le
      spkBundles_le        := Nat.le_succ_of_le hBaseVal.spkBundles_le
      opkEntries_le        := Nat.le_succ_of_le hBaseVal.opkEntries_le
      sessions_le          := Nat.succ_le_succ hBaseVal.sessions_le
      usedSendSessions_le  := Nat.succ_le_succ hBaseVal.usedSendSessions_le
      usedRecvOPK_le       := Nat.le_succ_of_le hBaseVal.usedRecvOPK_le
      usedRecvNoOPK_le     := Nat.le_succ_of_le hBaseVal.usedRecvNoOPK_le
      seenKyberBaseKeys_le := Nat.le_succ_of_le hBaseVal.seenKyberBaseKeys_le
      sentOPKEvents_le     := Nat.le_succ_of_le hBaseVal.sentOPKEvents_le
      sentNoOPKEvents_le   := Nat.le_succ_of_le hBaseVal.sentNoOPKEvents_le
      recvdOPKEvents_le    := Nat.le_succ_of_le hBaseVal.recvdOPKEvents_le
      recvdNoOPKEvents_le  := Nat.le_succ_of_le hBaseVal.recvdNoOPKEvents_le
      advKeys_le           := Nat.le_succ_of_le hBaseVal.advKeys_le }
  have hPowsEq : (embedVal fgSimTy sim'_l).2.2.2.2.2.2 = sim.2.2.2.2.2.2 := by
    change (embedVal fgSimTy sim_l).2.2.2.2.2.2 = sim.2.2.2.2.2.2
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.2.2) hs_emb
  have hRespEq : (embedVal fgSimTy sim'_l).2.2.2.2.2.1 = sim.2.2.2.2.2.1 := by
    change (embedVal fgSimTy sim_l).2.2.2.2.2.1 = sim.2.2.2.2.2.1
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.2.1) hs_emb
  have hLogEq : (embedVal fgSimTy sim'_l).2.2.2.2.1 = sim.2.2.2.2.1 := by
    change (embedVal fgSimTy sim_l).2.2.2.2.1 = sim.2.2.2.2.1
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.1) hs_emb
  have hRawEq : (embedVal fgSimTy sim'_l).2.2.2.1 = sim.2.2.2.1 := by
    change (embedVal fgSimTy sim_l).2.2.2.1 = sim.2.2.2.1
    exact congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.1) hs_emb
  refine
    { counter_inv := hInv.counter_inv.bump t hroom
      base_online := by
        change AuthBaseAtomOnlineBounded _ (embedVal authStateTy st'_l)
        exact hb0 ▸ (AuthBaseAtomOnlineBounded.iff_embedVal st'_l).mpr hBaseNew
      pows_len    := by rw [hPowsEq, hb0]; exact Nat.le_succ_of_le hInv.pows_len
      resp_len    := by rw [hRespEq, hb0]; exact Nat.le_succ_of_le hInv.resp_len
      log_len     := by rw [hLogEq, hb1]; exact hInv.log_len
      fg_shadow   := by
        change FgTableShadow S b _ _ (embedVal (.list fgPatchEntryTy) fgL') (auxFgRoAvl aux)
          (embedVal (.list seqFgEntryTy) fgSess') fgCtr'
        simpa only [hb0, hb1] using hFG
      root_shadow := by
        change RootTableShadow S b _ _ (embedVal (.list rootEntryTy) rootL') (auxFgRootRoAvl aux)
          (embedVal (.list seqRootEntryTy) rootSess') rootCtr'
        simpa only [hb0, hb2] using hRT
      raw_rel     := by
        have hRawAux : auxRawAvl (putSauxAtom aux (embedVal sessAuxLegTy saux'_l)) = auxRawAvl aux := rfl
        rw [hRawEq, hRawAux]; exact hInv.raw_rel
      raw_len     := by rw [hRawEq, hb1]; exact hInv.raw_len }

set_option maxHeartbeats 1600000 in
private theorem fgSend2ShadowC_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (vpa : Var Γ₁ a1gParams2Ty) (vsim : Var Γ₂ fgSimTy) (vx : Var Γ₃ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (pa_l : a1gParams2Ty.denote) (sim_l : fgSimTy.denote)
    (saux_l : sessAuxLegTy.denote) (x_l : sendQTy.denote)
    (sim : (embedTy fgSimTy).denote) (aux : fgAuthShadowAuxTy.denote)
    (hpa : Env.get env (h₁.wk vpa) = pa_l)
    (hsim : Env.get env (h₂.wk vsim) = sim_l)
    (hx : Env.get env (h₃.wk vx) = x_l)
    (hs_emb : embedVal fgSimTy sim_l = sim)
    (hsaux_emb : embedVal sessAuxLegTy saux_l =
      (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux))))
    (hon : authSimPred S 0 t) (hn1 : ¬ authSimPred S 1 t) (hn2 : ¬ authSimPred S 2 t)
    (hbound : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux) :
    let F := AuthKindFuels.ofBudget S b
    let dropSaux : (Ty.prod authRespTy (.prod fgSimTy sessAuxLegTy)).denote → RSF.denote :=
      fun r => (r.1, r.2.1)
    let P : (Ty.prod authRespTy (.prod fgSimTy sessAuxLegTy)).denote → Prop :=
      fun out => FgSimShadowInv S b (bumpPred (authSimPred S) c t)
        (embedVal fgSimTy out.2.1) (putSauxAtom aux (embedVal sessAuxLegTy out.2.2))
    dropSaux <$> (fgSend2ShadowC S F opk).eval (.cons (pa_l, (sim_l, (saux_l, x_l))) .nil) =
      (fgSend2C S b.q_total opk vpa vsim vx).eval env ∧
    ∀ out ∈ support ((fgSend2ShadowC S F opk).eval (.cons (pa_l, (sim_l, (saux_l, x_l))) .nil)),
      P out := by
  intro F dropSaux P
  have hAbort : ∀ r : authRespTy.denote, P (r, (sim_l, saux_l)) := fun _ => by
    dsimp only [P]
    rw [hs_emb, hsaux_emb, putSauxAtom_self]
    exact FgSimShadowInv.bump_unchanged t hroom hInv
  have hBaseEq : embedVal authStateTy sim_l.1 = sim.1 := congrArg Prod.fst hs_emb
  have hBaseVal : AuthBaseValOnlineBounded F.M_on sim_l.1 :=
    AuthBaseValOnlineBounded.mono (hbound 0)
      ((AuthBaseAtomOnlineBounded.iff_embedVal sim_l.1).mp (hBaseEq ▸ hInv.base_online))
  have hPowsLen : sim_l.2.2.2.2.2.2.length ≤ F.M_on := by
    have hp : (embedVal (.list (.prod (B 32) (B 32))) sim_l.2.2.2.2.2.2).length =
        sim.2.2.2.2.2.2.length :=
      congrArg List.length (congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.2.2.2.2) hs_emb)
    rw [embedVal_length] at hp
    exact Nat.le_trans (hp ▸ hInv.pows_len) (hbound 0)
  have hStep := hInv.counter_inv.online_step_bounds hon hroom
  have hFgSh : FgTableShadow S b (c 0) (c 1)
      (embedVal (.list fgPatchEntryTy) sim_l.2.1) (auxFgRoAvl aux)
      (embedVal (.list seqFgEntryTy) saux_l.1) saux_l.2.1 := by
    have h1 : embedVal (.list fgPatchEntryTy) sim_l.2.1 = sim.2.1 :=
      congrArg (fun g : (embedTy fgSimTy).denote => g.2.1) hs_emb
    have h2 : embedVal (.list seqFgEntryTy) saux_l.1 = auxFgSess aux :=
      congrArg Prod.fst hsaux_emb
    have h3 : saux_l.2.1 = auxFgCtr aux :=
      congrArg (fun s : (embedTy sessAuxLegTy).denote => s.2.1) hsaux_emb
    rw [h1, h2, h3]; exact hInv.fg_shadow
  have hRtSh : RootTableShadow S b (c 0) (c 2)
      (embedVal (.list rootEntryTy) sim_l.2.2.1) (auxFgRootRoAvl aux)
      (embedVal (.list seqRootEntryTy) saux_l.2.2.1) saux_l.2.2.2 := by
    have h1 : embedVal (.list rootEntryTy) sim_l.2.2.1 = sim.2.2.1 :=
      congrArg (fun g : (embedTy fgSimTy).denote => g.2.2.1) hs_emb
    have h2 : embedVal (.list seqRootEntryTy) saux_l.2.2.1 = auxFgRootSess aux :=
      congrArg (fun s : (embedTy sessAuxLegTy).denote => s.2.2.1) hsaux_emb
    have h3 : saux_l.2.2.2 = auxFgRootCtr aux :=
      congrArg (fun s : (embedTy sessAuxLegTy).denote => s.2.2.2) hsaux_emb
    rw [h1, h2, h3]; exact hInv.root_shadow
  dsimp only [fgSend2ShadowC, fgSend2C]
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ pa_l rfl ?_
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ sim_l rfl ?_
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ saux_l rfl ?_
  refine eq_and_inv_letV_l dropSaux P _ _ _ _ _ x_l rfl ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _
    (by cases opk <;>
      simp only [sendGuardE, Bool.false_eq_true, ↓reduceIte, isSomeE,
        v, Expr.eval, Ext.refl_wk, Var.vz, Env.get, hx])
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ sim_l.1 rfl
    (by simp only [v, Expr.eval, hsim]) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ sim_l.2.2.2.2.2.2 rfl
    (by simp only [v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hsim]) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ x_l.2.2.1 rfl
    (by simp only [v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hx]) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ x_l.2.2.2.1 rfl
    (by simp only [v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hx]) ?_
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ x_l.2.2.2.2 rfl
    (by simp only [v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hx]) ?_
  let sid : sessionIdTy.denote :=
    if opk then .inl (x_l.1, x_l.2.1) else .inr (.inl (x_l.1, x_l.2.1))
  refine eq_and_inv_letV_val dropSaux P _ _ _ _ _ _ sid
    (by cases opk <;> rfl)
    (by cases opk <;>
      simp only [sid, Bool.false_eq_true, ↓reduceIte, v, Expr.eval, Ext.step_wk, Var.vs, Env.get, hx]) ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _
    (eAny_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl (fun _ => rfl) hBaseVal.usedSendSessions_le)
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) ?_
  refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _
    (eFind_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl
      (fun _ => by simp only [eval_natEq, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hx])
      hBaseVal.principals_le)
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _))
    fun uE => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
    (liftChal_gdh_congr _ _ _ _
      (findHonestC_kon_eq S b Var.vz _ _ Var.vz _ _ rfl rfl hBaseVal.principals_le))
    fun pp _ => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun fresh => ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
    (liftChal_gdh_congr _ _ _ _
      (koskBundleOkPowsC_kon_eq S b Var.vz Var.vz _ _ Var.vz Var.vz _ _
        rfl rfl rfl hBaseVal.principals_le hBaseVal.spkBundles_le hBaseVal.opkEntries_le hPowsLen))
    fun ok _ => ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _
    (by
      rcases pa_l with ⟨_, _, _ | (_ | _)⟩ <;> cases opk <;>
        simp only [Bool.false_eq_true, ↓reduceIte, eCaseSum, pa2Role, nat2Eq, eval_natEq,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hpa, hx])
    fun isT => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (by simp only [eval_sampleBytes32C]) fun ekRaw _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (by simp only [eval_sampleBytes32C]) fun coins _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (by simp only [eval_sampleBytes32C]) fun ephSk _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (by simp only [eval_sampleBytes32C]) fun spqrCoins _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
    (liftChal_gdh_congr _ _ _ _
      (resolveSigPkC_kon_eq S b Var.vz _ _ Var.vz _ _ rfl rfl hBaseVal.principals_le))
    fun spk _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun v1 _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun v2 _ => ?_
  refine eq_and_inv_iteC dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun enc _ => ?_
  refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _ rfl
    (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) fun sc => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun ekPkRaw _ => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun ekSk => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _
    (by cases isT <;> simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hpa])
    fun ekPk => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _
    (liftChal_gdh_congr _ _ _ _
      (lookupSpkSkC_kon_eq S b Var.vz Var.vz _ _ Var.vz Var.vz _ _
        rfl rfl rfl hBaseVal.spkBundles_le hPowsLen))
    fun spkSk _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun p1 _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun p2 _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideC_eval_congr _ _ _ _ rfl) fun p3 _ => ?_
  refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (twoSideOptC_eval_congr _ _ _ _ rfl) fun p4 _ => ?_
  refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun pk => ?_
  apply map_eq_and_inv_bindV_joint
  · refine patchWithShadowC_sim (S := S) (b := b) (nOn := c 0) (nRo := c 1)
      Var.vz Var.vz _ _ _ _ _ _ (auxFgRoAvl aux) ?_ ?_ hStep.2.1 ?_
    · rfl
    · simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]
    · exact hFgSh
  · intro dr hDr
    refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun ephPk _ => ?_
    refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun dhR _ => ?_
    refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (mkSecretPosC_eval_congr _ _ _ _ rfl) fun posR _ => ?_
    apply map_eq_and_inv_bindV_joint
    · refine rootPatchWithShadowC_sim (S := S) (b := b) (nOn := c 0) (nRoot := c 2)
        _ _ _ _ _ _ _ _ _ _ (auxFgRootRoAvl aux) ?_ ?_ ?_ hStep.2.2.1 ?_
      · rfl
      · rfl
      · simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]
      · exact hRtSh
    · intro rkOut hRkOut
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun mkSeed _ => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun ck11 _ => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun sp? _ => ?_
      refine eq_and_inv_caseOptV dropSaux P _ _ _ _ _ _ _ _ rfl
        (eq_and_inv_retC dropSaux P _ _ _ _ (by simp only [dropSaux, aNone, v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim]) (hAbort _)) fun sp => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun mk _ => ?_
      refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun ad => ?_
      refine eq_and_inv_bindV dropSaux P _ _ _ _ _ _ (queryPrimC_eval_congr _ _ _ _ _ rfl) fun ct _ => ?_
      refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun wm => ?_
      refine eq_and_inv_letV dropSaux P _ _ _ _ _ _
        (by
          cases pp with
          | none => rfl
          | some p =>
            exact Prod.ext
              (eAny_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl (fun _ => rfl) hBaseVal.spkBundles_le)
              (eAny_kon_eq b.q_total F.M_on _ _ _ _ _ _ rfl (fun _ => rfl) hBaseVal.spkBundles_le))
        fun honPair => ?_
      refine eq_and_inv_letV dropSaux P _ _ _ _ _ _ rfl fun se => ?_
      let st'_l : authStateTy.denote :=
        (sim_l.1.1, (sim_l.1.2.1, (sim_l.1.2.2.1, (sim_l.1.2.2.2.1,
          (sim_l.1.2.2.2.2.1, (se :: sim_l.1.2.2.2.2.2.1,
            (sid :: sim_l.1.2.2.2.2.2.2.1, sim_l.1.2.2.2.2.2.2.2)))))))
      let sim'_l : fgSimTy.denote := (st'_l, (dr.2.1, (rkOut.2.1, sim_l.2.2.2)))
      let saux'_l : sessAuxLegTy.denote := (dr.2.2.1, (dr.2.2.2, rkOut.2.2))
      let resp_l : authRespTy.denote :=
        match pp with
        | none => .inr (.inr (.inr (.inr (.inr (.inr (.inl (dr.1, (rkOut.1.1, (ck11, wm)))))))))
        | some _ => .inr (.inr (.inr (.inr (.inr (.inl wm)))))
      exact eq_and_inv_retC_val dropSaux P _ _ _ _ (resp_l, (sim'_l, saux'_l))
        (by cases pp <;> simp only [resp_l, sim'_l, st'_l, saux'_l, eCaseOpt, aSendFresh, aSendUnfresh,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get])
        (by cases pp <;> simp only [resp_l, sim'_l, st'_l, dropSaux, eCaseOpt, aSendFresh, aSendUnfresh,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, Var.vz, Var.vs, Env.get, hsim])
        (fgSend_commit_inv hs_emb hon hn1 hn2 hroom hInv se sid
          dr.2.1 dr.2.2.1 dr.2.2.2 rkOut.2.1 rkOut.2.2.1 rkOut.2.2.2 hDr hRkOut)

private theorem oracleComp_bind_pure_eq_map {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (mx : OracleComp spec α) (f : α → β) :
    (mx >>= fun a => pure (f a)) = f <$> mx := by
  rw [map_eq_bind_pure_comp]
  rfl

private theorem oracleComp_map_map {ι : Type} {spec : OracleSpec ι} {α β γ : Type}
    (f : α → β) (g : β → γ) (mx : OracleComp spec α) :
    g <$> (f <$> mx) = (fun x => g (f x)) <$> mx :=
  Functor.map_map f g mx

private theorem embed_bind_liftGdhToSign (sigB : ℕ)
    (mx : OracleComp _ (authRespTy.denote × fgSimTy.denote)) :
    (embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
      ((liftGdhToSign mx : OracleComp AuthSigDdhSpec _) >>= fun x => pure (x.1, x.2, sigB))) =
    ((fun x => (embedVal authRespTy x.1, (embedVal fgSimTy x.2, sigB))) <$>
      (liftGdhToSign mx : OracleComp AuthSigDdhSpec _)) := by
  rw [oracleComp_bind_pure_eq_map, oracleComp_map_map]
  rfl

theorem fgArmSim_sendOPK (S : Setup) (b : QueryBudget) :
    FgArmSim S b
      (fun p => AuthQuery.sendOPK p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (armEval_sendOPK S b) := by
  intro c pa sim sigB aux p t hbound hroom hInv
  rcases p with ⟨u, i, bu, m0, m1⟩
  let F := AuthKindFuels.ofBudget S b
  let pa_l := projVal a1gParams2Ty pa
  let sim_l := projVal fgSimTy sim
  let saux_atom : (embedTy sessAuxLegTy).denote :=
    (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux)))
  let saux_l := projVal sessAuxLegTy saux_atom
  let x_l : sendQTy.denote :=
    (u.val, (i.val, (bundleV (ℓ := 1) (Pt := _root_.SignalPqxdh.LegacyCosted.PTag) bu, (m0, m1))))
  have hx_l : projVal sendQTy (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) = x_l := by
    rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl
  let mxSign : OracleComp AuthSigDdhSpec
      (authRespTy.denote × fgSimTy.denote × sessAuxLegTy.denote) :=
    liftGdhToSign ((fgSend2ShadowC S F true).eval (.cons (pa_l, (sim_l, (saux_l, x_l))) .nil))
  have hArm : armEval_sendOPK S b pa sim sigB aux (u, (i, (bu, (m0, m1)))) =
      (fun out => (embedVal authRespTy out.1,
        ((embedVal fgSimTy out.2.1, sigB), putSauxAtom aux (embedVal sessAuxLegTy out.2.2)))) <$>
        mxSign := by
    simp only [armEval_sendOPK, fgCoreArm_send, Comp.eval, Expr.eval, Env.get, pure_bind]
    rw [liftGdh1_eval]
    have hArg : projVal (.prod a1gParams2Ty (.prod fgSimTy (.prod sessAuxLegTy sendQTy)))
        ((Expr.pair (exprRename Var.succ (.var (.succ .zero)))
          (.pair (exprRename Var.succ (.var (.succ (.succ .zero))))
            (.pair (auxSessSliceE (.snd .v0)) (exprRename Var.succ (.var .zero))))).eval
          (Env.cons (t := .prod .nat fgAuthShadowAuxTy) (sigB, aux)
            (.cons (t := embedTy sendQTy) (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1))))
              (.cons pa (.cons sim (.cons (t := .nat) sigB (.cons aux .nil))))))) =
        (pa_l, (sim_l, (saux_l, x_l))) := by
      dsimp only [exprRename, auxSessSliceE, auxFgSessE, auxFgCtrE, auxFgRootSessE, auxFgRootCtrE,
        Expr.eval, Env.get]
      exact congrArg (fun z => (pa_l, (sim_l, (saux_l, z)))) hx_l
    rw [hArg]
    refine (bind_map_left (embedVal (.prod authRespTy (.prod fgSimTy sessAuxLegTy)))
      mxSign _).trans ?_
    exact oracleComp_bind_pure_eq_map mxSign _
  have hon : authSimPred S 0 t := trivial
  have hn1 : ¬ authSimPred S 1 t := fun h => nomatch h
  have hn2 : ¬ authSimPred S 2 t := fun h => nomatch h
  refine ⟨?_, ?_⟩
  · rw [hArm, oracleComp_map_map]
    let q_l := (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
    have hLeg : legacyCoreArmEval S b pa sim sigB t =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa_l (.cons sim_l (.cons (t := .nat) sigB (.cons q_l .nil)))) := by
      rw [← mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
      unfold legacyCoreArmEval
      congr 1
      dsimp only [embedEnv, pa_l, sim_l, q_l]
      rw [embedVal_projVal, embedVal_projVal, authQenc_eq t]
      rfl
    rw [hLeg]
    dsimp only [legacyCoreArmComp, a1gPre2C, fgStep2C,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      bindV, caseSumV, v, q_l, t]
    simp only [Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vz, Env.get_vs,
      pure_bind, liftGdhComp_eval]
    rw [embed_bind_liftGdhToSign sigB]
    rw [← (fgSend2ShadowC_sim S b true _ _ _ _ c t
      pa_l sim_l saux_l x_l sim aux rfl rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).1, liftGdhToSign_map, oracleComp_map_map]
    rfl
  · intro pOut hpOut
    rw [hArm] at hpOut
    have hpImg := Eq.mp (congrArg (pOut ∈ ·) (support_map _ _)) hpOut
    rcases hpImg with ⟨out, houtSign, rfl⟩
    have hSim2 := (fgSend2ShadowC_sim S b true
      (.zero : Var [a1gParams2Ty, fgSimTy, sendQTy] a1gParams2Ty)
      (.succ .zero : Var [a1gParams2Ty, fgSimTy, sendQTy] fgSimTy)
      (.succ (.succ .zero) : Var [a1gParams2Ty, fgSimTy, sendQTy] sendQTy)
      (.cons pa_l (.cons sim_l (.cons x_l .nil))) c t pa_l sim_l saux_l x_l sim aux rfl rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).2
    exact hSim2 out (mem_support_liftGdhToSign houtSign)

theorem fgArmSim_sendNoOPK (S : Setup) (b : QueryBudget) :
    FgArmSim S b
      (fun p => AuthQuery.sendNoOPK p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (armEval_sendNoOPK S b) := by
  intro c pa sim sigB aux p t hbound hroom hInv
  rcases p with ⟨u, i, bu, m0, m1⟩
  let F := AuthKindFuels.ofBudget S b
  let pa_l := projVal a1gParams2Ty pa
  let sim_l := projVal fgSimTy sim
  let saux_atom : (embedTy sessAuxLegTy).denote :=
    (auxFgSess aux, (auxFgCtr aux, (auxFgRootSess aux, auxFgRootCtr aux)))
  let saux_l := projVal sessAuxLegTy saux_atom
  let x_l : sendQTy.denote :=
    (u.val, (i.val, (bundleV (ℓ := 1) (Pt := _root_.SignalPqxdh.LegacyCosted.PTag) bu, (m0, m1))))
  have hx_l : projVal sendQTy (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) = x_l := by
    rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl
  let mxSign : OracleComp AuthSigDdhSpec
      (authRespTy.denote × fgSimTy.denote × sessAuxLegTy.denote) :=
    liftGdhToSign ((fgSend2ShadowC S F false).eval (.cons (pa_l, (sim_l, (saux_l, x_l))) .nil))
  have hArm : armEval_sendNoOPK S b pa sim sigB aux (u, (i, (bu, (m0, m1)))) =
      (fun out => (embedVal authRespTy out.1,
        ((embedVal fgSimTy out.2.1, sigB), putSauxAtom aux (embedVal sessAuxLegTy out.2.2)))) <$>
        mxSign := by
    simp only [armEval_sendNoOPK, fgCoreArm_send, Comp.eval, Expr.eval, Env.get, pure_bind]
    rw [liftGdh1_eval]
    have hArg : projVal (.prod a1gParams2Ty (.prod fgSimTy (.prod sessAuxLegTy sendQTy)))
        ((Expr.pair (exprRename Var.succ (.var (.succ .zero)))
          (.pair (exprRename Var.succ (.var (.succ (.succ .zero))))
            (.pair (auxSessSliceE (.snd .v0)) (exprRename Var.succ (.var .zero))))).eval
          (Env.cons (t := .prod .nat fgAuthShadowAuxTy) (sigB, aux)
            (.cons (t := embedTy sendQTy) (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1))))
              (.cons pa (.cons sim (.cons (t := .nat) sigB (.cons aux .nil))))))) =
        (pa_l, (sim_l, (saux_l, x_l))) := by
      dsimp only [exprRename, auxSessSliceE, auxFgSessE, auxFgCtrE, auxFgRootSessE, auxFgRootCtrE,
        Expr.eval, Env.get]
      exact congrArg (fun z => (pa_l, (sim_l, (saux_l, z)))) hx_l
    rw [hArg]
    refine (bind_map_left (embedVal (.prod authRespTy (.prod fgSimTy sessAuxLegTy)))
      mxSign _).trans ?_
    exact oracleComp_bind_pure_eq_map mxSign _
  have hon : authSimPred S 0 t := trivial
  have hn1 : ¬ authSimPred S 1 t := fun h => nomatch h
  have hn2 : ¬ authSimPred S 2 t := fun h => nomatch h
  refine ⟨?_, ?_⟩
  · rw [hArm, oracleComp_map_map]
    let q_l := (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
    have hLeg : legacyCoreArmEval S b pa sim sigB t =
        embedVal (.prod authRespTy (.prod fgSimTy .nat)) <$>
          (legacyCoreArmComp S b).eval (.cons pa_l (.cons sim_l (.cons (t := .nat) sigB (.cons q_l .nil)))) := by
      rw [← mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
      unfold legacyCoreArmEval
      congr 1
      dsimp only [embedEnv, pa_l, sim_l, q_l]
      rw [embedVal_projVal, embedVal_projVal, authQenc_eq t]
      rfl
    rw [hLeg]
    dsimp only [legacyCoreArmComp, a1gPre2C, fgStep2C,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      bindV, caseSumV, v, q_l, t]
    simp only [Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_vz, Env.get_vs,
      pure_bind, liftGdhComp_eval]
    rw [embed_bind_liftGdhToSign sigB]
    rw [← (fgSend2ShadowC_sim S b false _ _ _ _ c t
      pa_l sim_l saux_l x_l sim aux rfl rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).1, liftGdhToSign_map, oracleComp_map_map]
    rfl
  · intro pOut hpOut
    rw [hArm] at hpOut
    have hpImg := Eq.mp (congrArg (pOut ∈ ·) (support_map _ _)) hpOut
    rcases hpImg with ⟨out, houtSign, rfl⟩
    have hSim2 := (fgSend2ShadowC_sim S b false
      (.zero : Var [a1gParams2Ty, fgSimTy, sendQTy] a1gParams2Ty)
      (.succ .zero : Var [a1gParams2Ty, fgSimTy, sendQTy] fgSimTy)
      (.succ (.succ .zero) : Var [a1gParams2Ty, fgSimTy, sendQTy] sendQTy)
      (.cons pa_l (.cons sim_l (.cons x_l .nil))) c t pa_l sim_l saux_l x_l sim aux rfl rfl rfl
      (embedVal_projVal fgSimTy sim) (embedVal_projVal sessAuxLegTy saux_atom)
      hon hn1 hn2 hbound hroom hInv).2
    exact hSim2 out (mem_support_liftGdhToSign houtSign)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimSend
