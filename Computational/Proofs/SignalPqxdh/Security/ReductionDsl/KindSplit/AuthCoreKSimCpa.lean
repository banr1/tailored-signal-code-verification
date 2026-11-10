/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSimTwoStage -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpaBase

/-!
# Two-Stage Forgetful Simulation for `AuthAeadCpa`

Proves `TwoStageForgetSim` between the kind-split shadow-indexed `aeadCpa1KeyKindProg` and the
reference atomic reduction `aeadCpaOldAtomicProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpa

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open Computational.Proofs.ReductionDsl.StepSimTwoStage (TwoStageForgetSim forgetPreOut)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedCtx embedEnv mapComp
   comp_queries_zero_of_zero mapComp_eval liftAuthHandle_eval
   aiAuthPrim tlAuthPrim)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery authSpec PrimBaseSpec)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy preKeyBundleTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext authHybridStateFixedTy emptyAuthHybridStFixedE
   initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB
   roFixedB roRootFixedB registerFixedB
   hkdfRoC rootRoC isAdvRegC isGameSpkC findHonestC isGameOpkC
   koskBundleOkC koskSenderOkC checkBundleProvenanceExactC
   v ahsfHybrid ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions ahsfMkSaltCache
   asPrincipals asSpkBundles asOpkEntries asUsedKyberTriples asRoCache asRootRoCache
   stUpd stMk eMap sendQTy recvQTy authRespTy letV bindV caseSumV RSF aNone)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (cpaStTy cpaPayloadTy finishCpaC spkHonIdealFromPeerC cpaInitC cpaResumeC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authFixedShadowStTy forgetAuthFixedShadow emptyRoBothAvlE
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (aeadCpa1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv
   AuthBaseValOnlineBounded AuthBaseAtomOnlineBounded
   AuthFixedValOnlineBounded AuthFixedAtomOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache
   RoBothShadowRel CacheStepAtMostOne
   authCpaShadowStTy forgetCpa aeadCpaOldAtomicProg
   AuthFixedShadowAt cpaShadowFixed
   cpaPayloadRoCache cpaPayloadRootRoCache CpaPausePayloadOk
   AuthCpaInv AuthCpaPauseInv dispatchAuthQEval dispatchAuthQ_eval_qenc)

open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpaBase
  (projEnv embedEnv_projEnv tlAuthPrim_unsupported_zero
   mapComp_tlAuthPrim_eval_embed mapComp_tlAuthPrim_eval
   mapComp_tlAuthPrim_congr mem_support_mapComp_tlAuthPrim
   atomRoCache_embedVal atomRootRoCache_embedVal
   cpaPayloadRoCache_embedVal cpaPayloadRootRoCache_embedVal
   prf_letV_eval prf_bindV_eval prf_caseOptV_eval
   prf_eFind_eq prf_eAny_eq prf_eMap_eq prf_findMV_min_eq
   prf_letV_congr prf_letV_congr_eq prf_bindV_congr
   prf_ite_congr prf_caseOptV_congr prf_caseSumV_congr
   findHonestC_prf_fuel_eq koskSenderOkC_fuel_eq
   hkdfRoC_fuel_eq hkdfRoC_step rootRoC_fuel_eq rootRoC_step
   support_prf_letV support_prf_bindV support_prf_bindV_any
   support_prf_ite support_prf_caseOptV support_prf_caseSumV support_prf_ret
   ext_step_wk ext_refl_wk env_get_succ env_get_zero
   cpaInitC_preserves finishCpaC_preserves
   cpaSendSlotKB_fuel_eq CpaSendSlotPost cpaSendSlotB_preserves)

private theorem bumpPred_online_slots {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    bumpPred (authSimPred S) c t 0 = c 0 + 1 ∧
    bumpPred (authSimPred S) c t 1 = c 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [bumpPred, hOn, ↓reduceIte]
  · simp only [bumpPred, hNotRo, ↓reduceIte, add_zero]
  · simp only [bumpPred, hNotRt, ↓reduceIte, add_zero]

private theorem bumpPred_ro_slots {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hNotOn : ¬ authSimPred S 0 t)
    (hRo : authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    bumpPred (authSimPred S) c t 0 = c 0 ∧
    bumpPred (authSimPred S) c t 1 = c 1 + 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [bumpPred, hNotOn, ↓reduceIte, add_zero]
  · simp only [bumpPred, hRo, ↓reduceIte]
  · simp only [bumpPred, hNotRt, ↓reduceIte, add_zero]

private theorem bumpPred_roRoot_slots {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hNotOn : ¬ authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hRt : authSimPred S 2 t) :
    bumpPred (authSimPred S) c t 0 = c 0 ∧
    bumpPred (authSimPred S) c t 1 = c 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [bumpPred, hNotOn, ↓reduceIte, add_zero]
  · simp only [bumpPred, hNotRo, ↓reduceIte, add_zero]
  · simp only [bumpPred, hRt, ↓reduceIte]

private theorem cpa_pauseInv_of_online {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {t : AuthQuery S} {p' : (embedTy cpaPayloadTy).denote} {s' s'₁ : authCpaShadowStTy.denote}
    (hInv : AuthCpaInv S b c s')
    (hShEq : cpaShadowFixed s'₁ = cpaShadowFixed s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hPay : CpaPausePayloadOk (c 0) (c 1) (c 2) p' s'₁) :
    AuthCpaPauseInv S b (bumpPred (authSimPred S) c t) p' s'₁ := by
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c t hOn hNotRo hNotRt
  refine ⟨hInv.counter_inv.bump t hroom, ?_, ?_, ?_⟩
  · omega
  · have hsub : bumpPred (authSimPred S) c t 0 - 1 = c 0 := by omega
    rw [hsub, hc1, hc2]
    change AuthFixedShadowAt S b (c 0) (c 0 + c 1) (c 0 + c 2) (cpaShadowFixed s'₁)
    rw [hShEq]
    exact hInv.shadow_ok
  · have hsub : bumpPred (authSimPred S) c t 0 - 1 = c 0 := by omega
    rw [hsub, hc1, hc2]
    exact hPay

private theorem pause_counter_bounds (S : Setup) (b : QueryBudget) {c : Fin 4 → ℕ}
    (hCnt : AuthCounterInv b c) (hOne : 1 ≤ c 0) :
    let F := AuthKindFuels.ofBudget S b
    (c 0 - 1) + 1 = c 0 ∧ c 0 ≤ F.K_on ∧ c 0 ≤ b.q_total ∧
    c 0 + c 1 ≤ F.K_ro ∧ c 0 + c 2 ≤ F.K_ro ∧ F.K_ro ≤ F.K_cap := by
  have := hCnt.on_le; have := hCnt.ro_le; have := hCnt.roRoot_le
  have := hCnt.tot_le; have := hCnt.sum_eq
  dsimp only [AuthKindFuels.ofBudget]; omega

private theorem cpaRecvKC_fuel_eq (S : Setup) (K_on K_ro Q : ℕ) {n : ℕ}
    (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst)))
    (hOn : n ≤ K_on) (hOnQ : K_on ≤ Q)
    (hRo : (valRoCache (env.get (h₁.wk fhst)).1.1).length ≤ K_ro)
    (hRt : (valRootRoCache (env.get (h₁.wk fhst)).1.1).length ≤ K_ro)
    (hRoQ : K_ro ≤ Q) :
    (AuthCoreKArmsBase.cpaRecvKC S K_on K_ro opk fhst x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S Q opk fhst x).eval env := by
  unfold AuthCoreKArmsBase.cpaRecvKC _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC
  refine prf_letV_congr_eq rfl fun hstVal hhst => ?_
  refine prf_letV_congr_eq rfl fun stVal hst => ?_
  have hhst₀ : hstVal = (env.get (h₁.wk fhst)).1 := by
    simpa only [v, ahsfHybrid, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hhst
  have hst₀ : stVal = (env.get (h₁.wk fhst)).1.1 := by
    simpa only [hhst₀, v, ahsBase, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hst
  have hb_st : AuthBaseValOnlineBounded n stVal := hst₀ ▸ hb.base_le
  have hRo_st : (valRoCache stVal).length ≤ K_ro := hst₀ ▸ hRo
  have hRt_st : (valRootRoCache stVal).length ≤ K_ro := hst₀ ▸ hRt
  have hPrinOn : stVal.2.2.1.length ≤ K_on := Nat.le_trans hb_st.principals_le hOn
  have hSpkOn : stVal.2.2.2.1.length ≤ K_on := Nat.le_trans hb_st.spkBundles_le hOn
  have hOpkOn : stVal.2.2.2.2.1.length ≤ K_on := Nat.le_trans hb_st.opkEntries_le hOn
  iterate 5 refine prf_letV_congr rfl fun _ => ?_
  refine prf_ite_congr rfl rfl (prf_ite_congr ?_ rfl ?_)
  · cases opk
    · have hL := Nat.le_trans hb_st.usedRecvNoOPK_le hOn; exact prf_eAny_eq K_on Q _ _ _ hL (Nat.le_trans hL hOnQ)
    · have hL := Nat.le_trans hb_st.usedRecvOPK_le hOn; exact prf_eAny_eq K_on Q _ _ _ hL (Nat.le_trans hL hOnQ)
  refine prf_bindV_congr (koskSenderOkC_fuel_eq S K_on Q _ _ _
    (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hb_st) hOn hOnQ) fun _ => ?_
  refine prf_ite_congr rfl rfl ?_
  refine prf_caseOptV_congr (prf_eFind_eq K_on Q _ _ _
    (by simpa only [v, asPrincipals, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hPrinOn)
    (Nat.le_trans (by simpa only [v, asPrincipals, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hPrinOn) hOnQ)) rfl fun _ => ?_
  refine prf_caseOptV_congr (prf_eFind_eq K_on Q _ _ _
    (by simpa only [v, asSpkBundles, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hSpkOn)
    (Nat.le_trans (by simpa only [v, asSpkBundles, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hSpkOn) hOnQ)) rfl fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr ?_ fun _ => ?_
  · cases opk
    · rfl
    · simp only [↓reduceIte]; refine prf_caseOptV_congr (prf_eFind_eq K_on Q _ _ _ ?_ ?_) rfl fun _ => rfl
      · simpa only [v, asOpkEntries, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hOpkOn
      · exact Nat.le_trans (by simpa only [v, asOpkEntries, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hOpkOn) hOnQ
  refine prf_caseSumV_congr rfl (fun _ => rfl) fun _ => ?_
  refine prf_letV_congr (AuthCoreKSimPrfBase.kyberCheckE_fuel_eq _ _ _
    (by simpa only [v, asUsedKyberTriples, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hb_st.seenKyberBaseKeys_le)
    hOn (Nat.le_trans hOn hOnQ)) fun _ => ?_
  iterate 2 refine prf_bindV_congr rfl fun _ => ?_
  refine prf_ite_congr rfl rfl (prf_bindV_congr rfl fun _ => prf_caseOptV_congr rfl rfl fun _ => ?_)
  refine prf_letV_congr rfl fun _ => prf_letV_congr_eq rfl fun hstDecVal hhstDec => ?_
  have hIdealOn : hstDecVal.2.2.2.length ≤ K_on := by
    have hId : hstDecVal.2.2.2 = (env.get (h₁.wk fhst)).1.2.2.2 := by
      simp only [hhstDec, hhst₀, v, ahsIdealSessions, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    exact hId ▸ Nat.le_trans hb.idealSessions_le hOn
  iterate 4 refine prf_bindV_congr rfl fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  refine prf_letV_congr_eq rfl fun cacheVal hcache => ?_
  have hCacheOn : cacheVal.length ≤ K_on := by
    have hC : cacheVal = (env.get (h₁.wk fhst)).2.2.1 := by
      simpa only [v, ahsfMkSaltCache, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hcache
    exact hC ▸ Nat.le_trans hb.mkSaltCache_le hOn
  refine prf_letV_congr rfl fun _ => prf_bindV_congr (findHonestC_prf_fuel_eq S K_on Q _ _ _
    (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hb_st) hOn hOnQ) fun _ => ?_
  iterate 4 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr (prf_findMV_min_eq K_on Q S.N_sess_tot _ _ _
    (by simpa only [v, ahsIdealSessions, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hIdealOn) hOnQ) fun _ => ?_
  refine prf_bindV_congr (prf_caseOptV_congr rfl (prf_ite_congr rfl rfl
    (hkdfRoC_fuel_eq K_ro Q _ _ _ (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hRo_st)
      (Nat.le_trans (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hRo_st) hRoQ))) fun _ => rfl) fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  iterate 2 refine prf_bindV_congr rfl fun _ => ?_
  refine prf_bindV_congr (prf_caseOptV_congr rfl (prf_ite_congr rfl rfl
    (rootRoC_fuel_eq K_ro Q _ _ _ _ (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hRt_st)
      (Nat.le_trans (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hRt_st) hRoQ))) fun _ => rfl) fun _ => ?_
  iterate 3 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr rfl fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr rfl fun _ => prf_letV_congr rfl fun _ => prf_caseOptV_congr rfl rfl fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr (prf_caseOptV_congr rfl rfl fun _ =>
    prf_ite_congr rfl rfl (prf_ite_congr rfl (prf_letV_congr rfl fun _ =>
      prf_caseOptV_congr (prf_eFind_eq K_on Q _ _ _
        (by simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hCacheOn)
        (Nat.le_trans (by simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hCacheOn) hOnQ))
        rfl fun _ => rfl) rfl)) fun _ => ?_
  iterate 4 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr rfl fun _ => prf_caseOptV_congr rfl rfl fun _ => ?_
  refine prf_bindV_congr (findHonestC_prf_fuel_eq S K_on Q _ _ _
    (by simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hb_st) hOn hOnQ) fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  refine prf_letV_congr ?_ fun _ => rfl
  cases opk
  · rfl
  · simp only [↓reduceIte, stUpd, stMk, Expr.eval]
    refine congrArg (fun opksV => (_, _, _, _, opksV, _))
      (prf_eMap_eq K_on Q _ _ _
        (by simpa only [v, asOpkEntries, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hOpkOn)
        (Nat.le_trans (by simpa only [v, asOpkEntries, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hOpkOn) hOnQ))

private theorem prf_eMap_length_le {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (ρ : Env Γ) {m : ℕ}
    (h : (xs.eval ρ).length ≤ m) :
    ((eMap Q xs f).eval ρ).length ≤ m := by
  simp only [eMap, Expr.eval, List.length_map]
  exact Nat.le_trans (List.length_take_le' Q _) h

private theorem cpaRecvC_preserves (S : Setup) (Q : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst)))
    (hRoQ : (valRoCache (env.get (h₁.wk fhst)).1.1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk fhst)).1.1).length ≤ Q) :
    ∀ out ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S Q opk fhst x).eval env),
      AuthFixedValOnlineBounded (n + 1) out.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk fhst)).1.1) (valRoCache out.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk fhst)).1.1) (valRootRoCache out.2.1.1) := by
  have hb' := hb.mono (Nat.le_succ n)
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC
  apply support_prf_letV; intro hstVal hhst; apply support_prf_letV; intro stVal hst
  have hhst₀ : hstVal = (env.get (h₁.wk fhst)).1 := by
    simpa only [v, ahsfHybrid, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hhst
  have hst₀ : stVal = (env.get (h₁.wk fhst)).1.1 := by
    simpa only [hhst₀, v, ahsBase, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hst
  have hb_st : AuthBaseValOnlineBounded n stVal := hst₀ ▸ hb.base_le
  apply support_prf_letV; intro _ _; apply support_prf_letV; intro noneRcVal hnoneRc
  have hAbort : AuthFixedValOnlineBounded (n + 1) noneRcVal.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk fhst)).1.1) (valRoCache noneRcVal.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk fhst)).1.1) (valRootRoCache noneRcVal.2.1.1) := by
    simp only [hnoneRc, v, ahsfHybrid, ahsfMkSaltCache, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    exact ⟨⟨hb'.base_le, hb'.initKemRecs_le, hb'.recvKemRecs_le, hb'.idealSessions_le, hb'.mkSaltCache_le⟩,
      CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
  iterate 3 (apply support_prf_letV; intro _ _)
  apply support_prf_ite; · intro _; apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_ite; · intro _; apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_bindV_any; intro _
  apply support_prf_ite; · intro _; apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_caseOptV; · apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_caseOptV; · apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_bindV_any; intro _
  apply support_prf_caseSumV; · intro _; apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_letV; intro kcVal hkc
  have hkcLen : kcVal.2.length ≤ n + 1 := by
    rw [hkc]
    exact AuthCoreKSimPrfBase.kyberCheckE_snd_len_le Q _ _ _
      (by simpa only [v, asUsedKyberTriples, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hb_st.seenKyberBaseKeys_le)
  iterate 2 (apply support_prf_bindV_any; intro _)
  apply support_prf_ite; · intro _; apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_bindV_any; intro _
  apply support_prf_caseOptV; · apply support_prf_ret; simpa only [v, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _; apply support_prf_letV; intro _ _; apply support_prf_letV; intro hstDecVal hhstDec
  iterate 4 (apply support_prf_bindV_any; intro _)
  iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_letV; intro cacheVal hcache
  have hcache₀ : cacheVal = (env.get (h₁.wk fhst)).2.2.1 := by
    simpa only [v, ahsfMkSaltCache, Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hcache
  apply support_prf_letV; intro _ _
  apply support_prf_bindV_any; intro _
  iterate 4 (apply support_prf_letV; intro _ _)
  apply support_prf_bindV_any; intro _
  apply support_prf_bindV; intro drOut hdrOut
  have hdr : CacheStepAtMostOne (valRoCache (env.get (h₁.wk fhst)).1.1) drOut.2 := by
    revert drOut
    apply support_prf_caseOptV
    · apply support_prf_ite
      · intro _; apply support_prf_bindV_any; intro _; apply support_prf_ret
        simp only [hst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRoCache, valRoCache,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
        exact CacheStepAtMostOne.refl _
      · intro _ d hd
        have hstep := fun hlen => hkdfRoC_step Q _ _ _ hlen d hd
        simpa only [hst₀, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using
          hstep (by simpa only [hst₀, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hRoQ)
    · intro _; apply support_prf_ret
      simp only [hst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRoCache, valRoCache,
        Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
      exact CacheStepAtMostOne.refl _
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro roC'Val hroC'
  have hroC'₀ : roC'Val = drOut.2 := by
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hroC'
  iterate 2 (apply support_prf_bindV_any; intro _)
  apply support_prf_bindV; intro rkOut hrkOut
  have hrk : CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk fhst)).1.1) rkOut.2 := by
    revert rkOut
    apply support_prf_caseOptV
    · apply support_prf_ite
      · intro _
        apply support_prf_bindV_any; intro _
        apply support_prf_bindV_any; intro _
        apply support_prf_ret
        simp only [hst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRootRoCache, valRootRoCache,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
        exact CacheStepAtMostOne.refl _
      · intro _ d hd
        have hstep := fun hlen => rootRoC_step Q _ _ _ _ hlen d hd
        simpa only [hst₀, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using
          hstep (by simpa only [hst₀, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hRtQ)
    · intro _; apply support_prf_ite
      · intro _; apply support_prf_ret
        simp only [hst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRootRoCache, valRootRoCache,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
        exact CacheStepAtMostOne.refl _
      · intro _
        apply support_prf_bindV_any; intro _
        apply support_prf_bindV_any; intro _
        apply support_prf_ret
        simp only [hst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRootRoCache, valRootRoCache,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
        exact CacheStepAtMostOne.refl _
  iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_letV; intro rootC'Val hrootC'
  have hrootC'₀ : rootC'Val = rkOut.2 := by
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hrootC'
  apply support_prf_bindV_any; intro _
  iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_bindV_any; intro _
  apply support_prf_letV; intro hstDecVVal hhstDecV
  apply support_prf_caseOptV
  · apply support_prf_ret
    simp only [hhstDecV, hhstDec, hhst₀, hcache₀,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    exact ⟨⟨hb'.base_le, hb'.initKemRecs_le, Nat.succ_le_succ hb.recvKemRecs_le,
      hb'.idealSessions_le, hb'.mkSaltCache_le⟩,
      CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
  intro _
  iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_bindV; intro mkOut hmkOut
  have hmkLen : mkOut.2.length ≤ n + 1 := by
    have hcLen : cacheVal.length ≤ n := hcache₀ ▸ hb.mkSaltCache_le
    revert mkOut
    apply support_prf_caseOptV
    · apply support_prf_ite <;>
        (intro _; apply support_prf_bindV_any; intro _; apply support_prf_ret;
         simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
           Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero];
         exact Nat.le_succ_of_le hcLen)
    · intro _; apply support_prf_ite
      · intro _; apply support_prf_ret
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
        exact Nat.le_succ_of_le hcLen
      · intro _; apply support_prf_ite
        · intro _; apply support_prf_letV; intro _ _; apply support_prf_caseOptV
          · apply support_prf_bindV_any; intro _; apply support_prf_ret
            simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
              Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, List.length_cons]
            exact Nat.succ_le_succ hcLen
          · intro _; apply support_prf_ret
            simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
              Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
            exact Nat.le_succ_of_le hcLen
        · intro _; apply support_prf_bindV_any; intro _; apply support_prf_ret
          simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
            Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
          exact Nat.le_succ_of_le hcLen
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro cache'Val hcache'
  have hcache'Len : cache'Val.length ≤ n + 1 := by
    simpa only [hcache', _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hmkLen
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro noneDecVal hnoneDec
  apply support_prf_bindV_any; intro _
  apply support_prf_caseOptV
  · apply support_prf_ret
    simp only [hnoneDec, hhstDecV, hhstDec, hhst₀,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    exact ⟨⟨hb'.base_le, hb'.initKemRecs_le, Nat.succ_le_succ hb.recvKemRecs_le,
      hb'.idealSessions_le, hcache'Len⟩,
      CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
  intro _
  apply support_prf_bindV_any; intro _
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro stDVal hstD
  apply support_prf_letV; intro base'Val hbase'
  apply support_prf_ret
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte] at hbase'
    simp only [hbase', hstD, hhstDec, hhst₀, hst₀, hroC'₀, hrootC'₀,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSecb,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asHasWonAuth,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asPrincipals,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSpkBundles,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asOpkEntries,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedSendSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvOPK,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvNoOPK,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentNoOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdNoOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asAdvKeys,
      valRoCache, valRootRoCache,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    exact ⟨⟨⟨hb'.base_le.principals_le, hb'.base_le.spkBundles_le, hb'.base_le.opkEntries_le,
      hb'.base_le.sessions_le, hb'.base_le.usedSendSessions_le, hb'.base_le.usedRecvOPK_le,
      Nat.succ_le_succ hb.base_le.usedRecvNoOPK_le, hkcLen,
      hb'.base_le.sentOPKEvents_le, hb'.base_le.sentNoOPKEvents_le,
      hb'.base_le.recvdOPKEvents_le, hb'.base_le.recvdNoOPKEvents_le, hb'.base_le.advKeys_le⟩,
      hb'.initKemRecs_le, Nat.succ_le_succ hb.recvKemRecs_le, hb'.idealSessions_le, hcache'Len⟩,
      hdr, hrk⟩
  · simp only [↓reduceIte] at hbase'
    simp only [hbase', hstD, hhstDec, hhst₀, hst₀, hroC'₀, hrootC'₀,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSecb,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asHasWonAuth,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asPrincipals,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSpkBundles,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedSendSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvOPK,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvNoOPK,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentNoOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdNoOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asAdvKeys,
      valRoCache, valRootRoCache,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    refine ⟨⟨⟨hb'.base_le.principals_le, hb'.base_le.spkBundles_le,
      prf_eMap_length_le Q _ _ _ ?_,
      hb'.base_le.sessions_le, hb'.base_le.usedSendSessions_le,
      Nat.succ_le_succ hb.base_le.usedRecvOPK_le, hb'.base_le.usedRecvNoOPK_le, hkcLen,
      hb'.base_le.sentOPKEvents_le, hb'.base_le.sentNoOPKEvents_le,
      hb'.base_le.recvdOPKEvents_le, hb'.base_le.recvdNoOPKEvents_le, hb'.base_le.advKeys_le⟩,
      hb'.initKemRecs_le, Nat.succ_le_succ hb.recvKemRecs_le, hb'.idealSessions_le, hcache'Len⟩,
      hdr, hrk⟩
    simpa only [hst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asOpkEntries,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using
      hb'.base_le.opkEntries_le

private def ren2 {Δ : List (Ty pqSig)} {A B : Ty pqSig} (vA : Var Δ A) (vB : Var Δ B) :
    ∀ {t}, Var [A, B] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB

private def ren4 {Δ : List (Ty pqSig)} {A B C D : Ty pqSig}
    (vA : Var Δ A) (vB : Var Δ B) (vC : Var Δ C) (vD : Var Δ D) :
    ∀ {t}, Var [A, B, C, D] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB
  | _, .succ (.succ .zero) => vC
  | _, .succ (.succ (.succ .zero)) => vD

private theorem compRename_ren2_eval {A B out : Ty pqSig} {Δ : List (Ty pqSig)}
    (c0 : Comp pqxdhOps pqPrimIface [A, B] out)
    (c : Comp pqxdhOps pqPrimIface Δ out)
    (vA : Var Δ A) (vB : Var Δ B) (env : Env Δ)
    (hRen : Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 vA vB) c0 = c) :
    c.eval env = c0.eval (.cons (env.get vA) (.cons (env.get vB) .nil)) := by
  rw [← hRen]
  refine Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval c0 (ren2 vA vB) _ env ?_
  intro _ v
  cases v with
  | zero => rfl
  | succ v => cases v with
    | zero => rfl
    | succ v => nomatch v

private theorem compRename_ren4_eval {A B C D out : Ty pqSig} {Δ : List (Ty pqSig)}
    (c0 : Comp pqxdhOps pqPrimIface [A, B, C, D] out)
    (c : Comp pqxdhOps pqPrimIface Δ out)
    (vA : Var Δ A) (vB : Var Δ B) (vC : Var Δ C) (vD : Var Δ D) (env : Env Δ)
    (hRen : Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren4 vA vB vC vD) c0 = c) :
    c.eval env = c0.eval (.cons (env.get vA) (.cons (env.get vB)
      (.cons (env.get vC) (.cons (env.get vD) .nil)))) := by
  rw [← hRen]
  refine Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval c0 (ren4 vA vB vC vD) _ env ?_
  intro _ v
  cases v with
  | zero => rfl
  | succ v => cases v with
    | zero => rfl
    | succ v => cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => nomatch v

private theorem liftAuthPrim1_eval {a r : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (AuthCoreKArms.liftAuthPrim1 c e).eval ρ =
      (mapComp tlAuthPrim c).eval (.cons (e.eval ρ) .nil) := by
  simp only [AuthCoreKArms.liftAuthPrim1, Comp.eval, pure_bind]
  exact Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval _ _ _ _
    (fun v => by cases v with | zero => rfl | succ v => nomatch v)

private theorem mapComp_tlAuthPrim_eval_single {A out : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [A] out)
    (a : (embedTy A).denote) :
    (mapComp tlAuthPrim c).eval (.cons a .nil) =
      embedVal out <$> c.eval (.cons (projVal A a) .nil) := by
  have hEnv : (Env.cons a Env.nil : Env (embedCtx [A])) =
      embedEnv (.cons (projVal A a) .nil) := by
    simp only [embedEnv, Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal]
  exact (congrArg (mapComp tlAuthPrim c).eval hEnv).trans
    (mapComp_tlAuthPrim_eval_embed c (.cons (projVal A a) .nil))

private theorem mapComp_tlAuthPrim_eval_pair {A B out : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [A, B] out)
    (a : (embedTy A).denote) (b : (embedTy B).denote) :
    (mapComp tlAuthPrim c).eval (.cons a (.cons b .nil)) =
      embedVal out <$> c.eval (.cons (projVal A a) (.cons (projVal B b) .nil)) := by
  have hEnv : (Env.cons a (Env.cons b Env.nil) : Env (embedCtx [A, B])) =
      embedEnv (.cons (projVal A a) (.cons (projVal B b) .nil)) := by
    simp only [embedEnv, Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal]
  exact (congrArg (mapComp tlAuthPrim c).eval hEnv).trans
    (mapComp_tlAuthPrim_eval_embed c (.cons (projVal A a) (.cons (projVal B b) .nil)))

private theorem liftAuthPrim1_let2_eval {arg out : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ out)
    (hRen : Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren2 (.succ .zero) .zero)
      (step (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
        (Δ := [authHybridStateFixedTy, arg]) .zero .zero) =
      step (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero)
    {Γ : List (Ty pqAtomicSig)}
    (s' : authCpaShadowStTy.denote) (xA : (embedTy arg).denote) (ρ : Env Γ) :
    (AuthCoreKArms.liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       step fhst x)
      (.pair (.snd (.snd (.fst .v1))) .v0)).eval (.cons xA (.cons s' ρ)) =
    (mapComp tlAuthPrim
      (step (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
        (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval
      (.cons s'.1.2.2 (.cons xA .nil)) := by
  have h0 := liftAuthPrim1_eval
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
     step fhst x)
    (.pair (.snd (.snd (.fst .v1))) .v0) (.cons xA (.cons s' ρ))
  have h1 := mapComp_tlAuthPrim_eval_single (A := .prod authHybridStateFixedTy arg)
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
     step fhst x)
    (s'.1.2.2, xA)
  have h2 := mapComp_tlAuthPrim_eval_pair
    (step (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
      (Δ := [authHybridStateFixedTy, arg]) .zero .zero)
    s'.1.2.2 xA
  have hInner :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       step fhst x).eval
        (.cons (projVal (.prod authHybridStateFixedTy arg) (s'.1.2.2, xA)) .nil) =
      (step (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
        (Δ := [authHybridStateFixedTy, arg]) .zero .zero).eval
        (.cons (projVal authHybridStateFixedTy s'.1.2.2) (.cons (projVal arg xA) .nil)) := by
    rw [prf_letV_eval, prf_letV_eval]
    dsimp only [Expr.eval, Env.get, projVal]
    exact compRename_ren2_eval _ _ (.succ .zero) .zero _ hRen
  exact h0.trans (h1.trans ((congrArg (Functor.map _) hInner).trans h2.symm))

private theorem cpaBaseArmC_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (stepK stepOld : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)}
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    (hRenK : Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren2 (.succ .zero) .zero)
      (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
        (Δ := [authHybridStateFixedTy, arg]) .zero .zero) =
      stepK (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero)
    {nOn nRo nRoot : ℕ} {Γ : List (Ty pqAtomicSig)}
    (s' : authCpaShadowStTy.denote) (xA : (embedTy arg).denote) (ρ : Env Γ)
    (hEq : (mapComp tlAuthPrim
        (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval
        (.cons s'.1.2.2 (.cons xA .nil)) =
      (mapComp tlAuthPrim
        (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval
        (.cons s'.1.2.2 (.cons xA .nil)))
    (hPres : ∀ rsf ∈ support ((mapComp tlAuthPrim
        (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval
        (.cons s'.1.2.2 (.cons xA .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, s'.2)) :
    Prod.map id forgetCpa <$>
      (AuthCoreKArms.cpaBaseArmC S stepK).eval (.cons xA (.cons s' ρ)) =
      (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, rsf.2)))) <$>
        (mapComp tlAuthPrim
          (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval
          (.cons s'.1.2.2 (.cons xA .nil)) ∧
    ∀ p ∈ support ((AuthCoreKArms.cpaBaseArmC S stepK).eval (.cons xA (.cons s' ρ))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (cpaShadowFixed p.2) := by
  dsimp only [AuthCoreKArms.cpaBaseArmC, AuthCoreKArms.cpaRebuildE, Comp.eval]
  rw [liftAuthPrim1_let2_eval stepK hRenK s' xA ρ]
  constructor
  · rw [hEq, map_bind, map_eq_bind_pure_comp]
    congr 1
  · intro p hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨rsf, hrsf, hp'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v2, mem_support_pure_iff] at hp'
    subst hp'
    exact hPres rsf hrsf

private theorem cacheStep_embed_ro {st st' : authStateTy.denote}
    (h : CacheStepAtMostOne (valRoCache st) (valRoCache st')) :
    CacheStepAtMostOne (atomRoCache (embedVal authStateTy st))
      (atomRoCache (embedVal authStateTy st')) := by
  simpa only [atomRoCache_embedVal] using h

private theorem cacheStep_embed_root {st st' : authStateTy.denote}
    (h : CacheStepAtMostOne (valRootRoCache st) (valRootRoCache st')) :
    CacheStepAtMostOne (atomRootRoCache (embedVal authStateTy st))
      (atomRootRoCache (embedVal authStateTy st')) := by
  simpa only [atomRootRoCache_embedVal] using h

set_option maxRecDepth 4096 in
private theorem cpaRecvKC_ren2 (S : Setup) (K_on K_ro : ℕ) (opk : Bool) :
    let RTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren2 (.succ .zero) .zero)
      (AuthCoreKArms.cpaRecvKC S K_on K_ro opk
        (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
        (Δ := [authHybridStateFixedTy, RTy]) .zero .zero) =
    AuthCoreKArms.cpaRecvKC S K_on K_ro opk
      (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy RTy])
      (Γ₂ := [RTy, authHybridStateFixedTy, .prod authHybridStateFixedTy RTy])
      (Δ := [RTy, authHybridStateFixedTy, .prod authHybridStateFixedTy RTy]) .zero .zero := by
  cases opk <;> rfl

set_option linter.constructorNameAsVariable false in
private theorem syncFixedShadow_cpaRebuild_sim (S : Setup) (b : QueryBudget)
    {A : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (c_leg : Comp pqAtomicOps pqAuthPrimIface
      (A :: authCpaShadowStTy :: Γ)
      (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF))
    (s' : authCpaShadowStTy.denote) (xA : A.denote) (ρ : Env Γ)
    {nOn nRo nRoot : ℕ}
    (hCapRo : nRo ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hCapRt : nRoot ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hShadow0 : RoBothShadowRel (AuthKindFuels.ofBudget S b).K_cap s'.1.2.2.1.1 s'.2)
    (hEach : ∀ rsf ∈ support (c_leg.eval (.cons xA (.cons s' ρ))),
      AuthFixedAtomOnlineBounded nOn rsf.2 ∧
      CacheStepAtMostOne (atomRoCache s'.1.2.2.1.1) (atomRoCache rsf.2.1.1) ∧
      CacheStepAtMostOne (atomRootRoCache s'.1.2.2.1.1) (atomRootRoCache rsf.2.1.1) ∧
      (atomRoCache rsf.2.1.1).length ≤ nRo ∧
      (atomRootRoCache rsf.2.1.1).length ≤ nRoot) :
    let cap := (AuthKindFuels.ofBudget S b).K_cap
    let wrapped : Comp pqAtomicOps pqAuthPrimIface
        (A :: authCpaShadowStTy :: Γ) (.prod (authCodec S).R authCpaShadowStTy) :=
      .bind (.bind c_leg (AuthCoreK.syncFixedShadowRespC cap .v0 (.snd .v2)))
        (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))
    Prod.map id forgetCpa <$> wrapped.eval (.cons xA (.cons s' ρ)) =
      (fun rsf : (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF).denote =>
        (rsf.1, (s'.1.1, (s'.1.2.1, rsf.2)))) <$>
        c_leg.eval (.cons xA (.cons s' ρ)) ∧
    ∀ p ∈ support (wrapped.eval (.cons xA (.cons s' ρ))),
      AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed p.2) := by
  intro cap wrapped
  obtain ⟨hSyncMap, hSyncRel⟩ :=
    AuthCoreKSimRo.syncFixedShadowRespC_bind_sim (I := pqAuthPrimIface) cap
      (cpaShadowFixed s') c_leg (.snd .v1) (.cons xA (.cons s' ρ)) hShadow0 rfl
      (fun rsf hrsf => by
        rcases hEach rsf hrsf with ⟨_, h1, h2, h3, h4⟩
        exact ⟨h1, h2, Nat.le_trans h3 hCapRo, Nat.le_trans h4 hCapRt⟩)
  let synced := Comp.bind c_leg (AuthCoreK.syncFixedShadowRespC cap .v0 (.snd .v2))
  let retComp : Comp pqAtomicOps pqAuthPrimIface
      (.prod AuthCoreK.authRespAtomicTy authFixedShadowStTy :: A :: authCpaShadowStTy :: Γ)
      (.prod (authCodec S).R authCpaShadowStTy) :=
    .ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0)))
  change Prod.map id forgetAuthFixedShadow <$> synced.eval (.cons xA (.cons s' ρ)) = _ at hSyncMap
  change ∀ q ∈ support (synced.eval (.cons xA (.cons s' ρ))), _ at hSyncRel
  change Prod.map id forgetCpa <$> (Comp.bind synced retComp).eval (.cons xA (.cons s' ρ)) = _ ∧
    ∀ p ∈ support ((Comp.bind synced retComp).eval (.cons xA (.cons s' ρ))), _
  dsimp only [retComp, AuthCoreKArms.cpaRebuildE, Comp.eval]
  constructor
  · rw [map_bind, ← hSyncMap, Functor.map_map, map_eq_bind_pure_comp]
    congr 1
  · intro p hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v2, mem_support_pure_iff] at hp'
    subst hp'
    have hRel' := hSyncRel q hq
    dsimp only [synced, Comp.eval] at hq
    rw [mem_support_bind_iff] at hq
    rcases hq with ⟨rsf, hrsf, hq'⟩
    have hForget : q.2.1 = rsf.2 := by
      simp only [AuthCoreK.syncFixedShadowRespC, Comp.eval, Expr.eval, pure_bind,
        mem_support_bind_iff, mem_support_pure_iff] at hq'
      rcases hq' with ⟨_, _, rfl⟩
      rfl
    rcases hEach rsf hrsf with ⟨hOn', _, _, hRo', hRt'⟩
    exact ⟨hForget ▸ hOn', hForget ▸ hRo', hForget ▸ hRt', hRel'⟩

set_option maxRecDepth 4096 in
private theorem cpaRecv_val_eval_and_post (S : Setup) (b : QueryBudget) (opk : Bool)
    {nOn nRo nRoot : ℕ}
    (fhst0 : authHybridStateFixedTy.denote)
    (x0 : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy.denote)
    (hb0 : AuthFixedValOnlineBounded nOn fhst0)
    (hRo0 : (valRoCache fhst0.1.1).length ≤ nRo)
    (hRt0 : (valRootRoCache fhst0.1.1).length ≤ nRoot)
    (hOn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRo : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRt : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    let F := AuthKindFuels.ofBudget S b
    let RTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy
    let env2 : Env [authHybridStateFixedTy, RTy] := .cons fhst0 (.cons x0 .nil)
    (AuthCoreKArms.cpaRecvKC S F.K_on F.K_ro opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero).eval env2 =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero).eval env2 ∧
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero).eval env2),
      AuthFixedValOnlineBounded (nOn + 1) y.2 ∧
      CacheStepAtMostOne (valRoCache fhst0.1.1) (valRoCache y.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valRootRoCache y.2.1.1) := by
  intro F RTy env2
  have hRoK : (valRoCache fhst0.1.1).length ≤ F.K_ro := Nat.le_trans hRo0 (Nat.le_of_succ_le hRo)
  have hRtK : (valRootRoCache fhst0.1.1).length ≤ F.K_ro := Nat.le_trans hRt0 (Nat.le_of_succ_le hRt)
  exact ⟨cpaRecvKC_fuel_eq S F.K_on F.K_ro b.q_total opk .zero .zero env2 hb0
      (Nat.le_of_succ_le hOn) (AuthKindFuels.K_on_le_q_total S b)
      hRoK hRtK (AuthKindFuels.K_ro_le_q_total S b),
    cpaRecvC_preserves S b.q_total opk .zero .zero env2 hb0
      (Nat.le_trans hRoK (AuthKindFuels.K_ro_le_q_total S b))
      (Nat.le_trans hRtK (AuthKindFuels.K_ro_le_q_total S b))⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4096 in
private theorem cpaRecvArmC_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {nOn nRo nRoot : ℕ} {Γ : List (Ty pqAtomicSig)}
    (s' : authCpaShadowStTy.denote)
    (xA : (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy).denote)
    (ρ : Env Γ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hOn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRo : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRt : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    let F := AuthKindFuels.ofBudget S b
    let RTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy
    let cOld := mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
        (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
        (Δ := [authHybridStateFixedTy, RTy]) .zero .zero)
    Prod.map id forgetCpa <$>
      (AuthCoreKArms.cpaRecvArmC S F opk).eval (.cons xA (.cons s' ρ)) =
      (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, rsf.2)))) <$>
        cOld.eval (.cons s'.1.2.2 (.cons xA .nil)) ∧
    ∀ p ∈ support ((AuthCoreKArms.cpaRecvArmC S F opk).eval (.cons xA (.cons s' ρ))),
      AuthFixedShadowAt S b (nOn + 1) (nRo + 1) (nRoot + 1) (cpaShadowFixed p.2) := by
  intro F RTy cOld
  have hLegEq0 := liftAuthPrim1_let2_eval
    (fun fhst x => AuthCoreKArms.cpaRecvKC S F.K_on F.K_ro opk fhst x)
    (cpaRecvKC_ren2 S F.K_on F.K_ro opk) s' xA ρ
  have hOldEval0 := mapComp_tlAuthPrim_eval_pair
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero) s'.1.2.2 xA
  have hKEval0 := mapComp_tlAuthPrim_eval_pair
    (AuthCoreKArms.cpaRecvKC S F.K_on F.K_ro opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero) s'.1.2.2 xA
  have hb0 : AuthFixedValOnlineBounded nOn (projVal authHybridStateFixedTy s'.1.2.2) :=
    (AuthFixedAtomOnlineBounded.iff_embedVal _).mp
      (by simpa only [cpaShadowFixed, Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal] using hSh.online_le)
  have hRo0 : (valRoCache (projVal authHybridStateFixedTy s'.1.2.2).1.1).length ≤ nRo := by
    have h : (atomRoCache s'.1.2.2.1.1).length ≤ nRo := hSh.ro_len_le
    rw [← Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy s'.1.2.2] at h
    exact (congrArg List.length (atomRoCache_embedVal _)).symm.trans_le h
  have hRt0 : (valRootRoCache (projVal authHybridStateFixedTy s'.1.2.2).1.1).length ≤ nRoot := by
    have h : (atomRootRoCache s'.1.2.2.1.1).length ≤ nRoot := hSh.root_len_le
    rw [← Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy s'.1.2.2] at h
    exact (congrArg List.length (atomRootRoCache_embedVal _)).symm.trans_le h
  obtain ⟨hValFuel, hValPost⟩ := cpaRecv_val_eval_and_post S b opk
    (projVal authHybridStateFixedTy s'.1.2.2) (projVal RTy xA) hb0 hRo0 hRt0 hOn hRo hRt
  unfold AuthCoreKArms.cpaRecvArmC
  dsimp only [cOld]
  generalize (AuthCoreKArms.liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       AuthCoreKArms.cpaRecvKC S F.K_on F.K_ro opk fhst x)
      (.pair (.snd (.snd (.fst .v1))) .v0)) = c_leg at hLegEq0 ⊢
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero) = dOld at hOldEval0 hValFuel hValPost ⊢
  generalize (AuthCoreKArms.cpaRecvKC S F.K_on F.K_ro opk
      (Γ₁ := [authHybridStateFixedTy, RTy]) (Γ₂ := [RTy])
      (Δ := [authHybridStateFixedTy, RTy]) .zero .zero) = dK at hLegEq0 hKEval0 hValFuel
  have hLegOld : c_leg.eval (.cons xA (.cons s' ρ)) =
      (mapComp tlAuthPrim dOld).eval (.cons s'.1.2.2 (.cons xA .nil)) :=
    hLegEq0.trans (hKEval0.trans ((congrArg (Functor.map (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)) hValFuel).trans hOldEval0.symm))
  have hEachOld : ∀ rsf ∈ support (c_leg.eval (.cons xA (.cons s' ρ))),
      AuthFixedAtomOnlineBounded (nOn + 1) rsf.2 ∧
      CacheStepAtMostOne (atomRoCache s'.1.2.2.1.1) (atomRoCache rsf.2.1.1) ∧
      CacheStepAtMostOne (atomRootRoCache s'.1.2.2.1.1) (atomRootRoCache rsf.2.1.1) ∧
      (atomRoCache rsf.2.1.1).length ≤ nRo + 1 ∧
      (atomRootRoCache rsf.2.1.1).length ≤ nRoot + 1 := by
    intro rsf hrsf
    rw [hLegOld, hOldEval0, support_map, Set.mem_image] at hrsf
    rcases hrsf with ⟨y, hy, rfl⟩
    rcases hValPost y hy with ⟨hyOn, hyRo, hyRt⟩
    have hyOnA : AuthFixedAtomOnlineBounded (nOn + 1) (embedVal authHybridStateFixedTy y.2) :=
      (AuthFixedAtomOnlineBounded.iff_embedVal y.2).mpr hyOn
    have hRoS : CacheStepAtMostOne (atomRoCache s'.1.2.2.1.1)
        (atomRoCache (embedVal authHybridStateFixedTy y.2).1.1) := by
      have h : CacheStepAtMostOne
          (atomRoCache (embedVal authHybridStateFixedTy (projVal authHybridStateFixedTy s'.1.2.2)).1.1)
          (atomRoCache (embedVal authHybridStateFixedTy y.2).1.1) := cacheStep_embed_ro hyRo
      rwa [Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal] at h
    have hRtS : CacheStepAtMostOne (atomRootRoCache s'.1.2.2.1.1)
        (atomRootRoCache (embedVal authHybridStateFixedTy y.2).1.1) := by
      have h : CacheStepAtMostOne
          (atomRootRoCache (embedVal authHybridStateFixedTy (projVal authHybridStateFixedTy s'.1.2.2)).1.1)
          (atomRootRoCache (embedVal authHybridStateFixedTy y.2).1.1) := cacheStep_embed_root hyRt
      rwa [Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal] at h
    exact ⟨hyOnA, hRoS, hRtS,
      Nat.le_trans hRoS.length_le (Nat.succ_le_succ hSh.ro_len_le),
      Nat.le_trans hRtS.length_le (Nat.succ_le_succ hSh.root_len_le)⟩
  have hRoLeCap : F.K_ro ≤ F.K_cap := by dsimp only [F, AuthKindFuels.ofBudget]; omega
  obtain ⟨hMap, hPres⟩ := syncFixedShadow_cpaRebuild_sim S b c_leg s' xA ρ
    (Nat.le_trans hRo hRoLeCap) (Nat.le_trans hRt hRoLeCap) hSh.ro_shadow hEachOld
  rw [hLegOld] at hMap
  exact ⟨hMap, hPres⟩

private theorem cpaRoArm_sim (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (s' : authCpaShadowStTy.denote)
    (sec : (PB 192).denote) (ρ : Env Γ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hOld : nRo + 1 ≤ b.q_total) (hCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let F := AuthKindFuels.ofBudget S b
    let arm : Comp pqAtomicOps pqAuthPrimIface (PB 192 :: authCpaShadowStTy :: Γ)
        (.prod (authCodec S).R authCpaShadowStTy) :=
      .bind (AuthCoreK.roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
        (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))
    let leg := mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.roFixedB b.q_total
        (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
        (Δ := [authHybridStateFixedTy, B 192]) .zero .zero)
    Prod.map id forgetCpa <$> arm.eval (.cons sec (.cons s' ρ)) =
      (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, rsf.2)))) <$>
        leg.eval (.cons s'.1.2.2 (.cons sec .nil)) ∧
    ∀ p ∈ support (arm.eval (.cons sec (.cons s' ρ))),
      AuthFixedShadowAt S b nOn (nRo + 1) nRoot (cpaShadowFixed p.2) := by
  intro F arm leg
  obtain ⟨hEq, hPres⟩ :=
    AuthCoreKSimRo.roFixedShadowArmC_sim_prim S b
      (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0 (.cons sec (.cons s' ρ))
      (cpaShadowFixed s') sec rfl rfl hSh hOld hCap
  dsimp only [arm, leg, cpaShadowFixed, AuthCoreKArms.cpaRebuildE, Comp.eval] at hEq ⊢
  constructor
  · rw [map_bind, ← hEq, Functor.map_map, map_eq_bind_pure_comp]
    congr 1
  · intro p hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v2, mem_support_pure_iff] at hp'
    subst hp'
    exact hPres q hq

private theorem cpaRoRootArm_sim (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {Γ : List (Ty pqAtomicSig)} (s' : authCpaShadowStTy.denote)
    (inp : ((PB 32).prod (PB 32)).denote) (ρ : Env Γ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hOld : nRoot + 1 ≤ b.q_total) (hCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap) :
    let F := AuthKindFuels.ofBudget S b
    let B32 := B 32
    let arm : Comp pqAtomicOps pqAuthPrimIface (.prod (PB 32) (PB 32) :: authCpaShadowStTy :: Γ)
        (.prod (authCodec S).R authCpaShadowStTy) :=
      .bind (AuthCoreK.roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
        (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))
    let leg := mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.roRootFixedB b.q_total
        (Γ₁ := [authHybridStateFixedTy, .prod B32 B32]) (Γ₂ := [.prod B32 B32])
        (Δ := [authHybridStateFixedTy, .prod B32 B32]) .zero .zero)
    Prod.map id forgetCpa <$> arm.eval (.cons inp (.cons s' ρ)) =
      (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, rsf.2)))) <$>
        leg.eval (.cons s'.1.2.2 (.cons inp .nil)) ∧
    ∀ p ∈ support (arm.eval (.cons inp (.cons s' ρ))),
      AuthFixedShadowAt S b nOn nRo (nRoot + 1) (cpaShadowFixed p.2) := by
  intro F B32 arm leg
  obtain ⟨hEq, hPres⟩ :=
    AuthCoreKSimRo.roRootFixedShadowArmC_sim_prim S b
      (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0 (.cons inp (.cons s' ρ))
      (cpaShadowFixed s') inp rfl rfl hSh hOld hCap
  dsimp only [arm, leg, cpaShadowFixed, AuthCoreKArms.cpaRebuildE, Comp.eval] at hEq ⊢
  constructor
  · rw [map_bind, ← hEq, Functor.map_map, map_eq_bind_pure_comp]
    congr 1
  · intro p hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v2, mem_support_pure_iff] at hp'
    subst hp'
    exact hPres q hq

set_option maxRecDepth 4096 in
private theorem cpaSendSlot_eval_and_post (S : Setup) (b : QueryBudget) (opk allowPause : Bool)
    {nOn nRo nRoot : ℕ}
    (s' : authCpaShadowStTy.denote)
    (xA : (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sendQTy).denote)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hOn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRo : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRt : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    let F := AuthKindFuels.ofBudget S b
    let STy := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sendQTy
    let s0 := projVal cpaStTy s'.1
    let x0 := projVal STy xA
    let env4 : Env [.nat, .nat, authHybridStateFixedTy, STy] :=
      .cons s0.1 (.cons s0.2.1 (.cons s0.2.2 (.cons x0 .nil)))
    (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk allowPause
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, STy])
      (Γ₂ := [.nat, authHybridStateFixedTy, STy])
      (Γ₃ := [authHybridStateFixedTy, STy])
      (Γ₄ := [STy]) .zero .zero .zero .zero).eval env4 =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk allowPause
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, STy])
      (Γ₂ := [.nat, authHybridStateFixedTy, STy])
      (Γ₃ := [authHybridStateFixedTy, STy])
      (Γ₄ := [STy]) .zero .zero .zero .zero).eval env4 ∧
    ∀ out ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB
      S b.q_total opk allowPause
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, STy])
      (Γ₂ := [.nat, authHybridStateFixedTy, STy])
      (Γ₃ := [authHybridStateFixedTy, STy])
      (Γ₄ := [STy]) .zero .zero .zero .zero).eval env4),
      CpaSendSlotPost nOn allowPause s0.2.2 out := by
  intro F STy s0 x0 env4
  have hs0 : s0.2.2 = projVal authHybridStateFixedTy s'.1.2.2 := rfl
  have hb0 : AuthFixedValOnlineBounded nOn s0.2.2 :=
    (AuthFixedAtomOnlineBounded.iff_embedVal _).mp
      (by simpa only [hs0, cpaShadowFixed, Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal]
            using hSh.online_le)
  have hRo0 : (valRoCache s0.2.2.1.1).length ≤ nRo := by
    have h : (atomRoCache s'.1.2.2.1.1).length ≤ nRo := hSh.ro_len_le
    rw [← Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy s'.1.2.2] at h
    exact (congrArg List.length (atomRoCache_embedVal s0.2.2.1.1)).symm.trans_le h
  have hRt0 : (valRootRoCache s0.2.2.1.1).length ≤ nRoot := by
    have h : (atomRootRoCache s'.1.2.2.1.1).length ≤ nRoot := hSh.root_len_le
    rw [← Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy s'.1.2.2] at h
    exact (congrArg List.length (atomRootRoCache_embedVal s0.2.2.1.1)).symm.trans_le h
  have hRoK : (valRoCache s0.2.2.1.1).length ≤ F.K_ro := Nat.le_trans hRo0 (Nat.le_of_succ_le hRo)
  have hRtK : (valRootRoCache s0.2.2.1.1).length ≤ F.K_ro := Nat.le_trans hRt0 (Nat.le_of_succ_le hRt)
  exact ⟨cpaSendSlotKB_fuel_eq S F.K_on F.K_ro b.q_total opk allowPause
      .zero .zero .zero .zero env4 hb0
      (Nat.le_of_succ_le hOn) (AuthKindFuels.K_on_le_q_total S b)
      hRoK hRtK (AuthKindFuels.K_ro_le_q_total S b),
    cpaSendSlotB_preserves S b.q_total opk allowPause .zero .zero .zero .zero env4 hb0
      (Nat.le_trans hRoK (AuthKindFuels.K_ro_le_q_total S b))
      (Nat.le_trans hRtK (AuthKindFuels.K_ro_le_q_total S b))⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem cpaSendSlotKB_ren4 (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren4 (.succ (.succ .zero)) (.succ .zero) .zero (.succ (.succ (.succ .zero))))
      (AuthCoreKArms.cpaSendSlotKB S K_on K_ro opk allowPause
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy]) .zero .zero .zero .zero) =
    AuthCoreKArms.cpaSendSlotKB S K_on K_ro opk allowPause
      (Γ₁ := [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy])
      (Γ₂ := [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy])
      (Γ₃ := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy])
      (Γ₄ := [sendQTy, cpaStTy, .prod cpaStTy sendQTy])
      (Δ := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy])
      .zero .zero .zero .zero := by
  cases opk <;> cases allowPause <;> rfl

private theorem liftExpr1_eval {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (AuthCoreK.liftExpr1 e argE).eval ρ =
      (Computational.Proofs.SignalPqxdh.AtomicLift.mapExpr e :
        Expr pqAtomicOps [embedTy a] (embedTy b)).eval (.cons (argE.eval ρ) .nil) := by
  dsimp only [AuthCoreK.liftExpr1, Expr.eval]
  exact Computational.Proofs.SignalPqxdh.AtomicLift.exprRename_eval _ _ _ _
    (fun | .zero => rfl | .succ v' => nomatch v')

private theorem fixedRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ AuthCoreK.authFixedAtomicTy) (ρ : Env Γ) :
    (AuthCoreK.fixedRoCacheE fhstE).eval ρ = atomRoCache (fhstE.eval ρ).1.1 := by
  rw [AuthCoreK.fixedRoCacheE, liftExpr1_eval]; rfl

private theorem fixedRootRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ AuthCoreK.authFixedAtomicTy) (ρ : Env Γ) :
    (AuthCoreK.fixedRootRoCacheE fhstE).eval ρ = atomRootRoCache (fhstE.eval ρ).1.1 := by
  rw [AuthCoreK.fixedRootRoCacheE, liftExpr1_eval]; rfl

private theorem bind_congr_of_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a ∈ support mx, f a = g a) : (mx >>= f) = (mx >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]; congr 1; ext u
    exact ih u (fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩))

set_option linter.constructorNameAsVariable false in
private theorem cpaSendInlShadow_sync (S : Setup) (b : QueryBudget) (allowPause : Bool)
    {nOn nRo nRoot : ℕ} {Γs : List (Ty pqAtomicSig)}
    (s' : authCpaShadowStTy.denote)
    (d0 : authRespTy.denote × (ℕ × authHybridStateFixedTy.denote))
    (roBothE : Expr pqAtomicOps (.prod (authCodec S).R (embedTy cpaStTy) :: Γs) roBothAvlTy)
    (ρs : Env Γs)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hRo : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRt : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hPost : CpaSendSlotPost nOn allowPause (projVal cpaStTy s'.1).2.2 (.inl d0))
    (hBothE : roBothE.eval (.cons (embedVal (.prod authRespTy cpaStTy)
        (d0.1, ((projVal cpaStTy s'.1).1, d0.2))) ρs) = s'.2) :
    let F := AuthKindFuels.ofBudget S b
    let dA := embedVal (.prod authRespTy cpaStTy)
      (d0.1, ((projVal cpaStTy s'.1).1, d0.2))
    ∃ avls' : roBothAvlTy.denote,
      (AuthCoreK.syncRoBothC (I := pqAuthPrimIface) F.K_cap
          (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
          (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
          roBothE).eval (.cons dA ρs) = pure avls' ∧
      AuthFixedShadowAt S b (nOn + 1) (nRo + 1) (nRoot + 1) (dA.2.2.2, avls') := by
  intro F dA
  rcases hPost with ⟨hb', hRoStep0, hRtStep0⟩
  have hRoLeCap : F.K_ro ≤ F.K_cap := by dsimp only [F, AuthKindFuels.ofBudget]; omega
  have hEmbedSt : embedVal authStateTy (projVal cpaStTy s'.1).2.2.1.1 = s'.1.2.2.1.1 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authStateTy s'.1.2.2.1.1
  have hbA : AuthFixedAtomOnlineBounded (nOn + 1) (embedVal authHybridStateFixedTy d0.2.2) :=
    (AuthFixedAtomOnlineBounded.iff_embedVal d0.2.2).mpr hb'
  have hRoS : CacheStepAtMostOne (atomRoCache s'.1.2.2.1.1)
      (atomRoCache (embedVal authHybridStateFixedTy d0.2.2).1.1) := by
    have h := cacheStep_embed_ro hRoStep0; rwa [hEmbedSt] at h
  have hRtS : CacheStepAtMostOne (atomRootRoCache s'.1.2.2.1.1)
      (atomRootRoCache (embedVal authHybridStateFixedTy d0.2.2).1.1) := by
    have h := cacheStep_embed_root hRtStep0; rwa [hEmbedSt] at h
  have hRoLen := Nat.le_trans hRoS.length_le (Nat.succ_le_succ hSh.ro_len_le)
  have hRtLen := Nat.le_trans hRtS.length_le (Nat.succ_le_succ hSh.root_len_le)
  obtain ⟨avls', hSyncEval, hRel'⟩ :=
    AuthCoreKSimRo.syncRoBothC_sim (I := pqAuthPrimIface) F.K_cap
      s'.1.2.2.1.1 (embedVal authHybridStateFixedTy d0.2.2).1.1 s'.2
      (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
      (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
      roBothE (.cons dA ρs) hSh.ro_shadow hRoS hRtS
      (Nat.le_trans hRoLen (Nat.le_trans hRo hRoLeCap))
      (Nat.le_trans hRtLen (Nat.le_trans hRt hRoLeCap))
      (by rw [fixedRoCacheE_eval]; rfl) (by rw [fixedRootRoCacheE_eval]; rfl) hBothE
  exact ⟨avls', hSyncEval, ⟨hbA, hRoLen, hRtLen, hRel'⟩⟩

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4096 in
private theorem cpaSendPostArm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {nOn nRo nRoot : ℕ} {Γ : List (Ty pqAtomicSig)}
    (s' : authCpaShadowStTy.denote) (xA : (embedTy sendQTy).denote) (ρ : Env Γ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hOn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRo : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRt : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    let F := AuthKindFuels.ofBudget S b
    let s0 := projVal cpaStTy s'.1
    let x0 := projVal sendQTy xA
    let env4 : Env [.nat, .nat, authHybridStateFixedTy, sendQTy] :=
      .cons s0.1 (.cons s0.2.1 (.cons s0.2.2 (.cons x0 .nil)))
    let arm : Comp pqAtomicOps pqAuthPrimIface (embedTy sendQTy :: authCpaShadowStTy :: Γ)
        (.prod (authCodec S).R authCpaShadowStTy) :=
      .bind (AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun idx =>
           letV (.fst (.snd (v s))) fun ns =>
           letV (.snd (.snd (v s))) fun fhst =>
           bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk false idx ns fhst x) fun r =>
           caseSumV (v r)
             (fun d => .ret (.pair (.fst (v d)) (.pair (v idx) (.snd (v d)))))
             (fun _ => .ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst))))))
          (.pair (.fst .v1) .v0))
        (.bind (AuthCoreK.syncRoBothC F.K_cap
            (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
            (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
    let dOld := _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk false
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
      (Γ₃ := [authHybridStateFixedTy, sendQTy])
      (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy]) .zero .zero .zero .zero
    Prod.map id forgetCpa <$> arm.eval (.cons xA (.cons s' ρ)) =
      embedVal (.prod authRespTy cpaStTy) <$>
        ((fun out => match out with
          | .inl d => (d.1, (s0.1, d.2))
          | .inr _ => ((aNone (Γ := [])).eval .nil, (s0.1, (s0.2.1, s0.2.2)))) <$> dOld.eval env4) ∧
    ∀ p ∈ support (arm.eval (.cons xA (.cons s' ρ))),
      AuthFixedShadowAt S b (nOn + 1) (nRo + 1) (nRoot + 1) (cpaShadowFixed p.2) := by
  intro F s0 x0 env4 arm dOld
  obtain ⟨hValFuel, hValPost⟩ := cpaSendSlot_eval_and_post S b opk false s' xA hSh hOn hRo hRt
  have hRen := cpaSendSlotKB_ren4 S F.K_on F.K_ro opk false
  dsimp only [arm, dOld] at hValFuel hValPost ⊢
  generalize (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk false
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
      (Γ₃ := [authHybridStateFixedTy, sendQTy])
      (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      .zero .zero .zero .zero) = cK0 at hRen hValFuel
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk false
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
      (Γ₃ := [authHybridStateFixedTy, sendQTy])
      (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      .zero .zero .zero .zero) = cOld0 at hValFuel hValPost ⊢
  have hStep1 :
      (AuthCoreKArms.liftAuthPrim1
        (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun idx => letV (.fst (.snd (v s))) fun ns =>
         letV (.snd (.snd (v s))) fun fhst =>
         bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk false idx ns fhst x) fun r =>
         caseSumV (v r)
           (fun d => .ret (.pair (.fst (v d)) (.pair (v idx) (.snd (v d)))))
           (fun _ => .ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst))))))
        (.pair (.fst .v1) .v0)).eval (.cons xA (.cons s' ρ)) =
      embedVal (.prod authRespTy cpaStTy) <$>
        ((fun out => match out with
          | .inl d => (d.1, (s0.1, d.2))
          | .inr _ => ((aNone (Γ := [])).eval .nil, (s0.1, (s0.2.1, s0.2.2)))) <$> cOld0.eval env4) := by
    rw [liftAuthPrim1_eval]; dsimp only [Expr.eval, Env.get, Expr.v0, Expr.v1]
    rw [mapComp_tlAuthPrim_eval_single]; congr 1
    iterate 5 rw [prf_letV_eval]
    dsimp only [v, Expr.eval, Env.get, projVal, ext_step_wk, ext_refl_wk]
    rw [prf_bindV_eval, compRename_ren4_eval cK0 _ _ _ _ _ _ hRen]
    change (cK0.eval env4 >>= _) = _; rw [hValFuel, map_eq_bind_pure_comp]
    congr 1; funext out; cases out <;> rfl
  generalize (AuthCoreKArms.liftAuthPrim1
      (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
       letV (.fst (v s)) fun idx => letV (.fst (.snd (v s))) fun ns =>
       letV (.snd (.snd (v s))) fun fhst =>
       bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk false idx ns fhst x) fun r =>
       caseSumV (v r)
         (fun d => .ret (.pair (.fst (v d)) (.pair (v idx) (.snd (v d)))))
         (fun _ => .ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst))))))
      (.pair (.fst .v1) .v0)) = c_leg at hStep1 ⊢
  let syncTail : Comp pqAtomicOps pqAuthPrimIface
      (.prod (authCodec S).R (embedTy cpaStTy) :: embedTy sendQTy :: authCpaShadowStTy :: Γ)
      (.prod (authCodec S).R authCpaShadowStTy) :=
    .bind (AuthCoreK.syncRoBothC F.K_cap
        (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
        (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v2))
      (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))
  change Prod.map id forgetCpa <$> (_ >>= fun dA => syncTail.eval (.cons dA (.cons xA (.cons s' ρ)))) = _ ∧
    ∀ p ∈ support (_ >>= fun dA => syncTail.eval (.cons dA (.cons xA (.cons s' ρ)))), _
  rw [hStep1]
  constructor
  · rw [Functor.map_map]; erw [bind_map_left, map_bind, map_eq_bind_pure_comp]
    refine bind_congr_of_support _ _ _ fun out hout => ?_
    have hPost := hValPost out hout
    cases out with
    | inr p0 => exact absurd hPost.1 Bool.false_ne_true
    | inl d0 =>
      obtain ⟨avls', hSync, _⟩ :=
        cpaSendInlShadow_sync S b false s' d0 (.snd .v2) (.cons xA (.cons s' ρ)) hSh hRo hRt hPost rfl
      dsimp only [syncTail, Comp.eval]; rw [hSync, pure_bind, map_pure]; rfl
  · intro p hp
    rw [Functor.map_map] at hp; erw [bind_map_left, mem_support_bind_iff] at hp
    rcases hp with ⟨out, hout, hp'⟩
    have hPost := hValPost out hout
    cases out with
    | inr p0 => exact absurd hPost.1 Bool.false_ne_true
    | inl d0 =>
      obtain ⟨avls', hSync, hSh'⟩ :=
        cpaSendInlShadow_sync S b false s' d0 (.snd .v2) (.cons xA (.cons s' ρ)) hSh hRo hRt hPost rfl
      dsimp only [syncTail, Comp.eval] at hp'; rw [hSync, pure_bind, mem_support_pure_iff] at hp'
      subst hp'; exact hSh'

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4096 in
private theorem cpaSendPreArm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {nOn nRo nRoot : ℕ} {Γ : List (Ty pqAtomicSig)}
    (s' : authCpaShadowStTy.denote) (xA : (embedTy sendQTy).denote) (ρ : Env Γ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (cpaShadowFixed s'))
    (hOn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRo : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRt : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    let F := AuthKindFuels.ofBudget S b
    let s0 := projVal cpaStTy s'.1
    let x0 := projVal sendQTy xA
    let env4 : Env [.nat, .nat, authHybridStateFixedTy, sendQTy] :=
      .cons s0.1 (.cons s0.2.1 (.cons s0.2.2 (.cons x0 .nil)))
    let arm : Comp pqAtomicOps pqAuthPrimIface (embedTy sendQTy :: authCpaShadowStTy :: Γ)
        (.sum (.prod (authCodec S).R authCpaShadowStTy)
          (.prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
            (.prod (embedTy cpaPayloadTy) authCpaShadowStTy))) :=
      .bind (AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun idx =>
           letV (.fst (.snd (v s))) fun ns =>
           letV (.snd (.snd (v s))) fun fhst =>
           bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
           caseSumV (v r)
             (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
             (fun p => .ret (.inr (.pair (.fst (v p))
               (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p)))))))))
          (.pair (.fst .v1) .v0))
        (.caseSum .v0
          (.bind (AuthCoreK.syncRoBothC F.K_cap
              (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
              (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
              (.snd .v3))
            (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
          (.ret (.inr (.pair (.fst .v0)
            (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))
    let dOld := _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk true
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
      (Γ₃ := [authHybridStateFixedTy, sendQTy])
      (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy]) .zero .zero .zero .zero
    forgetPreOut id forgetCpa <$> arm.eval (.cons xA (.cons s' ρ)) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$>
        ((fun out => match out with
          | .inl d => Sum.inl (d.1, (s0.1, d.2))
          | .inr p => Sum.inr (p.1, (p.2.1, (s0.1, p.2.2)))) <$> dOld.eval env4) ∧
    (∀ vOut s'₁, .inl (vOut, s'₁) ∈ support (arm.eval (.cons xA (.cons s' ρ))) →
      AuthFixedShadowAt S b (nOn + 1) (nRo + 1) (nRoot + 1) (cpaShadowFixed s'₁)) ∧
    (∀ c_out p' s'₁, .inr (c_out, p', s'₁) ∈ support (arm.eval (.cons xA (.cons s' ρ))) →
      cpaShadowFixed s'₁ = cpaShadowFixed s' ∧ CpaPausePayloadOk nOn nRo nRoot p' s'₁) := by
  intro F s0 x0 env4 arm dOld
  obtain ⟨hValFuel, hValPost⟩ := cpaSendSlot_eval_and_post S b opk true s' xA hSh hOn hRo hRt
  have hRen := cpaSendSlotKB_ren4 S F.K_on F.K_ro opk true
  dsimp only [arm, dOld] at hValFuel hValPost ⊢
  generalize (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk true
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
      (Γ₃ := [authHybridStateFixedTy, sendQTy])
      (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      .zero .zero .zero .zero) = cK0 at hRen hValFuel
  generalize (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk true
      (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
      (Γ₃ := [authHybridStateFixedTy, sendQTy])
      (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
      .zero .zero .zero .zero) = cOld0 at hValFuel hValPost ⊢
  have hStep1 :
      (AuthCoreKArms.liftAuthPrim1
        (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun idx => letV (.fst (.snd (v s))) fun ns =>
         letV (.snd (.snd (v s))) fun fhst =>
         bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
         caseSumV (v r)
           (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
           (fun p => .ret (.inr (.pair (.fst (v p))
             (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p)))))))))
        (.pair (.fst .v1) .v0)).eval (.cons xA (.cons s' ρ)) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$>
        ((fun out => match out with
          | .inl d => Sum.inl (d.1, (s0.1, d.2))
          | .inr p => Sum.inr (p.1, (p.2.1, (s0.1, p.2.2)))) <$> cOld0.eval env4) := by
    rw [liftAuthPrim1_eval]; dsimp only [Expr.eval, Env.get, Expr.v0, Expr.v1]
    rw [mapComp_tlAuthPrim_eval_single]; congr 1
    iterate 5 rw [prf_letV_eval]
    dsimp only [v, Expr.eval, Env.get, projVal, ext_step_wk, ext_refl_wk]
    rw [prf_bindV_eval, compRename_ren4_eval cK0 _ _ _ _ _ _ hRen]
    change (cK0.eval env4 >>= _) = _; rw [hValFuel, map_eq_bind_pure_comp]
    congr 1; funext out; cases out <;> rfl
  generalize (AuthCoreKArms.liftAuthPrim1
      (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
       letV (.fst (v s)) fun idx => letV (.fst (.snd (v s))) fun ns =>
       letV (.snd (.snd (v s))) fun fhst =>
       bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
       caseSumV (v r)
         (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
         (fun p => .ret (.inr (.pair (.fst (v p))
           (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p)))))))))
      (.pair (.fst .v1) .v0)) = c_leg at hStep1 ⊢
  let caseTail : Comp pqAtomicOps pqAuthPrimIface
      (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy ::
        embedTy sendQTy :: authCpaShadowStTy :: Γ)
      (.sum (.prod (authCodec S).R authCpaShadowStTy)
        (.prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
          (.prod (embedTy cpaPayloadTy) authCpaShadowStTy))) :=
    .caseSum .v0
      (.bind (AuthCoreK.syncRoBothC F.K_cap
          (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
          (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v3))
        (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
      (.ret (.inr (.pair (.fst .v0)
        (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3))))))
  change forgetPreOut id forgetCpa <$> (_ >>= fun resA => caseTail.eval (.cons resA (.cons xA (.cons s' ρ)))) = _ ∧
    (∀ vOut s'₁, .inl (vOut, s'₁) ∈ support (_ >>= fun resA => caseTail.eval (.cons resA (.cons xA (.cons s' ρ)))) → _) ∧
    (∀ c_out p' s'₁, .inr (c_out, p', s'₁) ∈ support (_ >>= fun resA => caseTail.eval (.cons resA (.cons xA (.cons s' ρ)))) → _)
  rw [hStep1]
  have hEmbedS : embedVal authHybridStateFixedTy s0.2.2 = s'.1.2.2 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy s'.1.2.2
  let CPTy := embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy
  have hCaseInl (d) : caseTail.eval (.cons (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy (.inl d)) (.cons xA (.cons s' ρ))) =
      ((AuthCoreK.syncRoBothC F.K_cap (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
          (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v3)).eval
        (.cons (embedVal (.prod authRespTy cpaStTy) d)
          (.cons (t := CPTy) (Sum.inl (embedVal (.prod authRespTy cpaStTy) d)) (.cons xA (.cons s' ρ)))) >>= fun avls' =>
        pure (Sum.inl (embedVal authRespTy d.1, (embedVal cpaStTy d.2, avls')))) := rfl
  have hCaseInr (p) : caseTail.eval (.cons (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy (.inr p)) (.cons xA (.cons s' ρ))) =
      pure (Sum.inr (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaChOutTy p.1,
        (embedVal cpaPayloadTy p.2.1, (embedVal cpaStTy p.2.2, s'.2)))) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Functor.map_map]; erw [bind_map_left, map_bind, map_eq_bind_pure_comp]
    refine bind_congr_of_support _ _ _ fun out hout => ?_
    have hPost := hValPost out hout
    cases out with
    | inl d0 =>
      let dA := embedVal (.prod authRespTy cpaStTy) (d0.1, (s0.1, d0.2))
      obtain ⟨avls', hSync, _⟩ :=
        cpaSendInlShadow_sync S b true s' d0 (.snd .v3)
          (.cons (t := CPTy) (Sum.inl dA) (.cons xA (.cons s' ρ))) hSh hRo hRt hPost rfl
      rw [hCaseInl]; erw [hSync, pure_bind, map_pure]; rfl
    | inr p0 =>
      rw [hCaseInr]; erw [map_pure]; rfl
  · intro vOut s'₁ hmem
    rw [Functor.map_map] at hmem; erw [bind_map_left, mem_support_bind_iff] at hmem
    rcases hmem with ⟨out, hout, hmem'⟩
    have hPost := hValPost out hout
    cases out with
    | inl d0 =>
      let dA := embedVal (.prod authRespTy cpaStTy) (d0.1, (s0.1, d0.2))
      obtain ⟨avls', hSync, hSh'⟩ :=
        cpaSendInlShadow_sync S b true s' d0 (.snd .v3)
          (.cons (t := CPTy) (Sum.inl dA) (.cons xA (.cons s' ρ))) hSh hRo hRt hPost rfl
      rw [hCaseInl] at hmem'; erw [hSync, pure_bind, mem_support_pure_iff] at hmem'
      rcases Prod.mk.inj (Sum.inl.inj hmem') with ⟨_, rfl⟩; exact hSh'
    | inr p0 =>
      rw [hCaseInr] at hmem'; erw [mem_support_pure_iff] at hmem'; nomatch hmem'
  · intro c_out p' s'₁ hmem
    rw [Functor.map_map] at hmem; erw [bind_map_left, mem_support_bind_iff] at hmem
    rcases hmem with ⟨out, hout, hmem'⟩
    have hPost := hValPost out hout
    cases out with
    | inl d0 =>
      let dA := embedVal (.prod authRespTy cpaStTy) (d0.1, (s0.1, d0.2))
      obtain ⟨avls', hSync, _⟩ :=
        cpaSendInlShadow_sync S b true s' d0 (.snd .v3)
          (.cons (t := CPTy) (Sum.inl dA) (.cons xA (.cons s' ρ))) hSh hRo hRt hPost rfl
      rw [hCaseInl] at hmem'; erw [hSync, pure_bind, mem_support_pure_iff] at hmem'; nomatch hmem'
    | inr p0 =>
      rcases hPost with ⟨_, hFhstEq, hPlRo, hPlRt⟩
      rw [hCaseInr] at hmem'; erw [mem_support_pure_iff] at hmem'
      rcases Prod.mk.inj (Sum.inr.inj hmem') with ⟨_, hpRest⟩
      rcases Prod.mk.inj hpRest with ⟨rfl, rfl⟩
      have hFixedEq : embedVal authHybridStateFixedTy p0.2.2.2 = s'.1.2.2 := by rw [hFhstEq, hEmbedS]
      have hShEq : cpaShadowFixed (embedVal cpaStTy (s0.1, p0.2.2), s'.2) = cpaShadowFixed s' := by
        change (embedVal authHybridStateFixedTy p0.2.2.2, s'.2) = (s'.1.2.2, s'.2); rw [hFixedEq]
      have hBaseEq : embedVal authStateTy (projVal cpaStTy s'.1).2.2.1.1 = s'.1.2.2.1.1 :=
        Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authStateTy s'.1.2.2.1.1
      dsimp only
      refine ⟨hShEq, ?_, ?_⟩
      · rw [cpaPayloadRoCache_embedVal, hPlRo, ← atomRoCache_embedVal, hBaseEq, hShEq]; rfl
      · rw [cpaPayloadRootRoCache_embedVal, hPlRt, ← atomRootRoCache_embedVal, hBaseEq, hShEq]; rfl

set_option linter.constructorNameAsVariable false in
private theorem cpa_hInit (S : Setup) (b : QueryBudget) (x : Ty.unit.denote) :
    Prod.map id forgetCpa <$> (aeadCpa1KeyKindProg S b).init.eval (.cons x .nil) =
      (aeadCpaOldAtomicProg S b).init.eval (.cons x .nil) ∧
    ∀ as' ∈ support ((aeadCpa1KeyKindProg S b).init.eval (.cons x .nil)),
      AuthCpaInv S b 0 as'.2 := by
  constructor
  · simp only [aeadCpa1KeyKindProg, aeadCpaOldAtomicProg, forgetCpa,
      AuthCoreKArms.cpaKindInitC, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.aeadCpaRedProg1Key,
      Comp.eval, Expr.eval, Env.get, Expr.v0, map_bind, map_pure,
      Prod.map_apply, id_eq, Prod.mk.eta, bind_pure]
  · unfold aeadCpa1KeyKindProg AuthCoreKArms.cpaKindInitC
    dsimp only [Comp.eval]
    intro as' has'
    cases x
    rw [mem_support_bind_iff] at has'
    rcases has' with ⟨usA, husA, has'⟩
    simp only [Expr.eval, Env.get, Expr.v0, mem_support_pure_iff] at has'
    subst has'
    obtain ⟨us, hus, rfl⟩ := mem_support_mapComp_tlAuthPrim (cpaInitC S b.q_total) (.cons () .nil) usA husA
    have hus' : us ∈ support ((cpaInitC S b.q_total).eval (.cons () .nil)) := hus
    obtain ⟨hBnd, hRo0, hRt0⟩ := cpaInitC_preserves S b.q_total us hus'
    refine ⟨AuthCounterInv.zero b, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (AuthFixedAtomOnlineBounded.iff_embedVal us.2.2.2).mpr hBnd
    · dsimp only [cpaShadowFixed]
      change (atomRoCache (embedVal authStateTy us.2.2.2.1.1)).length ≤ _
      rw [atomRoCache_embedVal, hRo0]
      exact Nat.zero_le _
    · dsimp only [cpaShadowFixed]
      change (atomRootRoCache (embedVal authStateTy us.2.2.2.1.1)).length ≤ _
      rw [atomRootRoCache_embedVal, hRt0]
      exact Nat.zero_le _
    · exact AuthCoreKSimRo.emptyRoBothAvlE_roBothShadowRel _ _ _
        (by dsimp only [cpaShadowFixed]; change atomRoCache (embedVal authStateTy us.2.2.2.1.1) = []; rw [atomRoCache_embedVal, hRo0])
        (by dsimp only [cpaShadowFixed]; change atomRootRoCache (embedVal authStateTy us.2.2.2.1.1) = []; rw [atomRootRoCache_embedVal, hRt0])

set_option linter.constructorNameAsVariable false in
private theorem cpa_hChDone (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (bOut : Bool)
    (_hc : ∀ j, c j ≤ authSimBounds b j) (_hInv : AuthCpaInv S b c s') :
    (aeadCpa1KeyKindProg S b).chDone.eval (.cons s' (.cons bOut .nil)) =
      (aeadCpaOldAtomicProg S b).chDone.eval (.cons (forgetCpa s') (.cons bOut .nil)) := by
  simp only [aeadCpa1KeyKindProg, aeadCpaOldAtomicProg, forgetCpa,
    AuthCoreKArms.cpaKindChDoneC, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.aeadCpaRedProg1Key,
    Comp.eval, Expr.eval, Env.get, Expr.v0, pure_bind]
  exact Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval
    (mapComp tlAuthPrim _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaDefaultChC)
    (fun {a} => AuthCoreKArms.dropShadow1)
    (.cons s'.1 (.cons bOut .nil)) (.cons s'.1 (.cons s' (.cons bOut .nil)))
    (fun v => by cases v with | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v)

private theorem cpaKindResumeC_eval (S : Setup)
    (s' : authCpaShadowStTy.denote) (p' : (embedTy cpaPayloadTy).denote)
    (y : (Ty.opt (PB 32)).denote) :
    (AuthCoreKArms.cpaKindResumeC S).eval (.cons s' (.cons p' (.cons y .nil))) =
      ((mapComp tlAuthPrim cpaResumeC).eval (.cons s'.1 (.cons p' (.cons y .nil))) >>=
        fun r => (pure (r.1, (r.2, s'.2)) :
          OracleComp _ (((authCodec S).R.prod authCpaShadowStTy).denote))) := by
  unfold AuthCoreKArms.cpaKindResumeC
  generalize mapComp tlAuthPrim cpaResumeC = m
  simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, pure_bind]
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval m
    (fun {a} => AuthCoreKArms.dropShadow1)
    (.cons s'.1 (.cons p' (.cons y .nil)))
    (.cons s'.1 (.cons s' (.cons p' (.cons y .nil))))
    (fun v => by
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => cases v with
          | zero => rfl
          | succ v => nomatch v)]
  rfl

set_option linter.constructorNameAsVariable false in
private theorem cpa_hResume (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (p' : (embedTy cpaPayloadTy).denote) (s' : authCpaShadowStTy.denote)
    (y : (Ty.opt (PB 32)).denote)
    (_hc : ∀ j, c j ≤ authSimBounds b j) (hPause : AuthCpaPauseInv S b c p' s') :
    Prod.map id forgetCpa <$>
        (aeadCpa1KeyKindProg S b).resume.eval (.cons s' (.cons p' (.cons y .nil))) =
      (aeadCpaOldAtomicProg S b).resume.eval (.cons (forgetCpa s') (.cons p' (.cons y .nil))) ∧
    ∀ vs' ∈ support ((aeadCpa1KeyKindProg S b).resume.eval (.cons s' (.cons p' (.cons y .nil)))),
      AuthCpaInv S b c vs'.2 := by
  unfold aeadCpa1KeyKindProg aeadCpaOldAtomicProg
    Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.aeadCpaRedProg1Key
  let ρAtom : Env (embedCtx [cpaStTy, cpaPayloadTy, .opt (B 32)]) :=
    .cons s'.1 (.cons p' (.cons y .nil))
  rw [cpaKindResumeC_eval S s' p' y]
  constructor
  · rw [map_bind]
    have hPure :
        (fun r : (embedTy (.prod authRespTy cpaStTy)).denote =>
          Prod.map id forgetCpa <$>
            (pure (r.1, (r.2, s'.2)) :
              OracleComp PrimBaseSpec
                (((authCodec S).R.prod authCpaShadowStTy).denote))) =
          pure := by
      funext ⟨_, _⟩
      simp only [map_pure]
      rfl
    rw [hPure]
    exact bind_pure ((mapComp tlAuthPrim cpaResumeC).eval ρAtom)
  · intro vs' hvs
    rw [mem_support_bind_iff] at hvs
    rcases hvs with ⟨r, hr, hvs'⟩
    rw [mem_support_pure_iff] at hvs'
    subst hvs'
    obtain ⟨rv, hrv, rfl⟩ := mem_support_mapComp_tlAuthPrim cpaResumeC ρAtom r hr
    clear hr
    have hs0_raw : embedVal cpaStTy (projVal cpaStTy s'.1) = s'.1 :=
      congrArg (fun e => Env.get e .zero) (embedEnv_projEnv ρAtom)
    have hp0_raw : embedVal cpaPayloadTy (projVal cpaPayloadTy p') = p' :=
      congrArg (fun e => Env.get e (.succ .zero)) (embedEnv_projEnv ρAtom)
    have hProj : projEnv ρAtom =
        .cons (projVal cpaStTy s'.1)
          (.cons (projVal cpaPayloadTy p') (.cons (projVal (.opt (B 32)) y) .nil)) := rfl
    rw [hProj] at hrv
    generalize projVal cpaStTy s'.1 = s0 at hrv hs0_raw
    generalize projVal cpaPayloadTy p' = p0 at hrv hp0_raw
    generalize projVal (.opt (B 32)) y = y0 at hrv
    have hs0 : embedVal cpaStTy s0 = s'.1 := hs0_raw
    have hp0 : embedVal cpaPayloadTy p0 = p' := hp0_raw
    have hs0_fhst : embedVal authHybridStateFixedTy s0.2.2 = s'.1.2.2 := by
      rw [← hs0]; rfl
    have hb0 : AuthFixedValOnlineBounded (c 0 - 1) s0.2.2 :=
      (AuthFixedAtomOnlineBounded.iff_embedVal s0.2.2).mp
        (hs0_fhst.symm ▸ hPause.shadow_pre.online_le)
    revert rv hrv
    unfold cpaResumeC
    refine support_prf_letV fun idx _hidx =>
      support_prf_letV fun fhst hfhst =>
      support_prf_bindV fun rsf hrsf =>
      support_prf_ret ?_
    have hfhst_eq : fhst = s0.2.2 := by
      simp only [hfhst, Expr.eval, env_get_succ, env_get_zero]
    have hb_fhst : AuthFixedValOnlineBounded (c 0 - 1) fhst := hfhst_eq ▸ hb0
    let ρVal : Env [authHybridStateFixedTy, .nat, cpaStTy, cpaPayloadTy, .opt (B 32)] :=
      .cons fhst (.cons idx (.cons s0 (.cons p0 (.cons y0 .nil))))
    obtain ⟨hOnVal, hRoVal, hRtVal⟩ :=
      finishCpaC_preserves
        (Var.zero : Var [authHybridStateFixedTy, .nat, cpaStTy, cpaPayloadTy, .opt (B 32)]
          authHybridStateFixedTy)
        (.bool true) (.bool true)
        (.var (.succ (.succ (.succ .zero))))
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.getDBytes
          (.var (.succ (.succ (.succ (.succ .zero))))))
        ρVal hb_fhst rsf hrsf
    have hp_eval :
        (Expr.var (.succ (.succ (.succ .zero))) :
          Expr pqxdhOps [authHybridStateFixedTy, .nat, cpaStTy, cpaPayloadTy, .opt (B 32)]
            cpaPayloadTy).eval ρVal = p0 := rfl
    rw [hp_eval] at hRoVal hRtVal
    have hRoEq : atomRoCache (embedVal authStateTy rsf.2.1.1) = atomRoCache s'.1.2.2.1.1 := by
      calc atomRoCache (embedVal authStateTy rsf.2.1.1)
          = valRoCache rsf.2.1.1 := atomRoCache_embedVal rsf.2.1.1
        _ = p0.2.2.2.2.2.2.2.2.2.2.2.2.1 := hRoVal
        _ = cpaPayloadRoCache (embedVal cpaPayloadTy p0) := (cpaPayloadRoCache_embedVal p0).symm
        _ = cpaPayloadRoCache p' := by rw [hp0]
        _ = atomRoCache s'.1.2.2.1.1 := hPause.payload_ok.ro_eq
    have hRtEq : atomRootRoCache (embedVal authStateTy rsf.2.1.1) = atomRootRoCache s'.1.2.2.1.1 := by
      calc atomRootRoCache (embedVal authStateTy rsf.2.1.1)
          = valRootRoCache rsf.2.1.1 := atomRootRoCache_embedVal rsf.2.1.1
        _ = p0.2.2.2.2.2.2.2.2.2.2.2.2.2 := hRtVal
        _ = cpaPayloadRootRoCache (embedVal cpaPayloadTy p0) :=
            (cpaPayloadRootRoCache_embedVal p0).symm
        _ = cpaPayloadRootRoCache p' := by rw [hp0]
        _ = atomRootRoCache s'.1.2.2.1.1 := hPause.payload_ok.root_eq
    obtain ⟨hc0, _, _, _, _, _⟩ := pause_counter_bounds S b hPause.counter_inv hPause.one_le_on
    refine ⟨hPause.counter_inv, ?_⟩
    change AuthFixedShadowAt S b (c 0) (c 0 + c 1) (c 0 + c 2)
      (embedVal authHybridStateFixedTy rsf.2, s'.2)
    refine ⟨(AuthFixedAtomOnlineBounded.iff_embedVal rsf.2).mpr (hc0 ▸ hOnVal), ?_, ?_, ?_⟩
    · change (atomRoCache (embedVal authStateTy rsf.2.1.1)).length ≤ c 0 + c 1
      rw [hRoEq]
      exact Nat.le_trans hPause.shadow_pre.ro_len_le (by omega)
    · change (atomRootRoCache (embedVal authStateTy rsf.2.1.1)).length ≤ c 0 + c 2
      rw [hRtEq]
      exact Nat.le_trans hPause.shadow_pre.root_len_le (by omega)
    · change RoBothShadowRel (AuthKindFuels.ofBudget S b).K_cap (embedVal authStateTy rsf.2.1.1) s'.2
      exact ⟨by rw [hRoEq, hRtEq]; exact hPause.shadow_pre.ro_shadow.both_valid,
        by rw [hRoEq]; exact hPause.shadow_pre.ro_shadow.ro_nodup,
        by rw [hRtEq]; exact hPause.shadow_pre.ro_shadow.root_nodup⟩

set_option linter.constructorNameAsVariable false in
private theorem cpa_hFinish (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (bOut : Bool)
    (y : (Ty.opt (PB 32)).denote)
    (_hc : ∀ j, c j ≤ authSimBounds b j) (hInv : AuthCpaInv S b c s') :
    (aeadCpa1KeyKindProg S b).finish.eval (.cons s' (.cons bOut (.cons y .nil))) =
      (aeadCpaOldAtomicProg S b).finish.eval
        (.cons (forgetCpa s') (.cons bOut (.cons y .nil))) := by
  simp only [aeadCpa1KeyKindProg, aeadCpaOldAtomicProg, forgetCpa,
    AuthCoreKArms.cpaKindFinishC, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.aeadCpaRedProg1Key,
    Comp.eval, Expr.eval, Env.get, Expr.v0, pure_bind]
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval
    (mapComp tlAuthPrim (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaFinishC S (AuthKindFuels.ofBudget S b).K_on))
    (fun {a} => AuthCoreKArms.dropShadow1)
    (.cons s'.1 (.cons bOut (.cons y .nil)))
    (.cons s'.1 (.cons s' (.cons bOut (.cons y .nil))))
    (fun v => by cases v with | zero => rfl | succ v => cases v with | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v)]
  apply mapComp_tlAuthPrim_congr
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaFinishC, projEnv]
  simp only [prf_letV_eval, Expr.eval, Env.get, ahsfHybrid]
  have hVal : AuthFixedValOnlineBounded (c 0) (projVal authHybridStateFixedTy s'.1.2.2) :=
    (AuthFixedAtomOnlineBounded.iff_embedVal _).mp (by
      rw [Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal]
      exact hInv.shadow_ok.online_le)
  have hKon : c 0 ≤ (AuthKindFuels.ofBudget S b).K_on := by
    have := hInv.counter_inv.on_le
    dsimp only [AuthKindFuels.ofBudget]; omega
  exact AuthCoreKSimArms.finalizeAuthFixedKDsl_fuel_eq S b
    (projVal authHybridStateFixedTy s'.1.2.2).1 bOut true _
    hVal.base_le hVal.initKemRecs_le hVal.recvKemRecs_le hVal.idealSessions_le hKon

private theorem cpaNonSendRhs_bridge {arg : Ty pqSig}
    (stepOld : Comp pqxdhOps pqPrimIface [authHybridStateFixedTy, arg]
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    (s' : authCpaShadowStTy.denote) (x0 : arg.denote) :
    let s0 := projVal cpaStTy s'.1
    (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, rsf.2)))) <$>
      (mapComp tlAuthPrim stepOld).eval (.cons s'.1.2.2 (.cons (embedVal arg x0) .nil)) =
    embedVal (.prod authRespTy cpaStTy) <$>
      ((fun rsf0 => (rsf0.1, (s0.1, (s0.2.1, rsf0.2)))) <$>
        stepOld.eval (.cons s0.2.2 (.cons x0 .nil))) := by
  intro s0
  have hs : s'.1 = embedVal cpaStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal cpaStTy s'.1).symm
  have hs1 : s'.1.1 = s0.1 := by rw [hs]; rfl
  have hs21 : s'.1.2.1 = s0.2.1 := by rw [hs]; rfl
  have hs22 : s'.1.2.2 = embedVal authHybridStateFixedTy s0.2.2 := by rw [hs]; rfl
  rw [hs1, hs21, hs22]
  have hMap := mapComp_tlAuthPrim_eval_embed stepOld (.cons s0.2.2 (.cons x0 .nil))
  dsimp only [embedEnv] at hMap
  rw [hMap, Functor.map_map, Functor.map_map]
  rfl

private theorem eval_inl_wrapCpaSlot {K_ctx Γ₁ Γ₂ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ K_ctx] [h₂ : Ext Γ₂ K_ctx]
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (m : Comp pqxdhOps pqPrimIface K_ctx RSF) (env : Env K_ctx) :
    (bindV (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.wrapCpaSlot idx ns m)
      fun r => .ret (.inl (v r)) :
      Comp pqxdhOps pqPrimIface K_ctx _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy).eval env =
    (fun rsf => Sum.inl (rsf.1, (env.get (h₁.wk idx), (env.get (h₂.wk ns), rsf.2)))) <$> m.eval env := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.wrapCpaSlot]
  rw [prf_bindV_eval, prf_bindV_eval, map_eq_bind_pure_comp, bind_assoc]
  congr 1

private theorem initPrin1KeyFixedKB_ren2 (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk u))
      (initPrin1KeyFixedKB F (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) =
    initPrin1KeyFixedKB F fhst u := rfl

private theorem corruptFixedKB_ren2 (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk u))
      (corruptFixedKB F (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) =
    corruptFixedKB F fhst u := rfl

private theorem genSpkFixedKB_ren2 (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk x))
      (genSpkFixedKB F (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
        (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) =
    genSpkFixedKB F fhst x := rfl

private theorem genOpkFixedKB_ren2 (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk x))
      (genOpkFixedKB F
        (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
        (Γ₂ := [.prod .nat (.prod .nat .nat)])
        (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero) =
    genOpkFixedKB F fhst x := rfl

private theorem registerFixedKB_ren2 {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk sk))
      (registerFixedKB (Γ₁ := [authHybridStateFixedTy, B 32])
        (Γ₂ := [B 32]) (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) =
    registerFixedKB fhst sk := rfl

private theorem initPrin1KeyFixedB_ren2 (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk u))
      (initPrin1KeyFixedB K
        (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) =
    initPrin1KeyFixedB K fhst u := rfl

private theorem corruptFixedB_ren2 (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk u))
      (corruptFixedB K (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) =
    corruptFixedB K fhst u := rfl

private theorem genSpkFixedB_ren2 (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk x))
      (genSpkFixedB K (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
        (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) =
    genSpkFixedB K fhst x := rfl

private theorem genOpkFixedB_ren2 (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk x))
      (genOpkFixedB K (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
        (Γ₂ := [.prod .nat (.prod .nat .nat)])
        (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero) =
    genOpkFixedB K fhst x := rfl

private theorem roFixedB_ren2 (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (sec : Var Γ₂ (B 192)) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk sec))
      (roFixedB K (Γ₁ := [authHybridStateFixedTy, B 192])
        (Γ₂ := [B 192]) (Δ := [authHybridStateFixedTy, B 192]) .zero .zero) =
    roFixedB K fhst sec := rfl

private theorem roRootFixedB_ren2 (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod (B 32) (B 32))) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk x))
      (roRootFixedB K (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
        (Γ₂ := [.prod (B 32) (B 32)]) (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)]) .zero .zero) =
    roRootFixedB K fhst x := rfl

private theorem registerFixedB_ren2 {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk sk))
      (registerFixedB (Γ₁ := [authHybridStateFixedTy, B 32])
        (Γ₂ := [B 32]) (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) =
    registerFixedB fhst sk := rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem cpaRecvC_ren2_poly (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) :
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename (ren2 (h₁.wk fhst) (h₂.wk x))
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S K opk
        (Γ₁ := [authHybridStateFixedTy, recvQTy])
        (Γ₂ := [recvQTy]) (Δ := [authHybridStateFixedTy, recvQTy]) .zero .zero) =
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S K opk fhst x := by
  cases opk <;> rfl

private def cpaPostStepValEval (S : Setup) (K : ℕ) (s0 : cpaStTy.denote) (t : AuthQuery S) :
    OracleComp PrimBaseSpec (Ty.prod authRespTy cpaStTy).denote :=
  let wrapNS {arg : Ty pqSig}
      (stepOld : Comp pqxdhOps pqPrimIface [authHybridStateFixedTy, arg] RSF) (x0 : arg.denote) :=
    (fun rsf0 => (rsf0.1, (s0.1, (s0.2.1, rsf0.2)))) <$> stepOld.eval (.cons s0.2.2 (.cons x0 .nil))
  let wrapSend (opk : Bool) (x0 : sendQTy.denote) :=
    (fun out => match out with
      | .inl d => (d.1, (s0.1, d.2))
      | .inr _ => ((aNone (Γ := [])).eval .nil, (s0.1, (s0.2.1, s0.2.2)))) <$>
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K opk false
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        .zero .zero .zero .zero).eval (.cons s0.1 (.cons s0.2.1 (.cons s0.2.2 (.cons x0 .nil))))
  match t with
  | .initPrin u =>
    wrapNS (initPrin1KeyFixedB K
      (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) u.val
  | .corruptIK u =>
    wrapNS (corruptFixedB K (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) u.val
  | .genSPK u j =>
    wrapNS (genSpkFixedB K (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
      (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) (u.val, j.val)
  | .genOPK u j o =>
    wrapNS (genOpkFixedB K (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
      (Γ₂ := [.prod .nat (.prod .nat .nat)]) (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero) (u.val, (j.val, o.val))
  | .sendOPK u i bu m0 m1 =>
    wrapSend true (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
  | .sendNoOPK u i bu m0 m1 =>
    wrapSend false (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
  | .recvOPK k j o msg =>
    wrapNS (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S K true
      (Γ₁ := [authHybridStateFixedTy, recvQTy]) (Γ₂ := [recvQTy]) (Δ := [authHybridStateFixedTy, recvQTy]) .zero .zero)
      (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))
  | .recvNoOPK k j l msg =>
    wrapNS (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S K false
      (Γ₁ := [authHybridStateFixedTy, recvQTy]) (Γ₂ := [recvQTy]) (Δ := [authHybridStateFixedTy, recvQTy]) .zero .zero)
      (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))
  | .roQuery sec =>
    wrapNS (roFixedB K (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192]) (Δ := [authHybridStateFixedTy, B 192]) .zero .zero) sec
  | .roRootQuery rk dh =>
    wrapNS (roRootFixedB K (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
      (Γ₂ := [.prod (B 32) (B 32)]) (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)]) .zero .zero) (rk, dh)
  | .revealDhSecrets =>
    pure ((aNone (Γ := [])).eval .nil, (s0.1, (s0.2.1, s0.2.2)))
  | .registerKey sk =>
    wrapNS (registerFixedB (Γ₁ := [authHybridStateFixedTy, B 32]) (Γ₂ := [B 32]) (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) sk

private theorem prf_caseSumV_inl {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (env : Env Γ) {a : τ₁.denote} (hs : s.eval env = .inl a) :
    (caseSumV s kl kr).eval env = (kl .zero).eval (.cons a env) := by
  dsimp only [caseSumV, Comp.eval]
  rw [hs]

private theorem prf_caseSumV_inr {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (env : Env Γ) {b : τ₂.denote} (hs : s.eval env = .inr b) :
    (caseSumV s kl kr).eval env = (kr .zero).eval (.cons b env) := by
  dsimp only [caseSumV, Comp.eval]
  rw [hs]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem cpaSendSlotB_false_opk_ren4 (S : Setup) (K : ℕ)
    {R₁ R₂ R₃ R₄ : Ty pqSig} :
    let QT := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy
    let Δ := [sendQTy, R₄, R₃, R₂, R₁, authHybridStateFixedTy, .nat, .nat, cpaStTy, QT]
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren4 (Δ := Δ)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.succ (.succ (.succ (.succ (.succ .zero)))))
        .zero)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K true false
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy])
        (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        .zero .zero .zero .zero) =
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K true false
      (Γ₁ := [.nat, cpaStTy, QT])
      (Γ₂ := [.nat, .nat, cpaStTy, QT])
      (Γ₃ := [authHybridStateFixedTy, .nat, .nat, cpaStTy, QT])
      (Γ₄ := Δ) (Δ := Δ)
      .zero .zero .zero .zero := rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem cpaSendSlotB_false_noOpk_ren4 (S : Setup) (K : ℕ)
    {R₁ R₂ R₃ R₄ R₅ : Ty pqSig} :
    let QT := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy
    let Δ := [sendQTy, R₅, R₄, R₃, R₂, R₁, authHybridStateFixedTy, .nat, .nat, cpaStTy, QT]
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren4 (Δ := Δ)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
        .zero)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K false false
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy])
        (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        .zero .zero .zero .zero) =
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K false false
      (Γ₁ := [.nat, cpaStTy, QT])
      (Γ₂ := [.nat, .nat, cpaStTy, QT])
      (Γ₃ := [authHybridStateFixedTy, .nat, .nat, cpaStTy, QT])
      (Γ₄ := Δ) (Δ := Δ)
      .zero .zero .zero .zero := rfl

set_option linter.constructorNameAsVariable false in
private theorem cpaStep1KeyC_false_eval_qenc (S : Setup) (K : ℕ)
    (s0 : cpaStTy.denote) (t : AuthQuery S) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaStep1KeyC S K false).eval
      (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
    Sum.inl <$> cpaPostStepValEval S K s0 t := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaStep1KeyC]
  iterate 3 rw [prf_letV_eval]
  dsimp only [Expr.eval, Env.get,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaNonSendSlot1KeyC]
  cases t with
  | initPrin u =>
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (initPrin1KeyFixedB_ren2 K _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | corruptIK u =>
    rw [prf_caseSumV_inr _ _ _ _ rfl, prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (corruptFixedB_ren2 K _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | genSPK u j =>
    iterate 2 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (genSpkFixedB_ren2 K _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | genOPK u j o =>
    iterate 3 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (genOpkFixedB_ren2 K _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | sendOPK u i bu m0 m1 =>
    iterate 4 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, prf_bindV_eval,
      compRename_ren4_eval _ _ _ _ _ _ _ (cpaSendSlotB_false_opk_ren4 S K)]
    dsimp only [cpaPostStepValEval, Env.get]
    rw [Functor.map_map, map_eq_bind_pure_comp]
    congr 1; funext out; cases out <;> rfl
  | sendNoOPK u i bu m0 m1 =>
    iterate 5 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, prf_bindV_eval,
      compRename_ren4_eval _ _ _ _ _ _ _ (cpaSendSlotB_false_noOpk_ren4 S K)]
    dsimp only [cpaPostStepValEval, Env.get]
    rw [Functor.map_map, map_eq_bind_pure_comp]
    congr 1; funext out; cases out <;> rfl
  | recvOPK k j o msg =>
    iterate 6 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (cpaRecvC_ren2_poly S K true _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | recvNoOPK k j l msg =>
    iterate 7 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (cpaRecvC_ren2_poly S K false _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | roQuery sec =>
    iterate 8 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (roFixedB_ren2 K _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | roRootQuery rk dh =>
    iterate 9 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (roRootFixedB_ren2 K _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]
  | revealDhSecrets =>
    iterate 10 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, prf_bindV_eval]
    dsimp only [cpaPostStepValEval, Comp.eval, v, Expr.eval,
      ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [pure_bind, map_pure]
    rfl
  | registerKey sk =>
    iterate 11 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (registerFixedB_ren2 _ _)]
    dsimp only [cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    rw [Functor.map_map]

set_option linter.constructorNameAsVariable false in
private theorem cpaPost1KeyC_eval_qenc (S : Setup) (K : ℕ) (s0 : cpaStTy.denote) (t : AuthQuery S) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPost1KeyC S K).eval
      (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
    cpaPostStepValEval S K s0 t := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPost1KeyC]
  rw [prf_bindV_eval, cpaStep1KeyC_false_eval_qenc]
  erw [bind_map_left]
  simp only [caseSumV, Comp.eval, v, Expr.eval, ext_refl_wk, env_get_zero, bind_pure]

private def dispatchAuthQByQuery {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqAtomicSig T}
    {S : Setup} {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (ρ : Env Γ) (t : AuthQuery S)
    (armInitPrin armCorrupt : Comp pqAtomicOps I (.nat :: Γ) out)
    (armGenSpk : Comp pqAtomicOps I (.prod .nat .nat :: Γ) out)
    (armGenOpk : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: Γ) out)
    (armSendOpk armSendNoOpk : Comp pqAtomicOps I (AuthCoreK.authSendQAtomicTy :: Γ) out)
    (armRecvOpk armRecvNoOpk : Comp pqAtomicOps I (AuthCoreK.authRecvQAtomicTy :: Γ) out)
    (armRo : Comp pqAtomicOps I (PB 192 :: Γ) out)
    (armRoRoot : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: Γ) out)
    (armRevealDh : Comp pqAtomicOps I (.unit :: Γ) out)
    (armRegister : Comp pqAtomicOps I (PB 32 :: Γ) out) :
    OracleComp T out.denote :=
  match t with
  | .initPrin u => armInitPrin.eval (.cons (embedVal .nat u.val) ρ)
  | .corruptIK u => armCorrupt.eval (.cons (embedVal .nat u.val) ρ)
  | .genSPK u j => armGenSpk.eval (.cons (embedVal (.prod .nat .nat) (u.val, j.val)) ρ)
  | .genOPK u j o =>
    armGenOpk.eval (.cons (embedVal (.prod .nat (.prod .nat .nat)) (u.val, (j.val, o.val))) ρ)
  | .sendOPK u i bu m0 m1 =>
    armSendOpk.eval (.cons (embedVal sendQTy
      (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))) ρ)
  | .sendNoOPK u i bu m0 m1 =>
    armSendNoOpk.eval (.cons (embedVal sendQTy
      (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))) ρ)
  | .recvOPK k j o msg =>
    armRecvOpk.eval (.cons (embedVal recvQTy
      (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))) ρ)
  | .recvNoOPK k j l msg =>
    armRecvNoOpk.eval (.cons (embedVal recvQTy
      (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))) ρ)
  | .roQuery sec => armRo.eval (.cons sec ρ)
  | .roRootQuery rk dh => armRoRoot.eval (.cons (rk, dh) ρ)
  | .revealDhSecrets => armRevealDh.eval (.cons () ρ)
  | .registerKey sk => armRegister.eval (.cons sk ρ)

private theorem dispatchAuthQEval_eq_byQuery {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqAtomicSig T}
    {S : Setup} {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (ρ : Env Γ) (t : AuthQuery S)
    (armInitPrin armCorrupt : Comp pqAtomicOps I (.nat :: Γ) out)
    (armGenSpk : Comp pqAtomicOps I (.prod .nat .nat :: Γ) out)
    (armGenOpk : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: Γ) out)
    (armSendOpk armSendNoOpk : Comp pqAtomicOps I (AuthCoreK.authSendQAtomicTy :: Γ) out)
    (armRecvOpk armRecvNoOpk : Comp pqAtomicOps I (AuthCoreK.authRecvQAtomicTy :: Γ) out)
    (armRo : Comp pqAtomicOps I (PB 192 :: Γ) out)
    (armRoRoot : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: Γ) out)
    (armRevealDh : Comp pqAtomicOps I (.unit :: Γ) out)
    (armRegister : Comp pqAtomicOps I (PB 32 :: Γ) out) :
    dispatchAuthQEval ρ t armInitPrin armCorrupt armGenSpk armGenOpk
      armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk
      armRo armRoRoot armRevealDh armRegister =
    dispatchAuthQByQuery ρ t armInitPrin armCorrupt armGenSpk armGenOpk
      armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk
      armRo armRoRoot armRevealDh armRegister := by
  dsimp only [dispatchAuthQEval, dispatchAuthQByQuery]
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq t]
  cases t <;> rfl

private theorem cpa_online_step_arith {S : Setup} {b : QueryBudget}
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hCnt : AuthCounterInv b c)
    (hOnPred : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t) (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    AuthCounterInv b (bumpPred (authSimPred S) c t) ∧
    c 0 + 1 ≤ (AuthKindFuels.ofBudget S b).K_on ∧
    (c 0 + c 1) + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro ∧
    (c 0 + c 2) + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro ∧
    (∀ {s1 : authCpaShadowStTy.denote},
      AuthFixedShadowAt S b (c 0 + 1) (c 0 + c 1 + 1) (c 0 + c 2 + 1) (cpaShadowFixed s1) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s1) ∧
    (∀ {s1 : authCpaShadowStTy.denote},
      AuthFixedShadowAt S b (c 0 + 1) (c 0 + c 1) (c 0 + c 2) (cpaShadowFixed s1) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s1) ∧
    (∀ {s1 : authCpaShadowStTy.denote},
      AuthFixedShadowAt S b (c 0) (c 0 + c 1) (c 0 + c 2) (cpaShadowFixed s1) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s1) := by
  have hCnt' : AuthCounterInv b (bumpPred (authSimPred S) c t) := hCnt.bump t hroom
  obtain ⟨hOnB, hRoB, hRtB, _⟩ := hCnt.online_step_bounds hOnPred hroom
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c t hOnPred hNotRo hNotRt
  have hRo' : (c 0 + c 1) + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro := by omega
  have hRt' : (c 0 + c 2) + 1 ≤ (AuthKindFuels.ofBudget S b).K_ro := by omega
  have hm11 : c 0 + 1 ≤ bumpPred (authSimPred S) c t 0 := by omega
  have hm12 : c 0 + c 1 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1 := by omega
  have hm13 : c 0 + c 2 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2 := by omega
  have hm22 : c 0 + c 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1 := by omega
  have hm23 : c 0 + c 2 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2 := by omega
  have hm31 : c 0 ≤ bumpPred (authSimPred S) c t 0 := by omega
  exact ⟨hCnt', hOnB, hRo', hRt',
    fun h => ⟨hCnt', h.mono hm11 hm12 hm13⟩,
    fun h => ⟨hCnt', h.mono hm11 hm22 hm23⟩,
    fun h => ⟨hCnt', h.mono hm31 hm22 hm23⟩⟩

private theorem cpa_ro_step_arith {S : Setup} {b : QueryBudget}
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hCnt : AuthCounterInv b c)
    (hNotOn : ¬ authSimPred S 0 t)
    (hRoPred : authSimPred S 1 t) (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    (c 0 + c 1) + 1 ≤ b.q_total ∧
    (c 0 + c 1) + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap ∧
    (∀ {s1 : authCpaShadowStTy.denote},
      AuthFixedShadowAt S b (c 0) (c 0 + c 1 + 1) (c 0 + c 2) (cpaShadowFixed s1) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s1) := by
  have hCnt' : AuthCounterInv b (bumpPred (authSimPred S) c t) := hCnt.bump t hroom
  obtain ⟨hRoK, hRoOld, hCap⟩ := hCnt.ro_step_bounds hRoPred hroom
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_ro_slots c t hNotOn hRoPred hNotRt
  have h1 : (c 0 + c 1) + 1 ≤ b.q_total := by omega
  have h2 : (c 0 + c 1) + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap := by omega
  have hm1 : c 0 ≤ bumpPred (authSimPred S) c t 0 := by omega
  have hm2 : c 0 + c 1 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1 := by omega
  have hm3 : c 0 + c 2 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2 := by omega
  exact ⟨h1, h2, fun h => ⟨hCnt', h.mono hm1 hm2 hm3⟩⟩

private theorem cpa_roRoot_step_arith {S : Setup} {b : QueryBudget}
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hCnt : AuthCounterInv b c)
    (hNotOn : ¬ authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t) (hRtPred : authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    (c 0 + c 2) + 1 ≤ b.q_total ∧
    (c 0 + c 2) + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap ∧
    (∀ {s1 : authCpaShadowStTy.denote},
      AuthFixedShadowAt S b (c 0) (c 0 + c 1) (c 0 + c 2 + 1) (cpaShadowFixed s1) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s1) := by
  have hCnt' : AuthCounterInv b (bumpPred (authSimPred S) c t) := hCnt.bump t hroom
  obtain ⟨hRtK, hRtOld, hCap⟩ := hCnt.roRoot_step_bounds hRtPred hroom
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_roRoot_slots c t hNotOn hNotRo hRtPred
  have h1 : (c 0 + c 2) + 1 ≤ b.q_total := by omega
  have h2 : (c 0 + c 2) + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap := by omega
  have hm1 : c 0 ≤ bumpPred (authSimPred S) c t 0 := by omega
  have hm2 : c 0 + c 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1 := by omega
  have hm3 : c 0 + c 2 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2 := by omega
  exact ⟨h1, h2, fun h => ⟨hCnt', h.mono hm1 hm2 hm3⟩⟩

private abbrev cpaSendPostArmC (S : Setup) (b : QueryBudget) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (AuthCoreK.authSendQAtomicTy :: authCpaShadowStTy :: Γ)
      (.prod (authCodec S).R authCpaShadowStTy) :=
  .bind (AuthCoreKArms.liftAuthPrim1
      (letV (.fst (.var .zero)) fun s =>
       letV (.snd (.var (.succ .zero))) fun x =>
       letV (.fst (v s)) fun idx =>
       letV (.fst (.snd (v s))) fun ns =>
       letV (.snd (.snd (v s))) fun fhst =>
       bindV (AuthCoreKArms.cpaSendSlotKB S (AuthKindFuels.ofBudget S b).K_on
         (AuthKindFuels.ofBudget S b).K_ro opk false idx ns fhst x) fun r =>
       caseSumV (v r)
         (fun d => .ret (.pair (.fst (v d)) (.pair (v idx) (.snd (v d)))))
         (fun _ => .ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst))))))
      (.pair (.fst .v1) .v0))
    (.bind (AuthCoreK.syncRoBothC (AuthKindFuels.ofBudget S b).K_cap
        (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
        (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
        (.snd .v2))
      (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))

private abbrev cpaRoPostArmC (S : Setup) (b : QueryBudget)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (PB 192 :: authCpaShadowStTy :: Γ)
      (.prod (authCodec S).R authCpaShadowStTy) :=
  .bind (AuthCoreK.roFixedShadowArmC aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap
      (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
    (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))

private abbrev cpaRoRootPostArmC (S : Setup) (b : QueryBudget)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (.prod (PB 32) (PB 32) :: authCpaShadowStTy :: Γ)
      (.prod (authCodec S).R authCpaShadowStTy) :=
  .bind (AuthCoreK.roRootFixedShadowArmC aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap
      (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
    (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4096 in
private theorem cpa_hPost_send (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (t : AuthQuery S)
    (x0 : sendQTy.denote) {Γ : List (Ty pqAtomicSig)} (ρ0 : Env Γ)
    (hOnPred : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t) (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthCpaInv S b c s') :
    Prod.map id forgetCpa <$>
        (cpaSendPostArmC S b opk).eval (.cons (embedVal sendQTy x0) (.cons s' ρ0)) =
      embedVal (.prod authRespTy cpaStTy) <$>
        ((fun out => match out with
          | .inl d => (d.1, ((projVal cpaStTy s'.1).1, d.2))
          | .inr _ => ((aNone (Γ := [])).eval .nil,
              ((projVal cpaStTy s'.1).1, ((projVal cpaStTy s'.1).2.1, (projVal cpaStTy s'.1).2.2)))) <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk false
            (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
            (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
            (Γ₃ := [authHybridStateFixedTy, sendQTy])
            (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
            .zero .zero .zero .zero).eval
            (.cons (projVal cpaStTy s'.1).1
              (.cons (projVal cpaStTy s'.1).2.1
                (.cons (projVal cpaStTy s'.1).2.2 (.cons x0 .nil))))) ∧
    ∀ p ∈ support ((cpaSendPostArmC S b opk).eval (.cons (embedVal sendQTy x0) (.cons s' ρ0))),
      AuthCpaInv S b (bumpPred (authSimPred S) c t) p.2 := by
  obtain ⟨_, hOnB, hRoB, hRtB, hLift1, _, _⟩ :=
    cpa_online_step_arith c t hInv.counter_inv hOnPred hNotRo hNotRt hroom
  have hProj : projVal sendQTy (embedVal sendQTy x0) = x0 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.projVal_embedVal sendQTy x0
  generalize embedVal sendQTy x0 = xA at hProj ⊢
  have hSim := cpaSendPostArm_sim S b opk s' xA ρ0 hInv.shadow_ok hOnB hRoB hRtB
  have hArmEq := hSim.1
  rw [hProj] at hArmEq
  exact ⟨hArmEq, fun p hp => hLift1 (hSim.2 p hp)⟩

private theorem support_imp {ι : Type} {T : OracleSpec ι} {α : Type}
    {m₁ m₂ : OracleComp T α} {P Q : α → Prop}
    (hm : m₁ = m₂) (h1 : ∀ p ∈ support m₁, P p) (h2 : ∀ p, P p → Q p) :
    ∀ p ∈ support m₂, Q p := by
  subst hm
  intro p hp
  exact h2 p (h1 p hp)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4096 in
private theorem cpa_hPost_recv (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (t : AuthQuery S)
    (x0 : recvQTy.denote) {Γ : List (Ty pqAtomicSig)} (ρ0 : Env Γ)
    (hOnPred : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t) (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthCpaInv S b c s') :
    Prod.map id forgetCpa <$>
        (AuthCoreKArms.cpaRecvArmC S (AuthKindFuels.ofBudget S b) opk).eval
          (.cons (embedVal recvQTy x0) (.cons s' ρ0)) =
      embedVal (.prod authRespTy cpaStTy) <$>
        ((fun rsf0 => (rsf0.1, ((projVal cpaStTy s'.1).1, ((projVal cpaStTy s'.1).2.1, rsf0.2)))) <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
            (Γ₁ := [authHybridStateFixedTy, recvQTy]) (Γ₂ := [recvQTy])
            (Δ := [authHybridStateFixedTy, recvQTy]) .zero .zero).eval
            (.cons (projVal cpaStTy s'.1).2.2 (.cons x0 .nil))) ∧
    ∀ p ∈ support ((AuthCoreKArms.cpaRecvArmC S (AuthKindFuels.ofBudget S b) opk).eval
        (.cons (embedVal recvQTy x0) (.cons s' ρ0))),
      AuthCpaInv S b (bumpPred (authSimPred S) c t) p.2 := by
  obtain ⟨_, hOnB, hRoB, hRtB, hLift1, _, _⟩ :=
    cpa_online_step_arith c t hInv.counter_inv hOnPred hNotRo hNotRt hroom
  have hSim := cpaRecvArmC_sim S b opk s' (embedVal recvQTy x0) ρ0 hInv.shadow_ok hOnB hRoB hRtB
  have hBridge := cpaNonSendRhs_bridge
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaRecvC S b.q_total opk
      (Γ₁ := [authHybridStateFixedTy, recvQTy]) (Γ₂ := [recvQTy])
      (Δ := [authHybridStateFixedTy, recvQTy]) .zero .zero) s' x0
  exact ⟨Eq.trans hSim.1 hBridge, support_imp rfl hSim.2 (fun _ h => hLift1 h)⟩

private theorem oc_map_pure {ι : Type} {T : OracleSpec ι} {α β : Type}
    (f : α → β) (a : α) : (f <$> (pure a : OracleComp T α)) = pure (f a) :=
  map_pure f a

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
private theorem cpa_hPost (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (t : AuthQuery S)
    (_hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthCpaInv S b c s') :
    Prod.map id forgetCpa <$>
        (aeadCpa1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (aeadCpaOldAtomicProg S b).handlePost.eval
        (.cons (forgetCpa s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support
        ((aeadCpa1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      AuthCpaInv S b (bumpPred (authSimPred S) c t) p.2 := by
  have hEmbedS : embedVal cpaStTy (projVal cpaStTy s'.1) = s'.1 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal cpaStTy s'.1
  have hRhs :
      (aeadCpaOldAtomicProg S b).handlePost.eval
        (.cons (forgetCpa s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal (.prod authRespTy cpaStTy) <$>
        cpaPostStepValEval S b.q_total (projVal cpaStTy s'.1) t := by
    change (Computational.Proofs.SignalPqxdh.AtomicLift.liftAuthHandle tlAuthPrim S
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPost1KeyC S b.q_total)).eval
        (.cons s'.1 (.cons ((authCodec S).qenc t) .nil)) = _
    conv_lhs => rw [← hEmbedS]
    rw [Computational.Proofs.SignalPqxdh.AtomicLift.liftAuthHandle_eval tlAuthPrim S
        tlAuthPrim_unsupported_zero
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPost1KeyC S b.q_total)
        (projVal cpaStTy s'.1) t,
      cpaPost1KeyC_eval_qenc S b.q_total (projVal cpaStTy s'.1) t]
  have hLhs :
      (aeadCpa1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      dispatchAuthQByQuery (.cons s' (.cons ((authCodec S).qenc t) .nil)) t
        (AuthCoreKArms.cpaBaseArmC S
          (fun fhst u => initPrin1KeyFixedKB (AuthKindFuels.ofBudget S b) fhst u))
        (AuthCoreKArms.cpaBaseArmC S
          (fun fhst u => corruptFixedKB (AuthKindFuels.ofBudget S b) fhst u))
        (AuthCoreKArms.cpaBaseArmC S
          (fun fhst x => genSpkFixedKB (AuthKindFuels.ofBudget S b) fhst x))
        (AuthCoreKArms.cpaBaseArmC S
          (fun fhst x => genOpkFixedKB (AuthKindFuels.ofBudget S b) fhst x))
        (cpaSendPostArmC S b true) (cpaSendPostArmC S b false)
        (AuthCoreKArms.cpaRecvArmC S (AuthKindFuels.ofBudget S b) true)
        (AuthCoreKArms.cpaRecvArmC S (AuthKindFuels.ofBudget S b) false)
        (cpaRoPostArmC S b) (cpaRoRootPostArmC S b)
        (.ret (.pair AuthCoreK.aNoneAtomicE .v1))
        (AuthCoreKArms.cpaBaseArmC S (fun fhst sk => registerFixedKB fhst sk)) := by
    dsimp only [aeadCpa1KeyKindProg, AuthCoreKArms.cpaKindHandlePostC]
    exact (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ t rfl _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dispatchAuthQEval_eq_byQuery _ t _ _ _ _ _ _ _ _ _ _ _ _)
  rw [hRhs, hLhs]
  generalize (Env.cons ((authCodec S).qenc t) .nil : Env [(authCodec S).Q]) = ρ0
  cases t with
  | initPrin u =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.initPrin u) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.initPrinFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') u.val hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst u => initPrin1KeyFixedKB (AuthKindFuels.ofBudget S b) fhst u)
      (fun fhst u => initPrin1KeyFixedB b.q_total fhst u)
      (by rfl) s' (embedVal .nat u.val) ρ0 hSh.1 hSh.2
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (initPrin1KeyFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
          (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) s' u.val),
      support_imp rfl hArm.2 (fun _ h => hLift2 h)⟩
  | corruptIK u =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.corruptIK u) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.corruptFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') u.val hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst u => corruptFixedKB (AuthKindFuels.ofBudget S b) fhst u)
      (fun fhst u => corruptFixedB b.q_total fhst u)
      (by rfl) s' (embedVal .nat u.val) ρ0 hSh.1 hSh.2
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (corruptFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
          (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) s' u.val),
      support_imp rfl hArm.2 (fun _ h => hLift2 h)⟩
  | genSPK u j =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.genSPK u j) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.genSpkFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') (u.val, j.val) hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst x => genSpkFixedKB (AuthKindFuels.ofBudget S b) fhst x)
      (fun fhst x => genSpkFixedB b.q_total fhst x)
      (by rfl) s' (embedVal (.prod .nat .nat) (u.val, j.val)) ρ0 hSh.1 hSh.2
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (genSpkFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
          (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) s' (u.val, j.val)),
      support_imp rfl hArm.2 (fun _ h => hLift2 h)⟩
  | genOPK u j o =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.genOPK u j o) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.genOpkFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') (u.val, (j.val, o.val)) hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst x => genOpkFixedKB (AuthKindFuels.ofBudget S b) fhst x)
      (fun fhst x => genOpkFixedB b.q_total fhst x)
      (by rfl) s' (embedVal (.prod .nat (.prod .nat .nat)) (u.val, (j.val, o.val))) ρ0 hSh.1 hSh.2
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (genOpkFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
          (Γ₂ := [.prod .nat (.prod .nat .nat)])
          (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero)
        s' (u.val, (j.val, o.val))),
      support_imp rfl hArm.2 (fun _ h => hLift2 h)⟩
  | sendOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    exact cpa_hPost_send S b true c s' (.sendOPK u i bu m0 m1)
      (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1)))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv
  | sendNoOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    exact cpa_hPost_send S b false c s' (.sendNoOPK u i bu m0 m1)
      (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1)))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv
  | recvOPK k j o msg =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    exact cpa_hPost_recv S b true c s' (.recvOPK k j o msg)
      (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv
  | recvNoOPK k j l msg =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    exact cpa_hPost_recv S b false c s' (.recvNoOPK k j l msg)
      (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv
  | roQuery sec =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval, cpaRoPostArmC]
    obtain ⟨hRoOld, hRoCap, hLiftRo⟩ :=
      cpa_ro_step_arith c (.roQuery sec) hInv.counter_inv
        (fun h => nomatch h) trivial (fun h => nomatch h) hroom
    have hArm := cpaRoArm_sim S b s' sec ρ0 hInv.shadow_ok hRoOld hRoCap
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (roFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
          (Δ := [authHybridStateFixedTy, B 192]) .zero .zero) s' sec),
      support_imp rfl hArm.2 (fun _ h => hLiftRo h)⟩
  | roRootQuery rk dh =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval, cpaRoRootPostArmC]
    obtain ⟨hRtOld, hRtCap, hLiftRt⟩ :=
      cpa_roRoot_step_arith c (.roRootQuery rk dh) hInv.counter_inv
        (fun h => nomatch h) (fun h => nomatch h) trivial hroom
    have hArm := cpaRoRootArm_sim S b s' (rk, dh) ρ0 hInv.shadow_ok hRtOld hRtCap
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (roRootFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
          (Γ₂ := [.prod (B 32) (B 32)])
          (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)]) .zero .zero) s' (rk, dh)),
      support_imp rfl hArm.2 (fun _ h => hLiftRt h)⟩
  | revealDhSecrets =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval,
      Comp.eval, Expr.eval, Env.get, Expr.v1, AuthCoreK.aNoneAtomicE]
    obtain ⟨_, _, _, _, _, _, hLift3⟩ :=
      cpa_online_step_arith c .revealDhSecrets hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    constructor
    · rw [oc_map_pure, oc_map_pure]
      exact congrArg pure (Prod.ext rfl hEmbedS.symm)
    · intro p hp
      have hp' : p = (Sum.inl (), s') := Iff.mp (mem_support_pure_iff _ _) hp
      subst hp'
      exact hLift3 hInv.shadow_ok
  | registerKey sk =>
    dsimp only [dispatchAuthQByQuery, cpaPostStepValEval]
    obtain ⟨_, _, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.registerKey sk) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hPres0 := AuthCoreKSimArmsFixed.registerFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') sk hInv.shadow_ok
    have hArm := cpaBaseArmC_sim S b
      (fun fhst sk => registerFixedKB fhst sk)
      (fun fhst sk => registerFixedB fhst sk)
      (by rfl) s' (embedVal (B 32) sk) ρ0 rfl hPres0
    exact ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (registerFixedB
          (Γ₁ := [authHybridStateFixedTy, B 32]) (Γ₂ := [B 32])
          (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) s' sk),
      support_imp rfl hArm.2 (fun _ h => hLift2 h)⟩

private abbrev cpaPrePauseOutAtomicTy : Ty pqAtomicSig :=
  .prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
    (.prod (embedTy cpaPayloadTy) authCpaShadowStTy)

private def cpaPreStepValEval (S : Setup) (K : ℕ) (s0 : cpaStTy.denote) (t : AuthQuery S) :
    OracleComp PrimBaseSpec _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy.denote :=
  let wrapSendPre (opk : Bool) (x0 : sendQTy.denote) :=
    (fun out => match out with
      | .inl d => Sum.inl (d.1, (s0.1, d.2))
      | .inr p => Sum.inr (p.1, (p.2.1, (s0.1, p.2.2)))) <$>
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K opk true
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        .zero .zero .zero .zero).eval (.cons s0.1 (.cons s0.2.1 (.cons s0.2.2 (.cons x0 .nil))))
  match t with
  | .sendOPK u i bu m0 m1 =>
    wrapSendPre true (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
  | .sendNoOPK u i bu m0 m1 =>
    wrapSendPre false (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
  | _ => Sum.inl <$> cpaPostStepValEval S K s0 t

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem cpaSendSlotB_true_opk_ren4 (S : Setup) (K : ℕ)
    {R₁ R₂ R₃ R₄ : Ty pqSig} :
    let QT := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy
    let Δ := [sendQTy, R₄, R₃, R₂, R₁, authHybridStateFixedTy, .nat, .nat, cpaStTy, QT]
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren4 (Δ := Δ)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.succ (.succ (.succ (.succ (.succ .zero)))))
        .zero)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K true true
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy])
        (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        .zero .zero .zero .zero) =
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K true true
      (Γ₁ := [.nat, cpaStTy, QT])
      (Γ₂ := [.nat, .nat, cpaStTy, QT])
      (Γ₃ := [authHybridStateFixedTy, .nat, .nat, cpaStTy, QT])
      (Γ₄ := Δ) (Δ := Δ)
      .zero .zero .zero .zero := rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem cpaSendSlotB_true_noOpk_ren4 (S : Setup) (K : ℕ)
    {R₁ R₂ R₃ R₄ R₅ : Ty pqSig} :
    let QT := _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy
    let Δ := [sendQTy, R₅, R₄, R₃, R₂, R₁, authHybridStateFixedTy, .nat, .nat, cpaStTy, QT]
    Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (ren4 (Δ := Δ)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
        .zero)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K false true
        (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy])
        (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
        .zero .zero .zero .zero) =
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S K false true
      (Γ₁ := [.nat, cpaStTy, QT])
      (Γ₂ := [.nat, .nat, cpaStTy, QT])
      (Γ₃ := [authHybridStateFixedTy, .nat, .nat, cpaStTy, QT])
      (Γ₄ := Δ) (Δ := Δ)
      .zero .zero .zero .zero := rfl

set_option linter.constructorNameAsVariable false in
private theorem cpaPre1KeyC_eval_qenc (S : Setup) (K : ℕ)
    (s0 : cpaStTy.denote) (t : AuthQuery S) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPre1KeyC S K).eval
      (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
    cpaPreStepValEval S K s0 t := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPre1KeyC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaStep1KeyC]
  iterate 3 rw [prf_letV_eval]
  dsimp only [Expr.eval, Env.get,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaNonSendSlot1KeyC]
  cases t with
  | initPrin u =>
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (initPrin1KeyFixedB_ren2 K _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | corruptIK u =>
    rw [prf_caseSumV_inr _ _ _ _ rfl, prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (corruptFixedB_ren2 K _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | genSPK u j =>
    iterate 2 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (genSpkFixedB_ren2 K _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | genOPK u j o =>
    iterate 3 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (genOpkFixedB_ren2 K _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | sendOPK u i bu m0 m1 =>
    iterate 4 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, prf_bindV_eval,
      compRename_ren4_eval _ _ _ _ _ _ _ (cpaSendSlotB_true_opk_ren4 S K)]
    simp only [cpaPreStepValEval, env_get_succ, env_get_zero]
    rw [map_eq_bind_pure_comp]
    congr 1; funext out; cases out <;> rfl
  | sendNoOPK u i bu m0 m1 =>
    iterate 5 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, prf_bindV_eval,
      compRename_ren4_eval _ _ _ _ _ _ _ (cpaSendSlotB_true_noOpk_ren4 S K)]
    simp only [cpaPreStepValEval, env_get_succ, env_get_zero]
    rw [map_eq_bind_pure_comp]
    congr 1; funext out; cases out <;> rfl
  | recvOPK k j o msg =>
    iterate 6 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (cpaRecvC_ren2_poly S K true _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | recvNoOPK k j l msg =>
    iterate 7 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (cpaRecvC_ren2_poly S K false _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | roQuery sec =>
    iterate 8 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (roFixedB_ren2 K _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | roRootQuery rk dh =>
    iterate 9 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (roRootFixedB_ren2 K _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]
  | revealDhSecrets =>
    iterate 10 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [prf_caseSumV_inl _ _ _ _ rfl, prf_bindV_eval]
    simp only [cpaPreStepValEval, cpaPostStepValEval, Comp.eval, v, Expr.eval,
      ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, pure_bind, map_pure]
    rfl
  | registerKey sk =>
    iterate 11 rw [prf_caseSumV_inr _ _ _ _ rfl]
    rw [eval_inl_wrapCpaSlot,
      compRename_ren2_eval _ _ _ _ _ (registerFixedB_ren2 _ _)]
    simp only [cpaPreStepValEval, cpaPostStepValEval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero,
      Functor.map_map]

private theorem cpaPre_map_map_eq {ι : Type} {T : OracleSpec ι} {α β γ δ : Type}
    (g₁ : β → δ) (g₂ : α → β) (h₁ : γ → δ) (h₂ : α → γ)
    (m : OracleComp T α) (hfg : ∀ a, g₁ (g₂ a) = h₁ (h₂ a)) :
    g₁ <$> (g₂ <$> m) = h₁ <$> (h₂ <$> m) := by
  rw [Functor.map_map, Functor.map_map]
  congr 1; funext a; exact hfg a

private theorem cpaPre_wrapInl_bridge (S : Setup) {Γ : List (Ty pqAtomicSig)}
    (m : Comp pqAtomicOps pqAuthPrimIface Γ (.prod (authCodec S).R authCpaShadowStTy))
    (env : Env Γ)
    (val : OracleComp PrimBaseSpec (Ty.prod authRespTy cpaStTy).denote)
    {P : authCpaShadowStTy.denote → Prop}
    {Q : (embedTy cpaPayloadTy).denote → authCpaShadowStTy.denote → Prop}
    (h : Prod.map id forgetCpa <$> m.eval env = embedVal (.prod authRespTy cpaStTy) <$> val ∧
      ∀ p ∈ support (m.eval env), P p.2) :
    let armInl : Comp pqAtomicOps pqAuthPrimIface Γ
        (.sum (.prod (authCodec S).R authCpaShadowStTy) cpaPrePauseOutAtomicTy) :=
      Comp.bind m (.ret (.inl .v0))
    (forgetPreOut id forgetCpa <$> armInl.eval env =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$> (Sum.inl <$> val)) ∧
    (∀ vOut s'₁, .inl (vOut, s'₁) ∈ support (armInl.eval env) → P s'₁) ∧
    (∀ c_out p' s'₁, .inr (c_out, p', s'₁) ∈ support (armInl.eval env) → Q p' s'₁) := by
  intro armInl
  refine ⟨?_, ?_, ?_⟩
  · let OutT := ((authCodec S).R.denote × (embedTy cpaStTy).denote) ⊕
      ((Ty.prod (PB 158) (.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote ×
        (embedTy cpaPayloadTy).denote × (embedTy cpaStTy).denote)
    have hBind : armInl.eval env = Sum.inl <$> m.eval env := by
      dsimp only [armInl, Comp.eval, Expr.eval, Env.get, Expr.v0]
      rw [map_eq_bind_pure_comp]
      rfl
    have hL :
        forgetPreOut id forgetCpa <$> armInl.eval env =
        ((Sum.inl : ((authCodec S).R.denote × (embedTy cpaStTy).denote) → OutT) <$>
          (Prod.map id forgetCpa <$> m.eval env)) := by
      rw [hBind]
      exact cpaPre_map_map_eq _ _ _ _ _ fun _ => rfl
    have hMid :=
      congrArg (Functor.map (Sum.inl : ((authCodec S).R.denote × (embedTy cpaStTy).denote) → OutT)) h.1
    have hR :
        ((Sum.inl : ((authCodec S).R.denote × (embedTy cpaStTy).denote) → OutT) <$>
          (embedVal (.prod authRespTy cpaStTy) <$> val)) =
        embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$> (Sum.inl <$> val) :=
      cpaPre_map_map_eq _ _ _ _ _ fun _ => rfl
    exact hL.trans (hMid.trans hR)
  · intro vOut s'₁ hMem
    simp only [armInl, Comp.eval, Expr.eval, Env.get, Expr.v0,
      mem_support_bind_iff, mem_support_pure_iff] at hMem
    rcases hMem with ⟨p, hp, hEq⟩
    injection hEq with hPair
    subst hPair
    exact h.2 (vOut, s'₁) hp
  · intro c_out p' s'₁ hMem
    simp only [armInl, Comp.eval, Expr.eval, Env.get, Expr.v0,
      mem_support_bind_iff, mem_support_pure_iff] at hMem
    rcases hMem with ⟨_, _, hEq⟩
    nomatch hEq

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4096 in
private theorem cpa_hPre_send (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (t : AuthQuery S)
    (x0 : sendQTy.denote) {Γ : List (Ty pqAtomicSig)} (ρ0 : Env Γ)
    (hOnPred : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t) (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthCpaInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let s0 := projVal cpaStTy s'.1
    let arm : Comp pqAtomicOps pqAuthPrimIface
        (AuthCoreK.authSendQAtomicTy :: authCpaShadowStTy :: Γ)
        (.sum (.prod (authCodec S).R authCpaShadowStTy) cpaPrePauseOutAtomicTy) :=
      .bind (AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun idx =>
           letV (.fst (.snd (v s))) fun ns =>
           letV (.snd (.snd (v s))) fun fhst =>
           bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
           caseSumV (v r)
             (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
             (fun p => .ret (.inr (.pair (.fst (v p))
               (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p)))))))))
          (.pair (.fst .v1) .v0))
        (.caseSum .v0
          (.bind (AuthCoreK.syncRoBothC F.K_cap
              (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
              (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
              (.snd .v3))
            (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
          (.ret (.inr (.pair (.fst .v0)
            (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))
    (forgetPreOut id forgetCpa <$> arm.eval (.cons (embedVal sendQTy x0) (.cons s' ρ0)) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$>
        ((fun out => match out with
          | .inl d => Sum.inl (d.1, (s0.1, d.2))
          | .inr p => Sum.inr (p.1, (p.2.1, (s0.1, p.2.2)))) <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S b.q_total opk true
            (Γ₁ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
            (Γ₂ := [.nat, authHybridStateFixedTy, sendQTy])
            (Γ₃ := [authHybridStateFixedTy, sendQTy])
            (Γ₄ := [sendQTy]) (Δ := [.nat, .nat, authHybridStateFixedTy, sendQTy])
            .zero .zero .zero .zero).eval
            (.cons s0.1 (.cons s0.2.1 (.cons s0.2.2 (.cons x0 .nil)))))) ∧
    (∀ vOut s'₁, .inl (vOut, s'₁) ∈ support (arm.eval (.cons (embedVal sendQTy x0) (.cons s' ρ0))) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s'₁) ∧
    (∀ c_out p' s'₁, .inr (c_out, p', s'₁) ∈ support (arm.eval (.cons (embedVal sendQTy x0) (.cons s' ρ0))) →
      AuthCpaPauseInv S b (bumpPred (authSimPred S) c t) p' s'₁) := by
  intro F s0 arm
  obtain ⟨_, hOnB, hRoB, hRtB, hLift1, _, _⟩ :=
    cpa_online_step_arith c t hInv.counter_inv hOnPred hNotRo hNotRt hroom
  have hProj : projVal sendQTy (embedVal sendQTy x0) = x0 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.projVal_embedVal sendQTy x0
  generalize embedVal sendQTy x0 = xA at hProj ⊢
  obtain ⟨hArmEq, hInlInv, hInrInv⟩ :=
    cpaSendPreArm_sim S b opk s' xA ρ0 hInv.shadow_ok hOnB hRoB hRtB
  dsimp only [arm] at hArmEq hInlInv hInrInv ⊢
  rw [hProj] at hArmEq
  refine ⟨hArmEq, fun vOut s'₁ hMem => hLift1 (hInlInv vOut s'₁ hMem), fun c_out p' s'₁ hMem => ?_⟩
  obtain ⟨hShEq, hPay⟩ := hInrInv c_out p' s'₁ hMem
  exact cpa_pauseInv_of_online hInv hShEq hOnPred hNotRo hNotRt hroom ⟨hPay.ro_eq, hPay.root_eq⟩

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
private theorem cpa_hPre (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authCpaShadowStTy.denote) (t : AuthQuery S)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthCpaInv S b c s') :
    forgetPreOut id forgetCpa <$>
        (aeadCpa1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (aeadCpaOldAtomicProg S b).handlePre.eval
        (.cons (forgetCpa s') (.cons ((authCodec S).qenc t) .nil)) ∧
    (∀ vOut s'₁,
      .inl (vOut, s'₁) ∈ support
        ((aeadCpa1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthCpaInv S b (bumpPred (authSimPred S) c t) s'₁) ∧
    (∀ c_out p' s'₁,
      .inr (c_out, p', s'₁) ∈ support
        ((aeadCpa1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthCpaPauseInv S b (bumpPred (authSimPred S) c t) p' s'₁) := by
  let F := AuthKindFuels.ofBudget S b
  let s0 := projVal cpaStTy s'.1
  let c' := bumpPred (authSimPred S) c t
  have hEmbedS : embedVal cpaStTy s0 = s'.1 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal cpaStTy s'.1
  have hRhs :
      (aeadCpaOldAtomicProg S b).handlePre.eval
        (.cons (forgetCpa s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$>
        cpaPreStepValEval S b.q_total s0 t := by
    change (Computational.Proofs.SignalPqxdh.AtomicLift.liftAuthHandle tlAuthPrim S
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPre1KeyC S b.q_total)).eval
        (.cons s'.1 (.cons ((authCodec S).qenc t) .nil)) = _
    rw [← hEmbedS,
      Computational.Proofs.SignalPqxdh.AtomicLift.liftAuthHandle_eval tlAuthPrim S
        tlAuthPrim_unsupported_zero
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPre1KeyC S b.q_total) s0 t,
      cpaPre1KeyC_eval_qenc S b.q_total s0 t]
  let wrapInl {a : Ty pqAtomicSig}
      (m : Comp pqAtomicOps pqAuthPrimIface
        [a, authCpaShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authCpaShadowStTy)) :
      Comp pqAtomicOps pqAuthPrimIface
        [a, authCpaShadowStTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R authCpaShadowStTy) cpaPrePauseOutAtomicTy) :=
    Comp.bind m (.ret (.inl .v0))
  let sendPreArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [AuthCoreK.authSendQAtomicTy, authCpaShadowStTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R authCpaShadowStTy) cpaPrePauseOutAtomicTy) :=
    .bind (AuthCoreKArms.liftAuthPrim1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun idx =>
         letV (.fst (.snd (v s))) fun ns =>
         letV (.snd (.snd (v s))) fun fhst =>
         bindV (AuthCoreKArms.cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
         caseSumV (v r)
           (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
           (fun p => .ret (.inr (.pair (.fst (v p))
             (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p)))))))))
        (.pair (.fst .v1) .v0))
      (.caseSum .v0
        (.bind (AuthCoreK.syncRoBothC F.K_cap
            (AuthCoreK.fixedRoCacheE (.snd (.snd (.snd .v0))))
            (AuthCoreK.fixedRootRoCacheE (.snd (.snd (.snd .v0))))
            (.snd .v3))
          (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
        (.ret (.inr (.pair (.fst .v0)
          (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))
  let roArm : Comp pqAtomicOps pqAuthPrimIface
      [PB 192, authCpaShadowStTy, (authCodec S).Q]
      (.prod (authCodec S).R authCpaShadowStTy) :=
    .bind (AuthCoreK.roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))
  let roRootArm : Comp pqAtomicOps pqAuthPrimIface
      [.prod (PB 32) (PB 32), authCpaShadowStTy, (authCodec S).Q]
      (.prod (authCodec S).R authCpaShadowStTy) :=
    .bind (AuthCoreK.roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (AuthCoreKArms.cpaRebuildE (.fst .v2) (.snd .v0))))
  have hLhs :
      (aeadCpa1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      dispatchAuthQByQuery (.cons s' (.cons ((authCodec S).qenc t) .nil)) t
        (wrapInl (AuthCoreKArms.cpaBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u)))
        (wrapInl (AuthCoreKArms.cpaBaseArmC S (fun fhst u => corruptFixedKB F fhst u)))
        (wrapInl (AuthCoreKArms.cpaBaseArmC S (fun fhst x => genSpkFixedKB F fhst x)))
        (wrapInl (AuthCoreKArms.cpaBaseArmC S (fun fhst x => genOpkFixedKB F fhst x)))
        (sendPreArm true) (sendPreArm false)
        (wrapInl (AuthCoreKArms.cpaRecvArmC S F true)) (wrapInl (AuthCoreKArms.cpaRecvArmC S F false))
        (wrapInl roArm) (wrapInl roRootArm)
        (.ret (.inl (.pair AuthCoreK.aNoneAtomicE .v1)))
        (wrapInl (AuthCoreKArms.cpaBaseArmC S (fun fhst sk => registerFixedKB fhst sk))) := by
    dsimp only [aeadCpa1KeyKindProg, AuthCoreKArms.cpaKindHandlePreC]
    exact (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ t rfl _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dispatchAuthQEval_eq_byQuery _ t _ _ _ _ _ _ _ _ _ _ _ _)
  let _ := hc
  rw [hRhs, hLhs]
  generalize (Env.cons ((authCodec S).qenc t) .nil : Env [(authCodec S).Q]) = ρ0
  cases t with
  | initPrin u =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.initPrin u) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.initPrinFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') u.val hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst u => initPrin1KeyFixedKB F fhst u)
      (fun fhst u => initPrin1KeyFixedB b.q_total fhst u)
      (by rfl) s' (embedVal .nat u.val) ρ0 hSh.1 hSh.2
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (initPrin1KeyFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
          (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) s' u.val),
      fun p hp => hLift2 (hArm.2 p hp)⟩
  | corruptIK u =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.corruptIK u) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.corruptFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') u.val hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst u => corruptFixedKB F fhst u)
      (fun fhst u => corruptFixedB b.q_total fhst u)
      (by rfl) s' (embedVal .nat u.val) ρ0 hSh.1 hSh.2
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (corruptFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
          (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) s' u.val),
      fun p hp => hLift2 (hArm.2 p hp)⟩
  | genSPK u j =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.genSPK u j) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.genSpkFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') (u.val, j.val) hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst x => genSpkFixedKB F fhst x)
      (fun fhst x => genSpkFixedB b.q_total fhst x)
      (by rfl) s' (embedVal (.prod .nat .nat) (u.val, j.val)) ρ0 hSh.1 hSh.2
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (genSpkFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
          (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) s' (u.val, j.val)),
      fun p hp => hLift2 (hArm.2 p hp)⟩
  | genOPK u j o =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    obtain ⟨_, hOnB, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.genOPK u j o) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hSh := AuthCoreKSimArmsFixed.genOpkFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') (u.val, (j.val, o.val)) hInv.shadow_ok hOnB
    have hArm := cpaBaseArmC_sim S b
      (fun fhst x => genOpkFixedKB F fhst x)
      (fun fhst x => genOpkFixedB b.q_total fhst x)
      (by rfl) s' (embedVal (.prod .nat (.prod .nat .nat)) (u.val, (j.val, o.val))) ρ0 hSh.1 hSh.2
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (genOpkFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
          (Γ₂ := [.prod .nat (.prod .nat .nat)])
          (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero)
        s' (u.val, (j.val, o.val))),
      fun p hp => hLift2 (hArm.2 p hp)⟩
  | sendOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, sendPreArm]
    exact cpa_hPre_send S b true c s' (.sendOPK u i bu m0 m1)
      (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1)))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv
  | sendNoOPK u i bu m0 m1 =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, sendPreArm]
    exact cpa_hPre_send S b false c s' (.sendNoOPK u i bu m0 m1)
      (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1)))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv
  | recvOPK k j o msg =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    exact cpaPre_wrapInl_bridge S _ _ _ (cpa_hPost_recv S b true c s' (.recvOPK k j o msg)
      (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv)
  | recvNoOPK k j l msg =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    exact cpaPre_wrapInl_bridge S _ _ _ (cpa_hPost_recv S b false c s' (.recvNoOPK k j l msg)
      (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg))) ρ0
      trivial (fun h => nomatch h) (fun h => nomatch h) hroom hInv)
  | roQuery sec =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl, roArm]
    obtain ⟨hRoOld, hRoCap, hLiftRo⟩ :=
      cpa_ro_step_arith c (.roQuery sec) hInv.counter_inv
        (fun h => nomatch h) trivial (fun h => nomatch h) hroom
    have hArm := cpaRoArm_sim S b s' sec ρ0 hInv.shadow_ok hRoOld hRoCap
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (roFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
          (Δ := [authHybridStateFixedTy, B 192]) .zero .zero) s' sec),
      support_imp rfl hArm.2 (fun _ h => hLiftRo h)⟩
  | roRootQuery rk dh =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl, roRootArm]
    obtain ⟨hRtOld, hRtCap, hLiftRt⟩ :=
      cpa_roRoot_step_arith c (.roRootQuery rk dh) hInv.counter_inv
        (fun h => nomatch h) (fun h => nomatch h) trivial hroom
    have hArm := cpaRoRootArm_sim S b s' (rk, dh) ρ0 hInv.shadow_ok hRtOld hRtCap
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (roRootFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
          (Γ₂ := [.prod (B 32) (B 32)])
          (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)]) .zero .zero) s' (rk, dh)),
      support_imp rfl hArm.2 (fun _ h => hLiftRt h)⟩
  | revealDhSecrets =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval]
    obtain ⟨_, _, _, _, _, _, hLift3⟩ :=
      cpa_online_step_arith c .revealDhSecrets hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    change forgetPreOut id forgetCpa <$>
        (pure (Sum.inl ((Sum.inl () : (authCodec S).R.denote), s')) :
          OracleComp _ (((authCodec S).R.denote × authCpaShadowStTy.denote) ⊕
            cpaPrePauseOutAtomicTy.denote)) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaPreTy <$>
        (Sum.inl <$> pure ((aNone (Γ := [])).eval .nil, s0)) ∧
      (∀ vOut s'₁,
        .inl (vOut, s'₁) ∈ support
          (pure (Sum.inl ((Sum.inl () : (authCodec S).R.denote), s')) :
            OracleComp _ (((authCodec S).R.denote × authCpaShadowStTy.denote) ⊕
              cpaPrePauseOutAtomicTy.denote)) →
        AuthCpaInv S b c' s'₁) ∧
      (∀ c_out p' s'₁,
        .inr (c_out, p' , s'₁) ∈ support
          (pure (Sum.inl ((Sum.inl () : (authCodec S).R.denote), s')) :
            OracleComp _ (((authCodec S).R.denote × authCpaShadowStTy.denote) ⊕
              cpaPrePauseOutAtomicTy.denote)) →
        AuthCpaPauseInv S b c' p' s'₁)
    refine ⟨?_, ?_, ?_⟩
    · erw [map_pure, map_pure]
      exact congrArg pure (congrArg Sum.inl (Prod.ext rfl hEmbedS.symm))
    · intro vOut s'₁ hp
      erw [mem_support_pure_iff] at hp
      injection hp with hPair
      injection hPair with _ hs1
      subst hs1
      exact hLift3 hInv.shadow_ok
    · intro c_out p' s'₁ hp
      erw [mem_support_pure_iff] at hp
      nomatch hp
  | registerKey sk =>
    dsimp only [dispatchAuthQByQuery, cpaPreStepValEval, cpaPostStepValEval, wrapInl]
    obtain ⟨_, _, _, _, _, hLift2, _⟩ :=
      cpa_online_step_arith c (.registerKey sk) hInv.counter_inv
        trivial (fun h => nomatch h) (fun h => nomatch h) hroom
    have hPres0 := AuthCoreKSimArmsFixed.registerFixedShadowB_sim
      tlAuthPrim (fun c => c) (fun _ _ y hy => ⟨y, hy, rfl⟩)
      S b (cpaShadowFixed s') sk hInv.shadow_ok
    have hArm := cpaBaseArmC_sim S b
      (fun fhst sk => registerFixedKB fhst sk)
      (fun fhst sk => registerFixedB fhst sk)
      (by rfl) s' (embedVal (B 32) sk) ρ0 rfl hPres0
    exact cpaPre_wrapInl_bridge S _ _ _
      ⟨hArm.1.trans (cpaNonSendRhs_bridge
        (registerFixedB
          (Γ₁ := [authHybridStateFixedTy, B 32]) (Γ₂ := [B 32])
          (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) s' sk),
      fun p hp => hLift2 (hArm.2 p hp)⟩

/-- Two-stage forgetful simulation between `aeadCpa1KeyKindProg` and `aeadCpaOldAtomicProg`. -/
theorem aeadCpa1KeyKindProg_twoStageForgetSim
    (S : Setup) (b : QueryBudget) (x : Ty.unit.denote) :
    TwoStageForgetSim (aeadCpa1KeyKindProg S b) (aeadCpaOldAtomicProg S b)
      id forgetCpa (authSimPred S) (authSimBounds b) x
      (AuthCpaInv S b) (AuthCpaPauseInv S b) where
  hInit := cpa_hInit S b x
  hPre := cpa_hPre S b
  hChDone := cpa_hChDone S b
  hResume := cpa_hResume S b
  hPost := cpa_hPost S b
  hFinish := cpa_hFinish S b

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpa
