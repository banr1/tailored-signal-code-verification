/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfInt
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfMk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac

/-!
# Forgetful Simulation for `Auth` Key-Schedule and HMAC PRF Reductions

Proves `ForgetSim` between the kind-split shadow-indexed reductions and their reference atomic
counterparts for the three one-stage `Auth` PRF hops (`PrfChainKey`, `PrfMsgKeys`, and `PrfHmac`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrf

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.ReductionDsl.StepSim
  (ForgetSim bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal projVal embedCtx embedEnv mapComp
   compRename compRename_eval
   comp_queries_zero_of_zero mapComp_eval liftAuthHandle_eval
   aiAuthPrim aiPrfMk aiPrfHmac tlAuthPrim tlPrfMk tlPrfHmac)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery authSpec)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface pqPrfMkIface pqPrfHmacIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B U32)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT v letV bindV caseOptV caseSumV findMV anyMV consumeFirstMV
   eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
   eval_letC bytesBeq bytesBeq_eval bytes2Eq kyberCheckE
   AllLeaves liftPrimComp eval_liftPrimComp samplePrim queryPrim
   authStateTy preKeyBundleTy sendQTy recvQTy
   asPrincipals asSpkBundles asOpkEntries asSessions asUsedSendSessions
   asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples asSentOPKEvents
   asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents asRoCache asRootRoCache asAdvKeys
   authHybridStateTy authHybridStateFixedTy
   findHonestC isAdvRegC isGameSpkC isGameOpkC
   koskBundleOkC koskSenderOkC resolveSigPkC hkdfRoC rootRoC
   checkBundleProvenanceExactC checkBundleSpkHonIdealC
   recvFinishTagTy recvFinishResTy preparedAuthRecvTy finishSendArgsTy
   recvFinishTagRunC prepareAuthHybridRecvC finishAuthHybridSendC)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (spkHonIdealFromPeerC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authBaseAtomicTy authFixedAtomicTy
   authBaseShadowStTy authFixedShadowStTy
   forgetAuthBaseShadow forgetAuthFixedShadow
   emptyRoBothAvlE syncFixedShadowRespC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv
   AuthBaseValOnlineBounded AuthBaseAtomOnlineBounded
   AuthFixedValOnlineBounded AuthFixedAtomOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache
   RoBothShadowRel CacheStepAtMostOne
   AuthFixedShadowAt AuthHmShadowAt
   ckShadowFixed mkShadowFixed hmShadowFixed
   forgetCk forgetMk forgetHm
   prfCkOldAtomicProg prfMkOldAtomicProg prfHmacOldAtomicProg
   AuthCkInv AuthMkInv AuthHmInv)

open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (authCkSendKB authCkRecvKB authMkSendPreKB authMkRecvPreKB
   intSendPrepKC hmSendKC hmSchedPrepKC hmSchedKC hmRecvTailKC hmRecvKC
   prfCk1KeyKindProg prfMsgKeys1KeyKindProg prfHmac1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
  (projEnv embedEnv_projEnv mapComp_eval_of_zero mapComp_congr_of_zero
   mem_support_mapComp_of_zero
   AllLeaves_mem_support liftPrimComp_eval_congr
   mem_support_liftPrimComp atomRoCache_embedVal atomRootRoCache_embedVal
   take_eq_of_le take_min_eq_of_le
   findHonestC_prf_fuel_eq isAdvRegC_fuel_eq isGameSpkC_fuel_eq isGameOpkC_prf_fuel_eq
   koskBundleOkC_fuel_eq koskSenderOkC_fuel_eq resolveSigPkC_fuel_eq
   checkBundleProvenanceExactC_fuel_eq checkBundleSpkHonIdealC_fuel_eq
   spkHonIdealFromPeerC_fuel_eq kyberCheckE_fuel_eq kyberCheckE_snd_len_le
   hkdfRoC_fuel_eq hkdfRoC_step rootRoC_fuel_eq rootRoC_step
   letV_congr letV_congr_eq letV_allLeaves letV_allLeaves_eq
   bindV_congr bindV_congr_leaves bindV_allLeaves_const bindV_allLeaves
   caseSumV_congr caseSumV_congr_eq caseSumV_allLeaves caseSumV_allLeaves_eq
   caseOptV_congr caseOptV_allLeaves caseOptV_allLeaves_eq
   ite_congr_eval ite_allLeaves consumeFirstML_allLeaves_len
   AuthHybridValOnlineBounded RecvTagValBounded PreparedRecvValBounded
   finishAuthHybridSendC_fuel_eq finishAuthHybridSendC_leaves
   recvFinishTagRunC_fuel_eq recvFinishTagRunC_leaves
   prepareAuthHybridRecvC_fuel_eq prepareAuthHybridRecvC_leaves)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm
  (letV_congr₂ bindV_congr₂ caseOptV_congr₂ ite_congr₂ ret_congr₂
   hkdfRoC_eval_congr rootRoC_eval_congr prepareAuthHybridRecvC_eval_congr
   recvFinishTagRunC_eval_congr finishAuthHybridSendC_eval_congr)

private theorem env_get_succ {sig} {t u : Ty sig} {Γ : List (Ty sig)}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (.succ v) = ρ.get v := rfl
private theorem env_get_zero {sig} {t : Ty sig} {Γ : List (Ty sig)}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get .zero = x := rfl

private theorem AuthFixedValOnlineBounded.toHybrid {n : ℕ} {fhst : authHybridStateFixedTy.denote}
    (hb : AuthFixedValOnlineBounded n fhst) : AuthHybridValOnlineBounded n fhst.1 :=
  ⟨hb.base_le, hb.initKemRecs_le, hb.recvKemRecs_le, hb.idealSessions_le⟩

private theorem finishAuthRecvCkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyMsgTy)
    (prep : Var Γ₂ preparedAuthRecvTy) [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ]
    (drKey : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
    (rk1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (rc' : Expr pqxdhOps Δ .nat) (p : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (env : Env Δ) (hPrep : PreparedRecvValBounded n ro0 root0 (env.get (h₂_ext.wk prep)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC S K₁
        msg prep drKey rk1 spqrSalt? rc' p).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC S K₂
        msg prep drKey rk1 spqrSalt? rc' p).eval env := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC
  iterate 8 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun fTag hfTag => ?_
  have hbTag : RecvTagValBounded n ro0 root0 fTag := by
    have : fTag = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.2 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTag
    rw [this]; exact hPrep.tag_bounded
  refine bindV_congr rfl fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  refine bindV_congr rfl fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  refine bindV_congr (recvFinishTagRunC_fuel_eq (ro0 := ro0) (root0 := root0) S _ rfl ?_ h₁ h₂)
    fun _ => rfl
  simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag

private theorem finishAuthRecvCkC_leaves (S : Setup) (K : ℕ) {n : ℕ}
    {ro0 : List (List UInt8 × _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyMsgTy)
    (prep : Var Γ₂ preparedAuthRecvTy) [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ]
    (drKey : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
    (rk1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (rc' : Expr pqxdhOps Δ .nat) (p : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (env : Env Δ) (hPrep : PreparedRecvValBounded n ro0 root0 (env.get (h₂_ext.wk prep))) :
    AllLeaves (fun res =>
      AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne ro0 (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne root0 (valRootRoCache res.2.1.1))
      ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC S K
        msg prep drKey rk1 spqrSalt? rc' p).eval env) := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC
  iterate 7 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hstEq => ?_
  refine letV_allLeaves_eq fun fTag hfTag => ?_
  have hstVal : st = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.1.1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parHstDec, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
  have hbTag : RecvTagValBounded n ro0 root0 fTag := by
    have : fTag = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.2 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTag
    rw [this]; exact hPrep.tag_bounded
  refine bindV_allLeaves_const fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun pt? => ?_
  refine letV_allLeaves_eq fun res? hResEq => ?_
  refine bindV_allLeaves (recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0) S K _ _ _ ?_ ?_)
    fun out ⟨hhOut, hRoOut, hRootOut⟩ => ?_
  · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
  · intro r hr
    have hResVal : res? = some r := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hr
    rw [hResVal] at hResEq
    cases pt? with
    | none => simp [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hResEq
    | some pt =>
      simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
        Option.some.injEq] at hResEq
      subst hResEq
      refine ⟨?_, ?_⟩
      · simpa [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hstVal] using
          (hPrep.ro_eq ▸ CacheStepAtMostOne.refl (valRoCache _))
      · simpa [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hstVal] using
          (hPrep.root_eq ▸ CacheStepAtMostOne.refl (valRootRoCache _))
  · exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
      hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut, hRootOut⟩

private theorem AllLeaves_of_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {m : OracleComp spec α} (h : ∀ y ∈ support m, P y) :
    AllLeaves P m := by
  induction m using OracleComp.inductionOn with
  | pure a => exact h a (by simp)
  | query_bind q k ih =>
    intro u
    exact ih u fun y hy => h y (by rw [mem_support_bind_iff]; refine ⟨u, ?_, hy⟩; simp; trivial)

private theorem hkdfRoC_allLeaves {K : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hRo : (valRoCache (env.get (h.wk st))).length ≤ K) :
    AllLeaves (fun p => CacheStepAtMostOne (valRoCache (env.get (h.wk st))) p.2)
      ((hkdfRoC K st sec).eval env) :=
  AllLeaves_of_mem_support (hkdfRoC_step st sec env hRo)

private theorem rootRoC_allLeaves {K : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hRoot : (valRootRoCache (env.get (h.wk st))).length ≤ K) :
    AllLeaves (fun p => CacheStepAtMostOne (valRootRoCache (env.get (h.wk st))) p.2)
      ((rootRoC K st rk dh).eval env) :=
  AllLeaves_of_mem_support (rootRoC_step st rk dh env hRoot)

set_option maxHeartbeats 600000 in
private theorem authCkSendB_leaves (S : Setup) (K : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃_ext : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₃_ext.wk fhst)))
    (hRoK : (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K)
    (hRootK : (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K) :
    AllLeaves (fun res =>
      AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₃_ext.wk fhst)).1.1) (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1) (valRootRoCache res.2.1.1))
      ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S K opk idx chalP fhst x).eval env) := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB
  refine letV_allLeaves_eq fun noneDone hNoneEq => ?_
  have hNone : AuthFixedValOnlineBounded (n + 1) noneDone.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₃_ext.wk fhst)).1.1) (valRoCache noneDone.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1) (valRootRoCache noneDone.2.1.1) := by
    have hnd : noneDone.2 = env.get (h₃_ext.wk fhst) := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
        congrArg Prod.snd hNoneEq
    rw [hnd]
    exact ⟨hb.mono (Nat.le_succ n), CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  refine letV_allLeaves_eq fun hst hhstEq => ?_
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hstEq => ?_
  have hhstVal : hst = (env.get (h₃_ext.wk fhst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
  have hstVal : st = (env.get (h₃_ext.wk fhst)).1.1 := by
    have h1 : st = hst.1 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
    exact h1.trans (congrArg Prod.fst hhstVal)
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  refine caseOptV_allLeaves (AllLeaves.pure hNone) fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  iterate 7 refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (AllLeaves.pure hNone) ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine caseOptV_allLeaves (AllLeaves.pure hNone) fun _ => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  iterate 3 refine bindV_allLeaves_const fun _ => ?_
  iterate 3 refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves ?_ ?_
  · iterate 3 refine bindV_allLeaves_const fun _ => ?_
    refine caseOptV_allLeaves (AllLeaves.pure hNone) fun _ => ?_
    iterate 3 refine letV_allLeaves fun _ => ?_
    refine bindV_allLeaves_const fun _ => ?_
    iterate 2 refine letV_allLeaves fun _ => ?_
    refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine bindV_allLeaves_const fun _ => ?_
    apply bindV_allLeaves
    · apply finishAuthHybridSendC_leaves (n := n)
      · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using
          AuthFixedValOnlineBounded.toHybrid hb
      · simpa [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hhstVal, hstVal] using CacheStepAtMostOne.refl _
      · simpa [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hhstVal, hstVal] using CacheStepAtMostOne.refl _
    · rintro out ⟨hhOut, hRoOut, hRootOut⟩
      have hRoOut' : CacheStepAtMostOne (valRoCache (env.get (h₃_ext.wk fhst)).1.1)
          (valRoCache out.2.1) := by
        simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using hRoOut
      have hRootOut' : CacheStepAtMostOne (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1)
          (valRootRoCache out.2.1) := by
        simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using hRootOut
      exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
        hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut', hRootOut'⟩
  · iterate 4 refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    apply bindV_allLeaves
    · apply hkdfRoC_allLeaves
      simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal] using hRoK
    rintro drOut hRoStep
    refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun roC' hRoCEq => ?_
    have hRoCVal : roC' = drOut.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoCEq
    refine bindV_allLeaves_const fun _ => ?_
    apply bindV_allLeaves
    · apply rootRoC_allLeaves
      simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal] using hRootK
    rintro rkOut hRootStep
    iterate 2 refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun rootC' hRootCEq => ?_
    have hRootCVal : rootC' = rkOut.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRootCEq
    iterate 3 refine bindV_allLeaves_const fun _ => ?_
    refine caseOptV_allLeaves (AllLeaves.pure hNone) fun _ => ?_
    iterate 2 refine letV_allLeaves fun _ => ?_
    refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine bindV_allLeaves_const fun _ => ?_
    apply bindV_allLeaves
    · apply finishAuthHybridSendC_leaves (n := n)
      · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using
          AuthFixedValOnlineBounded.toHybrid hb
      · have hRoStep' : CacheStepAtMostOne (valRoCache (env.get (h₃_ext.wk fhst)).1.1) drOut.2 := by
          simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal] using hRoStep
        simpa [valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hhstVal, hRoCVal] using hRoStep'
      · have hRootStep' : CacheStepAtMostOne (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1) rkOut.2 := by
          simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal] using hRootStep
        simpa [valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hhstVal, hRootCVal] using hRootStep'
    · rintro out ⟨hhOut, hRoOut, hRootOut⟩
      have hRoOut' : CacheStepAtMostOne (valRoCache (env.get (h₃_ext.wk fhst)).1.1)
          (valRoCache out.2.1) := by
        simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using hRoOut
      have hRootOut' : CacheStepAtMostOne (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1)
          (valRootRoCache out.2.1) := by
        simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using hRootOut
      exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
        hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut', hRootOut'⟩

set_option maxHeartbeats 600000 in

private theorem authCkRecvB_leaves (S : Setup) (K : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃_ext : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₃_ext.wk fhst)))
    (hRoK : (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K)
    (hRootK : (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K) :
    AllLeaves (fun res =>
      AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₃_ext.wk fhst)).1.1) (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1) (valRootRoCache res.2.1.1))
      ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB S K opk idx chalP fhst x).eval env) := by
  let ro0 := valRoCache (env.get (h₃_ext.wk fhst)).1.1
  let root0 := valRootRoCache (env.get (h₃_ext.wk fhst)).1.1
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB
  refine letV_allLeaves_eq fun hst hhstEq => ?_
  have hhstVal : hst = (env.get (h₃_ext.wk fhst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves (prepareAuthHybridRecvC_leaves (n := n) S K opk _ _ _ ?_) fun prep? hPrepOpt => ?_
  · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using
      AuthFixedValOnlineBounded.toHybrid hb
  refine caseOptV_allLeaves_eq ?_ (fun prep hSome => ?_)
  · have hb1 := hb.mono (Nat.le_succ n)
    exact AllLeaves.pure ⟨⟨hb1.base_le, hb1.initKemRecs_le, hb1.recvKemRecs_le,
      hb1.idealSessions_le, hb1.mkSaltCache_le⟩, CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
  · have hPrep : PreparedRecvValBounded n ro0 root0 prep := by
      have hp : prep? = some prep := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hSome
      rw [hp] at hPrepOpt
      simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using hPrepOpt prep rfl
    refine letV_allLeaves_eq fun st hstEq => ?_
    refine letV_allLeaves_eq fun fTag hfTagEq => ?_
    have hstVal : st = prep.2.2.2.2.2.2.2.2.1.1 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parHstDec, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
    have hbTag : RecvTagValBounded n ro0 root0 fTag := by
      have : fTag = prep.2.2.2.2.2.2.2.2.2 := by
        simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag, v, Expr.eval,
          Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTagEq
      rw [this]; exact hPrep.tag_bounded
    refine letV_allLeaves fun _ => ?_
    refine ite_allLeaves ?_ ?_
    · refine caseOptV_allLeaves ?_ (fun _ => ?_)
      · iterate 3 refine bindV_allLeaves_const fun _ => ?_
        refine caseOptV_allLeaves ?_ (fun _ => ?_)
        · refine bindV_allLeaves (recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0)
            S K _ _ _ (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag)
            (fun r hr => by simp [Expr.eval] at hr)) fun out ⟨hhOut, hRoOut, hRootOut⟩ => ?_
          exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
            hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut, hRootOut⟩
        · refine letV_allLeaves fun _ => ?_
          refine bindV_allLeaves_const fun _ => ?_
          refine bindV_allLeaves (finishAuthRecvCkC_leaves (n := n) (ro0 := ro0) (root0 := root0)
            S K _ _ _ _ _ _ _ _
            (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hPrep))
            fun res ⟨hbRes, hRoRes, hRootRes⟩ => ?_
          exact AllLeaves.pure ⟨⟨hbRes.base_le, hbRes.initKemRecs_le, hbRes.recvKemRecs_le,
            hbRes.idealSessions_le, hbRes.mkSaltCache_le⟩, hRoRes, hRootRes⟩
      · refine ite_allLeaves ?_ ?_
        · refine bindV_allLeaves_const fun _ => ?_
          refine caseOptV_allLeaves ?_ (fun _ => ?_)
          · refine bindV_allLeaves (recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0)
              S K _ _ _ (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag)
              (fun r hr => by simp [Expr.eval] at hr)) fun out ⟨hhOut, hRoOut, hRootOut⟩ => ?_
            exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
              hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut, hRootOut⟩
          · refine bindV_allLeaves (finishAuthRecvCkC_leaves (n := n) (ro0 := ro0) (root0 := root0)
              S K _ _ _ _ _ _ _ _
              (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hPrep))
              fun res ⟨hbRes, hRoRes, hRootRes⟩ => ?_
            exact AllLeaves.pure ⟨⟨hbRes.base_le, hbRes.initKemRecs_le, hbRes.recvKemRecs_le,
              hbRes.idealSessions_le, hbRes.mkSaltCache_le⟩, hRoRes, hRootRes⟩
        · iterate 2 refine bindV_allLeaves_const fun _ => ?_
          refine caseOptV_allLeaves ?_ (fun _ => ?_)
          · refine bindV_allLeaves (recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0)
              S K _ _ _ (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag)
              (fun r hr => by simp [Expr.eval] at hr)) fun out ⟨hhOut, hRoOut, hRootOut⟩ => ?_
            exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
              hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut, hRootOut⟩
          · refine letV_allLeaves fun _ => ?_
            refine bindV_allLeaves_const fun _ => ?_
            refine bindV_allLeaves (finishAuthRecvCkC_leaves (n := n) (ro0 := ro0) (root0 := root0)
              S K _ _ _ _ _ _ _ _
              (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hPrep))
              fun res ⟨hbRes, hRoRes, hRootRes⟩ => ?_
            exact AllLeaves.pure ⟨⟨hbRes.base_le, hbRes.initKemRecs_le, hbRes.recvKemRecs_le,
              hbRes.idealSessions_le, hbRes.mkSaltCache_le⟩, hRoRes, hRootRes⟩
    · refine bindV_allLeaves (hkdfRoC_allLeaves _ _ _ ?_) fun drOut hRoStep => ?_
      · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal, hPrep.ro_eq] using hRoK
      refine letV_allLeaves fun _ => ?_
      refine letV_allLeaves_eq fun roC' hRoCEq => ?_
      have hRoCVal : roC' = drOut.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoCEq
      refine bindV_allLeaves (rootRoC_allLeaves _ _ _ _ ?_) fun rkOut hRootStep => ?_
      · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal, hPrep.root_eq] using hRootK
      iterate 2 refine letV_allLeaves fun _ => ?_
      refine letV_allLeaves_eq fun rootC' hRootCEq => ?_
      have hRootCVal : rootC' = rkOut.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRootCEq
      iterate 3 refine bindV_allLeaves_const fun _ => ?_
      refine caseOptV_allLeaves ?_ (fun _ => ?_)
      · refine bindV_allLeaves (recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0)
          S K _ _ _ (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag)
          (fun r hr => by simp [Expr.eval] at hr)) fun out ⟨hhOut, hRoOut, hRootOut⟩ => ?_
        exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
          hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut, hRootOut⟩
      · refine bindV_allLeaves_const fun _ => ?_
        refine letV_allLeaves fun _ => ?_
        refine bindV_allLeaves_const fun pt? => ?_
        refine letV_allLeaves_eq fun res? hResEq => ?_
        refine bindV_allLeaves (recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0)
          S K _ _ _ (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag) ?_)
          fun out ⟨hhOut, hRoOut, hRootOut⟩ => ?_
        · intro r hr
          have hResVal : res? = some r := by
            simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hr
          rw [hResVal] at hResEq
          cases pt? with
          | none => simp [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hResEq
          | some pt =>
            simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
              Option.some.injEq] at hResEq
            subst hResEq
            refine ⟨?_, ?_⟩
            · rw [← hPrep.ro_eq]
              simpa [valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
                env_get_succ, env_get_zero, hstVal, hRoCVal] using hRoStep
            · rw [← hPrep.root_eq]
              simpa [valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
                env_get_succ, env_get_zero, hstVal, hRootCVal] using hRootStep
        · exact AllLeaves.pure ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le,
            hhOut.idealSessions_le, by simp [Expr.eval]⟩, hRoOut, hRootOut⟩

set_option maxHeartbeats 600000 in
private theorem authCkSendKB_fuel_eq (S : Setup) {K_on K_ro K n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃_ext : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₃_ext.wk fhst)))
    (hOn : n ≤ K_on) (hOld : n ≤ K)
    (hRoK : (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K_ro)
    (hRoOld : (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K)
    (hRootK : (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K_ro)
    (hRootOld : (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K) :
    (authCkSendKB S K_on K_ro opk idx chalP fhst x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S K opk idx chalP fhst x).eval env := by
  unfold authCkSendKB
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase.authCkSendKB
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB
  refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine letV_congr_eq rfl fun hst hhstEq => ?_
  refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun st hstEq => ?_
  have hhstVal : hst = (env.get (h₃_ext.wk fhst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
  have hstVal : st = (env.get (h₃_ext.wk fhst)).1.1 := by
    have h1 : st = hst.1 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
    exact h1.trans (congrArg Prod.fst hhstVal)
  have hbBase : AuthBaseValOnlineBounded n st := hstVal ▸ hb.base_le
  refine ite_congr_eval rfl rfl ?_
  iterate 4 refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine ite_congr_eval ?_ rfl ?_
  · dsimp only [eAny, Expr.eval]
    rw [take_eq_of_le (K₁ := K_on) (K₂ := K)]
    · simpa [asUsedSendSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero] using Nat.le_trans hbBase.usedSendSessions_le hOn
    · simpa [asUsedSendSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero] using Nat.le_trans hbBase.usedSendSessions_le hOld
  refine caseOptV_congr ?_ rfl fun _ => ?_
  · dsimp only [eFind, Expr.eval]
    rw [take_eq_of_le (K₁ := K_on) (K₂ := K)]
    · simpa [asPrincipals, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero] using Nat.le_trans hbBase.principals_le hOn
    · simpa [asPrincipals, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero] using Nat.le_trans hbBase.principals_le hOld
  refine letV_congr rfl fun _ => ?_
  apply bindV_congr
  · apply findHonestC_prf_fuel_eq (n := n)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbBase
    · exact hOn
    · exact hOld
  intro pp
  refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine letV_congr rfl fun _ => ?_
  apply bindV_congr
  · apply koskBundleOkC_fuel_eq (n := n)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbBase
    · exact hOn
    · exact hOld
  intro _
  refine ite_congr_eval rfl rfl ?_
  iterate 4 refine bindV_congr rfl fun _ => ?_
  apply bindV_congr
  · apply resolveSigPkC_fuel_eq (n := n)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbBase
    · exact hOn
    · exact hOld
  intro _
  iterate 2 refine bindV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine bindV_congr rfl fun _ => ?_
  refine caseOptV_congr rfl rfl fun _ => ?_
  iterate 2 refine letV_congr rfl fun _ => ?_
  iterate 2 refine bindV_congr rfl fun _ => ?_
  apply bindV_congr
  · apply checkBundleSpkHonIdealC_fuel_eq (n := n)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbBase
    · exact hOn
    · exact hOld
  intro _
  refine letV_congr ?_ fun _ => ?_
  · cases pp with
    | none => simp [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    | some p =>
      simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      have hLen := hbBase.spkBundles_le
      simp [eAny, asSpkBundles, Expr.eval,
        take_eq_of_le (Nat.le_trans hLen hOn) (Nat.le_trans hLen hOld)]
  iterate 2 refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl ?_ ?_
  · iterate 3 refine bindV_congr rfl fun _ => ?_
    refine caseOptV_congr rfl rfl fun _ => ?_
    iterate 3 refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    iterate 2 refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    apply bindV_congr
    · apply finishAuthHybridSendC_fuel_eq (n := n)
      · rfl
      · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using
          AuthFixedValOnlineBounded.toHybrid hb
      · exact hOn
      · exact hOld
    · intro _; rfl
  · iterate 4 refine bindV_congr rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    apply bindV_congr
    · apply hkdfRoC_fuel_eq (nRo := (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length)
      · simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal, le_rfl]
      · exact hRoK
      · exact hRoOld
    intro _
    iterate 2 refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    apply bindV_congr
    · apply rootRoC_fuel_eq (nRoot := (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length)
      · simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal, le_rfl]
      · exact hRootK
      · exact hRootOld
    intro _
    iterate 3 refine letV_congr rfl fun _ => ?_
    iterate 3 refine bindV_congr rfl fun _ => ?_
    refine caseOptV_congr rfl rfl fun _ => ?_
    iterate 2 refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    apply bindV_congr
    · apply finishAuthHybridSendC_fuel_eq (n := n)
      · rfl
      · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using
          AuthFixedValOnlineBounded.toHybrid hb
      · exact hOn
      · exact hOld
    · intro _; rfl

private theorem caseOptV_congr_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {o₁ o₂ : Expr pqxdhOps Γ (.opt τ₁)} {kn₁ kn₂ : Comp pqxdhOps I Γ τ₂}
    {ks₁ ks₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (ho : o₁.eval env = o₂.eval env) (hkn : kn₁.eval env = kn₂.eval env)
    (hks : ∀ x : τ₁.denote, o₁.eval env = some x →
      (ks₁ .zero).eval (.cons x env) = (ks₂ .zero).eval (.cons x env)) :
    (caseOptV o₁ kn₁ ks₁).eval env = (caseOptV o₂ kn₂ ks₂).eval env := by
  simp only [caseOptV, Comp.eval, ← ho]
  cases h : o₁.eval env with
  | none => exact hkn
  | some x => exact hks x h

set_option maxHeartbeats 600000 in
private theorem authCkRecvKB_fuel_eq (S : Setup) {K_on K_ro K n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃_ext : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₃_ext.wk fhst)))
    (hOn : n ≤ K_on) (hOld : n ≤ K)
    (hRoK : (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K_ro)
    (hRoOld : (valRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K)
    (hRootK : (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K_ro)
    (hRootOld : (valRootRoCache (env.get (h₃_ext.wk fhst)).1.1).length ≤ K) :
    (authCkRecvKB S K_on K_ro opk idx chalP fhst x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB S K opk idx chalP fhst x).eval env := by
  let ro0 := valRoCache (env.get (h₃_ext.wk fhst)).1.1
  let root0 := valRootRoCache (env.get (h₃_ext.wk fhst)).1.1
  unfold authCkRecvKB
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase.authCkRecvKB
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB
  refine letV_congr_eq rfl fun hst hhstEq => ?_
  have hhstVal : hst = (env.get (h₃_ext.wk fhst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
  iterate 4 refine letV_congr rfl fun _ => ?_
  have hhstB : AuthHybridValOnlineBounded n hst := hhstVal ▸ AuthFixedValOnlineBounded.toHybrid hb
  apply bindV_congr_leaves
  · apply prepareAuthHybridRecvC_fuel_eq (n := n)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstB
    · exact hOn
    · exact hOld
  · apply prepareAuthHybridRecvC_leaves (n := n)
    simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstB
  intro prep? hPrepOpt
  refine caseOptV_congr_eq rfl rfl ?_
  · intro prep hSome
    have hPrep : PreparedRecvValBounded n ro0 root0 prep := by
      have hp : prep? = some prep := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hSome
      rw [hp] at hPrepOpt
      simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal] using hPrepOpt prep rfl
    refine letV_congr_eq rfl fun st hstEq => ?_
    refine letV_congr_eq rfl fun fTag hfTagEq => ?_
    have hstVal : st = prep.2.2.2.2.2.2.2.2.1.1 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parHstDec, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
    have hbTag : RecvTagValBounded n ro0 root0 fTag := by
      have : fTag = prep.2.2.2.2.2.2.2.2.2 := by
        simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag, v, Expr.eval,
          Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTagEq
      rw [this]; exact hPrep.tag_bounded
    refine letV_congr rfl fun _ => ?_
    refine ite_congr_eval rfl ?_ ?_
    · refine caseOptV_congr rfl ?_ fun _ => ?_
      · iterate 3 refine bindV_congr rfl fun _ => ?_
        refine caseOptV_congr rfl ?_ fun _ => ?_
        · apply bindV_congr
          · apply recvFinishTagRunC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
            · rfl
            · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
            · exact hOn
            · exact hOld
          · intro _; rfl
        · refine letV_congr rfl fun _ => ?_
          refine bindV_congr rfl fun _ => ?_
          apply bindV_congr
          · apply finishAuthRecvCkC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
            · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hPrep
            · exact hOn
            · exact hOld
          · intro _; rfl
      · refine ite_congr_eval rfl ?_ ?_
        · refine bindV_congr rfl fun _ => ?_
          refine caseOptV_congr rfl ?_ fun _ => ?_
          · apply bindV_congr
            · apply recvFinishTagRunC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
              · rfl
              · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
              · exact hOn
              · exact hOld
            · intro _; rfl
          · apply bindV_congr
            · apply finishAuthRecvCkC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
              · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hPrep
              · exact hOn
              · exact hOld
            · intro _; rfl
        · iterate 2 refine bindV_congr rfl fun _ => ?_
          refine caseOptV_congr rfl ?_ fun _ => ?_
          · apply bindV_congr
            · apply recvFinishTagRunC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
              · rfl
              · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
              · exact hOn
              · exact hOld
            · intro _; rfl
          · refine letV_congr rfl fun _ => ?_
            refine bindV_congr rfl fun _ => ?_
            apply bindV_congr
            · apply finishAuthRecvCkC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
              · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hPrep
              · exact hOn
              · exact hOld
            · intro _; rfl
    · apply bindV_congr
      · apply hkdfRoC_fuel_eq (nRo := ro0.length)
        · simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal, hPrep.ro_eq, le_rfl]
        · exact hRoK
        · exact hRoOld
      intro _
      iterate 2 refine letV_congr rfl fun _ => ?_
      apply bindV_congr
      · apply rootRoC_fuel_eq (nRoot := root0.length)
        · simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal, hPrep.root_eq, le_rfl]
        · exact hRootK
        · exact hRootOld
      intro _
      iterate 3 refine letV_congr rfl fun _ => ?_
      iterate 3 refine bindV_congr rfl fun _ => ?_
      refine caseOptV_congr rfl ?_ fun _ => ?_
      · apply bindV_congr
        · apply recvFinishTagRunC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
          · rfl
          · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
          · exact hOn
          · exact hOld
        · intro _; rfl
      · refine bindV_congr rfl fun _ => ?_
        refine letV_congr rfl fun _ => ?_
        refine bindV_congr rfl fun _ => ?_
        refine letV_congr rfl fun _ => ?_
        apply bindV_congr
        · apply recvFinishTagRunC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
          · rfl
          · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
          · exact hOn
          · exact hOld
        · intro _; rfl

private def ren2 {Δ : List PT} {A B : PT} (vA : Var Δ A) (vB : Var Δ B) :
    ∀ {t}, Var [A, B] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB

private def ren4 {Δ : List PT} {A B C D : PT}
    (vA : Var Δ A) (vB : Var Δ B) (vC : Var Δ C) (vD : Var Δ D) :
    ∀ {t}, Var [A, B, C, D] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB
  | _, .succ (.succ .zero) => vC
  | _, .succ (.succ (.succ .zero)) => vD

set_option maxRecDepth 4096 in
private theorem authCkSendB_eval_ren4 (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
    (env : Env Δ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S K opk idx chalP fhst x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S K opk
        (Γ₁ := [.nat, .prod (B 32) (B 32), authHybridStateFixedTy, sendQTy])
        (Γ₂ := [.prod (B 32) (B 32), authHybridStateFixedTy, sendQTy])
        (Γ₃ := [authHybridStateFixedTy, sendQTy])
        (Γ₄ := [sendQTy]) .zero .zero .zero .zero).eval
        (.cons (env.get (h₁.wk idx)) (.cons (env.get (h₂.wk chalP))
          (.cons (env.get (h₃.wk fhst)) (.cons (env.get (h₄.wk x)) .nil)))) := by
  have hren :
      compRename (ren4 (h₁.wk idx) (h₂.wk chalP) (h₃.wk fhst) (h₄.wk x))
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S K opk
          (Γ₁ := [.nat, .prod (B 32) (B 32), authHybridStateFixedTy, sendQTy])
          (Γ₂ := [.prod (B 32) (B 32), authHybridStateFixedTy, sendQTy])
          (Γ₃ := [authHybridStateFixedTy, sendQTy])
          (Γ₄ := [sendQTy]) .zero .zero .zero .zero) =
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S K opk idx chalP fhst x := by
    cases opk <;> rfl
  rw [← hren]
  refine compRename_eval _ _ _ _ ?_
  intro a v
  cases v with
  | zero => rfl
  | succ v => cases v with
    | zero => rfl
    | succ v => cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => nomatch v

private theorem queryPrim_congr₂ {Δ₁ Δ₂ : List PT}
    (t : _root_.SignalPqxdh.LegacyCosted.PTag)
    {e₁ : Expr pqxdhOps Δ₁ t.dom} {e₂ : Expr pqxdhOps Δ₂ t.dom}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂} (he : e₁.eval env₁ = e₂.eval env₂) :
    (queryPrim t e₁).eval env₁ = (queryPrim t e₂).eval env₂ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queryPrim_eval, he]

private theorem sampAtCkC_congr₂ {Δ₁ Δ₂ : List PT}
    {idx₁ : Expr pqxdhOps Δ₁ .nat} {idx₂ : Expr pqxdhOps Δ₂ .nat}
    {chal₁ : Expr pqxdhOps Δ₁ (.prod (B 32) (B 32))}
    {chal₂ : Expr pqxdhOps Δ₂ (.prod (B 32) (B 32))}
    {s₁ : Expr pqxdhOps Δ₁ .nat} {s₂ : Expr pqxdhOps Δ₂ .nat}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hi : idx₁.eval env₁ = idx₂.eval env₂) (hc : chal₁.eval env₁ = chal₂.eval env₂)
    (hs : s₁.eval env₁ = s₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sampAtCkC idx₁ chal₁ s₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sampAtCkC idx₂ chal₂ s₂).eval env₂ := by
  rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sampAtCkC_eval,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sampAtCkC_eval, hi, hc, hs]

private theorem allocRecvSlotE_eval_congr {Δ₁ Δ₂ : List PT}
    {ss₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authSlotStateTy}
    {rc₁ : Expr pqxdhOps Δ₁ .nat} {env₁ : Env Δ₁}
    {ss₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authSlotStateTy}
    {rc₂ : Expr pqxdhOps Δ₂ .nat} {env₂ : Env Δ₂}
    (hss : ss₁.eval env₁ = ss₂.eval env₂) (hrc : rc₁.eval env₁ = rc₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allocRecvSlotE ss₁ rc₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allocRecvSlotE ss₂ rc₂).eval env₂ := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allocRecvSlotE, eLet2, eLet,
    eCaseOpt, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assRecv,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assNext,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assMk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assSendOpk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assSendNoOpk,
    Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, hss, hrc]
  rfl

local macro "env_eq" : tactic =>
  `(tactic| (simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parHstDec,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parMatchedSess?,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parIsUncorrSender,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parSameEph,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parSecrets,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parDhRatchet,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parKEntry,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.iasDrKey,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.iasRk1,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.iasMkSeed,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.iasCk1_1,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkmPqRatchetMsg,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkmAeadCt,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkmEphAPk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkmHdr,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.hdrIkAPk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.peIkAPk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.boolOr,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.isSomeE,
    eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, *]; try rfl))

local macro "ret_slots_eq" : tactic =>
  `(tactic| (
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfUpdSlots,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSlots,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfRecvCount,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSaltCache,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]))

set_option linter.unusedSimpArgs false in
private theorem finishAuthRecvCkC_eval_congr (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    {msg₁ : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyMsgTy}
    {prep₁ : Var Γ₂ preparedAuthRecvTy}
    {dr₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy}
    {rk₁ : Expr pqxdhOps Δ₁ (B 32)} {sp₁ : Expr pqxdhOps Δ₁ (.opt (B 32))}
    {rc₁ : Expr pqxdhOps Δ₁ .nat} {p₁ : Expr pqxdhOps Δ₁ (.prod (B 32) (B 32))}
    [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] {env₁ : Env Δ₁}
    {msg₂ : Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyMsgTy}
    {prep₂ : Var Γ₄ preparedAuthRecvTy}
    {dr₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy}
    {rk₂ : Expr pqxdhOps Δ₂ (B 32)} {sp₂ : Expr pqxdhOps Δ₂ (.opt (B 32))}
    {rc₂ : Expr pqxdhOps Δ₂ .nat} {p₂ : Expr pqxdhOps Δ₂ (.prod (B 32) (B 32))}
    [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] {env₂ : Env Δ₂}
    (hmsg : env₁.get (h₁.wk msg₁) = env₂.get (h₃.wk msg₂))
    (hprep : env₁.get (h₂.wk prep₁) = env₂.get (h₄.wk prep₂))
    (hdr : dr₁.eval env₁ = dr₂.eval env₂) (hrk : rk₁.eval env₁ = rk₂.eval env₂)
    (hsp : sp₁.eval env₁ = sp₂.eval env₂) (hrc : rc₁.eval env₁ = rc₂.eval env₂)
    (hp : p₁.eval env₁ = p₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC S K
      msg₁ prep₁ dr₁ rk₁ sp₁ rc₁ p₁).eval env₁ =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC S K
      msg₂ prep₂ dr₂ rk₂ sp₂ rc₂ p₂).eval env₂ := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvCkC
  refine letV_congr₂ (by simp only [Expr.eval, hdr, hrk, hsp, hrc, hp]) fun _ => ?_
  iterate 8 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
  refine letV_congr₂ (by
    rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.firstMsgADE_eval,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.firstMsgADE_eval]; env_eq) fun _ => ?_
  refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
  refine letV_congr₂ (by
    dsimp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, asRoCache, asRootRoCache]
    simp only [env_get_succ, env_get_zero]) fun _ => ?_
  refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
  exact recvFinishTagRunC_eval_congr S K _ _ _ _ _ _ (by env_eq) (by env_eq)

set_option linter.unusedSimpArgs false in
private theorem authCkRecvB_eval_congr (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ₁ Γ₅ Γ₆ Γ₇ Γ₈ Δ₂ : List PT}
    (idx₁ : Var Γ₁ .nat) (chal₁ : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst₁ : Var Γ₃ authHybridStateFixedTy) (x₁ : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] [h₃ : Ext Γ₃ Δ₁] [h₄ : Ext Γ₄ Δ₁] (env₁ : Env Δ₁)
    (idx₂ : Var Γ₅ .nat) (chal₂ : Var Γ₆ (.prod (B 32) (B 32)))
    (fhst₂ : Var Γ₇ authHybridStateFixedTy) (x₂ : Var Γ₈ recvQTy)
    [h₅ : Ext Γ₅ Δ₂] [h₆ : Ext Γ₆ Δ₂] [h₇ : Ext Γ₇ Δ₂] [h₈ : Ext Γ₈ Δ₂] (env₂ : Env Δ₂)
    (hidx : env₁.get (h₁.wk idx₁) = env₂.get (h₅.wk idx₂))
    (hchal : env₁.get (h₂.wk chal₁) = env₂.get (h₆.wk chal₂))
    (hfhst : env₁.get (h₃.wk fhst₁) = env₂.get (h₇.wk fhst₂))
    (hx : env₁.get (h₄.wk x₁) = env₂.get (h₈.wk x₂)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB S K opk
      idx₁ chal₁ fhst₁ x₁).eval env₁ =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB S K opk
      idx₂ chal₂ fhst₂ x₂).eval env₂ := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB
  refine letV_congr₂ (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid]; env_eq) fun _ => ?_
  refine letV_congr₂ (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfRecvCount]; env_eq) fun _ => ?_
  refine letV_congr₂ (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfSlots]; env_eq) fun _ => ?_
  iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine (bindV_congr₂ ?_ fun _ => ?_)
  · exact prepareAuthHybridRecvC_eval_congr S K opk _ _ _ _ _ _ (by env_eq) (by env_eq)
  · refine caseOptV_congr₂ (by env_eq)
      (ret_congr₂ (by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfUpd,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSlots,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSaltCache,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfSlots,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero, hfhst])) fun _ => ?_
    iterate 3 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine ite_congr₂ (by env_eq) ?_ ?_
    · refine caseOptV_congr₂ (by env_eq) ?_ fun _ => ?_
      · refine bindV_congr₂ (by rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.samplePrim_drKey96_eval,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.samplePrim_drKey96_eval]) fun _ => ?_
        refine bindV_congr₂ (by rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.samplePrim_bytes32_eval,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.samplePrim_bytes32_eval]) fun _ => ?_
        refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
        refine caseOptV_congr₂ (by env_eq) ?_ fun _ => ?_
        · refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
          exact recvFinishTagRunC_eval_congr S K _ _ _ _ _ _ (by env_eq) rfl
        · refine letV_congr₂ (allocRecvSlotE_eval_congr (by env_eq) (by env_eq)) fun _ => ?_
          refine bindV_congr₂ (sampAtCkC_congr₂ (by env_eq) (by env_eq) (by env_eq)) fun _ => ?_
          refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
          exact finishAuthRecvCkC_eval_congr S K (by env_eq) (by env_eq) (by env_eq) (by env_eq)
            (by env_eq) (by env_eq) (by env_eq)
      · refine ite_congr₂ (by env_eq) ?_ ?_
        · refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
          refine caseOptV_congr₂ (by env_eq) ?_ fun _ => ?_
          · refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
            exact recvFinishTagRunC_eval_congr S K _ _ _ _ _ _ (by env_eq) rfl
          · refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
            exact finishAuthRecvCkC_eval_congr S K (by env_eq) (by env_eq) (by env_eq) (by env_eq)
              (by env_eq) (by env_eq) (by env_eq)
        · refine bindV_congr₂ (by rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.samplePrim_bytes32_eval,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.samplePrim_bytes32_eval]) fun _ => ?_
          refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
          refine caseOptV_congr₂ (by env_eq) ?_ fun _ => ?_
          · refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
            exact recvFinishTagRunC_eval_congr S K _ _ _ _ _ _ (by env_eq) rfl
          · refine letV_congr₂ (allocRecvSlotE_eval_congr (by env_eq) (by env_eq)) fun _ => ?_
            refine bindV_congr₂ (sampAtCkC_congr₂ (by env_eq) (by env_eq) (by env_eq)) fun _ => ?_
            refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
            exact finishAuthRecvCkC_eval_congr S K (by env_eq) (by env_eq) (by env_eq) (by env_eq)
              (by env_eq) (by env_eq) (by env_eq)
    · refine (bindV_congr₂ ?_ fun _ => ?_)
      · exact hkdfRoC_eval_congr K _ _ _ _ _ _ (by env_eq) (by env_eq)
      · iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
        refine (bindV_congr₂ ?_ fun _ => ?_)
        · exact rootRoC_eval_congr K _ _ _ _ _ _ _ _ (by env_eq) (by env_eq) (by env_eq)
        · iterate 3 refine letV_congr₂ (by env_eq) fun _ => ?_
          iterate 3 refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
          refine caseOptV_congr₂ (by env_eq) ?_ fun _ => ?_
          · refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
            exact recvFinishTagRunC_eval_congr S K _ _ _ _ _ _ (by env_eq) rfl
          · refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
            refine letV_congr₂ (by
              rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.firstMsgADE_eval,
                _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.firstMsgADE_eval]; env_eq) fun _ => ?_
            refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
            refine letV_congr₂ (by env_eq) fun _ => ?_
            refine (bindV_congr₂ ?_ fun _ => ret_congr₂ (by ret_slots_eq))
            exact recvFinishTagRunC_eval_congr S K _ _ _ _ _ _ (by env_eq) (by env_eq)

private theorem eval_ren2_loc {A B R : PT} {Δ : List PT}
    (vA : Var Δ A) (vB : Var Δ B)
    (c0 : Comp pqxdhOps pqPrimIface [A, B] R) (c : Comp pqxdhOps pqPrimIface Δ R) (env : Env Δ)
    (h : compRename (ren2 vA vB) c0 = c) :
    c.eval env = c0.eval (.cons (env.get vA) (.cons (env.get vB) .nil)) := by
  rw [← h]
  exact compRename_eval c0 (ren2 vA vB) _ env
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)

private theorem liftAuthPrim1_eval {a r : Ty pqSig} (c : Comp pqxdhOps pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1 c e).eval ρ =
      embedVal r <$> c.eval (.cons (projVal a (e.eval ρ)) .nil) :=
  Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm.lift1_eval
    tlAuthPrim (fun _ => rfl) c e ρ

private theorem ckBaseArmC_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (stepK stepOld : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ₁tail Γ₂tail Δleg : List PT} {hF : Ext (authHybridStateFixedTy :: Γ₁tail) Δleg}
    {hX : Ext (arg :: Γ₂tail) Δleg} (envLeg : Env Δleg)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy.denote)
    (qAtom : (authCodec S).Q.denote) (x0 : arg.denote)
    {nOn' nRo' nRoot' : ℕ}
    (hBump : AuthCounterInv b (bumpPred (authSimPred S) c t))
    (hOnM : nOn' ≤ bumpPred (authSimPred S) c t 0)
    (hRoM : nRo' ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1)
    (hRtM : nRoot' ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2)
    (hRenK : compRename (ren2 (.succ .zero) .zero)
      (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg]) (Δ := [authHybridStateFixedTy, arg]) .zero .zero) =
      stepK (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero)
    (hRenLeg : compRename (ren2 (hF.wk .zero) (hX.wk .zero))
      (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg]) (Δ := [authHybridStateFixedTy, arg]) .zero .zero) =
      @stepOld (authHybridStateFixedTy :: Γ₁tail) (arg :: Γ₂tail) Δleg hF hX .zero .zero)
    (hFhstLeg : envLeg.get (hF.wk .zero) = projVal authHybridStateFixedTy s'.1.2.2.2)
    (hXLeg : envLeg.get (hX.wk .zero) = x0)
    (hSim :
      let ρ0 : Env (embedCtx [authHybridStateFixedTy, arg]) := .cons s'.1.2.2.2 (.cons (embedVal arg x0) .nil)
      (mapComp tlAuthPrim (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg]) (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval ρ0 =
      (mapComp tlAuthPrim (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg]) (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval ρ0 ∧
      ∀ rsf ∈ support ((mapComp tlAuthPrim (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg]) (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval ρ0),
        AuthFixedShadowAt S b nOn' nRo' nRoot' (rsf.2, s'.2)) :
    Prod.map id forgetCk <$> (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckBaseArmC S
      (fun fhst x => stepK fhst x)).eval (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil))) =
      (fun r : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF.denote =>
        (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy r.1,
         (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, embedVal authHybridStateFixedTy r.2))))) <$>
        (@stepOld (authHybridStateFixedTy :: Γ₁tail) (arg :: Γ₂tail) Δleg hF hX .zero .zero).eval envLeg ∧
    ∀ p ∈ support ((Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckBaseArmC S
      (fun fhst x => stepK fhst x)).eval (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil)))),
      AuthCkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let arm := (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckBaseArmC S
    (fun fhst x => stepK fhst x)).eval (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil)))
  let ρ0 : Env (embedCtx [authHybridStateFixedTy, arg]) := .cons s'.1.2.2.2 (.cons (embedVal arg x0) .nil)
  have hProj0 : projEnv ρ0 = Env.cons (projVal authHybridStateFixedTy s'.1.2.2.2) (Env.cons x0 Env.nil) := by
    change Env.cons (projVal authHybridStateFixedTy s'.1.2.2.2)
      (Env.cons (projVal arg (embedVal arg x0)) Env.nil) = _
    rw [AtomicLift.projVal_embedVal]
  have hLift :
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
        (letV (.fst (.var .zero)) fun fhst => letV (.snd (.var (.succ .zero))) fun x => stepK fhst x)
        (.pair (.snd (.snd (.snd (.fst .v1)))) .v0) :
        Comp pqAtomicOps _ [embedTy arg,
          Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy,
          (authCodec S).Q] _).eval
        (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil))) =
      (mapComp tlAuthPrim (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
        (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval ρ0 := by
    rw [liftAuthPrim1_eval, mapComp_eval_of_zero tlAuthPrim (fun _ => rfl), hProj0]
    dsimp only [letV, Expr.v0, Expr.v1]
    simp only [Expr.eval, env_get_succ, env_get_zero]
    have hPP : projVal (.prod authHybridStateFixedTy arg) (s'.1.2.2.2, embedVal arg x0) =
        (projVal authHybridStateFixedTy s'.1.2.2.2, x0) :=
      Prod.ext rfl (AtomicLift.projVal_embedVal arg x0)
    rw [hPP, eval_letC, eval_letC]
    simp only [Expr.eval, env_get_succ, env_get_zero]
    exact congrArg _ (eval_ren2_loc (.succ .zero) .zero _ _ _ hRenK)
  have hOldEval :
      (mapComp tlAuthPrim (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
        (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval ρ0 =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF <$>
        (@stepOld (authHybridStateFixedTy :: Γ₁tail) (arg :: Γ₂tail) Δleg hF hX .zero .zero).eval envLeg := by
    rw [mapComp_eval_of_zero tlAuthPrim (fun _ => rfl), hProj0,
      eval_ren2_loc (hF.wk .zero) (hX.wk .zero) _ _ envLeg hRenLeg, hFhstLeg, hXLeg]
  constructor
  · dsimp only [arm, Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckBaseArmC,
      Comp.eval]
    rw [hLift, hSim.1, hOldEval, bind_map_left, map_bind]
    conv_rhs => rw [map_eq_bind_pure_comp]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun r _ => ?_
    simp only [Function.comp_def, map_pure, Expr.eval, env_get_succ, env_get_zero, Expr.v0, Expr.v2,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE,
      forgetCk, Prod.map]
    rfl
  · intro p hp
    dsimp only [arm, Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckBaseArmC,
      Comp.eval] at hp
    rw [hLift, mem_support_bind_iff] at hp
    rcases hp with ⟨rsf, hrsf, hp'⟩
    simp only [Expr.eval, env_get_succ, env_get_zero, Expr.v0, Expr.v2,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE,
      support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    exact ⟨hBump, (hSim.2 rsf hrsf).mono hOnM hRoM hRtM⟩

set_option maxHeartbeats 400000 in
private theorem ckSessionArm_sim (S : Setup) (b : QueryBudget) {XTy : PT}
    (stepK : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
      [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ],
      Var Γ₁ .nat → Var Γ₂ (.prod (B 32) (B 32)) → Var Γ₃ authHybridStateFixedTy → Var Γ₄ XTy →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    (stepOld : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
      [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ],
      Var Γ₁ .nat → Var Γ₂ (.prod (B 32) (B 32)) → Var Γ₃ authHybridStateFixedTy → Var Γ₄ XTy →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ₁tail Γ₂tail Γ₃tail Γ₄tail Δleg : List PT}
    {h₁ : Ext (.nat :: Γ₁tail) Δleg}
    {h₂ : Ext (.prod (B 32) (B 32) :: Γ₂tail) Δleg}
    {h₃ : Ext (authHybridStateFixedTy :: Γ₃tail) Δleg}
    {h₄ : Ext (XTy :: Γ₄tail) Δleg}
    (envLeg : Env Δleg)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy.denote)
    (qAtom : (authCodec S).Q.denote) (x0 : XTy.denote)
    {s0 : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy.denote}
    (hs0 : projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1 = s0)
    {nOn nRo nRoot : ℕ}
    (hBump : AuthCounterInv b (bumpPred (authSimPred S) c t))
    (hOnM : nOn + 1 ≤ bumpPred (authSimPred S) c t 0)
    (hRoM : nRo + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1)
    (hRtM : nRoot + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (ckShadowFixed s'))
    (hRoCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hRtCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hEq :
      (stepK
        (Γ₁ := [.nat, XTy, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
                .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy XTy])
        (Γ₂ := [.prod (B 32) (B 32), .nat, XTy, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
                .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy XTy])
        (Γ₃ := [authHybridStateFixedTy, .prod (B 32) (B 32), .nat, XTy,
                _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
                .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy XTy])
        (Γ₄ := [XTy, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
                .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy XTy])
        (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32), .nat, XTy,
               _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
               .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy XTy])
        .zero .zero .zero .zero).eval
        (.cons s0.2.2.2 (.cons s0.2.2.1 (.cons s0.2.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))) =
      (@stepOld (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
        (authHybridStateFixedTy :: Γ₃tail) (XTy :: Γ₄tail) Δleg h₁ h₂ h₃ h₄
        .zero .zero .zero .zero).eval envLeg)
    (hLeaves :
      AllLeaves (fun res =>
        AuthFixedValOnlineBounded (nOn + 1) res.2 ∧
        CacheStepAtMostOne (valRoCache s0.2.2.2.1.1) (valRoCache res.2.1.1) ∧
        CacheStepAtMostOne (valRootRoCache s0.2.2.2.1.1) (valRootRoCache res.2.1.1))
        ((@stepOld (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
          (authHybridStateFixedTy :: Γ₃tail) (XTy :: Γ₄tail) Δleg h₁ h₂ h₃ h₄
          .zero .zero .zero .zero).eval envLeg)) :
    Prod.map id forgetCk <$> ((Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           stepK idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC (AuthKindFuels.ofBudget S b).K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal XTy x0) (.cons s' (.cons qAtom .nil)))) =
      (fun r : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF.denote =>
        (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy r.1,
         (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, embedVal authHybridStateFixedTy r.2))))) <$>
        (@stepOld (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
          (authHybridStateFixedTy :: Γ₃tail) (XTy :: Γ₄tail) Δleg h₁ h₂ h₃ h₄
          .zero .zero .zero .zero).eval envLeg ∧
    ∀ p ∈ support ((Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           stepK idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC (AuthKindFuels.ofBudget S b).K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal XTy x0) (.cons s' (.cons qAtom .nil)))),
      AuthCkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let F := AuthKindFuels.ofBudget S b
  let cOld_leg := @stepOld (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
    (authHybridStateFixedTy :: Γ₃tail) (XTy :: Γ₄tail) Δleg h₁ h₂ h₃ h₄ .zero .zero .zero .zero
  let c_leg : Comp pqAtomicOps pqAuthPrimIface [embedTy XTy,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy,
      (authCodec S).Q] _ :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      (letV (.fst (.var .zero)) fun s =>
       letV (.snd (.var (.succ .zero))) fun x =>
       letV (.fst (.snd (v s))) fun idx =>
       letV (.fst (.snd (.snd (v s)))) fun chalP =>
       letV (.snd (.snd (.snd (v s)))) fun fhst =>
       stepK idx chalP fhst x)
      (.pair (.fst .v1) .v0)
  let arm := (Comp.bind
    (Comp.bind c_leg (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
    (.ret (.pair (.fst .v0)
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
        (.fst .v2) (.snd .v0))))).eval
    (.cons (embedVal XTy x0) (.cons s' (.cons qAtom .nil)))
  let ρ : Env [embedTy XTy,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy,
    (authCodec S).Q] := .cons (embedVal XTy x0) (.cons s' (.cons qAtom .nil))
  have hLegEval : c_leg.eval ρ = embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF <$> cOld_leg.eval envLeg := by
    rw [liftAuthPrim1_eval]
    dsimp only [ρ, letV, v, Expr.v0, Expr.v1, Ext.step_wk, Ext.refl_wk]
    simp only [Expr.eval, env_get_succ, env_get_zero]
    have hProjPair : projVal (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy XTy)
        (s'.1, embedVal XTy x0) = (s0, x0) :=
      Prod.ext hs0 (AtomicLift.projVal_embedVal XTy x0)
    rw [hProjPair]
    iterate 5 rw [eval_letC]
    simp only [Expr.eval, env_get_succ, env_get_zero]
    exact congrArg _ hEq
  have hRoInit : atomRoCache (ckShadowFixed s').1.1.1 = valRoCache s0.2.2.2.1.1 := by
    rw [← hs0]
    conv_lhs =>
      rw [show (ckShadowFixed s').1 = (s'.1).2.2.2 from rfl,
        ← AtomicLift.embedVal_projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1]
    exact atomRoCache_embedVal _
  have hRtInit : atomRootRoCache (ckShadowFixed s').1.1.1 = valRootRoCache s0.2.2.2.1.1 := by
    rw [← hs0]
    conv_lhs =>
      rw [show (ckShadowFixed s').1 = (s'.1).2.2.2 from rfl,
        ← AtomicLift.embedVal_projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1]
    exact atomRootRoCache_embedVal _
  have hLegProps : ∀ rsf ∈ support (c_leg.eval ρ),
      AuthFixedAtomOnlineBounded (nOn + 1) rsf.2 ∧
      CacheStepAtMostOne (atomRoCache (ckShadowFixed s').1.1.1) (atomRoCache rsf.2.1.1) ∧
      CacheStepAtMostOne (atomRootRoCache (ckShadowFixed s').1.1.1) (atomRootRoCache rsf.2.1.1) ∧
      (atomRoCache rsf.2.1.1).length ≤ nRo + 1 ∧
      (atomRootRoCache rsf.2.1.1).length ≤ nRoot + 1 := by
    intro rsf hrsf
    rw [hLegEval, support_map, Set.mem_image] at hrsf
    rcases hrsf with ⟨res, hres, rfl⟩
    obtain ⟨hOnB, hRoS, hRtS⟩ := AllLeaves_mem_support hLeaves hres
    have hRoEnd : atomRoCache (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF res).2.1.1 =
        valRoCache res.2.1.1 := atomRoCache_embedVal res.2.1.1
    have hRtEnd : atomRootRoCache (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF res).2.1.1 =
        valRootRoCache res.2.1.1 := atomRootRoCache_embedVal res.2.1.1
    have hRoS' : CacheStepAtMostOne (atomRoCache (ckShadowFixed s').1.1.1)
        (atomRoCache (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF res).2.1.1) := by
      rw [hRoInit, hRoEnd]; exact hRoS
    have hRtS' : CacheStepAtMostOne (atomRootRoCache (ckShadowFixed s').1.1.1)
        (atomRootRoCache (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF res).2.1.1) := by
      rw [hRtInit, hRtEnd]; exact hRtS
    exact ⟨(AuthFixedAtomOnlineBounded.iff_embedVal res.2).mpr hOnB, hRoS', hRtS',
      Nat.le_trans hRoS'.length_le (Nat.add_le_add_right hSh.ro_len_le 1),
      Nat.le_trans hRtS'.length_le (Nat.add_le_add_right hSh.root_len_le 1)⟩
  obtain ⟨hSyncMap, hSyncRel⟩ :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.syncFixedShadowRespC_bind_sim
      F.K_cap (ckShadowFixed s') c_leg (.snd .v1) ρ hSh.ro_shadow rfl
      (fun rsf hrsf =>
        let ⟨_, h1, h2, h3, h4⟩ := hLegProps rsf hrsf
        ⟨h1, h2, Nat.le_trans h3 hRoCap, Nat.le_trans h4 hRtCap⟩)
  constructor
  · have hArm : Prod.map id forgetCk <$> arm =
        (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, rsf.2))))) <$>
          (Prod.map id forgetAuthFixedShadow <$>
            (Comp.bind c_leg (syncFixedShadowRespC F.K_cap (.var .zero)
              (AtomicLift.exprRename Var.succ (.snd .v1)))).eval ρ) := by
      dsimp only [arm, Comp.eval, AtomicLift.exprRename]
      rw [map_bind, Functor.map_map, map_eq_bind_pure_comp]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun p _ => ?_
      simp only [Function.comp_def, map_pure, Expr.eval, env_get_succ, env_get_zero, Expr.v0, Expr.v2,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE,
        forgetCk, forgetAuthFixedShadow, Prod.map]
    rw [hArm, hSyncMap, hLegEval, Functor.map_map]
    rfl
  · intro p hp
    dsimp only [arm, Comp.eval] at hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    simp only [Expr.eval, Env.get, Expr.v0, Expr.v2,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE,
      support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    have hqMap : (q.1, q.2.1) ∈ support (c_leg.eval ρ) := by
      rw [← hSyncMap, support_map]
      exact ⟨q, hq, rfl⟩
    obtain ⟨hOnB, _, _, hRoL, hRtL⟩ := hLegProps (q.1, q.2.1) hqMap
    exact ⟨hBump, (AuthFixedShadowAt.mk hOnB hRoL hRtL (hSyncRel q hq)).mono hOnM hRoM hRtM⟩

set_option maxHeartbeats 400000 in
private theorem ckSendArm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {Γ₁tail Γ₂tail Γ₃tail Γ₄tail Δleg : List PT}
    {h₁ : Ext (.nat :: Γ₁tail) Δleg}
    {h₂ : Ext (.prod (B 32) (B 32) :: Γ₂tail) Δleg}
    {h₃ : Ext (authHybridStateFixedTy :: Γ₃tail) Δleg}
    {h₄ : Ext (sendQTy :: Γ₄tail) Δleg}
    (envLeg : Env Δleg)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy.denote)
    (qAtom : (authCodec S).Q.denote) (x0 : sendQTy.denote)
    {s0 : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy.denote}
    (hs0 : projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1 = s0)
    {nOn nRo nRoot : ℕ}
    (hBump : AuthCounterInv b (bumpPred (authSimPred S) c t))
    (hOnM : nOn + 1 ≤ bumpPred (authSimPred S) c t 0)
    (hRoM : nRo + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1)
    (hRtM : nRoot + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (ckShadowFixed s'))
    (hRoCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hRtCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hValOn : AuthFixedValOnlineBounded nOn s0.2.2.2)
    (hOnK : nOn ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hTotOld : nOn ≤ b.q_total)
    (hRoK : (valRoCache s0.2.2.2.1.1).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRoTotOld : (valRoCache s0.2.2.2.1.1).length ≤ b.q_total)
    (hRtK : (valRootRoCache s0.2.2.2.1.1).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRtTotOld : (valRootRoCache s0.2.2.2.1.1).length ≤ b.q_total)
    (hIdxLeg : envLeg.get (h₁.wk .zero) = s0.2.1)
    (hChalLeg : envLeg.get (h₂.wk .zero) = s0.2.2.1)
    (hFhstLeg : envLeg.get (h₃.wk .zero) = s0.2.2.2)
    (hXLeg : envLeg.get (h₄.wk .zero) = x0) :
    Prod.map id forgetCk <$> ((Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkSendKB S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro
             opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC (AuthKindFuels.ofBudget S b).K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal sendQTy x0) (.cons s' (.cons qAtom .nil)))) =
      (fun r : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF.denote =>
        (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy r.1,
         (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, embedVal authHybridStateFixedTy r.2))))) <$>
        (@_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S b.q_total
          (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
          (authHybridStateFixedTy :: Γ₃tail) (sendQTy :: Γ₄tail) Δleg opk
          .zero .zero .zero .zero h₁ h₂ h₃ h₄).eval envLeg ∧
    ∀ p ∈ support ((Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkSendKB S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro
             opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC (AuthKindFuels.ofBudget S b).K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal sendQTy x0) (.cons s' (.cons qAtom .nil)))),
      AuthCkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let F := AuthKindFuels.ofBudget S b
  let envK : Env [authHybridStateFixedTy, .prod (B 32) (B 32), .nat, sendQTy,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
      .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy sendQTy] :=
    .cons s0.2.2.2 (.cons s0.2.2.1 (.cons s0.2.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))
  have hFK : envK.get (Ext.refl.wk .zero) = s0.2.2.2 := by
    simp only [envK, Ext.refl_wk, env_get_zero]
  refine ckSessionArm_sim S b
    (fun idx chalP fhst x => authCkSendKB S F.K_on F.K_ro opk idx chalP fhst x)
    (fun idx chalP fhst x =>
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkSendB S b.q_total opk idx chalP fhst x)
    (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) envLeg c t s' qAtom x0 hs0
    hBump hOnM hRoM hRtM hSh hRoCap hRtCap ?_ ?_
  · refine (authCkSendKB_fuel_eq S opk .zero .zero .zero .zero envK
      (hFK.symm ▸ hValOn) hOnK hTotOld
      (hFK.symm ▸ hRoK) (hFK.symm ▸ hRoTotOld)
      (hFK.symm ▸ hRtK) (hFK.symm ▸ hRtTotOld)).trans ?_
    rw [authCkSendB_eval_ren4,
      authCkSendB_eval_ren4 S b.q_total opk .zero .zero .zero .zero
        (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) envLeg]
    simp only [envK, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
      hIdxLeg, hChalLeg, hFhstLeg, hXLeg]
  · have hL := @authCkSendB_leaves S b.q_total opk nOn
      (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
      (authHybridStateFixedTy :: Γ₃tail) (sendQTy :: Γ₄tail) Δleg
      .zero .zero .zero .zero h₁ h₂ h₃ h₄ envLeg
      (hFhstLeg.symm ▸ hValOn) (hFhstLeg.symm ▸ hRoTotOld) (hFhstLeg.symm ▸ hRtTotOld)
    simpa only [hFhstLeg] using hL

set_option maxHeartbeats 400000 in
private theorem ckRecvArm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    {Γ₁tail Γ₂tail Γ₃tail Γ₄tail Δleg : List PT}
    {h₁ : Ext (.nat :: Γ₁tail) Δleg}
    {h₂ : Ext (.prod (B 32) (B 32) :: Γ₂tail) Δleg}
    {h₃ : Ext (authHybridStateFixedTy :: Γ₃tail) Δleg}
    {h₄ : Ext (recvQTy :: Γ₄tail) Δleg}
    (envLeg : Env Δleg)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy.denote)
    (qAtom : (authCodec S).Q.denote) (x0 : recvQTy.denote)
    {s0 : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy.denote}
    (hs0 : projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1 = s0)
    {nOn nRo nRoot : ℕ}
    (hBump : AuthCounterInv b (bumpPred (authSimPred S) c t))
    (hOnM : nOn + 1 ≤ bumpPred (authSimPred S) c t 0)
    (hRoM : nRo + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1)
    (hRtM : nRoot + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot (ckShadowFixed s'))
    (hRoCap : nRo + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hRtCap : nRoot + 1 ≤ (AuthKindFuels.ofBudget S b).K_cap)
    (hValOn : AuthFixedValOnlineBounded nOn s0.2.2.2)
    (hOnK : nOn ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hTotOld : nOn ≤ b.q_total)
    (hRoK : (valRoCache s0.2.2.2.1.1).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRoTotOld : (valRoCache s0.2.2.2.1.1).length ≤ b.q_total)
    (hRtK : (valRootRoCache s0.2.2.2.1.1).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRtTotOld : (valRootRoCache s0.2.2.2.1.1).length ≤ b.q_total)
    (hIdxLeg : envLeg.get (h₁.wk .zero) = s0.2.1)
    (hChalLeg : envLeg.get (h₂.wk .zero) = s0.2.2.1)
    (hFhstLeg : envLeg.get (h₃.wk .zero) = s0.2.2.2)
    (hXLeg : envLeg.get (h₄.wk .zero) = x0) :
    Prod.map id forgetCk <$> ((Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkRecvKB S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro
             opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC (AuthKindFuels.ofBudget S b).K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal recvQTy x0) (.cons s' (.cons qAtom .nil)))) =
      (fun r : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF.denote =>
        (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy r.1,
         (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, embedVal authHybridStateFixedTy r.2))))) <$>
        (@_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB S b.q_total
          (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
          (authHybridStateFixedTy :: Γ₃tail) (recvQTy :: Γ₄tail) Δleg opk
          .zero .zero .zero .zero h₁ h₂ h₃ h₄).eval envLeg ∧
    ∀ p ∈ support ((Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkRecvKB S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro
             opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC (AuthKindFuels.ofBudget S b).K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal recvQTy x0) (.cons s' (.cons qAtom .nil)))),
      AuthCkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let F := AuthKindFuels.ofBudget S b
  let envK : Env [authHybridStateFixedTy, .prod (B 32) (B 32), .nat, recvQTy,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
      .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy recvQTy] :=
    .cons s0.2.2.2 (.cons s0.2.2.1 (.cons s0.2.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))
  have hFK : envK.get (Ext.refl.wk .zero) = s0.2.2.2 := by
    simp only [envK, Ext.refl_wk, env_get_zero]
  refine ckSessionArm_sim S b
    (fun idx chalP fhst x => authCkRecvKB S F.K_on F.K_ro opk idx chalP fhst x)
    (fun idx chalP fhst x =>
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkRecvB S b.q_total opk idx chalP fhst x)
    (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) envLeg c t s' qAtom x0 hs0
    hBump hOnM hRoM hRtM hSh hRoCap hRtCap ?_ ?_
  · refine (authCkRecvKB_fuel_eq S opk .zero .zero .zero .zero envK
      (hFK.symm ▸ hValOn) hOnK hTotOld
      (hFK.symm ▸ hRoK) (hFK.symm ▸ hRoTotOld)
      (hFK.symm ▸ hRtK) (hFK.symm ▸ hRtTotOld)).trans
      (authCkRecvB_eval_congr S b.q_total opk .zero .zero .zero .zero envK
        .zero .zero .zero .zero (h₅ := h₁) (h₆ := h₂) (h₇ := h₃) (h₈ := h₄) envLeg ?_ ?_ ?_ ?_) <;>
      simp only [envK, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
        hIdxLeg, hChalLeg, hFhstLeg, hXLeg]
  · have hL := @authCkRecvB_leaves S b.q_total opk nOn
      (.nat :: Γ₁tail) (.prod (B 32) (B 32) :: Γ₂tail)
      (authHybridStateFixedTy :: Γ₃tail) (recvQTy :: Γ₄tail) Δleg
      .zero .zero .zero .zero h₁ h₂ h₃ h₄ envLeg
      (hFhstLeg.symm ▸ hValOn) (hFhstLeg.symm ▸ hRoTotOld) (hFhstLeg.symm ▸ hRtTotOld)
    simpa only [hFhstLeg] using hL

private theorem ckRoArm_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (armRo : Comp pqAtomicOps pqAuthPrimIface
      [embedTy arg,
       Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy,
       (authCodec S).Q]
      (.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
        authFixedShadowStTy))
    (stepOld : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ₁tail Γ₂tail Δleg : List PT} {hF : Ext (authHybridStateFixedTy :: Γ₁tail) Δleg}
    {hX : Ext (arg :: Γ₂tail) Δleg} (envLeg : Env Δleg)
    (c : Fin 4 → ℕ) (t : AuthQuery S)
    (s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.authCkShadowStTy.denote)
    (qAtom : (authCodec S).Q.denote) (x0 : arg.denote)
    {nOn' nRo' nRoot' : ℕ}
    (hBump : AuthCounterInv b (bumpPred (authSimPred S) c t))
    (hOnM : nOn' ≤ bumpPred (authSimPred S) c t 0)
    (hRoM : nRo' ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1)
    (hRtM : nRoot' ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2)
    (hRenLeg : compRename (ren2 (hF.wk .zero) (hX.wk .zero))
      (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg]) (Δ := [authHybridStateFixedTy, arg]) .zero .zero) =
      @stepOld (authHybridStateFixedTy :: Γ₁tail) (arg :: Γ₂tail) Δleg hF hX .zero .zero)
    (hFhstLeg : envLeg.get (hF.wk .zero) = projVal authHybridStateFixedTy s'.1.2.2.2)
    (hXLeg : envLeg.get (hX.wk .zero) = x0)
    (hRoSim :
      let ρ := Env.cons (embedVal arg x0) (Env.cons s' (Env.cons qAtom Env.nil))
      Prod.map id forgetAuthFixedShadow <$> armRo.eval ρ =
        (mapComp tlAuthPrim (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero)).eval
          (.cons (ckShadowFixed s').1 (.cons (embedVal arg x0) .nil)) ∧
      ∀ q ∈ support (armRo.eval ρ), AuthFixedShadowAt S b nOn' nRo' nRoot' q.2) :
    Prod.map id forgetCk <$> ((Comp.bind armRo
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil)))) =
      (fun r : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF.denote =>
        (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy r.1,
         (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, embedVal authHybridStateFixedTy r.2))))) <$>
        (@stepOld (authHybridStateFixedTy :: Γ₁tail) (arg :: Γ₂tail) Δleg hF hX .zero .zero).eval envLeg ∧
    ∀ p ∈ support ((Comp.bind armRo
      (.ret (.pair (.fst .v0)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
          (.fst .v2) (.snd .v0))))).eval
      (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil)))),
      AuthCkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let arm := (Comp.bind armRo
    (.ret (.pair (.fst .v0)
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE
        (.fst .v2) (.snd .v0))))).eval
    (.cons (embedVal arg x0) (.cons s' (.cons qAtom .nil)))
  obtain ⟨hMap, hPres⟩ := hRoSim
  constructor
  · dsimp only [arm, Comp.eval, Expr.eval, Expr.v0, Expr.v2,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE]
    rw [map_bind]
    simp only [env_get_succ, env_get_zero]
    have hL : ∀ m : OracleComp _root_.SignalPqxdh.PrimBaseSpec
          (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy.denote × authFixedShadowStTy.denote),
        (m >>= fun q => Prod.map id forgetCk <$> pure (q.1, ((s'.1.1, (s'.1.2.1, (s'.1.2.2.1, q.2.1))), q.2.2))) =
          (fun rsf => (rsf.1, (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, rsf.2))))) <$> (Prod.map id forgetAuthFixedShadow <$> m) := by
      intro m; rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
    rw [hL, hMap, mapComp_eval_of_zero tlAuthPrim (fun _ => rfl), Functor.map_map]
    have hPE : projEnv (Γ := [authHybridStateFixedTy, arg])
        (.cons (ckShadowFixed s').1 (.cons (embedVal arg x0) .nil)) =
        Env.cons (projVal authHybridStateFixedTy s'.1.2.2.2) (Env.cons x0 Env.nil) := by
      change Env.cons (projVal authHybridStateFixedTy s'.1.2.2.2)
        (Env.cons (projVal arg (embedVal arg x0)) Env.nil) = _
      rw [AtomicLift.projVal_embedVal]
    rw [hPE, eval_ren2_loc (hF.wk .zero) (hX.wk .zero) _ _ envLeg hRenLeg, hFhstLeg, hXLeg]
    rfl
  · intro p hp
    dsimp only [arm, Comp.eval] at hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    simp only [Expr.eval, env_get_succ, env_get_zero, Expr.v0, Expr.v2,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.ckRebuildE,
      support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    exact ⟨hBump, (hPres q hq).mono hOnM hRoM hRtM⟩

private theorem bump_on_step {S : Setup} (c : Fin 4 → ℕ) {t : AuthQuery S}
    (h0 : authSimPred S 0 t) (h1 : ¬ authSimPred S 1 t) (h2 : ¬ authSimPred S 2 t) :
    (c 0 + 1 ≤ bumpPred (authSimPred S) c t 0) ∧
    (c 0 + c 1 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1) ∧
    (c 0 + c 2 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2) := by
  simp only [bumpPred, eq_true h0, eq_false h1, eq_false h2, ite_true, ite_false]
  omega

private theorem bump_on_keep {S : Setup} (c : Fin 4 → ℕ) {t : AuthQuery S}
    (h0 : authSimPred S 0 t) (h1 : ¬ authSimPred S 1 t) (h2 : ¬ authSimPred S 2 t) :
    (c 0 ≤ bumpPred (authSimPred S) c t 0) ∧
    (c 0 + c 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1) ∧
    (c 0 + c 2 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2) := by
  simp only [bumpPred, eq_true h0, eq_false h1, eq_false h2, ite_true, ite_false]
  omega

private theorem bump_ro_step {S : Setup} (c : Fin 4 → ℕ) {t : AuthQuery S}
    (h0 : ¬ authSimPred S 0 t) (h1 : authSimPred S 1 t) (h2 : ¬ authSimPred S 2 t) :
    (c 0 ≤ bumpPred (authSimPred S) c t 0) ∧
    (c 0 + c 1 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1) ∧
    (c 0 + c 2 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2) := by
  simp only [bumpPred, eq_false h0, eq_true h1, eq_false h2, ite_true, ite_false]
  omega

private theorem bump_rt_step {S : Setup} (c : Fin 4 → ℕ) {t : AuthQuery S}
    (h0 : ¬ authSimPred S 0 t) (h1 : ¬ authSimPred S 1 t) (h2 : authSimPred S 2 t) :
    (c 0 ≤ bumpPred (authSimPred S) c t 0) ∧
    (c 0 + c 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 1) ∧
    (c 0 + c 2 + 1 ≤ bumpPred (authSimPred S) c t 0 + bumpPred (authSimPred S) c t 2) := by
  simp only [bumpPred, eq_false h0, eq_false h1, eq_true h2, ite_true, ite_false]
  omega

private theorem eval_caseSumV {Γ : List PT} {τ₁ τ₂ τ : PT} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ) (env : Env Γ) :
    (caseSumV s kl kr).eval env =
      match s.eval env with
      | .inl a => (kl .zero).eval (.cons a env)
      | .inr b => (kr .zero).eval (.cons b env) := by
  simp only [caseSumV, Comp.eval]
  cases s.eval env <;> rfl

set_option maxHeartbeats 400000 in
/-- Forgetful simulation between `prfCk1KeyKindProg` and `prfCkOldAtomicProg`. -/
theorem prfCk1KeyKindProg_forgetSim (S : Setup) (b : QueryBudget)
    (chalPair : ((.prod (PB 32) (PB 32)) : Ty pqAtomicSig).denote) :
    ForgetSim (prfCk1KeyKindProg S b) (prfCkOldAtomicProg S b)
      forgetCk (authSimPred S) (authSimBounds b) chalPair (AuthCkInv S b) := by
  let F := AuthKindFuels.ofBudget S b
  dsimp only [prfCk1KeyKindProg]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · dsimp only [prfCkOldAtomicProg, AtomicLift.liftAuth1Stage,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkRedProg1Key,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.prfCkKindInitC,
        Comp.eval]
      rw [map_bind]
      conv_rhs => rw [← bind_pure ((mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkInitDslK S b.q_total)).eval (.cons chalPair .nil))]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun p _ => ?_
      simp only [map_pure, Expr.eval, env_get_zero, Expr.v0, forgetCk, Prod.map]
    · dsimp only [
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.prfCkKindInitC,
        Comp.eval]
      intro as' has'
      rw [mem_support_bind_iff] at has'
      rcases has' with ⟨p, hp, has'⟩
      obtain ⟨x, hx, rfl⟩ := mem_support_mapComp_of_zero tlAuthPrim (fun _ => rfl)
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkInitDslK S b.q_total)
        (.cons chalPair .nil) hp
      simp only [Expr.eval, env_get_zero, Expr.v0, support_pure, Set.mem_singleton_iff] at has'
      subst has'
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkInitDslK, bindV, Comp.eval] at hx
      rw [mem_support_bind_iff] at hx
      rcases hx with ⟨idx, -, hx⟩
      rw [mem_support_bind_iff] at hx
      rcases hx with ⟨secb, -, hx⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      refine ⟨AuthCounterInv.zero b, ?_⟩
      have hRoEmpty : atomRoCache (ckShadowFixed ((embedVal
          (.prod .unit _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy) x).2,
          emptyRoBothAvlE.eval
            (.cons (embedVal (.prod .unit _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy) x)
              (.cons chalPair .nil)))).1.1.1 = [] := by
        change atomRoCache (embedVal authStateTy x.2.2.2.2.1.1) = []
        rw [atomRoCache_embedVal, hx]
        rfl
      have hRtEmpty : atomRootRoCache (ckShadowFixed ((embedVal
          (.prod .unit _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy) x).2,
          emptyRoBothAvlE.eval
            (.cons (embedVal (.prod .unit _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy) x)
              (.cons chalPair .nil)))).1.1.1 = [] := by
        change atomRootRoCache (embedVal authStateTy x.2.2.2.2.1.1) = []
        rw [atomRootRoCache_embedVal, hx]
        rfl
      refine ⟨(AuthFixedAtomOnlineBounded.iff_embedVal x.2.2.2.2).mpr ?_, ?_, ?_, ?_⟩
      · rw [hx]
        refine ⟨⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
          by rfl, by rfl, by rfl, by rfl⟩, by rfl, by rfl, by rfl, by rfl⟩
      · rw [hRoEmpty]; exact Nat.zero_le _
      · rw [hRtEmpty]; exact Nat.zero_le _
      · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.emptyRoBothAvlE_roBothShadowRel
          F.K_cap _
          (.cons (embedVal (.prod .unit _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy) x)
            (.cons chalPair .nil)) hRoEmpty hRtEmpty
  · intro c s' t _ hroom hInv
    let s0 := projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1
    have hs1 : s'.1 = embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s0 :=
      (AtomicLift.embedVal_projVal _ s'.1).symm
    have hSh1 : (ckShadowFixed s').1 = embedVal authHybridStateFixedTy s0.2.2.2 := by
      dsimp only [ckShadowFixed]; rw [hs1]; rfl
    have hShSt : (ckShadowFixed s').1.1.1 = embedVal authStateTy s0.2.2.2.1.1 :=
      congrArg (fun x => x.1.1) hSh1
    have hValOn : AuthFixedValOnlineBounded (c 0) s0.2.2.2 :=
      (AuthFixedAtomOnlineBounded.iff_embedVal s0.2.2.2).mp (hSh1 ▸ hInv.shadow_ok.online_le)
    have hRoLen : (valRoCache s0.2.2.2.1.1).length ≤ c 0 + c 1 := by
      rw [← atomRoCache_embedVal, ← hShSt]; exact hInv.shadow_ok.ro_len_le
    have hRtLen : (valRootRoCache s0.2.2.2.1.1).length ≤ c 0 + c 2 := by
      rw [← atomRootRoCache_embedVal, ← hShSt]; exact hInv.shadow_ok.root_len_le
    have hTotOld : c 0 ≤ b.q_total := Nat.le_trans hInv.counter_inv.on_le (Nat.min_le_right _ _)
    have hRoTotOld : c 0 + c 1 ≤ b.q_total := by
      have := hInv.counter_inv.sum_eq; have := hInv.counter_inv.tot_le; omega
    have hRtTotOld : c 0 + c 2 ≤ b.q_total := by
      have := hInv.counter_inv.sum_eq; have := hInv.counter_inv.tot_le; omega
    let q0 : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy.denote :=
      (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
    have hRhs :
        (prfCkOldAtomicProg S b).handle.eval (.cons (forgetCk s') (.cons ((authCodec S).qenc t) .nil)) =
          (fun r : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF.denote =>
            (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy r.1,
             (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, embedVal authHybridStateFixedTy r.2))))) <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC S b.q_total
            (Γ₁ := [.nat, .bool, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy])
            (Γ₂ := [.prod (B 32) (B 32), .nat, .bool, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy])
            (Γ₃ := [authHybridStateFixedTy, .prod (B 32) (B 32), .nat, .bool,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy])
            (Γ₄ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authQueryTy])
            .zero .zero .zero (.succ .zero)).eval
            (.cons s0.2.2.2 (.cons s0.2.2.1 (.cons s0.2.1 (.cons s0.1
              (.cons s0 (.cons s0 (.cons q0 .nil))))))) := by
      dsimp only [prfCkOldAtomicProg, AtomicLift.liftAuth1Stage, forgetCk,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkRedProg1Key]
      rw [hs1]
      refine (liftAuthHandle_eval tlAuthPrim S (fun _ => rfl)
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkHandle1KeyDsl S b.q_total) s0 t).trans ?_
      dsimp only [q0, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkHandle1KeyDsl,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckSecb,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckIdx,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckChal,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckFhst,
        letV, bindV, v, Ext.step_wk, Ext.refl_wk]
      iterate 5 rw [eval_letC]
      dsimp only [Comp.eval]
      rw [map_eq_bind_pure_comp, bind_assoc]
      symm
      rw [map_eq_bind_pure_comp]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun r _ => ?_
      simp only [pure_bind, Function.comp_def, Expr.eval, env_get_succ, env_get_zero, embedVal]
    rw [hRhs]
    dsimp only [q0,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.prfCkKindHandleC]
    rw [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.dispatchAuthQ_eval_qenc
      (Γ := [.prod (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy) roBothAvlTy, (authCodec S).Q])
      (.var (.succ .zero)) (.cons s' (.cons ((authCodec S).qenc t) .nil)) t rfl]
    unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.dispatchAuthQEval
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hOnStep := fun h0 => AuthCounterInv.online_step_bounds hInv.counter_inv h0 hroom
    have hRoStep := fun h1 => AuthCounterInv.ro_step_bounds hInv.counter_inv h1 hroom
    have hRtStep := fun h2 => AuthCounterInv.roRoot_step_bounds hInv.counter_inv h2 hroom
    cases t with
    | initPrin u =>
      obtain ⟨hOn, _, _, _⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .initPrin u) trivial nofun nofun
      have hQ : (authCodec S).qenc (.initPrin u) = .inl (embedVal .nat u.val) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckBaseArmC_sim S b
        (fun fhst x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.initPrin1KeyFixedKB F fhst x)
        (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.initPrin1KeyFixedB b.q_total fhst x)
        _ c _ s' _ u.val hBump hM0 (Nat.le_of_succ_le hM1) (Nat.le_of_succ_le hM2)
        ?_ ?_ ?_ ?_
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed.initPrinFixedShadowB_sim
          tlAuthPrim id (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩) S b (ckShadowFixed s') u.val
          hInv.shadow_ok hOn) <;>
        rfl
    | corruptIK u =>
      obtain ⟨hOn, _, _, _⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .corruptIK u) trivial nofun nofun
      have hQ : (authCodec S).qenc (.corruptIK u) = .inr (.inl (embedVal .nat u.val)) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckBaseArmC_sim S b
        (fun fhst x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.corruptFixedKB F fhst x)
        (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.corruptFixedB b.q_total fhst x)
        _ c _ s' _ u.val hBump hM0 (Nat.le_of_succ_le hM1) (Nat.le_of_succ_le hM2)
        ?_ ?_ ?_ ?_
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed.corruptFixedShadowB_sim
          tlAuthPrim id (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩) S b (ckShadowFixed s') u.val
          hInv.shadow_ok hOn) <;>
        rfl
    | genSPK u j =>
      obtain ⟨hOn, _, _, _⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .genSPK u j) trivial nofun nofun
      have hQ : (authCodec S).qenc (.genSPK u j) =
          .inr (.inr (.inl (embedVal (.prod .nat .nat) (u.val, j.val)))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckBaseArmC_sim S b
        (fun fhst x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.genSpkFixedKB F fhst x)
        (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genSpkFixedB b.q_total fhst x)
        _ c _ s' _ (u.val, j.val) hBump hM0 (Nat.le_of_succ_le hM1) (Nat.le_of_succ_le hM2)
        ?_ ?_ ?_ ?_
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed.genSpkFixedShadowB_sim
          tlAuthPrim id (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩) S b (ckShadowFixed s') (u.val, j.val)
          hInv.shadow_ok hOn) <;>
        rfl
    | genOPK u j k =>
      obtain ⟨hOn, _, _, _⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .genOPK u j k) trivial nofun nofun
      have hQ : (authCodec S).qenc (.genOPK u j k) =
          .inr (.inr (.inr (.inl (embedVal (.prod .nat (.prod .nat .nat)) (u.val, (j.val, k.val)))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckBaseArmC_sim S b
        (fun fhst x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.genOpkFixedKB F fhst x)
        (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genOpkFixedB b.q_total fhst x)
        _ c _ s' _ (u.val, (j.val, k.val)) hBump hM0 (Nat.le_of_succ_le hM1) (Nat.le_of_succ_le hM2)
        ?_ ?_ ?_ ?_
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed.genOpkFixedShadowB_sim
          tlAuthPrim id (fun _ _ _ h => h) (fun _ _ y hy => ⟨y, hy, rfl⟩) S b (ckShadowFixed s') (u.val, (j.val, k.val))
          hInv.shadow_ok hOn) <;>
        rfl
    | sendOPK u i bu m0 m1 =>
      obtain ⟨hOn, hRoK, hRtK, hCap⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .sendOPK u i bu m0 m1) trivial nofun nofun
      have hQ : (authCodec S).qenc (.sendOPK u i bu m0 m1) =
          .inr (.inr (.inr (.inr (.inl (embedVal sendQTy _))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckSendArm_sim S b true _ c _ s' _ _ rfl hBump hM0 hM1 hM2
        hInv.shadow_ok (Nat.le_trans (by omega) hCap) (Nat.le_trans (by omega) hCap)
        hValOn (Nat.le_of_succ_le hOn) hTotOld
        (Nat.le_trans hRoLen (by omega)) (Nat.le_trans hRoLen hRoTotOld)
        (Nat.le_trans hRtLen (by omega)) (Nat.le_trans hRtLen hRtTotOld) ?_ ?_ ?_ ?_ <;>
        (simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; try rfl)
    | sendNoOPK u i bu m0 m1 =>
      obtain ⟨hOn, hRoK, hRtK, hCap⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .sendNoOPK u i bu m0 m1) trivial nofun nofun
      have hQ : (authCodec S).qenc (.sendNoOPK u i bu m0 m1) =
          .inr (.inr (.inr (.inr (.inr (.inl (embedVal sendQTy _)))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckSendArm_sim S b false _ c _ s' _ _ rfl hBump hM0 hM1 hM2
        hInv.shadow_ok (Nat.le_trans (by omega) hCap) (Nat.le_trans (by omega) hCap)
        hValOn (Nat.le_of_succ_le hOn) hTotOld
        (Nat.le_trans hRoLen (by omega)) (Nat.le_trans hRoLen hRoTotOld)
        (Nat.le_trans hRtLen (by omega)) (Nat.le_trans hRtLen hRtTotOld) ?_ ?_ ?_ ?_ <;>
        (simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; try rfl)
    | recvOPK u i o msg =>
      obtain ⟨hOn, hRoK, hRtK, hCap⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .recvOPK u i o msg) trivial nofun nofun
      have hQ : (authCodec S).qenc (.recvOPK u i o msg) =
          .inr (.inr (.inr (.inr (.inr (.inr (.inl (embedVal recvQTy _))))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckRecvArm_sim S b true _ c _ s' _ _ rfl hBump hM0 hM1 hM2
        hInv.shadow_ok (Nat.le_trans (by omega) hCap) (Nat.le_trans (by omega) hCap)
        hValOn (Nat.le_of_succ_le hOn) hTotOld
        (Nat.le_trans hRoLen (by omega)) (Nat.le_trans hRoLen hRoTotOld)
        (Nat.le_trans hRtLen (by omega)) (Nat.le_trans hRtLen hRtTotOld) ?_ ?_ ?_ ?_ <;>
        (simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; try rfl)
    | recvNoOPK u i o msg =>
      obtain ⟨hOn, hRoK, hRtK, hCap⟩ := hOnStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .recvNoOPK u i o msg) trivial nofun nofun
      have hQ : (authCodec S).qenc (.recvNoOPK u i o msg) =
          .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (embedVal recvQTy _)))))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckRecvArm_sim S b false _ c _ s' _ _ rfl hBump hM0 hM1 hM2
        hInv.shadow_ok (Nat.le_trans (by omega) hCap) (Nat.le_trans (by omega) hCap)
        hValOn (Nat.le_of_succ_le hOn) hTotOld
        (Nat.le_trans hRoLen (by omega)) (Nat.le_trans hRoLen hRoTotOld)
        (Nat.le_trans hRtLen (by omega)) (Nat.le_trans hRtLen hRtTotOld) ?_ ?_ ?_ ?_ <;>
        (simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; try rfl)
    | roQuery sec =>
      obtain ⟨hRoK, hRoOld, _⟩ := hRoStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_ro_step (S := S) c (t := .roQuery sec) nofun trivial nofun
      have hQ : (authCodec S).qenc (.roQuery sec) =
          .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (embedVal (B 192) sec))))))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckRoArm_sim S b _ (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.roFixedB b.q_total fhst x)
        _ c _ s' _ sec hBump hM0 (by omega) hM2 ?_ ?_ ?_
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.roFixedShadowArmC_sim_prim
          S b (.pair (.snd (.snd (.snd (.fst .v1)))) (.snd .v1)) .v0 _ (ckShadowFixed s') sec
          rfl rfl hInv.shadow_ok (by omega) (by omega)) <;>
        rfl
    | roRootQuery rk dh =>
      obtain ⟨hRtK, hRtOld, _⟩ := hRtStep trivial
      obtain ⟨hM0, hM1, hM2⟩ := bump_rt_step (S := S) c (t := .roRootQuery rk dh) nofun nofun trivial
      have hQ : (authCodec S).qenc (.roRootQuery rk dh) =
          .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (embedVal (.prod (B 32) (B 32)) (rk, dh))))))))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckRoArm_sim S b _ (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.roRootFixedB b.q_total fhst x)
        _ c _ s' _ (rk, dh) hBump hM0 hM1 (by omega) ?_ ?_ ?_
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.roRootFixedShadowArmC_sim_prim
          S b (.pair (.snd (.snd (.snd (.fst .v1)))) (.snd .v1)) .v0 _ (ckShadowFixed s') (rk, dh)
          rfl rfl hInv.shadow_ok (by omega) (by omega)) <;>
        rfl
    | revealDhSecrets =>
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_keep (S := S) c (t := .revealDhSecrets) trivial nofun nofun
      have hQ : (authCodec S).qenc .revealDhSecrets =
          .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (embedVal .unit ()))))))))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]
      dsimp only [_root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC, caseSumV, v, Comp.eval,
        Expr.eval, Ext.step_wk, Ext.refl_wk, Expr.v1,
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.aNoneAtomicE,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aNone, map_pure, forgetCk, Prod.map]
      simp only [env_get_succ, env_get_zero, map_pure]
      refine ⟨by simp only [Prod.map, forgetCk, hs1, embedVal]; rfl, ?_⟩
      intro p hp
      rw [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hBump, hInv.shadow_ok.mono hM0 hM1 hM2⟩
    | registerKey sk =>
      obtain ⟨hM0, hM1, hM2⟩ := bump_on_step (S := S) c (t := .registerKey sk) trivial nofun nofun
      have hQ : (authCodec S).qenc (.registerKey sk) =
          .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (embedVal (B 32) sk))))))))))) :=
        AtomicLift.authQenc_eq _
      rw [hQ]; dsimp only []
      conv =>
        arg 1; rhs
        simp only [eval_caseSumV, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authCkStep1KeyC,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      refine ckBaseArmC_sim S b
        (fun fhst x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.registerFixedKB fhst x)
        (fun fhst x => _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.registerFixedB fhst x)
        _ c _ s' _ sk hBump hM0 (Nat.le_of_succ_le hM1) (Nat.le_of_succ_le hM2) ?_ ?_ ?_ ?_
        ⟨rfl, Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed.registerFixedShadowB_sim
          tlAuthPrim id (fun _ _ y hy => ⟨y, hy, rfl⟩) S b (ckShadowFixed s') sk
          hInv.shadow_ok⟩ <;>
        rfl
  · dsimp only [prfCkOldAtomicProg, AtomicLift.liftAuth1Stage, forgetCk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkRedProg1Key,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.prfCkKindFinishC,
      Comp.eval]
    intro c s' bOut _ hInv
    simp only [Expr.eval, env_get_zero, Expr.v0, pure_bind]
    let ρf : Env (embedCtx [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy, .bool]) :=
      .cons s'.1 (.cons bOut .nil)
    rw [compRename_eval
      (mapComp tlAuthPrim (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkFinishDsl S (AuthKindFuels.ofBudget S b).K_on))
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.dropShadow1
      ρf (.cons s'.1 (.cons s' (.cons bOut .nil)))
      (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)]
    refine mapComp_congr_of_zero tlAuthPrim (fun _ => rfl) _ _ ρf ?_
    dsimp only [ρf, embedCtx, projEnv, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkFinishDsl, letV]
    iterate 3 rw [eval_letC]
    simp only [Expr.eval, env_get_succ,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckSecb,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckFhst,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid]
    let s0 := projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s'.1
    have hs1 : s'.1 = embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy s0 :=
      (AtomicLift.embedVal_projVal _ s'.1).symm
    have hSh1 : (ckShadowFixed s').1 = embedVal authHybridStateFixedTy s0.2.2.2 := by
      dsimp only [ckShadowFixed]; rw [hs1]; rfl
    have hValOn : AuthFixedValOnlineBounded (c 0) s0.2.2.2 :=
      (AuthFixedAtomOnlineBounded.iff_embedVal s0.2.2.2).mp (hSh1 ▸ hInv.shadow_ok.online_le)
    have hOnK : c 0 ≤ (AuthKindFuels.ofBudget S b).K_on := by
      have := hInv.counter_inv.on_le
      dsimp only [AuthKindFuels.ofBudget]; omega
    exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.finalizeAuthFixedKDsl_fuel_eq
      S b _ _ _ _ hValOn.base_le hValOn.initKemRecs_le hValOn.recvKemRecs_le hValOn.idealSessions_le hOnK

/-- Forgetful simulation between `prfMsgKeys1KeyKindProg` and `prfMkOldAtomicProg`. -/
theorem prfMsgKeys1KeyKindProg_forgetSim (S : Setup) (b : QueryBudget) (x : Unit) :
    ForgetSim (prfMsgKeys1KeyKindProg S b) (prfMkOldAtomicProg S b)
      forgetMk (authSimPred S) (authSimBounds b) x (AuthMkInv S b) := by
  exact _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfMk.prfMsgKeys1KeyKindProg_forgetSim S b x

/-- Forgetful simulation between `prfHmac1KeyKindProg` and `prfHmacOldAtomicProg`. -/
theorem prfHmac1KeyKindProg_forgetSim (S : Setup) (b : QueryBudget) (x : Unit) :
    ForgetSim (prfHmac1KeyKindProg S b) (prfHmacOldAtomicProg S b)
      forgetHm (authSimPred S) (authSimBounds b) x (AuthHmInv S b) := by
  exact _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfInt.prfHmac1KeyKindProg_forgetSim S b x

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrf
