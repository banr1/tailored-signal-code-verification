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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac

/-!
# Tag-Lift, Renaming, and Session Evaluation Helpers for `Auth` PRF Reductions

Proves `TagLift` evaluation (`lift1_eval`), context-renaming combinators, and two-environment
`Comp.eval` congruences for shared `Auth` hybrid handshake and random-oracle operations, along
with fuel-equivalence and leaf-preservation lemmas for `PrfMsgKeys` send and receive helpers.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.ReductionDsl.StepSim
  (ForgetSim bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal projVal embedCtx embedEnv mapComp
   liftRen compRename compRename_eval exprRename exprRename_eval
   comp_queries_zero_of_zero mapComp_eval liftAuthHandle_eval
   aiAuthPrim aiPrfMk aiPrfHmac tlAuthPrim tlPrfMk tlPrfHmac)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery authSpec)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface pqPrfMkIface pqPrfHmacIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT v letV bindV caseOptV caseSumV eval_letC AllLeaves
   liftPrimComp eval_liftPrimComp samplePrim queryPrim
   authStateTy preKeyBundleTy sendQTy recvQTy
   authHybridStateTy authHybridStateFixedTy RSF
   asPrincipals asSpkBundles asOpkEntries asSessions asUsedSendSessions
   asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples asSentOPKEvents
   asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents asRoCache asRootRoCache asAdvKeys
   eAny eFind eMap natEq nat2Eq nat3Eq sidEq sameSaltKeyE bytesBeq boolOr
   findHonestC koskBundleOkC resolveSigPkC checkBundleSpkHonIdealC
   hkdfRoC rootRoC finishAuthHybridSendC prepareAuthHybridRecvC recvFinishTagRunC
   prfMkCoreTy prfMkStepPreTy prfMkStTy finishAuthSendMkC finishAuthRecvMkC
   finishRecvUnmatchedMkPreC prfMkStepPostC queryDeriveMk)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authFixedShadowStTy forgetAuthFixedShadow emptyRoBothAvlE
   roFixedShadowArmC roRootFixedShadowArmC syncRoBothC syncFixedShadowRespC
   fixedRoCacheE fixedRootRoCacheE)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (dropShadow0 dropShadow1 liftAuthPrim1 liftPrfMk1 liftPrfHmac1
   authMkSendPreKB authMkRecvPreKB
   intSendPrepKC hmSendKC hmSchedPrepKC hmSchedKC hmRecvTailKC hmRecvKC
   prfMkKindInitC mkRebuildE mkBaseArmC mkPostRunC prfMkKindHandleC prfMkKindFinishC
   prfMsgKeys1KeyKindProg
   prfHmacKindInitC hmRebuildE hmBaseArmC hmPostRunC prfHmacKindHandleC prfHmacKindFinishC
   prfHmac1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv
   AuthBaseValOnlineBounded AuthFixedValOnlineBounded AuthFixedAtomOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache
   RoBothShadowRel CacheStepAtMostOne
   authMkShadowStTy authHmShadowStTy forgetMk forgetHm
   prfMkOldAtomicProg prfHmacOldAtomicProg
   AuthFixedShadowAt mkShadowFixed hmShadowFixed AuthHmShadowAt
   AuthMkInv AuthHmInv dispatchAuthQEval dispatchAuthQ_eval_qenc)
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

theorem lift1_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T} (tl : TagLift I A)
    (hZero : ∀ g, tl.unsupportedW g = 0) {a r : Ty pqSig}
    (c : Comp pqxdhOps I [a] r) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (Comp.bind (.ret e) (compRename dropShadow0 (mapComp tl c))).eval ρ =
      embedVal r <$> c.eval (.cons (projVal a (e.eval ρ)) .nil) := by
  dsimp only [Comp.eval]
  rw [pure_bind, compRename_eval (mapComp tl c) dropShadow0
    (.cons (e.eval ρ) .nil) (.cons (e.eval ρ) ρ)
    (fun | .zero => rfl | .succ v => nomatch v)]
  exact mapComp_eval_of_zero tl hZero c (.cons (e.eval ρ) .nil)

def ren2 {Δ : List PT} {A B : PT} (vA : Var Δ A) (vB : Var Δ B) :
    ∀ {t}, Var [A, B] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB

def ren4 {Δ : List PT} {A B C D : PT}
    (vA : Var Δ A) (vB : Var Δ B) (vC : Var Δ C) (vD : Var Δ D) :
    ∀ {t}, Var [A, B, C, D] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB
  | _, .succ (.succ .zero) => vC
  | _, .succ (.succ (.succ .zero)) => vD

theorem eval_ren2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} {Δ : List PT} (vA : Var Δ A) (vB : Var Δ B)
    (c0 : Comp pqxdhOps I [A, B] R) (c : Comp pqxdhOps I Δ R) (env : Env Δ)
    (hEq : compRename (ren2 vA vB) c0 = c) :
    c.eval env = c0.eval (.cons (env.get vA) (.cons (env.get vB) .nil)) := by
  rw [← hEq]
  exact compRename_eval c0 (ren2 vA vB) _ env
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)

theorem eval_ren4 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B C D R : PT} {Δ : List PT}
    (vA : Var Δ A) (vB : Var Δ B) (vC : Var Δ C) (vD : Var Δ D)
    (c0 : Comp pqxdhOps I [A, B, C, D] R) (c : Comp pqxdhOps I Δ R) (env : Env Δ)
    (hEq : compRename (ren4 vA vB vC vD) c0 = c) :
    c.eval env =
      c0.eval (.cons (env.get vA) (.cons (env.get vB) (.cons (env.get vC) (.cons (env.get vD) .nil)))) := by
  rw [← hEq]
  exact compRename_eval c0 (ren4 vA vB vC vD) _ env
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ .zero) => rfl
         | .succ (.succ (.succ .zero)) => rfl | .succ (.succ (.succ (.succ v))) => nomatch v)

private abbrev env_get_succ := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ
private abbrev env_get_zero := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero

private theorem caseOptV_congr_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {o₁ o₂ : Expr pqxdhOps Γ (.opt τ₁)} {kn₁ kn₂ : Comp pqxdhOps I Γ τ₂}
    {ks₁ ks₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (ho : o₁.eval env = o₂.eval env) (hkn : kn₁.eval env = kn₂.eval env)
    (hks : ∀ x : τ₁.denote, o₂.eval env = some x →
      (ks₁ .zero).eval (.cons x env) = (ks₂ .zero).eval (.cons x env)) :
    (caseOptV o₁ kn₁ ks₁).eval env = (caseOptV o₂ kn₂ ks₂).eval env := by
  simp only [caseOptV, Comp.eval, ho]
  cases h : o₂.eval env with | none => exact hkn | some x => exact hks x h

private theorem ret_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT} {P : τ.denote → Prop}
    {e : Expr pqxdhOps Γ τ} {env : Env Γ} (hP : P (e.eval env)) :
    AllLeaves P ((Comp.ret (I := I) e).eval env) :=
  AllLeaves.pure hP

theorem letV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {e₁ : Expr pqxdhOps Δ₁ τ₁} {e₂ : Expr pqxdhOps Δ₂ τ₁}
    {b₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {b₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (he : e₁.eval env₁ = e₂.eval env₂)
    (hb : ∀ x : τ₁.denote, (b₁ .zero).eval (.cons x env₁) = (b₂ .zero).eval (.cons x env₂)) :
    (letV e₁ b₁).eval env₁ = (letV e₂ b₂).eval env₂ := by
  rw [letV, letV, eval_letC, eval_letC, he]; exact hb _

theorem bindV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {m₁ : Comp pqxdhOps I Δ₁ τ₁} {m₂ : Comp pqxdhOps I Δ₂ τ₁}
    {b₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {b₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hm : m₁.eval env₁ = m₂.eval env₂)
    (hb : ∀ x : τ₁.denote, (b₁ .zero).eval (.cons x env₁) = (b₂ .zero).eval (.cons x env₂)) :
    (bindV m₁ b₁).eval env₁ = (bindV m₂ b₂).eval env₂ := by
  simp only [bindV, Comp.eval, hm]; congr 1; funext x; exact hb x

theorem caseOptV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {o₁ : Expr pqxdhOps Δ₁ (.opt τ₁)} {o₂ : Expr pqxdhOps Δ₂ (.opt τ₁)}
    {kn₁ : Comp pqxdhOps I Δ₁ τ₂} {kn₂ : Comp pqxdhOps I Δ₂ τ₂}
    {ks₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {ks₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (ho : o₁.eval env₁ = o₂.eval env₂) (hkn : kn₁.eval env₁ = kn₂.eval env₂)
    (hks : ∀ x : τ₁.denote, (ks₁ .zero).eval (.cons x env₁) = (ks₂ .zero).eval (.cons x env₂)) :
    (caseOptV o₁ kn₁ ks₁).eval env₁ = (caseOptV o₂ kn₂ ks₂).eval env₂ := by
  simp only [caseOptV, Comp.eval, ho]; cases o₂.eval env₂ with | none => exact hkn | some x => exact hks x

theorem ite_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ : PT}
    {c₁ : Expr pqxdhOps Δ₁ .bool} {c₂ : Expr pqxdhOps Δ₂ .bool}
    {t₁ e₁ : Comp pqxdhOps I Δ₁ τ} {t₂ e₂ : Comp pqxdhOps I Δ₂ τ}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hc : c₁.eval env₁ = c₂.eval env₂) (ht : t₁.eval env₁ = t₂.eval env₂)
    (he : e₁.eval env₁ = e₂.eval env₂) :
    (Comp.ite c₁ t₁ e₁).eval env₁ = (Comp.ite c₂ t₂ e₂).eval env₂ := by
  simp only [Comp.eval, hc]; cases c₂.eval env₂ with | true => exact ht | false => exact he

theorem ret_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ : PT}
    {e₁ : Expr pqxdhOps Δ₁ τ} {e₂ : Expr pqxdhOps Δ₂ τ}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂} (he : e₁.eval env₁ = e₂.eval env₂) :
    (Comp.ret (I := I) e₁).eval env₁ = (Comp.ret (I := I) e₂).eval env₂ := by
  simp only [Comp.eval, he]

theorem letV_body_ren2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} {Δ₁ Δ₂ : List PT}
    (vB₁ : Var Δ₁ B) (eA₁ : Expr pqxdhOps Δ₁ A) (env₁ : Env Δ₁)
    (vB₂ : Var Δ₂ B) (eA₂ : Expr pqxdhOps Δ₂ A) (env₂ : Env Δ₂)
    (b0 : Var [A, B] A → Comp pqxdhOps I [A, B] R)
    (b₁ : Var (A :: Δ₁) A → Comp pqxdhOps I (A :: Δ₁) R)
    (b₂ : Var (A :: Δ₂) A → Comp pqxdhOps I (A :: Δ₂) R)
    (hEq₁ : compRename (ren2 .zero (.succ vB₁)) (b0 .zero) = b₁ .zero)
    (hEq₂ : compRename (ren2 .zero (.succ vB₂)) (b0 .zero) = b₂ .zero)
    (hB : env₁.get vB₁ = env₂.get vB₂)
    (hA : eA₁.eval env₁ = eA₂.eval env₂) :
    (letV eA₁ b₁).eval env₁ = (letV eA₂ b₂).eval env₂ := by
  rw [letV, letV, eval_letC, eval_letC,
    eval_ren2 .zero (.succ vB₁) (b0 .zero) (b₁ .zero) (.cons (eA₁.eval env₁) env₁) hEq₁,
    eval_ren2 .zero (.succ vB₂) (b0 .zero) (b₂ .zero) (.cons (eA₂.eval env₂) env₂) hEq₂]
  simp [hA, hB]

theorem hkdfRoC_eval_congr (K : ℕ) {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (sec₁ : Expr pqxdhOps Δ₁ (B 192)) (env₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (sec₂ : Expr pqxdhOps Δ₂ (B 192)) (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₂.wk st₂))
    (hsec : sec₁.eval env₁ = sec₂.eval env₂) :
    (hkdfRoC K st₁ sec₁).eval env₁ = (hkdfRoC K st₂ sec₂).eval env₂ := by
  unfold hkdfRoC
  exact letV_body_ren2 (h₁.wk st₁) sec₁ env₁ (h₂.wk st₂) sec₂ env₂
    (fun sec => by
      let st : Var [authStateTy] authStateTy := .zero
      exact caseOptV (eFind K (asRoCache (v st)) fun e => bytesBeq 192 (.fst (v e)) (v sec))
        (bindV (samplePrim .drKey96) fun dk =>
          .ret (.pair (v dk) (.cons (.pair (v sec) (v dk)) (asRoCache (v st)))))
        fun e => .ret (.pair (.snd (v e)) (asRoCache (v st))))
    _ _ rfl rfl hst hsec

theorem rootRoC_eval_congr (K : ℕ) {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (rk₁ dh₁ : Expr pqxdhOps Δ₁ (B 32)) (env₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (rk₂ dh₂ : Expr pqxdhOps Δ₂ (B 32)) (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₂.wk st₂))
    (hrk : rk₁.eval env₁ = rk₂.eval env₂) (hdh : dh₁.eval env₁ = dh₂.eval env₂) :
    (rootRoC K st₁ rk₁ dh₁).eval env₁ = (rootRoC K st₂ rk₂ dh₂).eval env₂ := by
  unfold rootRoC
  exact letV_body_ren2 (h₁.wk st₁) (.pair rk₁ dh₁) env₁ (h₂.wk st₂) (.pair rk₂ dh₂) env₂
    (fun inp => by
      let st : Var [authStateTy] authStateTy := .zero
      exact caseOptV (eFind K (asRootRoCache (v st)) fun e =>
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytes2Eq (.fst (v e)) (v inp))
        (bindV (samplePrim .bytes32) fun rk1 => bindV (samplePrim .bytes32) fun ck1 =>
          .ret (.pair (.pair (v rk1) (v ck1)) (.cons (.pair (v inp) (.pair (v rk1) (v ck1)))
            (asRootRoCache (v st)))))
        fun e => .ret (.pair (.snd (v e)) (asRootRoCache (v st))))
    _ _ rfl rfl hst (by simp [Expr.eval, hrk, hdh])

theorem prepareAuthHybridRecvC_eval_congr (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (hst₁ : Var Γ₁ authHybridStateTy) (x₁ : Var Γ₂ recvQTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁]
    (env₁ : Env Δ₁)
    (hst₂ : Var Γ₃ authHybridStateTy) (x₂ : Var Γ₄ recvQTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂]
    (env₂ : Env Δ₂)
    (hhst : env₁.get (h₁.wk hst₁) = env₂.get (h₃.wk hst₂))
    (hx : env₁.get (h₂.wk x₁) = env₂.get (h₄.wk x₂)) :
    (prepareAuthHybridRecvC S K opk hst₁ x₁).eval env₁ =
      (prepareAuthHybridRecvC S K opk hst₂ x₂).eval env₂ := by
  have hr₁ := eval_ren2 (h₁.wk hst₁) (h₂.wk x₁)
    (prepareAuthHybridRecvC S K opk
      (Γ₁ := [authHybridStateTy, recvQTy]) (Γ₂ := [recvQTy]) .zero .zero)
    (prepareAuthHybridRecvC S K opk hst₁ x₁) env₁ (by cases opk <;> rfl)
  have hr₂ := eval_ren2 (h₃.wk hst₂) (h₄.wk x₂)
    (prepareAuthHybridRecvC S K opk
      (Γ₁ := [authHybridStateTy, recvQTy]) (Γ₂ := [recvQTy]) .zero .zero)
    (prepareAuthHybridRecvC S K opk hst₂ x₂) env₂ (by cases opk <;> rfl)
  rw [hr₁, hr₂, hhst, hx]

private def ren3 {Δ : List PT} {A B C : PT} (vA : Var Δ A) (vB : Var Δ B) (vC : Var Δ C) :
    ∀ {t}, Var [A, B, C] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB
  | _, .succ (.succ .zero) => vC

private def psortEq : (a b : _root_.SignalPqxdh.LegacyCosted.PSort) → Option (PLift (a = b))
  | .u32, .u32 => some (.up rfl)
  | .bytes w₁, .bytes w₂ =>
      match decEq w₁.1 w₂.1 with
      | isTrue h => some (.up (congrArg _ (Subtype.ext h)))
      | isFalse _ => none
  | _, _ => none

private def ptEq : (a b : PT) → Option (PLift (a = b))
  | .unit, .unit => some (.up rfl)
  | .bool, .bool => some (.up rfl)
  | .nat, .nat => some (.up rfl)
  | .base s₁, .base s₂ =>
      match psortEq s₁ s₂ with
      | some (.up h) => some (.up (congrArg _ h))
      | none => none
  | .prod a₁ b₁, .prod a₂ b₂ =>
      match ptEq a₁ a₂, ptEq b₁ b₂ with
      | some (.up h₁), some (.up h₂) => some (.up (h₁ ▸ h₂ ▸ rfl))
      | _, _ => none
  | .sum a₁ b₁, .sum a₂ b₂ =>
      match ptEq a₁ a₂, ptEq b₁ b₂ with
      | some (.up h₁), some (.up h₂) => some (.up (h₁ ▸ h₂ ▸ rfl))
      | _, _ => none
  | .opt a₁, .opt a₂ =>
      match ptEq a₁ a₂ with
      | some (.up h) => some (.up (congrArg _ h))
      | none => none
  | .list a₁, .list a₂ =>
      match ptEq a₁ a₂ with
      | some (.up h) => some (.up (congrArg _ h))
      | none => none
  | _, _ => none

private def unlet3 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} (c : Comp pqxdhOps I [A, B] R) :
    Option (Comp pqxdhOps I [A, A, B] R) :=
  match c with
  | .bind (t := τ₁) _ k =>
      match ptEq τ₁ A with
      | some (.up h) => some (h ▸ k)
      | none => none
  | _ => none

private theorem eval_unlet3_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} {Δ₁ Δ₂ : List PT}
    (uk : Option (Comp pqxdhOps I [A, A, B] R))
    (vB₁ : Var Δ₁ B) (eA₁ : Expr pqxdhOps Δ₁ A) (env₁ : Env Δ₁)
    (b₁ : Var (A :: Δ₁) A → Comp pqxdhOps I (A :: Δ₁) R)
    (vB₂ : Var Δ₂ B) (eA₂ : Expr pqxdhOps Δ₂ A) (env₂ : Env Δ₂)
    (b₂ : Var (A :: Δ₂) A → Comp pqxdhOps I (A :: Δ₂) R)
    (hEq₁ : uk.map (compRename (ren3 .zero .zero (.succ vB₁))) = some (b₁ .zero))
    (hEq₂ : uk.map (compRename (ren3 .zero .zero (.succ vB₂))) = some (b₂ .zero))
    (hB : env₁.get vB₁ = env₂.get vB₂)
    (hA : eA₁.eval env₁ = eA₂.eval env₂) :
    (letV eA₁ b₁).eval env₁ = (letV eA₂ b₂).eval env₂ := by
  cases uk with
  | none => cases hEq₁
  | some k0 =>
    injection hEq₁ with hEq₁
    injection hEq₂ with hEq₂
    have step1 : ∀ {Δ : List PT} (vB : Var Δ B) (eA : Expr pqxdhOps Δ A) (env : Env Δ)
        (b : Var (A :: Δ) A → Comp pqxdhOps I (A :: Δ) R),
        compRename (ren3 .zero .zero (.succ vB)) k0 = b .zero →
        (letV eA b).eval env =
          k0.eval (.cons (eA.eval env) (.cons (eA.eval env) (.cons (env.get vB) .nil))) := by
      intro Δ vB eA env b hEq
      rw [letV, eval_letC, ← hEq]
      refine compRename_eval k0 (ren3 .zero .zero (.succ vB)) _ _ ?_
      intro t v
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => cases v with
          | zero => rfl
          | succ v => nomatch v
    rw [step1 vB₁ eA₁ env₁ b₁ hEq₁, step1 vB₂ eA₂ env₂ b₂ hEq₂, hA, hB]

theorem recvFinishTagRunC_eval_congr (S : Setup) (K : ℕ)
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (tag₁ : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy)
    [h₁ : Ext Γ₁ Δ₁]
    (res₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishResTy)
    (env₁ : Env Δ₁)
    (tag₂ : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy)
    [h₂ : Ext Γ₂ Δ₂]
    (res₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishResTy)
    (env₂ : Env Δ₂)
    (htag : env₁.get (h₁.wk tag₁) = env₂.get (h₂.wk tag₂))
    (hres : res₁.eval env₁ = res₂.eval env₂) :
    (recvFinishTagRunC S K tag₁ res₁).eval env₁ =
      (recvFinishTagRunC S K tag₂ res₂).eval env₂ := by
  let c0 := recvFinishTagRunC S K
    (Γ₁ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy])
    (Δ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishResTy,
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy])
    .zero (.var .zero)
  unfold recvFinishTagRunC
  refine eval_unlet3_congr (unlet3 c0) (h₁.wk tag₁) res₁ env₁ _ (h₂.wk tag₂) res₂ env₂ _ ?_ ?_ htag hres <;> rfl

set_option maxRecDepth 4096 in
theorem finishAuthHybridSendC_eval_congr (S : Setup) (K : ℕ)
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (hst₁ : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateTy)
    [h₁ : Ext Γ₁ Δ₁]
    (args₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishSendArgsTy)
    (env₁ : Env Δ₁)
    (hst₂ : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateTy)
    [h₂ : Ext Γ₂ Δ₂]
    (args₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishSendArgsTy)
    (env₂ : Env Δ₂)
    (hhst : env₁.get (h₁.wk hst₁) = env₂.get (h₂.wk hst₂))
    (hargs : args₁.eval env₁ = args₂.eval env₂) :
    (finishAuthHybridSendC S K hst₁ args₁).eval env₁ =
      (finishAuthHybridSendC S K hst₂ args₂).eval env₂ := by
  let c0 := finishAuthHybridSendC S K
    (Γ₁ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateTy])
    (Δ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishSendArgsTy,
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateTy])
    .zero (.var .zero)
  unfold finishAuthHybridSendC
  refine eval_unlet3_congr (unlet3 c0) (h₁.wk hst₁) args₁ env₁ _ (h₂.wk hst₂) args₂ env₂ _ ?_ ?_ hhst hargs <;> rfl

private theorem fixed_toHybrid {n : ℕ} {fhst : authHybridStateFixedTy.denote}
    (hb : AuthFixedValOnlineBounded n fhst) : AuthHybridValOnlineBounded n fhst.1 :=
  ⟨hb.base_le, hb.initKemRecs_le, hb.recvKemRecs_le, hb.idealSessions_le⟩

private theorem finishAuthSendMkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) [h₁_ext : Ext Γ₁ Δ]
    (sid : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sessionIdTy)
    (uE : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.principalEntryTy)))
    (isFresh : Expr pqxdhOps Δ .bool) (bu : Expr pqxdhOps Δ preKeyBundleTy)
    (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.keys6Ty)
    (drKey : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32))
    (mks : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.msgKeysTy)
    (env : Env Δ) (hb : AuthFixedValOnlineBounded n (env.get (h₁_ext.wk fhst)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (finishAuthSendMkC S K₁ fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
        spqrSalt? pqMsg msgPlain mks).eval env =
      (finishAuthSendMkC S K₂ fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
        spqrSalt? pqMsg msgPlain mks).eval env := by
  unfold finishAuthSendMkC
  refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun hst hhst => ?_
  have hbHst : AuthHybridValOnlineBounded n hst := by
    have : hst = (env.get (h₁_ext.wk fhst)).1 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhst
    rw [this]; exact fixed_toHybrid hb
  iterate 18 refine letV_congr rfl fun _ => ?_
  refine bindV_congr rfl fun _ => ?_
  apply bindV_congr
  · apply finishAuthHybridSendC_fuel_eq (n := n)
    · rfl
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbHst
    · exact h₁
    · exact h₂
  · intro _; rfl

private theorem finishAuthSendMkC_leaves (S : Setup) (K : ℕ) {n : ℕ} {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) [h₁_ext : Ext Γ₁ Δ]
    (sid : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sessionIdTy)
    (uE : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.principalEntryTy)))
    (isFresh : Expr pqxdhOps Δ .bool) (bu : Expr pqxdhOps Δ preKeyBundleTy)
    (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.keys6Ty)
    (drKey : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32))
    (mks : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.msgKeysTy)
    (env : Env Δ) (hb : AuthFixedValOnlineBounded n (env.get (h₁_ext.wk fhst))) :
    let fhst0 := env.get (h₁_ext.wk fhst)
    AllLeaves (fun res =>
      AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne (valRoCache fhst0.1.1) (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valRootRoCache res.2.1.1))
      ((finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
          spqrSalt? pqMsg msgPlain mks).eval env) := by
  intro fhst0
  unfold finishAuthSendMkC
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun hst hhst => ?_
  have hhstEq : hst = fhst0.1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, fhst0] using hhst
  refine letV_allLeaves_eq fun st hstBase => ?_
  have hstEq : st = fhst0.1.1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hstBase
  iterate 17 refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  apply bindV_allLeaves
  · apply finishAuthHybridSendC_leaves (n := n)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using fixed_toHybrid hb
    · simpa [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero, hhstEq, hstEq] using CacheStepAtMostOne.refl (valRoCache fhst0.1.1)
    · simpa [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero, hhstEq, hstEq] using CacheStepAtMostOne.refl (valRootRoCache fhst0.1.1)
  · rintro out ⟨hOutB, hOutRo, hOutRoot⟩
    have hOutRo' : CacheStepAtMostOne (valRoCache fhst0.1.1) (valRoCache out.2.1) := by
      simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hOutRo
    have hOutRoot' : CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valRootRoCache out.2.1) := by
      simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hOutRoot
    refine ret_allLeaves ?_
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfRecvCount,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSaltCache,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, fhst0]
    exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le,
      Nat.le_trans hb.mkSaltCache_le (Nat.le_succ n)⟩, hOutRo', hOutRoot'⟩

private theorem finishAuthRecvMkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyMsgTy)
    (prep : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preparedAuthRecvTy)
    [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ]
    (drKey : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
    (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authMkSaltCacheTy)
    (mks : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.msgKeysTy)
    (env : Env Δ) (hPrep : PreparedRecvValBounded n ro0 root0 (env.get (h₂_ext.wk prep)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (finishAuthRecvMkC S K₁ msg prep drKey rk1 ck1_1 rc' cache' mks).eval env =
      (finishAuthRecvMkC S K₂ msg prep drKey rk1 ck1_1 rc' cache' mks).eval env := by
  unfold finishAuthRecvMkC
  iterate 8 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun fTag hfTag => ?_
  have hbTag : RecvTagValBounded n ro0 root0 fTag := by
    have : fTag = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.2 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTag
    rw [this]; exact hPrep.tag_bounded
  refine letV_congr rfl fun _ => ?_
  refine bindV_congr rfl fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  apply bindV_congr
  · apply recvFinishTagRunC_fuel_eq (n := n) (ro0 := ro0) (root0 := root0)
    · rfl
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag
    · exact h₁
    · exact h₂
  · intro _; rfl

private theorem finishAuthRecvMkC_leaves (S : Setup) (K : ℕ) {n : ℕ}
    {ro0 : List (List UInt8 × _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyMsgTy)
    (prep : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preparedAuthRecvTy)
    [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ]
    (drKey : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
    (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authMkSaltCacheTy)
    (mks : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.msgKeysTy)
    (env : Env Δ) (hPrep : PreparedRecvValBounded n ro0 root0 (env.get (h₂_ext.wk prep)))
    (hCache : (cache'.eval env).length ≤ n + 1) :
    AllLeaves (fun res =>
      AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne ro0 (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne root0 (valRootRoCache res.2.1.1))
      ((finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).eval env) := by
  unfold finishAuthRecvMkC
  refine letV_allLeaves_eq fun a ha => ?_
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun cVal hcVal => ?_
  have hcLen : cVal.length ≤ n + 1 := by
    have : cVal = cache'.eval env := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, ha] using hcVal
    rwa [this]
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hstEq => ?_
  have hstVal : st = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.1.1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parHstDec, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
  refine letV_allLeaves_eq fun fTag hfTag => ?_
  have hbTag : RecvTagValBounded n ro0 root0 fTag := by
    have : fTag = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.2 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.parFinishTag, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTag
    rw [this]; exact hPrep.tag_bounded
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
    | none => simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eCaseOpt, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk] at hResEq
    | some pt =>
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eCaseOpt, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, Option.some.injEq] at hResEq
      subst hResEq
      refine ⟨?_, ?_⟩
      · simpa [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hstVal] using
          (hPrep.ro_eq ▸ CacheStepAtMostOne.refl (valRoCache _))
      · simpa [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hstVal] using
          (hPrep.root_eq ▸ CacheStepAtMostOne.refl (valRootRoCache _))
  · refine ret_allLeaves ?_
    simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    exact ⟨⟨hhOut.base_le, hhOut.initKemRecs_le, hhOut.recvKemRecs_le, hhOut.idealSessions_le,
      hcLen⟩, hRoOut, hRootOut⟩

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm
