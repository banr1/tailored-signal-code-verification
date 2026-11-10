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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo

/-!
# Forgetful Step-Simulation for One-Key `Auth` `PrfMsgKeys`

Proves `prfMsgKeys1KeyKindProg_forgetSim`, establishing `ForgetSim` of `prfMsgKeys1KeyKindProg`
against `prfMkOldAtomicProg` under `forgetMk` and `AuthMkInv`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfMk

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.ReductionDsl.StepSim (ForgetSim bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal projVal embedVal_projVal projVal_embedVal embedEnv
   exprRename_eval mapComp mapComp_eval
   compRename compRename_eval comp_queries_zero_of_zero
   aiPrfMk tlPrfMk liftAuthHandle liftAuthHandle_eval)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery authSpec)
open _root_.SignalPqxdh.Costed (authCodec pqPrfMkIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B msgKeyPrfOracle)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT v letV bindV caseOptV caseSumV eval_letC AllLeaves liftPrimComp eval_liftPrimComp
   embedPrim_pure embedPrim_bind
   sampleChal samplePrim queryPrim natEq natLt aNone boolOr isSomeE bytesLen litB
   eLet eLet2 eCaseOpt eCaseSum eFind eAny bytesBeq sidEq sameSaltKeyE_eval firstMsgADE_eval buildSecretsE_eval
   natEq_eval nat2Eq_eval nat3Eq_eval bytesLen_eval bytesBeq_eval encEC_eval encKEM_eval boolOr_eval
   emptyAuthHybridStFixedE authStateTy authRespTy authQueryTy preKeyBundleTy sendQTy recvQTy
   sessionIdTy principalEntryTy keys6Ty drKeyTy preKeyMsgTy preparedAuthRecvTy
   authMkSaltCacheTy authSlotStateTy
   asPrincipals asSpkBundles asUsedSendSessions asRoCache asRootRoCache asHasWonAuth asSecb
   authHybridStateTy authHybridStateFixedTy RSF
   prfMkStTy prfMkCoreTy prfMkStepPreTy prfMkChalContTy msgKeysTy
   mkcSecb mkcIdx mkcSentChal mkcFhst mkcMk ahsfMk
   ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots ahsfUpd ahsfUpdSlots ahsfMkSlots ahsBase
   parHstDec parFinishTag parMatchedSess? parIsUncorrSender parSameEph parSecrets parDhRatchet parKEntry
   iasSid iasSpqrSalt? iasDrKey iasRk1 iasMkSeed iasCk1_1 iasMsgKeys
   pkmPqRatchetMsg pkmAeadCt pkmEphAPk pkmHdr hdrIkAPk
   peIkAPk peSecIKA0 peCorrupted pkbIkB pkbSpkB pkbSpkSig pkbPqspkB pkbPqspkSig pkbOpkB? sbPqspkPk
   encEC encKEM sendGuardE allocSendSlotE allocRecvSlotE lookupSendSlotOrZeroE
   initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB
   roFixedB roRootFixedB registerFixedB
   findHonestC koskBundleOkC resolveSigPkC checkBundleSpkHonIdealC hkdfRoC rootRoC
   recvFinishTagRunC prepareAuthHybridRecvC finishAuthHybridSendC
   finishAuthSendMkC finishAuthRecvMkC finishRecvUnmatchedMkPreC
   authMkSendPreB authMkRecvPreB prfMkStepPostC queryDeriveMk
   prfMsgKeysInitDslK prfMsgKeysFinishDsl finalizeAuthFixedDsl
   prfMkStepPre1KeyC prfMsgKeysHandle1KeyDsl prfMsgKeysRedProg1Key wrapMkBase)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authFixedAtomicTy authFixedShadowStTy emptyRoBothAvlE forgetAuthFixedShadow
   liftExpr1 aNoneAtomicE fixedRoCacheE fixedRootRoCacheE syncRoBothC roFixedShadowArmC roRootFixedShadowArmC
   authSendQAtomicTy authRecvQAtomicTy finalizeAuthFixedKDsl
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv
   AuthBaseValOnlineBounded AuthFixedValOnlineBounded AuthFixedAtomOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache
   RoBothShadowRel CacheStepAtMostOne AuthFixedShadowAt
   authMkShadowStTy mkShadowFixed forgetMk prfMkOldAtomicProg AuthMkInv
   dispatchAuthQEval dispatchAuthQ_eval_qenc)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (dropShadow0 dropShadow1 prfMkKindInitC prfMkKindHandleC prfMkKindFinishC
   mkRebuildE mkBaseArmC mkPostRunC liftPrfMk1
   authMkSendPreKB authMkRecvPreKB prfMsgKeys1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
  (finalizeAuthFixedKDsl_fuel_eq)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
  (initPrinFixedShadowB_sim corruptFixedShadowB_sim genSpkFixedShadowB_sim
   genOpkFixedShadowB_sim registerFixedShadowB_sim)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
  (projEnv embedEnv_projEnv mapComp_eval_of_zero mapComp_congr_of_zero mem_support_mapComp_of_zero
   AllLeaves_mem_support liftPrimComp_eval_congr mem_support_liftPrimComp
   atomRoCache_embedVal atomRootRoCache_embedVal take_eq_of_le
   findHonestC_prf_fuel_eq koskBundleOkC_fuel_eq resolveSigPkC_fuel_eq
   checkBundleSpkHonIdealC_fuel_eq hkdfRoC_fuel_eq rootRoC_fuel_eq hkdfRoC_step rootRoC_step
   letV_congr letV_congr_eq letV_allLeaves letV_allLeaves_eq
   bindV_congr bindV_congr_leaves bindV_allLeaves_const bindV_allLeaves
   caseSumV_congr caseSumV_congr_eq caseSumV_allLeaves caseSumV_allLeaves_eq
   caseOptV_congr caseOptV_allLeaves caseOptV_allLeaves_eq
   ite_congr_eval ite_allLeaves
   AuthHybridValOnlineBounded RecvTagValBounded PreparedRecvValBounded
   finishAuthHybridSendC_fuel_eq finishAuthHybridSendC_leaves
   recvFinishTagRunC_fuel_eq recvFinishTagRunC_leaves
   prepareAuthHybridRecvC_fuel_eq prepareAuthHybridRecvC_leaves)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo
  (emptyRoBothAvlE_roBothShadowRel syncRoBothC_sim
   roFixedShadowArmC_sim_mk roRootFixedShadowArmC_sim_mk)

private abbrev env_get_succ := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ
private abbrev env_get_zero := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero

private def ren2 {Δ : List PT} {A B : PT} (vA : Var Δ A) (vB : Var Δ B) :
    ∀ {t}, Var [A, B] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB

private theorem lift1_eval {a r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftPrfMk1 c e).eval ρ = embedVal r <$> c.eval (.cons (projVal a (e.eval ρ)) .nil) := by
  dsimp only [liftPrfMk1, Comp.eval]
  erw [pure_bind, compRename_eval (mapComp tlPrfMk c) dropShadow0
    (.cons (e.eval ρ) .nil) (.cons (e.eval ρ) ρ)
    (fun | .zero => rfl | .succ v => nomatch v)]
  exact mapComp_eval_of_zero tlPrfMk (fun _ => rfl) c (.cons (e.eval ρ) .nil)

private theorem eval_ren2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} {Δ : List PT} (vA : Var Δ A) (vB : Var Δ B)
    (c0 : Comp pqxdhOps I [A, B] R) (c : Comp pqxdhOps I Δ R) (env : Env Δ)
    (hEq : compRename (ren2 vA vB) c0 = c) :
    c.eval env = c0.eval (.cons (env.get vA) (.cons (env.get vB) .nil)) := by
  rw [← hEq]
  exact compRename_eval c0 (ren2 vA vB) _ env
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)

private theorem ret_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT} {P : τ.denote → Prop}
    {e : Expr pqxdhOps Γ τ} {env : Env Γ} (hP : P (e.eval env)) :
    AllLeaves P ((Comp.ret (I := I) e).eval env) :=
  AllLeaves.pure hP

private theorem letV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {e₁ : Expr pqxdhOps Δ₁ τ₁} {e₂ : Expr pqxdhOps Δ₂ τ₁}
    {b₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {b₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (he : e₁.eval env₁ = e₂.eval env₂)
    (hb : ∀ x : τ₁.denote, (b₁ .zero).eval (.cons x env₁) = (b₂ .zero).eval (.cons x env₂)) :
    (letV e₁ b₁).eval env₁ = (letV e₂ b₂).eval env₂ := by
  rw [letV, letV, eval_letC, eval_letC, he]; exact hb _

private theorem letV_congr₂_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {e₁ : Expr pqxdhOps Δ₁ τ₁} {e₂ : Expr pqxdhOps Δ₂ τ₁}
    {b₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {b₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (he : e₁.eval env₁ = e₂.eval env₂)
    (hb : ∀ x : τ₁.denote, e₁.eval env₁ = x →
      (b₁ .zero).eval (.cons x env₁) = (b₂ .zero).eval (.cons x env₂)) :
    (letV e₁ b₁).eval env₁ = (letV e₂ b₂).eval env₂ := by
  rw [letV, letV, eval_letC, eval_letC, ← he]; exact hb _ rfl

private theorem bindV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {m₁ : Comp pqxdhOps I Δ₁ τ₁} {m₂ : Comp pqxdhOps I Δ₂ τ₁}
    {b₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {b₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hm : m₁.eval env₁ = m₂.eval env₂)
    (hb : ∀ x : τ₁.denote, (b₁ .zero).eval (.cons x env₁) = (b₂ .zero).eval (.cons x env₂)) :
    (bindV m₁ b₁).eval env₁ = (bindV m₂ b₂).eval env₂ := by
  simp only [bindV, Comp.eval, hm]; congr 1; funext x; exact hb x

private theorem bindV_congr₂_leaves {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT} {P : τ₁.denote → Prop}
    {m₁ : Comp pqxdhOps I Δ₁ τ₁} {m₂ : Comp pqxdhOps I Δ₂ τ₁}
    {b₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {b₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hm : m₁.eval env₁ = m₂.eval env₂) (hP : AllLeaves P (m₁.eval env₁))
    (hb : ∀ x : τ₁.denote, P x → (b₁ .zero).eval (.cons x env₁) = (b₂ .zero).eval (.cons x env₂)) :
    (bindV m₁ b₁).eval env₁ = (bindV m₂ b₂).eval env₂ := by
  simp only [bindV, Comp.eval, ← hm]
  exact _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allLeaves_bind_congr hP hb

private theorem caseOptV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
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

private theorem caseOptV_congr₂_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ₁ τ₂ : PT}
    {o₁ : Expr pqxdhOps Δ₁ (.opt τ₁)} {o₂ : Expr pqxdhOps Δ₂ (.opt τ₁)}
    {kn₁ : Comp pqxdhOps I Δ₁ τ₂} {kn₂ : Comp pqxdhOps I Δ₂ τ₂}
    {ks₁ : Var (τ₁ :: Δ₁) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₁) τ₂}
    {ks₂ : Var (τ₁ :: Δ₂) τ₁ → Comp pqxdhOps I (τ₁ :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (ho : o₁.eval env₁ = o₂.eval env₂) (hkn : kn₁.eval env₁ = kn₂.eval env₂)
    (hks : ∀ x : τ₁.denote, o₁.eval env₁ = some x →
      (ks₁ .zero).eval (.cons x env₁) = (ks₂ .zero).eval (.cons x env₂)) :
    (caseOptV o₁ kn₁ ks₁).eval env₁ = (caseOptV o₂ kn₂ ks₂).eval env₂ := by
  simp only [caseOptV, Comp.eval, ← ho]
  cases h : o₁.eval env₁ with | none => exact hkn | some x => exact hks x h

private theorem caseSumV_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {α β τ : PT}
    {s₁ : Expr pqxdhOps Δ₁ (.sum α β)} {s₂ : Expr pqxdhOps Δ₂ (.sum α β)}
    {kl₁ : Var (α :: Δ₁) α → Comp pqxdhOps I (α :: Δ₁) τ}
    {kl₂ : Var (α :: Δ₂) α → Comp pqxdhOps I (α :: Δ₂) τ}
    {kr₁ : Var (β :: Δ₁) β → Comp pqxdhOps I (β :: Δ₁) τ}
    {kr₂ : Var (β :: Δ₂) β → Comp pqxdhOps I (β :: Δ₂) τ}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hs : s₁.eval env₁ = s₂.eval env₂)
    (hl : ∀ x, s₁.eval env₁ = .inl x → (kl₁ .zero).eval (.cons x env₁) = (kl₂ .zero).eval (.cons x env₂))
    (hr : ∀ y, s₁.eval env₁ = .inr y → (kr₁ .zero).eval (.cons y env₁) = (kr₂ .zero).eval (.cons y env₂)) :
    (caseSumV s₁ kl₁ kr₁).eval env₁ = (caseSumV s₂ kl₂ kr₂).eval env₂ := by
  simp only [caseSumV, Comp.eval, ← hs]
  cases h : s₁.eval env₁ with | inl x => exact hl x h | inr y => exact hr y h

private theorem ite_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ : PT}
    {c₁ : Expr pqxdhOps Δ₁ .bool} {c₂ : Expr pqxdhOps Δ₂ .bool}
    {t₁ e₁ : Comp pqxdhOps I Δ₁ τ} {t₂ e₂ : Comp pqxdhOps I Δ₂ τ}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hc : c₁.eval env₁ = c₂.eval env₂) (ht : t₁.eval env₁ = t₂.eval env₂)
    (he : e₁.eval env₁ = e₂.eval env₂) :
    (Comp.ite c₁ t₁ e₁).eval env₁ = (Comp.ite c₂ t₂ e₂).eval env₂ := by
  simp only [Comp.eval, hc]; cases c₂.eval env₂ with | true => exact ht | false => exact he

private theorem ret_congr₂ {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Δ₁ Δ₂ : List PT} {τ : PT}
    {e₁ : Expr pqxdhOps Δ₁ τ} {e₂ : Expr pqxdhOps Δ₂ τ}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂} (he : e₁.eval env₁ = e₂.eval env₂) :
    (Comp.ret (I := I) e₁).eval env₁ = (Comp.ret (I := I) e₂).eval env₂ := by
  simp only [Comp.eval, he]

private theorem queryPrim_congr₂ {Δ₁ Δ₂ : List PT}
    (t : _root_.SignalPqxdh.LegacyCosted.PTag)
    {e₁ : Expr pqxdhOps Δ₁ t.dom} {e₂ : Expr pqxdhOps Δ₂ t.dom}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂} (he : e₁.eval env₁ = e₂.eval env₂) :
    (queryPrim t e₁).eval env₁ = (queryPrim t e₂).eval env₂ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queryPrim_eval, he]

private theorem letV_body_ren2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
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

private theorem hkdfRoC_eval_eq {K₁ K₂ nRo : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (sec₁ : Expr pqxdhOps Δ₁ (B 192)) (env₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (sec₂ : Expr pqxdhOps Δ₂ (B 192)) (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₂.wk st₂))
    (hsec : sec₁.eval env₁ = sec₂.eval env₂)
    (hRo : (valRoCache (env₁.get (h₁.wk st₁))).length ≤ nRo)
    (hK₁ : nRo ≤ K₁) (hK₂ : nRo ≤ K₂) :
    (hkdfRoC K₁ st₁ sec₁).eval env₁ = (hkdfRoC K₂ st₂ sec₂).eval env₂ := by
  rw [hkdfRoC_fuel_eq st₁ sec₁ env₁ hRo hK₁ hK₂]
  unfold hkdfRoC
  exact letV_body_ren2 (h₁.wk st₁) sec₁ env₁ (h₂.wk st₂) sec₂ env₂
    (fun sec => by
      let st : Var [authStateTy] authStateTy := .zero
      exact caseOptV (eFind K₂ (asRoCache (v st)) fun e => bytesBeq 192 (.fst (v e)) (v sec))
        (bindV (samplePrim .drKey96) fun dk =>
          .ret (.pair (v dk) (.cons (.pair (v sec) (v dk)) (asRoCache (v st)))))
        fun e => .ret (.pair (.snd (v e)) (asRoCache (v st))))
    _ _ rfl rfl hst hsec

private theorem rootRoC_eval_eq {K₁ K₂ nRoot : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (rk₁ dh₁ : Expr pqxdhOps Δ₁ (B 32)) (env₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (rk₂ dh₂ : Expr pqxdhOps Δ₂ (B 32)) (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₂.wk st₂))
    (hrk : rk₁.eval env₁ = rk₂.eval env₂) (hdh : dh₁.eval env₁ = dh₂.eval env₂)
    (hRoot : (valRootRoCache (env₁.get (h₁.wk st₁))).length ≤ nRoot)
    (hK₁ : nRoot ≤ K₁) (hK₂ : nRoot ≤ K₂) :
    (rootRoC K₁ st₁ rk₁ dh₁).eval env₁ = (rootRoC K₂ st₂ rk₂ dh₂).eval env₂ := by
  rw [rootRoC_fuel_eq st₁ rk₁ dh₁ env₁ hRoot hK₁ hK₂]
  unfold rootRoC
  exact letV_body_ren2 (h₁.wk st₁) (.pair rk₁ dh₁) env₁ (h₂.wk st₂) (.pair rk₂ dh₂) env₂
    (fun inp => by
      let st : Var [authStateTy] authStateTy := .zero
      exact caseOptV (eFind K₂ (asRootRoCache (v st)) fun e =>
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bytes2Eq (.fst (v e)) (v inp))
        (bindV (samplePrim .bytes32) fun rk1 => bindV (samplePrim .bytes32) fun ck1 =>
          .ret (.pair (.pair (v rk1) (v ck1)) (.cons (.pair (v inp) (.pair (v rk1) (v ck1)))
            (asRootRoCache (v st)))))
        fun e => .ret (.pair (.snd (v e)) (asRootRoCache (v st))))
    _ _ rfl rfl hst (by simp [Expr.eval, hrk, hdh])

private theorem findHonestC_eval_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (env₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₂.wk st₂))
    (hik : ik₁.eval env₁ = ik₂.eval env₂)
    (hb : AuthBaseValOnlineBounded n (env₁.get (h₁.wk st₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (findHonestC S K₁ st₁ ik₁).eval env₁ = (findHonestC S K₂ st₂ ik₂).eval env₂ := by
  rw [findHonestC_prf_fuel_eq S st₁ ik₁ env₁ hb hK₁ hK₂]
  unfold findHonestC
  exact letV_body_ren2 (h₁.wk st₁) ik₁ env₁ (h₂.wk st₂) ik₂ env₂
    (fun ikV => by
      let st : Var [authStateTy] authStateTy := .zero
      exact _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.findMV (min K₂ S.N_dh)
        (asPrincipals (v st)) fun e =>
          bindV (queryPrim .pow8 (v ikV)) fun p1 =>
            bindV (queryPrim .pow8 (peIkAPk (.snd (v e)))) fun p2 =>
              .ret (bytesBeq 32 (v p1) (v p2)))
    _ _ rfl rfl hst hik

private theorem resolveSigPkC_eval_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) [h₁ : Ext Γ₁ Δ₁] (ik₁ : Expr pqxdhOps Δ₁ (B 32)) (env₁ : Env Δ₁)
    (st₂ : Var Γ₂ authStateTy) [h₂ : Ext Γ₂ Δ₂] (ik₂ : Expr pqxdhOps Δ₂ (B 32)) (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₂.wk st₂))
    (hik : ik₁.eval env₁ = ik₂.eval env₂)
    (hb : AuthBaseValOnlineBounded n (env₁.get (h₁.wk st₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (resolveSigPkC S K₁ st₁ ik₁).eval env₁ = (resolveSigPkC S K₂ st₂ ik₂).eval env₂ := by
  rw [resolveSigPkC_fuel_eq S st₁ ik₁ env₁ hb hK₁ hK₂]
  unfold resolveSigPkC
  exact letV_congr₂ hik fun _ => bindV_congr₂
    (findHonestC_eval_eq S st₁ (.var .zero) _ st₂ (.var .zero) _
      (by simpa [Ext.step_wk, env_get_succ] using hst) rfl
      (by simpa [Ext.step_wk, env_get_succ] using hb) hK₂ hK₂)
    fun f => ret_congr₂ (by
      cases f with
      | none => simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      | some _ =>
        simp only [eCaseOpt, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.peIkSignPk,
          v, Expr.eval, Ext.refl_wk, env_get_zero])

private theorem koskBundleOkC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) (bu₁ : Var Γ₂ preKeyBundleTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (st₂ : Var Γ₃ authStateTy) (bu₂ : Var Γ₄ preKeyBundleTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₃.wk st₂))
    (hbu : env₁.get (h₂.wk bu₁) = env₂.get (h₄.wk bu₂))
    (hb : AuthBaseValOnlineBounded n (env₁.get (h₁.wk st₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (koskBundleOkC S K₁ st₁ bu₁).eval env₁ = (koskBundleOkC S K₂ st₂ bu₂).eval env₂ := by
  rw [koskBundleOkC_fuel_eq S st₁ bu₁ env₁ hb hK₁ hK₂,
    eval_ren2 (h₁.wk st₁) (h₂.wk bu₁)
      (koskBundleOkC S K₂ (Γ₁ := [authStateTy, preKeyBundleTy]) (Γ₂ := [preKeyBundleTy]) .zero .zero)
      (koskBundleOkC S K₂ st₁ bu₁) env₁ rfl,
    eval_ren2 (h₃.wk st₂) (h₄.wk bu₂)
      (koskBundleOkC S K₂ (Γ₁ := [authStateTy, preKeyBundleTy]) (Γ₂ := [preKeyBundleTy]) .zero .zero)
      (koskBundleOkC S K₂ st₂ bu₂) env₂ rfl, hst, hbu]

private theorem checkBundleSpkHonIdealC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) (bu₁ : Var Γ₂ preKeyBundleTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (st₂ : Var Γ₃ authStateTy) (bu₂ : Var Γ₄ preKeyBundleTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₃.wk st₂))
    (hbu : env₁.get (h₂.wk bu₁) = env₂.get (h₄.wk bu₂))
    (hb : AuthBaseValOnlineBounded n (env₁.get (h₁.wk st₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (checkBundleSpkHonIdealC S K₁ st₁ bu₁).eval env₁ = (checkBundleSpkHonIdealC S K₂ st₂ bu₂).eval env₂ := by
  rw [checkBundleSpkHonIdealC_fuel_eq S st₁ bu₁ env₁ hb hK₁ hK₂,
    eval_ren2 (h₁.wk st₁) (h₂.wk bu₁)
      (checkBundleSpkHonIdealC S K₂ (Γ₁ := [authStateTy, preKeyBundleTy]) (Γ₂ := [preKeyBundleTy]) .zero .zero)
      (checkBundleSpkHonIdealC S K₂ st₁ bu₁) env₁ rfl,
    eval_ren2 (h₃.wk st₂) (h₄.wk bu₂)
      (checkBundleSpkHonIdealC S K₂ (Γ₁ := [authStateTy, preKeyBundleTy]) (Γ₂ := [preKeyBundleTy]) .zero .zero)
      (checkBundleSpkHonIdealC S K₂ st₂ bu₂) env₂ rfl, hst, hbu]

private theorem prepareAuthHybridRecvC_eval_eq (S : Setup) {K₁ K₂ n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (hst₁ : Var Γ₁ authHybridStateTy) (x₁ : Var Γ₂ recvQTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (hst₂ : Var Γ₃ authHybridStateTy) (x₂ : Var Γ₄ recvQTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hhst : env₁.get (h₁.wk hst₁) = env₂.get (h₃.wk hst₂))
    (hx : env₁.get (h₂.wk x₁) = env₂.get (h₄.wk x₂))
    (hb : AuthHybridValOnlineBounded n (env₁.get (h₁.wk hst₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (prepareAuthHybridRecvC S K₁ opk hst₁ x₁).eval env₁ =
      (prepareAuthHybridRecvC S K₂ opk hst₂ x₂).eval env₂ := by
  rw [prepareAuthHybridRecvC_fuel_eq S opk hst₁ x₁ env₁ hb hK₁ hK₂,
    eval_ren2 (h₁.wk hst₁) (h₂.wk x₁)
      (prepareAuthHybridRecvC S K₂ opk (Γ₁ := [authHybridStateTy, recvQTy]) (Γ₂ := [recvQTy]) .zero .zero)
      (prepareAuthHybridRecvC S K₂ opk hst₁ x₁) env₁ (by cases opk <;> rfl),
    eval_ren2 (h₃.wk hst₂) (h₄.wk x₂)
      (prepareAuthHybridRecvC S K₂ opk (Γ₁ := [authHybridStateTy, recvQTy]) (Γ₂ := [recvQTy]) .zero .zero)
      (prepareAuthHybridRecvC S K₂ opk hst₂ x₂) env₂ (by cases opk <;> rfl), hhst, hx]

private theorem recvFinishTagRunC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (tag₁ : Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy) [h₁ : Ext Γ₁ Δ₁]
    (res₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishResTy) (env₁ : Env Δ₁)
    (tag₂ : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy) [h₂ : Ext Γ₂ Δ₂]
    (res₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishResTy) (env₂ : Env Δ₂)
    (htag : env₁.get (h₁.wk tag₁) = env₂.get (h₂.wk tag₂))
    (hres : res₁.eval env₁ = res₂.eval env₂)
    (hbTag : RecvTagValBounded n ro0 root0 (env₁.get (h₁.wk tag₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (recvFinishTagRunC S K₁ tag₁ res₁).eval env₁ = (recvFinishTagRunC S K₂ tag₂ res₂).eval env₂ := by
  rw [recvFinishTagRunC_fuel_eq S tag₁ rfl hbTag hK₁ hK₂]
  let c0 := recvFinishTagRunC S K₂
    (Γ₁ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy])
    (Δ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishResTy,
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagTy])
    .zero (.var .zero)
  unfold recvFinishTagRunC
  refine eval_unlet3_congr (unlet3 c0) (h₁.wk tag₁) res₁ env₁ _ (h₂.wk tag₂) res₂ env₂ _ ?_ ?_ htag hres <;> rfl

private theorem checkBundleProvenanceExactC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (st₁ : Var Γ₁ authStateTy) (bu₁ : Var Γ₂ preKeyBundleTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (st₂ : Var Γ₃ authStateTy) (bu₂ : Var Γ₄ preKeyBundleTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hst : env₁.get (h₁.wk st₁) = env₂.get (h₃.wk st₂))
    (hbu : env₁.get (h₂.wk bu₁) = env₂.get (h₄.wk bu₂))
    (hb : AuthBaseValOnlineBounded n (env₁.get (h₁.wk st₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.checkBundleProvenanceExactC S K₁ st₁ bu₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.checkBundleProvenanceExactC S K₂ st₂ bu₂).eval env₂ := by
  rw [_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase.checkBundleProvenanceExactC_fuel_eq S st₁ bu₁ env₁ hb hK₁ hK₂,
    eval_ren2 (h₁.wk st₁) (h₂.wk bu₁)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.checkBundleProvenanceExactC S K₂
        (Γ₁ := [authStateTy, preKeyBundleTy]) (Γ₂ := [preKeyBundleTy]) .zero .zero)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.checkBundleProvenanceExactC S K₂ st₁ bu₁) env₁ rfl,
    eval_ren2 (h₃.wk st₂) (h₄.wk bu₂)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.checkBundleProvenanceExactC S K₂
        (Γ₁ := [authStateTy, preKeyBundleTy]) (Γ₂ := [preKeyBundleTy]) .zero .zero)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.checkBundleProvenanceExactC S K₂ st₂ bu₂) env₂ rfl, hst, hbu]

set_option linter.unusedSimpArgs false in
private theorem finishAuthHybridSendC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    (hst₁ : Var Γ₁ authHybridStateTy) [h₁ : Ext Γ₁ Δ₁]
    (args₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishSendArgsTy) (env₁ : Env Δ₁)
    (hst₂ : Var Γ₂ authHybridStateTy) [h₂ : Ext Γ₂ Δ₂]
    (args₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishSendArgsTy) (env₂ : Env Δ₂)
    (hhst : env₁.get (h₁.wk hst₁) = env₂.get (h₂.wk hst₂))
    (hargs : args₁.eval env₁ = args₂.eval env₂)
    (hb : AuthHybridValOnlineBounded n (env₁.get (h₁.wk hst₁)))
    (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (finishAuthHybridSendC S K₁ hst₁ args₁).eval env₁ =
      (finishAuthHybridSendC S K₂ hst₂ args₂).eval env₂ := by
  rw [finishAuthHybridSendC_fuel_eq S hst₁ rfl hb hK₁ hK₂]
  unfold finishAuthHybridSendC
  refine letV_congr₂ hargs fun _ => ?_
  refine letV_congr₂_eq (by
    simp only [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhst]) fun st hstEq => ?_
  have hbSt : AuthBaseValOnlineBounded n st := by
    have : st = (env₁.get (h₁.wk hst₁)).1 := by
      simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq.symm
    rw [this]; exact hb.base_le
  iterate 29 refine letV_congr₂ (by
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.hdMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pmMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.peIkAPk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbSpkId,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbOpkB?,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbPqspkId,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.optFst,
      eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]) fun _ => ?_
  refine bindV_congr₂ (checkBundleProvenanceExactC_eval_eq S _ _ _ _ _ _
    (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])
    (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hK₂ hK₂) fun _ => ?_
  refine bindV_congr₂ (checkBundleSpkHonIdealC_eval_eq S _ _ _ _ _ _
    (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])
    (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hK₂ hK₂) fun _ => ?_
  iterate 10 refine letV_congr₂ (by
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.seMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbIkB,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbSpkB,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbOpkB?,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbPqspkB,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.optSnd,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.peIkAPk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.snoMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.soMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ikrMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.iasMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSecb,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asHasWonAuth,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asOpkEntries,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSessions,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvOPK,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvNoOPK,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedKyberTriples,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentNoOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdNoOPKEvents,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asAdvKeys,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.boolOr,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.isSomeE,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aSendFresh,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.aSendUnfresh,
      asPrincipals, asSpkBundles, asUsedSendSessions, asRoCache, asRootRoCache,
      bytesBeq, eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hhst]) fun _ => ?_
  exact ret_congr₂ (by simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])

private theorem allocSendSlotE_eval_congr {Δ₁ Δ₂ : List PT}
    {ss₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authSlotStateTy}
    {sid₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sessionIdTy} {env₁ : Env Δ₁}
    {ss₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authSlotStateTy}
    {sid₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sessionIdTy} {env₂ : Env Δ₂}
    (hss : ss₁.eval env₁ = ss₂.eval env₂) (hsid : sid₁.eval env₁ = sid₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allocSendSlotE ss₁ sid₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allocSendSlotE ss₂ sid₂).eval env₂ := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allocSendSlotE, eLet2, eLet,
    eCaseOpt, eCaseSum, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assRecv,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assNext,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assMk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assSendOpk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assSendNoOpk,
    Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, hss, hsid]

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

private theorem lookupSendSlotOrZeroE_eval_congr {Δ₁ Δ₂ : List PT}
    {ss₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authSlotStateTy}
    {sid₁ : Expr pqxdhOps Δ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sessionIdTy} {env₁ : Env Δ₁}
    {ss₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authSlotStateTy}
    {sid₂ : Expr pqxdhOps Δ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sessionIdTy} {env₂ : Env Δ₂}
    (hss : ss₁.eval env₁ = ss₂.eval env₂) (hsid : sid₁.eval env₁ = sid₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.lookupSendSlotOrZeroE ss₁ sid₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.lookupSendSlotOrZeroE ss₂ sid₂).eval env₂ := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.lookupSendSlotOrZeroE,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.lookupSendSlotE, eLet2, eLet,
    eCaseOpt, eCaseSum, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assRecv,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assSendOpk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.assSendNoOpk,
    Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, hss, hsid]

local macro "env_eq" : tactic =>
  `(tactic| simp only [ahsBase, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, parHstDec, parFinishTag, parMatchedSess?,
    parIsUncorrSender, parSameEph, parSecrets, parDhRatchet, parKEntry,
    iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    pkmPqRatchetMsg, pkmAeadCt, pkmEphAPk, pkmHdr, hdrIkAPk, peIkAPk, peSecIKA0, peCorrupted,
    pkbIkB, pkbSpkB, pkbSpkSig, pkbPqspkB, pkbPqspkSig, pkbOpkB?, sbPqspkPk,
    encEC_eval, encKEM_eval, sendGuardE, asHasWonAuth, asSecb, boolOr_eval, boolOr, isSomeE, natLt, bytesLen_eval, litB,
    sameSaltKeyE_eval, firstMsgADE_eval, buildSecretsE_eval,
    sidEq, eLet2, eLet, eCaseSum, natEq_eval, nat2Eq_eval, nat3Eq_eval, bytesBeq_eval, asRoCache, asRootRoCache,
    aNone, Bool.false_eq_true, ite_true, ite_false,
    eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, *])

local macro "ret_mk_eq" : tactic =>
  `(tactic| (
    dsimp only [mkcMk, ahsfUpd, ahsfUpdSlots, ahsfMkSlots,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, aNone,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, *]))

private theorem fixed_toHybrid {n : ℕ} {fhst : authHybridStateFixedTy.denote}
    (hb : AuthFixedValOnlineBounded n fhst) : AuthHybridValOnlineBounded n fhst.1 :=
  ⟨hb.base_le, hb.initKemRecs_le, hb.recvKemRecs_le, hb.idealSessions_le⟩

set_option linter.unusedSimpArgs false in
private theorem finishAuthSendMkC_eval_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    {fhst₁ : Var Γ₁ authHybridStateFixedTy} [h₁ : Ext Γ₁ Δ₁] {sid₁ : Expr pqxdhOps Δ₁ sessionIdTy}
    {uE₁ : Expr pqxdhOps Δ₁ principalEntryTy} {pp₁ : Expr pqxdhOps Δ₁ (.opt (.prod .nat principalEntryTy))}
    {isFresh₁ : Expr pqxdhOps Δ₁ .bool} {bu₁ : Expr pqxdhOps Δ₁ preKeyBundleTy}
    {m01₁ : Expr pqxdhOps Δ₁ (.prod (B 32) (B 32))} {keys6₁ : Expr pqxdhOps Δ₁ keys6Ty}
    {drKey₁ : Expr pqxdhOps Δ₁ drKeyTy} {rk1₁ mkSeed₁ ck1_1₁ : Expr pqxdhOps Δ₁ (B 32)}
    {spqrSalt?₁ : Expr pqxdhOps Δ₁ (.opt (B 32))} {pqMsg₁ msgPlain₁ : Expr pqxdhOps Δ₁ (B 32)}
    {mks₁ : Expr pqxdhOps Δ₁ msgKeysTy} {env₁ : Env Δ₁}
    {fhst₂ : Var Γ₂ authHybridStateFixedTy} [h₂ : Ext Γ₂ Δ₂] {sid₂ : Expr pqxdhOps Δ₂ sessionIdTy}
    {uE₂ : Expr pqxdhOps Δ₂ principalEntryTy} {pp₂ : Expr pqxdhOps Δ₂ (.opt (.prod .nat principalEntryTy))}
    {isFresh₂ : Expr pqxdhOps Δ₂ .bool} {bu₂ : Expr pqxdhOps Δ₂ preKeyBundleTy}
    {m01₂ : Expr pqxdhOps Δ₂ (.prod (B 32) (B 32))} {keys6₂ : Expr pqxdhOps Δ₂ keys6Ty}
    {drKey₂ : Expr pqxdhOps Δ₂ drKeyTy} {rk1₂ mkSeed₂ ck1_1₂ : Expr pqxdhOps Δ₂ (B 32)}
    {spqrSalt?₂ : Expr pqxdhOps Δ₂ (.opt (B 32))} {pqMsg₂ msgPlain₂ : Expr pqxdhOps Δ₂ (B 32)}
    {mks₂ : Expr pqxdhOps Δ₂ msgKeysTy} {env₂ : Env Δ₂}
    (hfhst : env₁.get (h₁.wk fhst₁) = env₂.get (h₂.wk fhst₂))
    (ha : (Expr.pair sid₁ (.pair uE₁ (.pair pp₁ (.pair isFresh₁ (.pair bu₁ (.pair m01₁
      (.pair keys6₁ (.pair drKey₁ (.pair rk1₁ (.pair mkSeed₁ (.pair ck1_1₁
        (.pair spqrSalt?₁ (.pair pqMsg₁ (.pair msgPlain₁ mks₁)))))))))))))).eval env₁ =
      (Expr.pair sid₂ (.pair uE₂ (.pair pp₂ (.pair isFresh₂ (.pair bu₂ (.pair m01₂
      (.pair keys6₂ (.pair drKey₂ (.pair rk1₂ (.pair mkSeed₂ (.pair ck1_1₂
        (.pair spqrSalt?₂ (.pair pqMsg₂ (.pair msgPlain₂ mks₂)))))))))))))).eval env₂)
    (hb : AuthFixedValOnlineBounded n (env₁.get (h₁.wk fhst₁))) (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (finishAuthSendMkC S K₁ fhst₁ sid₁ uE₁ pp₁ isFresh₁ bu₁ m01₁ keys6₁ drKey₁ rk1₁ mkSeed₁ ck1_1₁
        spqrSalt?₁ pqMsg₁ msgPlain₁ mks₁).eval env₁ =
      (finishAuthSendMkC S K₂ fhst₂ sid₂ uE₂ pp₂ isFresh₂ bu₂ m01₂ keys6₂ drKey₂ rk1₂ mkSeed₂ ck1_1₂
        spqrSalt?₂ pqMsg₂ msgPlain₂ mks₂).eval env₂ := by
  unfold finishAuthSendMkC; refine letV_congr₂ ha fun _ => ?_
  refine letV_congr₂_eq (by env_eq) fun hst hhst => ?_
  have hbHst : AuthHybridValOnlineBounded n hst := by
    have : hst = (env₁.get (h₁.wk fhst₁)).1 := by
      simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhst.symm
    rw [this]; exact fixed_toHybrid hb
  iterate 18 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
  refine bindV_congr₂ (finishAuthHybridSendC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbHst) hK₁ hK₂) fun _ => ?_
  exact ret_congr₂ (by ret_mk_eq)

private theorem finishAuthSendMkC_leaves (S : Setup) (K n : ℕ) {Γ₁ Δ : List PT}
    {fhst : Var Γ₁ authHybridStateFixedTy} [h₁_ext : Ext Γ₁ Δ] {sid : Expr pqxdhOps Δ sessionIdTy}
    {uE : Expr pqxdhOps Δ principalEntryTy} {pp : Expr pqxdhOps Δ (.opt (.prod .nat principalEntryTy))}
    {isFresh : Expr pqxdhOps Δ .bool} {bu : Expr pqxdhOps Δ preKeyBundleTy}
    {m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32))} {keys6 : Expr pqxdhOps Δ keys6Ty}
    {drKey : Expr pqxdhOps Δ drKeyTy} {rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)}
    {spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))} {pqMsg msgPlain : Expr pqxdhOps Δ (B 32)}
    {mks : Expr pqxdhOps Δ msgKeysTy} {env : Env Δ}
    (hb : AuthFixedValOnlineBounded n (env.get (h₁_ext.wk fhst))) :
    AllLeaves (fun res => AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁_ext.wk fhst)).1.1) (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁_ext.wk fhst)).1.1) (valRootRoCache res.2.1.1))
      ((finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
          spqrSalt? pqMsg msgPlain mks).eval env) := by
  let fhst0 := env.get (h₁_ext.wk fhst)
  change AllLeaves (fun (res : RSF.denote) => AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne (valRoCache fhst0.1.1) (valRoCache res.2.1.1) ∧
      CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valRootRoCache res.2.1.1)) _
  unfold finishAuthSendMkC; refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun hst hhst => ?_
  have hhstEq : hst = fhst0.1 := by
    simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, fhst0] using hhst
  refine letV_allLeaves_eq fun st hstBase => ?_
  have hstEq : st = fhst0.1.1 := by
    simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hstBase
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
    dsimp only [ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, fhst0]
    exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le,
      Nat.le_trans hb.mkSaltCache_le (Nat.le_succ n)⟩, hOutRo', hOutRoot'⟩

private theorem fixed_withSlots {n : ℕ} {fhst : authHybridStateFixedTy.denote}
    {ss : authSlotStateTy.denote} (hb : AuthFixedValOnlineBounded n fhst) :
    AuthFixedValOnlineBounded n (fhst.1, fhst.2.1, fhst.2.2.1, ss) :=
  ⟨hb.base_le, hb.initKemRecs_le, hb.recvKemRecs_le, hb.idealSessions_le, hb.mkSaltCache_le⟩

set_option linter.unusedSimpArgs false in
private theorem finishAuthRecvMkC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × drKeyTy.denote)} {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT} {msg₁ : Var Γ₁ preKeyMsgTy} {prep₁ : Var Γ₂ preparedAuthRecvTy}
    [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] {drKey₁ : Expr pqxdhOps Δ₁ drKeyTy}
    {rk1₁ ck1_1₁ : Expr pqxdhOps Δ₁ (B 32)} {rc'₁ : Expr pqxdhOps Δ₁ .nat}
    {cache'₁ : Expr pqxdhOps Δ₁ authMkSaltCacheTy} {mks₁ : Expr pqxdhOps Δ₁ msgKeysTy} {env₁ : Env Δ₁}
    {msg₂ : Var Γ₃ preKeyMsgTy} {prep₂ : Var Γ₄ preparedAuthRecvTy}
    [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] {drKey₂ : Expr pqxdhOps Δ₂ drKeyTy}
    {rk1₂ ck1_1₂ : Expr pqxdhOps Δ₂ (B 32)} {rc'₂ : Expr pqxdhOps Δ₂ .nat}
    {cache'₂ : Expr pqxdhOps Δ₂ authMkSaltCacheTy} {mks₂ : Expr pqxdhOps Δ₂ msgKeysTy} {env₂ : Env Δ₂}
    (hmsg : env₁.get (h₁.wk msg₁) = env₂.get (h₃.wk msg₂))
    (hprep : env₁.get (h₂.wk prep₁) = env₂.get (h₄.wk prep₂))
    (ha : (Expr.pair drKey₁ (.pair rk1₁ (.pair ck1_1₁ (.pair rc'₁ (.pair cache'₁ mks₁))))).eval env₁ =
          (Expr.pair drKey₂ (.pair rk1₂ (.pair ck1_1₂ (.pair rc'₂ (.pair cache'₂ mks₂))))).eval env₂)
    (hbPrep : PreparedRecvValBounded n ro0 root0 (env₁.get (h₂.wk prep₁))) (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (finishAuthRecvMkC S K₁ msg₁ prep₁ drKey₁ rk1₁ ck1_1₁ rc'₁ cache'₁ mks₁).eval env₁ =
      (finishAuthRecvMkC S K₂ msg₂ prep₂ drKey₂ rk1₂ ck1_1₂ rc'₂ cache'₂ mks₂).eval env₂ := by
  unfold finishAuthRecvMkC; refine letV_congr₂ ha fun _ => ?_
  iterate 7 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine letV_congr₂_eq (by env_eq) fun fTag hfTag => ?_
  have hbTag : RecvTagValBounded n ro0 root0 fTag := by
    have : fTag = (env₁.get (h₂.wk prep₁)).2.2.2.2.2.2.2.2.2 := by
      simpa [parFinishTag, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTag.symm
    rw [this]; exact hbPrep.tag_bounded
  refine letV_congr₂ (by env_eq) fun _ => ?_
  refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun pt? => ?_
  refine letV_congr₂ (by cases pt? <;> env_eq) fun _ => ?_
  refine bindV_congr₂ (recvFinishTagRunC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbTag) hK₁ hK₂) fun _ => ?_
  exact ret_congr₂ (by ret_mk_eq)

private theorem finishAuthRecvMkC_leaves (S : Setup) (K n : ℕ)
    (ro0 : List (List UInt8 × drKeyTy.denote)) (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))
    {Γ₁ Γ₂ Δ : List PT} {msg : Var Γ₁ preKeyMsgTy} {prep : Var Γ₂ preparedAuthRecvTy}
    [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ] {drKey : Expr pqxdhOps Δ drKeyTy}
    {rk1 ck1_1 : Expr pqxdhOps Δ (B 32)} {rc' : Expr pqxdhOps Δ .nat}
    {cache' : Expr pqxdhOps Δ authMkSaltCacheTy} {mks : Expr pqxdhOps Δ msgKeysTy} {env : Env Δ}
    (hbPrep : PreparedRecvValBounded n ro0 root0 (env.get (h₂_ext.wk prep)))
    (hCache : (cache'.eval env).length ≤ n + 1) :
    AllLeaves (fun res => AuthFixedValOnlineBounded (n + 1) res.2 ∧
      CacheStepAtMostOne ro0 (valRoCache res.2.1.1) ∧ CacheStepAtMostOne root0 (valRootRoCache res.2.1.1))
      ((finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).eval env) := by
  unfold finishAuthRecvMkC; refine letV_allLeaves_eq fun a ha => ?_
  have haC : a.2.2.2.2.1.length ≤ n + 1 := by
    have : a.2.2.2.2.1 = cache'.eval env := by simpa [Expr.eval] using congrArg (fun p => p.2.2.2.2.1) ha
    rw [this]; exact hCache
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun cVal hcVal => ?_
  have hcLen : cVal.length ≤ n + 1 := by
    have : cVal = a.2.2.2.2.1 := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hcVal
    rw [this]; exact haC
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hst => ?_
  have hstEq : st = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.1.1 := by
    simpa [ahsBase, parHstDec, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hst
  refine letV_allLeaves_eq fun fTag hfTag => ?_
  have hfTagEq : fTag = (env.get (h₂_ext.wk prep)).2.2.2.2.2.2.2.2.2 := by
    simpa [parFinishTag, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfTag
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun pt? => ?_
  refine letV_allLeaves_eq fun res? hres? => ?_
  apply bindV_allLeaves
  · apply recvFinishTagRunC_leaves (n := n) (ro0 := ro0) (root0 := root0)
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfTagEq] using hbPrep.tag_bounded
    · intro r hr
      have hr' : res? = some r := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hr
      rw [hr'] at hres?
      cases pt? with
      | none => simp only [eCaseOpt, v, Expr.eval, Ext.refl_wk, env_get_zero, reduceCtorEq] at hres?
      | some pt =>
        simp only [eCaseOpt, asRoCache, asRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hstEq, Option.some.injEq] at hres?
        subst hres?
        exact ⟨by rw [← hbPrep.ro_eq]; exact CacheStepAtMostOne.refl _,
               by rw [← hbPrep.root_eq]; exact CacheStepAtMostOne.refl _⟩
  · rintro out ⟨hOutB, hOutRo, hOutRoot⟩; refine ret_allLeaves ?_
    dsimp only [ahsfMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]
    exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le, hcLen⟩,
      hOutRo, hOutRoot⟩

private def MkContBounded (n : ℕ) (ro0 : List (List UInt8 × drKeyTy.denote))
    (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))) : prfMkChalContTy.denote → Prop
  | .inl sCont => AuthFixedValOnlineBounded n sCont.2.2.1 ∧
      valRoCache sCont.2.2.1.1.1 = ro0 ∧ valRootRoCache sCont.2.2.1.1.1 = root0
  | .inr rCont => PreparedRecvValBounded n ro0 root0 rCont.2.2.2.2.1 ∧ rCont.2.2.2.2.2.2.2.2.2.1.length ≤ n

private def MkPreLeafOk (n : ℕ) (ro0 : List (List UInt8 × drKeyTy.denote))
    (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))) : prfMkStepPreTy.denote → Prop
  | .inl d => AuthFixedValOnlineBounded (n + 1) d.2.2.2.2 ∧
      CacheStepAtMostOne ro0 (valRoCache d.2.2.2.2.1.1) ∧ CacheStepAtMostOne root0 (valRootRoCache d.2.2.2.2.1.1)
  | .inr req => MkContBounded n ro0 root0 req.2

set_option linter.unusedSimpArgs false in
private theorem finishRecvUnmatchedMkPreC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × drKeyTy.denote)} {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Γ₃ Δ₁ Γ₄ Γ₅ Γ₆ Δ₂ : List PT} {core₁ : Var Γ₁ prfMkCoreTy} {msg₁ : Var Γ₂ preKeyMsgTy}
    {prep₁ : Var Γ₃ preparedAuthRecvTy} [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] [h₃ : Ext Γ₃ Δ₁]
    {drKey₁ : Expr pqxdhOps Δ₁ drKeyTy} {rk1₁ : Expr pqxdhOps Δ₁ (B 32)} {spqrSalt?₁ : Expr pqxdhOps Δ₁ (.opt (B 32))}
    {rSlot₁ rc'₁ : Expr pqxdhOps Δ₁ .nat} {env₁ : Env Δ₁}
    {core₂ : Var Γ₄ prfMkCoreTy} {msg₂ : Var Γ₅ preKeyMsgTy}
    {prep₂ : Var Γ₆ preparedAuthRecvTy} [h₄ : Ext Γ₄ Δ₂] [h₅ : Ext Γ₅ Δ₂] [h₆ : Ext Γ₆ Δ₂]
    {drKey₂ : Expr pqxdhOps Δ₂ drKeyTy} {rk1₂ : Expr pqxdhOps Δ₂ (B 32)} {spqrSalt?₂ : Expr pqxdhOps Δ₂ (.opt (B 32))}
    {rSlot₂ rc'₂ : Expr pqxdhOps Δ₂ .nat} {env₂ : Env Δ₂}
    (hcore : env₁.get (h₁.wk core₁) = env₂.get (h₄.wk core₂)) (hmsg : env₁.get (h₂.wk msg₁) = env₂.get (h₅.wk msg₂))
    (hprep : env₁.get (h₃.wk prep₁) = env₂.get (h₆.wk prep₂))
    (ha : (Expr.pair drKey₁ (.pair rk1₁ (.pair spqrSalt?₁ (.pair rSlot₁ rc'₁)))).eval env₁ =
          (Expr.pair drKey₂ (.pair rk1₂ (.pair spqrSalt?₂ (.pair rSlot₂ rc'₂)))).eval env₂)
    (hbPrep : PreparedRecvValBounded n ro0 root0 (env₁.get (h₃.wk prep₁))) (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (finishRecvUnmatchedMkPreC S K₁ core₁ msg₁ prep₁ drKey₁ rk1₁ spqrSalt?₁ rSlot₁ rc'₁).eval env₁ =
      (finishRecvUnmatchedMkPreC S K₂ core₂ msg₂ prep₂ drKey₂ rk1₂ spqrSalt?₂ rSlot₂ rc'₂).eval env₂ := by
  unfold finishRecvUnmatchedMkPreC; refine letV_congr₂ ha fun _ => ?_
  iterate 10 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine ite_congr₂ (by env_eq) ?_ ?_
  · refine bindV_congr₂ rfl fun _ => ite_congr₂ (by env_eq) (ret_congr₂ (by ret_mk_eq)) ?_
    refine bindV_congr₂ rfl fun _ => bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by env_eq) (by env_eq) (by env_eq)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep) hK₁ hK₂) fun _ =>
      ret_congr₂ (by ret_mk_eq)
  · refine ite_congr₂ (by env_eq) ?_ ?_
    · refine bindV_congr₂ rfl fun _ => bindV_congr₂ rfl fun _ =>
        bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by env_eq) (by env_eq) (by env_eq)
          (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep) hK₁ hK₂) fun _ =>
          ret_congr₂ (by ret_mk_eq)
    · refine bindV_congr₂ rfl fun _ => bindV_congr₂ rfl fun _ =>
        bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ =>
        bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by env_eq) (by env_eq) (by env_eq)
          (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep) hK₁ hK₂) fun _ =>
          ret_congr₂ (by ret_mk_eq)

private theorem finishRecvUnmatchedMkPreC_leaves (S : Setup) (K n : ℕ)
    (ro0 : List (List UInt8 × drKeyTy.denote)) (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))
    {Γ₁ Γ₂ Γ₃ Δ : List PT} {core : Var Γ₁ prfMkCoreTy} {msg : Var Γ₂ preKeyMsgTy} {prep : Var Γ₃ preparedAuthRecvTy}
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] {drKey : Expr pqxdhOps Δ drKeyTy}
    {rk1 : Expr pqxdhOps Δ (B 32)} {spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))}
    {rSlot rc' : Expr pqxdhOps Δ .nat} {env : Env Δ}
    (hbPrep : PreparedRecvValBounded n ro0 root0 (env.get (h₃.wk prep)))
    (hCache : (env.get (h₁.wk core)).2.2.2.2.2.1.length ≤ n) :
    AllLeaves (MkPreLeafOk n ro0 root0)
      ((finishRecvUnmatchedMkPreC S K core msg prep drKey rk1 spqrSalt? rSlot rc').eval env) := by
  unfold finishRecvUnmatchedMkPreC; iterate 9 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun cVal hcVal => ?_
  have hcLen : cVal.length ≤ n := by
    have : cVal = (env.get (h₁.wk core)).2.2.2.2.2.1 := by
      simpa [ahsfMkSaltCache, mkcFhst, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hcVal
    rw [this]; exact hCache
  refine letV_allLeaves fun _ => ?_; refine ite_allLeaves ?_ (ite_allLeaves ?_ ?_)
  · refine bindV_allLeaves_const fun _ => ite_allLeaves ?_ ?_
    · refine ret_allLeaves ?_
      dsimp only [MkPreLeafOk, MkContBounded, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_succ, env_get_zero]; exact ⟨hbPrep, hcLen⟩
    · refine bindV_allLeaves_const fun _ => bindV_allLeaves (finishAuthRecvMkC_leaves S K n ro0 root0
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep)
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using Nat.le_trans hcLen (Nat.le_succ n))) fun res ⟨hB, hRo, hRoot⟩ => ?_
      refine ret_allLeaves ?_
      dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
        v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]
      exact ⟨fixed_withSlots hB, hRo, hRoot⟩
  · refine bindV_allLeaves_const fun _ => bindV_allLeaves_const fun _ =>
      bindV_allLeaves (finishAuthRecvMkC_leaves S K n ro0 root0
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep)
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using Nat.le_trans hcLen (Nat.le_succ n))) fun res ⟨hB, hRo, hRoot⟩ => ?_
    refine ret_allLeaves ?_
    dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]
    exact ⟨fixed_withSlots hB, hRo, hRoot⟩
  · refine bindV_allLeaves_const fun _ => bindV_allLeaves_const fun _ => bindV_allLeaves_const fun _ =>
      bindV_allLeaves (finishAuthRecvMkC_leaves S K n ro0 root0
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep)
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using Nat.le_trans hcLen (Nat.le_succ n))) fun res ⟨hB, hRo, hRoot⟩ => ?_
    refine ret_allLeaves ?_
    dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]
    exact ⟨fixed_withSlots hB, hRo, hRoot⟩

set_option linter.unusedSimpArgs false in
private theorem prfMkStepPostC_eval_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × drKeyTy.denote)} {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (cont₁ : Var Γ₁ prfMkChalContTy) (mk₁ : Var Γ₂ msgKeysTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (cont₂ : Var Γ₃ prfMkChalContTy) (mk₂ : Var Γ₄ msgKeysTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hcont : env₁.get (h₁.wk cont₁) = env₂.get (h₃.wk cont₂)) (hmk : env₁.get (h₂.wk mk₁) = env₂.get (h₄.wk mk₂))
    (hb : MkContBounded n ro0 root0 (env₁.get (h₁.wk cont₁))) (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (prfMkStepPostC S K₁ cont₁ mk₁).eval env₁ = (prfMkStepPostC S K₂ cont₂ mk₂).eval env₂ := by
  unfold prfMkStepPostC; refine caseSumV_congr₂ (by env_eq) (fun sCont hs => ?_) (fun rCont hr => ?_)
  · have hbS : AuthFixedValOnlineBounded n sCont.2.2.1 := by
      have : env₁.get (h₁.wk cont₁) = .inl sCont := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_zero] using hs
      rw [this] at hb; exact hb.1
    iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine letV_congr₂_eq (by env_eq) fun fhst hfhst => ?_
    have hbFhst : AuthFixedValOnlineBounded n fhst := by
      have : fhst = sCont.2.2.1 := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfhst.symm
      rw [this]; exact hbS
    iterate 13 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine bindV_congr₂ (finishAuthSendMkC_eval_eq S (by env_eq) (by env_eq)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbFhst) hK₁ hK₂) fun _ => ?_
    exact ret_congr₂ (by ret_mk_eq)
  · have hbR : PreparedRecvValBounded n ro0 root0 rCont.2.2.2.2.1 := by
      have : env₁.get (h₁.wk cont₁) = .inr rCont := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_zero] using hr
      rw [this] at hb; exact hb.1
    iterate 4 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine letV_congr₂_eq (by env_eq) fun prep hprep => ?_
    have hbPrep : PreparedRecvValBounded n ro0 root0 prep := by
      have : prep = rCont.2.2.2.2.1 := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hprep.symm
      rw [this]; exact hbR
    iterate 6 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine letV_congr₂_eq (by env_eq) fun ci? _ => ?_
    refine letV_congr₂ (by cases ci? <;> env_eq) fun _ => ?_
    refine bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by env_eq) (by env_eq) (by env_eq)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbPrep) hK₁ hK₂) fun _ => ?_
    exact ret_congr₂ (by ret_mk_eq)

private structure Leaves {ι : Type} {T : OracleSpec ι} {α : Type} (P : α → Prop) (c : OracleComp T α) : Prop where
  run : AllLeaves P c

private theorem letV_leavesL {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₂.denote → Prop} {e : Expr pqxdhOps Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {env : Env Γ} (hk : ∀ x, Leaves P ((k .zero).eval (.cons x env))) : Leaves P ((letV e k).eval env) :=
  ⟨letV_allLeaves fun x => (hk x).run⟩

private theorem letV_leavesL_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₂.denote → Prop} {e : Expr pqxdhOps Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {env : Env Γ} (hk : ∀ x, x = e.eval env → Leaves P ((k .zero).eval (.cons x env))) :
    Leaves P ((letV e k).eval env) := ⟨letV_allLeaves_eq fun x hx => (hk x hx).run⟩

private theorem bindV_leavesL_const {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₂.denote → Prop} {m : Comp pqxdhOps I Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {env : Env Γ} (hk : ∀ x, Leaves P ((k .zero).eval (.cons x env))) : Leaves P ((bindV m k).eval env) :=
  ⟨bindV_allLeaves_const fun x => (hk x).run⟩

private theorem bindV_leavesL {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₁.denote → Prop} {Q : τ₂.denote → Prop} {m : Comp pqxdhOps I Γ τ₁}
    {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hm : AllLeaves P (m.eval env)) (hk : ∀ x, P x → Leaves Q ((k .zero).eval (.cons x env))) :
    Leaves Q ((bindV m k).eval env) := ⟨bindV_allLeaves hm fun x hx => (hk x hx).run⟩

private theorem ite_leavesL {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ : PT}
    {P : τ.denote → Prop} {c : Expr pqxdhOps Γ .bool} {t e : Comp pqxdhOps I Γ τ} {env : Env Γ}
    (ht : Leaves P (t.eval env)) (he : Leaves P (e.eval env)) : Leaves P ((Comp.ite c t e).eval env) :=
  ⟨ite_allLeaves ht.run he.run⟩

private theorem caseOptV_leavesL {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₂.denote → Prop} {o : Expr pqxdhOps Γ (.opt τ₁)} {kn : Comp pqxdhOps I Γ τ₂}
    {ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hkn : Leaves P (kn.eval env)) (hks : ∀ x, Leaves P ((ks .zero).eval (.cons x env))) :
    Leaves P ((caseOptV o kn ks).eval env) := ⟨caseOptV_allLeaves hkn.run fun x => (hks x).run⟩

private theorem caseOptV_leavesL_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₂.denote → Prop} {o : Expr pqxdhOps Γ (.opt τ₁)} {kn : Comp pqxdhOps I Γ τ₂}
    {ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ} (hkn : Leaves P (kn.eval env))
    (hks : ∀ x, o.eval env = some x → Leaves P ((ks .zero).eval (.cons x env))) :
    Leaves P ((caseOptV o kn ks).eval env) := ⟨caseOptV_allLeaves_eq hkn.run fun x hx => (hks x hx).run⟩

private theorem caseSumV_leavesL_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ τ : PT}
    {P : τ.denote → Prop} {s : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ} {kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ}
    {env : Env Γ} (hkl : ∀ x, s.eval env = .inl x → Leaves P ((kl .zero).eval (.cons x env)))
    (hkr : ∀ y, s.eval env = .inr y → Leaves P ((kr .zero).eval (.cons y env))) :
    Leaves P ((caseSumV s kl kr).eval env) :=
  ⟨caseSumV_allLeaves_eq (fun x hx => (hkl x hx).run) (fun y hy => (hkr y hy).run)⟩

private theorem ret_leavesL {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT} {τ : PT}
    {P : τ.denote → Prop} {e : Expr pqxdhOps Γ τ} {env : Env Γ} (h : P (e.eval env)) :
    Leaves P ((Comp.ret (I := I) e).eval env) := ⟨ret_allLeaves h⟩

private theorem prfMkStepPostC_leaves (S : Setup) (K : ℕ) {n : ℕ}
    {ro0 : List (List UInt8 × drKeyTy.denote)} {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Γ₂ Δ : List PT} (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ msgKeysTy) [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ) (hb : MkContBounded n ro0 root0 (env.get (h₁.wk cont))) :
    AllLeaves (fun post => AuthFixedValOnlineBounded (n + 1) post.2.2.2.2 ∧
      CacheStepAtMostOne ro0 (valRoCache post.2.2.2.2.1.1) ∧
      CacheStepAtMostOne root0 (valRootRoCache post.2.2.2.2.1.1))
      ((prfMkStepPostC S K cont mk).eval env) := by
  apply Leaves.run; unfold prfMkStepPostC
  refine caseSumV_leavesL_eq (fun sCont hs => ?_) (fun rCont hr => ?_)
  · have hEq : env.get (h₁.wk cont) = .inl sCont := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_zero] using hs
    rw [hEq] at hb; rcases hb with ⟨hbS, hRo0, hRoot0⟩
    iterate 2 refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun fhst hfhst => ?_
    have hfhstEq : fhst = sCont.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfhst
    iterate 13 refine letV_leavesL fun _ => ?_
    refine bindV_leavesL (finishAuthSendMkC_leaves S K n
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstEq] using hbS))
      fun res ⟨hB, hRo, hRoot⟩ => ?_
    have hRo' : CacheStepAtMostOne ro0 (valRoCache res.2.1.1) := by
      rw [← hRo0]; simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstEq] using hRo
    have hRoot' : CacheStepAtMostOne root0 (valRootRoCache res.2.1.1) := by
      rw [← hRoot0]; simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstEq] using hRoot
    refine ret_leavesL ?_
    dsimp only [mkcMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_zero]; exact ⟨hB, hRo', hRoot'⟩
  · have hEq : env.get (h₁.wk cont) = .inr rCont := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_zero] using hr
    rw [hEq] at hb; rcases hb with ⟨hbPrep, hCache⟩
    iterate 4 refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun prep hprep => ?_
    have hprepEq : prep = rCont.2.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hprep
    iterate 4 refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun cVal hcVal => ?_
    have hcEq : cVal = rCont.2.2.2.2.2.2.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hcVal
    refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun ci? _ => ?_
    refine letV_leavesL_eq fun cache' hcache' => ?_
    have hc'Len : cache'.length ≤ n + 1 := by
      cases ci? with
      | none =>
        simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] at hcache'
        rw [hcache']; omega
      | some _ =>
        simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] at hcache'
        rw [hcache']; simp only [List.length_cons]; omega
    refine bindV_leavesL (finishAuthRecvMkC_leaves S K n ro0 root0
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hprepEq] using hbPrep)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hc'Len))
      fun res ⟨hB, hRo, hRoot⟩ => ?_
    refine ret_leavesL ?_
    dsimp only [mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]; exact ⟨fixed_withSlots hB, hRo, hRoot⟩

private theorem eAny_eval_eq {K₁ K₂ n : ℕ} {Γ₁ Γ₂ : List PT} {τ : PT}
    {xs₁ : Expr pqxdhOps Γ₁ (.list τ)} {p₁ : Var (τ :: Γ₁) τ → Expr pqxdhOps (τ :: Γ₁) .bool} {env₁ : Env Γ₁}
    {xs₂ : Expr pqxdhOps Γ₂ (.list τ)} {p₂ : Var (τ :: Γ₂) τ → Expr pqxdhOps (τ :: Γ₂) .bool} {env₂ : Env Γ₂}
    (hxs : xs₁.eval env₁ = xs₂.eval env₂) (hLen : (xs₁.eval env₁).length ≤ n) (h₁ : n ≤ K₁) (h₂ : n ≤ K₂)
    (hp : ∀ a, (p₁ .zero).eval (.cons a env₁) = (p₂ .zero).eval (.cons a env₂)) :
    (eAny K₁ xs₁ p₁).eval env₁ = (eAny K₂ xs₂ p₂).eval env₂ := by
  simp only [eAny, Expr.eval]
  rw [take_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂), hxs]
  congr 1; funext a; exact hp a

private theorem eFind_eval_eq {K₁ K₂ n : ℕ} {Γ₁ Γ₂ : List PT} {τ : PT}
    {xs₁ : Expr pqxdhOps Γ₁ (.list τ)} {p₁ : Var (τ :: Γ₁) τ → Expr pqxdhOps (τ :: Γ₁) .bool} {env₁ : Env Γ₁}
    {xs₂ : Expr pqxdhOps Γ₂ (.list τ)} {p₂ : Var (τ :: Γ₂) τ → Expr pqxdhOps (τ :: Γ₂) .bool} {env₂ : Env Γ₂}
    (hxs : xs₁.eval env₁ = xs₂.eval env₂) (hLen : (xs₁.eval env₁).length ≤ n) (h₁ : n ≤ K₁) (h₂ : n ≤ K₂)
    (hp : ∀ a, (p₁ .zero).eval (.cons a env₁) = (p₂ .zero).eval (.cons a env₂)) :
    (eFind K₁ xs₁ p₁).eval env₁ = (eFind K₂ xs₂ p₂).eval env₂ := by
  simp only [eFind, Expr.eval]
  rw [take_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂), hxs]
  congr 1; funext a; exact hp a

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem authMkSendPreKB_eval_eq (S : Setup) {K_on K_ro K n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (core₁ : Var Γ₁ prfMkCoreTy) (x₁ : Var Γ₂ sendQTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (core₂ : Var Γ₃ prfMkCoreTy) (x₂ : Var Γ₄ sendQTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hcore : env₁.get (h₁.wk core₁) = env₂.get (h₃.wk core₂))
    (hx : env₁.get (h₂.wk x₁) = env₂.get (h₄.wk x₂))
    (hb : AuthFixedValOnlineBounded n (env₁.get (h₁.wk core₁)).2.2.2)
    (hKon : n ≤ K_on) (hK : n ≤ K)
    (hRoK : (valRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K_ro)
    (hRoOld : (valRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K)
    (hRootK : (valRootRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K_ro)
    (hRootOld : (valRootRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K) :
    (authMkSendPreKB S K_on K_ro opk core₁ x₁).eval env₁ =
      (authMkSendPreB S K opk core₂ x₂).eval env₂ := by
  unfold authMkSendPreKB
  unfold _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase.authMkSendPreKB
  unfold authMkSendPreB
  iterate 3 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine letV_congr₂_eq (by env_eq) fun fhst hfhst => ?_
  have hfhstEq : fhst = (env₁.get (h₁.wk core₁)).2.2.2 := by
    simpa [mkcFhst, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfhst.symm
  have hbFhst : AuthFixedValOnlineBounded n fhst := hfhstEq ▸ hb
  iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine ite_congr₂ (by cases opk <;> env_eq) (ret_congr₂ (by env_eq)) ?_
  refine letV_congr₂_eq (by env_eq) fun hst hhst => ?_
  have hhstEq : hst = fhst.1 := by
    simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhst.symm
  have hbHst : AuthHybridValOnlineBounded n hst := hhstEq ▸ fixed_toHybrid hbFhst
  refine letV_congr₂_eq (by env_eq) fun st hstB => ?_
  have hstEq : st = (env₁.get (h₁.wk core₁)).2.2.2.1.1 := by
    have : st = hst.1 := by
      simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstB.symm
    rw [this, hhstEq, hfhstEq]
  have hbSt : AuthBaseValOnlineBounded n st := hstEq ▸ hb.base_le
  refine ite_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) ?_
  iterate 3 refine letV_congr₂ (by env_eq) fun _ => ?_
  refine letV_congr₂ (by cases opk <;> env_eq) fun _ => ?_
  refine ite_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) ?_
  refine ite_congr₂ (eAny_eval_eq (by dsimp only [asUsedSendSessions]; env_eq)
    (by simpa [asUsedSendSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      using hbSt.usedSendSessions_le) hKon hK fun _ => by env_eq) (ret_congr₂ (by env_eq)) ?_
  refine caseOptV_congr₂ (eFind_eval_eq (by dsimp only [asPrincipals]; env_eq)
    (by simpa [asPrincipals, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      using hbSt.principals_le) hKon hK fun _ => by env_eq) (ret_congr₂ (by env_eq)) fun _ => ?_
  refine letV_congr₂ (by env_eq) fun _ => ?_
  refine bindV_congr₂ (findHonestC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hKon hK) fun pp => ?_
  refine letV_congr₂ (by cases pp <;> env_eq) fun _ => ?_
  refine ite_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) ?_
  refine letV_congr₂ (by env_eq) fun _ => ?_
  refine bindV_congr₂ (koskBundleOkC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hKon hK) fun _ => ?_
  refine ite_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) ?_
  iterate 4 refine bindV_congr₂ rfl fun _ => ?_
  refine bindV_congr₂ (resolveSigPkC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hKon hK) fun _ => ?_
  iterate 2 refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
  refine ite_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) ?_
  refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
  refine caseOptV_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) fun _ => ?_
  iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
  iterate 2 refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
  refine bindV_congr₂ (checkBundleSpkHonIdealC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hKon hK) fun _ => ?_
  refine letV_congr₂ (by
    cases pp with
    | none => env_eq
    | some p =>
      simp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      exact eAny_eval_eq (by dsimp only [asSpkBundles]; env_eq)
        (by simpa [asSpkBundles, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
          using hbSt.spkBundles_le) hKon hK fun _ => by env_eq) fun _ => ?_
  refine letV_congr₂ (by cases pp <;> env_eq) fun _ => ?_
  refine letV_congr₂ (by env_eq) fun _ => ?_
  refine ite_congr₂ (by env_eq) ?_ ?_
  · iterate 2 refine bindV_congr₂ rfl fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
    refine caseOptV_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) fun _ => ?_
    iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine letV_congr₂ (allocSendSlotE_eval_congr (by env_eq) (by env_eq)) fun _ => ?_
    refine letV_congr₂ (by env_eq) fun _ => ?_
    refine letV_congr₂_eq (by ret_mk_eq) fun fhst' hfhst' => ?_
    have hbFhst' : AuthFixedValOnlineBounded n fhst' := by
      have : fhst' = (fhst.1, fhst.2.1, fhst.2.2.1, fhst'.2.2.2) := by
        have hEq : (fhst'.1, fhst'.2.1, fhst'.2.2.1) = (fhst.1, fhst.2.1, fhst.2.2.1) := by
          simpa [ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
            v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
            congrArg (fun q => (q.1, q.2.1, q.2.2.1)) hfhst'.symm
        rcases fhst' with ⟨a, b, c, d⟩; rcases hEq with ⟨rfl, rfl, rfl⟩; rfl
      rw [this]; exact fixed_withSlots hbFhst
    refine ite_congr₂ (by env_eq) (bindV_congr₂ rfl fun _ => ret_congr₂ (by env_eq)) ?_
    refine ite_congr₂ (by env_eq) ?_ ?_
    · iterate 2 refine bindV_congr₂ rfl fun _ => ?_
      refine bindV_congr₂ (finishAuthSendMkC_eval_eq S (by env_eq) (by env_eq)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbFhst') hKon hK) fun _ =>
        ret_congr₂ (by ret_mk_eq)
    · iterate 2 refine bindV_congr₂ rfl fun _ => ?_
      refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
      refine bindV_congr₂ (finishAuthSendMkC_eval_eq S (by env_eq) (by env_eq)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbFhst') hKon hK) fun _ =>
        ret_congr₂ (by ret_mk_eq)
  · iterate 3 refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
    refine bindV_congr₂ (caseOptV_congr₂ (by env_eq) (ret_congr₂ rfl) fun _ =>
      bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ret_congr₂ (by env_eq)) fun _ => ?_
    refine letV_congr₂ (by env_eq) fun _ => ?_
    refine bindV_congr₂ (hkdfRoC_eval_eq _ _ _ _ _ _ (by env_eq) (by env_eq)
      (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq]; exact le_rfl) hRoK hRoOld) fun _ => ?_
    iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
    refine bindV_congr₂ (rootRoC_eval_eq _ _ _ _ _ _ _ _ (by env_eq) (by env_eq) (by env_eq)
      (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq]; exact le_rfl) hRootK hRootOld) fun _ => ?_
    iterate 3 refine letV_congr₂ (by env_eq) fun _ => ?_
    iterate 3 refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
    refine caseOptV_congr₂ (by env_eq) (ret_congr₂ (by env_eq)) fun _ => ?_
    iterate 2 refine letV_congr₂ (by env_eq) fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
    refine letV_congr₂ (by env_eq) fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by env_eq)) fun _ => ?_
    refine bindV_congr₂ (finishAuthHybridSendC_eval_eq S _ _ _ _ _ _ (by env_eq) (by env_eq)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbHst) hKon hK) fun _ => ?_
    exact ret_congr₂ (by ret_mk_eq)

private theorem AllLeaves_of_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {oa : OracleComp spec α} (h : ∀ x ∈ support oa, P x) : AllLeaves P oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AllLeaves.pure (h a (by simp only [support_pure, Set.mem_singleton_iff]))
  | query_bind q k ih =>
    intro u; exact ih u fun x hx => h x (by rw [mem_support_bind_iff]; exact ⟨u, mem_support_query q u, hx⟩)

private theorem hkdfRoC_allLeaves {K : ℕ} {Γ Δ : List PT} {st : Var Γ authStateTy} [h : Ext Γ Δ]
    {sec : Expr pqxdhOps Δ (B 192)} {env : Env Δ} {ro0 : List (List UInt8 × drKeyTy.denote)}
    (hEq : valRoCache (env.get (h.wk st)) = ro0) (hRo : ro0.length ≤ K) :
    AllLeaves (fun p => CacheStepAtMostOne ro0 p.2) ((hkdfRoC K st sec).eval env) :=
  AllLeaves_of_mem_support fun p hp => by rw [← hEq]; exact hkdfRoC_step st sec env (hEq ▸ hRo) p hp

private theorem rootRoC_allLeaves {K : ℕ} {Γ Δ : List PT} {st : Var Γ authStateTy} [h : Ext Γ Δ]
    {rk dh : Expr pqxdhOps Δ (B 32)} {env : Env Δ}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    (hEq : valRootRoCache (env.get (h.wk st)) = root0) (hRoot : root0.length ≤ K) :
    AllLeaves (fun p => CacheStepAtMostOne root0 p.2) ((rootRoC K st rk dh).eval env) :=
  AllLeaves_of_mem_support fun p hp => by rw [← hEq]; exact rootRoC_step st rk dh env (hEq ▸ hRoot) p hp

private theorem finishAuthHybridSendC_allLeaves (S : Setup) (K n : ℕ)
    (ro0 : List (List UInt8 × drKeyTy.denote)) (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))
    {Γ₁ Δ : List PT} {hst : Var Γ₁ authHybridStateTy} [h₁_ext : Ext Γ₁ Δ]
    {args : Expr pqxdhOps Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishSendArgsTy} {env : Env Δ}
    (hb : AuthHybridValOnlineBounded n (env.get (h₁_ext.wk hst)))
    (hRo0 : valRoCache (env.get (h₁_ext.wk hst)).1 = ro0)
    (hRoot0 : valRootRoCache (env.get (h₁_ext.wk hst)).1 = root0)
    (hRo : CacheStepAtMostOne ro0 (args.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (hRoot : CacheStepAtMostOne root0 (args.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) :
    AllLeaves (fun p => AuthHybridValOnlineBounded (n + 1) p.2 ∧
      CacheStepAtMostOne ro0 (valRoCache p.2.1) ∧ CacheStepAtMostOne root0 (valRootRoCache p.2.1))
      ((finishAuthHybridSendC S K hst args).eval env) := by
  rw [← hRo0, ← hRoot0]; exact finishAuthHybridSendC_leaves S K hst args env hb (hRo0 ▸ hRo) (hRoot0 ▸ hRoot)

private theorem authMkSendPreKB_leaves (S : Setup) (K_on K_ro n : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy) [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk core)).2.2.2)
    (hRoK : (valRoCache (env.get (h₁.wk core)).2.2.2.1.1).length ≤ K_ro)
    (hRootK : (valRootRoCache (env.get (h₁.wk core)).2.2.2.1.1).length ≤ K_ro) :
    AllLeaves (MkPreLeafOk n
        (valRoCache (env.get (h₁.wk core)).2.2.2.1.1)
        (valRootRoCache (env.get (h₁.wk core)).2.2.2.1.1))
      ((authMkSendPreKB S K_on K_ro opk core x).eval env) := by
  let core0 := env.get (h₁.wk core)
  let ro0 := valRoCache core0.2.2.2.1.1
  let root0 := valRootRoCache core0.2.2.2.1.1
  change AllLeaves (MkPreLeafOk n ro0 root0) _
  apply Leaves.run
  unfold authMkSendPreKB
  unfold _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase.authMkSendPreKB
  iterate 3 refine letV_leavesL fun _ => ?_
  refine letV_leavesL_eq fun fhst hfhst => ?_
  have hfhstEq : fhst = core0.2.2.2 := by
    simpa [mkcFhst, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, core0] using hfhst
  refine letV_leavesL fun _ => ?_
  refine letV_leavesL_eq fun noneDone hnd => ?_
  have hND : MkPreLeafOk n ro0 root0 noneDone := by
    have : ∃ r, noneDone = .inl (r, core0) :=
      ⟨_, by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, core0] using hnd⟩
    rcases this with ⟨_, rfl⟩
    exact ⟨hb.mono (Nat.le_succ n), CacheStepAtMostOne.refl ro0, CacheStepAtMostOne.refl root0⟩
  refine ite_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) ?_
  refine letV_leavesL_eq fun hst hhst => ?_
  have hhstEq : hst = core0.2.2.2.1 := by
    simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstEq] using hhst
  refine letV_leavesL_eq fun st hstB => ?_
  have hstEq : st = core0.2.2.2.1.1 := by
    simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hstB
  refine ite_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) ?_
  iterate 4 refine letV_leavesL fun _ => ?_
  iterate 2 refine ite_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) ?_
  refine caseOptV_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) fun _ => ?_
  refine letV_leavesL fun _ => ?_
  refine bindV_leavesL_const fun _ => ?_
  refine letV_leavesL fun _ => ?_
  refine ite_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) ?_
  refine letV_leavesL fun _ => ?_
  refine bindV_leavesL_const fun _ => ?_
  refine ite_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) ?_
  iterate 7 refine bindV_leavesL_const fun _ => ?_
  refine ite_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) ?_
  refine bindV_leavesL_const fun _ => ?_
  refine caseOptV_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) fun _ => ?_
  iterate 2 refine letV_leavesL fun _ => ?_
  iterate 3 refine bindV_leavesL_const fun _ => ?_
  iterate 3 refine letV_leavesL fun _ => ?_
  refine ite_leavesL ?_ ?_
  · iterate 3 refine bindV_leavesL_const fun _ => ?_
    refine caseOptV_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) fun _ => ?_
    iterate 4 refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun fhst' hfhst' => ?_
    have hbFhst' : AuthFixedValOnlineBounded n fhst' ∧ valRoCache fhst'.1.1 = ro0 ∧ valRootRoCache fhst'.1.1 = root0 := by
      have hEq : (fhst'.1, fhst'.2.1, fhst'.2.2.1) = (core0.2.2.2.1, core0.2.2.2.2.1, core0.2.2.2.2.2.1) := by
        simpa [ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
          v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstEq] using
          congrArg (fun q => (q.1, q.2.1, q.2.2.1)) hfhst'
      have hShape : fhst' = (core0.2.2.2.1, core0.2.2.2.2.1, core0.2.2.2.2.2.1, fhst'.2.2.2) := by
        rcases fhst' with ⟨a, b, c, d⟩; rcases hEq with ⟨rfl, rfl, rfl⟩; rfl
      rw [hShape]; exact ⟨fixed_withSlots hb, rfl, rfl⟩
    refine ite_leavesL (bindV_leavesL_const fun _ => ret_leavesL ?_) (ite_leavesL ?_ ?_)
    · dsimp only [MkPreLeafOk, MkContBounded, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_succ, env_get_zero]; exact hbFhst'
    · iterate 2 refine bindV_leavesL_const fun _ => ?_
      refine bindV_leavesL (finishAuthSendMkC_leaves S K_on n
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbFhst'.1)) fun res ⟨hB, hRo, hRoot⟩ => ?_
      have hRo' : CacheStepAtMostOne ro0 (valRoCache res.2.1.1) := by
        rw [← hbFhst'.2.1]; simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRo
      have hRoot' : CacheStepAtMostOne root0 (valRootRoCache res.2.1.1) := by
        rw [← hbFhst'.2.2]; simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoot
      refine ret_leavesL ?_
      dsimp only [MkPreLeafOk, mkcMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_zero]; exact ⟨hB, hRo', hRoot'⟩
    · iterate 3 refine bindV_leavesL_const fun _ => ?_
      refine bindV_leavesL (finishAuthSendMkC_leaves S K_on n
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbFhst'.1)) fun res ⟨hB, hRo, hRoot⟩ => ?_
      have hRo' : CacheStepAtMostOne ro0 (valRoCache res.2.1.1) := by
        rw [← hbFhst'.2.1]; simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRo
      have hRoot' : CacheStepAtMostOne root0 (valRootRoCache res.2.1.1) := by
        rw [← hbFhst'.2.2]; simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoot
      refine ret_leavesL ?_
      dsimp only [MkPreLeafOk, mkcMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_zero]; exact ⟨hB, hRo', hRoot'⟩
  · iterate 4 refine bindV_leavesL_const fun _ => ?_
    refine letV_leavesL fun _ => ?_
    refine bindV_leavesL (hkdfRoC_allLeaves
      (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq]; rfl) hRoK) fun drOut hDrRo => ?_
    refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun roC' hroC' => ?_
    have hRoC' : CacheStepAtMostOne ro0 roC' := by
      have : roC' = drOut.2 := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hroC'
      rw [this]; exact hDrRo
    refine bindV_leavesL_const fun _ => ?_
    refine bindV_leavesL (rootRoC_allLeaves
      (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq]; rfl) hRootK) fun rkOut hRkRoot => ?_
    iterate 2 refine letV_leavesL fun _ => ?_
    refine letV_leavesL_eq fun rootC' hrootC' => ?_
    have hRootC' : CacheStepAtMostOne root0 rootC' := by
      have : rootC' = rkOut.2 := by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hrootC'
      rw [this]; exact hRkRoot
    iterate 3 refine bindV_leavesL_const fun _ => ?_
    refine caseOptV_leavesL (ret_leavesL (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hND)) fun _ => ?_
    iterate 2 refine letV_leavesL fun _ => ?_
    refine bindV_leavesL_const fun _ => ?_
    refine letV_leavesL fun _ => ?_
    refine bindV_leavesL_const fun _ => ?_
    refine bindV_leavesL (finishAuthHybridSendC_allLeaves S K_on n ro0 root0
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq, core0] using fixed_toHybrid hb)
      (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq]; rfl)
      (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq]; rfl)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoC')
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRootC'))
      fun out ⟨hOutB, hOutRo, hOutRoot⟩ => ?_
    refine ret_leavesL ?_
    dsimp only [MkPreLeafOk, mkcMk, ahsfUpd, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hfhstEq]
    exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le,
      Nat.le_trans hb.mkSaltCache_le (Nat.le_succ n)⟩, hOutRo, hOutRoot⟩

private theorem eFind_congr₂ {Δ₁ Δ₂ : List PT} {τ : PT} {K₁ K₂ n : ℕ}
    {xs₁ : Expr pqxdhOps Δ₁ (.list τ)} {xs₂ : Expr pqxdhOps Δ₂ (.list τ)}
    {p₁ : Var (τ :: Δ₁) τ → Expr pqxdhOps (τ :: Δ₁) .bool}
    {p₂ : Var (τ :: Δ₂) τ → Expr pqxdhOps (τ :: Δ₂) .bool}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    (hxs : xs₁.eval env₁ = xs₂.eval env₂)
    (hp : ∀ x : τ.denote, (p₁ .zero).eval (.cons x env₁) = (p₂ .zero).eval (.cons x env₂))
    (hLen : (xs₁.eval env₁).length ≤ n) (hK₁ : n ≤ K₁) (hK₂ : n ≤ K₂) :
    (eFind K₁ xs₁ p₁).eval env₁ = (eFind K₂ xs₂ p₂).eval env₂ := by
  simp only [eFind, Expr.eval, ← hxs, take_eq_of_le (Nat.le_trans hLen hK₁) (Nat.le_trans hLen hK₂)]
  congr 1; funext x; exact hp x

private theorem sidEq_congr₂ {Δ₁ Δ₂ : List PT}
    {a₁ b₁ : Expr pqxdhOps Δ₁ sessionIdTy} {env₁ : Env Δ₁}
    {a₂ b₂ : Expr pqxdhOps Δ₂ sessionIdTy} {env₂ : Env Δ₂}
    (ha : a₁.eval env₁ = a₂.eval env₂) (hb : b₁.eval env₁ = b₂.eval env₂) :
    (sidEq a₁ b₁).eval env₁ = (sidEq a₂ b₂).eval env₂ := by
  dsimp only [sidEq, eLet2, eLet, eCaseSum,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.nat2Eq,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.nat3Eq,
    natEq, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, ha, hb]

local macro "val_rfl" : tactic =>
  `(tactic| (
    try rw [sameSaltKeyE_eval, sameSaltKeyE_eval]
    try rw [firstMsgADE_eval, firstMsgADE_eval]
    dsimp only [ahsBase, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk, ahsfUpd, ahsfUpdSlots, ahsfMkSlots, ahsfMk,
      parHstDec, parFinishTag, parMatchedSess?, parIsUncorrSender, parSameEph,
      parSecrets, parDhRatchet, parKEntry,
      iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      pkmPqRatchetMsg, pkmAeadCt, pkmEphAPk, pkmHdr, hdrIkAPk, peIkAPk,
      boolOr, isSomeE, natLt, natEq, sidEq, bytesBeq, aNone,
      eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]))

local macro "val_rfl0" : tactic =>
  `(tactic| (
    dsimp only [ahsBase, ahsfSlots, parHstDec, eCaseOpt, v, Expr.eval, Ext.refl_wk]
    simp only [env_get_zero]))

local macro "env_norm" : tactic =>
  `(tactic| (
    dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]))

private theorem authMkRecvPreKB_eval_eq (S : Setup) {K_on K_ro K n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ₁ Γ₃ Γ₄ Δ₂ : List PT}
    (core₁ : Var Γ₁ prfMkCoreTy) (x₁ : Var Γ₂ recvQTy) [h₁ : Ext Γ₁ Δ₁] [h₂ : Ext Γ₂ Δ₁] (env₁ : Env Δ₁)
    (core₂ : Var Γ₃ prfMkCoreTy) (x₂ : Var Γ₄ recvQTy) [h₃ : Ext Γ₃ Δ₂] [h₄ : Ext Γ₄ Δ₂] (env₂ : Env Δ₂)
    (hcore : env₁.get (h₁.wk core₁) = env₂.get (h₃.wk core₂))
    (hx : env₁.get (h₂.wk x₁) = env₂.get (h₄.wk x₂))
    (hb : AuthFixedValOnlineBounded n (env₁.get (h₁.wk core₁)).2.2.2)
    (hKon : n ≤ K_on) (hK : n ≤ K)
    (hRoK : (valRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K_ro)
    (hRoOld : (valRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K)
    (hRootK : (valRootRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K_ro)
    (hRootOld : (valRootRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1).length ≤ K) :
    (authMkRecvPreKB S K_on K_ro opk core₁ x₁).eval env₁ =
      (authMkRecvPreB S K opk core₂ x₂).eval env₂ := by
  let ro0 := valRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1
  let root0 := valRootRoCache (env₁.get (h₁.wk core₁)).2.2.2.1.1
  unfold authMkRecvPreKB AuthCoreKArmsBase.authMkRecvPreKB authMkRecvPreB
  refine letV_congr₂ (by dsimp only [mkcSecb, v, Expr.eval]; rw [hcore]) fun _ => ?_
  refine letV_congr₂ (by dsimp only [mkcIdx, v, Expr.eval, Ext.step_wk]; simp only [env_get_succ]; rw [hcore]) fun _ => ?_
  refine letV_congr₂ (by dsimp only [mkcSentChal, v, Expr.eval, Ext.step_wk]; simp only [env_get_succ]; rw [hcore]) fun _ => ?_
  refine letV_congr₂_eq (by dsimp only [mkcFhst, v, Expr.eval, Ext.step_wk]; simp only [env_get_succ]; rw [hcore]) fun fhst hfhst => ?_
  have hfhstEq : fhst = (env₁.get (h₁.wk core₁)).2.2.2 := by
    dsimp only [mkcFhst, v, Expr.eval, Ext.step_wk] at hfhst
    simp only [env_get_succ] at hfhst
    exact hfhst.symm
  have hbFhst : AuthFixedValOnlineBounded n fhst := hfhstEq ▸ hb
  refine letV_congr₂ (by val_rfl0) fun _ => ?_
  refine letV_congr₂_eq (by val_rfl) fun hst hhst => ?_
  have hhstEq : hst = fhst.1 := by
    dsimp only [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hhst
    simp only [env_get_succ, env_get_zero] at hhst
    exact hhst.symm
  have hbHst : AuthHybridValOnlineBounded n hst := hhstEq ▸ fixed_toHybrid hbFhst
  refine letV_congr₂ (by val_rfl) fun _ => ?_
  refine letV_congr₂_eq (by val_rfl) fun cache hcache => ?_
  have hcacheEq : cache = fhst.2.2.1 := by
    dsimp only [ahsfMkSaltCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hcache
    simp only [env_get_succ, env_get_zero] at hcache
    exact hcache.symm
  have hcLen : cache.length ≤ n := hcacheEq ▸ hbFhst.mkSaltCache_le
  refine letV_congr₂ (by dsimp only [v, Expr.eval, Ext.step_wk]; simp only [env_get_succ]; rw [hx]) fun _ => ?_
  refine letV_congr₂ (by val_rfl) fun _ => ?_
  have hhstRo : valRoCache hst.1 = ro0 := by rw [hhstEq, hfhstEq]
  have hhstRoot : valRootRoCache hst.1 = root0 := by rw [hhstEq, hfhstEq]
  refine bindV_congr₂_leaves
    (prepareAuthHybridRecvC_eval_eq S opk _ _ _ _ _ _ (by val_rfl)
      (by dsimp only [Ext.step_wk]; simp only [env_get_succ]; exact hx)
      (by env_norm; exact hbHst) hKon hK)
    (prepareAuthHybridRecvC_leaves S K_on opk _ _ _
      (by env_norm; exact hbHst))
    fun prep? hprepL => ?_
  refine caseOptV_congr₂_eq (by val_rfl0) (ret_congr₂ (by val_rfl)) fun prep hprepSome => ?_
  have hbPrep : PreparedRecvValBounded n ro0 root0 prep := by
    dsimp only [v, Expr.eval, Ext.refl_wk] at hprepSome
    simp only [env_get_zero] at hprepSome
    have hP := hprepL prep hprepSome
    dsimp only [Ext.step_wk, Ext.refl_wk] at hP
    simp only [env_get_succ, env_get_zero] at hP
    rw [hhstRo, hhstRoot] at hP
    exact hP
  refine letV_congr₂_eq (by val_rfl0) fun st hstVal => ?_
  have hstEq : st = prep.2.2.2.2.2.2.2.2.1.1 := by
    dsimp only [ahsBase, parHstDec, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hstVal
    simp only [env_get_zero] at hstVal
    exact hstVal.symm
  have hstRo : valRoCache st = ro0 := hstEq ▸ hbPrep.ro_eq
  have hstRoot : valRootRoCache st = root0 := hstEq ▸ hbPrep.root_eq
  refine letV_congr₂_eq (by val_rfl) fun fTag hfTag => ?_
  have hfTagEq : fTag = prep.2.2.2.2.2.2.2.2.2 := by
    dsimp only [parFinishTag, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hfTag
    simp only [env_get_succ, env_get_zero] at hfTag
    exact hfTag.symm
  have hbTag : RecvTagValBounded n ro0 root0 fTag := hfTagEq ▸ hbPrep.tag_bounded
  refine letV_congr₂ (by val_rfl) fun _ => ?_
  refine ite_congr₂ (by val_rfl0) ?_ ?_
  · refine caseOptV_congr₂ (by val_rfl) ?_ fun _ => ?_
    · refine bindV_congr₂ rfl fun _ => bindV_congr₂ rfl fun _ =>
        bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
      refine caseOptV_congr₂ (by val_rfl0) ?_ fun _ => ?_
      · refine bindV_congr₂ (recvFinishTagRunC_eval_eq S _ _ _ _ _ _ (by val_rfl) rfl
          (by env_norm; exact hbTag) hKon hK) fun _ =>
          ret_congr₂ (by val_rfl)
      · refine letV_congr₂ (allocRecvSlotE_eval_congr (by val_rfl) (by val_rfl)) fun _ => ?_
        refine letV_congr₂ (by val_rfl) fun _ => ?_
        exact finishRecvUnmatchedMkPreC_eval_eq S (by val_rfl0) (by val_rfl) (by val_rfl) (by val_rfl)
          (by env_norm; exact hbPrep) hKon hK
    · refine ite_congr₂ (by val_rfl) ?_ ?_
      · refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
        refine caseOptV_congr₂ (by val_rfl0) ?_ fun _ => ?_
        · refine bindV_congr₂ (recvFinishTagRunC_eval_eq S _ _ _ _ _ _ (by val_rfl) rfl
            (by env_norm; exact hbTag) hKon hK) fun _ =>
            ret_congr₂ (by val_rfl)
        · refine letV_congr₂ (by val_rfl0) fun _ => ?_
          refine letV_congr₂ (lookupSendSlotOrZeroE_eval_congr (by val_rfl) (by val_rfl)) fun _ => ?_
          refine letV_congr₂ (by val_rfl) fun _ => ?_
          refine ite_congr₂ (by val_rfl) ?_ ?_
          · refine ite_congr₂ (by val_rfl) ?_ ?_
            · refine bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by val_rfl) (by val_rfl) (by val_rfl)
                (by env_norm; exact hbPrep) hKon hK) fun _ =>
                ret_congr₂ (by val_rfl)
            · refine caseOptV_congr₂
                (eFind_congr₂ (by val_rfl)
                  (fun _ => by
                    dsimp only [Expr.eval]
                    exact congrArg₂ and (sidEq_congr₂ (by val_rfl0) (by val_rfl)) (by val_rfl))
                  (by env_norm; exact hcLen)
                  hKon hK)
                (ret_congr₂ (by val_rfl)) fun _ => ?_
              refine bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by val_rfl) (by val_rfl) (by val_rfl)
                (by env_norm; exact hbPrep) hKon hK) fun _ =>
                ret_congr₂ (by val_rfl)
          · refine ite_congr₂ (by val_rfl) ?_ ?_
            · refine ite_congr₂ (by val_rfl) ?_ ?_
              · refine bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by val_rfl) (by val_rfl) (by val_rfl)
                  (by env_norm; exact hbPrep) hKon hK) fun _ =>
                  ret_congr₂ (by val_rfl)
              · refine caseOptV_congr₂
                  (eFind_congr₂ (by val_rfl)
                    (fun _ => by
                      dsimp only [Expr.eval]
                      exact congrArg₂ and (sidEq_congr₂ (by val_rfl0) (by val_rfl)) (by val_rfl))
                    (by env_norm; exact hcLen)
                    hKon hK)
                  ?_ fun _ => ?_
                · refine bindV_congr₂ rfl fun _ => letV_congr₂ (by val_rfl) fun _ =>
                    bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by val_rfl) (by val_rfl) (by val_rfl)
                      (by env_norm; exact hbPrep) hKon hK) fun _ =>
                      ret_congr₂ (by val_rfl)
                · refine bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by val_rfl) (by val_rfl) (by val_rfl)
                    (by env_norm; exact hbPrep) hKon hK) fun _ =>
                    ret_congr₂ (by val_rfl)
            · refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ =>
                bindV_congr₂ (finishAuthRecvMkC_eval_eq S (by val_rfl) (by val_rfl) (by val_rfl)
                  (by env_norm; exact hbPrep) hKon hK) fun _ =>
                  ret_congr₂ (by val_rfl)
      · refine bindV_congr₂ rfl fun _ => bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
        refine caseOptV_congr₂ (by val_rfl0) ?_ fun _ => ?_
        · refine bindV_congr₂ (recvFinishTagRunC_eval_eq S _ _ _ _ _ _ (by val_rfl) rfl
            (by env_norm; exact hbTag) hKon hK) fun _ =>
            ret_congr₂ (by val_rfl)
        · refine letV_congr₂ (allocRecvSlotE_eval_congr (by val_rfl) (by val_rfl)) fun _ => ?_
          refine letV_congr₂ (by val_rfl) fun _ => ?_
          exact finishRecvUnmatchedMkPreC_eval_eq S (by val_rfl0) (by val_rfl) (by val_rfl) (by val_rfl)
            (by env_norm; exact hbPrep) hKon hK
  · refine bindV_congr₂ (hkdfRoC_eval_eq _ _ _ _ _ _ (by val_rfl) (by val_rfl)
      (nRo := ro0.length)
      (by env_norm; rw [hstRo]) hRoK hRoOld) fun _ => ?_
    refine letV_congr₂ (by val_rfl0) fun _ => ?_
    refine letV_congr₂ (by val_rfl) fun _ => ?_
    refine bindV_congr₂ (rootRoC_eval_eq _ _ _ _ _ _ _ _ (by val_rfl) (by val_rfl) (by val_rfl)
      (nRoot := root0.length)
      (by env_norm; rw [hstRoot]) hRootK hRootOld) fun _ => ?_
    refine letV_congr₂ (by val_rfl0) fun _ => ?_
    iterate 2 refine letV_congr₂ (by val_rfl) fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
    refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
    refine caseOptV_congr₂ (by val_rfl0) ?_ fun _ => ?_
    · refine bindV_congr₂ (recvFinishTagRunC_eval_eq S _ _ _ _ _ _ (by val_rfl) rfl
        (by env_norm; exact hbTag) hKon hK) fun _ =>
        ret_congr₂ (by val_rfl)
    · refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun _ => ?_
      refine letV_congr₂ (by val_rfl) fun _ => ?_
      refine bindV_congr₂ (queryPrim_congr₂ _ (by val_rfl)) fun pt? => ?_
      refine letV_congr₂ (by cases pt? with | none => val_rfl0 | some _ => val_rfl) fun _ => ?_
      refine bindV_congr₂ (recvFinishTagRunC_eval_eq S _ _ _ _ _ _ (by val_rfl) (by val_rfl0)
        (by env_norm; exact hbTag) hKon hK) fun _ =>
        ret_congr₂ (by val_rfl)

private theorem authMkRecvPreKB_leaves (S : Setup) (K_on K_ro : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy) [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk core)).2.2.2)
    (hRoK : (valRoCache (env.get (h₁.wk core)).2.2.2.1.1).length ≤ K_ro)
    (hRootK : (valRootRoCache (env.get (h₁.wk core)).2.2.2.1.1).length ≤ K_ro) :
    AllLeaves (MkPreLeafOk n (valRoCache (env.get (h₁.wk core)).2.2.2.1.1)
      (valRootRoCache (env.get (h₁.wk core)).2.2.2.1.1))
      ((authMkRecvPreKB S K_on K_ro opk core x).eval env) := by
  let fhst0 := (env.get (h₁.wk core)).2.2.2
  let ro0 := valRoCache fhst0.1.1
  let root0 := valRootRoCache fhst0.1.1
  change AllLeaves (MkPreLeafOk n ro0 root0) _
  apply Leaves.run
  unfold authMkRecvPreKB AuthCoreKArmsBase.authMkRecvPreKB
  iterate 3 refine letV_leavesL fun _ => ?_
  refine letV_leavesL_eq fun fhst hfhst => ?_
  have hfhstEq : fhst = fhst0 := by
    dsimp only [mkcFhst, v, Expr.eval, Ext.step_wk, env_get_succ, fhst0] at hfhst; exact hfhst
  refine letV_leavesL fun _ => ?_
  refine letV_leavesL_eq fun hst hhst => ?_
  have hhstEq : hst = fhst0.1 := by
    dsimp only [ahsfHybrid, v, Expr.eval, Ext.step_wk, env_get_succ] at hhst
    rw [hfhstEq] at hhst; exact hhst
  refine letV_leavesL fun _ => ?_
  refine letV_leavesL_eq fun cache hcache => ?_
  have hcacheEq : cache = fhst0.2.2.1 := by
    dsimp only [ahsfMkSaltCache, v, Expr.eval, Ext.step_wk, env_get_succ] at hcache
    rw [hfhstEq] at hcache; exact hcache
  have hcLen : cache.length ≤ n := hcacheEq ▸ hb.mkSaltCache_le
  have hcLen1 : cache.length ≤ n + 1 := Nat.le_trans hcLen (Nat.le_succ n)
  iterate 2 refine letV_leavesL fun _ => ?_
  refine bindV_leavesL (prepareAuthHybridRecvC_leaves S K_on opk _ _ _
    (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; rw [hhstEq]; exact fixed_toHybrid hb))
    fun prep? hprepL => ?_
  refine caseOptV_leavesL_eq ?_ fun prep hprepSome => ?_
  · refine ret_leavesL ?_
    dsimp only [MkPreLeafOk, mkcMk, ahsfUpd, ahsfHybrid, ahsfMkSaltCache, ahsfSlots, aNone,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    rw [hfhstEq]
    have hb1 := hb.mono (Nat.le_succ n)
    exact ⟨⟨hb1.base_le, hb1.initKemRecs_le, hb1.recvKemRecs_le, hb1.idealSessions_le, hb1.mkSaltCache_le⟩,
      CacheStepAtMostOne.refl ro0, CacheStepAtMostOne.refl root0⟩
  · have hbPrep : PreparedRecvValBounded n ro0 root0 prep := by
      dsimp only [v, Expr.eval, Ext.refl_wk, env_get_zero] at hprepSome
      have hP := hprepL prep hprepSome
      dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hP
      rw [hhstEq] at hP; exact hP
    refine letV_leavesL_eq fun st hstVal => ?_
    have hstEq : st = prep.2.2.2.2.2.2.2.2.1.1 := by
      dsimp only [ahsBase, parHstDec, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hstVal
      exact hstVal
    have hstRo : valRoCache st = ro0 := hstEq ▸ hbPrep.ro_eq
    have hstRoot : valRootRoCache st = root0 := hstEq ▸ hbPrep.root_eq
    refine letV_leavesL_eq fun fTag hfTag => ?_
    have hfTagEq : fTag = prep.2.2.2.2.2.2.2.2.2 := by
      dsimp only [parFinishTag, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hfTag
      exact hfTag
    have hbTag : RecvTagValBounded n ro0 root0 fTag := hfTagEq ▸ hbPrep.tag_bounded
    refine letV_leavesL fun _ => ?_
    refine ite_leavesL ?_ ?_
    · refine caseOptV_leavesL ?_ fun _ => ?_
      · iterate 3 refine bindV_leavesL_const fun _ => ?_
        refine caseOptV_leavesL ?_ fun _ => ?_
        · refine bindV_leavesL (recvFinishTagRunC_leaves S K_on (n := n) (ro0 := ro0) (root0 := root0) _ _ _
            (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbTag)
            (by rintro _ ⟨⟩)) fun out ⟨hOutB, hOutRo, hOutRoot⟩ => ?_
          refine ret_leavesL ?_
          dsimp only [MkPreLeafOk, mkcMk, ahsfMkSlots, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
          exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le, hcLen1⟩,
            hOutRo, hOutRoot⟩
        · refine letV_leavesL fun _ => ?_
          refine letV_leavesL_eq fun core' hcore' => ?_
          have hcCore' : core'.2.2.2.2.2.1.length ≤ n := by
            dsimp only [mkcMk, ahsfUpdSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
              v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hcore'
            rw [hcore', hfhstEq]; exact hb.mkSaltCache_le
          exact ⟨finishRecvUnmatchedMkPreC_leaves S K_on n ro0 root0
            (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
            (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcCore')⟩
      · refine ite_leavesL ?_ ?_
        · refine bindV_leavesL_const fun _ => ?_
          refine caseOptV_leavesL ?_ fun _ => ?_
          · refine bindV_leavesL (recvFinishTagRunC_leaves S K_on (n := n) (ro0 := ro0) (root0 := root0) _ _ _
              (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbTag)
              (by rintro _ ⟨⟩)) fun out ⟨hOutB, hOutRo, hOutRoot⟩ => ?_
            refine ret_leavesL ?_
            dsimp only [MkPreLeafOk, mkcMk, ahsfMkSlots, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
            exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le, hcLen1⟩,
              hOutRo, hOutRoot⟩
          · iterate 3 refine letV_leavesL fun _ => ?_
            refine ite_leavesL ?_ ?_
            · refine ite_leavesL ?_ ?_
              · refine bindV_leavesL (finishAuthRecvMkC_leaves S K_on n ro0 root0
                  (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
                  (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcLen1))
                  fun res ⟨hB, hRo, hRoot⟩ => ?_
                refine ret_leavesL ?_
                dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                  v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                exact ⟨fixed_withSlots hB, hRo, hRoot⟩
              · refine caseOptV_leavesL ?_ fun _ => ?_
                · refine ret_leavesL ?_
                  dsimp only [MkPreLeafOk, MkContBounded, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                  exact ⟨hbPrep, hcLen⟩
                · refine bindV_leavesL (finishAuthRecvMkC_leaves S K_on n ro0 root0
                    (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
                    (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcLen1))
                    fun res ⟨hB, hRo, hRoot⟩ => ?_
                  refine ret_leavesL ?_
                  dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                    v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                  exact ⟨fixed_withSlots hB, hRo, hRoot⟩
            · refine ite_leavesL ?_ ?_
              · refine ite_leavesL ?_ ?_
                · refine bindV_leavesL (finishAuthRecvMkC_leaves S K_on n ro0 root0
                    (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
                    (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcLen1))
                    fun res ⟨hB, hRo, hRoot⟩ => ?_
                  refine ret_leavesL ?_
                  dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                    v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                  exact ⟨fixed_withSlots hB, hRo, hRoot⟩
                · refine caseOptV_leavesL ?_ fun _ => ?_
                  · refine bindV_leavesL_const fun _ => ?_
                    refine letV_leavesL_eq fun cache' hcache' => ?_
                    have hc'Len : cache'.length ≤ n + 1 := by
                      dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hcache'
                      simp only [env_get_succ, env_get_zero] at hcache'
                      rw [hcache']; simp only [List.length_cons]; omega
                    refine bindV_leavesL (finishAuthRecvMkC_leaves S K_on n ro0 root0
                      (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
                      (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hc'Len))
                      fun res ⟨hB, hRo, hRoot⟩ => ?_
                    refine ret_leavesL ?_
                    dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                      v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                    exact ⟨fixed_withSlots hB, hRo, hRoot⟩
                  · refine bindV_leavesL (finishAuthRecvMkC_leaves S K_on n ro0 root0
                      (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
                      (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcLen1))
                      fun res ⟨hB, hRo, hRoot⟩ => ?_
                    refine ret_leavesL ?_
                    dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                      v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                    exact ⟨fixed_withSlots hB, hRo, hRoot⟩
              · refine bindV_leavesL_const fun _ => ?_
                refine bindV_leavesL (finishAuthRecvMkC_leaves S K_on n ro0 root0
                  (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
                  (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcLen1))
                  fun res ⟨hB, hRo, hRoot⟩ => ?_
                refine ret_leavesL ?_
                dsimp only [MkPreLeafOk, mkcMk, ahsfUpdSlots, ahsfMkSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                  v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
                exact ⟨fixed_withSlots hB, hRo, hRoot⟩
        · iterate 2 refine bindV_leavesL_const fun _ => ?_
          refine caseOptV_leavesL ?_ fun _ => ?_
          · refine bindV_leavesL (recvFinishTagRunC_leaves S K_on (n := n) (ro0 := ro0) (root0 := root0) _ _ _
              (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbTag)
              (by rintro _ ⟨⟩)) fun out ⟨hOutB, hOutRo, hOutRoot⟩ => ?_
            refine ret_leavesL ?_
            dsimp only [MkPreLeafOk, mkcMk, ahsfMkSlots, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
            exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le, hcLen1⟩,
              hOutRo, hOutRoot⟩
          · refine letV_leavesL fun _ => ?_
            refine letV_leavesL_eq fun core' hcore' => ?_
            have hcCore' : core'.2.2.2.2.2.1.length ≤ n := by
              dsimp only [mkcMk, ahsfUpdSlots, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
                v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hcore'
              rw [hcore', hfhstEq]; exact hb.mkSaltCache_le
            exact ⟨finishRecvUnmatchedMkPreC_leaves S K_on n ro0 root0
              (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbPrep)
              (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hcCore')⟩
    · refine bindV_leavesL
        (hkdfRoC_allLeaves
          (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hstRo) hRoK)
        fun drOut hDrRo => ?_
      refine letV_leavesL fun _ => ?_
      refine letV_leavesL_eq fun roC' hroC' => ?_
      have hRoC' : CacheStepAtMostOne ro0 roC' := by
        dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hroC'
        rw [hroC']; exact hDrRo
      refine bindV_leavesL
        (rootRoC_allLeaves
          (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hstRoot) hRootK)
        fun rkOut hRkRoot => ?_
      iterate 2 refine letV_leavesL fun _ => ?_
      refine letV_leavesL_eq fun rootC' hrootC' => ?_
      have hRootC' : CacheStepAtMostOne root0 rootC' := by
        dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hrootC'
        rw [hrootC']; exact hRkRoot
      iterate 3 refine bindV_leavesL_const fun _ => ?_
      refine caseOptV_leavesL ?_ fun _ => ?_
      · refine bindV_leavesL (recvFinishTagRunC_leaves S K_on (n := n) (ro0 := ro0) (root0 := root0) _ _ _
          (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbTag)
          (by rintro _ ⟨⟩)) fun out ⟨hOutB, hOutRo, hOutRoot⟩ => ?_
        refine ret_leavesL ?_
        dsimp only [MkPreLeafOk, mkcMk, ahsfMkSlots, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
        exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le, hcLen1⟩,
          hOutRo, hOutRoot⟩
      · refine bindV_leavesL_const fun _ => ?_
        refine letV_leavesL fun _ => ?_
        refine bindV_leavesL_const fun pt? => ?_
        refine letV_leavesL_eq fun res? hres? => ?_
        refine bindV_leavesL (recvFinishTagRunC_leaves S K_on (n := n) (ro0 := ro0) (root0 := root0) _ _ _
          (by dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]; exact hbTag)
          ?_) fun out ⟨hOutB, hOutRo, hOutRoot⟩ => ?_
        · intro r hr
          dsimp only [v, Expr.eval, Ext.refl_wk] at hr
          simp only [env_get_zero] at hr
          rw [hr] at hres?
          cases pt? with
          | none =>
            dsimp only [eCaseOpt, v, Expr.eval, Ext.refl_wk] at hres?
            simp only [env_get_zero] at hres?
            cases hres?
          | some pt =>
            dsimp only [eCaseOpt, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hres?
            simp only [env_get_succ, env_get_zero] at hres?
            injection hres? with hEq
            subst hEq
            exact ⟨hRoC', hRootC'⟩
        · refine ret_leavesL ?_
          dsimp only [MkPreLeafOk, mkcMk, ahsfMkSlots, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
          exact ⟨⟨hOutB.base_le, hOutB.initKemRecs_le, hOutB.recvKemRecs_le, hOutB.idealSessions_le, hcLen1⟩,
            hOutRo, hOutRoot⟩

/-! ## Outer `ForgetSim` Simulation Assembly -/

private theorem fixedRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (ρ : Env Γ) :
    (fixedRoCacheE fhstE).eval ρ = atomRoCache (fhstE.eval ρ).1.1 := by
  dsimp only [fixedRoCacheE, liftExpr1, Expr.eval]
  rw [exprRename_eval _ _ (.cons (fhstE.eval ρ) .nil) _ (fun | .zero => rfl | .succ v' => nomatch v')]
  rfl

private theorem fixedRootRoCacheE_eval {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (ρ : Env Γ) :
    (fixedRootRoCacheE fhstE).eval ρ = atomRootRoCache (fhstE.eval ρ).1.1 := by
  dsimp only [fixedRootRoCacheE, liftExpr1, Expr.eval]
  rw [exprRename_eval _ _ (.cons (fhstE.eval ρ) .nil) _ (fun | .zero => rfl | .succ v' => nomatch v')]
  rfl

private theorem bind_const_congr {m : Type → Type} [Bind m] {α β : Type}
    {x₁ x₂ : m α} {k : α → m β} (h : x₁ = x₂) : (x₁ >>= k) = (x₂ >>= k) :=
  congrArg (· >>= k) h

private theorem eval_ren2_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} {Δ : List PT} {vA : Var Δ A} {vB : Var Δ B}
    (c0 : Comp pqxdhOps I [A, B] R) {c : Comp pqxdhOps I Δ R} {env : Env Δ}
    {xA : A.denote} {xB : B.denote}
    (hEq : compRename (ren2 vA vB) c0 = c)
    (hA : env.get vA = xA) (hB : env.get vB = xB) :
    c.eval env = c0.eval (.cons xA (.cons xB .nil)) := by
  subst hA; subst hB; exact eval_ren2 vA vB c0 c env hEq

private theorem mapComp_eval1 {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂) (hZero : ∀ g, tl.unsupportedW g = 0)
    {a out : Ty pqSig} (c : Comp pqxdhOps I₁ [a] out) (x : (embedTy a).denote) :
    (mapComp tl c).eval (.cons x .nil) =
      embedVal out <$> c.eval (.cons (projVal a x) .nil) := by
  conv_lhs => rw [← embedVal_projVal a x]
  exact mapComp_eval tl c (comp_queries_zero_of_zero hZero c) (.cons (projVal a x) .nil)

private theorem mapComp_eval2 {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂) (hZero : ∀ g, tl.unsupportedW g = 0)
    {a b out : Ty pqSig} (c : Comp pqxdhOps I₁ [a, b] out)
    (x : (embedTy a).denote) (y : (embedTy b).denote) :
    (mapComp tl c).eval (.cons x (.cons y .nil)) =
      embedVal out <$> c.eval (.cons (projVal a x) (.cons (projVal b y) .nil)) := by
  conv_lhs => rw [← embedVal_projVal a x, ← embedVal_projVal b y]
  exact mapComp_eval tl c (comp_queries_zero_of_zero hZero c)
    (.cons (projVal a x) (.cons (projVal b y) .nil))

private theorem liftDropShadow1_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T} (tl : TagLift I A)
    (hZero : ∀ g, tl.unsupportedW g = 0) {a b r : Ty pqSig}
    (c : Comp pqxdhOps I [a, b] r)
    (sVal : (Ty.prod (embedTy a) roBothAvlTy).denote) (bVal : (embedTy b).denote) :
    (Comp.bind (.ret (.fst .v0)) (compRename dropShadow1 (mapComp tl c))).eval
        (.cons sVal (.cons bVal .nil)) =
      embedVal r <$> c.eval (.cons (projVal a sVal.1) (.cons (projVal b bVal) .nil)) := by
  dsimp only [Comp.eval, Expr.eval, Expr.v0, Env.get]
  rw [pure_bind, compRename_eval (mapComp tl c) dropShadow1
    (.cons sVal.1 (.cons bVal .nil)) _
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)]
  exact mapComp_eval2 tl hZero c sVal.1 bVal

private theorem prfMsgKeys1KeyKindProg_init_sim (S : Setup) (b : QueryBudget) (x : Unit) :
    Prod.map id forgetMk <$> (prfMsgKeys1KeyKindProg S b).init.eval (.cons x .nil) =
      (prfMkOldAtomicProg S b).init.eval (.cons x .nil) ∧
    ∀ p ∈ support ((prfMsgKeys1KeyKindProg S b).init.eval (.cons x .nil)),
      AuthMkInv S b 0 p.2 := by
  refine ⟨?_, ?_⟩
  · change Prod.map id forgetMk <$> (prfMkKindInitC S b).eval (.cons x .nil) =
      (mapComp tlPrfMk (prfMsgKeysInitDslK S b.q_total)).eval (.cons x .nil)
    dsimp only [prfMkKindInitC, Comp.eval, Expr.eval, Expr.v0, forgetMk, Prod.map, id]
    simp only [Env.get, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    exact bind_pure _
  · change ∀ p ∈ support ((prfMkKindInitC S b).eval (.cons x .nil)), AuthMkInv S b 0 p.2
    dsimp only [prfMkKindInitC, Comp.eval]
    intro p hp
    erw [mem_support_bind_iff] at hp
    rcases hp with ⟨y, hy, hp⟩
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    change y ∈ support ((mapComp tlPrfMk (prfMsgKeysInitDslK S b.q_total)).eval (.cons x .nil)) at hy
    rw [mapComp_eval1 tlPrfMk (fun _ => rfl) (prfMsgKeysInitDslK S b.q_total) x, support_map, Set.mem_image] at hy
    rcases hy with ⟨z, hz, hzy⟩
    dsimp only [prfMsgKeysInitDslK, bindV, Comp.eval] at hz
    erw [mem_support_bind_iff] at hz
    rcases hz with ⟨idx, _, hz⟩
    erw [mem_support_bind_iff] at hz
    rcases hz with ⟨secb, _, hz⟩
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [Expr.eval, Expr.v0, Env.get]
    set empFixed := (emptyAuthHybridStFixedE (.var .zero)).eval
      (.cons secb (.cons idx (.cons (projVal .unit x) .nil)))
    have hyFhst : y.2.2.2.2.2 = embedVal authHybridStateFixedTy empFixed := by
      rw [← hzy]; rfl
    have hRo : atomRoCache (embedVal authHybridStateFixedTy empFixed).1.1 = [] := by
      change atomRoCache (embedVal authStateTy empFixed.1.1) = []
      rw [atomRoCache_embedVal]; rfl
    have hRoot : atomRootRoCache (embedVal authHybridStateFixedTy empFixed).1.1 = [] := by
      change atomRootRoCache (embedVal authStateTy empFixed.1.1) = []
      rw [atomRootRoCache_embedVal]; rfl
    have hBnd : AuthFixedAtomOnlineBounded 0 (embedVal authHybridStateFixedTy empFixed) := by
      rw [AuthFixedAtomOnlineBounded.iff_embedVal]
      exact ⟨⟨Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0,
        Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0,
        Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0⟩,
        Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0, Nat.zero_le 0⟩
    let xA : (Ty.unit : Ty pqAtomicSig).denote := x
    have hAvl : RoBothShadowRel (AuthKindFuels.ofBudget S b).K_cap
        (embedVal authHybridStateFixedTy empFixed).1.1
        (emptyRoBothAvlE.eval (.cons y (.cons xA .nil))) :=
      emptyRoBothAvlE_roBothShadowRel (AuthKindFuels.ofBudget S b).K_cap _
        (.cons y (.cons xA .nil)) hRo hRoot
    refine ⟨AuthCounterInv.zero b, ?_⟩
    dsimp only [mkShadowFixed]; rw [hyFhst]
    exact ⟨hBnd, by rw [hRo]; exact Nat.zero_le _, by rw [hRoot]; exact Nat.zero_le _, hAvl⟩

private theorem prfMsgKeys1KeyKindProg_finish_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (bOut : Bool)
    (hInv : AuthMkInv S b c s') :
    (prfMsgKeys1KeyKindProg S b).finish.eval (.cons s' (.cons bOut .nil)) =
      (prfMkOldAtomicProg S b).finish.eval (.cons (forgetMk s') (.cons bOut .nil)) := by
  let F := AuthKindFuels.ofBudget S b
  refine (liftDropShadow1_eval tlPrfMk (fun _ => rfl) (prfMsgKeysFinishDsl S F.K_on) s' bOut).trans ?_
  refine (congrArg (embedVal .bool <$> ·) ?_).trans
    (mapComp_eval2 tlPrfMk (fun _ => rfl) (prfMsgKeysFinishDsl S b.q_total) s'.1 bOut).symm
  dsimp only [prfMsgKeysFinishDsl]
  refine liftPrimComp_eval_congr _ _ _ ?_
  dsimp only [letV]
  rw [eval_letC, eval_letC, eval_letC, eval_letC]
  dsimp only [v, mkcSecb, mkcFhst, ahsfHybrid, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, projVal]
  set fhst0 := projVal authHybridStateFixedTy s'.1.2.2.2.2
  have hFhst0Emb : embedVal authHybridStateFixedTy fhst0 = s'.1.2.2.2.2 :=
    embedVal_projVal authHybridStateFixedTy s'.1.2.2.2.2
  have hb0 : AuthFixedValOnlineBounded (c 0) fhst0 := by
    rw [← AuthFixedAtomOnlineBounded.iff_embedVal, hFhst0Emb]
    exact hInv.shadow_ok.online_le
  exact finalizeAuthFixedKDsl_fuel_eq S b fhst0.1 bOut s'.1.2.1 _
    hb0.base_le hb0.initKemRecs_le hb0.recvKemRecs_le hb0.idealSessions_le
    (by have := hInv.counter_inv.on_le; dsimp only [AuthKindFuels.ofBudget]; omega)

private theorem oldHandle_eval (S : Setup) (b : QueryBudget)
    (s' : authMkShadowStTy.denote) (t : AuthQuery S) :
    (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal (.prod authRespTy prfMkStTy) <$>
        (prfMsgKeysHandle1KeyDsl S b.q_total).eval
          (.cons (projVal prfMkStTy s'.1)
            ((.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil) : Env [authQueryTy])) := by
  change (liftAuthHandle tlPrfMk S (prfMsgKeysHandle1KeyDsl S b.q_total)).eval
    (.cons s'.1 (.cons ((authCodec S).qenc t) .nil)) = _
  conv_lhs => rw [← embedVal_projVal prfMkStTy s'.1]
  exact liftAuthHandle_eval tlPrfMk S (fun _ => rfl) (prfMsgKeysHandle1KeyDsl S b.q_total)
    (projVal prfMkStTy s'.1) t

private abbrev mkPreEnv (S : Setup) (s0 : prfMkStTy.denote) (t : AuthQuery S) :
    Env [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] :=
  .cons s0.2 (.cons s0.1 (.cons s0 (.cons s0
    ((.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil) : Env [authQueryTy]))))

private theorem mkOther_rhs_eq (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (s' : authMkShadowStTy.denote) (t : AuthQuery S) (xAtom : (embedTy arg).denote)
    (m : Comp pqxdhOps pqPrimIface [authHybridStateFixedTy, arg] RSF)
    (hPre : (prfMkStepPre1KeyC S b.q_total
        (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy)
        (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)).eval
        (mkPreEnv S (projVal prfMkStTy s'.1) t) =
      (m.eval (.cons (projVal authHybridStateFixedTy s'.1.2.2.2.2) (.cons (projVal arg xAtom) .nil)) >>=
        fun r => pure (Sum.inl (r.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, r.2))))))) :
    (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) =
      ((mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle) m)).eval
        (.cons s'.1.2.2.2.2 (.cons xAtom .nil)) >>=
        fun rsf => pure (rsf.1, (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, rsf.2)))))) := by
  rw [oldHandle_eval, mapComp_eval2 tlPrfMk (fun _ => rfl) (liftPrimComp (C := msgKeyPrfOracle) m) s'.1.2.2.2.2 xAtom]
  dsimp only [prfMsgKeysHandle1KeyDsl, letV]
  rw [eval_letC, eval_letC, eval_letC]
  dsimp only [bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, eval_liftPrimComp]
  rw [hPre, embedPrim_bind, bind_assoc, map_bind, bind_map_left]
  refine congrArg (_ >>= ·) (funext fun r => ?_)
  rw [embedPrim_pure, pure_bind]
  dsimp only [caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, projVal, map_pure]
  rcases r with ⟨resp, fhst1⟩; rfl

private theorem mkBaseArm_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (stepK stepOld : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RSF)
    (hRenK : ∀ {Γ₁ Γ₂ Δ : List PT} [i₁ : Ext Γ₁ Δ] [i₂ : Ext Γ₂ Δ]
      (vF : Var Γ₁ authHybridStateFixedTy) (vX : Var Γ₂ arg),
      compRename (ren2 (i₁.wk vF) (i₂.wk vX))
        (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero) = stepK vF vX)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (t : AuthQuery S) (xAtom : (embedTy arg).denote)
    (hOn : authSimPred S 0 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s')
    (hSim :
      (mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle)
          (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons (mkShadowFixed s').1 (.cons xAtom .nil)) =
      (mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle)
          (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons (mkShadowFixed s').1 (.cons xAtom .nil)) ∧
      ∀ rsf ∈ support ((mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle)
          (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons (mkShadowFixed s').1 (.cons xAtom .nil))),
        AuthFixedShadowAt S b (c 0 + 1) (c 0 + c 1) (c 0 + c 2) (rsf.2, (mkShadowFixed s').2))
    (hPre : (prfMkStepPre1KeyC S b.q_total
        (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy)
        (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)).eval
        (mkPreEnv S (projVal prfMkStTy s'.1) t) =
      ((stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero).eval
        (.cons (projVal authHybridStateFixedTy s'.1.2.2.2.2) (.cons (projVal arg xAtom) .nil)) >>=
        fun r => pure (Sum.inl (r.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, r.2))))))) :
    let ρ := Env.cons xAtom (.cons s' (.cons ((authCodec S).qenc t) .nil))
    Prod.map id forgetMk <$> (mkBaseArmC S stepK).eval ρ =
      (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((mkBaseArmC S stepK).eval ρ),
      AuthMkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro ρ
  have hLhsLift :
      (liftPrfMk1
        (liftPrimComp (C := msgKeyPrfOracle)
          (letV (.fst (.var .zero)) fun fhst =>
           letV (.snd (.var (.succ .zero))) fun x =>
           stepK fhst x))
        (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) .v0)).eval ρ =
      (mapComp tlPrfMk (liftPrimComp (C := msgKeyPrfOracle)
        (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons s'.1.2.2.2.2 (.cons xAtom .nil)) := by
    rw [lift1_eval, mapComp_eval2 tlPrfMk (fun _ => rfl)]
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, projVal, ρ, eval_liftPrimComp]
    congr 2; dsimp only [letV]; rw [eval_letC, eval_letC]
    simp only [Expr.eval, env_get_zero, env_get_succ]
    exact eval_ren2_eq (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
      (Δ := [authHybridStateFixedTy, arg]) .zero .zero) (hRenK _ _) rfl rfl
  refine ⟨?_, ?_⟩
  · rw [mkOther_rhs_eq S b s' t xAtom _ hPre]
    dsimp only [mkShadowFixed] at hSim
    simp only [mkBaseArmC, mkRebuildE, forgetMk, Comp.eval, Expr.eval, Expr.v0, Expr.v2,
      Env.get, ρ, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, id]
    erw [hLhsLift, hSim.1]; rfl
  · dsimp only [mkBaseArmC, Comp.eval]; intro p hp
    erw [hLhsLift, mem_support_bind_iff] at hp; rcases hp with ⟨rsf, hrsf, hp⟩
    simp only [mkRebuildE, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hSh := hSim.2 rsf hrsf
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, hOn]
    have hGe1 : c 1 ≤ bumpPred (authSimPred S) c t 1 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe2 : c 2 ≤ bumpPred (authSimPred S) c t 2 := by dsimp only [bumpPred]; split_ifs <;> omega
    exact ⟨hBump, hSh.mono (by omega) (by omega) (by omega)⟩

private theorem roArm_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (sec : (PB 192).denote)
    (hroom : ∀ j : Fin 4, authSimPred S j (.roQuery sec) → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let t := AuthQuery.roQuery (S := S) sec
    let ρ := Env.cons sec (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm := Comp.bind
      (roFixedShadowArmC aiPrfMk F.K_cap (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (mkRebuildE (.fst .v2) (.snd .v0))))
    Prod.map id forgetMk <$> arm.eval ρ =
      (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthMkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F t ρ arm
  have hRoPred : authSimPred S 1 t := trivial
  have ⟨_, hOld, hKR⟩ := AuthCounterInv.ro_step_bounds hInv.counter_inv hRoPred hroom
  have hSim := roFixedShadowArmC_sim_mk S b
    (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0 ρ (mkShadowFixed s') sec
    rfl rfl hInv.shadow_ok (by omega) (by omega)
  have hPre : (prfMkStepPre1KeyC S b.q_total
        (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy)
        (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)).eval
        (mkPreEnv S (projVal prfMkStTy s'.1) t) =
      ((roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
          (Δ := [authHybridStateFixedTy, B 192]) .zero .zero).eval
        (.cons (projVal authHybridStateFixedTy s'.1.2.2.2.2) (.cons (projVal (B 192) sec) .nil)) >>=
        fun r => pure (Sum.inl (r.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, r.2)))))) := by
    simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
      letV, eval_letC, caseSumV, bindV, v,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_zero, env_get_succ, projVal, t]
    exact bind_const_congr (eval_ren2_eq
      (roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
        (Δ := [authHybridStateFixedTy, B 192]) .zero .zero) rfl rfl rfl)
  refine ⟨?_, ?_⟩
  · dsimp only [mkShadowFixed] at hSim
    refine (?_ : _ = ((Prod.map id forgetAuthFixedShadow <$>
        (roFixedShadowArmC aiPrfMk F.K_cap
          (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0).eval ρ) >>=
        fun rsf => pure (rsf.1, (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, rsf.2))))))).trans
      ((bind_const_congr hSim.1).trans (mkOther_rhs_eq S b (arg := B 192) s' t sec _ hPre).symm)
    dsimp only [arm, Comp.eval]
    rw [map_bind, bind_map_left]
    refine congrArg (_ >>= ·) (funext fun x => ?_)
    rw [map_pure]; rfl
  · dsimp only [arm, Comp.eval]; intro p hp
    erw [mem_support_bind_iff] at hp; rcases hp with ⟨q0, hq0, hp⟩
    simp only [mkRebuildE, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hSh := hSim.2 q0 hq0
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthOnlineQuery, t]
    have hB1 : bumpPred (authSimPred S) c t 1 = c 1 + 1 := by simp [bumpPred, hRoPred]
    have hB2 : bumpPred (authSimPred S) c t 2 = c 2 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthRoRootQuery, t]
    exact ⟨hBump, hSh.mono (by omega) (by omega) (by omega)⟩

private theorem roRootArm_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (rk dh : (PB 32).denote)
    (hroom : ∀ j : Fin 4, authSimPred S j (.roRootQuery rk dh) → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let t := AuthQuery.roRootQuery (S := S) rk dh
    let ρ := Env.cons (rk, dh) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm := Comp.bind
      (roRootFixedShadowArmC aiPrfMk F.K_cap (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (mkRebuildE (.fst .v2) (.snd .v0))))
    Prod.map id forgetMk <$> arm.eval ρ =
      (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthMkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F t ρ arm
  have hRtPred : authSimPred S 2 t := trivial
  have ⟨_, hOld, hKR⟩ := AuthCounterInv.roRoot_step_bounds hInv.counter_inv hRtPred hroom
  have hSim := roRootFixedShadowArmC_sim_mk S b
    (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0 ρ (mkShadowFixed s') (rk, dh)
    rfl rfl hInv.shadow_ok (by omega) (by omega)
  have hPre : (prfMkStepPre1KeyC S b.q_total
        (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy)
        (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)).eval
        (mkPreEnv S (projVal prfMkStTy s'.1) t) =
      ((roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
          (Γ₂ := [.prod (B 32) (B 32)]) (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)]) .zero .zero).eval
        (.cons (projVal authHybridStateFixedTy s'.1.2.2.2.2)
          (.cons (projVal (.prod (B 32) (B 32)) (rk, dh)) .nil)) >>=
        fun r => pure (Sum.inl (r.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, r.2)))))) := by
    simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
      letV, eval_letC, caseSumV, bindV, v,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_zero, env_get_succ, projVal, t]
    exact bind_const_congr (eval_ren2_eq
      (roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
        (Γ₂ := [.prod (B 32) (B 32)]) (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)]) .zero .zero)
      rfl rfl rfl)
  refine ⟨?_, ?_⟩
  · dsimp only [mkShadowFixed] at hSim
    refine (?_ : _ = ((Prod.map id forgetAuthFixedShadow <$>
        (roRootFixedShadowArmC aiPrfMk F.K_cap
          (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0).eval ρ) >>=
        fun rsf => pure (rsf.1, (s'.1.1, (s'.1.2.1, (s'.1.2.2.1, (s'.1.2.2.2.1, rsf.2))))))).trans
      ((bind_const_congr hSim.1).trans
        (mkOther_rhs_eq S b (arg := .prod (B 32) (B 32)) s' t (rk, dh) _ hPre).symm)
    dsimp only [arm, Comp.eval]
    rw [map_bind, bind_map_left]
    refine congrArg (_ >>= ·) (funext fun x => ?_)
    rw [map_pure]; rfl
  · dsimp only [arm, Comp.eval]; intro p hp
    erw [mem_support_bind_iff] at hp; rcases hp with ⟨q0, hq0, hp⟩
    simp only [mkRebuildE, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hSh := hSim.2 q0 hq0
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthOnlineQuery, t]
    have hB1 : bumpPred (authSimPred S) c t 1 = c 1 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthRoQuery, t]
    have hB2 : bumpPred (authSimPred S) c t 2 = c 2 + 1 := by simp [bumpPred, hRtPred]
    exact ⟨hBump, hSh.mono (by omega) (by omega) (by omega)⟩

private theorem revealDh_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote)
    (hroom : ∀ j : Fin 4, authSimPred S j .revealDhSecrets → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s') :
    let t := AuthQuery.revealDhSecrets (S := S)
    let ρ := Env.cons (() : (Ty.unit : Ty pqAtomicSig).denote) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm : Comp pqAtomicOps pqPrfMkIface
        [.unit, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy)) :=
      .ret (.pair aNoneAtomicE .v1)
    Prod.map id forgetMk <$> arm.eval ρ =
      (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthMkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro t ρ arm
  refine ⟨?_, ?_⟩
  · rw [oldHandle_eval]
    have hRhs : ∀ (s0 : prfMkStTy.denote),
        (prfMsgKeysHandle1KeyDsl S b.q_total).eval
          (.cons s0 ((.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil) : Env [authQueryTy])) =
        pure (Sum.inl (), s0) := by
      intro s0
      simp only [prfMsgKeysHandle1KeyDsl, prfMkStepPre1KeyC, bindV, letV, eval_letC, caseSumV, v,
        _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
        aNone, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_zero, env_get_succ, eval_liftPrimComp, embedPrim_pure, t]
      rcases s0 with ⟨bud0, core0⟩
      exact pure_bind _ _
    rw [hRhs (projVal prfMkStTy s'.1)]
    simp only [arm, aNoneAtomicE, forgetMk, Comp.eval, Expr.eval, Expr.v1, Env.get, ρ, map_pure, Prod.map, id]
    exact congrArg pure (Prod.ext rfl (embedVal_projVal prfMkStTy s'.1).symm)
  · simp only [arm, Comp.eval, Expr.eval, Expr.v1, Env.get, ρ]
    intro p hp; rw [support_pure, Set.mem_singleton_iff] at hp; subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hGe0 : c 0 ≤ bumpPred (authSimPred S) c t 0 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe1 : c 1 ≤ bumpPred (authSimPred S) c t 1 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe2 : c 2 ≤ bumpPred (authSimPred S) c t 2 := by dsimp only [bumpPred]; split_ifs <;> omega
    exact ⟨hBump, hInv.shadow_ok.mono hGe0 (by omega) (by omega)⟩

private theorem liftPrimComp_eval_congr₂ {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    {Δ₁ Δ₂ : List PT} {out : PT} (c₁ : Comp pqxdhOps pqPrimIface Δ₁ out) (env₁ : Env Δ₁)
    (c₂ : Comp pqxdhOps pqPrimIface Δ₂ out) (env₂ : Env Δ₂)
    (h : c₁.eval env₁ = c₂.eval env₂) :
    (liftPrimComp (C := C) c₁).eval env₁ = (liftPrimComp (C := C) c₂).eval env₂ := by
  rw [eval_liftPrimComp, eval_liftPrimComp, h]

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 400000 in
private theorem mkOnlineArm_sim (S : Setup) (b : QueryBudget) {arg : PT}
    (preStepK : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ prfMkCoreTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (t : AuthQuery S)
    (s0 : prfMkStTy.denote) (hs0 : projVal prfMkStTy s'.1 = s0)
    {xAtom : (embedTy arg).denote}
    (hOn : authSimPred S 0 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s')
    (hPreEq :
      let x0 := projVal arg xAtom
      (preStepK (Γ₁ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
        (Γ₂ := [arg, prfMkStTy, .prod prfMkStTy arg])
        (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg]) .zero .zero).eval
        (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil))))) =
      (prfMkStepPre1KeyC S b.q_total
        (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy)
        (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)).eval
        (mkPreEnv S s0 t))
    (hPreLeaves :
      let x0 := projVal arg xAtom
      AllLeaves (MkPreLeafOk (c 0) (valRoCache s0.2.2.2.2.1.1) (valRootRoCache s0.2.2.2.2.1.1))
        ((preStepK (Γ₁ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
          (Γ₂ := [arg, prfMkStTy, .prod prfMkStTy arg])
          (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg]) .zero .zero).eval
          (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil))))))) :
    let F := AuthKindFuels.ofBudget S b
    let ρ := Env.cons xAtom (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm : Comp pqAtomicOps pqPrfMkIface
        [embedTy arg, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy)) :=
      .bind (liftPrfMk1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun _bud =>
           letV (.snd (v s)) fun core =>
           bindV (liftPrimComp (preStepK core x)) fun _pre =>
           mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
            (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
    Prod.map id forgetMk <$> arm.eval ρ =
      (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthMkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F ρ arm
  have ⟨hnOn, hRoStepB, hRootStepB, hKroCap⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
  have hKonQ : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  set x0 := projVal arg xAtom
  have hFhst0 : s0.2.2.2.2 = projVal authHybridStateFixedTy s'.1.2.2.2.2 := by
    rw [← hs0]; rfl
  have hFhst0Emb : embedVal authHybridStateFixedTy s0.2.2.2.2 = s'.1.2.2.2.2 := by
    rw [hFhst0]; exact embedVal_projVal authHybridStateFixedTy s'.1.2.2.2.2
  have hb0 : AuthFixedValOnlineBounded (c 0) s0.2.2.2.2 := by
    rw [← AuthFixedAtomOnlineBounded.iff_embedVal, hFhst0Emb]; exact hInv.shadow_ok.online_le
  let innerK : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface
      [.prod prfMkStTy arg] (.prod authRespTy prfMkStTy) :=
    letV (.fst (.var .zero)) fun s =>
    letV (.snd (.var (.succ .zero))) fun x =>
    letV (.fst (v s)) fun _bud =>
    letV (.snd (v s)) fun core =>
    bindV (liftPrimComp (preStepK core x)) fun _pre =>
    mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero
  have hInnerEq :
      innerK.eval (.cons (s0, x0) .nil) =
        (prfMsgKeysHandle1KeyDsl S b.q_total).eval
          (.cons s0 ((.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil) : Env [authQueryTy])) ∧
      ∀ z ∈ support (innerK.eval (.cons (s0, x0) .nil)),
        AuthFixedValOnlineBounded (c 0 + 1) z.2.2.2.2.2 ∧
        CacheStepAtMostOne (valRoCache s0.2.2.2.2.1.1) (valRoCache z.2.2.2.2.2.1.1) ∧
        CacheStepAtMostOne (valRootRoCache s0.2.2.2.2.1.1) (valRootRoCache z.2.2.2.2.2.1.1) := by
    dsimp only [innerK, prfMsgKeysHandle1KeyDsl, letV]
    iterate 7 rw [eval_letC]
    dsimp only [bindV, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]
    have hPreSupp : ∀ pre ∈ support ((liftPrimComp
          (C := _root_.SignalPqxdh.LegacyCosted.msgKeyPrfOracle) (preStepK
          (Γ₁ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
          (Γ₂ := [arg, prfMkStTy, .prod prfMkStTy arg])
          (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg]) .zero .zero)).eval
          (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))),
        MkPreLeafOk (c 0) (valRoCache s0.2.2.2.2.1.1) (valRootRoCache s0.2.2.2.2.1.1) pre := by
      intro pre hpre
      obtain ⟨pre0, hpre0, rfl⟩ := mem_support_liftPrimComp _ _ pre hpre
      exact AllLeaves_mem_support hPreLeaves hpre0
    refine ⟨?_, ?_⟩
    · have hPreLift :
          (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.msgKeyPrfOracle)
            (preStepK (Γ₁ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
              (Γ₂ := [arg, prfMkStTy, .prod prfMkStTy arg])
              (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg]) .zero .zero)).eval
            (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil))))) =
          (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.msgKeyPrfOracle)
            (prfMkStepPre1KeyC S b.q_total
              (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy)
              (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy))).eval
            (mkPreEnv S s0 t) := by
        rw [eval_liftPrimComp, eval_liftPrimComp, hPreEq]
      conv_rhs => rw [← hPreLift]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun pre hpre => ?_
      have hInvPre := hPreSupp pre hpre
      cases pre with
      | inl d =>
        dsimp only [mkPostRunC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero]
      | inr req =>
        dsimp only [mkPostRunC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [natEq_eval, Expr.eval, env_get_succ, env_get_zero]
        by_cases hBud : (s0.1 == 0) = true
        · simp only [hBud, ↓reduceIte, Expr.eval, aNone]
        · simp only [Bool.eq_false_iff.mpr hBud, Bool.false_eq_true, ↓reduceIte,
            letV, eval_letC, bindV, queryDeriveMk, Comp.eval, Expr.eval,
            env_get_succ, env_get_zero]
          refine congrArg (_ >>= ·) (funext fun mk => bind_const_congr ?_)
          apply liftPrimComp_eval_congr₂
          apply prfMkStepPostC_eval_eq S
          · rfl
          · rfl
          · exact hInvPre
          · exact Nat.le_of_succ_le hnOn
          · exact Nat.le_trans (Nat.le_of_succ_le hnOn) hKonQ
    · intro z hz
      erw [mem_support_bind_iff] at hz; rcases hz with ⟨pre, hpre, hz⟩
      have hInvPre := hPreSupp pre hpre
      cases pre with
      | inl d =>
        dsimp only [mkPostRunC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk] at hz
        simp only [env_get_succ, env_get_zero, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hInvPre
      | inr req =>
        dsimp only [mkPostRunC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk] at hz
        simp only [natEq_eval, Expr.eval, env_get_succ, env_get_zero] at hz
        by_cases hBud : (s0.1 == 0) = true
        · simp only [hBud, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hb0.mono (Nat.le_succ (c 0)), CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
        · simp only [Bool.eq_false_iff.mpr hBud, Bool.false_eq_true, ↓reduceIte,
            letV, eval_letC, bindV, queryDeriveMk, Comp.eval, Expr.eval,
            env_get_succ, env_get_zero] at hz
          erw [mem_support_bind_iff] at hz; rcases hz with ⟨mk, _, hz⟩
          erw [mem_support_bind_iff] at hz; rcases hz with ⟨post, hpost, hz⟩
          simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
          obtain ⟨post0, hpost0, rfl⟩ := mem_support_liftPrimComp _ _ post hpost
          have hPostOk : AuthFixedValOnlineBounded (c 0 + 1) post0.2.2.2.2 ∧
              CacheStepAtMostOne (valRoCache s0.2.2.2.2.1.1) (valRoCache post0.2.2.2.2.1.1) ∧
              CacheStepAtMostOne (valRootRoCache s0.2.2.2.2.1.1) (valRootRoCache post0.2.2.2.2.1.1) := by
            refine AllLeaves_mem_support (P := fun p =>
              AuthFixedValOnlineBounded (c 0 + 1) p.2.2.2.2 ∧
              CacheStepAtMostOne (valRoCache s0.2.2.2.2.1.1) (valRoCache p.2.2.2.2.1.1) ∧
              CacheStepAtMostOne (valRootRoCache s0.2.2.2.2.1.1) (valRootRoCache p.2.2.2.2.1.1)) ?_ hpost0
            apply prfMkStepPostC_leaves S F.K_on
            exact hInvPre
          exact hPostOk
  have hEnv0 : Env.cons (projVal (.prod prfMkStTy arg) (s'.1, xAtom)) .nil = Env.cons (s0, x0) .nil :=
    congrArg (Env.cons · .nil) (Prod.ext hs0 rfl)
  have hLiftEval :
      (liftPrfMk1 innerK (.pair (.fst .v1) .v0)).eval ρ =
        embedVal (.prod authRespTy prfMkStTy) <$> innerK.eval (.cons (s0, x0) .nil) := by
    refine (lift1_eval innerK (.pair (.fst .v1) .v0) ρ).trans ?_
    change embedVal (.prod authRespTy prfMkStTy) <$>
        innerK.eval (.cons (projVal (.prod prfMkStTy arg) (s'.1, xAtom)) .nil) = _
    rw [hEnv0]
  have hSyncEach :
      ∀ y ∈ support ((liftPrfMk1 innerK (.pair (.fst .v1) .v0)).eval ρ),
        ∃ avls' : roBothAvlTy.denote,
          (syncRoBothC (I := pqPrfMkIface) F.K_cap
              (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
              (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
              (.snd .v2)).eval (.cons y ρ) = pure avls' ∧
          AuthFixedShadowAt S b (c 0 + 1) (c 0 + 1 + c 1) (c 0 + 1 + c 2)
            (mkShadowFixed (y.2, avls')) := by
    intro y hy
    have hEqMap : (liftPrfMk1 innerK (.pair (.fst .v1) .v0)).eval ρ =
        (mapComp tlPrfMk innerK).eval (.cons (s'.1, xAtom) .nil) := by
      dsimp only [liftPrfMk1, Comp.eval]
      exact (pure_bind _ _).trans (compRename_eval (mapComp tlPrfMk innerK) dropShadow0
        (.cons (s'.1, xAtom) .nil) _ (fun | .zero => rfl | .succ v => nomatch v))
    have hy' : y ∈ support ((mapComp tlPrfMk innerK).eval (.cons (s'.1, xAtom) .nil)) :=
      hEqMap ▸ hy
    obtain ⟨z, hz0, rfl⟩ :=
      mem_support_mapComp_of_zero tlPrfMk (fun _ => rfl) innerK (.cons (s'.1, xAtom) .nil) hy'
    have hz0' : z ∈ support (innerK.eval (.cons (projVal (.prod prfMkStTy arg) (s'.1, xAtom)) .nil)) := hz0
    have hz : z ∈ support (innerK.eval (.cons (s0, x0) .nil)) := (congrArg innerK.eval hEnv0) ▸ hz0'
    obtain ⟨hFixed1, hRoS, hRootS⟩ := hInnerEq.2 z hz
    have hPreSt : s'.1.2.2.2.2.1.1 = embedVal authStateTy s0.2.2.2.2.1.1 := by
      rw [← hFhst0Emb]; rfl
    have hPostSt : (embedVal (.prod authRespTy prfMkStTy) z).2.2.2.2.2.1.1 =
        embedVal authStateTy z.2.2.2.2.2.1.1 := rfl
    have hRoS' : CacheStepAtMostOne (atomRoCache s'.1.2.2.2.2.1.1)
        (atomRoCache (embedVal (.prod authRespTy prfMkStTy) z).2.2.2.2.2.1.1) := by
      rw [hPreSt, hPostSt, atomRoCache_embedVal, atomRoCache_embedVal]; exact hRoS
    have hRootS' : CacheStepAtMostOne (atomRootRoCache s'.1.2.2.2.2.1.1)
        (atomRootRoCache (embedVal (.prod authRespTy prfMkStTy) z).2.2.2.2.2.1.1) := by
      rw [hPreSt, hPostSt, atomRootRoCache_embedVal, atomRootRoCache_embedVal]; exact hRootS
    have hRoLen1 : (atomRoCache (embedVal (.prod authRespTy prfMkStTy) z).2.2.2.2.2.1.1).length ≤
        c 0 + 1 + c 1 := by
      have h0 := hInv.shadow_ok.ro_len_le; dsimp only [mkShadowFixed] at h0
      have h1 := hRoS'.length_le; omega
    have hRootLen1 : (atomRootRoCache (embedVal (.prod authRespTy prfMkStTy) z).2.2.2.2.2.1.1).length ≤
        c 0 + 1 + c 2 := by
      have h0 := hInv.shadow_ok.root_len_le; dsimp only [mkShadowFixed] at h0
      have h1 := hRootS'.length_le; omega
    obtain ⟨avls', hSyncEv, hRel'⟩ :=
      syncRoBothC_sim (I := pqPrfMkIface) F.K_cap
        s'.1.2.2.2.2.1.1 (embedVal (.prod authRespTy prfMkStTy) z).2.2.2.2.2.1.1 s'.2
        (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
        (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
        (.snd .v2)
        (.cons (embedVal (.prod authRespTy prfMkStTy) z) ρ)
        hInv.shadow_ok.ro_shadow hRoS' hRootS'
        (Nat.le_trans hRoLen1 (Nat.le_trans hRoStepB hKroCap))
        (Nat.le_trans hRootLen1 (Nat.le_trans hRootStepB hKroCap))
        (fixedRoCacheE_eval _ _) (fixedRootRoCacheE_eval _ _) rfl
    refine ⟨avls', hSyncEv, ⟨?_, hRoLen1, hRootLen1, hRel'⟩⟩
    change AuthFixedAtomOnlineBounded (c 0 + 1) (embedVal authHybridStateFixedTy z.2.2.2.2.2)
    exact (AuthFixedAtomOnlineBounded.iff_embedVal z.2.2.2.2.2).mpr hFixed1
  have hOld0 :
      embedVal (.prod authRespTy prfMkStTy) <$>
        (prfMsgKeysHandle1KeyDsl S b.q_total).eval
          (.cons s0 ((.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil) : Env [authQueryTy])) =
      (prfMkOldAtomicProg S b).handle.eval (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) := by
    rw [← hs0]; exact (oldHandle_eval S b s' t).symm
  refine ⟨?_, ?_⟩
  · refine (?_ : _ = (liftPrfMk1 innerK (.pair (.fst .v1) .v0)).eval ρ).trans
      ((hLiftEval.trans (congrArg (embedVal (.prod authRespTy prfMkStTy) <$> ·) hInnerEq.1)).trans hOld0)
    dsimp only [arm, Comp.eval]
    rw [map_bind]
    conv_rhs => rw [← bind_pure ((liftPrfMk1 innerK (.pair (.fst .v1) .v0)).eval ρ)]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun y hy => ?_
    obtain ⟨avls', hSyncEv, _⟩ := hSyncEach y hy
    rw [hSyncEv, pure_bind, map_pure]; rfl
  · dsimp only [arm, Comp.eval]; intro p hp
    erw [mem_support_bind_iff] at hp; rcases hp with ⟨y, hy, hp⟩
    obtain ⟨avls', hSyncEv, hSh'⟩ := hSyncEach y hy
    erw [hSyncEv, pure_bind] at hp
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, hOn]
    have hGe1 : c 1 ≤ bumpPred (authSimPred S) c t 1 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe2 : c 2 ≤ bumpPred (authSimPred S) c t 2 := by dsimp only [bumpPred]; split_ifs <;> omega
    exact ⟨hBump, hSh'.mono (by omega) (by omega) (by omega)⟩

private theorem mkOnlineStep_bounds (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (t : AuthQuery S)
    (s0 : prfMkStTy.denote) (hs0 : projVal prfMkStTy s'.1 = s0)
    (hOn : authSimPred S 0 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s') :
    AuthFixedValOnlineBounded (c 0) s0.2.2.2.2 ∧
    c 0 ≤ (AuthKindFuels.ofBudget S b).K_on ∧ c 0 ≤ b.q_total ∧
    (valRoCache s0.2.2.2.2.1.1).length ≤ (AuthKindFuels.ofBudget S b).K_ro ∧
    (valRoCache s0.2.2.2.2.1.1).length ≤ b.q_total ∧
    (valRootRoCache s0.2.2.2.2.1.1).length ≤ (AuthKindFuels.ofBudget S b).K_ro ∧
    (valRootRoCache s0.2.2.2.2.1.1).length ≤ b.q_total := by
  have ⟨hnOn, hRoStepB, hRootStepB, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
  have hKonQ := AuthKindFuels.K_on_le_q_total S b
  have hKroQ := AuthKindFuels.K_ro_le_q_total S b
  have hEmb : embedVal authHybridStateFixedTy s0.2.2.2.2 = s'.1.2.2.2.2 := by
    rw [← hs0]; exact embedVal_projVal authHybridStateFixedTy s'.1.2.2.2.2
  have hb0 : AuthFixedValOnlineBounded (c 0) s0.2.2.2.2 := by
    rw [← AuthFixedAtomOnlineBounded.iff_embedVal, hEmb]; exact hInv.shadow_ok.online_le
  have hSt : embedVal authStateTy s0.2.2.2.2.1.1 = s'.1.2.2.2.2.1.1 := by rw [← hEmb]; rfl
  have hRoL : (valRoCache s0.2.2.2.2.1.1).length ≤ c 0 + c 1 := by
    rw [← atomRoCache_embedVal, hSt]; exact hInv.shadow_ok.ro_len_le
  have hRootL : (valRootRoCache s0.2.2.2.2.1.1).length ≤ c 0 + c 2 := by
    rw [← atomRootRoCache_embedVal, hSt]; exact hInv.shadow_ok.root_len_le
  exact ⟨hb0, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 400000 in
private theorem prfMsgKeys1KeyKindProg_handle_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authMkShadowStTy.denote) (t : AuthQuery S)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthMkInv S b c s') :
    Prod.map id forgetMk <$> (prfMsgKeys1KeyKindProg S b).handle.eval
        (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (prfMkOldAtomicProg S b).handle.eval
        (.cons (forgetMk s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((prfMsgKeys1KeyKindProg S b).handle.eval
        (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      AuthMkInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let F := AuthKindFuels.ofBudget S b
  change Prod.map id forgetMk <$> (prfMkKindHandleC S F).eval
      (.cons s' (.cons ((authCodec S).qenc t) .nil)) = _ ∧
    ∀ p ∈ support ((prfMkKindHandleC S F).eval
      (.cons s' (.cons ((authCodec S).qenc t) .nil))), _
  dsimp only [prfMkKindHandleC]
  erw [dispatchAuthQ_eval_qenc (.var (.succ .zero)) (.cons s' (.cons ((authCodec S).qenc t) .nil)) t rfl]
  cases t with
  | initPrin u =>
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv (t := .initPrin u) trivial hroom
    exact mkBaseArm_sim S b (arg := .nat)
      (fun fhst x => initPrin1KeyFixedKB F fhst x) (fun fhst x => initPrin1KeyFixedB b.q_total fhst x)
      (fun _ _ => rfl) c s' (.initPrin u) u trivial hroom hInv
      (initPrinFixedShadowB_sim tlPrfMk liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (mkShadowFixed s') u hInv.shadow_ok hn)
      (by simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
            letV, eval_letC, caseSumV, bindV, v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_zero, env_get_succ, projVal]
          exact bind_const_congr (eval_ren2_eq (initPrin1KeyFixedB b.q_total
            (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
            (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) rfl rfl rfl))
  | corruptIK u =>
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv (t := .corruptIK u) trivial hroom
    exact mkBaseArm_sim S b (arg := .nat)
      (fun fhst x => corruptFixedKB F fhst x) (fun fhst x => corruptFixedB b.q_total fhst x)
      (fun _ _ => rfl) c s' (.corruptIK u) u trivial hroom hInv
      (corruptFixedShadowB_sim tlPrfMk liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (mkShadowFixed s') u hInv.shadow_ok hn)
      (by simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
            letV, eval_letC, caseSumV, bindV, v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_zero, env_get_succ, projVal]
          exact bind_const_congr (eval_ren2_eq (corruptFixedB b.q_total
            (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
            (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) rfl rfl rfl))
  | genSPK u j =>
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv (t := .genSPK u j) trivial hroom
    exact mkBaseArm_sim S b (arg := .prod .nat .nat)
      (fun fhst x => genSpkFixedKB F fhst x) (fun fhst x => genSpkFixedB b.q_total fhst x)
      (fun _ _ => rfl) c s' (.genSPK u j) (u, j) trivial hroom hInv
      (genSpkFixedShadowB_sim tlPrfMk liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (mkShadowFixed s') (u, j) hInv.shadow_ok hn)
      (by simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
            letV, eval_letC, caseSumV, bindV, v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_zero, env_get_succ, projVal]
          exact bind_const_congr (eval_ren2_eq (genSpkFixedB b.q_total
            (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
            (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) rfl rfl rfl))
  | genOPK u j o =>
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv (t := .genOPK u j o) trivial hroom
    exact mkBaseArm_sim S b (arg := .prod .nat (.prod .nat .nat))
      (fun fhst x => genOpkFixedKB F fhst x) (fun fhst x => genOpkFixedB b.q_total fhst x)
      (fun _ _ => rfl) c s' (.genOPK u j o) (u, (j, o)) trivial hroom hInv
      (genOpkFixedShadowB_sim tlPrfMk liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (mkShadowFixed s') (u, (j, o)) hInv.shadow_ok hn)
      (by simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
            letV, eval_letC, caseSumV, bindV, v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_zero, env_get_succ, projVal]
          exact bind_const_congr (eval_ren2_eq (genOpkFixedB b.q_total
            (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
            (Γ₂ := [.prod .nat (.prod .nat .nat)])
            (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero) rfl rfl rfl))
  | sendOPK u i bu m0 m1 =>
    obtain ⟨s0, hs0⟩ : ∃ s0, projVal prfMkStTy s'.1 = s0 := ⟨_, rfl⟩
    obtain ⟨hb0, hKon, hK, hRoK, hRoOld, hRootK, hRootOld⟩ :=
      mkOnlineStep_bounds S b c s' (.sendOPK u i bu m0 m1) s0 hs0 trivial hroom hInv
    exact mkOnlineArm_sim S b (arg := sendQTy) (fun core x => authMkSendPreKB S F.K_on F.K_ro true core x)
      c s' (.sendOPK u i bu m0 m1) s0 hs0 trivial hroom hInv
      (by dsimp only [mkPreEnv, prfMkStepPre1KeyC, letV, caseSumV]; rw [eval_letC]
          dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
          simp only [env_get_zero, env_get_succ]
          apply authMkSendPreKB_eval_eq S true
          · rfl
          · dsimp only [Ext.step_wk, Ext.refl_wk]; simp only [env_get_zero, env_get_succ]
            rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl
          · exact hb0
          · exact hKon
          · exact hK
          · exact hRoK
          · exact hRoOld
          · exact hRootK
          · exact hRootOld)
      (by intro x0
          exact authMkSendPreKB_leaves S F.K_on F.K_ro (c 0) true
            (Γ₁ := [prfMkCoreTy, .nat, sendQTy, prfMkStTy, .prod prfMkStTy sendQTy])
            (Γ₂ := [sendQTy, prfMkStTy, .prod prfMkStTy sendQTy])
            (Δ := [prfMkCoreTy, .nat, sendQTy, prfMkStTy, .prod prfMkStTy sendQTy])
            .zero .zero (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))
            hb0 hRoK hRootK)
  | sendNoOPK u i bu m0 m1 =>
    obtain ⟨s0, hs0⟩ : ∃ s0, projVal prfMkStTy s'.1 = s0 := ⟨_, rfl⟩
    obtain ⟨hb0, hKon, hK, hRoK, hRoOld, hRootK, hRootOld⟩ :=
      mkOnlineStep_bounds S b c s' (.sendNoOPK u i bu m0 m1) s0 hs0 trivial hroom hInv
    exact mkOnlineArm_sim S b (arg := sendQTy) (fun core x => authMkSendPreKB S F.K_on F.K_ro false core x)
      c s' (.sendNoOPK u i bu m0 m1) s0 hs0 trivial hroom hInv
      (by dsimp only [mkPreEnv, prfMkStepPre1KeyC, letV, caseSumV]; rw [eval_letC]
          dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
          simp only [env_get_zero, env_get_succ]
          apply authMkSendPreKB_eval_eq S false
          · rfl
          · dsimp only [Ext.step_wk, Ext.refl_wk]; simp only [env_get_zero, env_get_succ]
            rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl
          · exact hb0
          · exact hKon
          · exact hK
          · exact hRoK
          · exact hRoOld
          · exact hRootK
          · exact hRootOld)
      (by intro x0
          exact authMkSendPreKB_leaves S F.K_on F.K_ro (c 0) false
            (Γ₁ := [prfMkCoreTy, .nat, sendQTy, prfMkStTy, .prod prfMkStTy sendQTy])
            (Γ₂ := [sendQTy, prfMkStTy, .prod prfMkStTy sendQTy])
            (Δ := [prfMkCoreTy, .nat, sendQTy, prfMkStTy, .prod prfMkStTy sendQTy])
            .zero .zero (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))
            hb0 hRoK hRootK)
  | recvOPK k j o msg =>
    obtain ⟨s0, hs0⟩ : ∃ s0, projVal prfMkStTy s'.1 = s0 := ⟨_, rfl⟩
    obtain ⟨hb0, hKon, hK, hRoK, hRoOld, hRootK, hRootOld⟩ :=
      mkOnlineStep_bounds S b c s' (.recvOPK k j o msg) s0 hs0 trivial hroom hInv
    exact mkOnlineArm_sim S b (arg := recvQTy) (fun core x => authMkRecvPreKB S F.K_on F.K_ro true core x)
      c s' (.recvOPK k j o msg) s0 hs0 trivial hroom hInv
      (by dsimp only [mkPreEnv, prfMkStepPre1KeyC, letV, caseSumV]; rw [eval_letC]
          dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
          simp only [env_get_zero, env_get_succ]
          apply authMkRecvPreKB_eval_eq S true
          · rfl
          · dsimp only [Ext.step_wk, Ext.refl_wk]; simp only [env_get_zero, env_get_succ]
            rcases msg with ⟨⟨_, _, _, _ | _, _, _⟩, _, _, _⟩ <;> rfl
          · exact hb0
          · exact hKon
          · exact hK
          · exact hRoK
          · exact hRoOld
          · exact hRootK
          · exact hRootOld)
      (by intro x0
          exact authMkRecvPreKB_leaves S F.K_on F.K_ro true
            (Γ₁ := [prfMkCoreTy, .nat, recvQTy, prfMkStTy, .prod prfMkStTy recvQTy])
            (Γ₂ := [recvQTy, prfMkStTy, .prod prfMkStTy recvQTy])
            (Δ := [prfMkCoreTy, .nat, recvQTy, prfMkStTy, .prod prfMkStTy recvQTy])
            .zero .zero (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))
            hb0 hRoK hRootK)
  | recvNoOPK k j l msg =>
    obtain ⟨s0, hs0⟩ : ∃ s0, projVal prfMkStTy s'.1 = s0 := ⟨_, rfl⟩
    obtain ⟨hb0, hKon, hK, hRoK, hRoOld, hRootK, hRootOld⟩ :=
      mkOnlineStep_bounds S b c s' (.recvNoOPK k j l msg) s0 hs0 trivial hroom hInv
    exact mkOnlineArm_sim S b (arg := recvQTy) (fun core x => authMkRecvPreKB S F.K_on F.K_ro false core x)
      c s' (.recvNoOPK k j l msg) s0 hs0 trivial hroom hInv
      (by dsimp only [mkPreEnv, prfMkStepPre1KeyC, letV, caseSumV]; rw [eval_letC]
          dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
          simp only [env_get_zero, env_get_succ]
          apply authMkRecvPreKB_eval_eq S false
          · rfl
          · dsimp only [Ext.step_wk, Ext.refl_wk]; simp only [env_get_zero, env_get_succ]
            rcases msg with ⟨⟨_, _, _, _ | _, _, _⟩, _, _, _⟩ <;> rfl
          · exact hb0
          · exact hKon
          · exact hK
          · exact hRoK
          · exact hRoOld
          · exact hRootK
          · exact hRootOld)
      (by intro x0
          exact authMkRecvPreKB_leaves S F.K_on F.K_ro false
            (Γ₁ := [prfMkCoreTy, .nat, recvQTy, prfMkStTy, .prod prfMkStTy recvQTy])
            (Γ₂ := [recvQTy, prfMkStTy, .prod prfMkStTy recvQTy])
            (Δ := [prfMkCoreTy, .nat, recvQTy, prfMkStTy, .prod prfMkStTy recvQTy])
            .zero .zero (.cons s0.2 (.cons s0.1 (.cons x0 (.cons s0 (.cons (s0, x0) .nil)))))
            hb0 hRoK hRootK)
  | roQuery sec =>
    exact roArm_sim S b c s' sec hroom hInv
  | roRootQuery rk dh =>
    exact roRootArm_sim S b c s' rk dh hroom hInv
  | revealDhSecrets =>
    exact revealDh_sim S b c s' hroom hInv
  | registerKey sk =>
    exact mkBaseArm_sim S b (arg := B 32)
      (fun fhst x => registerFixedKB fhst x) (fun fhst x => registerFixedB fhst x)
      (fun _ _ => rfl) c s' (.registerKey sk) sk trivial hroom hInv
      ⟨rfl, registerFixedShadowB_sim tlPrfMk liftPrimComp mem_support_liftPrimComp
        S b (mkShadowFixed s') sk hInv.shadow_ok⟩
      (by simp only [mkPreEnv, prfMkStepPre1KeyC, wrapMkBase, mkcMk, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
            letV, eval_letC, caseSumV, bindV, v, _root_.SignalPqxdh.LegacyCosted.authCodec,
            _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_zero, env_get_succ, projVal]
          exact bind_const_congr (eval_ren2_eq (registerFixedB
            (Γ₁ := [authHybridStateFixedTy, B 32]) (Γ₂ := [B 32])
            (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) rfl rfl rfl))

/-- Forgetful simulation bundle for `prfMsgKeys1KeyKindProg` against `prfMkOldAtomicProg`. -/
theorem prfMsgKeys1KeyKindProg_forgetSim (S : Setup) (b : QueryBudget) (x : Unit) :
    ForgetSim (prfMsgKeys1KeyKindProg S b) (prfMkOldAtomicProg S b)
      forgetMk (authSimPred S) (authSimBounds b) x (AuthMkInv S b) where
  hInit   := prfMsgKeys1KeyKindProg_init_sim S b x
  hHandle := fun c s' t _hc hroom hInv => prfMsgKeys1KeyKindProg_handle_sim S b c s' t hroom hInv
  hFinish := fun c s' bOut _hc hInv => prfMsgKeys1KeyKindProg_finish_sim S b c s' bOut hInv

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfMk
