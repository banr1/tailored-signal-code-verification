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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacDsl
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo

/-!
# Forgetful Step-Simulation for One-Key `Auth` `PrfHmac`

Proves `prfHmac1KeyKindProg_forgetSim`, establishing `ForgetSim` of `prfHmac1KeyKindProg` against
`prfHmacOldAtomicProg` under `forgetHm` and `AuthHmInv`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfInt

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open _root_.Computational.Proofs.ReductionDsl.StepSim (ForgetSim bumpPred)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal projVal embedVal_projVal projVal_embedVal embedEnv
   mapComp mapComp_eval compRename compRename_eval exprRename_eval comp_queries_zero_of_zero
   aiPrfHmac tlPrfHmac liftAuthHandle liftAuthHandle_eval
   mapExpr)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery authSpec)
open _root_.SignalPqxdh.Costed (authCodec pqPrfHmacIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B hmacPrfOracle
   U32)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT v letV bindV caseOptV caseSumV eval_letC AllLeaves liftPrimComp sampleChal samplePrim
   emptyAuthHybridStFixedE authStateTy authRespTy sendQTy recvQTy authHybridStateFixedTy RSF
   ahsfHybrid ahsBase ahsInitKemRecs ahsIdealSessions ahsfRecvCount ahsfMkSaltCache ahsfUpd ahsfMk ahsUpd stUpd
   asUsedSendSessions asPrincipals asSessions asRoCache asRootRoCache
   eAny eFind sidEq natEq bytesBeq findHonestC koskBundleOkC
   checkBundleProvenanceExactC hkdfRoC rootRoC sendGuardE
   aNone initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB
   roFixedB roRootFixedB registerFixedB
   authHybridStateTy authMkSaltCacheTy aRecvHonest aRecvUnfresh eMap eCaseOpt findMV asSpkBundles asOpkEntries asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents asAdvKeys ahsRecvKemRecs ahsMk stMk drKeyTy opkEntryTy oeConsumed oeOpkSk oeOpkPk oeUpd pkmHdr pkmEphAPk hdrSpkId hdrPqspkId hdrOpkId? hdrIkAPk hdrEkAPk hdrKemCt u32Beq u32OfNat optU32Eq nat2Eq nat3Eq bytesLen boolOr queryPrim sbPqspkSk sbPqspkPk sbSpkSk peSecIKA0 rkrMk buildSecretsE isSomeE)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (spkHonIdealFromPeerC defaultMsgKeysE)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (hmStTy muStTy hmPreTy hmResTy hmSendContTy encContTy encPreTy muKeyIdTy intPrepTy intFinArgsTy
   muKeys muChal muPend muBad muMk pendFilterE pendHitE
   hmKeyIdC encPostC hmEncPreIdC finishIntC intSendPrepC sendSidE hmSendTailC
   ipIdeal ipRoC ipRootC
   hmInitC hmFinishC hmPostC hmContX0E queryHmacEval
   hmOther hmDispatch1KeyC hmPre1KeyC hmHandle1KeyC prfHmacRedProg1Key emptyMuE
   hmSendC hmRecvC
   hmForgeIdC forgeRetIdC hmRecvDataTy schedPrepTy schedPrepArgsTy schedFinArgsTy schedArgsTy schedResTy schedOutTy hmRecvPrepC hmSchedPrepC hmSchedFinC hmSchedC finErasedE hmRecvTailC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authFixedShadowStTy emptyRoBothAvlE forgetAuthFixedShadow
   aNoneAtomicE liftExpr1 fixedRoCacheE fixedRootRoCacheE syncRoBothC
   roFixedShadowArmC roRootFixedShadowArmC
   authFixedAtomicTy authSendQAtomicTy authRecvQAtomicTy
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv
   AuthBaseValOnlineBounded AuthFixedValOnlineBounded AuthFixedAtomOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache CacheStepAtMostOne
   RoBothShadowRel AuthFixedShadowAt
   authHmShadowStTy hmShadowFixed forgetHm prfHmacOldAtomicProg AuthHmShadowAt AuthHmInv
   dispatchAuthQEval dispatchAuthQ_eval_qenc)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (dropShadow0 dropShadow1 prfHmacKindInitC prfHmacKindHandleC prfHmacKindFinishC
   hmRebuildE hmBaseArmC hmPostRunC liftPrfHmac1 intSendPrepKC hmSendKC
   hmSchedPrepKC hmSchedKC hmRecvTailKC hmRecvKC prfHmac1KeyKindProg)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
  (hmFinishC_fuel_eq)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
  (initPrinFixedShadowB_sim corruptFixedShadowB_sim genSpkFixedShadowB_sim
   genOpkFixedShadowB_sim registerFixedShadowB_sim)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
  (mapComp_eval_of_zero mapComp_congr_of_zero mem_support_mapComp_of_zero
   AllLeaves_mem_support liftPrimComp_eval_congr mem_support_liftPrimComp
   atomRoCache_embedVal atomRootRoCache_embedVal take_eq_of_le take_min_eq_of_le
   findHonestC_prf_fuel_eq koskBundleOkC_fuel_eq koskSenderOkC_fuel_eq
   checkBundleProvenanceExactC_fuel_eq spkHonIdealFromPeerC_fuel_eq
   kyberCheckE_fuel_eq kyberCheckE_snd_len_le
   hkdfRoC_fuel_eq hkdfRoC_step rootRoC_fuel_eq rootRoC_step
   letV_congr letV_congr_eq letV_allLeaves letV_allLeaves_eq
   bindV_congr bindV_congr_leaves bindV_allLeaves_const bindV_allLeaves
   caseSumV_congr caseSumV_congr_eq caseSumV_allLeaves caseSumV_allLeaves_eq
   caseOptV_congr caseOptV_allLeaves caseOptV_allLeaves_eq
   ite_congr_eval ite_allLeaves)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfHm
  (lift1_eval)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo
  (emptyRoBothAvlE_roBothShadowRel syncRoBothC_sim
   roFixedShadowArmC_sim_hmac roRootFixedShadowArmC_sim_hmac)

private abbrev env_get_succ := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ
private abbrev env_get_zero := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero

private theorem projVal_pair {a b : PT} (p : (embedTy (.prod a b)).denote) :
    projVal (.prod a b) p = (projVal a p.1, projVal b p.2) := rfl

private theorem projVal_hmSt_1 (s : (embedTy hmStTy).denote) :
    (projVal hmStTy s).1 = s.1 := rfl

private theorem projVal_hmSt_21 (s : (embedTy hmStTy).denote) :
    (projVal hmStTy s).2.1 = projVal authHybridStateFixedTy s.2.1 := rfl

private theorem projVal_hmSt_22 (s : (embedTy hmStTy).denote) :
    (projVal hmStTy s).2.2 = projVal muStTy s.2.2 := rfl

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

private theorem eval_ren2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {A B R : PT} {Δ : List PT} (vA : Var Δ A) (vB : Var Δ B)
    (c0 : Comp pqxdhOps I [A, B] R) (c : Comp pqxdhOps I Δ R) (env : Env Δ)
    (hEq : compRename (ren2 vA vB) c0 = c) :
    c.eval env = c0.eval (.cons (env.get vA) (.cons (env.get vB) .nil)) := by
  rw [← hEq]
  exact compRename_eval c0 (ren2 vA vB) _ env
    (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)

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

private theorem liftPrfHmac1_eval {a r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftPrfHmac1 c e).eval ρ =
      embedVal r <$> c.eval (.cons (projVal a (e.eval ρ)) .nil) :=
  lift1_eval tlPrfHmac (fun _ => rfl) c e ρ

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

private theorem prfHmac1KeyKindProg_init_sim (S : Setup) (b : QueryBudget) (x : Unit) :
    Prod.map id forgetHm <$> (prfHmac1KeyKindProg S b).init.eval (.cons x .nil) =
      (prfHmacOldAtomicProg S b).init.eval (.cons x .nil) ∧
    ∀ p ∈ support ((prfHmac1KeyKindProg S b).init.eval (.cons x .nil)),
      AuthHmInv S b 0 p.2 := by
  refine ⟨?_, ?_⟩
  · change Prod.map id forgetHm <$> (prfHmacKindInitC S).eval (.cons x .nil) =
      (mapComp tlPrfHmac (hmInitC S)).eval (.cons x .nil)
    dsimp only [prfHmacKindInitC, Comp.eval, Expr.eval, Expr.v0, forgetHm, Prod.map, id]
    simp only [Env.get, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    exact bind_pure _
  · change ∀ p ∈ support ((prfHmacKindInitC S).eval (.cons x .nil)), AuthHmInv S b 0 p.2
    dsimp only [prfHmacKindInitC, Comp.eval]
    intro p hp
    erw [mem_support_bind_iff] at hp
    rcases hp with ⟨y, hy, hp⟩
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    change y ∈ support ((mapComp tlPrfHmac (hmInitC S)).eval (.cons x .nil)) at hy
    rw [mapComp_eval1 tlPrfHmac (fun _ => rfl) (hmInitC S) x] at hy
    obtain ⟨z, hz, hzy⟩ := OracleComp.mem_support_map_peel _ _ hy
    dsimp only [hmInitC, bindV, Comp.eval] at hz
    erw [mem_support_bind_iff] at hz
    rcases hz with ⟨jt, _, hz⟩
    erw [mem_support_bind_iff] at hz
    rcases hz with ⟨secb, _, hz⟩
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [Expr.eval, Expr.v0, Env.get]
    set empFixed := (emptyAuthHybridStFixedE (.var .zero)).eval
      (.cons secb (.cons jt (.cons (projVal .unit x) .nil)))
    have hy2 : y.2 = (jt, (embedVal authHybridStateFixedTy empFixed, ([], ([], ([], false))))) := by
      rw [hzy]; rfl
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
    rw [hy2]
    exact ⟨AuthCounterInv.zero b, ⟨⟨hBnd,
      by dsimp only [hmShadowFixed]; rw [hRo]; exact Nat.zero_le _,
      by dsimp only [hmShadowFixed]; rw [hRoot]; exact Nat.zero_le _,
      emptyRoBothAvlE_roBothShadowRel (AuthKindFuels.ofBudget S b).K_cap _ _ hRo hRoot⟩,
      Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩⟩

private theorem liftPrfHmacDropShadow1_eval {a b r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a, b] r)
    (sVal : (Ty.prod (embedTy a) roBothAvlTy).denote) (bVal : (embedTy b).denote) :
    (Comp.bind (I := pqPrfHmacIface) (.ret (.fst .v0))
        (compRename dropShadow1 (mapComp tlPrfHmac c))).eval
        (.cons sVal (.cons bVal .nil)) =
      embedVal r <$> c.eval (.cons (projVal a sVal.1) (.cons (projVal b bVal) .nil)) := by
  change (Comp.bind (I := aiPrfHmac.toIface) (.ret (.fst .v0))
      (compRename dropShadow1 (mapComp tlPrfHmac c))).eval
      (.cons sVal (.cons bVal .nil)) = _
  dsimp only [Comp.eval, Expr.eval, Expr.v0, Env.get]
  exact (pure_bind sVal.1 _).trans
    ((compRename_eval (mapComp tlPrfHmac c) dropShadow1
      (.cons sVal.1 (.cons bVal .nil)) _
      (fun | .zero => rfl | .succ .zero => rfl | .succ (.succ v) => nomatch v)).trans
      (mapComp_eval2 tlPrfHmac (fun _ => rfl) c sVal.1 bVal))

private theorem liftPrfHmacMapComp2_eval {a b r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a, b] r)
    (x : (embedTy a).denote) (y : (embedTy b).denote) :
    Comp.eval (I := pqPrfHmacIface) (mapComp tlPrfHmac c) (.cons x (.cons y .nil)) =
      embedVal r <$> c.eval (.cons (projVal a x) (.cons (projVal b y) .nil)) :=
  mapComp_eval2 tlPrfHmac (fun _ => rfl) c x y

private theorem prfHmac1KeyKindProg_finish_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (bOut : Bool)
    (hInv : AuthHmInv S b c s') :
    (prfHmac1KeyKindProg S b).finish.eval (.cons s' (.cons bOut .nil)) =
      (prfHmacOldAtomicProg S b).finish.eval (.cons (forgetHm s') (.cons bOut .nil)) := by
  let F := AuthKindFuels.ofBudget S b
  have hBound : (projVal hmStTy s'.1).2.2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).M_on := by
    have hPend := hInv.shadow_ok.mu_pend_le
    have hOn := hInv.counter_inv.on_le
    have hLen : (projVal hmStTy s'.1).2.2.2.2.1.length = s'.1.2.2.2.2.1.length := by
      rw [projVal_hmSt_22]
      simp [projVal]
    dsimp only [AuthKindFuels.ofBudget]
    omega
  have hMK : (AuthKindFuels.ofBudget S b).M_on ≤ (AuthKindFuels.ofBudget S b).K_on := by
    dsimp only [AuthKindFuels.ofBudget, AuthKindFuels.K_on]
    omega
  exact (liftPrfHmacDropShadow1_eval (hmFinishC F.K_on) s' bOut).trans
    ((congrArg (embedVal .bool <$> ·) (hmFinishC_fuel_eq S b (projVal hmStTy s'.1) bOut hBound hMK)).trans
      (liftPrfHmacMapComp2_eval (hmFinishC b.q_total) s'.1 bOut).symm)

private theorem oldHandle_eval (S : Setup) (b : QueryBudget)
    (s' : authHmShadowStTy.denote) (t : AuthQuery S) :
    (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal (.prod authRespTy hmStTy) <$>
        (hmHandle1KeyC S b.q_total).eval
          (.cons (projVal hmStTy s'.1)
            (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) := by
  change (liftAuthHandle tlPrfHmac S (hmHandle1KeyC S b.q_total)).eval
    (.cons s'.1 (.cons ((authCodec S).qenc t) .nil)) = _
  conv_lhs => rw [← embedVal_projVal hmStTy s'.1]
  exact liftAuthHandle_eval tlPrfHmac S (fun _ => rfl) (hmHandle1KeyC S b.q_total)
    (projVal hmStTy s'.1) t

private theorem hmOther_rhs_eq (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (s' : authHmShadowStTy.denote) (t : AuthQuery S) (xAtom : (embedTy arg).denote)
    (m : Comp pqxdhOps pqPrimIface [authHybridStateFixedTy, arg] RSF)
    (hPre : (hmPre1KeyC S b.q_total).eval
        (.cons (projVal hmStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
      (m.eval (.cons (projVal authHybridStateFixedTy s'.1.2.1) (.cons (projVal arg xAtom) .nil)) >>=
        fun r => pure (Sum.inl (r, projVal muStTy s'.1.2.2)))) :
    (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) =
      ((mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle) m)).eval
        (.cons s'.1.2.1 (.cons xAtom .nil)) >>=
        fun rsf => pure (rsf.1, (s'.1.1, (rsf.2, s'.1.2.2)))) := by
  rw [oldHandle_eval]
  change embedVal (.prod authRespTy hmStTy) <$>
      (hmHandle1KeyC S b.q_total).eval
        (.cons (projVal hmStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
    ((mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle) m)).eval
      (.cons s'.1.2.1 (.cons xAtom .nil)) >>=
      fun rsf => pure (rsf.1, (s'.1.1, (rsf.2, s'.1.2.2))))
  rw [mapComp_eval2 tlPrfHmac (fun _ => rfl)
    (liftPrimComp (C := hmacPrfOracle) m) s'.1.2.1 xAtom]
  dsimp only [hmHandle1KeyC, bindV, letV, Comp.eval]
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval, hPre]
  rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.embedPrim_bind]
  erw [map_bind, bind_assoc]
  conv_rhs => erw [map_eq_bind_pure_comp, bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun r _ => ?_
  dsimp only [Function.comp_apply]
  erw [_root_.SignalPqxdh.Security.embedPrim_pure, pure_bind, eval_letC, pure_bind]
  dsimp only [caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, projVal_hmSt_1]
  erw [map_pure]
  have hMu : embedVal muStTy (projVal muStTy s'.1.2.2) = s'.1.2.2 :=
    embedVal_projVal muStTy s'.1.2.2
  rcases r with ⟨resp, fhst1⟩
  change pure (embedVal authRespTy resp, (s'.1.1, (embedVal authHybridStateFixedTy fhst1, embedVal muStTy (projVal muStTy s'.1.2.2)))) = _
  rw [hMu]; rfl

private theorem hmBaseArm_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (stepK stepOld : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RSF)
    (hRenK : compRename (ren2 (.succ .zero) .zero)
        (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero) =
      stepK (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
        (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (t : AuthQuery S)
    (xAtom : (embedTy arg).denote)
    (hOn : authSimPred S 0 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s')
    (hSim :
      (mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle)
          (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons (hmShadowFixed s').1 (.cons xAtom .nil)) =
      (mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle)
          (stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons (hmShadowFixed s').1 (.cons xAtom .nil)) ∧
      ∀ rsf ∈ support ((mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle)
          (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
            (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons (hmShadowFixed s').1 (.cons xAtom .nil))),
        AuthFixedShadowAt S b (c 0 + 1) (c 0 + c 1) (c 0 + c 2) (rsf.2, (hmShadowFixed s').2))
    (hPre : (hmPre1KeyC S b.q_total).eval
        (.cons (projVal hmStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
      ((stepOld (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero).eval
        (.cons (projVal authHybridStateFixedTy s'.1.2.1) (.cons (projVal arg xAtom) .nil)) >>=
        fun r => pure (Sum.inl (r, projVal muStTy s'.1.2.2)))) :
    let ρ := Env.cons xAtom (.cons s' (.cons ((authCodec S).qenc t) .nil))
    Prod.map id forgetHm <$> (hmBaseArmC S stepK).eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((hmBaseArmC S stepK).eval ρ),
      AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro ρ
  have hLhsLift :
      (liftPrfHmac1
        (liftPrimComp (C := hmacPrfOracle)
          (letV (.fst (.var .zero)) fun fhst =>
           letV (.snd (.var (.succ .zero))) fun x =>
           stepK fhst x))
        (.pair (.fst (.snd (.fst .v1))) .v0)).eval ρ =
      (mapComp tlPrfHmac (liftPrimComp (C := hmacPrfOracle)
        (stepK (Γ₁ := [authHybridStateFixedTy, arg]) (Γ₂ := [arg])
          (Δ := [authHybridStateFixedTy, arg]) .zero .zero))).eval
        (.cons s'.1.2.1 (.cons xAtom .nil)) := by
    rw [liftPrfHmac1_eval,
        mapComp_eval2 tlPrfHmac (fun _ => rfl)]
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, ρ,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval]
    rw [projVal_pair]
    refine congrArg _ (congrArg _ ?_)
    dsimp only [letV]
    rw [eval_letC, eval_letC]
    simp only [Expr.eval, env_get_zero, env_get_succ]
    exact eval_ren2 (.succ .zero) .zero _ _ _ hRenK
  refine ⟨?_, ?_⟩
  · rw [hmOther_rhs_eq S b s' t xAtom _ hPre]
    dsimp only [hmShadowFixed] at hSim
    simp only [hmBaseArmC, hmRebuildE, forgetHm, Comp.eval, Expr.eval, Expr.v0, Expr.v2,
      Env.get, ρ, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map, id]
    erw [hLhsLift, hSim.1]
    rfl
  · dsimp only [hmBaseArmC, Comp.eval]
    intro p hp
    erw [hLhsLift, mem_support_bind_iff] at hp
    rcases hp with ⟨rsf, hrsf, hp⟩
    simp only [hmRebuildE, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ,
      support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hSh := hSim.2 rsf hrsf
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, hOn]
    have hGe1 : c 1 ≤ bumpPred (authSimPred S) c t 1 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe2 : c 2 ≤ bumpPred (authSimPred S) c t 2 := by dsimp only [bumpPred]; split_ifs <;> omega
    refine ⟨hBump, ⟨?_, ?_, ?_, ?_⟩⟩
    · exact hSh.mono (by omega) (by omega) (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_keys_le (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_chal_le (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_pend_le (by omega)

private theorem roArm_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (sec : (PB 192).denote)
    (hroom : ∀ j : Fin 4, authSimPred S j (.roQuery sec) → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let t := AuthQuery.roQuery (S := S) sec
    let ρ := Env.cons sec (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm := Comp.bind
      (roFixedShadowArmC aiPrfHmac F.K_cap (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (hmRebuildE (.fst .v2) (.snd .v0))))
    Prod.map id forgetHm <$> arm.eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F t ρ arm
  have hRoPred : authSimPred S 1 t := trivial
  have ⟨_, hOld, hKR⟩ := AuthCounterInv.ro_step_bounds hInv.counter_inv hRoPred hroom
  have hSim := roFixedShadowArmC_sim_hmac S b
    (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0 ρ (hmShadowFixed s') sec
    rfl rfl hInv.shadow_ok.fixed_ok (by omega) (by omega)
  have hPre : (hmPre1KeyC S b.q_total).eval
      (.cons (projVal hmStTy s'.1)
        (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
    ((roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
        (Δ := [authHybridStateFixedTy, B 192]) .zero .zero).eval
      (.cons (projVal authHybridStateFixedTy s'.1.2.1) (.cons (projVal (B 192) sec) .nil)) >>=
      fun r => pure (Sum.inl (r, projVal muStTy s'.1.2.2))) := by
    simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ, t]
    exact bind_const_congr (eval_ren2_eq
      (roFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, B 192]) (Γ₂ := [B 192])
        (Δ := [authHybridStateFixedTy, B 192]) .zero .zero) rfl rfl rfl)
  refine ⟨?_, ?_⟩
  · dsimp only [hmShadowFixed] at hSim
    have hLhs : Prod.map id forgetHm <$> arm.eval ρ =
        ((Prod.map id forgetAuthFixedShadow <$>
            (roFixedShadowArmC aiPrfHmac (AuthKindFuels.ofBudget S b).K_cap
              (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0).eval ρ) >>=
          fun rsf => pure (rsf.1, (s'.1.1, (rsf.2, s'.1.2.2)))) := by
      simp only [arm, F, hmRebuildE, forgetHm, forgetAuthFixedShadow,
        Comp.eval, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map, id]
    exact hLhs.trans ((bind_const_congr hSim.1).trans
      (hmOther_rhs_eq S b (arg := B 192) s' t sec _ hPre).symm)
  · dsimp only [arm, Comp.eval]
    intro p hp
    erw [mem_support_bind_iff] at hp
    rcases hp with ⟨q0, hq0, hp⟩
    simp only [hmRebuildE, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ,
      support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hSh := hSim.2 q0 hq0
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthOnlineQuery, t]
    have hB1 : bumpPred (authSimPred S) c t 1 = c 1 + 1 := by simp [bumpPred, hRoPred]
    have hB2 : bumpPred (authSimPred S) c t 2 = c 2 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthRoRootQuery, t]
    refine ⟨hBump, ⟨?_, ?_, ?_, ?_⟩⟩
    · exact hSh.mono (by omega) (by omega) (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_keys_le (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_chal_le (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_pend_le (by omega)

private theorem roRootArm_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (rk dh : (PB 32).denote)
    (hroom : ∀ j : Fin 4, authSimPred S j (.roRootQuery rk dh) → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let t := AuthQuery.roRootQuery (S := S) rk dh
    let ρ := Env.cons (rk, dh) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm := Comp.bind
      (roRootFixedShadowArmC aiPrfHmac F.K_cap (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (hmRebuildE (.fst .v2) (.snd .v0))))
    Prod.map id forgetHm <$> arm.eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F t ρ arm
  have hRtPred : authSimPred S 2 t := trivial
  have ⟨_, hOld, hKR⟩ := AuthCounterInv.roRoot_step_bounds hInv.counter_inv hRtPred hroom
  have hSim := roRootFixedShadowArmC_sim_hmac S b
    (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0 ρ (hmShadowFixed s') (rk, dh)
    rfl rfl hInv.shadow_ok.fixed_ok (by omega) (by omega)
  have hPre : (hmPre1KeyC S b.q_total).eval
      (.cons (projVal hmStTy s'.1)
        (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
    ((roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
        (Γ₂ := [.prod (B 32) (B 32)]) (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
        .zero .zero).eval
      (.cons (projVal authHybridStateFixedTy s'.1.2.1)
        (.cons (projVal (.prod (B 32) (B 32)) (rk, dh)) .nil)) >>=
      fun r => pure (Sum.inl (r, projVal muStTy s'.1.2.2))) := by
    simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
      _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
      Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ, t]
    exact bind_const_congr (eval_ren2_eq
      (roRootFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
        (Γ₂ := [.prod (B 32) (B 32)]) (Δ := [authHybridStateFixedTy, .prod (B 32) (B 32)])
        .zero .zero) rfl rfl rfl)
  refine ⟨?_, ?_⟩
  · dsimp only [hmShadowFixed] at hSim
    have hLhs : Prod.map id forgetHm <$> arm.eval ρ =
        ((Prod.map id forgetAuthFixedShadow <$>
            (roRootFixedShadowArmC aiPrfHmac (AuthKindFuels.ofBudget S b).K_cap
              (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0).eval ρ) >>=
          fun rsf => pure (rsf.1, (s'.1.1, (rsf.2, s'.1.2.2)))) := by
      simp only [arm, F, hmRebuildE, forgetHm, forgetAuthFixedShadow,
        Comp.eval, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map, id]
    exact hLhs.trans ((bind_const_congr hSim.1).trans
      (hmOther_rhs_eq S b (arg := .prod (B 32) (B 32)) s' t (rk, dh) _ hPre).symm)
  · dsimp only [arm, Comp.eval]
    intro p hp
    erw [mem_support_bind_iff] at hp
    rcases hp with ⟨q0, hq0, hp⟩
    simp only [hmRebuildE, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ,
      support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hSh := hSim.2 q0 hq0
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthOnlineQuery, t]
    have hB1 : bumpPred (authSimPred S) c t 1 = c 1 := by
      simp [bumpPred, authSimPred, _root_.SignalPqxdh.isAuthRoQuery, t]
    have hB2 : bumpPred (authSimPred S) c t 2 = c 2 + 1 := by simp [bumpPred, hRtPred]
    refine ⟨hBump, ⟨?_, ?_, ?_, ?_⟩⟩
    · exact hSh.mono (by omega) (by omega) (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_keys_le (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_chal_le (by omega)
    · exact Nat.le_trans hInv.shadow_ok.mu_pend_le (by omega)

private theorem revealDh_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote)
    (hroom : ∀ j : Fin 4, authSimPred S j .revealDhSecrets → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    let t := AuthQuery.revealDhSecrets (S := S)
    let ρ := Env.cons () (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm : Comp pqAtomicOps pqPrfHmacIface
        [.unit, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
      .ret (.pair aNoneAtomicE .v1)
    Prod.map id forgetHm <$> arm.eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro t ρ arm
  refine ⟨?_, ?_⟩
  · rw [oldHandle_eval]
    have hRhs : ∀ (s0 : hmStTy.denote),
        (hmHandle1KeyC S b.q_total).eval
          (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
        pure (Sum.inl (), s0) := by
      intro s0
      simp only [hmHandle1KeyC, hmPre1KeyC, hmDispatch1KeyC, bindV, letV, eval_letC, caseSumV, v,
        _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
        aNone, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval,
        _root_.SignalPqxdh.Security.embedPrim_pure, t]
      rcases s0 with ⟨a, b0, c0⟩
      exact pure_bind _ _
    rw [hRhs (projVal hmStTy s'.1)]
    simp only [arm, aNoneAtomicE, forgetHm, Comp.eval, Expr.eval, Expr.v1, Env.get, ρ,
      map_pure, Prod.map, id]
    exact congrArg pure (Prod.ext rfl (embedVal_projVal hmStTy s'.1).symm)
  · simp only [arm, Comp.eval, Expr.eval, Expr.v1, Env.get, ρ]
    intro p hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hGe0 : c 0 ≤ bumpPred (authSimPred S) c t 0 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe1 : c 1 ≤ bumpPred (authSimPred S) c t 1 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe2 : c 2 ≤ bumpPred (authSimPred S) c t 2 := by dsimp only [bumpPred]; split_ifs <;> omega
    exact ⟨hBump, ⟨hInv.shadow_ok.fixed_ok.mono hGe0 (by omega) (by omega),
      Nat.le_trans hInv.shadow_ok.mu_keys_le hGe0,
      Nat.le_trans hInv.shadow_ok.mu_chal_le hGe0,
      Nat.le_trans hInv.shadow_ok.mu_pend_le hGe0⟩⟩

/-! ## Online Session-Arm Simulation -/

private theorem ret_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT} {P : τ.denote → Prop}
    {e : Expr pqxdhOps Γ τ} {env : Env Γ} (hP : P (e.eval env)) :
    AllLeaves P ((Comp.ret (I := I) e).eval env) :=
  AllLeaves.pure hP

private theorem AllLeaves_of_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {oa : OracleComp spec α} (h : ∀ x ∈ support oa, P x) :
    AllLeaves P oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AllLeaves.pure (h a (by simp))
  | query_bind q k ih =>
    intro u
    exact ih u fun x hx =>
      h x (by rw [mem_support_bind_iff]; exact ⟨u, mem_support_query q u, hx⟩)

private structure MuValBounded (m : ℕ) (mst : muStTy.denote) : Prop where
  keys_le : mst.1.length ≤ m
  chal_le : mst.2.1.length ≤ m
  pend_le : mst.2.2.1.length ≤ m

private theorem MuValBounded.mono {m₁ m₂ : ℕ} {mst : muStTy.denote}
    (h : MuValBounded m₁ mst) (hle : m₁ ≤ m₂) : MuValBounded m₂ mst :=
  ⟨Nat.le_trans h.keys_le hle, Nat.le_trans h.chal_le hle, Nat.le_trans h.pend_le hle⟩

private structure FixedStepPost (n : ℕ) (fhst0 fhst1 : authHybridStateFixedTy.denote) : Prop where
  bounded : AuthFixedValOnlineBounded (n + 1) fhst1
  ro_step : CacheStepAtMostOne (valRoCache fhst0.1.1) (valRoCache fhst1.1.1)
  root_step : CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valRootRoCache fhst1.1.1)

private abbrev valIpRoC (p : intPrepTy.denote) := p.2.2.2.2.2.2.2.2.2.2.1
private abbrev valIpRootC (p : intPrepTy.denote) := p.2.2.2.2.2.2.2.2.2.2.2

@[reducible] private def HmPreLeafInv (n : ℕ) (fhst0 : authHybridStateFixedTy.denote) :
    hmPreTy.denote → Prop
  | .inl r => FixedStepPost n fhst0 r.1.2 ∧ MuValBounded (n + 1) r.2
  | .inr c =>
      c.2.2.2.2.1 = fhst0 ∧
        CacheStepAtMostOne (valRoCache fhst0.1.1) (valIpRoC c.2.2.2.1) ∧
        CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valIpRootC c.2.2.2.1) ∧
        c.2.2.2.2.2.2.2.2.2.1.length ≤ n + 1 ∧
        c.2.2.2.2.2.2.2.2.2.2.1.length ≤ n ∧
        c.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ n

private theorem foldr_step_len_le {α : Type} (f : α → List α → Bool) :
    ∀ xs : List α,
      (xs.foldr (fun x acc => if f x acc then acc else x :: acc) []).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    dsimp only [List.foldr]
    split_ifs <;> simp only [List.length_cons] <;> have := foldr_step_len_le f xs <;> omega

private theorem pendFilterE_fuel_eq {K₁ K₂ : ℕ} {Γ₁ Γ : List PT}
    (a : Var Γ₁ (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.muPendTy
      (.prod .nat (B 359)))) [ha : Ext Γ₁ Γ] {env : Env Γ}
    (h₁ : (env.get (ha.wk a)).1.length ≤ K₁)
    (h₂ : (env.get (ha.wk a)).1.length ≤ K₂) :
    (pendFilterE K₁ a).eval env = (pendFilterE K₂ a).eval env := by
  simp only [pendFilterE, v, Expr.eval, take_eq_of_le h₁ h₂]

private theorem pendFilterE_len_le {K : ℕ} {Γ₁ Γ : List PT}
    (a : Var Γ₁ (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.muPendTy
      (.prod .nat (B 359)))) [ha : Ext Γ₁ Γ] (env : Env Γ) :
    ((pendFilterE K a).eval env).length ≤ (env.get (ha.wk a)).1.length := by
  dsimp only [pendFilterE, v, Expr.eval]
  refine Nat.le_trans (foldr_step_len_le _ _) ?_
  rw [List.length_take]
  omega

private theorem pendHitE_fuel_eq {K₁ K₂ : ℕ} {Γ₁ Γ : List PT}
    (a : Var Γ₁ (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.muPendTy
      (.prod .nat (.prod (B 359) (B 32))))) [ha : Ext Γ₁ Γ]
    {env : Env Γ}
    (h₁ : (env.get (ha.wk a)).1.length ≤ K₁)
    (h₂ : (env.get (ha.wk a)).1.length ≤ K₂) :
    (pendHitE K₁ a).eval env = (pendHitE K₂ a).eval env := by
  simp only [pendHitE, eAny, v, Expr.eval, take_eq_of_le h₁ h₂]

private theorem hmKeyIdC_fuel_eq {K₁ K₂ : ℕ} {Δ : List PT}
    {a₁ a₂ : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)}
    {env : Env Δ}
    (ha : a₁.eval env = a₂.eval env)
    (h₁ : (a₂.eval env).2.1.length ≤ K₁)
    (h₂ : (a₂.eval env).2.1.length ≤ K₂) :
    (hmKeyIdC K₁ a₁).eval env = (hmKeyIdC K₂ a₂).eval env := by
  unfold hmKeyIdC
  refine letV_congr_eq ha fun av hav => ?_
  rw [ha] at hav
  refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun st hst => ?_
  have hstEq : st = (a₂.eval env).2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst
  refine caseOptV_congr ?_ rfl fun _ => rfl
  dsimp only [eFind, muKeys, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_zero, hstEq, take_eq_of_le h₁ h₂]

private theorem hmKeyIdC_leaves (K : ℕ) {n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy))
    (env : Env Δ)
    (hKeys : (a.eval env).2.1.length ≤ n) :
    AllLeaves (fun kr =>
      kr.2.1.length ≤ n + 1 ∧
      kr.2.2.1 = (a.eval env).2.2.1 ∧
      kr.2.2.2.1 = (a.eval env).2.2.2.1)
      ((hmKeyIdC K a).eval env) := by
  unfold hmKeyIdC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hst => ?_
  have hstEq : st = (a.eval env).2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst
  refine caseOptV_allLeaves ?_ fun _ => ?_
  · refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine ret_allLeaves ?_
    dsimp only [muMk, muKeys, muChal, muPend, muBad, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      List.length_cons]
    simp only [env_get_succ, env_get_zero]
    rw [hstEq]
    exact ⟨Nat.succ_le_succ hKeys, rfl, rfl⟩
  · refine ret_allLeaves ?_
    dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero]
    rw [hstEq]
    exact ⟨Nat.le_trans hKeys (Nat.le_succ n), rfl, rfl⟩

private theorem encPostC_fuel_eq {K₁ K₂ : ℕ} {Δ : List PT}
    {a₁ a₂ : Expr pqxdhOps Δ (.prod encContTy (B 32))}
    {env : Env Δ}
    (ha : a₁.eval env = a₂.eval env)
    (h₁ : (a₂.eval env).1.2.2.2.2.2.2.1.length ≤ K₁)
    (h₂ : (a₂.eval env).1.2.2.2.2.2.2.1.length ≤ K₂) :
    (encPostC K₁ a₁).eval env = (encPostC K₂ a₂).eval env := by
  unfold encPostC
  refine letV_congr_eq ha fun av hav => ?_
  rw [ha] at hav
  refine letV_congr_eq rfl fun cv hcv => ?_
  iterate 5 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun st hst => ?_
  have hstEq : st = (a₂.eval env).1.2.2.2.2 := by
    have hcEq : cv = (a₂.eval env).1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcv
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] using hst
  iterate 2 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun fa hfa => ?_
  refine letV_congr_eq rfl fun ha' hha' => ?_
  have hfa1 : fa.1 = st.2.2.1 := by
    simpa [muPend, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
      congrArg Prod.fst hfa
  have hha1 : ha'.1 = st.2.2.1 := by
    simpa [muPend, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
      congrArg Prod.fst hha'
  have hfaL₁ : fa.1.length ≤ K₁ := by rw [hfa1, hstEq]; exact h₁
  have hfaL₂ : fa.1.length ≤ K₂ := by rw [hfa1, hstEq]; exact h₂
  have hhaL₁ : ha'.1.length ≤ K₁ := by rw [hha1, hstEq]; exact h₁
  have hhaL₂ : ha'.1.length ≤ K₂ := by rw [hha1, hstEq]; exact h₂
  dsimp only [Comp.eval]
  congr 1
  dsimp only [Expr.eval, muMk, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.boolOr]
  rw [pendFilterE_fuel_eq _
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfaL₁)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hfaL₂),
      pendHitE_fuel_eq _
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhaL₁)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhaL₂)]

private theorem encPostC_leaves (K : ℕ) {n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod encContTy (B 32)))
    (env : Env Δ)
    (hK : (a.eval env).1.2.2.2.2.1.length ≤ n + 1)
    (hC : (a.eval env).1.2.2.2.2.2.1.length ≤ n)
    (hP : (a.eval env).1.2.2.2.2.2.2.1.length ≤ n) :
    AllLeaves (fun ep => MuValBounded (n + 1) ep.2) ((encPostC K a).eval env) := by
  unfold encPostC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves_eq fun cv hcv => ?_
  iterate 5 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hst => ?_
  have hstEq : st = (a.eval env).1.2.2.2.2 := by
    have hcEq : cv = (a.eval env).1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcv
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] using hst
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun fa hfa => ?_
  refine letV_allLeaves fun _ => ?_
  have hfa1 : fa.1 = st.2.2.1 := by
    simpa [muPend, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
      congrArg Prod.fst hfa
  refine ret_allLeaves ?_
  dsimp only [muMk, muKeys, muChal, v, Expr.eval, Ext.step_wk, Ext.refl_wk, List.length_cons]
  refine ⟨?_, ?_, ?_⟩
  · simpa [env_get_succ, env_get_zero, hstEq] using hK
  · simpa [env_get_succ, env_get_zero, hstEq] using Nat.succ_le_succ hC
  · refine Nat.le_trans (pendFilterE_len_le _ _) ?_
    simpa [env_get_succ, env_get_zero, hfa1, hstEq] using Nat.le_trans hP (Nat.le_succ n)

private theorem hmEncPreIdC_fuel_eq {K₁ K₂ n : ℕ} {Δ : List PT}
    {a₁ a₂ : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))}
    {env : Env Δ}
    (ha : a₁.eval env = a₂.eval env)
    (hMu : MuValBounded n (a₂.eval env).2.2.2.2)
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (hmEncPreIdC K₁ a₁).eval env = (hmEncPreIdC K₂ a₂).eval env := by
  unfold hmEncPreIdC
  refine letV_congr_eq ha fun av hav => ?_
  rw [ha] at hav
  iterate 4 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun st0 hst0 => ?_
  have hst0Eq : st0 = (a₂.eval env).2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst0
  refine caseOptV_congr ?_ ?_ fun _ => rfl
  · dsimp only [eFind, muChal, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_zero, hst0Eq,
      take_eq_of_le (Nat.le_trans hMu.chal_le h₁) (Nat.le_trans hMu.chal_le h₂)]
  · refine bindV_congr_leaves
      (hmKeyIdC_fuel_eq rfl
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using Nat.le_trans hMu.keys_le h₁)
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using Nat.le_trans hMu.keys_le h₂))
      (hmKeyIdC_leaves K₁ _ _ (n := n)
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using hMu.keys_le))
      fun kr ⟨_, _, hPendEq⟩ => ?_
    have hPendEq' : kr.2.2.2.1 = (a₂.eval env).2.2.2.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using hPendEq
    iterate 2 refine letV_congr rfl fun _ => ?_
    refine letV_congr_eq rfl fun st hst => ?_
    have hstEq : st = kr.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hst
    refine bindV_congr rfl fun _ => ?_
    refine letV_congr_eq rfl fun cv hcv => ?_
    have hcPend : cv.2.2.2.2.2.2.1 = (a₂.eval env).2.2.2.2.2.2.1 := by
      have : cv.2.2.2.2 = st := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
          congrArg (fun x => x.2.2.2.2) hcv
      rw [this, hstEq, hPendEq']
    refine ite_congr_eval rfl ?_ rfl
    refine bindV_congr rfl fun _ => ?_
    refine bindV_congr (encPostC_fuel_eq rfl ?_ ?_) fun _ => rfl
    · simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcPend] using
        Nat.le_trans hMu.pend_le h₁
    · simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcPend] using
        Nat.le_trans hMu.pend_le h₂

private theorem hmEncPreIdC_leaves (K : ℕ) {n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ)
    (hMu : MuValBounded n (a.eval env).2.2.2.2) :
    AllLeaves (fun (e : encPreTy.denote) =>
      match e with
      | .inl l => MuValBounded (n + 1) l.2
      | .inr c =>
          c.2.2.2.2.1.length ≤ n + 1 ∧
          c.2.2.2.2.2.1.length ≤ n ∧
          c.2.2.2.2.2.2.1.length ≤ n)
      ((hmEncPreIdC K a).eval env) := by
  unfold hmEncPreIdC
  refine letV_allLeaves_eq fun av hav => ?_
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st0 hst0 => ?_
  have hst0Eq : st0 = (a.eval env).2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst0
  refine caseOptV_allLeaves ?_ fun _ => ?_
  · refine bindV_allLeaves
      (hmKeyIdC_leaves K _ _ (n := n)
        (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using hMu.keys_le))
      fun kr ⟨hKrK, hKrC, hKrP⟩ => ?_
    have hKrC' : kr.2.2.1 = (a.eval env).2.2.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using hKrC
    have hKrP' : kr.2.2.2.1 = (a.eval env).2.2.2.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hst0Eq] using hKrP
    iterate 2 refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun st hst => ?_
    have hstEq : st = kr.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hst
    refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves_eq fun cv hcv => ?_
    have hcSt : cv.2.2.2.2 = kr.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using
        congrArg (fun x => x.2.2.2.2) hcv
    refine ite_allLeaves ?_ (ite_allLeaves ?_ ?_)
    · refine bindV_allLeaves_const fun _ => ?_
      refine bindV_allLeaves
        (encPostC_leaves K _ _ (n := n)
          (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcSt] using hKrK)
          (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcSt, hKrC'] using hMu.chal_le)
          (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcSt, hKrP'] using hMu.pend_le))
        fun res hRes => ?_
      refine ret_allLeaves ?_
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRes
    · refine ret_allLeaves ?_
      dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_zero, hcSt, hKrC', hKrP']
      exact ⟨hKrK, hMu.chal_le, hMu.pend_le⟩
    · refine ret_allLeaves ?_
      dsimp only [muMk, muKeys, muChal, muPend, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        List.length_cons]
      simp only [env_get_succ, env_get_zero, hstEq, hKrC', hKrP']
      exact ⟨hKrK, Nat.succ_le_succ hMu.chal_le, Nat.le_trans hMu.pend_le (Nat.le_succ n)⟩
  · refine ret_allLeaves ?_
    dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hst0Eq]
    exact hMu.mono (Nat.le_succ n)

private theorem finishIntC_leaves {n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ intFinArgsTy)
    (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (a.eval env).1)
    (hRo : CacheStepAtMostOne (valRoCache (a.eval env).1.1.1) (valIpRoC (a.eval env).2.2.2.2.1))
    (hRoot : CacheStepAtMostOne (valRootRoCache (a.eval env).1.1.1) (valIpRootC (a.eval env).2.2.2.2.1)) :
    AllLeaves (fun r => FixedStepPost n (a.eval env).1 r.2) ((finishIntC a).eval env) := by
  unfold finishIntC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves_eq fun fhst hfhst => ?_
  have hfhstEq : fhst = (a.eval env).1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hfhst
  iterate 3 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun pv hpv => ?_
  have hpvEq : pv = (a.eval env).2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hpv
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun hst hhst => ?_
  have hhstEq : hst = (a.eval env).1.1 := by
    simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstEq] using hhst
  refine letV_allLeaves_eq fun st hst0 => ?_
  have hstEq : st = (a.eval env).1.1.1 := by
    simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hst0
  iterate 12 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun roC hroC => ?_
  refine letV_allLeaves_eq fun rootC hrootC => ?_
  have hroCEq : roC = valIpRoC (a.eval env).2.2.2.2.1 := by
    simpa [ipRoC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.ipT3, valIpRoC, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpvEq] using hroC
  have hrootCEq : rootC = valIpRootC (a.eval env).2.2.2.2.1 := by
    simpa [ipRootC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.ipT3, valIpRootC, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpvEq] using hrootC
  iterate 14 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun idealS' hideal => ?_
  have hidealLen : idealS'.length ≤ n + 1 := by
    dsimp only [ahsIdealSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hideal
    simp only [env_get_succ, env_get_zero, hhstEq] at hideal
    subst hideal
    split_ifs
    · dsimp only [List.length_cons]; have := hb.idealSessions_le; omega
    · exact Nat.le_trans hb.idealSessions_le (Nat.le_succ n)
  refine letV_allLeaves_eq fun hst' hhst' => ?_
  refine letV_allLeaves fun _ => ?_
  refine ret_allLeaves ?_
  dsimp only [ahsfUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSlots,
    ahsfRecvCount, ahsfMkSaltCache, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfSlots,
    v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, hhst', hfhstEq]
  dsimp only [ahsUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsMk,
    stUpd, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stMk,
    ahsBase, asSessions, asUsedSendSessions, ahsInitKemRecs,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asPrincipals,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSpkBundles,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asOpkEntries,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvOPK,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvNoOPK,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedKyberTriples,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentNoOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdNoOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asAdvKeys,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSecb,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asHasWonAuth,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
    valRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, hhstEq, hstEq, hroCEq, hrootCEq]
  have hb1 := hb.base_le.mono (Nat.le_succ n)
  exact ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le,
    by simpa only [List.length_cons] using Nat.succ_le_succ hb.base_le.sessions_le,
    by simpa only [List.length_cons] using Nat.succ_le_succ hb.base_le.usedSendSessions_le,
    hb1.usedRecvOPK_le, hb1.usedRecvNoOPK_le, hb1.seenKyberBaseKeys_le,
    hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
    hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
    by simpa only [List.length_cons] using Nat.succ_le_succ hb.initKemRecs_le,
    Nat.le_trans hb.recvKemRecs_le (Nat.le_succ n),
    hidealLen,
    Nat.le_trans hb.mkSaltCache_le (Nat.le_succ n)⟩, hRo, hRoot⟩

private theorem hmPostC_fuel_eq {K₁ K₂ : ℕ} {Δ : List PT}
    {a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32))}
    {env : Env Δ}
    (h₁ : (a.eval env).1.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ K₁)
    (h₂ : (a.eval env).1.2.2.2.2.2.2.2.2.2.2.2.1.length ≤ K₂) :
    (hmPostC K₁ a).eval env = (hmPostC K₂ a).eval env := by
  unfold hmPostC
  refine letV_congr_eq rfl fun av hav => ?_
  refine letV_congr_eq rfl fun cv hcv => ?_
  iterate 6 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun encv hencv => ?_
  have hencEq : encv = (a.eval env).1.2.2.2.2.2 := by
    have hcEq : cv = (a.eval env).1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcv
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] using hencv
  refine bindV_congr (encPostC_fuel_eq rfl ?_ ?_) fun _ => rfl
  · simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hencEq] using h₁
  · simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hencEq] using h₂

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem hmPostC_eval_ren2 (K : ℕ) {Δ : List PT}
    (tag : (B 32).denote) (cont : hmSendContTy.denote) (env : Env Δ) :
    (hmPostC K (Δ := B 32 :: hmSendContTy :: Δ) (.pair (.var (.succ .zero)) (.var .zero))).eval
      (.cons tag (.cons cont env)) =
    (hmPostC K (Δ := [B 32, hmSendContTy]) (.pair (.var (.succ .zero)) (.var .zero))).eval
      (.cons tag (.cons cont .nil)) :=
  eval_ren2_eq
    (hmPostC K (Δ := [B 32, hmSendContTy]) (.pair (.var (.succ .zero)) (.var .zero)))
    (vA := .zero) (vB := .succ .zero) rfl rfl rfl

set_option maxHeartbeats 800000 in
private theorem hmPostC_leaves (K : ℕ) {n : ℕ} {fhst0 : authHybridStateFixedTy.denote}
    {Δ : List PT} (a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32)))
    (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n fhst0)
    (hCont : HmPreLeafInv n fhst0 (.inr (a.eval env).1)) :
    AllLeaves (fun res => FixedStepPost n fhst0 res.1.2 ∧ MuValBounded (n + 1) res.2)
      ((hmPostC K a).eval env) := by
  obtain ⟨hFhst, hRo, hRoot, hK, hC, hP⟩ := hCont
  unfold hmPostC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves_eq fun cv hcv => ?_
  have hcEq : cv = (a.eval env).1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcv
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun pv hpv => ?_
  refine letV_allLeaves_eq fun fhstv hfhstv => ?_
  refine letV_allLeaves_eq fun encv hencv => ?_
  have hpvEq : pv = (a.eval env).1.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] using hpv
  have hfhstvEq : fhstv = fhst0 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq, hFhst] using hfhstv
  have hencEq : encv = (a.eval env).1.2.2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcEq] using hencv
  refine bindV_allLeaves
    (encPostC_leaves K _ _ (n := n)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hencEq] using hK)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hencEq] using hC)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hencEq] using hP))
    fun ep hEp => ?_
  refine bindV_allLeaves
    (finishIntC_leaves _ _ (n := n)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstvEq] using hb)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstvEq, hpvEq] using hRo)
      (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstvEq, hpvEq] using hRoot))
    fun r hR => ?_
  have hR' : FixedStepPost n fhst0 r.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hfhstvEq] using hR
  refine ret_allLeaves ?_
  dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero]
  exact ⟨hR', hEp⟩

private theorem intSendPrepKC_fuel_eq (S : Setup) {K_on K_ro K n nRo nRoot : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁_ext.wk fhst)))
    (hRoB : (valRoCache (env.get (h₁_ext.wk fhst)).1.1).length ≤ nRo)
    (hRootB : (valRootRoCache (env.get (h₁_ext.wk fhst)).1.1).length ≤ nRoot)
    (hOn₁ : n ≤ K_on) (hOn₂ : n ≤ K)
    (hRo₁ : nRo ≤ K_ro) (hRo₂ : nRo ≤ K)
    (hRoot₁ : nRoot ≤ K_ro) (hRoot₂ : nRoot ≤ K) :
    (intSendPrepKC S K_on K_ro opk fhst x).eval env =
      (intSendPrepC S K opk fhst x).eval env := by
  unfold intSendPrepKC intSendPrepC
  refine letV_congr_eq rfl fun hst hhst => ?_
  refine letV_congr_eq rfl fun st hstEq0 => ?_
  have hstEq : st = (env.get (h₁_ext.wk fhst)).1.1 := by
    have hhstEq : hst = (env.get (h₁_ext.wk fhst)).1 := by
      simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhst
    simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hstEq0
  have hbSt : AuthBaseValOnlineBounded n st := hstEq ▸ hb.base_le
  iterate 4 refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine ite_congr_eval ?_ rfl ?_
  · simp only [eAny, asUsedSendSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero,
      take_eq_of_le (Nat.le_trans hbSt.usedSendSessions_le hOn₁)
        (Nat.le_trans hbSt.usedSendSessions_le hOn₂)]
  refine caseOptV_congr ?_ rfl fun _ => ?_
  · simp only [eFind, asPrincipals, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero,
      take_eq_of_le (Nat.le_trans hbSt.principals_le hOn₁)
        (Nat.le_trans hbSt.principals_le hOn₂)]
  refine letV_congr rfl fun _ => ?_
  refine bindV_congr (findHonestC_prf_fuel_eq S _ _ _
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hOn₁ hOn₂) fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine letV_congr rfl fun _ => ?_
  refine bindV_congr (koskBundleOkC_fuel_eq S _ _ _
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hOn₁ hOn₂) fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  iterate 4 refine bindV_congr rfl fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  iterate 2 refine bindV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine bindV_congr rfl fun _ => ?_
  refine caseOptV_congr rfl rfl fun _ => ?_
  iterate 2 refine letV_congr rfl fun _ => ?_
  refine bindV_congr rfl fun _ => ?_
  refine bindV_congr (checkBundleProvenanceExactC_fuel_eq S _ _ _
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hOn₁ hOn₂) fun _ => ?_
  refine bindV_congr (spkHonIdealFromPeerC_fuel_eq S _ _ _ _
    (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) hOn₁ hOn₂) fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  iterate 4 refine bindV_congr rfl fun _ => ?_
  iterate 2 refine letV_congr rfl fun _ => ?_
  iterate 2 refine bindV_congr rfl fun _ => ?_
  refine bindV_congr (ite_congr_eval rfl rfl
    (hkdfRoC_fuel_eq _ _ _
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hRoB) hRo₁ hRo₂))
    fun _ => ?_
  iterate 2 refine letV_congr rfl fun _ => ?_
  refine bindV_congr (ite_congr_eval rfl rfl
    (rootRoC_fuel_eq _ _ _ _
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hRootB) hRoot₁ hRoot₂))
    fun _ => rfl

private theorem intSendPrepC_leaves (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (env : Env Δ)
    (hRoK : (valRoCache (env.get (h₁_ext.wk fhst)).1.1).length ≤ K)
    (hRootK : (valRootRoCache (env.get (h₁_ext.wk fhst)).1.1).length ≤ K) :
    let fhst0 := env.get (h₁_ext.wk fhst)
    AllLeaves (fun (p? : Option intPrepTy.denote) =>
      match p? with
      | none => True
      | some p =>
          CacheStepAtMostOne (valRoCache fhst0.1.1) (valIpRoC p) ∧
          CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valIpRootC p))
      ((intSendPrepC S K opk fhst x).eval env) := by
  intro fhst0
  unfold intSendPrepC
  refine letV_allLeaves_eq fun hst hhst => ?_
  refine letV_allLeaves_eq fun st hstEq0 => ?_
  have hstEq : st = fhst0.1.1 := by
    have hhstEq : hst = fhst0.1 := by
      simpa [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, fhst0] using hhst
    simpa [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq] using hstEq0
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves (ret_allLeaves trivial) ?_
  refine ite_allLeaves (ret_allLeaves trivial) ?_
  refine caseOptV_allLeaves (ret_allLeaves trivial) fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves (ret_allLeaves trivial) ?_
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (ret_allLeaves trivial) ?_
  iterate 4 refine bindV_allLeaves_const fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  iterate 2 refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (ret_allLeaves trivial) ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine caseOptV_allLeaves (ret_allLeaves trivial) fun _ => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  iterate 3 refine bindV_allLeaves_const fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  iterate 4 refine bindV_allLeaves_const fun _ => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  iterate 2 refine bindV_allLeaves_const fun _ => ?_
  refine bindV_allLeaves
    (ite_allLeaves (P := fun (drOut : _ × _) => CacheStepAtMostOne (valRoCache fhst0.1.1) drOut.2)
      (bindV_allLeaves_const fun _ => ret_allLeaves
        (by simpa [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
              env_get_succ, env_get_zero, hstEq] using CacheStepAtMostOne.refl (valRoCache fhst0.1.1)))
      (AllLeaves_of_mem_support fun p hp => by
        have := hkdfRoC_step _ _ _
          (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hRoK) p hp
        simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using this))
    fun drOut hDrStep => ?_
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun roC' hroC' => ?_
  have hroCStep : CacheStepAtMostOne (valRoCache fhst0.1.1) roC' := by
    have : roC' = drOut.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hroC'
    rwa [this]
  refine bindV_allLeaves
    (ite_allLeaves (P := fun (rkOut : _ × _) => CacheStepAtMostOne (valRootRoCache fhst0.1.1) rkOut.2)
      (bindV_allLeaves_const fun _ => bindV_allLeaves_const fun _ => ret_allLeaves
        (by simpa [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
              env_get_succ, env_get_zero, hstEq] using CacheStepAtMostOne.refl (valRootRoCache fhst0.1.1)))
      (AllLeaves_of_mem_support fun p hp => by
        have := rootRoC_step _ _ _ _
          (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hRootK) p hp
        simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using this))
    fun rkOut hRkStep => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun rootC' hrootC' => ?_
  have hrootCStep : CacheStepAtMostOne (valRootRoCache fhst0.1.1) rootC' := by
    have : rootC' = rkOut.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hrootC'
    rwa [this]
  refine bindV_allLeaves_const fun _ => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine caseOptV_allLeaves (ret_allLeaves trivial) fun _ => ?_
  iterate 3 refine letV_allLeaves fun _ => ?_
  refine ret_allLeaves ?_
  simp only [valIpRoC, valIpRootC, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
  exact ⟨hroCStep, hrootCStep⟩

private theorem hmSendKC_fuel_eq (S : Setup) {K_on K_ro K n nRo nRoot : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ] [h₃_ext : Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₂_ext.wk fhst)))
    (hRoB : (valRoCache (env.get (h₂_ext.wk fhst)).1.1).length ≤ nRo)
    (hRootB : (valRootRoCache (env.get (h₂_ext.wk fhst)).1.1).length ≤ nRoot)
    (hMu : MuValBounded n (env.get (h₃_ext.wk mst)))
    (hOn₁ : n ≤ K_on) (hOn₂ : n ≤ K)
    (hRo₁ : nRo ≤ K_ro) (hRo₂ : nRo ≤ K)
    (hRoot₁ : nRoot ≤ K_ro) (hRoot₂ : nRoot ≤ K) :
    (hmSendKC S K_on K_ro opk jt fhst mst x).eval env =
      (hmSendC S K opk jt fhst mst x).eval env := by
  unfold hmSendKC hmSendC
  refine ite_congr_eval rfl rfl ?_
  refine bindV_congr
    (intSendPrepKC_fuel_eq S opk fhst x env hb hRoB hRootB hOn₁ hOn₂ hRo₁ hRo₂ hRoot₁ hRoot₂)
    fun _ => ?_
  refine caseOptV_congr rfl rfl fun _ => ?_
  unfold hmSendTailC
  iterate 5 refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl ?_ rfl
  refine bindV_congr (hmEncPreIdC_fuel_eq rfl ?_ hOn₁ hOn₂) fun _ => rfl
  simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hMu

private theorem hmSendC_leaves (S : Setup) (K : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ] [h₃_ext : Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₂_ext.wk fhst)))
    (hRoK : (valRoCache (env.get (h₂_ext.wk fhst)).1.1).length ≤ K)
    (hRootK : (valRootRoCache (env.get (h₂_ext.wk fhst)).1.1).length ≤ K)
    (hMu : MuValBounded n (env.get (h₃_ext.wk mst))) :
    AllLeaves (HmPreLeafInv n (env.get (h₂_ext.wk fhst)))
      ((hmSendC S K opk jt fhst mst x).eval env) := by
  set fhst0 := env.get (h₂_ext.wk fhst)
  have hSelfPost : FixedStepPost n fhst0 fhst0 :=
    ⟨hb.mono (Nat.le_succ n), CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _⟩
  have hMu1 : MuValBounded (n + 1) (env.get (h₃_ext.wk mst)) := hMu.mono (Nat.le_succ n)
  unfold hmSendC
  refine ite_allLeaves ?_ ?_
  · refine ret_allLeaves ?_
    dsimp only [HmPreLeafInv, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    exact ⟨hSelfPost, hMu1⟩
  · refine bindV_allLeaves (intSendPrepC_leaves S K opk fhst x env hRoK hRootK) fun p? hp? => ?_
    refine caseOptV_allLeaves_eq ?_ fun p hpEq => ?_
    · refine ret_allLeaves ?_
      dsimp only [HmPreLeafInv, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_succ]
      exact ⟨hSelfPost, hMu1⟩
    · have hpVal : p? = some p := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hpEq
      rw [hpVal] at hp?
      rcases hp? with ⟨hpRo, hpRoot⟩
      unfold hmSendTailC
      iterate 5 refine letV_allLeaves fun _ => ?_
      refine ite_allLeaves ?_ ?_
      · refine bindV_allLeaves
          (hmEncPreIdC_leaves K _ _ (n := n)
            (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hMu))
          fun e he => ?_
        refine caseSumV_allLeaves_eq (fun l hl => ?_) (fun cont hcont => ?_)
        · have heVal : e = .inl l := by
            simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hl
          rw [heVal] at he
          refine bindV_allLeaves
            (finishIntC_leaves _ _ (n := n)
              (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hb)
              (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hpRo)
              (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hpRoot))
            fun r hr => ?_
          have hr' : FixedStepPost n fhst0 r.2 := by
            simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, fhst0] using hr
          refine ret_allLeaves ?_
          simp only [HmPreLeafInv, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
          exact ⟨hr', he⟩
        · have heVal : e = .inr cont := by
            simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hcont
          rw [heVal] at he
          refine ret_allLeaves ?_
          dsimp only [HmPreLeafInv, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
          simp only [env_get_succ, env_get_zero]
          exact ⟨rfl, hpRo, hpRoot, he.1, he.2.1, he.2.2⟩
      · iterate 2 refine bindV_allLeaves_const fun _ => ?_
        refine bindV_allLeaves
          (finishIntC_leaves _ _ (n := n)
            (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hb)
            (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hpRo)
            (by simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hpRoot))
          fun r hr => ?_
        have hr' : FixedStepPost n fhst0 r.2 := by
          simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, fhst0] using hr
        refine ret_allLeaves ?_
        simp only [HmPreLeafInv, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
        exact ⟨hr', hMu1⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem hmSendC_eval_ren4 (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
    (env : Env Δ) :
    (hmSendC S K opk jt fhst mst x).eval env =
      (hmSendC S K opk
        (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, sendQTy])
        (Γ₂ := [authHybridStateFixedTy, muStTy, sendQTy])
        (Γ₃ := [muStTy, sendQTy])
        (Γ₄ := [sendQTy])
        (Δ := [.nat, authHybridStateFixedTy, muStTy, sendQTy]) .zero .zero .zero .zero).eval
        (.cons (env.get (h₁.wk jt)) (.cons (env.get (h₂.wk fhst))
          (.cons (env.get (h₃.wk mst)) (.cons (env.get (h₄.wk x)) .nil)))) := by
  have hren :
      compRename (ren4 (h₁.wk jt) (h₂.wk fhst) (h₃.wk mst) (h₄.wk x))
        (hmSendC S K opk
          (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, sendQTy])
          (Γ₂ := [authHybridStateFixedTy, muStTy, sendQTy])
          (Γ₃ := [muStTy, sendQTy])
          (Γ₄ := [sendQTy])
          (Δ := [.nat, authHybridStateFixedTy, muStTy, sendQTy]) .zero .zero .zero .zero) =
      hmSendC S K opk jt fhst mst x := by
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

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem hmRecvC_eval_ren4 (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
    (env : Env Δ) :
    (hmRecvC S K opk jt fhst mst x).eval env =
      (hmRecvC S K opk
        (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
        (Γ₂ := [authHybridStateFixedTy, muStTy, recvQTy])
        (Γ₃ := [muStTy, recvQTy])
        (Γ₄ := [recvQTy])
        (Δ := [.nat, authHybridStateFixedTy, muStTy, recvQTy]) .zero .zero .zero .zero).eval
        (.cons (env.get (h₁.wk jt)) (.cons (env.get (h₂.wk fhst))
          (.cons (env.get (h₃.wk mst)) (.cons (env.get (h₄.wk x)) .nil)))) := by
  have hren :
      compRename (ren4 (h₁.wk jt) (h₂.wk fhst) (h₃.wk mst) (h₄.wk x))
        (hmRecvC S K opk
          (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
          (Γ₂ := [authHybridStateFixedTy, muStTy, recvQTy])
          (Γ₃ := [muStTy, recvQTy])
          (Γ₄ := [recvQTy])
          (Δ := [.nat, authHybridStateFixedTy, muStTy, recvQTy]) .zero .zero .zero .zero) =
      hmRecvC S K opk jt fhst mst x := by
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

set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
private theorem hmOnlineArm_sim (S : Setup) (b : QueryBudget) {arg : PT}
    (stepKC stepOldC : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
      [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ],
      Var Γ₁ .nat → Var Γ₂ authHybridStateFixedTy → Var Γ₃ muStTy → Var Γ₄ arg →
      Comp pqxdhOps pqPrimIface Δ hmPreTy)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (t : AuthQuery S)
    {xAtom : (embedTy arg).denote}
    (hOn : authSimPred S 0 t)
    (hPreOld : (hmPre1KeyC S b.q_total).eval
        (.cons (projVal hmStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
      (stepOldC (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, arg])
        (Γ₂ := [authHybridStateFixedTy, muStTy, arg])
        (Γ₃ := [muStTy, arg]) (Γ₄ := [arg])
        (Δ := [.nat, authHybridStateFixedTy, muStTy, arg]) .zero .zero .zero .zero).eval
        (.cons s'.1.1 (.cons (projVal authHybridStateFixedTy s'.1.2.1)
          (.cons (projVal muStTy s'.1.2.2) (.cons (projVal arg xAtom) .nil)))))
    (hEvalKC : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
      [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ]
      (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
      (mst : Var Γ₃ muStTy) (x : Var Γ₄ arg) (env5 : Env Δ),
      env5.get (h₁.wk jt) = s'.1.1 →
      env5.get (h₂.wk fhst) = projVal authHybridStateFixedTy s'.1.2.1 →
      env5.get (h₃.wk mst) = projVal muStTy s'.1.2.2 →
      env5.get (h₄.wk x) = projVal arg xAtom →
      (stepKC jt fhst mst x).eval env5 =
        (stepOldC (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, arg])
          (Γ₂ := [authHybridStateFixedTy, muStTy, arg])
          (Γ₃ := [muStTy, arg]) (Γ₄ := [arg])
          (Δ := [.nat, authHybridStateFixedTy, muStTy, arg]) .zero .zero .zero .zero).eval
          (.cons s'.1.1 (.cons (projVal authHybridStateFixedTy s'.1.2.1)
            (.cons (projVal muStTy s'.1.2.2) (.cons (projVal arg xAtom) .nil)))))
    (hLeaves :
      AllLeaves (HmPreLeafInv (c 0) (projVal authHybridStateFixedTy s'.1.2.1))
        ((stepOldC (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, arg])
          (Γ₂ := [authHybridStateFixedTy, muStTy, arg])
          (Γ₃ := [muStTy, arg]) (Γ₄ := [arg])
          (Δ := [.nat, authHybridStateFixedTy, muStTy, arg]) .zero .zero .zero .zero).eval
          (.cons s'.1.1 (.cons (projVal authHybridStateFixedTy s'.1.2.1)
            (.cons (projVal muStTy s'.1.2.2) (.cons (projVal arg xAtom) .nil))))))
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let ρ := Env.cons xAtom (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm : Comp pqAtomicOps pqPrfHmacIface
        [embedTy arg, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
      .bind (liftPrfHmac1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun jt =>
           letV (.fst (.snd (v s))) fun fhst =>
           letV (.snd (.snd (v s))) fun mst =>
           bindV (liftPrimComp (stepKC jt fhst mst x)) fun _pre =>
           hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
    Prod.map id forgetHm <$> arm.eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F ρ arm
  have ⟨hnOn, hRoStepB, hRootStepB, hKroCap⟩ :=
    AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
  have hKonQ : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  set fhst0 := projVal authHybridStateFixedTy s'.1.2.1
  have hFhst0Emb : embedVal authHybridStateFixedTy fhst0 = s'.1.2.1 :=
    embedVal_projVal authHybridStateFixedTy s'.1.2.1
  have hb0 : AuthFixedValOnlineBounded (c 0) fhst0 := by
    rw [← AuthFixedAtomOnlineBounded.iff_embedVal, hFhst0Emb]
    exact hInv.shadow_ok.fixed_ok.online_le
  let innerK : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface
      [.prod hmStTy arg] (.prod authRespTy hmStTy) :=
    letV (.fst (.var .zero)) fun s =>
    letV (.snd (.var (.succ .zero))) fun x =>
    letV (.fst (v s)) fun jt =>
    letV (.fst (.snd (v s))) fun fhst =>
    letV (.snd (.snd (v s))) fun mst =>
    bindV (liftPrimComp (stepKC jt fhst mst x)) fun _pre =>
    hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero
  have hInnerEq :
      innerK.eval (.cons (projVal hmStTy s'.1, projVal arg xAtom) .nil) =
        (hmHandle1KeyC S b.q_total).eval
          (.cons (projVal hmStTy s'.1)
            (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) ∧
      ∀ z ∈ support (innerK.eval (.cons (projVal hmStTy s'.1, projVal arg xAtom) .nil)),
        FixedStepPost (c 0) fhst0 z.2.2.1 ∧ MuValBounded (c 0 + 1) z.2.2.2 := by
    dsimp only [innerK, hmHandle1KeyC, letV]
    rw [eval_letC, eval_letC, eval_letC, eval_letC, eval_letC]
    dsimp only [bindV, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, projVal_hmSt_1, projVal_hmSt_21, projVal_hmSt_22]
    have hStepEq := (hEvalKC
      (Γ₁ := [.nat, arg, hmStTy, .prod hmStTy arg])
      (Γ₂ := [authHybridStateFixedTy, .nat, arg, hmStTy, .prod hmStTy arg])
      (Γ₃ := [muStTy, authHybridStateFixedTy, .nat, arg, hmStTy, .prod hmStTy arg])
      (Γ₄ := [arg, hmStTy, .prod hmStTy arg])
      (Δ := [muStTy, authHybridStateFixedTy, .nat, arg, hmStTy, .prod hmStTy arg])
      .zero .zero .zero .zero
      (.cons (projVal muStTy s'.1.2.2)
        (.cons (projVal authHybridStateFixedTy s'.1.2.1)
          (.cons s'.1.1
            (.cons (projVal arg xAtom)
              (.cons (projVal hmStTy s'.1)
                (.cons (projVal hmStTy s'.1, projVal arg xAtom) .nil))))))
      rfl rfl rfl rfl).trans hPreOld.symm
    rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval, hStepEq,
      ← _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval]
    have hPreSupp : ∀ pre ∈ support ((liftPrimComp (C := hmacPrfOracle) (hmPre1KeyC S b.q_total)).eval
          (.cons (projVal hmStTy s'.1)
            (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil))),
        HmPreLeafInv (c 0) fhst0 pre := by
      intro pre hpre
      obtain ⟨pre0, hpre0, rfl⟩ := mem_support_liftPrimComp _ _ pre hpre
      rw [hPreOld] at hpre0
      exact AllLeaves_mem_support hLeaves hpre0
    refine ⟨?_, ?_⟩
    · refine OracleComp.bind_congr_of_forall_mem_support _ fun pre hpre => ?_
      have hInvPre := hPreSupp pre hpre
      rw [eval_letC]
      cases pre with
      | inl r =>
        dsimp only [hmPostRunC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero, projVal_hmSt_1]
      | inr cont =>
        dsimp only [hmPostRunC, caseSumV, bindV, hmContX0E, queryHmacEval, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero, projVal_hmSt_1]
        refine congrArg _ (funext fun tag => ?_)
        refine bind_const_congr ?_
        exact (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval _ _).trans
          ((congrArg _ ((hmPostC_eval_ren2 F.K_on tag cont _).trans
            ((hmPostC_fuel_eq
                (by simpa only [Expr.eval, Env.get] using Nat.le_trans hInvPre.2.2.2.2.2 (Nat.le_trans (Nat.le_succ _) hnOn))
                (by simpa only [Expr.eval, Env.get] using Nat.le_trans hInvPre.2.2.2.2.2 (Nat.le_trans (Nat.le_succ _) (Nat.le_trans hnOn hKonQ)))).trans
              (hmPostC_eval_ren2 b.q_total tag cont _).symm))).trans
            (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.liftPrimComp_prfHmac_eval _ _).symm)
    · intro z hz
      erw [mem_support_bind_iff] at hz
      rcases hz with ⟨pre, hpre, hz⟩
      have hInvPre := hPreSupp pre hpre
      cases pre with
      | inl r =>
        dsimp only [hmPostRunC, caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk] at hz
        simp only [env_get_succ, env_get_zero, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hInvPre
      | inr cont =>
        dsimp only [hmPostRunC, caseSumV, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk] at hz
        erw [mem_support_bind_iff] at hz
        rcases hz with ⟨tag, _, hz⟩
        erw [mem_support_bind_iff] at hz
        rcases hz with ⟨res, hres, hz⟩
        simp only [env_get_succ, env_get_zero, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨res0, hres0, rfl⟩ := mem_support_liftPrimComp _ _ res hres
        refine AllLeaves_mem_support (hmPostC_leaves F.K_on _ _ hb0 ?_) hres0
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hInvPre
  have hLiftEval :
      (liftPrfHmac1 innerK (.pair (.fst .v1) .v0)).eval ρ =
        embedVal (.prod authRespTy hmStTy) <$>
          innerK.eval (.cons (projVal hmStTy s'.1, projVal arg xAtom) .nil) := by
    rw [liftPrfHmac1_eval]
    simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, ρ]
    rw [projVal_pair]
  have hSyncEach :
      ∀ y ∈ support ((liftPrfHmac1 innerK (.pair (.fst .v1) .v0)).eval ρ),
        ∃ avls' : roBothAvlTy.denote,
          (syncRoBothC (I := pqPrfHmacIface) F.K_cap
              (fixedRoCacheE (.fst (.snd (.snd .v0))))
              (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
              (.snd .v2)).eval (.cons y ρ) = pure avls' ∧
          AuthHmShadowAt S b (c 0 + 1) (c 0 + 1 + c 1) (c 0 + 1 + c 2) (y.2, avls') := by
    intro y hy
    rw [hLiftEval] at hy
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_support_map_peel _ _ hy
    obtain ⟨⟨hFixed1, hRoS, hRootS⟩, hMu1⟩ := hInnerEq.2 z hz
    have hPreSt : s'.1.2.1.1.1 = embedVal authStateTy fhst0.1.1 := by
      rw [← hFhst0Emb]; rfl
    have hPostSt : (embedVal (.prod authRespTy hmStTy) z).2.2.1.1.1 = embedVal authStateTy z.2.2.1.1.1 := rfl
    have hRoS' : CacheStepAtMostOne (atomRoCache s'.1.2.1.1.1)
        (atomRoCache (embedVal (.prod authRespTy hmStTy) z).2.2.1.1.1) := by
      rw [hPreSt, hPostSt, atomRoCache_embedVal, atomRoCache_embedVal]; exact hRoS
    have hRootS' : CacheStepAtMostOne (atomRootRoCache s'.1.2.1.1.1)
        (atomRootRoCache (embedVal (.prod authRespTy hmStTy) z).2.2.1.1.1) := by
      rw [hPreSt, hPostSt, atomRootRoCache_embedVal, atomRootRoCache_embedVal]; exact hRootS
    have hRoLen1 : (atomRoCache (embedVal (.prod authRespTy hmStTy) z).2.2.1.1.1).length ≤ c 0 + 1 + c 1 := by
      have h0 := hInv.shadow_ok.fixed_ok.ro_len_le
      dsimp only [hmShadowFixed] at h0
      have h1 := hRoS'.length_le
      omega
    have hRootLen1 : (atomRootRoCache (embedVal (.prod authRespTy hmStTy) z).2.2.1.1.1).length ≤ c 0 + 1 + c 2 := by
      have h0 := hInv.shadow_ok.fixed_ok.root_len_le
      dsimp only [hmShadowFixed] at h0
      have h1 := hRootS'.length_le
      omega
    obtain ⟨avls', hSyncEv, hRel'⟩ :=
      syncRoBothC_sim (I := pqPrfHmacIface) F.K_cap
        s'.1.2.1.1.1 (embedVal (.prod authRespTy hmStTy) z).2.2.1.1.1 s'.2
        (fixedRoCacheE (.fst (.snd (.snd .v0))))
        (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
        (.snd .v2)
        (.cons (embedVal (.prod authRespTy hmStTy) z) ρ)
        hInv.shadow_ok.fixed_ok.ro_shadow hRoS' hRootS'
        (Nat.le_trans hRoLen1 (Nat.le_trans hRoStepB hKroCap))
        (Nat.le_trans hRootLen1 (Nat.le_trans hRootStepB hKroCap))
        (fixedRoCacheE_eval _ _) (fixedRootRoCacheE_eval _ _) rfl
    refine ⟨avls', hSyncEv, ⟨⟨?_, hRoLen1, hRootLen1, hRel'⟩, ?_, ?_, ?_⟩⟩
    · change AuthFixedAtomOnlineBounded (c 0 + 1) (embedVal authHybridStateFixedTy z.2.2.1)
      exact (AuthFixedAtomOnlineBounded.iff_embedVal _).mpr hFixed1
    · simpa [embedVal] using hMu1.keys_le
    · simpa [embedVal] using hMu1.chal_le
    · simpa [embedVal] using hMu1.pend_le
  let retVal : (embedTy (.prod authRespTy hmStTy)).denote → roBothAvlTy.denote →
      ((authCodec S).R.prod ((embedTy hmStTy).prod roBothAvlTy)).denote :=
    fun y avls' => (y.1, (y.2, avls'))
  have hArmEval :
      arm.eval ρ =
        ((liftPrfHmac1 innerK (.pair (.fst .v1) .v0)).eval ρ >>= fun y =>
          (syncRoBothC (I := pqPrfHmacIface) F.K_cap
              (fixedRoCacheE (.fst (.snd (.snd .v0))))
              (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
              (.snd .v2)).eval (.cons y ρ) >>= fun avls' =>
            pure (retVal y avls')) := rfl
  refine ⟨?_, ?_⟩
  · rw [oldHandle_eval, ← hInnerEq.1, ← hLiftEval, hArmEval, map_bind]
    conv_rhs => rw [← bind_pure ((liftPrfHmac1 innerK (.pair (.fst .v1) .v0)).eval ρ)]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun y hy => ?_
    obtain ⟨avls', hSyncEv, _⟩ := hSyncEach y hy
    rw [hSyncEv, pure_bind, map_pure]
    rfl
  · rw [hArmEval]
    intro p hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨y, hy, hp⟩
    obtain ⟨avls', hSyncEv, hSh'⟩ := hSyncEach y hy
    rw [hSyncEv, pure_bind] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    dsimp only [retVal]
    have hBump := AuthCounterInv.bump t hInv.counter_inv hroom
    have hB0 : bumpPred (authSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, hOn]
    have hGe1 : c 1 ≤ bumpPred (authSimPred S) c t 1 := by dsimp only [bumpPred]; split_ifs <;> omega
    have hGe2 : c 2 ≤ bumpPred (authSimPred S) c t 2 := by dsimp only [bumpPred]; split_ifs <;> omega
    refine ⟨hBump, ⟨hSh'.fixed_ok.mono (by omega) (by omega) (by omega),
      Nat.le_trans hSh'.mu_keys_le (by omega),
      Nat.le_trans hSh'.mu_chal_le (by omega),
      Nat.le_trans hSh'.mu_pend_le (by omega)⟩⟩

private theorem hmSendArm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (t : AuthQuery S)
    {xAtom : authSendQAtomicTy.denote}
    (hOn : authSimPred S 0 t)
    (hPreOld : (hmPre1KeyC S b.q_total).eval
        (.cons (projVal hmStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
      (hmSendC S b.q_total opk
        (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, sendQTy])
        (Γ₂ := [authHybridStateFixedTy, muStTy, sendQTy])
        (Γ₃ := [muStTy, sendQTy])
        (Γ₄ := [sendQTy])
        (Δ := [.nat, authHybridStateFixedTy, muStTy, sendQTy]) .zero .zero .zero .zero).eval
        (.cons s'.1.1 (.cons (projVal authHybridStateFixedTy s'.1.2.1)
          (.cons (projVal muStTy s'.1.2.2) (.cons (projVal sendQTy xAtom) .nil)))))
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let ρ := Env.cons xAtom (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm : Comp pqAtomicOps pqPrfHmacIface
        [authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
      .bind (liftPrfHmac1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun jt =>
           letV (.fst (.snd (v s))) fun fhst =>
           letV (.snd (.snd (v s))) fun mst =>
           bindV (liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
           hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
    Prod.map id forgetHm <$> arm.eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F ρ arm
  have ⟨hnOn, hRoStepB, hRootStepB, _⟩ :=
    AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
  have hKonQ : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hKroQ : F.K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  set fhst0 := projVal authHybridStateFixedTy s'.1.2.1
  have hFhst0Emb : embedVal authHybridStateFixedTy fhst0 = s'.1.2.1 :=
    embedVal_projVal authHybridStateFixedTy s'.1.2.1
  have hb0 : AuthFixedValOnlineBounded (c 0) fhst0 := by
    rw [← AuthFixedAtomOnlineBounded.iff_embedVal, hFhst0Emb]
    exact hInv.shadow_ok.fixed_ok.online_le
  have hRo0 : (valRoCache fhst0.1.1).length ≤ c 0 + c 1 := by
    have h := hInv.shadow_ok.fixed_ok.ro_len_le
    dsimp only [hmShadowFixed] at h
    rw [← hFhst0Emb] at h
    change (atomRoCache (embedVal authStateTy fhst0.1.1)).length ≤ c 0 + c 1 at h
    rwa [atomRoCache_embedVal] at h
  have hRoot0 : (valRootRoCache fhst0.1.1).length ≤ c 0 + c 2 := by
    have h := hInv.shadow_ok.fixed_ok.root_len_le
    dsimp only [hmShadowFixed] at h
    rw [← hFhst0Emb] at h
    change (atomRootRoCache (embedVal authStateTy fhst0.1.1)).length ≤ c 0 + c 2 at h
    rwa [atomRootRoCache_embedVal] at h
  have hMu0 : MuValBounded (c 0) (projVal muStTy s'.1.2.2) :=
    ⟨by simpa [projVal] using hInv.shadow_ok.mu_keys_le,
     by simpa [projVal] using hInv.shadow_ok.mu_chal_le,
     by simpa [projVal] using hInv.shadow_ok.mu_pend_le⟩
  exact hmOnlineArm_sim S b (arg := sendQTy)
    (fun jt fhst mst x => hmSendKC S F.K_on F.K_ro opk jt fhst mst x)
    (fun jt fhst mst x => hmSendC S b.q_total opk jt fhst mst x)
    c s' t hOn hPreOld
    (fun jt fhst mst x env5 hJ hF hM hX => by
      rw [hmSendKC_fuel_eq S opk jt fhst mst x env5
        (hF ▸ hb0) (hF ▸ hRo0) (hF ▸ hRoot0) (hM ▸ hMu0)
        (Nat.le_trans (Nat.le_succ _) hnOn)
        (Nat.le_trans (Nat.le_succ _) (Nat.le_trans hnOn hKonQ))
        (Nat.le_trans (by omega : c 0 + c 1 ≤ c 0 + 1 + c 1) hRoStepB)
        (Nat.le_trans (by omega : c 0 + c 1 ≤ c 0 + 1 + c 1) (Nat.le_trans hRoStepB hKroQ))
        (Nat.le_trans (by omega : c 0 + c 2 ≤ c 0 + 1 + c 2) hRootStepB)
        (Nat.le_trans (by omega : c 0 + c 2 ≤ c 0 + 1 + c 2) (Nat.le_trans hRootStepB hKroQ)),
        hmSendC_eval_ren4, hJ, hF, hM, hX])
    (hmSendC_leaves S b.q_total opk .zero .zero .zero .zero _
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hb0)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
        Nat.le_trans hRo0 (Nat.le_trans (by omega : c 0 + c 1 ≤ c 0 + 1 + c 1) (Nat.le_trans hRoStepB hKroQ)))
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
        Nat.le_trans hRoot0 (Nat.le_trans (by omega : c 0 + c 2 ≤ c 0 + 1 + c 2) (Nat.le_trans hRootStepB hKroQ)))
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hMu0))
    hroom hInv

private theorem hkdfRoC_allLeaves {K : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    {st0 : authStateTy.denote} (hst : env.get (h.wk st) = st0)
    (hRo : (valRoCache st0).length ≤ K) :
    AllLeaves (fun p => CacheStepAtMostOne (valRoCache st0) p.2)
      ((hkdfRoC K st sec).eval env) := by
  subst hst; exact AllLeaves_of_mem_support (hkdfRoC_step st sec env hRo)

private theorem rootRoC_allLeaves {K : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    {st0 : authStateTy.denote} (hst : env.get (h.wk st) = st0)
    (hRoot : (valRootRoCache st0).length ≤ K) :
    AllLeaves (fun p => CacheStepAtMostOne (valRootRoCache st0) p.2)
      ((rootRoC K st rk dh).eval env) := by
  subst hst; exact AllLeaves_of_mem_support (rootRoC_step st rk dh env hRoot)


private theorem MuValBounded.of_atom {n : ℕ} (mAtom : (embedTy muStTy).denote)
    (hk : mAtom.1.length ≤ n) (hc : mAtom.2.1.length ≤ n) (hp : mAtom.2.2.1.length ≤ n) :
    MuValBounded n (projVal muStTy mAtom) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [muStTy, projVal, List.length_map] using hk
  · simpa only [muStTy, projVal, List.length_map] using hc
  · simpa only [muStTy, projVal, List.length_map] using hp

private theorem MuValBounded.to_embed {n : ℕ} {mst : muStTy.denote} (hb : MuValBounded n mst) :
    (embedVal muStTy mst).1.length ≤ n ∧
    (embedVal muStTy mst).2.1.length ≤ n ∧
    (embedVal muStTy mst).2.2.1.length ≤ n := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [muStTy, embedVal, List.length_map] using hb.keys_le
  · simpa only [muStTy, embedVal, List.length_map] using hb.chal_le
  · simpa only [muStTy, embedVal, List.length_map] using hb.pend_le

private theorem hmRecv_hmKeyIdC_fuel_eq {K₁ K₂ n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) (env : Env Δ)
    (hb : MuValBounded n (a.eval env).2) (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (hmKeyIdC K₁ a).eval env = (hmKeyIdC K₂ a).eval env := by
  unfold hmKeyIdC
  refine letV_congr_eq rfl fun av hav => ?_
  refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun st hst => ?_
  have hstEq : st = (a.eval env).2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst
  refine caseOptV_congr ?_ rfl fun _ => rfl
  dsimp only [eFind, muKeys, v, Expr.eval, Ext.refl_wk]
  rw [env_get_zero, hstEq,
    take_eq_of_le (Nat.le_trans hb.keys_le h₁) (Nat.le_trans hb.keys_le h₂)]

private theorem hmRecv_hmKeyIdC_leaves (K : ℕ) {n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) (env : Env Δ)
    (hb : MuValBounded n (a.eval env).2) :
    AllLeaves (fun kr => kr.2.1.length ≤ n + 1 ∧ kr.2.2.1 = (a.eval env).2.2.1 ∧
      kr.2.2.2.1 = (a.eval env).2.2.2.1) ((hmKeyIdC K a).eval env) := by
  unfold hmKeyIdC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun st hst => ?_
  have hstEq : st = (a.eval env).2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst
  refine caseOptV_allLeaves ?_ fun _ => ?_
  · refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine ret_allLeaves ?_
    dsimp only [muMk, muKeys, muChal, muPend, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hstEq, List.length_cons]
    exact ⟨Nat.add_le_add_right hb.keys_le 1, trivial, trivial⟩
  · refine ret_allLeaves ?_
    dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hstEq]
    exact ⟨Nat.le_trans hb.keys_le (Nat.le_succ n), trivial, trivial⟩


private theorem hmRecv_hmForgeIdC_fuel_eq {K₁ K₂ n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ)
    (hb : MuValBounded n (a.eval env).2.2.2.2) (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (hmForgeIdC K₁ a).eval env = (hmForgeIdC K₂ a).eval env := by
  unfold hmForgeIdC
  refine letV_congr_eq rfl fun av hav => ?_
  refine letV_congr rfl fun jt => ?_
  refine letV_congr rfl fun i => ?_
  refine letV_congr rfl fun ad => ?_
  refine letV_congr rfl fun ct => ?_
  refine letV_congr_eq rfl fun st0 hst0 => ?_
  have hst0Eq : st0 = (a.eval env).2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst0
  have hb0 : MuValBounded n st0 := hst0Eq ▸ hb
  refine ite_congr_eval ?_ rfl ?_
  · dsimp only [eCaseOpt, eFind, muChal, v, Expr.eval, Ext.refl_wk]
    rw [env_get_zero, take_eq_of_le (Nat.le_trans hb0.chal_le h₁) (Nat.le_trans hb0.chal_le h₂)]
  · refine bindV_congr_leaves
      (hmRecv_hmKeyIdC_fuel_eq _ _ (by simpa [v, Expr.eval, Ext.refl_wk, env_get_zero] using hb0) h₁ h₂)
      (hmRecv_hmKeyIdC_leaves K₁ _ _ (by simpa [v, Expr.eval, Ext.refl_wk, env_get_zero] using hb0))
      fun kr hkr => ?_
    refine letV_congr rfl fun r => ?_
    refine letV_congr rfl fun mk => ?_
    refine letV_congr_eq rfl fun st hst => ?_
    refine letV_congr rfl fun x => ?_
    have hChalSt : st.2.1.length ≤ n := by
      have hstEq : st = kr.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hst
      have hkrChal : kr.2.2.1 = st0.2.1 := by
        simpa [v, Expr.eval, Ext.refl_wk, env_get_zero] using hkr.2.1
      rw [hstEq, hkrChal]
      exact hb0.chal_le
    refine letV_congr ?_ fun _ => rfl
    dsimp only [eCaseOpt, eFind, muChal, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    rw [env_get_succ, env_get_zero,
      take_eq_of_le (Nat.le_trans hChalSt h₁) (Nat.le_trans hChalSt h₂)]

private theorem hmRecv_hmForgeIdC_leaves (K : ℕ) {n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ)
    (hb : MuValBounded n (a.eval env).2.2.2.2) :
    AllLeaves (MuValBounded (n + 1)) ((hmForgeIdC K a).eval env) := by
  unfold hmForgeIdC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves fun jt => ?_
  refine letV_allLeaves fun i => ?_
  refine letV_allLeaves fun ad => ?_
  refine letV_allLeaves fun ct => ?_
  refine letV_allLeaves_eq fun st0 hst0 => ?_
  have hb0 : MuValBounded n st0 := by
    have hst0Eq : st0 = (a.eval env).2.2.2.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hst0
    exact hst0Eq ▸ hb
  refine ite_allLeaves ?_ ?_
  · refine ret_allLeaves ?_
    simpa [v, Expr.eval, Ext.refl_wk, env_get_zero] using hb0.mono (Nat.le_succ n)
  · apply bindV_allLeaves (hmRecv_hmKeyIdC_leaves K _ _
      (by simpa [v, Expr.eval, Ext.refl_wk, env_get_zero] using hb0))
    intro kr hkr
    refine letV_allLeaves fun r => ?_
    refine letV_allLeaves fun mk => ?_
    refine letV_allLeaves_eq fun st hst => ?_
    have hstEq : st = kr.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hst
    have hkr2 : kr.2.2.1 = st0.2.1 ∧ kr.2.2.2.1 = st0.2.2.1 := by
      simpa [v, Expr.eval, Ext.refl_wk, env_get_zero] using hkr.2
    have hbSt : st.1.length ≤ n + 1 ∧ st.2.1.length ≤ n ∧ st.2.2.1.length ≤ n := by
      rw [hstEq, hkr2.1, hkr2.2]
      exact ⟨hkr.1, hb0.chal_le, hb0.pend_le⟩
    refine letV_allLeaves fun x => ?_
    refine letV_allLeaves fun fresh => ?_
    refine ite_allLeaves ?_ ?_
    · refine ite_allLeaves ?_ ?_
      · refine ret_allLeaves ?_
        dsimp only [muMk, muKeys, muChal, muPend, muBad, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        rw [env_get_succ, env_get_succ, env_get_zero]
        exact ⟨hbSt.1, Nat.le_trans hbSt.2.1 (Nat.le_succ n), by
          simpa only [List.length_cons] using Nat.add_le_add_right hbSt.2.2 1⟩
      · refine bindV_allLeaves_const fun _ => ret_allLeaves ?_
        dsimp only [muMk, muKeys, muChal, muPend, muBad, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        rw [env_get_succ, env_get_succ, env_get_succ, env_get_zero]
        exact ⟨hbSt.1, Nat.le_trans hbSt.2.1 (Nat.le_succ n), Nat.le_trans hbSt.2.2 (Nat.le_succ n)⟩
    · refine ret_allLeaves ?_
      dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      rw [env_get_succ, env_get_succ, env_get_zero]
      exact ⟨hbSt.1, Nat.le_trans hbSt.2.1 (Nat.le_succ n), Nat.le_trans hbSt.2.2 (Nat.le_succ n)⟩

private structure SchedResBounded (n : ℕ) (ro0 : (Ty.list (.prod (B 192) drKeyTy)).denote)
    (root0 : (Ty.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))).denote)
    (so : schedResTy.denote) : Prop where
  cache_le : so.1.2.length ≤ n + 1
  mu_le    : MuValBounded (n + 1) so.2
  res_step : ∀ r, so.1.1 = some r →
    CacheStepAtMostOne ro0 r.2.2.2.2.1 ∧ CacheStepAtMostOne root0 r.2.2.2.2.2

private theorem hmRecv_forgeRetIdC_fuel_eq {K₁ K₂ n : ℕ} {Γ₁ Δ : List PT}
    (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [h₁ : Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ muKeyIdTy) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy)
    (env : Env Δ) (hb : MuValBounded n (env.get (h₁.wk fc)).2.2.2)
    (hk₁ : n ≤ K₁) (hk₂ : n ≤ K₂) :
    (forgeRetIdC K₁ fc idx cache').eval env = (forgeRetIdC K₂ fc idx cache').eval env := by
  unfold forgeRetIdC
  refine letV_congr rfl fun ic => ?_
  refine bindV_congr (hmRecv_hmForgeIdC_fuel_eq _ _ ?_ hk₁ hk₂) fun _ => rfl
  simpa [v, Expr.eval, Ext.step_wk, env_get_succ] using hb

private theorem hmRecv_forgeRetIdC_leaves (K : ℕ) {n : ℕ}
    {ro0 : (Ty.list (.prod (B 192) drKeyTy)).denote}
    {root0 : (Ty.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))).denote}
    {Γ₁ Δ : List PT}
    (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [h₁ : Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ muKeyIdTy) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy)
    (env : Env Δ) (hb : MuValBounded n (env.get (h₁.wk fc)).2.2.2)
    (hc : (cache'.eval env).length ≤ n + 1) :
    AllLeaves (SchedResBounded n ro0 root0) ((forgeRetIdC K fc idx cache').eval env) := by
  unfold forgeRetIdC
  refine letV_allLeaves_eq fun ic hic => ?_
  apply bindV_allLeaves (hmRecv_hmForgeIdC_leaves K _ _
    (by simpa [v, Expr.eval, Ext.step_wk, env_get_succ] using hb))
  intro mst' hmst'
  refine ret_allLeaves ?_
  have hic2 : ic.2 = cache'.eval env := congrArg Prod.snd hic
  dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  rw [env_get_succ, env_get_zero, hic2]
  exact ⟨hc, hmst', fun _ h => nomatch h⟩


private theorem hmRecv_hmSchedFinC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) (env : Env Δ)
    (hc : (a.eval env).2.2.2.2.1.length ≤ n)
    (hb : MuValBounded n (a.eval env).2.2.2.2.2.2)
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (hmSchedFinC S K₁ a).eval env = (hmSchedFinC S K₂ a).eval env := by
  unfold hmSchedFinC
  refine letV_congr_eq rfl fun av hav => ?_
  refine letV_congr rfl fun jt => ?_
  refine letV_congr rfl fun kE => ?_
  refine letV_congr rfl fun msg => ?_
  refine letV_congr rfl fun rc => ?_
  refine letV_congr_eq rfl fun cache hcache => ?_
  refine letV_congr rfl fun sp => ?_
  refine letV_congr_eq rfl fun mst hmst => ?_
  refine letV_congr rfl fun matched? => ?_
  refine letV_congr rfl fun useIdeal => ?_
  refine letV_congr rfl fun drKey => ?_
  refine letV_congr rfl fun roC' => ?_
  refine letV_congr rfl fun sameEph => ?_
  refine letV_congr rfl fun rk1 => ?_
  refine letV_congr rfl fun rootC' => ?_
  refine letV_congr rfl fun mkSeed => ?_
  refine letV_congr rfl fun ck1_1 => ?_
  refine letV_congr rfl fun salt? => ?_
  refine letV_congr rfl fun sameMk => ?_
  refine letV_congr rfl fun ad => ?_
  refine letV_congr_eq rfl fun fc hfc => ?_
  have hcacheEq : cache = (a.eval env).2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcache
  have hmstEq : mst = (a.eval env).2.2.2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hmst
  have hbFc : MuValBounded n fc.2.2.2 := by
    have hfcEq : fc.2.2.2 = mst := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
        congrArg (fun p => p.2.2.2) hfc
    rw [hfcEq, hmstEq]; exact hb
  have hcLen : cache.length ≤ n := hcacheEq ▸ hc
  refine ite_congr_eval rfl ?_ rfl
  refine caseOptV_congr rfl
    (hmRecv_forgeRetIdC_fuel_eq _ _ _ _ (by simpa [env_get_zero] using hbFc) h₁ h₂) fun s => ?_
  refine ite_congr_eval rfl
    (ite_congr_eval rfl rfl
      (hmRecv_forgeRetIdC_fuel_eq _ _ _ _ (by simpa [env_get_succ, env_get_zero] using hbFc) h₁ h₂)) ?_
  refine ite_congr_eval rfl ?_
    (hmRecv_forgeRetIdC_fuel_eq _ _ _ _ (by simpa [env_get_succ, env_get_zero] using hbFc) h₁ h₂)
  refine caseOptV_congr ?_
    (hmRecv_forgeRetIdC_fuel_eq _ _ _ _ (by simpa [env_get_succ, env_get_zero] using hbFc) h₁ h₂)
    fun e =>
      hmRecv_forgeRetIdC_fuel_eq _ _ _ _ (by simpa [env_get_succ, env_get_zero] using hbFc) h₁ h₂
  dsimp only [eFind, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero]
  rw [take_eq_of_le (Nat.le_trans hcLen h₁) (Nat.le_trans hcLen h₂)]

private theorem hmRecv_hmSchedFinC_leaves (S : Setup) (K : ℕ) {n : ℕ}
    {ro0 : (Ty.list (.prod (B 192) drKeyTy)).denote}
    {root0 : (Ty.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))).denote}
    {Δ : List PT} (a : Expr pqxdhOps Δ schedFinArgsTy) (env : Env Δ)
    (hc : (a.eval env).2.2.2.2.1.length ≤ n)
    (hb : MuValBounded n (a.eval env).2.2.2.2.2.2)
    (hRo : CacheStepAtMostOne ro0 (a.eval env).2.2.2.2.2.1.2.2.2.2.1)
    (hRt : CacheStepAtMostOne root0 (a.eval env).2.2.2.2.2.1.2.2.2.2.2.2.2.2.1) :
    AllLeaves (SchedResBounded n ro0 root0) ((hmSchedFinC S K a).eval env) := by
  unfold hmSchedFinC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves fun jt => ?_
  refine letV_allLeaves fun kE => ?_
  refine letV_allLeaves fun msg => ?_
  refine letV_allLeaves fun rc => ?_
  refine letV_allLeaves_eq fun cache hcache => ?_
  refine letV_allLeaves_eq fun sp hsp => ?_
  refine letV_allLeaves_eq fun mst hmst => ?_
  refine letV_allLeaves fun matched? => ?_
  refine letV_allLeaves fun useIdeal => ?_
  refine letV_allLeaves fun drKey => ?_
  refine letV_allLeaves_eq fun roC' hroC' => ?_
  refine letV_allLeaves fun sameEph => ?_
  refine letV_allLeaves fun rk1 => ?_
  refine letV_allLeaves_eq fun rootC' hrootC' => ?_
  refine letV_allLeaves fun mkSeed => ?_
  refine letV_allLeaves fun ck1_1 => ?_
  refine letV_allLeaves fun salt? => ?_
  refine letV_allLeaves fun sameMk => ?_
  refine letV_allLeaves fun ad => ?_
  refine letV_allLeaves_eq fun fc hfc => ?_
  have hcacheEq : cache = (a.eval env).2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcache
  have hspEq : sp = (a.eval env).2.2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hsp
  have hmstEq : mst = (a.eval env).2.2.2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hmst
  have hroEq : roC' = (a.eval env).2.2.2.2.2.1.2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hspEq] using hroC'
  have hrtEq : rootC' = (a.eval env).2.2.2.2.2.1.2.2.2.2.2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hspEq] using hrootC'
  have hbFc : MuValBounded n fc.2.2.2 := by
    have hfcEq : fc.2.2.2 = mst := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using
        congrArg (fun p => p.2.2.2) hfc
    rw [hfcEq, hmstEq]; exact hb
  have hcLen : cache.length ≤ n := hcacheEq ▸ hc
  have hbMst : MuValBounded (n + 1) mst := hmstEq ▸ hb.mono (Nat.le_succ n)
  have hRo' : CacheStepAtMostOne ro0 roC' := hroEq ▸ hRo
  have hRt' : CacheStepAtMostOne root0 rootC' := hrtEq ▸ hRt
  refine ite_allLeaves ?_ ?_
  · refine caseOptV_allLeaves ?_ fun s => ?_
    · exact hmRecv_forgeRetIdC_leaves K _ _ _ _
        (by simpa [env_get_zero] using hbFc)
        (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]; omega)
    · refine ite_allLeaves ?_ ?_
      · refine ite_allLeaves ?_ ?_
        · refine ret_allLeaves ?_
          dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
          simp only [env_get_succ, env_get_zero]
          refine ⟨Nat.le_trans hcLen (Nat.le_succ n), hbMst, ?_⟩
          intro r hr; cases hr; exact ⟨hRo', hRt'⟩
        · exact hmRecv_forgeRetIdC_leaves K _ _ _ _
            (by simpa [env_get_succ, env_get_zero] using hbFc)
            (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]; omega)
      · refine ite_allLeaves ?_ ?_
        · refine caseOptV_allLeaves ?_ fun e => ?_
          · exact hmRecv_forgeRetIdC_leaves K _ _ _ _
              (by simpa [env_get_succ, env_get_zero] using hbFc)
              (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
                  simp only [env_get_succ, env_get_zero, List.length_cons]; omega)
          · exact hmRecv_forgeRetIdC_leaves K _ _ _ _
              (by simpa [env_get_succ, env_get_zero] using hbFc)
              (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]; omega)
        · exact hmRecv_forgeRetIdC_leaves K _ _ _ _
            (by simpa [env_get_succ, env_get_zero] using hbFc)
            (by dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]; simp only [env_get_succ, env_get_zero]; omega)
  · refine bindV_allLeaves_const fun mk => bindV_allLeaves_const fun pt? => ?_
    refine caseOptV_allLeaves ?_ fun pt => ?_
    · refine ret_allLeaves ?_
      dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_succ, env_get_zero]
      exact ⟨Nat.le_trans hcLen (Nat.le_succ n), hbMst, fun _ h => nomatch h⟩
    · refine ret_allLeaves ?_
      dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_succ, env_get_zero]
      refine ⟨Nat.le_trans hcLen (Nat.le_succ n), hbMst, ?_⟩
      intro r hr; cases hr; exact ⟨hRo', hRt'⟩


private theorem hmRecv_hmSchedPrepKC_fuel_eq (S : Setup) {K_on K_ro K_old n nRo nRt : ℕ}
    {Δ : List PT} (a : Expr pqxdhOps Δ schedPrepArgsTy) (env : Env Δ)
    (hbBase : AuthBaseValOnlineBounded n (a.eval env).1.1)
    (hbIdeal : (a.eval env).1.2.2.2.length ≤ n)
    (hbRo : (valRoCache (a.eval env).1.1).length ≤ nRo)
    (hbRt : (valRootRoCache (a.eval env).1.1).length ≤ nRt)
    (hon₁ : n ≤ K_on) (hon₂ : n ≤ K_old)
    (hro₁ : nRo ≤ K_ro) (hro₂ : nRo ≤ K_old)
    (hrt₁ : nRt ≤ K_ro) (hrt₂ : nRt ≤ K_old) :
    (hmSchedPrepKC S K_on K_ro a).eval env = (hmSchedPrepC S K_old a).eval env := by
  unfold hmSchedPrepKC hmSchedPrepC
  refine letV_congr_eq rfl fun av hav => ?_
  refine letV_congr_eq rfl fun hstDec hhst => ?_
  refine letV_congr rfl fun kE => ?_
  refine letV_congr rfl fun bE => ?_
  refine letV_congr rfl fun opkBPk? => ?_
  refine letV_congr rfl fun secrets => ?_
  refine letV_congr rfl fun msg => ?_
  refine letV_congr_eq rfl fun st hst => ?_
  refine letV_congr rfl fun hdr => ?_
  have hhstEq : hstDec = (a.eval env).1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hhst
  have hstEq : st = (a.eval env).1.1 := by
    simpa only [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq]
      using hst
  refine bindV_congr
    (findHonestC_prf_fuel_eq S _ _ _
      (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hbBase)
      hon₁ hon₂) fun snd? => ?_
  refine letV_congr rfl fun isUncorr => ?_
  refine letV_congr rfl fun ikBPk => ?_
  refine letV_congr rfl fun spkBPk => ?_
  refine letV_congr rfl fun pqspkBPk => ?_
  refine bindV_congr ?_ fun matched? => ?_
  · dsimp only [findMV, Comp.eval, ahsIdealSessions, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hhstEq]
    rw [take_min_eq_of_le (Nat.le_trans hbIdeal hon₁) (Nat.le_trans hbIdeal hon₂)]
  · refine letV_congr rfl fun useIdeal => ?_
    refine bindV_congr (ite_congr_eval rfl rfl (hkdfRoC_fuel_eq _ _ _
      (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hbRo)
      hro₁ hro₂)) fun drOut => ?_
    refine letV_congr rfl fun drKey => ?_
    refine letV_congr rfl fun roC' => ?_
    refine bindV_congr rfl fun dhR => ?_
    refine bindV_congr rfl fun sameEph => ?_
    exact bindV_congr (ite_congr_eval rfl rfl (rootRoC_fuel_eq _ _ _ _
      (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstEq] using hbRt)
      hrt₁ hrt₂)) fun _ => rfl

private theorem hmRecv_hmSchedPrepKC_leaves (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) (env : Env Δ)
    (hRo : (valRoCache (a.eval env).1.1).length ≤ K_ro)
    (hRt : (valRootRoCache (a.eval env).1.1).length ≤ K_ro) :
    AllLeaves (fun sp? => ∀ sp, sp? = some sp →
      CacheStepAtMostOne (valRoCache (a.eval env).1.1) sp.2.2.2.2.1 ∧
      CacheStepAtMostOne (valRootRoCache (a.eval env).1.1) sp.2.2.2.2.2.2.2.2.1)
      ((hmSchedPrepKC S K_on K_ro a).eval env) := by
  unfold hmSchedPrepKC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves_eq fun hstDec hhst => ?_
  refine letV_allLeaves fun kE => ?_
  refine letV_allLeaves fun bE => ?_
  refine letV_allLeaves fun opkBPk? => ?_
  refine letV_allLeaves fun secrets => ?_
  refine letV_allLeaves fun msg => ?_
  refine letV_allLeaves_eq fun st hst => ?_
  refine letV_allLeaves fun hdr => ?_
  have hhstEq : hstDec = (a.eval env).1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hhst
  have hstEq : st = (a.eval env).1.1 := by
    simpa only [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstEq]
      using hst
  refine bindV_allLeaves_const fun snd? => ?_
  refine letV_allLeaves fun isUncorr => ?_
  refine letV_allLeaves fun ikBPk => ?_
  refine letV_allLeaves fun spkBPk => ?_
  refine letV_allLeaves fun pqspkBPk => ?_
  refine bindV_allLeaves_const fun matched? => ?_
  refine letV_allLeaves fun useIdeal => ?_
  apply bindV_allLeaves
    (P := fun drOut : (Ty.prod drKeyTy (.list (.prod (B 192) drKeyTy))).denote =>
      CacheStepAtMostOne (valRoCache st) drOut.2)
  · refine ite_allLeaves ?_ ?_
    · refine caseOptV_allLeaves (bindV_allLeaves_const fun dk => ret_allLeaves ?_)
        fun s => ret_allLeaves ?_
      · dsimp only [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero]; exact Or.inl rfl
      · dsimp only [asRoCache, valRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero]; exact Or.inl rfl
    · exact hkdfRoC_allLeaves (K := K_ro) _ _ _
        (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])
        (hstEq ▸ hRo)
  intro drOut hdrOut
  refine letV_allLeaves fun drKey => ?_
  refine letV_allLeaves_eq fun roC' hroC' => ?_
  have hroStep : CacheStepAtMostOne (valRoCache (a.eval env).1.1) roC' := by
    have hroEq : roC' = drOut.2 := by
      simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hroC'
    rw [← hstEq, hroEq]; exact hdrOut
  refine bindV_allLeaves_const fun dhR => ?_
  refine bindV_allLeaves_const fun sameEph => ?_
  apply bindV_allLeaves
    (P := fun rkOut : (Ty.prod (.prod (B 32) (B 32))
      (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))).denote =>
      CacheStepAtMostOne (valRootRoCache st) rkOut.2)
  · refine ite_allLeaves ?_ ?_
    · refine caseOptV_allLeaves
        (bindV_allLeaves_const fun r => bindV_allLeaves_const fun c => ret_allLeaves ?_)
        fun s => ite_allLeaves (ret_allLeaves ?_)
          (bindV_allLeaves_const fun r => bindV_allLeaves_const fun c => ret_allLeaves ?_)
      · dsimp only [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero]; exact Or.inl rfl
      · dsimp only [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero]; exact Or.inl rfl
      · dsimp only [asRootRoCache, valRootRoCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [env_get_succ, env_get_zero]; exact Or.inl rfl
    · exact rootRoC_allLeaves (K := K_ro) _ _ _ _
        (by simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero])
        (hstEq ▸ hRt)
  intro rkOut hrkOut
  refine letV_allLeaves fun rk1 => ?_
  refine letV_allLeaves fun ck1_0 => ?_
  refine letV_allLeaves_eq fun rootC' hrootC' => ?_
  have hrtStep : CacheStepAtMostOne (valRootRoCache (a.eval env).1.1) rootC' := by
    have hrtEq : rootC' = rkOut.2 := by
      simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hrootC'
    rw [← hstEq, hrtEq]; exact hrkOut
  refine bindV_allLeaves_const fun mkc => ?_
  refine letV_allLeaves fun mkSeed => ?_
  refine letV_allLeaves fun ck1_1 => ?_
  refine bindV_allLeaves_const fun sp? => ?_
  refine caseOptV_allLeaves (ret_allLeaves fun _ h => nomatch h) fun sp => ret_allLeaves ?_
  dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero]
  intro sp0 hsp0; cases hsp0; exact ⟨hroStep, hrtStep⟩

private theorem hmRecv_hmSchedKC_fuel_eq (S : Setup) {K_on K_ro K_old n nRo nRt : ℕ}
    {Δ : List PT} (a : Expr pqxdhOps Δ schedArgsTy) (env : Env Δ)
    (hc : (a.eval env).2.2.1.length ≤ n)
    (hbBase : AuthBaseValOnlineBounded n (a.eval env).2.2.2.1.1.1)
    (hbIdeal : (a.eval env).2.2.2.1.1.2.2.2.length ≤ n)
    (hbRo : (valRoCache (a.eval env).2.2.2.1.1.1).length ≤ nRo)
    (hbRt : (valRootRoCache (a.eval env).2.2.2.1.1.1).length ≤ nRt)
    (hbMu : MuValBounded n (a.eval env).2.2.2.2)
    (hon₁ : n ≤ K_on) (hon₂ : n ≤ K_old)
    (hro₁ : nRo ≤ K_ro) (hro₂ : nRo ≤ K_old)
    (hrt₁ : nRt ≤ K_ro) (hrt₂ : nRt ≤ K_old) :
    (hmSchedKC S K_on K_ro a).eval env = (hmSchedC S K_old a).eval env := by
  unfold hmSchedKC hmSchedC
  refine letV_congr_eq rfl fun av hav => ?_
  refine letV_congr rfl fun jt => ?_
  refine letV_congr rfl fun rc => ?_
  refine letV_congr_eq rfl fun cache hcache => ?_
  refine letV_congr_eq rfl fun pa hpa => ?_
  refine letV_congr_eq rfl fun mst hmst => ?_
  have hcacheEq : cache = (a.eval env).2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcache
  have hpaEq : pa = (a.eval env).2.2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hpa
  have hmstEq : mst = (a.eval env).2.2.2.2 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hmst
  refine bindV_congr
    (hmRecv_hmSchedPrepKC_fuel_eq S _ _
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using hbBase)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using hbIdeal)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using hbRo)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using hbRt)
      hon₁ hon₂ hro₁ hro₂ hrt₁ hrt₂)
    fun sp? => ?_
  refine caseOptV_congr rfl rfl fun sp => ?_
  exact hmRecv_hmSchedFinC_fuel_eq S _ _
    (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcacheEq] using hc)
    (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hmstEq] using hbMu)
    hon₁ hon₂

private theorem hmRecv_hmSchedKC_leaves (S : Setup) (K_on K_ro : ℕ) {n : ℕ}
    {Δ : List PT} (a : Expr pqxdhOps Δ schedArgsTy) (env : Env Δ)
    (hc : (a.eval env).2.2.1.length ≤ n)
    (hbMu : MuValBounded n (a.eval env).2.2.2.2)
    (hRo : (valRoCache (a.eval env).2.2.2.1.1.1).length ≤ K_ro)
    (hRt : (valRootRoCache (a.eval env).2.2.2.1.1.1).length ≤ K_ro) :
    AllLeaves (SchedResBounded n (valRoCache (a.eval env).2.2.2.1.1.1)
      (valRootRoCache (a.eval env).2.2.2.1.1.1))
      ((hmSchedKC S K_on K_ro a).eval env) := by
  unfold hmSchedKC
  refine letV_allLeaves_eq fun av hav => ?_
  refine letV_allLeaves fun jt => ?_
  refine letV_allLeaves fun rc => ?_
  refine letV_allLeaves_eq fun cache hcache => ?_
  refine letV_allLeaves_eq fun pa hpa => ?_
  refine letV_allLeaves_eq fun mst hmst => ?_
  have hcacheEq : cache = (a.eval env).2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hcache
  have hpaEq : pa = (a.eval env).2.2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hpa
  have hmstEq : mst = (a.eval env).2.2.2.2 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hav] using hmst
  apply bindV_allLeaves (hmRecv_hmSchedPrepKC_leaves S K_on K_ro _ _
    (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using hRo)
    (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using hRt))
  intro sp? hsp?
  refine caseOptV_allLeaves_eq ?_ fun sp hsp => ?_
  · refine ret_allLeaves ?_
    dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ, env_get_zero, hcacheEq, hmstEq]
    exact ⟨Nat.le_trans hc (Nat.le_succ n), hbMu.mono (Nat.le_succ n), fun _ h => nomatch h⟩
  · have hspEq : sp? = some sp := by
      simpa only [v, Expr.eval, Ext.refl_wk, env_get_zero] using hsp
    have hSteps : CacheStepAtMostOne (valRoCache (a.eval env).2.2.2.1.1.1) sp.2.2.2.2.1 ∧
        CacheStepAtMostOne (valRootRoCache (a.eval env).2.2.2.1.1.1) sp.2.2.2.2.2.2.2.2.1 := by
      simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hpaEq] using
        hsp? sp hspEq
    exact hmRecv_hmSchedFinC_leaves S K_on _ _
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hcacheEq] using hc)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hmstEq] using hbMu)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hSteps.1)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hSteps.2)

private structure HmRecvDataBounded (n : ℕ) (fhst0 : authHybridStateFixedTy.denote)
    (d : hmRecvDataTy.denote) : Prop where
  base_eq  : d.2.2.2.2.1.1 = fhst0.1.1
  init_eq  : d.2.2.2.2.1.2.1 = fhst0.1.2.1
  recv_le  : d.2.2.2.2.1.2.2.1.length ≤ n + 1
  ideal_eq : d.2.2.2.2.1.2.2.2 = fhst0.1.2.2.2
  usedT_le : d.2.2.2.2.2.1.length ≤ n + 1

private theorem hmRecv_hmRecvPrepC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁_ext.wk fhst)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (hmRecvPrepC S K₁ opk fhst x).eval env = (hmRecvPrepC S K₂ opk fhst x).eval env := by
  unfold hmRecvPrepC
  refine letV_congr_eq rfl fun hst hhstEq => ?_
  refine letV_congr_eq rfl fun st hstEq => ?_
  have hhstVal : hst = (env.get (h₁_ext.wk fhst)).1 := by
    simpa only [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      using hhstEq
  have hstVal : st = (env.get (h₁_ext.wk fhst)).1.1 := by
    simpa only [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal]
      using hstEq
  have hbSt : AuthBaseValOnlineBounded n st := hstVal ▸ hb.base_le
  iterate 3 refine letV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine ite_congr_eval ?_ rfl ?_
  · cases opk
    · simp only [Bool.false_eq_true, ↓reduceIte, eAny, asUsedRecvNoOPK, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
        take_eq_of_le (Nat.le_trans hbSt.usedRecvNoOPK_le h₁)
          (Nat.le_trans hbSt.usedRecvNoOPK_le h₂)]
    · simp only [↓reduceIte, eAny, asUsedRecvOPK, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero,
        take_eq_of_le (Nat.le_trans hbSt.usedRecvOPK_le h₁)
          (Nat.le_trans hbSt.usedRecvOPK_le h₂)]
  refine bindV_congr (koskSenderOkC_fuel_eq S _ _ _
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) h₁ h₂)
    fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine caseOptV_congr ?_ rfl fun _ => ?_
  · simp only [eFind, asPrincipals, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero,
      take_eq_of_le (Nat.le_trans hbSt.principals_le h₁) (Nat.le_trans hbSt.principals_le h₂)]
  refine caseOptV_congr ?_ rfl fun _ => ?_
  · simp only [eFind, asSpkBundles, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero,
      take_eq_of_le (Nat.le_trans hbSt.spkBundles_le h₁) (Nat.le_trans hbSt.spkBundles_le h₂)]
  iterate 2 refine letV_congr rfl fun _ => ?_
  refine bindV_congr ?_ fun _ => ?_
  · cases opk
    · rfl
    · simp only [↓reduceIte]
      refine caseOptV_congr ?_ rfl fun _ => rfl
      simp only [eFind, asOpkEntries, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero,
        take_eq_of_le (Nat.le_trans hbSt.opkEntries_le h₁) (Nat.le_trans hbSt.opkEntries_le h₂)]
  refine caseSumV_congr rfl (fun _ => rfl) fun _ => ?_
  refine letV_congr (kyberCheckE_fuel_eq _ _ _ ?_ h₁ h₂) fun _ => ?_
  · simp only [asUsedKyberTriples, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero]
    exact hbSt.seenKyberBaseKeys_le
  iterate 2 refine bindV_congr rfl fun _ => ?_
  refine ite_congr_eval rfl rfl ?_
  refine bindV_congr rfl fun _ => ?_
  refine caseOptV_congr rfl rfl fun _ => ?_
  iterate 2 refine letV_congr rfl fun _ => ?_
  iterate 4 refine bindV_congr rfl fun _ => ?_
  refine letV_congr rfl fun _ => ?_
  exact bindV_congr (findHonestC_prf_fuel_eq S _ _ _
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt) h₁ h₂)
    fun _ => rfl

private theorem hmRecv_hmRecvPrepC_leaves (S : Setup) (K : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁_ext.wk fhst))) :
    AllLeaves (fun d? => ∀ d, d? = some d → HmRecvDataBounded n (env.get (h₁_ext.wk fhst)) d)
      ((hmRecvPrepC S K opk fhst x).eval env) := by
  have hNone : ∀ {Γ' : List PT} (ρ : Env Γ'),
      AllLeaves (fun d? => ∀ d, d? = some d → HmRecvDataBounded n (env.get (h₁_ext.wk fhst)) d)
        ((Comp.ret (I := pqPrimIface) (Expr.none : Expr pqxdhOps Γ' (.opt hmRecvDataTy))).eval ρ) :=
    fun _ => AllLeaves.pure (by intro _ h; cases h)
  unfold hmRecvPrepC
  refine letV_allLeaves_eq fun hst hhstEq => ?_
  refine letV_allLeaves_eq fun st hstEq => ?_
  have hhstVal : hst = (env.get (h₁_ext.wk fhst)).1 := by
    simpa only [ahsfHybrid, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
      using hhstEq
  have hstVal : st = (env.get (h₁_ext.wk fhst)).1.1 := by
    simpa only [ahsBase, v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal]
      using hstEq
  iterate 3 refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves (hNone _) ?_
  refine ite_allLeaves (hNone _) ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (hNone _) ?_
  refine caseOptV_allLeaves (hNone _) fun _ => ?_
  refine caseOptV_allLeaves (hNone _) fun _ => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine caseSumV_allLeaves (fun _ => hNone _) fun _ => ?_
  refine letV_allLeaves_eq fun kc hkcEq => ?_
  have hkcLen : kc.2.length ≤ n + 1 := by
    rw [hkcEq]
    refine kyberCheckE_snd_len_le K _ _ _ ?_
    simp only [asUsedKyberTriples, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero, hstVal]
    exact hb.base_le.seenKyberBaseKeys_le
  iterate 2 refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (hNone _) ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine caseOptV_allLeaves (hNone _) fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun hstDec hhstDecEq => ?_
  iterate 4 refine bindV_allLeaves_const fun _ => ?_
  refine letV_allLeaves fun _ => ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine ret_allLeaves fun d hSome => ?_
  dsimp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk] at hSome
  simp only [env_get_succ, env_get_zero] at hSome
  cases hSome
  have hhstD : hstDec.1 = hst.1 ∧ hstDec.2.1 = hst.2.1 ∧
      hstDec.2.2.1.length = hst.2.2.1.length + 1 ∧ hstDec.2.2.2 = hst.2.2.2 := by
    subst hhstDecEq
    dsimp only [ahsUpd, ahsMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [env_get_succ, env_get_zero, List.length_cons]
  rw [hhstVal] at hhstD
  exact ⟨hhstD.1, hhstD.2.1, by rw [hhstD.2.2.1]; exact Nat.add_le_add_right hb.recvKemRecs_le 1,
    hhstD.2.2.2, hkcLen⟩

private theorem hmRecv_finErasedE_fuel_eq {K₁ K₂ n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ : List PT}
    (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [Ext Γ₁ Γ] [Ext Γ₂ Γ] [Ext Γ₃ Γ] [h₄ : Ext Γ₄ Γ] [h₅ : Ext Γ₅ Γ]
    (env : Env Γ) (hOpk : (env.get (h₄.wk hstDec)).1.2.2.2.2.1.length ≤ n)
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (finErasedE K₁ opk kjo usedT' sndHon hstDec res?).eval env =
      (finErasedE K₂ opk kjo usedT' sndHon hstDec res?).eval env := by
  dsimp only [finErasedE, eCaseOpt, v, Expr.eval, Ext.refl_wk]
  cases env.get (h₅.wk res?) with
  | none => rfl
  | some r =>
    cases opk
    · rfl
    · simp only [↓reduceIte]
      congr 1
      dsimp only [ahsUpd, ahsMk, stUpd, stMk, eMap, asOpkEntries, ahsBase,
        v, Expr.eval, Ext.step_wk, Ext.refl_wk]
      simp only [env_get_succ, env_get_zero,
        take_eq_of_le (Nat.le_trans hOpk h₁) (Nat.le_trans hOpk h₂)]

private theorem hmRecv_finErasedE_props {K n : ℕ} {opk : Bool}
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ : List PT}
    {kjo : Var Γ₁ (.prod .nat (.prod .nat .nat))}
    {usedT' : Var Γ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32)))))}
    {sndHon : Var Γ₃ .bool} {hstDec : Var Γ₄ authHybridStateTy} {res? : Var Γ₅ schedOutTy}
    [Ext Γ₁ Γ] [h₂ : Ext Γ₂ Γ] [Ext Γ₃ Γ] [h₄ : Ext Γ₄ Γ] [h₅ : Ext Γ₅ Γ]
    {env : Env Γ} {fin : (Ty.prod authRespTy authHybridStateTy).denote}
    (hfin : fin = (finErasedE K opk kjo usedT' sndHon hstDec res?).eval env)
    (hbBase : AuthBaseValOnlineBounded n (env.get (h₄.wk hstDec)).1)
    (hInit : (env.get (h₄.wk hstDec)).2.1.length ≤ n)
    (hRecv : (env.get (h₄.wk hstDec)).2.2.1.length ≤ n + 1)
    (hIdeal : (env.get (h₄.wk hstDec)).2.2.2.length ≤ n)
    (hUsedT : (env.get (h₂.wk usedT')).length ≤ n + 1)
    (hStep : ∀ r, env.get (h₅.wk res?) = some r →
      CacheStepAtMostOne (valRoCache (env.get (h₄.wk hstDec)).1) r.2.2.2.2.1 ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₄.wk hstDec)).1) r.2.2.2.2.2) :
    AuthBaseValOnlineBounded (n + 1) fin.2.1 ∧
    fin.2.2.1.length ≤ n + 1 ∧ fin.2.2.2.1.length ≤ n + 1 ∧ fin.2.2.2.2.length ≤ n + 1 ∧
    CacheStepAtMostOne (valRoCache (env.get (h₄.wk hstDec)).1) (valRoCache fin.2.1) ∧
    CacheStepAtMostOne (valRootRoCache (env.get (h₄.wk hstDec)).1) (valRootRoCache fin.2.1) := by
  subst hfin
  have hb1 : AuthBaseValOnlineBounded (n + 1) (env.get (h₄.wk hstDec)).1 :=
    hbBase.mono (Nat.le_succ n)
  dsimp only [finErasedE, eCaseOpt, v, Expr.eval, Ext.refl_wk]
  cases hres : env.get (h₅.wk res?) with
  | none =>
    exact ⟨hb1, Nat.le_trans hInit (Nat.le_succ n), hRecv, Nat.le_trans hIdeal (Nat.le_succ n),
      Or.inl rfl, Or.inl rfl⟩
  | some r =>
    obtain ⟨hRoS, hRtS⟩ := hStep r hres
    cases opk
    · dsimp only [ahsUpd, ahsMk, stUpd, stMk, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
        ahsIdealSessions, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
        asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents,
        asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
        valRoCache, valRootRoCache, Expr.eval, Ext.step_wk]
      simp only [Bool.false_eq_true, ↓reduceIte, Expr.eval, env_get_succ, env_get_zero]
      exact ⟨⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le, hb1.sessions_le,
        hb1.usedSendSessions_le, hb1.usedRecvOPK_le,
        by rw [List.length_cons]; exact Nat.add_le_add_right hbBase.usedRecvNoOPK_le 1, hUsedT,
        hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le, hb1.recvdOPKEvents_le,
        hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
        Nat.le_trans hInit (Nat.le_succ n), hRecv, Nat.le_trans hIdeal (Nat.le_succ n),
        hRoS, hRtS⟩
    · dsimp only [ahsUpd, ahsMk, stUpd, stMk, eMap, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
        ahsIdealSessions, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
        asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents,
        asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
        valRoCache, valRootRoCache, Expr.eval, Ext.step_wk]
      simp only [↓reduceIte, Expr.eval, env_get_succ, env_get_zero]
      exact ⟨⟨hb1.principals_le, hb1.spkBundles_le,
        by rw [List.length_map, List.length_take]; have := hbBase.opkEntries_le; omega,
        hb1.sessions_le, hb1.usedSendSessions_le,
        by rw [List.length_cons]; exact Nat.add_le_add_right hbBase.usedRecvOPK_le 1,
        hb1.usedRecvNoOPK_le, hUsedT,
        hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le, hb1.recvdOPKEvents_le,
        hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
        Nat.le_trans hInit (Nat.le_succ n), hRecv, Nat.le_trans hIdeal (Nat.le_succ n),
        hRoS, hRtS⟩

private theorem hmRecv_hmRecvTailKC_fuel_eq (S : Setup) {K_on K_ro K_old n nRo nRt : ℕ}
    (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ] [h₅ : Ext Γ₅ Δ]
    (env : Env Δ)
    (hbFhst : AuthFixedValOnlineBounded n (env.get (h₂.wk fhst)))
    (hbMu : MuValBounded n (env.get (h₃.wk mst)))
    (hd : HmRecvDataBounded n (env.get (h₂.wk fhst)) (env.get (h₅.wk d)))
    (hbRo : (valRoCache (env.get (h₂.wk fhst)).1.1).length ≤ nRo)
    (hbRt : (valRootRoCache (env.get (h₂.wk fhst)).1.1).length ≤ nRt)
    (hon₁ : n ≤ K_on) (hon₂ : n ≤ K_old)
    (hro₁ : nRo ≤ K_ro) (hro₂ : nRo ≤ K_old)
    (hrt₁ : nRt ≤ K_ro) (hrt₂ : nRt ≤ K_old) :
    (hmRecvTailKC S K_on K_ro opk jt fhst mst x d).eval env =
      (hmRecvTailC S K_old opk jt fhst mst x d).eval env := by
  unfold hmRecvTailKC hmRecvTailC
  iterate 6 refine letV_congr rfl fun _ => ?_
  refine letV_congr_eq rfl fun hstDec hhstDec => ?_
  iterate 2 refine letV_congr rfl fun _ => ?_
  have hhstEq : hstDec = (env.get (h₅.wk d)).2.2.2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstDec
  have hstBaseEq : hstDec.1 = (env.get (h₂.wk fhst)).1.1 := hhstEq ▸ hd.base_eq
  have hstIdealEq : hstDec.2.2.2 = (env.get (h₂.wk fhst)).1.2.2.2 := hhstEq ▸ hd.ideal_eq
  refine bindV_congr
    (hmRecv_hmSchedKC_fuel_eq S _ _
      (by simpa only [ahsfMkSaltCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_succ, env_get_zero] using hbFhst.mkSaltCache_le)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
            using hbFhst.base_le)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstIdealEq]
            using hbFhst.idealSessions_le)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
            using hbRo)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
            using hbRt)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbMu)
      hon₁ hon₂ hro₁ hro₂ hrt₁ hrt₂)
    fun so => ?_
  iterate 3 refine letV_congr rfl fun _ => ?_
  refine letV_congr (hmRecv_finErasedE_fuel_eq opk _ _ _ _ _ _ ?_ hon₁ hon₂) fun _ => rfl
  simp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
  exact hbFhst.base_le.opkEntries_le

private structure HmRecvLeafInv (n : ℕ) (fhst0 : authHybridStateFixedTy.denote)
    (r : hmResTy.denote) : Prop where
  fixed_le  : AuthFixedValOnlineBounded (n + 1) r.1.2
  mu_le     : MuValBounded (n + 1) r.2
  ro_step   : CacheStepAtMostOne (valRoCache fhst0.1.1) (valRoCache r.1.2.1.1)
  root_step : CacheStepAtMostOne (valRootRoCache fhst0.1.1) (valRootRoCache r.1.2.1.1)

private theorem hmRecv_hmRecvTailKC_leaves (S : Setup) (K_on K_ro : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ] [h₅ : Ext Γ₅ Δ]
    (env : Env Δ)
    (hbFhst : AuthFixedValOnlineBounded n (env.get (h₂.wk fhst)))
    (hbMu : MuValBounded n (env.get (h₃.wk mst)))
    (hd : HmRecvDataBounded n (env.get (h₂.wk fhst)) (env.get (h₅.wk d)))
    (hRo : (valRoCache (env.get (h₂.wk fhst)).1.1).length ≤ K_ro)
    (hRt : (valRootRoCache (env.get (h₂.wk fhst)).1.1).length ≤ K_ro) :
    AllLeaves (HmRecvLeafInv n (env.get (h₂.wk fhst)))
      ((hmRecvTailKC S K_on K_ro opk jt fhst mst x d).eval env) := by
  unfold hmRecvTailKC
  iterate 6 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun hstDec hhstDec => ?_
  refine letV_allLeaves_eq fun usedT' husedT' => ?_
  refine letV_allLeaves fun _ => ?_
  have hhstEq : hstDec = (env.get (h₅.wk d)).2.2.2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstDec
  have husedEq : usedT' = (env.get (h₅.wk d)).2.2.2.2.2.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using husedT'
  have hstBaseEq : hstDec.1 = (env.get (h₂.wk fhst)).1.1 := hhstEq ▸ hd.base_eq
  have hstInitEq : hstDec.2.1 = (env.get (h₂.wk fhst)).1.2.1 := hhstEq ▸ hd.init_eq
  have hstRecvLe : hstDec.2.2.1.length ≤ n + 1 := hhstEq ▸ hd.recv_le
  have hstIdealEq : hstDec.2.2.2 = (env.get (h₂.wk fhst)).1.2.2.2 := hhstEq ▸ hd.ideal_eq
  have husedLe : usedT'.length ≤ n + 1 := husedEq ▸ hd.usedT_le
  apply bindV_allLeaves
    (hmRecv_hmSchedKC_leaves S K_on K_ro _ _
      (by simpa only [ahsfMkSaltCache, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
            env_get_succ, env_get_zero] using hbFhst.mkSaltCache_le)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbMu)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
            using hRo)
      (by simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
            using hRt))
  intro so hso
  have hsoStep : ∀ r, so.1.1 = some r →
      CacheStepAtMostOne (valRoCache hstDec.1) r.2.2.2.2.1 ∧
      CacheStepAtMostOne (valRootRoCache hstDec.1) r.2.2.2.2.2 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hso.res_step
  refine letV_allLeaves_eq fun res? hres? => ?_
  refine letV_allLeaves_eq fun cache' hcache' => ?_
  refine letV_allLeaves_eq fun mst' hmst' => ?_
  refine letV_allLeaves_eq fun fin hfin => ?_
  refine ret_allLeaves ?_
  have hresEq : res? = so.1.1 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hres?
  have hcacheEq : cache' = so.1.2 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hcache'
  have hmstEq : mst' = so.2 := by
    simpa only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hmst'
  have hFinProps := hmRecv_finErasedE_props hfin
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstBaseEq]
          using hbFhst.base_le)
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstInitEq]
          using hbFhst.initKemRecs_le)
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstRecvLe)
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstIdealEq]
          using hbFhst.idealSessions_le)
    (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using husedLe)
    (by intro r hr
        exact hsoStep r (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hresEq] using hr))
  have hRoStep0 : CacheStepAtMostOne (valRoCache (env.get (h₂.wk fhst)).1.1) (valRoCache fin.2.1) :=
    hstBaseEq ▸ hFinProps.2.2.2.2.1
  have hRtStep0 : CacheStepAtMostOne (valRootRoCache (env.get (h₂.wk fhst)).1.1)
      (valRootRoCache fin.2.1) :=
    hstBaseEq ▸ hFinProps.2.2.2.2.2
  dsimp only [ahsfMk, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
  simp only [env_get_succ, env_get_zero, hcacheEq, hmstEq]
  exact ⟨⟨hFinProps.1, hFinProps.2.1, hFinProps.2.2.1, hFinProps.2.2.2.1, hso.cache_le⟩,
    hso.mu_le, hRoStep0, hRtStep0⟩

private theorem hmRecvKC_fuel_eq (S : Setup) {K_on K_ro K_old n nRo nRt : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (env : Env Δ)
    (hbFhst : AuthFixedValOnlineBounded n (env.get (h₂.wk fhst)))
    (hbMu : MuValBounded n (env.get (h₃.wk mst)))
    (hbRo : (valRoCache (env.get (h₂.wk fhst)).1.1).length ≤ nRo)
    (hbRt : (valRootRoCache (env.get (h₂.wk fhst)).1.1).length ≤ nRt)
    (hon₁ : n ≤ K_on) (hon₂ : n ≤ K_old)
    (hro₁ : nRo ≤ K_ro) (hro₂ : nRo ≤ K_old)
    (hrt₁ : nRt ≤ K_ro) (hrt₂ : nRt ≤ K_old) :
    (hmRecvKC S K_on K_ro opk jt fhst mst x).eval env =
      (hmRecvC S K_old opk jt fhst mst x).eval env := by
  unfold hmRecvKC hmRecvC
  refine bindV_congr_leaves
    (hmRecv_hmRecvPrepC_fuel_eq S opk fhst x env hbFhst hon₁ hon₂)
    (hmRecv_hmRecvPrepC_leaves S K_on opk fhst x env hbFhst)
    fun d? hd? => ?_
  dsimp only [caseOptV, v, Comp.eval, Expr.eval, Ext.refl_wk, env_get_zero]
  cases d? with
  | none => rfl
  | some d =>
    have hd : HmRecvDataBounded n (env.get (h₂.wk fhst)) d := hd? d rfl
    exact bindV_congr
      (hmRecv_hmRecvTailKC_fuel_eq S opk _ _ _ _ _ _
        (by simpa only [Ext.step_wk, env_get_succ] using hbFhst)
        (by simpa only [Ext.step_wk, env_get_succ] using hbMu)
        (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hd)
        (by simpa only [Ext.step_wk, env_get_succ] using hbRo)
        (by simpa only [Ext.step_wk, env_get_succ] using hbRt)
        hon₁ hon₂ hro₁ hro₂ hrt₁ hrt₂)
      fun _ => rfl

private theorem hmRecvKC_leaves (S : Setup) (K_on K_ro : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (env : Env Δ)
    (hbFhst : AuthFixedValOnlineBounded n (env.get (h₂.wk fhst)))
    (hbMu : MuValBounded n (env.get (h₃.wk mst)))
    (hRo : (valRoCache (env.get (h₂.wk fhst)).1.1).length ≤ K_ro)
    (hRt : (valRootRoCache (env.get (h₂.wk fhst)).1.1).length ≤ K_ro) :
    AllLeaves (fun pre : hmPreTy.denote =>
      ∃ r : hmResTy.denote, pre = Sum.inl r ∧ HmRecvLeafInv n (env.get (h₂.wk fhst)) r)
      ((hmRecvKC S K_on K_ro opk jt fhst mst x).eval env) := by
  unfold hmRecvKC
  apply bindV_allLeaves (hmRecv_hmRecvPrepC_leaves S K_on opk fhst x env hbFhst)
  intro d? hd?
  refine caseOptV_allLeaves_eq ?_ fun d hdEq => ?_
  · refine ret_allLeaves ?_
    dsimp only [ahsfUpd, v, Expr.eval, Ext.step_wk, Ext.refl_wk]
    simp only [env_get_succ]
    refine ⟨_, rfl, ?_, hbMu.mono (Nat.le_succ n), Or.inl rfl, Or.inl rfl⟩
    exact ⟨hbFhst.base_le.mono (Nat.le_succ n),
      Nat.le_trans hbFhst.initKemRecs_le (Nat.le_succ n),
      Nat.le_trans hbFhst.recvKemRecs_le (Nat.le_succ n),
      Nat.le_trans hbFhst.idealSessions_le (Nat.le_succ n),
      Nat.le_trans hbFhst.mkSaltCache_le (Nat.le_succ n)⟩
  · have hd : HmRecvDataBounded n (env.get (h₂.wk fhst)) d :=
      hd? d (by simpa only [v, Expr.eval, Ext.refl_wk, env_get_zero] using hdEq)
    apply bindV_allLeaves
      (hmRecv_hmRecvTailKC_leaves S K_on K_ro opk _ _ _ _ _ _
        (by simpa only [Ext.step_wk, env_get_succ] using hbFhst)
        (by simpa only [Ext.step_wk, env_get_succ] using hbMu)
        (by simpa only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hd)
        (by simpa only [Ext.step_wk, env_get_succ] using hRo)
        (by simpa only [Ext.step_wk, env_get_succ] using hRt))
    intro r hr
    refine ret_allLeaves ?_
    dsimp only [v, Expr.eval, Ext.refl_wk]
    rw [env_get_zero]
    exact ⟨r, rfl, by simpa only [Ext.step_wk, env_get_succ] using hr⟩

private theorem hmRecvArm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (t : AuthQuery S)
    {xAtom : authRecvQAtomicTy.denote}
    (hOn : authSimPred S 0 t)
    (hPreOld : (hmPre1KeyC S b.q_total).eval
        (.cons (projVal hmStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) =
      (hmRecvC S b.q_total opk
        (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
        (Γ₂ := [authHybridStateFixedTy, muStTy, recvQTy])
        (Γ₃ := [muStTy, recvQTy])
        (Γ₄ := [recvQTy])
        (Δ := [.nat, authHybridStateFixedTy, muStTy, recvQTy]) .zero .zero .zero .zero).eval
        (.cons s'.1.1 (.cons (projVal authHybridStateFixedTy s'.1.2.1)
          (.cons (projVal muStTy s'.1.2.2) (.cons (projVal recvQTy xAtom) .nil)))))
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let ρ := Env.cons xAtom (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let arm : Comp pqAtomicOps pqPrfHmacIface
        [authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
      .bind (liftPrfHmac1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun jt =>
           letV (.fst (.snd (v s))) fun fhst =>
           letV (.snd (.snd (v s))) fun mst =>
           bindV (liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
           hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
    Prod.map id forgetHm <$> arm.eval ρ =
      (prfHmacOldAtomicProg S b).handle.eval (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support (arm.eval ρ), AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F ρ arm
  have ⟨hnOn, hRoStepB, hRootStepB, _⟩ :=
    AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
  have hKonQ : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hKroQ : F.K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hFhst0Emb : embedVal authHybridStateFixedTy (projVal authHybridStateFixedTy s'.1.2.1) = s'.1.2.1 :=
    embedVal_projVal authHybridStateFixedTy s'.1.2.1
  have hb0 : AuthFixedValOnlineBounded (c 0) (projVal authHybridStateFixedTy s'.1.2.1) := by
    rw [← AuthFixedAtomOnlineBounded.iff_embedVal, hFhst0Emb]
    exact hInv.shadow_ok.fixed_ok.online_le
  have hRo0 : (valRoCache (projVal authHybridStateFixedTy s'.1.2.1).1.1).length ≤ c 0 + c 1 := by
    have h := hInv.shadow_ok.fixed_ok.ro_len_le
    dsimp only [hmShadowFixed] at h
    rw [← hFhst0Emb] at h
    change (atomRoCache (embedVal authStateTy (projVal authHybridStateFixedTy s'.1.2.1).1.1)).length ≤ c 0 + c 1 at h
    rwa [atomRoCache_embedVal] at h
  have hRoot0 : (valRootRoCache (projVal authHybridStateFixedTy s'.1.2.1).1.1).length ≤ c 0 + c 2 := by
    have h := hInv.shadow_ok.fixed_ok.root_len_le
    dsimp only [hmShadowFixed] at h
    rw [← hFhst0Emb] at h
    change (atomRootRoCache (embedVal authStateTy (projVal authHybridStateFixedTy s'.1.2.1).1.1)).length ≤ c 0 + c 2 at h
    rwa [atomRootRoCache_embedVal] at h
  have hMu0 : MuValBounded (c 0) (projVal muStTy s'.1.2.2) :=
    ⟨by simpa [projVal] using hInv.shadow_ok.mu_keys_le,
     by simpa [projVal] using hInv.shadow_ok.mu_chal_le,
     by simpa [projVal] using hInv.shadow_ok.mu_pend_le⟩
  have hOnQ : c 0 ≤ b.q_total :=
    Nat.le_trans (Nat.le_succ _) (Nat.le_trans hnOn hKonQ)
  have hRoQ : c 0 + c 1 ≤ b.q_total :=
    Nat.le_trans (by omega : c 0 + c 1 ≤ c 0 + 1 + c 1) (Nat.le_trans hRoStepB hKroQ)
  have hRootQ : c 0 + c 2 ≤ b.q_total :=
    Nat.le_trans (by omega : c 0 + c 2 ≤ c 0 + 1 + c 2) (Nat.le_trans hRootStepB hKroQ)
  have hLeavesOld :
      AllLeaves (HmPreLeafInv (c 0) (projVal authHybridStateFixedTy s'.1.2.1))
        ((hmRecvC S b.q_total opk
          (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
          (Γ₂ := [authHybridStateFixedTy, muStTy, recvQTy])
          (Γ₃ := [muStTy, recvQTy]) (Γ₄ := [recvQTy])
          (Δ := [.nat, authHybridStateFixedTy, muStTy, recvQTy]) .zero .zero .zero .zero).eval
          (.cons s'.1.1 (.cons (projVal authHybridStateFixedTy s'.1.2.1)
            (.cons (projVal muStTy s'.1.2.2) (.cons (projVal recvQTy xAtom) .nil))))) := by
    refine AllLeaves_of_mem_support fun pre hpre => ?_
    rw [← hmRecvKC_fuel_eq S (K_on := b.q_total) (K_ro := b.q_total) (K_old := b.q_total) opk
      (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
      (Γ₂ := [authHybridStateFixedTy, muStTy, recvQTy])
      (Γ₃ := [muStTy, recvQTy]) (Γ₄ := [recvQTy])
      (Δ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
      .zero .zero .zero .zero _
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hb0)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hMu0)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRo0)
      (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoot0)
      hOnQ hOnQ hRoQ hRoQ hRootQ hRootQ] at hpre
    obtain ⟨r, rfl, hr⟩ := AllLeaves_mem_support
      (hmRecvKC_leaves S b.q_total b.q_total opk
        (Γ₁ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
        (Γ₂ := [authHybridStateFixedTy, muStTy, recvQTy])
        (Γ₃ := [muStTy, recvQTy]) (Γ₄ := [recvQTy])
        (Δ := [.nat, authHybridStateFixedTy, muStTy, recvQTy])
        .zero .zero .zero .zero _
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hb0)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hMu0)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using Nat.le_trans hRo0 hRoQ)
        (by simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using Nat.le_trans hRoot0 hRootQ))
      hpre
    dsimp only [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] at hr
    exact ⟨⟨hr.fixed_le, hr.ro_step, hr.root_step⟩, hr.mu_le⟩
  exact hmOnlineArm_sim S b (arg := recvQTy)
    (fun jt fhst mst x => hmRecvKC S F.K_on F.K_ro opk jt fhst mst x)
    (fun jt fhst mst x => hmRecvC S b.q_total opk jt fhst mst x)
    c s' t hOn hPreOld
    (fun jt fhst mst x env5 hJ hF hM hX => by
      rw [hmRecvKC_fuel_eq S opk jt fhst mst x env5
        (hF ▸ hb0) (hM ▸ hMu0) (hF ▸ hRo0) (hF ▸ hRoot0)
        (Nat.le_trans (Nat.le_succ _) hnOn) hOnQ
        (Nat.le_trans (by omega : c 0 + c 1 ≤ c 0 + 1 + c 1) hRoStepB) hRoQ
        (Nat.le_trans (by omega : c 0 + c 2 ≤ c 0 + 1 + c 2) hRootStepB) hRootQ,
        hmRecvC_eval_ren4, hJ, hF, hM, hX])
    hLeavesOld
    hroom hInv

private theorem prfHmac1KeyKindProg_handle_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authHmShadowStTy.denote) (t : AuthQuery S)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthHmInv S b c s') :
    Prod.map id forgetHm <$> (prfHmac1KeyKindProg S b).handle.eval
        (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (prfHmacOldAtomicProg S b).handle.eval
        (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((prfHmac1KeyKindProg S b).handle.eval
        (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      AuthHmInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let F := AuthKindFuels.ofBudget S b
  change Prod.map id forgetHm <$> (prfHmacKindHandleC S F).eval
      (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
    (prfHmacOldAtomicProg S b).handle.eval
      (.cons (forgetHm s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support ((prfHmacKindHandleC S F).eval
      (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      AuthHmInv S b (bumpPred (authSimPred S) c t) p.2
  dsimp only [prfHmacKindHandleC]
  erw [dispatchAuthQ_eval_qenc (.var (.succ .zero))
    (.cons s' (.cons ((authCodec S).qenc t) .nil)) t rfl]
  cases t with
  | initPrin u =>
    have hOn : authSimPred S 0 (.initPrin u) := trivial
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
    exact hmBaseArm_sim S b (arg := .nat)
      (fun fhst x => initPrin1KeyFixedKB F fhst x) (fun fhst x => initPrin1KeyFixedB b.q_total fhst x)
      rfl c s' (.initPrin u) u hOn hroom hInv
      (initPrinFixedShadowB_sim tlPrfHmac liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (hmShadowFixed s') u hInv.shadow_ok.fixed_ok hn)
      (by
        simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
          _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
          Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        exact bind_const_congr (eval_ren2_eq (initPrin1KeyFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
          (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) rfl rfl rfl))
  | corruptIK u =>
    have hOn : authSimPred S 0 (.corruptIK u) := trivial
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
    exact hmBaseArm_sim S b (arg := .nat)
      (fun fhst x => corruptFixedKB F fhst x) (fun fhst x => corruptFixedB b.q_total fhst x)
      rfl c s' (.corruptIK u) u hOn hroom hInv
      (corruptFixedShadowB_sim tlPrfHmac liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (hmShadowFixed s') u hInv.shadow_ok.fixed_ok hn)
      (by
        simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
          _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
          Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        exact bind_const_congr (eval_ren2_eq (corruptFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
          (Δ := [authHybridStateFixedTy, .nat]) .zero .zero) rfl rfl rfl))
  | genSPK u j =>
    have hOn : authSimPred S 0 (.genSPK u j) := trivial
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
    exact hmBaseArm_sim S b (arg := .prod .nat .nat)
      (fun fhst x => genSpkFixedKB F fhst x) (fun fhst x => genSpkFixedB b.q_total fhst x)
      rfl c s' (.genSPK u j) (u, j) hOn hroom hInv
      (genSpkFixedShadowB_sim tlPrfHmac liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (hmShadowFixed s') (u, j) hInv.shadow_ok.fixed_ok hn)
      (by
        simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
          _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
          Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        exact bind_const_congr (eval_ren2_eq (genSpkFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
          (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero) rfl rfl rfl))
  | genOPK u j o =>
    have hOn : authSimPred S 0 (.genOPK u j o) := trivial
    have ⟨hn, _, _, _⟩ := AuthCounterInv.online_step_bounds hInv.counter_inv hOn hroom
    exact hmBaseArm_sim S b (arg := .prod .nat (.prod .nat .nat))
      (fun fhst x => genOpkFixedKB F fhst x) (fun fhst x => genOpkFixedB b.q_total fhst x)
      rfl c s' (.genOPK u j o) (u, (j, o)) hOn hroom hInv
      (genOpkFixedShadowB_sim tlPrfHmac liftPrimComp liftPrimComp_eval_congr
        mem_support_liftPrimComp S b (hmShadowFixed s') (u, (j, o)) hInv.shadow_ok.fixed_ok hn)
      (by
        simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
          _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
          Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        exact bind_const_congr (eval_ren2_eq (genOpkFixedB b.q_total
          (Γ₁ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)])
          (Γ₂ := [.prod .nat (.prod .nat .nat)])
          (Δ := [authHybridStateFixedTy, .prod .nat (.prod .nat .nat)]) .zero .zero) rfl rfl rfl))
  | sendOPK u i bu m0 m1 =>
    exact hmSendArm_sim S b true c s' (.sendOPK u i bu m0 m1) trivial
      (by
        dsimp only [hmPre1KeyC, hmDispatch1KeyC, letV, caseSumV]
        rw [eval_letC, eval_letC, eval_letC, eval_letC]
        dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        rw [hmSendC_eval_ren4]
        congr 1
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ, Ext.step_wk, Ext.refl_wk]
        rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl)
      hroom hInv
  | sendNoOPK u i bu m0 m1 =>
    exact hmSendArm_sim S b false c s' (.sendNoOPK u i bu m0 m1) trivial
      (by
        dsimp only [hmPre1KeyC, hmDispatch1KeyC, letV, caseSumV]
        rw [eval_letC, eval_letC, eval_letC, eval_letC]
        dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        rw [hmSendC_eval_ren4]
        congr 1
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ, Ext.step_wk, Ext.refl_wk]
        rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl)
      hroom hInv
  | recvOPK k j o msg =>
    exact hmRecvArm_sim S b true c s' (.recvOPK k j o msg) trivial
      (by
        dsimp only [hmPre1KeyC, hmDispatch1KeyC, letV, caseSumV]
        rw [eval_letC, eval_letC, eval_letC, eval_letC]
        dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        rw [hmRecvC_eval_ren4]
        congr 1
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ, Ext.step_wk, Ext.refl_wk]
        rcases msg with ⟨⟨_, _, _, _ | _, _, _⟩, _, _, _⟩ <;> rfl)
      hroom hInv
  | recvNoOPK k j l msg =>
    exact hmRecvArm_sim S b false c s' (.recvNoOPK k j l msg) trivial
      (by
        dsimp only [hmPre1KeyC, hmDispatch1KeyC, letV, caseSumV]
        rw [eval_letC, eval_letC, eval_letC, eval_letC]
        dsimp only [v, _root_.SignalPqxdh.LegacyCosted.authCodec,
          _root_.SignalPqxdh.LegacyCosted.authQenc, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk]
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        rw [hmRecvC_eval_ren4]
        congr 1
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ, Ext.step_wk, Ext.refl_wk]
        rcases msg with ⟨⟨_, _, _, _ | _, _, _⟩, _, _, _⟩ <;> rfl)
      hroom hInv
  | roQuery sec =>
    exact roArm_sim S b c s' sec hroom hInv
  | roRootQuery rk dh =>
    exact roRootArm_sim S b c s' rk dh hroom hInv
  | revealDhSecrets =>
    exact revealDh_sim S b c s' hroom hInv
  | registerKey sk =>
    have hOn : authSimPred S 0 (.registerKey sk) := trivial
    exact hmBaseArm_sim S b (arg := B 32)
      (fun fhst x => registerFixedKB fhst x) (fun fhst x => registerFixedB fhst x)
      rfl c s' (.registerKey sk) sk hOn hroom hInv
      ⟨rfl, registerFixedShadowB_sim tlPrfHmac liftPrimComp mem_support_liftPrimComp
        S b (hmShadowFixed s') sk hInv.shadow_ok.fixed_ok⟩
      (by
        simp only [hmPre1KeyC, hmDispatch1KeyC, hmOther, letV, eval_letC, caseSumV, bindV, v,
          _root_.SignalPqxdh.LegacyCosted.authCodec, _root_.SignalPqxdh.LegacyCosted.authQenc,
          Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ]
        exact bind_const_congr (eval_ren2_eq (registerFixedB
          (Γ₁ := [authHybridStateFixedTy, B 32]) (Γ₂ := [B 32])
          (Δ := [authHybridStateFixedTy, B 32]) .zero .zero) rfl rfl rfl))

/-- Forgetful simulation bundle for `prfHmac1KeyKindProg` against `prfHmacOldAtomicProg`. -/
theorem prfHmac1KeyKindProg_forgetSim (S : Setup) (b : QueryBudget) (x : Unit) :
    ForgetSim (prfHmac1KeyKindProg S b) (prfHmacOldAtomicProg S b)
      forgetHm (authSimPred S) (authSimBounds b) x (AuthHmInv S b) where
  hInit   := prfHmac1KeyKindProg_init_sim S b x
  hHandle := fun c s' t _hc hroom hInv => prfHmac1KeyKindProg_handle_sim S b c s' t hroom hInv
  hFinish := fun c s' bOut _hc hInv => prfHmac1KeyKindProg_finish_sim S b c s' bOut hInv

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfInt
