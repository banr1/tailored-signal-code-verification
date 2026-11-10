/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedHs
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCr

/-!
# `shcrAuth1KeyKindProg` Cost, Query, and Size Bounds

Pre-stage handle, `init`/`chDone`/`finish` cost and primitive query bounds, and
`TwoStageCostedReduction.size` bound for `shcrAuth1KeyKindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcr

open _root_.ReductionDsl (Ty Var Comp Expr Env pqAtomicSig pqAtomicOps PB bits reductionSizeBudget
  TwoStageCostedReduction)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B primIfacePrimQueryWeight)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface)
open _root_.SignalPqxdh.Security
  (stepCostBudget authQueryKind authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (aiAuthPrim embedTy mapComp tlAuthPrim tlAuthPrim_primW tlAuthPrim_sizeLe
   mapComp_cost_two_mul_le mapComp_cost_eleven_mul_le mapComp_queries_le mapComp_size_le
   compRename_cost compRename_queries compRename_size compLitSize exprLitSize pqOpLitSize
   sampR64W r64W castLegacySamp
   bits_le_bits_stepCostBudget atomicSize_le_budget)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext RS shcrStTy pauseTy sendQTy recvQTy
   shcrReductionAuthProg shcrGenSpkB tryPauseC shcrExtractC
   shcr_init_cost_le_tight shcr_chDone_cost_le shcr_finish_cost_le
   shcrGenSpkB_costUB_le_tight tryPauseC_costUB
   shcr_init_queries shcr_chDone_queries shcr_finish_queries
   shcrGenSpkB_queries tryPauseC_queries)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (avlHeightCap)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy emptyRoBothAvlE authQueryAtomicTy authRespAtomicTy
   authSendQAtomicTy authRecvQAtomicTy
   baseRoCacheE baseRootRoCacheE dispatchAuthQ aNoneAtomicE
   initPrin1KeyFuelB initPrin1KeyKB corruptKB genOpkKB registerKB
   roBaseShadowArmC roRootBaseShadowArmC syncRoBothC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (dropShadow0 dropShadow1 liftAuthPrim1 syncShcrShadowRespC shcrBaseArmC
   shcrKindInitC shcrKindHandlePreC shcrKindChDoneC shcrKindResumeC shcrKindHandlePostC
   shcrKindFinishC shcrAuth1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
  (dispatchAuthQ_v1_costAt_kind1_le dispatchAuthQ_v1_costAt_kind0_le
   dispatchAuthQ_cost_le dispatchAuthQ_queries_le dispatchAuthQ_size_le
   roBaseShadowArmC_cost_le roBaseShadowArmC_queries_zero roBaseShadowArmC_size_le
   roRootBaseShadowArmC_cost_le roRootBaseShadowArmC_queries_zero roRootBaseShadowArmC_size_le
   syncRoBothC_cost_le syncRoBothC_queries_zero syncRoBothC_size_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedHs
  (initPrin1KeyKB_cost_le initPrin1KeyKB_r64_le initPrin1KeyKB_queries_prim_le
   corruptKB_cost_le corruptKB_r64_le corruptKB_queries_prim_le
   genOpkKB_cost_le genOpkKB_r64_le genOpkKB_queries_prim_le
   registerKB_cost_le registerKB_r64_le registerKB_queries_prim_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCost
  (shcrSendKC_cost_le shcrSendKC_r64_le shcrSendKC_queries_prim_le
   shcrSendKC_size_le shcrSendKC_litSize_le
   shcrAcceptKB_cost_le shcrAcceptKB_r64_le shcrAcceptKB_queries_prim_le
   shcrAcceptKB_size_le shcrAcceptKB_litSize_le
   shcrResumeKC_cost_le shcrResumeKC_r64_le shcrResumeKC_queries_prim_le
   shcrResumeKC_size_le shcrResumeKC_litSize_le)

section ShcrBounds

private theorem sampR64W_tlAuthPrim : sampR64W tlAuthPrim.hsmp = sampR64W rfl := rfl

private theorem emptyRoBothAvlE_cost_le {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).cost ≤ 500 := by
  change (emptyRoBothAvlE (Γ := [])).cost ≤ 500; decide

private theorem emptyRoBothAvlE_size_le {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).size ≤ 500 := by
  change (emptyRoBothAvlE (Γ := [])).size ≤ 500; decide

private theorem liftAuthPrim1_cost_two_mul_le {a r : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [a] r) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (embedTy a)) :
    2 * (liftAuthPrim1 c e).cost ≤
      4 + 2 * e.cost + 3 * c.cost + 78 * c.queries (fun _ => 0) (sampR64W rfl) := by
  have hm := mapComp_cost_two_mul_le tlAuthPrim c
  rw [sampR64W_tlAuthPrim] at hm
  unfold liftAuthPrim1
  simp only [Comp.cost]
  rw [compRename_cost]
  omega

private theorem liftAuthPrim1_queries_prim_le {a r : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [a] r) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (embedTy a)) :
    (liftAuthPrim1 c e).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      c.queries (fun _ => 1) (fun _ => 0) := by
  have hm := mapComp_queries_le tlAuthPrim (fun _ => 1) (fun _ => 0)
    authPrimIfacePrimQueryWeight tlAuthPrim_primW c
  unfold liftAuthPrim1 samplerZeroQueryWeight
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact hm

private theorem liftAuthPrim1_size_le {a r : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [a] r) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (embedTy a)) :
    (liftAuthPrim1 c e).size ≤ 2 + e.size + 10 * c.size + compLitSize c := by
  have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe c
  unfold liftAuthPrim1
  simp only [Comp.size]
  rw [compRename_size]
  omega

private theorem syncShcr_roCacheE_cost_eq {Γ : List (Ty pqAtomicSig)} :
    (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      (.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy :: Γ) _))))).cost =
    (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      [.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy] _))))).cost := rfl

private theorem syncShcr_rootRoCacheE_cost_eq {Γ : List (Ty pqAtomicSig)} :
    (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      (.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy :: Γ) _))))).cost =
    (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      [.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy] _))))).cost := rfl

private theorem syncShcrShadowRespC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (scsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy (embedTy shcrStTy)))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncShcrShadowRespC cap scsE roBothE).cost ≤
      8500 * bits cap + 1965 + scsE.cost + roBothE.cost := by
  have h1 : (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      (.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy :: Γ) _))))).cost ≤ 48 := by
    rw [syncShcr_roCacheE_cost_eq]; decide
  have h2 : (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      (.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy :: Γ) _))))).cost ≤ 48 := by
    rw [syncShcr_rootRoCacheE_cost_eq]; decide
  have hs := syncRoBothC_cost_le (I := pqAuthPrimIface) cap
    (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      (.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy :: Γ) _)))))
    (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps
      (.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy :: Γ) _)))))
    (.snd .v0)
  unfold syncShcrShadowRespC
  simp only [Expr.v0] at h1 h2
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hs ⊢
  omega

private theorem syncShcrShadowRespC_queries_zero (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (scsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy (embedTy shcrStTy)))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncShcrShadowRespC cap scsE roBothE).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  unfold syncShcrShadowRespC
  simp only [Comp.queries, syncRoBothC_queries_zero, Nat.add_zero]

private theorem wrapInl_cost (S : Setup) {a : Ty pqAtomicSig}
    (m : Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
          (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy))))).cost =
      m.cost + 4 := by
  simp only [Comp.cost, Expr.cost, Expr.v0]

private theorem wrapInl_queries (S : Setup) {a : Ty pqAtomicSig}
    (m : Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
          (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy))))).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight =
      m.queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight := by
  simp only [Comp.queries, Nat.add_zero]

theorem shcrKindInitC_cost_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindInitC S F).cost ≤
      1200 + 8 * Nat.log 2 S.N_dh + 8 * Nat.log 2 S.N_sess_tot := by
  have hc := shcr_init_cost_le_tight S F.K_on F.K_on
  have hr64 : (shcrReductionAuthProg S F.K_on F.K_on).init.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
    have hbool : sampR64W tlAuthPrim.hsmp _root_.SignalPqxdh.LegacyCosted.PSamp.bool = 0 := rfl
    have hidx : ∀ n, sampR64W tlAuthPrim.hsmp (_root_.SignalPqxdh.LegacyCosted.PSamp.index n) = 0 := fun _ => rfl
    dsimp only [shcrReductionAuthProg]
    split_ifs <;> simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
      _root_.ReductionDsl.Comp.sampleBool, _root_.ReductionDsl.Comp.sampleIndex, hbool, hidx, Comp.queries]
  have hm := mapComp_cost_two_mul_le tlAuthPrim (shcrReductionAuthProg S F.K_on F.K_on).init
  have he := emptyRoBothAvlE_cost_le (Γ := [.prod .unit (embedTy shcrStTy), .prod (PB 1568) (PB 3168)])
  unfold shcrKindInitC; simp only [Comp.cost, Expr.cost, Expr.v0]; omega

theorem shcrKindHandlePreC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy shcrStTy) roBothAvlTy).denote) (q : AuthQuery S) (hk : authQueryKind q = 1) :
    (shcrKindHandlePreC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  dsimp only [shcrKindHandlePreC]
  refine le_trans (dispatchAuthQ_v1_costAt_kind1_le _ _ _ _ _ _ _ _ _ _ _ _ s q .nil
    (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (roBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (roRootBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem shcrBaseArmC_cost_two_mul_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ], Var Γ₁ authStateTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RS)
    {Γ : List (Ty pqAtomicSig)} {C R : ℕ}
    (hc : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ authStateTy) (x : Var Γ₂ arg), (step (Δ := Δ) st x).cost ≤ C)
    (hr : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ authStateTy) (x : Var Γ₂ arg),
      (step (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) ≤ R) :
    2 * (shcrBaseArmC S step (Γ := Γ)).cost ≤ 72 + 3 * C + 78 * R := by
  let Δa := [arg, authStateTy, .prod authStateTy arg]
  have hl := liftAuthPrim1_cost_two_mul_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x => step st x)
    (.pair (.fst (.fst .v1)) .v0 : Expr pqAtomicOps (embedTy arg :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hc' : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (Γ := [.prod authStateTy arg]) (.fst (.var .zero)) fun st =>
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x => step st x).cost ≤ 8 + C := by
    have h0 := hc (Γ₁ := [authStateTy, .prod authStateTy arg]) (Γ₂ := Δa) (Δ := Δa) .vz .vz
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV, _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost]; omega
  have hr' : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (Γ := [.prod authStateTy arg]) (.fst (.var .zero)) fun st =>
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
      step st x).queries (fun _ => 0) (sampR64W rfl) ≤ R := by
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV, _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.zero_add] using
      hr (Γ₁ := [authStateTy, .prod authStateTy arg]) (Γ₂ := Δa) (Δ := Δa) .vz .vz
  unfold shcrBaseArmC; simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hl ⊢; omega

private theorem shcrBaseArmC_queries_prim_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ], Var Γ₁ authStateTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RS)
    {Γ : List (Ty pqAtomicSig)} {Q : ℕ}
    (hq : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ authStateTy) (x : Var Γ₂ arg),
      (step (Δ := Δ) st x).queries (fun _ => 1) (fun _ => 0) ≤ Q) :
    (shcrBaseArmC S step (Γ := Γ)).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  let Δa := [arg, authStateTy, .prod authStateTy arg]
  have hl := liftAuthPrim1_queries_prim_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x => step st x)
    (.pair (.fst (.fst .v1)) .v0 : Expr pqAtomicOps (embedTy arg :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have h0 := hq (Γ₁ := [authStateTy, .prod authStateTy arg]) (Γ₂ := Δa) (Δ := Δa) .vz .vz
  unfold shcrBaseArmC
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV, _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.add_zero, Nat.zero_add] at hl ⊢
  exact le_trans hl h0

private theorem shcrGenSpkB_r64_le (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).queries (fun _ => 0) (sampR64W rfl) ≤ 3 := by
  change (shcrGenSpkB (Δ := Δ) S K s x).queries (fun _ => 0) r64W ≤ 3
  simp only [shcrGenSpkB, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV, _root_.ReductionDsl.Comp.iteC, _root_.ReductionDsl.Comp.caseOptC,
    _root_.ReductionDsl.Comp.letC, _root_.ReductionDsl.Comp.sampleBytes32, _root_.ReductionDsl.Comp.sampleRandom64,
    _root_.ReductionDsl.Comp.queryPrim, r64W, Comp.queries]; omega

private theorem tryPauseC_r64_eq (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (tryPauseC (Δ := Δ) S K opk s x).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp only [tryPauseC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.preCheckC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.checkSigsC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.findHonestC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.koskBundleOkC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.resolveSigPkC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.isAdvRegC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.isGameSpkC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.isGameOpkC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.findMV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.anyMV,
    _root_.ReductionDsl.Comp.iteC, _root_.ReductionDsl.Comp.caseOptC, _root_.ReductionDsl.Comp.letC,
    _root_.ReductionDsl.Comp.findBoundedM, _root_.ReductionDsl.Comp.anyBoundedM, _root_.ReductionDsl.Comp.queryPrim, Comp.queries]; omega

private theorem aNoneAtomicE_cost_eq {Γ : List (Ty pqAtomicSig)} :
    (aNoneAtomicE (Γ := Γ)).cost = (aNoneAtomicE (Γ := [])).cost :=
  rfl

private theorem aNoneAtomicE_cost_le {Γ : List (Ty pqAtomicSig)} :
    (aNoneAtomicE (Γ := Γ)).cost ≤ 30 := by
  rw [aNoneAtomicE_cost_eq]
  decide

private abbrev shcrGenSpkStep (S : Setup) (F : AuthKindFuels) :
    Comp pqxdhOps pqPrimIface [.prod shcrStTy (.prod .nat .nat)] _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
  shcrGenSpkB S F.K_on s x

private abbrev shcrSendStep (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqPrimIface [.prod shcrStTy sendQTy] _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
  AuthCoreKArms.shcrSendKC S F.K_on F.K_ro opk s x

private abbrev shcrRecvStep (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqPrimIface [.prod shcrStTy recvQTy] _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
  AuthCoreKArms.shcrAcceptKB S F.K_on F.K_ro opk s x

private abbrev shcrPauseStep (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqPrimIface [.prod shcrStTy sendQTy] (.opt (.prod (B 1568) pauseTy)) :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV (tryPauseC S F.K_on opk s x) fun p =>
  .ret (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v p) .noneE fun d =>
    .someE (.pair (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.buPqspkB
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pdBu
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d)))
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d)))

private abbrev shcrGenSpkArmC (S : Setup) (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface (.prod .nat .nat :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ)
      (.prod authRespAtomicTy (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1 (shcrGenSpkStep S F) (.pair (.fst .v1) .v0))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))

private abbrev shcrSendArmC (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (.prod (embedTy shcrStTy) authSendQAtomicTy))
    (roBothE : Expr pqAtomicOps (.prod authRespAtomicTy (embedTy shcrStTy) :: Γ) roBothAvlTy) :
    Comp pqAtomicOps pqAuthPrimIface Γ (.prod authRespAtomicTy (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1 (shcrSendStep S F opk) argE) (syncShcrShadowRespC F.K_cap .v0 roBothE)

private abbrev shcrRecvArmC (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ)
      (.prod authRespAtomicTy (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1 (shcrRecvStep S F opk) (.pair (.fst .v1) .v0))
    (syncShcrShadowRespC F.K_cap .v0 (.snd .v2))

private abbrev shcrSendPreArmC (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ)
      (.sum (.prod authRespAtomicTy (.prod (embedTy shcrStTy) roBothAvlTy))
        (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy)))) :=
  .bind (liftAuthPrim1 (shcrPauseStep S F opk) (.pair (.fst .v1) .v0))
    (.caseOpt .v0
      (.bind (shcrSendArmC S F opk (.pair (.fst .v2) .v1) (.snd .v3)) (.ret (.inl .v0)))
      (.ret (.inr (.pair (.fst .v0) (.pair (.snd .v0) .v3)))))

private theorem shcrGenSpkArm_cost_le (S : Setup) (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)} :
    (shcrGenSpkArmC S F (Γ := Γ)).cost ≤ 38000 + 150 * F.K_on := by
  let Δg := [Ty.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)]
  have hl := liftAuthPrim1_cost_two_mul_le (shcrGenSpkStep S F)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (.prod .nat .nat :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have h1 := Comp.cost_le_costUB (shcrGenSpkB S F.K_on (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _) (.vz : Var Δg _) (Δ := Δg))
  have h2 := shcrGenSpkB_costUB_le_tight S F.K_on (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _) (.vz : Var Δg _) (Δ := Δg)
  have h3 := shcrGenSpkB_r64_le S F.K_on (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _) (.vz : Var Δg _) (Δ := Δg)
  simp only [shcrGenSpkStep, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries, Expr.v0, Expr.v1, Expr.v2] at hl ⊢; omega

private theorem shcrSendArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (.prod (embedTy shcrStTy) authSendQAtomicTy))
    (roBothE : Expr pqAtomicOps (.prod authRespAtomicTy (embedTy shcrStTy) :: Γ) roBothAvlTy)
    (hArg : argE.cost ≤ 5) (hRo : roBothE.cost ≤ 5) :
    (shcrSendArmC S F opk argE roBothE).cost ≤
      18700 + 5355 * F.K_on + 1545 * min F.K_on S.N_dh + 797 * F.K_ro + (8500 * bits F.K_cap + 1975) := by
  let Δs := [sendQTy, shcrStTy, .prod shcrStTy sendQTy]
  have hl := liftAuthPrim1_cost_two_mul_le (shcrSendStep S F opk) argE
  have hc := shcrSendKC_cost_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs)
  have hr := shcrSendKC_r64_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs)
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (syncShcrShadowRespC_cost_le F.K_cap _ _) _) 1) ?_
  simp only [shcrSendStep, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries, Expr.v0] at hl ⊢; omega

private theorem shcrRecvArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    (shcrRecvArmC S F opk (Γ := Γ)).cost ≤
      24200 + 555 * F.K_on + 618 * min F.K_on S.N_dh + 797 * F.K_ro + (8500 * bits F.K_cap + 1975) := by
  let Δr := [recvQTy, shcrStTy, .prod shcrStTy recvQTy]
  have hl := liftAuthPrim1_cost_two_mul_le (shcrRecvStep S F opk)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hc := shcrAcceptKB_cost_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _) (.vz : Var Δr _) (Δ := Δr)
  have hr := shcrAcceptKB_r64_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _) (.vz : Var Δr _) (Δ := Δr)
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (syncShcrShadowRespC_cost_le F.K_cap _ _) _) 1) ?_
  simp only [shcrRecvStep, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries, Expr.v0, Expr.v1, Expr.v2] at hl ⊢; omega

private theorem shcrSendPreArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    (shcrSendPreArmC S F opk (Γ := Γ)).cost ≤
      44978 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro + (8500 * bits F.K_cap + 2055) := by
  let Δs := [sendQTy, shcrStTy, .prod shcrStTy sendQTy]
  have hl := liftAuthPrim1_cost_two_mul_le (shcrPauseStep S F opk)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hp1 := Comp.cost_le_costUB (tryPauseC S F.K_on opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs))
  have hp2 := tryPauseC_costUB S F.K_on opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs)
  have hp3 := tryPauseC_r64_eq S F.K_on opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs)
  have hpe : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v (.vz : Var [.opt pauseTy, sendQTy, shcrStTy, .prod shcrStTy sendQTy] _)) .noneE fun d =>
      .someE (.pair (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.buPqspkB
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pdBu
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d)))
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d)) :
      Expr pqxdhOps [.opt pauseTy, sendQTy, shcrStTy, .prod shcrStTy sendQTy] _).cost ≤ 30 := by decide
  have hsnd := shcrSendArm_cost_le S F opk
    (.pair (.fst .v2) .v1 : Expr pqAtomicOps (embedTy (.opt (.prod (B 1568) pauseTy)) ::
      authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
    (.snd .v3) (by simp [Expr.cost, Expr.v1, Expr.v2]) (by simp [Expr.cost, Expr.v3])
  simp only [shcrPauseStep, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV, _root_.ReductionDsl.Comp.letC,
    Comp.cost, Expr.cost, Comp.queries, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hl hsnd ⊢; omega

private theorem shcrKindHandlePreC_cost_le_aux (S : Setup) (F : AuthKindFuels) :
    (shcrKindHandlePreC S F).cost ≤
      45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  dsimp only [shcrKindHandlePreC]
  refine le_trans (dispatchAuthQ_cost_le _ _ _ _ _ _ _ _ _ _ _ _ _
    (B := 44978 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro + (8500 * bits F.K_cap + 2058))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by simp [Expr.cost]; omega)
  · rw [wrapInl_cost S]
    have h := shcrBaseArmC_cost_two_mul_le S (fun st u => initPrin1KeyKB F st u)
      (Γ := [(authCodec S).Q]) (initPrin1KeyKB_cost_le F) (fun st u => le_of_eq (initPrin1KeyKB_r64_le F st u))
    omega
  · rw [wrapInl_cost S]
    have h := shcrBaseArmC_cost_two_mul_le S (fun st u => corruptKB F st u)
      (Γ := [(authCodec S).Q]) (corruptKB_cost_le F) (fun st u => le_of_eq (corruptKB_r64_le F st u))
    omega
  · rw [wrapInl_cost S]
    exact le_trans (Nat.add_le_add_right (shcrGenSpkArm_cost_le S F (Γ := [(authCodec S).Q])) 4) (by omega)
  · rw [wrapInl_cost S]
    have h := shcrBaseArmC_cost_two_mul_le S (fun st x => genOpkKB F st x)
      (Γ := [(authCodec S).Q]) (genOpkKB_cost_le F) (fun st x => le_of_eq (genOpkKB_r64_le F st x))
    omega
  · exact le_trans (shcrSendPreArm_cost_le S F true) (by omega)
  · exact le_trans (shcrSendPreArm_cost_le S F false) (by omega)
  · rw [wrapInl_cost S]
    exact le_trans (Nat.add_le_add_right (shcrRecvArm_cost_le S F true (Γ := [(authCodec S).Q])) 4) (by omega)
  · rw [wrapInl_cost S]
    exact le_trans (Nat.add_le_add_right (shcrRecvArm_cost_le S F false (Γ := [(authCodec S).Q])) 4) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (roBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (roRootBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost, Expr.cost, Expr.v1]
    change (aNoneAtomicE (Γ := [])).cost + 1 + 1 + 1 + 1 ≤ _
    have h := aNoneAtomicE_cost_le (Γ := [])
    omega
  · rw [wrapInl_cost S]
    have h := shcrBaseArmC_cost_two_mul_le S (fun st sk => registerKB st sk)
      (Γ := [(authCodec S).Q]) registerKB_cost_le (fun st sk => le_of_eq (registerKB_r64_le st sk))
    omega

theorem shcrKindHandlePreC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy shcrStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (_hk : authQueryKind q = 0) :
    (shcrKindHandlePreC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  le_trans (Comp.costAt_le_cost (shcrKindHandlePreC S F) _) (shcrKindHandlePreC_cost_le_aux S F)

theorem shcrKindHandlePreC_cost_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindHandlePreC S F).cost ≤
      45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  shcrKindHandlePreC_cost_le_aux S F

theorem shcrKindChDoneC_cost_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindChDoneC S F).cost ≤ 100 := by
  have hc := shcr_chDone_cost_le S F.K_on F.K_on
  have hm := mapComp_cost_eleven_mul_le tlAuthPrim (shcrReductionAuthProg S F.K_on F.K_on).chDone
  unfold shcrKindChDoneC; simp only [Comp.cost, Expr.cost, Expr.v0]; rw [compRename_cost]; omega

theorem shcrKindFinishC_cost_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindFinishC S F).cost ≤ 200 + 18000 * F.K_on := by
  have hc := shcr_finish_cost_le S F.K_on F.K_on
  have hr64 : (shcrReductionAuthProg S F.K_on F.K_on).finish.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
    rw [sampR64W_tlAuthPrim]
    simp [shcrReductionAuthProg, shcrExtractC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.findMV, _root_.ReductionDsl.Comp.queryPrim, Comp.queries]
  have hm := mapComp_cost_two_mul_le tlAuthPrim (shcrReductionAuthProg S F.K_on F.K_on).finish
  unfold shcrKindFinishC; simp only [Comp.cost, Expr.cost, Expr.v0]; rw [compRename_cost]; omega

theorem shcrKindInitC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindInitC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq := shcr_init_queries S F.K_on F.K_on
  have hm := mapComp_queries_le tlAuthPrim _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primWS authPrimIfacePrimQueryWeight tlAuthPrim_primW
    (shcrReductionAuthProg S F.K_on F.K_on).init
  apply Nat.eq_zero_of_le_zero; unfold shcrKindInitC; simp only [Comp.queries, Nat.add_zero]
  exact le_trans hm (by omega)

private theorem shcrSendPreArm_queries_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    (shcrSendPreArmC S F opk (Γ := Γ)).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh := by
  let Δs := [sendQTy, shcrStTy, .prod shcrStTy sendQTy]
  have hl1 := liftAuthPrim1_queries_prim_le (shcrPauseStep S F opk)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hl2 := liftAuthPrim1_queries_prim_le (shcrSendStep S F opk)
    (.pair (.fst .v2) .v1 : Expr pqAtomicOps (embedTy (.opt (.prod (B 1568) pauseTy)) ::
      authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hqp : (tryPauseC S F.K_on opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _)
      (.vz : Var Δs _) (Δ := Δs)).queries (fun _ => 1) (fun _ => 0) ≤ 5 + 10 * min F.K_on S.N_dh :=
    le_of_eq (tryPauseC_queries S F.K_on opk _ _)
  have hqs : (AuthCoreKArms.shcrSendKC S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _)
      (.vz : Var Δs _) (Δ := Δs)).queries (fun _ => 1) (fun _ => 0) ≤ 20 + 10 * min F.K_on S.N_dh :=
    shcrSendKC_queries_prim_le S F.K_on F.K_ro opk _ _
  have hm := Nat.min_le_right F.K_on S.N_dh
  simp only [Comp.queries]
  rw [syncShcrShadowRespC_queries_zero]
  simp only [shcrPauseStep, shcrSendStep,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
    _root_.ReductionDsl.Comp.letC, Comp.queries] at hl1 hl2 ⊢
  omega

private theorem shcrRecvArm_queries_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    (shcrRecvArmC S F opk (Γ := Γ)).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh := by
  let Δr := [recvQTy, shcrStTy, .prod shcrStTy recvQTy]
  have hl := liftAuthPrim1_queries_prim_le (shcrRecvStep S F opk)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hqa : (AuthCoreKArms.shcrAcceptKB S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _)
      (.vz : Var Δr _) (Δ := Δr)).queries (fun _ => 1) (fun _ => 0) ≤ 22 + 4 * min F.K_on S.N_dh :=
    shcrAcceptKB_queries_prim_le S F.K_on F.K_ro opk _ _
  have hm := Nat.min_le_right F.K_on S.N_dh
  simp only [Comp.queries]
  rw [syncShcrShadowRespC_queries_zero]
  simp only [shcrRecvStep, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.queries] at hl ⊢
  omega

theorem shcrKindHandlePreC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindHandlePreC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh := by
  dsimp only [shcrKindHandlePreC]
  refine dispatchAuthQ_queries_le (I := pqAuthPrimIface) (Q := 40 + 30 * S.N_dh)
    _ _ _ _ _ _ _ _ _ _ _ _ _ authPrimIfacePrimQueryWeight samplerZeroQueryWeight
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [wrapInl_queries S]
    exact le_trans (shcrBaseArmC_queries_prim_le S (fun st u => initPrin1KeyKB F st u)
      (Γ := [(authCodec S).Q]) (initPrin1KeyKB_queries_prim_le F)) (by omega)
  · rw [wrapInl_queries S]
    exact le_trans (shcrBaseArmC_queries_prim_le S (fun st u => corruptKB F st u)
      (Γ := [(authCodec S).Q]) (fun st u => le_of_eq (corruptKB_queries_prim_le F st u))) (by omega)
  · rw [wrapInl_queries S]
    have hl := liftAuthPrim1_queries_prim_le (shcrGenSpkStep S F)
      (.pair (.fst .v1) .v0 : Expr pqAtomicOps (.prod .nat .nat :: .prod (embedTy shcrStTy) roBothAvlTy :: [(authCodec S).Q]) _)
    have hq : (shcrGenSpkB S F.K_on (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
        (.vz : Var [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
        (Δ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])).queries (fun _ => 1) (fun _ => 0) = 4 :=
      shcrGenSpkB_queries S F.K_on _ _
    simp only [shcrGenSpkStep, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
      _root_.ReductionDsl.Comp.letC, Comp.queries] at hl ⊢; omega
  · rw [wrapInl_queries S]
    exact le_trans (shcrBaseArmC_queries_prim_le S (fun st x => genOpkKB F st x)
      (Γ := [(authCodec S).Q]) (genOpkKB_queries_prim_le F)) (by omega)
  · exact shcrSendPreArm_queries_prim_le S F true
  · exact shcrSendPreArm_queries_prim_le S F false
  · rw [wrapInl_queries S]; exact shcrRecvArm_queries_prim_le S F true (Γ := [(authCodec S).Q])
  · rw [wrapInl_queries S]; exact shcrRecvArm_queries_prim_le S F false (Γ := [(authCodec S).Q])
  · rw [wrapInl_queries S]; simp only [Comp.queries]; unfold samplerZeroQueryWeight
    rw [roBaseShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap]; omega
  · rw [wrapInl_queries S]; simp only [Comp.queries]; unfold samplerZeroQueryWeight
    rw [roRootBaseShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap]; omega
  · simp only [Comp.queries]; omega
  · rw [wrapInl_queries S]
    exact le_trans (shcrBaseArmC_queries_prim_le S (fun st sk => registerKB st sk)
      (Γ := [(authCodec S).Q]) registerKB_queries_prim_le) (by omega)

theorem shcrKindChDoneC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindChDoneC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq := shcr_chDone_queries S F.K_on F.K_on
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW
    (shcrReductionAuthProg S F.K_on F.K_on).chDone
  apply Nat.eq_zero_of_le_zero
  unfold shcrKindChDoneC
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact le_trans hm (by omega)

theorem shcrKindFinishC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindFinishC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      F.K_on := by
  have hq := shcr_finish_queries S F.K_on F.K_on
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW
    (shcrReductionAuthProg S F.K_on F.K_on).finish
  unfold shcrKindFinishC
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact le_trans hm (by omega)

section ShcrSizeHelpers

private theorem bits_fuels_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    bits F.K_on ≤ bits (stepCostBudget S b) ∧ bits F.K_on1 ≤ bits (stepCostBudget S b) ∧
    bits F.K_ro ≤ bits (stepCostBudget S b) ∧ bits (min F.K_on S.N_dh) ≤ bits (stepCostBudget S b) ∧
    bits (avlHeightCap F.K_cap) ≤ bits (stepCostBudget S b) := by
  intro F
  have hbmono : ∀ {x y : ℕ}, x ≤ y → bits x ≤ bits y := fun h => by
    unfold bits; exact Nat.add_le_add_right (Nat.log_mono_right h) 1
  have hBud : 6 * b.q_total + 6 ≤ stepCostBudget S b := by
    have h0 : 6 * b.q_total + 6 ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) := by nlinarith
    unfold stepCostBudget; dsimp only; omega
  have hOn := AuthCoreK.AuthKindFuels.K_on_le_q_total S b
  have hOn1 := AuthCoreK.AuthKindFuels.K_on1_le_q_total S b
  have hRo := AuthCoreK.AuthKindFuels.K_ro_le_q_total S b
  have hCap : F.K_cap ≤ 3 * b.q_total + 1 := by
    dsimp [F, AuthKindFuels.ofBudget]
    have := Nat.min_le_right b.q_on b.q_total
    have := Nat.min_le_right (b.q_ro + b.q_roRoot) b.q_total; omega
  have h1 : bits F.K_cap ≤ F.K_cap + 1 := by
    rcases Nat.eq_zero_or_pos F.K_cap with h0 | hn
    · rw [h0]; decide
    · unfold bits; have := (Nat.log_lt_iff_lt_pow (by decide) (Nat.ne_of_gt hn)).mpr Nat.lt_two_pow_self; omega
  have hAvl : avlHeightCap F.K_cap ≤ stepCostBudget S b := by dsimp [avlHeightCap]; omega
  dsimp only [F] at *
  exact ⟨hbmono (by omega), hbmono (by omega), hbmono (by omega),
    hbmono (Nat.le_trans (Nat.min_le_left _ _) (by omega)), hbmono hAvl⟩

private theorem syncShcrShadowRespC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (scsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy (embedTy shcrStTy)))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncShcrShadowRespC cap scsE roBothE).size ≤
      3900 + 4 * bits (avlHeightCap cap) + scsE.size + roBothE.size := by
  let ty0 := Ty.prod (.prod authRespAtomicTy (embedTy shcrStTy)) roBothAvlTy
  have h1 : (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps (ty0 :: Γ) _))))).size ≤ 60 := by
    change (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps [ty0] _))))).size ≤ 60; decide
  have h2 : (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps (ty0 :: Γ) _))))).size ≤ 60 := by
    change (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps [ty0] _))))).size ≤ 60; decide
  have hs := syncRoBothC_size_le (I := pqAuthPrimIface) cap
    (baseRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps (ty0 :: Γ) _)))))
    (baseRootRoCacheE (.fst (.snd (.fst (.v0 : Expr pqAtomicOps (ty0 :: Γ) _))))) (.snd .v0)
  unfold syncShcrShadowRespC; simp only [Expr.v0] at h1 h2
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1] at hs ⊢; omega

private theorem aNoneAtomicE_size_eq {Γ : List (Ty pqAtomicSig)} :
    (aNoneAtomicE (Γ := Γ)).size = (aNoneAtomicE (Γ := [])).size := rfl

private theorem aNoneAtomicE_size_le {Γ : List (Ty pqAtomicSig)} :
    (aNoneAtomicE (Γ := Γ)).size ≤ 30 := by
  rw [aNoneAtomicE_size_eq]; decide

open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  onBase genSpkB corruptB genOpkB registerB sendGuardE preCheckC checkSigsC findHonestC
  isAdvRegC isGameSpkC isGameOpkC koskBundleOkC resolveSigPkC scBase scTB scTPk scTSk scCnt scIR scRR
  scSIdx scChosen scMk scUpd rrCt pdSid pdBu pdM0 pdM1 pdUI stSecb stHasWon stPrin stSpks
  stOpks stSess stUsedS stUsedO stUsedN stKyb stSOE stSNE stROE stRNE stRo stRoot stAdv stMk
  stUpd peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted peMk peUpd sbSpkSk sbSpkPk
  sbSpkSig sbPqspkSk sbPqspkPk sbPqspkSig sbRevealed sbMk oeOpkSk oeOpkPk oeConsumed oeMk oeUpd
  buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig buMk buUpd
  aNone aInitPrin aPk aCorr aBundle rs emptyAuthStE isSomeE getDBytes optFst optSnd dhOptNZ
  guardE kyberCheckE natEq nat2Eq nat3Eq optBytesEq optU32Eq sidEq kyberEq nonZero32
  v bindV letV caseOptV caseSumV findMV anyMV mapMV foldMV eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
  encEC encKEM F_X25519_length
)

set_option linter.unusedSimpArgs false in
local macro "shcr_leaf_sz" : tactic => `(tactic| (
  try dsimp only [shcrReductionAuthProg]
  try split_ifs
  all_goals
    simp (config := { maxSteps := 500000 }) only [
      initPrin1KeyKB, initPrin1KeyFuelB, corruptKB, genOpkKB, registerKB, shcrExtractC, shcrGenSpkB, tryPauseC,
      onBase, genSpkB, corruptB, genOpkB, registerB, sendGuardE, preCheckC, checkSigsC, findHonestC,
      isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, resolveSigPkC, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR,
      scSIdx, scChosen, scMk, scUpd, rrCt, pdSid, pdBu, pdM0, pdM1, pdUI, stSecb, stHasWon, stPrin, stSpks,
      stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk,
      stUpd, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd, sbSpkSk, sbSpkPk, sbSpkSig,
      sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, rs, emptyAuthStE, isSomeE, getDBytes, optFst, optSnd, dhOptNZ,
      guardE, kyberCheckE, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
      v, Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      eLet, eLet2, eCaseOpt, eCaseSum, eFind, eAny, eMap, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE,
      Expr.boolNot, Expr.boolAnd, Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded,
      Expr.mapBounded, Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM, Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden, Expr.bytesTakeK,
      Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint, Expr.u32OfNat, Expr.u32Beq,
      Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96, Comp.sampleIndex,
      Comp.queryPrim, encEC, encKEM, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, F_X25519_length,
      Nat.add_zero, Nat.zero_add, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    try dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have : bits 0 = 1 := by decide
    have : bits 1 = 1 := by decide
    have : bits 32 = 6 := by decide
    have : bits 64 = 7 := by decide
    have : bits 1568 = 11 := by decide
    omega))

set_option linter.unusedSimpArgs false in
private theorem shcrLeaf_sizes (S : Setup) (F : AuthKindFuels) :
    (shcrReductionAuthProg S F.K_on F.K_on).init.size ≤ 200 ∧
    compLitSize (shcrReductionAuthProg S F.K_on F.K_on).init ≤ 20 ∧
    (shcrReductionAuthProg S F.K_on F.K_on).chDone.size ≤ 20 ∧
    compLitSize (shcrReductionAuthProg S F.K_on F.K_on).chDone ≤ 20 ∧
    (shcrReductionAuthProg S F.K_on F.K_on).finish.size ≤ 400 + 2 * bits F.K_on ∧
    compLitSize (shcrReductionAuthProg S F.K_on F.K_on).finish ≤ 20 := by
  refine ⟨by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz⟩

set_option linter.unusedSimpArgs false in
private theorem shcrArmLeaf_sizes (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    let cIp := initPrin1KeyKB F (.vz : Var [authStateTy, .prod authStateTy .nat] _)
      (.vz : Var [.nat, authStateTy, .prod authStateTy .nat] _) (Δ := [.nat, authStateTy, .prod authStateTy .nat])
    let cCo := corruptKB F (.vz : Var [authStateTy, .prod authStateTy .nat] _)
      (.vz : Var [.nat, authStateTy, .prod authStateTy .nat] _) (Δ := [.nat, authStateTy, .prod authStateTy .nat])
    let cGo := genOpkKB F (.vz : Var [authStateTy, .prod authStateTy (.prod .nat (.prod .nat .nat))] _)
      (.vz : Var [.prod .nat (.prod .nat .nat), authStateTy, .prod authStateTy (.prod .nat (.prod .nat .nat))] _)
      (Δ := [.prod .nat (.prod .nat .nat), authStateTy, .prod authStateTy (.prod .nat (.prod .nat .nat))])
    let cRg := registerKB (.vz : Var [authStateTy, .prod authStateTy (B 32)] _)
      (.vz : Var [B 32, authStateTy, .prod authStateTy (B 32)] _) (Δ := [B 32, authStateTy, .prod authStateTy (B 32)])
    let cGs := shcrGenSpkB S F.K_on (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
      (.vz : Var [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] _) (Δ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
    let cTp := tryPauseC S F.K_on opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _)
      (.vz : Var [sendQTy, shcrStTy, .prod shcrStTy sendQTy] _) (Δ := [sendQTy, shcrStTy, .prod shcrStTy sendQTy])
    cIp.size ≤ 400 + 2 * bits F.K_on ∧ compLitSize cIp ≤ 20 ∧
    cCo.size ≤ 400 + 2 * bits F.K_on ∧ compLitSize cCo ≤ 20 ∧
    cGo.size ≤ 400 + 2 * bits F.K_on ∧ compLitSize cGo ≤ 20 ∧
    cRg.size ≤ 400 ∧ compLitSize cRg ≤ 20 ∧
    cGs.size ≤ 2000 + 10 * bits F.K_on ∧ compLitSize cGs ≤ 400 + 10 * bits F.K_on ∧
    cTp.size ≤ 2000 + 10 * bits F.K_on + 10 * bits (min F.K_on S.N_dh) ∧
    compLitSize cTp ≤ 200 + 10 * bits F.K_on + 10 * bits (min F.K_on S.N_dh) := by
  dsimp only
  cases opk <;> refine ⟨by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz,
    by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz, by shcr_leaf_sz⟩

private theorem shcrSendArm_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (.prod (embedTy shcrStTy) authSendQAtomicTy))
    (roBothE : Expr pqAtomicOps (.prod authRespAtomicTy (embedTy shcrStTy) :: Γ) roBothAvlTy)
    (hArg : argE.size ≤ 6) (hRo : roBothE.size ≤ 6) :
    (shcrSendArmC S F opk argE roBothE).size ≤
      97000 + 200 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
  let Δs := [sendQTy, shcrStTy, .prod shcrStTy sendQTy]
  have hl := liftAuthPrim1_size_le (shcrSendStep S F opk) argE
  have hz := shcrSendKC_size_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs)
  have hlt := shcrSendKC_litSize_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _) (.vz : Var Δs _) (Δ := Δs)
  simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (syncShcrShadowRespC_size_le F.K_cap _ _) _) 1) ?_
  simp only [shcrSendStep, letV, _root_.ReductionDsl.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Nat.zero_add] at hl ⊢; omega

private theorem shcrRecvArm_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    (shcrRecvArmC S F opk (Γ := Γ)).size ≤
      97000 + 200 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
  let Δr := [recvQTy, shcrStTy, .prod shcrStTy recvQTy]
  have hl := liftAuthPrim1_size_le (shcrRecvStep S F opk)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hz := shcrAcceptKB_size_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _) (.vz : Var Δr _) (Δ := Δr)
  have hlt := shcrAcceptKB_litSize_le S F.K_on F.K_ro opk (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _) (.vz : Var Δr _) (Δ := Δr)
  simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (syncShcrShadowRespC_size_le F.K_cap _ _) _) 1) ?_
  simp only [shcrRecvStep, letV, _root_.ReductionDsl.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2, Nat.zero_add] at hl ⊢; omega

private theorem shcrBaseArmC_size_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authStateTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RS)
    {Γ : List (Ty pqAtomicSig)} {Z L : ℕ}
    (hz : (step (Γ₁ := [authStateTy, .prod authStateTy arg])
      (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
      (Δ := [arg, authStateTy, .prod authStateTy arg]) .vz .vz).size ≤ Z)
    (hl : compLitSize (step (Γ₁ := [authStateTy, .prod authStateTy arg])
      (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
      (Δ := [arg, authStateTy, .prod authStateTy arg]) .vz .vz) ≤ L) :
    (shcrBaseArmC S step (Γ := Γ)).size ≤ 120 + 10 * Z + L := by
  have hm := liftAuthPrim1_size_le
    (letV (.fst (.var .zero)) fun st => letV (.snd (.var (.succ .zero))) fun x => step st x)
    (.pair (.fst (.fst .v1)) .v0 : Expr pqAtomicOps (embedTy arg :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  unfold shcrBaseArmC
  simp only [letV, _root_.ReductionDsl.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2, Nat.zero_add] at hm ⊢; omega

private theorem shcrGenSpkArm_size_le (S : Setup) (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)} :
    (shcrGenSpkArmC S F (Γ := Γ)).size ≤ 22000 + 110 * bits F.K_on := by
  obtain ⟨_, _, _, _, _, _, _, _, hGsS, hGsL, _, _⟩ := shcrArmLeaf_sizes S F true
  have hm := liftAuthPrim1_size_le (shcrGenSpkStep S F)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (.prod .nat .nat :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  simp only [shcrGenSpkStep, letV, _root_.ReductionDsl.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2, Nat.zero_add] at hm ⊢; omega

private theorem shcrSendPreArm_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    (shcrSendPreArmC S F opk (Γ := Γ)).size ≤
      120000 + 320 * bits F.K_on + 120 * bits (min F.K_on S.N_dh) + 100 * bits F.K_ro +
        4 * bits (avlHeightCap F.K_cap) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hTpS, hTpL⟩ := shcrArmLeaf_sizes S F opk
  have hl := liftAuthPrim1_size_le (shcrPauseStep S F opk)
    (.pair (.fst .v1) .v0 : Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hpeS : (eCaseOpt (v (.vz : Var [.opt pauseTy, sendQTy, shcrStTy, .prod shcrStTy sendQTy] _))
      .noneE fun d => .someE (.pair (buPqspkB (pdBu (v d))) (v d)) :
      Expr pqxdhOps [.opt pauseTy, sendQTy, shcrStTy, .prod shcrStTy sendQTy] _).size ≤ 30 := by decide
  have hpeL : exprLitSize (eCaseOpt (v (.vz : Var [.opt pauseTy, sendQTy, shcrStTy, .prod shcrStTy sendQTy] _))
      .noneE fun d => .someE (.pair (buPqspkB (pdBu (v d))) (v d)) :
      Expr pqxdhOps [.opt pauseTy, sendQTy, shcrStTy, .prod shcrStTy sendQTy] _) = 0 := by decide
  have hsnd := shcrSendArm_size_le S F opk
    (.pair (.fst .v2) .v1 : Expr pqAtomicOps (embedTy (.opt (.prod (B 1568) pauseTy)) ::
      authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
    (.snd .v3) (by simp [Expr.size, Expr.v1, Expr.v2]) (by simp [Expr.size, Expr.v3])
  simp only [shcrPauseStep, letV, bindV, _root_.ReductionDsl.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Nat.zero_add] at hl hsnd ⊢; omega

private theorem wrapInl_size (S : Setup) {a : Ty pqAtomicSig}
    (m : Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
          (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy))))).size =
      m.size + 4 := by
  simp only [Comp.size, Expr.size, Expr.v0]

private theorem wrapInl_size_le (S : Setup) {a : Ty pqAtomicSig}
    {m : Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))} {B : ℕ}
    (h : m.size ≤ B) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
          (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy))))).size ≤
      B + 4 := by
  rw [wrapInl_size S]; omega

private theorem dispatchAuthQ_size_le_of_arms {out : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (qE : Expr pqAtomicOps Γ authQueryAtomicTy)
    (a1 a2 : Comp pqAtomicOps pqAuthPrimIface (.nat :: Γ) out)
    (a3 : Comp pqAtomicOps pqAuthPrimIface (.prod .nat .nat :: Γ) out)
    (a4 : Comp pqAtomicOps pqAuthPrimIface (.prod .nat (.prod .nat .nat) :: Γ) out)
    (a5 a6 : Comp pqAtomicOps pqAuthPrimIface (authSendQAtomicTy :: Γ) out)
    (a7 a8 : Comp pqAtomicOps pqAuthPrimIface (authRecvQAtomicTy :: Γ) out)
    (a9 : Comp pqAtomicOps pqAuthPrimIface (PB 192 :: Γ) out)
    (a10 : Comp pqAtomicOps pqAuthPrimIface (.prod (PB 32) (PB 32) :: Γ) out)
    (a11 : Comp pqAtomicOps pqAuthPrimIface (.unit :: Γ) out)
    (a12 : Comp pqAtomicOps pqAuthPrimIface (PB 32 :: Γ) out)
    {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : ℕ}
    (h1 : a1.size ≤ b1) (h2 : a2.size ≤ b2) (h3 : a3.size ≤ b3) (h4 : a4.size ≤ b4)
    (h5 : a5.size ≤ b5) (h6 : a6.size ≤ b6) (h7 : a7.size ≤ b7) (h8 : a8.size ≤ b8)
    (h9 : a9.size ≤ b9) (h10 : a10.size ≤ b10) (h11 : a11.size ≤ b11) (h12 : a12.size ≤ b12) :
    (dispatchAuthQ qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12).size ≤
      qE.size + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + 21 := by
  have hd := dispatchAuthQ_size_le qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  omega

end ShcrSizeHelpers

theorem shcrAuth1KeyKindProg_size_le (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyKindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  let F := AuthKindFuels.ofBudget S b
  obtain ⟨hInitS, hInitL, hChS, hChL, hFinS, hFinL⟩ := shcrLeaf_sizes S F
  obtain ⟨hIpS, hIpL, hCoS, hCoL, hGoS, hGoL, hRgS, hRgL, _, _, _, _⟩ := shcrArmLeaf_sizes S F true
  obtain ⟨hbOn, hbOn1, hbRo, hbDh, hbAvl⟩ := bits_fuels_le_stepCostBudget S b
  have hInit : (shcrKindInitC S F).size ≤ 3000 := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (shcrReductionAuthProg S F.K_on F.K_on).init
    have he := emptyRoBothAvlE_size_le (Γ := [.prod .unit (embedTy shcrStTy), .prod (PB 1568) (PB 3168)])
    unfold shcrKindInitC; simp only [Comp.size, Expr.size, Expr.v0]; omega
  have hCh : (shcrKindChDoneC S F).size ≤ 500 := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (shcrReductionAuthProg S F.K_on F.K_on).chDone
    unfold shcrKindChDoneC; simp only [Comp.size, Expr.size, Expr.v0, compRename_size]; omega
  have hFin : (shcrKindFinishC S F).size ≤ 4500 + 20 * bits F.K_on := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (shcrReductionAuthProg S F.K_on F.K_on).finish
    unfold shcrKindFinishC; simp only [Comp.size, Expr.size, Expr.v0, compRename_size]; omega
  have hRes : (shcrKindResumeC S F).size ≤
      68000 + 200 * bits F.K_on1 + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
    have hm := liftAuthPrim1_size_le
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.snd (.var (.succ .zero)))) fun d =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.snd (.var (.succ (.succ .zero))))) fun sc =>
       AuthCoreKArms.shcrResumeKC F.K_on1 F.K_ro sc d s)
      (.pair (.fst .v0) (.pair .v1 .v2) : Expr pqAtomicOps
        [.prod (embedTy shcrStTy) roBothAvlTy, embedTy pauseTy, .prod (PB 32) (PB 1568)] _)
    have hz := shcrResumeKC_size_le F.K_on1 F.K_ro
      (.vz : Var [.prod (B 32) (B 1568), pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))] _)
      (.vz : Var [pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))] _)
      (.vz : Var [shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))] _)
      (Δ := [.prod (B 32) (B 1568), pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))])
    have hlt := shcrResumeKC_litSize_le F.K_on1 F.K_ro
      (.vz : Var [.prod (B 32) (B 1568), pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))] _)
      (.vz : Var [pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))] _)
      (.vz : Var [shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))] _)
      (Δ := [.prod (B 32) (B 1568), pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy (.prod (B 32) (B 1568)))])
    unfold shcrKindResumeC; simp only [Comp.size]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (syncShcrShadowRespC_size_le F.K_cap _ _) _) 1) ?_
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
      _root_.ReductionDsl.Comp.letC, Comp.size, Expr.size, compLitSize, exprLitSize,
      Expr.v0, Expr.v1, Expr.v2, Nat.zero_add] at hm ⊢; omega
  have hRoA : (Comp.bind (roBaseShadowArmC aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0))))) :
      Comp pqAtomicOps pqAuthPrimIface [PB 192, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).size ≤
      2230 + 2 * bits (avlHeightCap F.K_cap) := by
    have h := roBaseShadowArmC_size_le aiAuthPrim F.K_cap
      (.pair (.fst (.fst .v1)) (.snd .v1) : Expr pqAtomicOps [PB 192, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q] _) .v0
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h ⊢; omega
  have hRoRA : (Comp.bind (roRootBaseShadowArmC aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0))))) :
      Comp pqAtomicOps pqAuthPrimIface [.prod (PB 32) (PB 32), .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).size ≤
      2280 + 2 * bits (avlHeightCap F.K_cap) := by
    have h := roRootBaseShadowArmC_size_le aiAuthPrim F.K_cap
      (.pair (.fst (.fst .v1)) (.snd .v1) : Expr pqAtomicOps [.prod (PB 32) (PB 32), .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q] _) .v0
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h ⊢; omega
  have hB1 := shcrBaseArmC_size_le S (fun st u => initPrin1KeyKB F st u) (Γ := [(authCodec S).Q]) hIpS hIpL
  have hB2 := shcrBaseArmC_size_le S (fun st u => corruptKB F st u) (Γ := [(authCodec S).Q]) hCoS hCoL
  have hB3 := shcrGenSpkArm_size_le S F (Γ := [(authCodec S).Q])
  have hB4 := shcrBaseArmC_size_le S (fun st x => genOpkKB F st x) (Γ := [(authCodec S).Q]) hGoS hGoL
  have hB12 := shcrBaseArmC_size_le S (fun st sk => registerKB st sk) (Γ := [(authCodec S).Q]) hRgS hRgL
  have hRcvT := shcrRecvArm_size_le S F true (Γ := [(authCodec S).Q])
  have hRcvF := shcrRecvArm_size_le S F false (Γ := [(authCodec S).Q])
  have hChP : (Comp.ret (.pair aNoneAtomicE .v1) :
      Comp pqAtomicOps pqAuthPrimIface [.unit, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).size ≤ 35 := by
    simp only [Comp.size, Expr.size, Expr.v1]
    change (aNoneAtomicE (Γ := [])).size + 1 + 1 + 1 ≤ 35
    have := aNoneAtomicE_size_le (Γ := []); omega
  have hPost : (shcrKindHandlePostC S F).size ≤
      450000 + 1020 * bits F.K_on + 400 * bits F.K_ro + 20 * bits (avlHeightCap F.K_cap) := by
    have hSndT := shcrSendArm_size_le S F true
      (.pair (.fst .v1) .v0 : Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q] _)
      (.snd .v2) (by simp [Expr.size, Expr.v0, Expr.v1]) (by simp [Expr.size, Expr.v2])
    have hSndF := shcrSendArm_size_le S F false
      (.pair (.fst .v1) .v0 : Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q] _)
      (.snd .v2) (by simp [Expr.size, Expr.v0, Expr.v1]) (by simp [Expr.size, Expr.v2])
    dsimp only [shcrKindHandlePostC]
    exact le_trans (dispatchAuthQ_size_le_of_arms _ _ _ _ _ _ _ _ _ _ _ _ _
      hB1 hB2 hB3 hB4 hSndT hSndF hRcvT hRcvF hRoA hRoRA hChP hB12) (by simp only [Expr.size]; omega)
  have hPre : (shcrKindHandlePreC S F).size ≤
      500000 + 1270 * bits F.K_on + 300 * bits (min F.K_on S.N_dh) +
        400 * bits F.K_ro + 20 * bits (avlHeightCap F.K_cap) := by
    have hPreT := shcrSendPreArm_size_le S F true (Γ := [(authCodec S).Q])
    have hPreF := shcrSendPreArm_size_le S F false (Γ := [(authCodec S).Q])
    have hChPre : (Comp.ret (.inl (.pair aNoneAtomicE .v1)) :
        Comp pqAtomicOps pqAuthPrimIface [.unit, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
          (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
            (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy))))).size ≤ 36 := by
      simp only [Comp.size, Expr.size, Expr.v1]
      change (aNoneAtomicE (Γ := [])).size + 1 + 1 + 1 + 1 ≤ 36
      have := aNoneAtomicE_size_le (Γ := []); omega
    dsimp only [shcrKindHandlePreC]
    exact le_trans (dispatchAuthQ_size_le_of_arms _ _ _ _ _ _ _ _ _ _ _ _ _
      (wrapInl_size_le S hB1) (wrapInl_size_le S hB2) (wrapInl_size_le S hB3) (wrapInl_size_le S hB4)
      hPreT hPreF (wrapInl_size_le S hRcvT) (wrapInl_size_le S hRcvF)
      (wrapInl_size_le S hRoA) (wrapInl_size_le S hRoRA) hChPre (wrapInl_size_le S hB12))
      (by simp only [Expr.size]; omega)
  have hB : reductionSizeBudget = 2 ^ 24 := rfl
  unfold shcrAuth1KeyKindProg TwoStageCostedReduction.size
  dsimp only [F] at *; rw [hB]; omega

end ShcrBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcr
