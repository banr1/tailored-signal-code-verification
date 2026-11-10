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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.CostUB
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs

/-!
# `shcrAuth1KeyKindProg` Post-Stage Handle and Resume Bounds

Kind-split `costAt`, static `cost`, and primitive `queries` bounds for `shcrKindHandlePostC` and
`shcrKindResumeC`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcrPost

open _root_.ReductionDsl (Ty Var Comp Expr Env pqAtomicSig pqAtomicOps PB bits)
open _root_.SignalPqxdh (Setup AuthQuery)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface PSamp)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface)
open _root_.SignalPqxdh.Security
  (authQueryKind authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (aiAuthPrim embedTy mapComp tlAuthPrim tlAuthPrim_primW
   mapComp_cost_two_mul_le mapComp_queries_le
   compRename_cost compRename_queries sampR64W r64W castLegacySamp)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext RS shcrStTy sendQTy recvQTy shcrGenSpkB shcrGenSpkB_costUB_le_tight shcrGenSpkB_queries)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authQueryAtomicTy authRespAtomicTy
   authSendQAtomicTy authRecvQAtomicTy aNoneAtomicE
   initPrin1KeyKB corruptKB genOpkKB registerKB
   baseRoCacheE baseRootRoCacheE
   roBaseShadowArmC roRootBaseShadowArmC syncRoBothC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (liftAuthPrim1 syncShcrShadowRespC shcrBaseArmC
   shcrKindResumeC shcrKindHandlePostC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
  (dispatchAuthQ_v1_costAt_kind1_le dispatchAuthQ_cost_le dispatchAuthQ_queries_le
   roBaseShadowArmC_cost_le roBaseShadowArmC_queries_zero
   roRootBaseShadowArmC_cost_le roRootBaseShadowArmC_queries_zero
   syncRoBothC_cost_le syncRoBothC_queries_zero)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedHs
  (initPrin1KeyKB_cost_le initPrin1KeyKB_r64_le initPrin1KeyKB_queries_prim_le
   corruptKB_cost_le corruptKB_r64_le corruptKB_queries_prim_le
   genOpkKB_cost_le genOpkKB_r64_le genOpkKB_queries_prim_le
   registerKB_cost_le registerKB_r64_le registerKB_queries_prim_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCost
  (shcrSendKC_cost_le shcrSendKC_r64_le shcrSendKC_queries_prim_le
   shcrAcceptKB_cost_le shcrAcceptKB_r64_le shcrAcceptKB_queries_prim_le
   shcrResumeKC_cost_le shcrResumeKC_r64_le shcrResumeKC_queries_prim_le)

section ShcrPostBounds

private theorem sampR64W_tlAuthPrim : sampR64W tlAuthPrim.hsmp = sampR64W rfl := rfl

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

theorem shcrKindHandlePostC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy shcrStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 1) :
    (shcrKindHandlePostC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  dsimp only [shcrKindHandlePostC]
  refine le_trans (dispatchAuthQ_v1_costAt_kind1_le _ _ _ _ _ _ _ _ _ _ _ _ s q .nil
    (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (roBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (roRootBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega

private theorem shcrBaseArmC_cost_two_mul_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authStateTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RS)
    {Γ : List (Ty pqAtomicSig)} {C R : ℕ}
    (hc : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st : Var Γ₁ authStateTy) (x : Var Γ₂ arg), (step (Δ := Δ) st x).cost ≤ C)
    (hr : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st : Var Γ₁ authStateTy) (x : Var Γ₂ arg),
      (step (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) ≤ R) :
    2 * (shcrBaseArmC S step (Γ := Γ)).cost ≤ 72 + 3 * C + 78 * R := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     step st x)
    (.pair (.fst (.fst .v1)) .v0 :
      Expr pqAtomicOps (embedTy arg :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hc' : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
      step (Δ := [arg, authStateTy, .prod authStateTy arg]) st x).cost ≤ 8 + C := by
    have h0 := hc (st := .vz) (x := .vz)
      (Γ₁ := [authStateTy, .prod authStateTy arg])
      (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
      (Δ := [arg, authStateTy, .prod authStateTy arg])
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
      _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost]
    omega
  have hr' : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
      step (Δ := [arg, authStateTy, .prod authStateTy arg]) st x).queries
      (fun _ => 0) (sampR64W rfl) ≤ R := by
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
      _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.zero_add] using
      hr (st := .vz) (x := .vz)
        (Γ₁ := [authStateTy, .prod authStateTy arg])
        (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
        (Δ := [arg, authStateTy, .prod authStateTy arg])
  unfold shcrBaseArmC
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hl ⊢
  omega

private theorem shcrGenSpkB_r64_le (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).queries (fun _ => 0) (sampR64W rfl) ≤ 3 := by
  change (shcrGenSpkB (Δ := Δ) S K s x).queries (fun _ => 0) r64W ≤ 3
  simp only [shcrGenSpkB,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV,
    _root_.ReductionDsl.Comp.iteC, _root_.ReductionDsl.Comp.caseOptC,
    _root_.ReductionDsl.Comp.letC, _root_.ReductionDsl.Comp.sampleBytes32,
    _root_.ReductionDsl.Comp.sampleRandom64, _root_.ReductionDsl.Comp.queryPrim,
    r64W, Comp.queries]
  omega

private theorem shcrGenSpkArm_cost_le (S : Setup) (F : AuthKindFuels)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         shcrGenSpkB S F.K_on s x)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (.prod .nat .nat :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2)))) :
      Comp pqAtomicOps pqAuthPrimIface _
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).cost ≤
      38000 + 150 * F.K_on := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     shcrGenSpkB S F.K_on s x)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (.prod .nat .nat :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have h1 := _root_.ReductionDsl.Comp.cost_le_costUB
    (shcrGenSpkB S F.K_on (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
      (.vz : Var [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
      (Δ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)]))
  have h2 := shcrGenSpkB_costUB_le_tight S F.K_on
    (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
    (.vz : Var [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
    (Δ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
  have h3 := shcrGenSpkB_r64_le S F.K_on
    (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
    (.vz : Var [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
    (Δ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries,
    Expr.v0, Expr.v1, Expr.v2] at hl ⊢
  omega

private theorem shcrSendArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         AuthCoreKArms.shcrSendKC S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2)) :
      Comp pqAtomicOps pqAuthPrimIface _
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).cost ≤
      18700 + 5355 * F.K_on + 1545 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 1975) := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     AuthCoreKArms.shcrSendKC S F.K_on F.K_ro opk s x)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hc := shcrSendKC_cost_le S F.K_on F.K_ro opk
    (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _)
    (.vz : Var [sendQTy, shcrStTy, .prod shcrStTy sendQTy] _)
    (Δ := [sendQTy, shcrStTy, .prod shcrStTy sendQTy])
  have hr := shcrSendKC_r64_le S F.K_on F.K_ro opk
    (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _)
    (.vz : Var [sendQTy, shcrStTy, .prod shcrStTy sendQTy] _)
    (Δ := [sendQTy, shcrStTy, .prod shcrStTy sendQTy])
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left
    (syncShcrShadowRespC_cost_le F.K_cap _ _) _) 1) ?_
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries,
    Expr.v0, Expr.v1, Expr.v2] at hl ⊢
  omega

private theorem shcrRecvArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         AuthCoreKArms.shcrAcceptKB S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2)) :
      Comp pqAtomicOps pqAuthPrimIface _
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).cost ≤
      24200 + 555 * F.K_on + 618 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 1975) := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     AuthCoreKArms.shcrAcceptKB S F.K_on F.K_ro opk s x)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hc := shcrAcceptKB_cost_le S F.K_on F.K_ro opk
    (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _)
    (.vz : Var [recvQTy, shcrStTy, .prod shcrStTy recvQTy] _)
    (Δ := [recvQTy, shcrStTy, .prod shcrStTy recvQTy])
  have hr := shcrAcceptKB_r64_le S F.K_on F.K_ro opk
    (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _)
    (.vz : Var [recvQTy, shcrStTy, .prod shcrStTy recvQTy] _)
    (Δ := [recvQTy, shcrStTy, .prod shcrStTy recvQTy])
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left
    (syncShcrShadowRespC_cost_le F.K_cap _ _) _) 1) ?_
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries,
    Expr.v0, Expr.v1, Expr.v2] at hl ⊢
  omega

private theorem shcrKindHandlePostC_cost_le_aux (S : Setup) (F : AuthKindFuels) :
    (shcrKindHandlePostC S F).cost ≤
      45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) := by
  dsimp only [shcrKindHandlePostC]
  refine le_trans (dispatchAuthQ_cost_le _ _ _ _ _ _ _ _ _ _ _ _ _
    (B := 44978 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
      (8500 * bits F.K_cap + 2080))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · have h := shcrBaseArmC_cost_two_mul_le S (fun st u => initPrin1KeyKB F st u)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st u => initPrin1KeyKB_cost_le (Δ := Δ) F st u)
      (fun {Γ₁ Γ₂ Δ} _ _ st u => le_of_eq (initPrin1KeyKB_r64_le (Δ := Δ) F st u))
    omega
  · have h := shcrBaseArmC_cost_two_mul_le S (fun st u => corruptKB F st u)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st u => corruptKB_cost_le (Δ := Δ) F st u)
      (fun {Γ₁ Γ₂ Δ} _ _ st u => le_of_eq (corruptKB_r64_le (Δ := Δ) F st u))
    omega
  · exact le_trans (shcrGenSpkArm_cost_le S F (Γ := [(authCodec S).Q])) (by omega)
  · have h := shcrBaseArmC_cost_two_mul_le S (fun st x => genOpkKB F st x)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st x => genOpkKB_cost_le (Δ := Δ) F st x)
      (fun {Γ₁ Γ₂ Δ} _ _ st x => le_of_eq (genOpkKB_r64_le (Δ := Δ) F st x))
    omega
  · exact le_trans (shcrSendArm_cost_le S F true (Γ := [(authCodec S).Q])) (by omega)
  · exact le_trans (shcrSendArm_cost_le S F false (Γ := [(authCodec S).Q])) (by omega)
  · exact le_trans (shcrRecvArm_cost_le S F true (Γ := [(authCodec S).Q])) (by omega)
  · exact le_trans (shcrRecvArm_cost_le S F false (Γ := [(authCodec S).Q])) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (roBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (roRootBaseShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) 1) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [aNoneAtomicE, Comp.cost, Expr.cost, Expr.v1]
    omega
  · have h := shcrBaseArmC_cost_two_mul_le S (fun st sk => registerKB st sk)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st sk => registerKB_cost_le (Δ := Δ) st sk)
      (fun {Γ₁ Γ₂ Δ} _ _ st sk => le_of_eq (registerKB_r64_le (Δ := Δ) st sk))
    omega
  · simp only [Expr.cost]
    omega

set_option linter.unusedVariables false in
theorem shcrKindHandlePostC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy shcrStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 0) :
    (shcrKindHandlePostC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  le_trans (_root_.ReductionDsl.Comp.costAt_le_cost _ _) (shcrKindHandlePostC_cost_le_aux S F)

theorem shcrKindHandlePostC_cost_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindHandlePostC S F).cost ≤
      45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  shcrKindHandlePostC_cost_le_aux S F

theorem shcrKindResumeC_cost_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindResumeC S F).cost ≤
      15200 + 6000 * F.K_on1 + 797 * F.K_ro + (8500 * bits F.K_cap + 2100) := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.snd (.var (.succ .zero)))) fun d =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV
       (.snd (.snd (.var (.succ (.succ .zero))))) fun sc =>
     AuthCoreKArms.shcrResumeKC F.K_on1 F.K_ro sc d s)
    (.pair (.fst .v0) (.pair .v1 .v2) :
      Expr pqAtomicOps [.prod (embedTy shcrStTy) roBothAvlTy,
        embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy,
        .prod (PB 32) (PB 1568)] _)
  have hc := shcrResumeKC_cost_le F.K_on1 F.K_ro
    (.vz : Var [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (.vz : Var [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (.vz : Var [shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (Δ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))])
  have hr := shcrResumeKC_r64_le F.K_on1 F.K_ro
    (.vz : Var [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (.vz : Var [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (.vz : Var [shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (Δ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))])
  unfold shcrKindResumeC
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left
    (syncShcrShadowRespC_cost_le F.K_cap _ _) _) 1) ?_
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.cost, Expr.cost, Comp.queries,
    Expr.v0, Expr.v1, Expr.v2] at hl ⊢
  omega

theorem shcrKindResumeC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindResumeC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ 20 := by
  have hl := liftAuthPrim1_queries_prim_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.snd (.var (.succ .zero)))) fun d =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV
       (.snd (.snd (.var (.succ (.succ .zero))))) fun sc =>
     AuthCoreKArms.shcrResumeKC F.K_on1 F.K_ro sc d s)
    (.pair (.fst .v0) (.pair .v1 .v2) :
      Expr pqAtomicOps [.prod (embedTy shcrStTy) roBothAvlTy,
        embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy,
        .prod (PB 32) (PB 1568)] _)
  have hq := shcrResumeKC_queries_prim_le F.K_on1 F.K_ro
    (.vz : Var [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (.vz : Var [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (.vz : Var [shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))] _)
    (Δ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568),
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy, shcrStTy,
      .prod shcrStTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseTy
        (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))])
  unfold shcrKindResumeC
  simp only [Comp.queries]
  refine le_trans (Nat.add_le_add hl (le_of_eq (syncShcrShadowRespC_queries_zero F.K_cap _ _))) ?_
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.add_zero, Nat.zero_add]
  exact le_trans hq (by omega)

private theorem shcrBaseArmC_queries_prim_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authStateTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RS)
    {Γ : List (Ty pqAtomicSig)} {Q : ℕ}
    (hq : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st : Var Γ₁ authStateTy) (x : Var Γ₂ arg),
      (step (Δ := Δ) st x).queries (fun _ => 1) (fun _ => 0) ≤ Q) :
    (shcrBaseArmC S step (Γ := Γ)).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  have hl := liftAuthPrim1_queries_prim_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     step st x)
    (.pair (.fst (.fst .v1)) .v0 :
      Expr pqAtomicOps (embedTy arg :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have h0 := hq (st := .vz) (x := .vz)
    (Γ₁ := [authStateTy, .prod authStateTy arg])
    (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
    (Δ := [arg, authStateTy, .prod authStateTy arg])
  unfold shcrBaseArmC
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.add_zero, Nat.zero_add] at hl ⊢
  exact le_trans hl h0

private theorem shcrSendArm_queries_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         AuthCoreKArms.shcrSendKC S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2)) :
      Comp pqAtomicOps pqAuthPrimIface _
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 10 * S.N_dh := by
  have hl := liftAuthPrim1_queries_prim_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     AuthCoreKArms.shcrSendKC S F.K_on F.K_ro opk s x)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hq := shcrSendKC_queries_prim_le S F.K_on F.K_ro opk
    (.vz : Var [shcrStTy, .prod shcrStTy sendQTy] _)
    (.vz : Var [sendQTy, shcrStTy, .prod shcrStTy sendQTy] _)
    (Δ := [sendQTy, shcrStTy, .prod shcrStTy sendQTy])
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  simp only [Comp.queries]
  refine le_trans (Nat.add_le_add hl (le_of_eq (syncShcrShadowRespC_queries_zero F.K_cap _ _))) ?_
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.add_zero, Nat.zero_add]
  exact le_trans hq (by omega)

private theorem shcrRecvArm_queries_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         AuthCoreKArms.shcrAcceptKB S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2)) :
      Comp pqAtomicOps pqAuthPrimIface _
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      22 + 4 * S.N_dh := by
  have hl := liftAuthPrim1_queries_prim_le
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     AuthCoreKArms.shcrAcceptKB S F.K_on F.K_ro opk s x)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ) _)
  have hq := shcrAcceptKB_queries_prim_le S F.K_on F.K_ro opk
    (.vz : Var [shcrStTy, .prod shcrStTy recvQTy] _)
    (.vz : Var [recvQTy, shcrStTy, .prod shcrStTy recvQTy] _)
    (Δ := [recvQTy, shcrStTy, .prod shcrStTy recvQTy])
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  simp only [Comp.queries]
  refine le_trans (Nat.add_le_add hl (le_of_eq (syncShcrShadowRespC_queries_zero F.K_cap _ _))) ?_
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.add_zero, Nat.zero_add]
  exact le_trans hq (by omega)

theorem shcrKindHandlePostC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (shcrKindHandlePostC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh := by
  dsimp only [shcrKindHandlePostC]
  apply dispatchAuthQ_queries_le
  · exact le_trans (shcrBaseArmC_queries_prim_le S (fun st u => initPrin1KeyKB F st u)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st u => initPrin1KeyKB_queries_prim_le (Δ := Δ) F st u)) (by omega)
  · exact le_trans (shcrBaseArmC_queries_prim_le S (fun st u => corruptKB F st u)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st u => le_of_eq (corruptKB_queries_prim_le (Δ := Δ) F st u))) (by omega)
  · have hl := liftAuthPrim1_queries_prim_le
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
       shcrGenSpkB S F.K_on s x)
      (.pair (.fst .v1) .v0 :
        Expr pqAtomicOps [.prod .nat .nat, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q] _)
    have hq := shcrGenSpkB_queries S F.K_on
      (.vz : Var [shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
      (.vz : Var [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] _)
      (Δ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
      _root_.ReductionDsl.Comp.letC, Comp.queries, Nat.add_zero, Nat.zero_add] at hl ⊢
    unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.primWS at hq
    exact le_trans hl (by rw [hq]; omega)
  · exact le_trans (shcrBaseArmC_queries_prim_le S (fun st x => genOpkKB F st x)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st x => genOpkKB_queries_prim_le (Δ := Δ) F st x)) (by omega)
  · exact le_trans (shcrSendArm_queries_prim_le S F true (Γ := [(authCodec S).Q])) (by omega)
  · exact le_trans (shcrSendArm_queries_prim_le S F false (Γ := [(authCodec S).Q])) (by omega)
  · exact le_trans (shcrRecvArm_queries_prim_le S F true (Γ := [(authCodec S).Q])) (by omega)
  · exact le_trans (shcrRecvArm_queries_prim_le S F false (Γ := [(authCodec S).Q])) (by omega)
  · simp only [Comp.queries, Nat.add_zero]
    refine le_of_eq_of_le ?_ (Nat.zero_le _)
    exact roBaseShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap _ _
  · simp only [Comp.queries, Nat.add_zero]
    refine le_of_eq_of_le ?_ (Nat.zero_le _)
    exact roRootBaseShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap _ _
  · simp only [Comp.queries]; omega
  · exact le_trans (shcrBaseArmC_queries_prim_le S (fun st sk => registerKB st sk)
      (Γ := [(authCodec S).Q])
      (fun {Γ₁ Γ₂ Δ} _ _ st sk => registerKB_queries_prim_le (Δ := Δ) st sk)) (by omega)

end ShcrPostBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcrPost
