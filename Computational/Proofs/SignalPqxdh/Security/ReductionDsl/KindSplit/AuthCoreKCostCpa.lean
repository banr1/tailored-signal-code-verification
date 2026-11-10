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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostPrf
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedFixed
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaProofs

/-!
# `aeadCpa1KeyKindProg` Cost, Query, and Size Bounds

Kind-split `costAt`, static `cost`, primitive `queries`, and `TwoStageCostedReduction.size` bounds
for `aeadCpa1KeyKindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostCpa

open _root_.ReductionDsl (Ty Var Comp Expr Env pqAtomicSig pqAtomicOps PB bits reductionSizeBudget
  TwoStageCostedReduction)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B PSamp primIfacePrimQueryWeight)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface)
open _root_.SignalPqxdh.Security
  (stepCostBudget authQueryKind authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (aiAuthPrim embedTy mapComp mapExpr tlAuthPrim tlAuthPrim_primW tlAuthPrim_sizeLe
   mapComp_cost_two_mul_le mapComp_queries_le mapComp_size_le
   compRename_cost compRename_queries compRename_size compLitSize exprLitSize pqOpLitSize
   exprRename_cost exprRename_size mapExpr_size
   sampR64W r64W castLegacySamp
   bits_le_bits_stepCostBudget atomicSize_le_budget)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (cpaStTy cpaPayloadTy cpaInitC cpaDefaultChC cpaResumeC cpaFinishC aeadCpaRedProg
   cpa_init_cost cpa_chDone_cost cpa_resume_cost cpa_finish_cost
   cpa_init_queries cpa_chDone_queries cpa_resume_queries cpa_finish_queries)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext RSF authHybridStateFixedTy sendQTy recvQTy
   finalizeAuthFixedDsl finalizeAuthFixedBodyDsl allHonestEcPksAuthDslK
   v bindV letV caseSumV aNone samplePrim queryPrim cost_letC queries_letC primW primWS)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (avlHeightCap)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy emptyRoBothAvlE authFixedAtomicTy authFixedShadowStTy
   authQueryAtomicTy authRespAtomicTy authSendQAtomicTy authRecvQAtomicTy
   liftExpr1 fixedRoCacheE fixedRootRoCacheE dispatchAuthQ aNoneAtomicE
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB
   roFixedShadowArmC roRootFixedShadowArmC syncRoBothC syncFixedShadowRespC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (cpaSendSlotKB cpaRecvKC dropShadow0 dropShadow1 liftAuthPrim1
   cpaKindInitC cpaRebuildE cpaBaseArmC cpaRecvArmC
   cpaKindHandlePreC cpaKindChDoneC cpaKindResumeC cpaKindHandlePostC
   cpaKindFinishC aeadCpa1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
  (dispatchAuthQ_v1_costAt_kind1_le dispatchAuthQ_v1_costAt_kind0_le
   dispatchAuthQ_cost_le dispatchAuthQ_queries_le dispatchAuthQ_size_le
   roFixedShadowArmC_cost_le roFixedShadowArmC_queries_zero roFixedShadowArmC_size_le
   roRootFixedShadowArmC_cost_le roRootFixedShadowArmC_queries_zero roRootFixedShadowArmC_size_le
   syncRoBothC_cost_le syncRoBothC_queries_zero syncRoBothC_size_le
   syncFixedShadowRespC_cost_le syncFixedShadowRespC_queries_zero syncFixedShadowRespC_size_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedFixed
  (initPrin1KeyFixedKB_cost_le initPrin1KeyFixedKB_r64_le initPrin1KeyFixedKB_queries_prim_le
   corruptFixedKB_cost_le corruptFixedKB_r64_le corruptFixedKB_queries_prim_le
   genSpkFixedKB_cost_le genSpkFixedKB_r64_le genSpkFixedKB_queries_prim_le
   genOpkFixedKB_cost_le genOpkFixedKB_r64_le genOpkFixedKB_queries_prim_le
   registerFixedKB_cost_le registerFixedKB_r64_le registerFixedKB_queries_prim_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostPrf
  (cpaSendSlotKB_cost_le cpaSendSlotKB_r64_le cpaSendSlotKB_queries_prim_le
   cpaSendSlotKB_size_le cpaSendSlotKB_litSize_le
   cpaRecvKC_cost_le cpaRecvKC_r64_le cpaRecvKC_queries_prim_le
   cpaRecvKC_size_le cpaRecvKC_litSize_le)

section CpaBounds

private def zeroSetup : Setup := ⟨0, 0, 0, 0, 0, 0⟩

private theorem sampR64W_tlAuthPrim : sampR64W tlAuthPrim.hsmp = sampR64W rfl := rfl

private theorem emptyRoBothAvlE_cost_eq {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).cost = (emptyRoBothAvlE (Γ := [])).cost :=
  rfl

private theorem emptyRoBothAvlE_cost_le {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).cost ≤ 500 := by
  rw [emptyRoBothAvlE_cost_eq]
  decide

private theorem emptyRoBothAvlE_size_eq {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).size = (emptyRoBothAvlE (Γ := [])).size :=
  rfl

private theorem emptyRoBothAvlE_size_le {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).size ≤ 500 := by
  rw [emptyRoBothAvlE_size_eq]
  decide

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

theorem cpaKindInitC_cost_le (S : Setup) (b : QueryBudget) :
    (cpaKindInitC S b).cost ≤ 1000 + 2 * Nat.log 2 S.N_sess_tot := by
  have hc : (cpaInitC S b.q_total).cost = 66 + bits (min b.q_total S.N_send_tot) :=
    cpa_init_cost S b.q_total
  have hmin : min b.q_total S.N_send_tot ≤ S.N_sess_tot := by
    have h1 : min b.q_total S.N_send_tot ≤ S.N_send_tot := Nat.min_le_right _ _
    unfold Setup.N_sess_tot
    omega
  have hlog : Nat.log 2 (min b.q_total S.N_send_tot) ≤ Nat.log 2 S.N_sess_tot :=
    Nat.log_mono_right hmin
  have hr64 : (cpaInitC S b.q_total).queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
    have hidx : ∀ n, sampR64W tlAuthPrim.hsmp (PSamp.index n) = 0 := fun _ => rfl
    simp [cpaInitC, bindV, samplePrim, hidx, Comp.queries]
  have hm := mapComp_cost_two_mul_le tlAuthPrim (cpaInitC S b.q_total)
  have he := emptyRoBothAvlE_cost_le (Γ := [.prod .unit (embedTy cpaStTy), .unit])
  unfold cpaKindInitC bits at *
  simp only [Comp.cost, Expr.cost, Expr.v0]
  omega

theorem cpaKindHandlePreC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy cpaStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 1) :
    (cpaKindHandlePreC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  unfold cpaKindHandlePreC
  refine le_trans (dispatchAuthQ_v1_costAt_kind1_le _ _ _ _ _ _ _ _ _ _ _ _ s q .nil
    (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (roFixedShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) _) _) _) ?_
    simp only [cpaRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (roRootFixedShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) _) _) _) ?_
    simp only [cpaRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega

private theorem liftExpr1_cost_le {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a))
    {C : ℕ} (h : (mapExpr e).cost + 1 ≤ C) :
    (liftExpr1 e argE).cost ≤ argE.cost + C := by
  simp only [liftExpr1, Expr.cost, exprRename_cost]; omega

private theorem fixedRoCacheE_cost {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRoCacheE e).cost ≤ e.cost + 22 := by
  rw [fixedRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem fixedRootRoCacheE_cost {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRootRoCacheE e).cost ≤ e.cost + 22 := by
  rw [fixedRootRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private abbrev cpaArmB0 (S : Setup) (F : AuthKindFuels) : ℕ :=
  19970 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh + 11300 * min F.K_on S.N_sess_tot +
    797 * F.K_ro + (8500 * bits F.K_cap + 2055)

private theorem syncCpaSendRoC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ authFixedAtomicTy) (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := pqAuthPrimIface) cap (fixedRoCacheE e) (fixedRootRoCacheE e) roBothE).cost ≤
      8500 * bits cap + 1894 + 2 * e.cost + roBothE.cost := by
  have h1 := fixedRoCacheE_cost e
  have h2 := fixedRootRoCacheE_cost e
  have hs := syncRoBothC_cost_le (I := pqAuthPrimIface) cap
    (fixedRoCacheE e) (fixedRootRoCacheE e) roBothE
  omega

private theorem aNoneAtomicE_cost_eq {Γ : List (Ty pqAtomicSig)} :
    (aNoneAtomicE (Γ := Γ)).cost = 2 :=
  rfl

private theorem cpaBaseArmC_cost_le (S : Setup) (F : AuthKindFuels) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ RSF)
    {Γ : List (Ty pqAtomicSig)} {C R : ℕ}
    (hc : (step (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero).cost ≤ C)
    (hr : (step (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero).queries
      (fun _ => 0) (sampR64W rfl) ≤ R)
    (hCR : 100 + 3 * C + 78 * R ≤ 2 * cpaArmB0 S F) :
    (cpaBaseArmC S step (Γ := Γ)).cost ≤ cpaArmB0 S F := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (letV (.fst (.var .zero)) fun fhst =>
     letV (.snd (.var (.succ .zero))) fun x =>
     step fhst x)
    (.pair (.snd (.snd (.fst .v1))) .v0 :
      Expr pqAtomicOps (embedTy arg :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  unfold cpaBaseArmC
  simp only [letV, cost_letC, queries_letC, cpaRebuildE, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hl ⊢
  omega

private theorem cpaRecvArmC_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaRecvArmC S F opk (Γ := Γ)).cost ≤ cpaArmB0 S F := by
  have hl := liftAuthPrim1_cost_two_mul_le
    (letV (.fst (.var .zero)) fun fhst =>
     letV (.snd (.var (.succ .zero))) fun x =>
     cpaRecvKC S F.K_on F.K_ro opk fhst x)
    (.pair (.snd (.snd (.fst .v1))) .v0 :
      Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  have hc := cpaRecvKC_cost_le S F.K_on F.K_ro opk
    (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
    (.zero : Var [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
    (Δ := [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy])
  have hr := cpaRecvKC_r64_le S F.K_on F.K_ro opk
    (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
    (.zero : Var [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
    (Δ := [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy])
  have hs := syncFixedShadowRespC_cost_le (I := pqAuthPrimIface) F.K_cap
    (.v0 : Expr pqAtomicOps
      (embedTy RSF :: authRecvQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
    (.snd .v2)
  unfold cpaRecvArmC
  simp only [letV, cost_letC, queries_letC, cpaRebuildE, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hl hs ⊢
  unfold cpaArmB0
  omega

private theorem cpaInitPrinArm_cost_le (S : Setup) (F : AuthKindFuels)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u) (Γ := Γ)).cost ≤ cpaArmB0 S F :=
  cpaBaseArmC_cost_le S F _ (initPrin1KeyFixedKB_cost_le F _ _)
    (Nat.le_of_eq (initPrin1KeyFixedKB_r64_le F _ _)) (by unfold cpaArmB0; omega)

private theorem cpaCorruptArm_cost_le (S : Setup) (F : AuthKindFuels)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaBaseArmC S (fun fhst u => corruptFixedKB F fhst u) (Γ := Γ)).cost ≤ cpaArmB0 S F :=
  cpaBaseArmC_cost_le S F _ (corruptFixedKB_cost_le F _ _)
    (Nat.le_of_eq (corruptFixedKB_r64_le F _ _)) (by unfold cpaArmB0; omega)

private theorem cpaGenSpkArm_cost_le (S : Setup) (F : AuthKindFuels)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaBaseArmC S (fun fhst x => genSpkFixedKB F fhst x) (Γ := Γ)).cost ≤ cpaArmB0 S F :=
  cpaBaseArmC_cost_le S F _ (genSpkFixedKB_cost_le F _ _)
    (genSpkFixedKB_r64_le F _ _) (by unfold cpaArmB0; omega)

private theorem cpaGenOpkArm_cost_le (S : Setup) (F : AuthKindFuels)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaBaseArmC S (fun fhst x => genOpkFixedKB F fhst x) (Γ := Γ)).cost ≤ cpaArmB0 S F :=
  cpaBaseArmC_cost_le S F _ (genOpkFixedKB_cost_le F _ _)
    (Nat.le_of_eq (genOpkFixedKB_r64_le F _ _)) (by unfold cpaArmB0; omega)

private theorem cpaRegisterArm_cost_le (S : Setup) (F : AuthKindFuels)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaBaseArmC S (fun fhst sk => registerFixedKB fhst sk) (Γ := Γ)).cost ≤ cpaArmB0 S F :=
  cpaBaseArmC_cost_le S F _ (registerFixedKB_cost_le _ _)
    (Nat.le_of_eq (registerFixedKB_r64_le _ _)) (by unfold cpaArmB0; omega)

private theorem cpaWrapInl_cost_le (S : Setup) {a b : Ty pqAtomicSig}
    {Γ : List (Ty pqAtomicSig)}
    {m : Comp pqAtomicOps pqAuthPrimIface (a :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))}
    {B : ℕ} (hm : m.cost ≤ B) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface (a :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ)
        (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) b)).cost ≤ B + 4 := by
  simp only [Comp.cost, Expr.cost, Expr.v0]; omega

private theorem cpaRoArm_cost_le (S : Setup) (F : AuthKindFuels) :
    (Comp.bind
      (roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface
        [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).cost ≤
      cpaArmB0 S F := by
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right
    (Nat.add_le_add_right (roFixedShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) _) ?_
  simp only [cpaRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  unfold cpaArmB0; omega

private theorem cpaRoRootArm_cost_le (S : Setup) (F : AuthKindFuels) :
    (Comp.bind
      (roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface
        [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).cost ≤
      cpaArmB0 S F := by
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right
    (Nat.add_le_add_right (roRootFixedShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) _) ?_
  simp only [cpaRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  unfold cpaArmB0; omega

private abbrev cpaSendPreInner (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqPrimIface [.prod cpaStTy sendQTy]
      (.sum (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy cpaStTy)
        (.prod (.prod (B 158) (.prod (B 32) (B 32))) (.prod cpaPayloadTy cpaStTy))) :=
  letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
  letV (.fst (v s)) fun idx => letV (.fst (.snd (v s))) fun ns =>
  letV (.snd (.snd (v s))) fun fhst =>
  bindV (cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
  caseSumV (v r)
    (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
    (fun p => .ret (.inr (.pair (.fst (v p))
      (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p))))))))

private abbrev cpaSendPostInner (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqxdhOps pqPrimIface [.prod cpaStTy sendQTy]
      (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy cpaStTy) :=
  letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
  letV (.fst (v s)) fun idx => letV (.fst (.snd (v s))) fun ns =>
  letV (.snd (.snd (v s))) fun fhst =>
  bindV (cpaSendSlotKB S F.K_on F.K_ro opk false idx ns fhst x) fun r =>
  caseSumV (v r)
    (fun d => .ret (.pair (.fst (v d)) (.pair (v idx) (.snd (v d)))))
    (fun _ => .ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst)))))

private theorem cpaSendPreArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1 (cpaSendPreInner S F opk)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _))
      (.caseSum .v0
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.snd (.snd (.snd .v0))))
            (fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v3))
          (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
        (.ret (.inr (.pair (.fst .v0)
          (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))).cost ≤
      cpaArmB0 S F + 4 := by
  have hl := liftAuthPrim1_cost_two_mul_le (cpaSendPreInner S F opk)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  simp only [Comp.cost]
  set liftCost := (liftAuthPrim1 _ _).cost
  let Δs := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy]
  have hc := cpaSendSlotKB_cost_le S F.K_on F.K_ro opk true
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  have hr := cpaSendSlotKB_r64_le S F.K_on F.K_ro opk true
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  simp only [cpaSendPreInner, letV, bindV, caseSumV, v, cost_letC, queries_letC,
    Comp.cost, Expr.cost, Comp.queries, Expr.v0, Expr.v1] at hl
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.max_le.mpr ⟨?_, ?_⟩ : _ ≤ 8500 * bits F.K_cap + 1930) _) _) _) _) ?_
  · refine le_trans (Nat.add_le_add_right
      (Nat.add_le_add_right (syncCpaSendRoC_cost_le F.K_cap _ _) _) _) ?_
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v3]; omega
  · simp only [Expr.cost, Expr.v0, Expr.v3]; omega
  · simp only [Expr.cost, Expr.v0]; unfold cpaArmB0; omega

theorem cpaKindHandlePreC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy cpaStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 0) :
    (cpaKindHandlePreC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      20000 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh + 11300 * min F.K_on S.N_sess_tot +
        797 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  unfold cpaKindHandlePreC
  refine le_trans (dispatchAuthQ_v1_costAt_kind0_le _ _ _ _ _ _ _ _ _ _ _ _ s q .nil
    (B₀ := cpaArmB0 S F + 4) hk
    (cpaWrapInl_cost_le S (cpaInitPrinArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaCorruptArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaGenSpkArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaGenOpkArm_cost_le S F))
    (cpaSendPreArm_cost_le S F true)
    (cpaSendPreArm_cost_le S F false)
    (cpaWrapInl_cost_le S (cpaRecvArmC_cost_le S F true))
    (cpaWrapInl_cost_le S (cpaRecvArmC_cost_le S F false))
    (by simp only [Comp.cost, Expr.cost, Expr.v1, aNoneAtomicE]; unfold cpaArmB0; omega)
    (cpaWrapInl_cost_le S (cpaRegisterArm_cost_le S F)))
    (by unfold cpaArmB0; omega)

theorem cpaKindHandlePreC_cost_le (S : Setup) (F : AuthKindFuels) :
    (cpaKindHandlePreC S F).cost ≤
      20000 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh + 11300 * min F.K_on S.N_sess_tot +
        797 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  unfold cpaKindHandlePreC; dsimp only
  refine le_trans (dispatchAuthQ_cost_le _ _ _ _ _ _ _ _ _ _ _ _ _ (B := cpaArmB0 S F + 4)
    (cpaWrapInl_cost_le S (cpaInitPrinArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaCorruptArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaGenSpkArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaGenOpkArm_cost_le S F))
    (cpaSendPreArm_cost_le S F true)
    (cpaSendPreArm_cost_le S F false)
    (cpaWrapInl_cost_le S (cpaRecvArmC_cost_le S F true))
    (cpaWrapInl_cost_le S (cpaRecvArmC_cost_le S F false))
    (cpaWrapInl_cost_le S (cpaRoArm_cost_le S F))
    (cpaWrapInl_cost_le S (cpaRoRootArm_cost_le S F))
    (by simp only [Comp.cost, Expr.cost, Expr.v1, aNoneAtomicE]; unfold cpaArmB0; omega)
    (cpaWrapInl_cost_le S (cpaRegisterArm_cost_le S F))) ?_
  simp only [Expr.cost]; unfold cpaArmB0; omega

theorem cpaKindChDoneC_cost_le :
    cpaKindChDoneC.cost ≤ 400 := by
  have hc : cpaDefaultChC.cost = 230 := cpa_chDone_cost zeroSetup 0
  have hr64 : cpaDefaultChC.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := rfl
  have hm := mapComp_cost_two_mul_le tlAuthPrim cpaDefaultChC
  unfold cpaKindChDoneC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  rw [compRename_cost]
  omega

theorem cpaKindResumeC_cost_le (S : Setup) :
    (cpaKindResumeC S).cost ≤ 1400 := by
  have hc : cpaResumeC.cost = 874 := cpa_resume_cost S 0
  have hr64 : cpaResumeC.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := rfl
  have hm := mapComp_cost_two_mul_le tlAuthPrim cpaResumeC
  unfold cpaKindResumeC
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  rw [compRename_cost]
  omega

theorem cpaKindHandlePostC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy cpaStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 1) :
    (cpaKindHandlePostC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  unfold cpaKindHandlePostC
  refine le_trans (dispatchAuthQ_v1_costAt_kind1_le _ _ _ _ _ _ _ _ _ _ _ _ s q .nil
    (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right
      (Nat.add_le_add_right (roFixedShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) _) ?_
    simp only [cpaRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right
      (Nat.add_le_add_right (roRootFixedShadowArmC_cost_le aiAuthPrim F.K_cap _ _) _) _) ?_
    simp only [cpaRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega

private theorem cpaSendPostArm_cost_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (Comp.bind (liftAuthPrim1 (cpaSendPostInner S F opk)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _))
      (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.snd (.snd (.snd .v0))))
          (fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))).cost ≤ cpaArmB0 S F := by
  have hl := liftAuthPrim1_cost_two_mul_le (cpaSendPostInner S F opk)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps (authSendQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  simp only [Comp.cost]
  set liftCost := (liftAuthPrim1 _ _).cost
  let Δs := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy]
  have hc := cpaSendSlotKB_cost_le S F.K_on F.K_ro opk false
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  have hr := cpaSendSlotKB_r64_le S F.K_on F.K_ro opk false
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  simp only [cpaSendPostInner, letV, bindV, caseSumV, v, aNone, cost_letC, queries_letC,
    Comp.cost, Expr.cost, Comp.queries, Expr.v0, Expr.v1] at hl
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.add_le_add_right (Nat.add_le_add_right (syncCpaSendRoC_cost_le F.K_cap _ _) _) _) _) _) ?_
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  unfold cpaArmB0
  omega

theorem cpaKindHandlePostC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy cpaStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 0) :
    (cpaKindHandlePostC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      20000 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh + 11300 * min F.K_on S.N_sess_tot +
        797 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  unfold cpaKindHandlePostC
  refine le_trans (dispatchAuthQ_v1_costAt_kind0_le _ _ _ _ _ _ _ _ _ _ _ _ s q .nil
    (B₀ := cpaArmB0 S F) hk
    (cpaInitPrinArm_cost_le S F)
    (cpaCorruptArm_cost_le S F)
    (cpaGenSpkArm_cost_le S F)
    (cpaGenOpkArm_cost_le S F)
    (cpaSendPostArm_cost_le S F true)
    (cpaSendPostArm_cost_le S F false)
    (cpaRecvArmC_cost_le S F true)
    (cpaRecvArmC_cost_le S F false)
    (by simp only [Comp.cost, Expr.cost, Expr.v1, aNoneAtomicE]; unfold cpaArmB0; omega)
    (cpaRegisterArm_cost_le S F))
    (by unfold cpaArmB0; omega)

theorem cpaKindHandlePostC_cost_le (S : Setup) (F : AuthKindFuels) :
    (cpaKindHandlePostC S F).cost ≤
      20000 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh + 11300 * min F.K_on S.N_sess_tot +
        797 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  unfold cpaKindHandlePostC; dsimp only
  refine le_trans (dispatchAuthQ_cost_le _ _ _ _ _ _ _ _ _ _ _ _ _ (B := cpaArmB0 S F)
    (cpaInitPrinArm_cost_le S F)
    (cpaCorruptArm_cost_le S F)
    (cpaGenSpkArm_cost_le S F)
    (cpaGenOpkArm_cost_le S F)
    (cpaSendPostArm_cost_le S F true)
    (cpaSendPostArm_cost_le S F false)
    (cpaRecvArmC_cost_le S F true)
    (cpaRecvArmC_cost_le S F false)
    (cpaRoArm_cost_le S F)
    (cpaRoRootArm_cost_le S F)
    (by simp only [Comp.cost, Expr.cost, Expr.v1, aNoneAtomicE]; unfold cpaArmB0; omega)
    (cpaRegisterArm_cost_le S F)) ?_
  simp only [Expr.cost]; unfold cpaArmB0; omega

theorem cpaKindFinishC_cost_le (S : Setup) (F : AuthKindFuels) :
    (cpaKindFinishC S F).cost ≤
      200 + 620 * min F.K_on S.N_dh + 1632 * (min F.K_on S.N_dh) ^ 2 +
        150 * F.K_on + 14267 * F.K_on ^ 2 := by
  have hc : (cpaFinishC S F.K_on).cost =
      112 + min F.K_on S.N_dh * 413 + (min F.K_on S.N_dh) ^ 2 * 1088 +
        F.K_on * 97 + F.K_on ^ 2 * 9511 := cpa_finish_cost S F.K_on
  have hr64 : (cpaFinishC S F.K_on).queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
    have hbool : sampR64W tlAuthPrim.hsmp _root_.SignalPqxdh.LegacyCosted.PSamp.bool = 0 := rfl
    simp [cpaFinishC, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
      allHonestEcPksAuthDslK, letV, queries_letC, samplePrim, queryPrim,
      hbool, Comp.queries]
  have hm := mapComp_cost_two_mul_le tlAuthPrim (cpaFinishC S F.K_on)
  unfold cpaKindFinishC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  rw [compRename_cost]
  omega

theorem cpaKindInitC_queries_prim_le (S : Setup) (b : QueryBudget) :
    (cpaKindInitC S b).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : (cpaInitC S b.q_total).queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS = 0 := cpa_init_queries S b.q_total
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW (cpaInitC S b.q_total)
  apply Nat.eq_zero_of_le_zero
  unfold cpaKindInitC
  simp only [Comp.queries, Nat.add_zero]
  exact le_trans hm (by omega)

private abbrev cpaArmQ0 (S : Setup) : ℕ :=
  40 + 30 * S.N_dh + 12 * S.N_sess_tot

private theorem cpaBaseArmC_queries_prim_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ RSF)
    {Γ : List (Ty pqAtomicSig)} {Q : ℕ}
    (hq : (step (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero).queries
      (fun _ => 1) (fun _ => 0) ≤ Q)
    (hQ : Q ≤ cpaArmQ0 S) :
    (cpaBaseArmC S step (Γ := Γ)).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      cpaArmQ0 S := by
  have hl := liftAuthPrim1_queries_prim_le
    (letV (.fst (.var .zero)) fun fhst =>
     letV (.snd (.var (.succ .zero))) fun x =>
     step fhst x)
    (.pair (.snd (.snd (.fst .v1))) .v0 :
      Expr pqAtomicOps (embedTy arg :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  unfold cpaBaseArmC
  simp only [letV, queries_letC, Comp.queries, Nat.add_zero] at hl ⊢
  exact le_trans hl (le_trans hq hQ)

private theorem cpaWrapInl_queries_prim_le (S : Setup) {a b : Ty pqAtomicSig}
    {Γ : List (Ty pqAtomicSig)}
    {m : Comp pqAtomicOps pqAuthPrimIface (a :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))}
    (hm : m.queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ cpaArmQ0 S) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface (a :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ)
        (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) b)).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ cpaArmQ0 S := by
  simpa only [Comp.queries, Nat.add_zero] using hm

private theorem cpaRecvArmC_queries_prim_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaRecvArmC S F opk (Γ := Γ)).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      cpaArmQ0 S := by
  have hq : (cpaRecvKC S F.K_on F.K_ro opk
      (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
      (.zero : Var [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
      (Δ := [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy])).queries
      (fun _ => 1) (fun _ => 0) ≤
      25 + 20 * min F.K_on S.N_dh + 10 * min F.K_on S.N_sess_tot :=
    cpaRecvKC_queries_prim_le S F.K_on F.K_ro opk _ _
  have hdh : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hsess : min F.K_on S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  unfold cpaRecvArmC
  simp only [Comp.queries, syncFixedShadowRespC_queries_zero, Nat.add_zero]
  refine le_trans (liftAuthPrim1_queries_prim_le _ _) ?_
  simp only [letV, queries_letC]
  unfold cpaArmQ0; omega

private theorem cpaRoArm_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (Comp.bind
      (roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface
        [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ cpaArmQ0 S := by
  have hz : (roFixedShadowArmC aiAuthPrim F.K_cap
      (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0 :
      Comp pqAtomicOps pqAuthPrimIface
        [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
    roFixedShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap _ _
  simp only [Comp.queries, Nat.add_zero]; omega

private theorem cpaRoRootArm_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (Comp.bind
      (roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface
        [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ cpaArmQ0 S := by
  have hz : (roRootFixedShadowArmC aiAuthPrim F.K_cap
      (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0 :
      Comp pqAtomicOps pqAuthPrimIface
        [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
    roRootFixedShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap _ _
  simp only [Comp.queries, Nat.add_zero]; omega

theorem cpaKindHandlePreC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (cpaKindHandlePreC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh + 12 * S.N_sess_tot := by
  have hSend : ∀ opk : Bool,
      (Comp.bind (liftAuthPrim1 (cpaSendPreInner S F opk)
          (.pair (.fst .v1) .v0 :
            Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _))
        (.caseSum .v0
          (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.snd (.snd (.snd .v0))))
              (fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v3))
            (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
          (.ret (.inr (.pair (.fst .v0)
            (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ cpaArmQ0 S := fun opk => by
    let Δs := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy]
    have hq : (cpaSendSlotKB S F.K_on F.K_ro opk true
        (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
        (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
        (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
        (Δ := Δs)).queries (fun _ => 1) (fun _ => 0) ≤ 25 + 20 * min F.K_on S.N_dh :=
      cpaSendSlotKB_queries_prim_le S F.K_on F.K_ro opk true _ _ _ _
    have hdh : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    simp only [Comp.queries, syncRoBothC_queries_zero, Nat.add_zero, Nat.max_self]
    refine le_trans (liftAuthPrim1_queries_prim_le _ _) ?_
    simp only [cpaSendPreInner, letV, bindV, caseSumV, queries_letC, Comp.queries,
      Nat.add_zero, Nat.max_self]
    unfold cpaArmQ0; omega
  unfold cpaKindHandlePreC; dsimp only
  exact dispatchAuthQ_queries_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (cpaWrapInl_queries_prim_le S (cpaBaseArmC_queries_prim_le S _ (initPrin1KeyFixedKB_queries_prim_le F _ _) (by unfold cpaArmQ0; omega)))
    (cpaWrapInl_queries_prim_le S (cpaBaseArmC_queries_prim_le S _ (Nat.le_of_eq (corruptFixedKB_queries_prim_le F _ _)) (by unfold cpaArmQ0; omega)))
    (cpaWrapInl_queries_prim_le S (cpaBaseArmC_queries_prim_le S _ (genSpkFixedKB_queries_prim_le F _ _) (by unfold cpaArmQ0; omega)))
    (cpaWrapInl_queries_prim_le S (cpaBaseArmC_queries_prim_le S _ (genOpkFixedKB_queries_prim_le F _ _) (by unfold cpaArmQ0; omega)))
    (hSend true) (hSend false)
    (cpaWrapInl_queries_prim_le S (cpaRecvArmC_queries_prim_le S F true))
    (cpaWrapInl_queries_prim_le S (cpaRecvArmC_queries_prim_le S F false))
    (cpaWrapInl_queries_prim_le S (cpaRoArm_queries_prim_le S F))
    (cpaWrapInl_queries_prim_le S (cpaRoRootArm_queries_prim_le S F))
    (by simp only [Comp.queries]; exact Nat.zero_le _)
    (cpaWrapInl_queries_prim_le S (cpaBaseArmC_queries_prim_le S _ (registerFixedKB_queries_prim_le _ _) (by unfold cpaArmQ0; omega)))

theorem cpaKindChDoneC_queries_prim_le :
    cpaKindChDoneC.queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : cpaDefaultChC.queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS = 0 :=
    cpa_chDone_queries zeroSetup 0
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW cpaDefaultChC
  apply Nat.eq_zero_of_le_zero
  unfold cpaKindChDoneC
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact le_trans hm (by omega)

theorem cpaKindResumeC_queries_prim_le (S : Setup) :
    (cpaKindResumeC S).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : cpaResumeC.queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS = 0 := cpa_resume_queries S 0
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW cpaResumeC
  apply Nat.eq_zero_of_le_zero
  unfold cpaKindResumeC
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact le_trans hm (by omega)

theorem cpaKindHandlePostC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (cpaKindHandlePostC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh + 12 * S.N_sess_tot := by
  have hSend : ∀ opk : Bool,
      (Comp.bind (liftAuthPrim1 (cpaSendPostInner S F opk)
          (.pair (.fst .v1) .v0 :
            Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _))
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.snd (.snd (.snd .v0))))
            (fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ cpaArmQ0 S := fun opk => by
    let Δs := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy]
    have hq : (cpaSendSlotKB S F.K_on F.K_ro opk false
        (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
        (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
        (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
        (Δ := Δs)).queries (fun _ => 1) (fun _ => 0) ≤ 25 + 20 * min F.K_on S.N_dh :=
      cpaSendSlotKB_queries_prim_le S F.K_on F.K_ro opk false _ _ _ _
    have hdh : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
    simp only [Comp.queries, syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (liftAuthPrim1_queries_prim_le _ _) ?_
    simp only [cpaSendPostInner, letV, bindV, caseSumV, queries_letC, Comp.queries,
      Nat.add_zero, Nat.max_self]
    unfold cpaArmQ0; omega
  unfold cpaKindHandlePostC; dsimp only
  exact dispatchAuthQ_queries_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (cpaBaseArmC_queries_prim_le S _ (initPrin1KeyFixedKB_queries_prim_le F _ _) (by unfold cpaArmQ0; omega))
    (cpaBaseArmC_queries_prim_le S _ (Nat.le_of_eq (corruptFixedKB_queries_prim_le F _ _)) (by unfold cpaArmQ0; omega))
    (cpaBaseArmC_queries_prim_le S _ (genSpkFixedKB_queries_prim_le F _ _) (by unfold cpaArmQ0; omega))
    (cpaBaseArmC_queries_prim_le S _ (genOpkFixedKB_queries_prim_le F _ _) (by unfold cpaArmQ0; omega))
    (hSend true) (hSend false)
    (cpaRecvArmC_queries_prim_le S F true)
    (cpaRecvArmC_queries_prim_le S F false)
    (cpaRoArm_queries_prim_le S F)
    (cpaRoRootArm_queries_prim_le S F)
    (by simp only [Comp.queries]; exact Nat.zero_le _)
    (cpaBaseArmC_queries_prim_le S _ (registerFixedKB_queries_prim_le _ _) (by unfold cpaArmQ0; omega))

theorem cpaKindFinishC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (cpaKindFinishC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 20 * S.N_dh := by
  have hq : (cpaFinishC S F.K_on).queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS = min F.K_on S.N_dh * 5 :=
    cpa_finish_queries S F.K_on
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW (cpaFinishC S F.K_on)
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  unfold cpaKindFinishC
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact le_trans hm (by omega)

section CpaSizeHelpers

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (
  initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB registerFixedB
  hasDuplicateBytesDsl hasBadSigAuthDsl hasKemPkCollisionAuthDsl
  hasBadKemShCrRecordsDsl notAllChallengedCleanDsl findHonestC fhstSetBase
  peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted peMk peUpd
  sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk sbMk oeOpkSk oeOpkPk oeConsumed oeMk oeUpd buMk
  aseSpkHonest asePqspkHonest aseEkASk aseFresh aseChallenged
  ikrPqspkPk ikrKemCt ikrKemSs rkrPqspkPk rkrKemCt rkrKemSs
  asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
  asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
  asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
  asRoCache asRootRoCache asAdvKeys ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions
  ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots
  assNext assSendOpk assSendNoOpk assRecv assMk emptyAuthSlotStE
  stMk stUpd ahsMk ahsUpd ahsfMkSlots ahsfMk ahsfUpdSlots ahsfUpd
  emptyAuthStE emptyAuthHybridStE emptyAuthHybridStFixedE
  aInitPrin aPk aCorr aBundle boolOr boolBeq natEq nat2Eq nat3Eq isSomeE optFst optSnd
  caseOptV findMV anyMV eLet eCaseOpt eCaseSum eFind eAny eMap
  litB catB bytesCons widenB takeKB bytesLen bytesBeq bytesVarint u32OfNat u32Beq encEC encKEM
)

private theorem liftExpr1_size_le {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a))
    {C : ℕ} (h : e.size + exprLitSize e + 1 ≤ C) :
    (liftExpr1 e argE).size ≤ argE.size + C := by
  simp only [liftExpr1, Expr.size, exprRename_size, mapExpr_size]; omega

private theorem fixedRoCacheE_size_le {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRoCacheE fhstE).size ≤ fhstE.size + 25 :=
  liftExpr1_size_le _ fhstE (by decide)

private theorem fixedRootRoCacheE_size_le {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRootRoCacheE fhstE).size ≤ fhstE.size + 25 :=
  liftExpr1_size_le _ fhstE (by decide)

private theorem cpaWrapInl_size (S : Setup) {a b : Ty pqAtomicSig}
    (m : Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) b)).size =
      m.size + 4 := by
  simp only [Comp.size, Expr.size, Expr.v0]

private theorem cpa_bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem bits_fuels_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    bits F.K_on ≤ bits (stepCostBudget S b) ∧ bits F.K_ro ≤ bits (stepCostBudget S b) ∧
    bits (min b.q_total S.N_send_tot) ≤ bits (stepCostBudget S b) ∧
    bits (min F.K_on S.N_dh) ≤ bits (stepCostBudget S b) ∧
    bits (4 * min F.K_on S.N_dh) ≤ bits (stepCostBudget S b) ∧
    bits (avlHeightCap F.K_cap) ≤ bits (stepCostBudget S b) := by
  intro F
  have hBud : 6 * b.q_total + 6 ≤ stepCostBudget S b := by
    have h1 : 6 * b.q_total + 6 ≤ 2 ^ 16 * (b.q_total + 1) := by omega
    have h2 : 2 ^ 16 * (b.q_total + 1) * 1 ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    unfold stepCostBudget; dsimp only; omega
  have hOn : F.K_on ≤ b.q_total := AuthCoreK.AuthKindFuels.K_on_le_q_total S b
  have hRo : F.K_ro ≤ b.q_total := AuthCoreK.AuthKindFuels.K_ro_le_q_total S b
  have hSend : min b.q_total S.N_send_tot ≤ b.q_total := Nat.min_le_left _ _
  have hDh : min F.K_on S.N_dh ≤ F.K_on := Nat.min_le_left _ _
  have hCap : F.K_cap ≤ 3 * b.q_total + 1 := by
    dsimp [F, AuthKindFuels.ofBudget]
    have := Nat.min_le_right b.q_on b.q_total
    have := Nat.min_le_right (b.q_ro + b.q_roRoot) b.q_total; omega
  have h1 : bits F.K_cap ≤ F.K_cap + 1 := by
    rcases Nat.eq_zero_or_pos F.K_cap with h0 | hn
    · rw [h0]; decide
    · unfold bits
      have := (Nat.log_lt_iff_lt_pow (by decide) (Nat.ne_of_gt hn)).mpr Nat.lt_two_pow_self; omega
  have hAvl : avlHeightCap F.K_cap ≤ stepCostBudget S b := by dsimp [avlHeightCap]; omega
  refine ⟨cpa_bits_mono (by omega), cpa_bits_mono (by omega), cpa_bits_mono (by omega),
    cpa_bits_mono (by omega), cpa_bits_mono (by omega), cpa_bits_mono hAvl⟩

private theorem cpa_F_X25519_len : _root_.SignalPqxdh.F_X25519.length = 32 := by decide

set_option linter.unusedSimpArgs false in
local macro "cpa_leaf_sz" : tactic => `(tactic| (
  simp (config := { maxSteps := 500000 }) only [
    cpaInitC, cpaFinishC, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDslK,
    hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    initPrin1KeyFixedKB, corruptFixedKB, genSpkFixedKB, genOpkFixedKB, registerFixedKB,
    initPrin1KeyFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, registerFixedB,
    findHonestC, fhstSetBase, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, sbMk, oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd, buMk,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, boolOr, boolBeq, natEq, nat2Eq, nat3Eq, isSomeE, optFst, optSnd,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, cpa_F_X25519_len,
    Nat.add_zero, Nat.zero_add, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  try dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have : bits 0 = 1 := by decide
  have : bits 1 = 1 := by decide
  have : bits 32 = 6 := by decide
  omega))

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem cpaLeaf_sizes (S : Setup) (b : QueryBudget) (F : AuthKindFuels) :
    (cpaInitC S b.q_total).size ≤ 300 + 2 * bits (min b.q_total S.N_send_tot) ∧
    compLitSize (cpaInitC S b.q_total) ≤ 50 ∧
    cpaDefaultChC.size ≤ 50 ∧ compLitSize cpaDefaultChC ≤ 50 ∧
    cpaResumeC.size ≤ 2000 ∧ compLitSize cpaResumeC ≤ 200 ∧
    (cpaFinishC S F.K_on).size ≤
      500 + 8 * bits F.K_on + 5 * bits (min F.K_on S.N_dh) + 6 * bits (4 * min F.K_on S.N_dh) ∧
    compLitSize (cpaFinishC S F.K_on) ≤ 50 := by
  refine ⟨by cpa_leaf_sz, by cpa_leaf_sz, by decide, by decide, by decide, by decide,
    by cpa_leaf_sz, by cpa_leaf_sz⟩

set_option linter.unusedSimpArgs false in
private theorem cpaFixedArmLeaf_sizes (F : AuthKindFuels) :
    let cIp := initPrin1KeyFixedKB F
      (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy .nat] _)
      (.zero : Var [.nat, authHybridStateFixedTy, .prod authHybridStateFixedTy .nat] _)
      (Δ := [.nat, authHybridStateFixedTy, .prod authHybridStateFixedTy .nat])
    let cCo := corruptFixedKB F
      (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy .nat] _)
      (.zero : Var [.nat, authHybridStateFixedTy, .prod authHybridStateFixedTy .nat] _)
      (Δ := [.nat, authHybridStateFixedTy, .prod authHybridStateFixedTy .nat])
    let cGs := genSpkFixedKB F
      (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy (.prod .nat .nat)] _)
      (.zero : Var [.prod .nat .nat, authHybridStateFixedTy,
        .prod authHybridStateFixedTy (.prod .nat .nat)] _)
      (Δ := [.prod .nat .nat, authHybridStateFixedTy, .prod authHybridStateFixedTy (.prod .nat .nat)])
    let cGo := genOpkFixedKB F
      (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy (.prod .nat (.prod .nat .nat))] _)
      (.zero : Var [.prod .nat (.prod .nat .nat), authHybridStateFixedTy,
        .prod authHybridStateFixedTy (.prod .nat (.prod .nat .nat))] _)
      (Δ := [.prod .nat (.prod .nat .nat), authHybridStateFixedTy,
        .prod authHybridStateFixedTy (.prod .nat (.prod .nat .nat))])
    let cRg := registerFixedKB
      (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy (B 32)] _)
      (.zero : Var [B 32, authHybridStateFixedTy, .prod authHybridStateFixedTy (B 32)] _)
      (Δ := [B 32, authHybridStateFixedTy, .prod authHybridStateFixedTy (B 32)])
    cIp.size ≤ 400 + 2 * bits F.K_on ∧ compLitSize cIp ≤ 50 ∧
    cCo.size ≤ 400 + 2 * bits F.K_on ∧ compLitSize cCo ≤ 50 ∧
    cGs.size ≤ 700 + 4 * bits F.K_on ∧ compLitSize cGs ≤ 100 ∧
    cGo.size ≤ 500 + 2 * bits F.K_on ∧ compLitSize cGo ≤ 50 ∧
    cRg.size ≤ 400 ∧ compLitSize cRg ≤ 50 := by
  dsimp only
  refine ⟨by cpa_leaf_sz, by cpa_leaf_sz, by cpa_leaf_sz, by cpa_leaf_sz,
    by cpa_leaf_sz, by cpa_leaf_sz, by cpa_leaf_sz, by cpa_leaf_sz, by decide, by decide⟩

private theorem cpaBaseArmC_size_le (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg → Comp pqxdhOps pqPrimIface Δ RSF)
    {Γ : List (Ty pqAtomicSig)} {Z L : ℕ}
    (hz : (step (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero).size ≤ Z)
    (hl : compLitSize (step (Γ₁ := [authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Γ₂ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg]) .zero .zero) ≤ L) :
    (cpaBaseArmC S step (Γ := Γ)).size ≤ 150 + 10 * Z + L := by
  have hm := liftAuthPrim1_size_le
    (letV (.fst (.var .zero)) fun fhst => letV (.snd (.var (.succ .zero))) fun x => step fhst x)
    (.pair (.snd (.snd (.fst .v1))) .v0 :
      Expr pqAtomicOps (embedTy arg :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  unfold cpaBaseArmC
  simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    cpaRebuildE, Comp.size, Expr.size, compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2,
    Nat.zero_add] at hm ⊢
  omega

private theorem cpaRecvArmC_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool)
    {Γ : List (Ty pqAtomicSig)} :
    (cpaRecvArmC S F opk (Γ := Γ)).size ≤
      130000 + 300 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
  let Δr := [recvQTy, authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy]
  have hl := liftAuthPrim1_size_le
    (letV (.fst (.var .zero)) fun fhst => letV (.snd (.var (.succ .zero))) fun x =>
      cpaRecvKC S F.K_on F.K_ro opk fhst x)
    (.pair (.snd (.snd (.fst .v1))) .v0 :
      Expr pqAtomicOps (authRecvQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _)
  have hz := cpaRecvKC_size_le S F.K_on F.K_ro opk
    (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
    (.zero : Var Δr _) (Δ := Δr)
  have hlt := cpaRecvKC_litSize_le S F.K_on F.K_ro opk
    (.zero : Var [authHybridStateFixedTy, .prod authHybridStateFixedTy recvQTy] _)
    (.zero : Var Δr _) (Δ := Δr)
  have hs := syncFixedShadowRespC_size_le (I := pqAuthPrimIface) F.K_cap
    (.v0 : Expr pqAtomicOps
      (embedTy RSF :: authRecvQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ) _) (.snd .v2)
  unfold cpaRecvArmC
  simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    cpaRebuildE, Comp.size, Expr.size, compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2,
    Nat.zero_add] at hl hs ⊢
  omega

private theorem cpaSendPreArm_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (Comp.bind (liftAuthPrim1 (cpaSendPreInner S F opk)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _))
      (.caseSum .v0
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.snd (.snd (.snd .v0))))
            (fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v3))
          (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
        (.ret (.inr (.pair (.fst .v0)
          (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))).size ≤
      130000 + 300 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
  let Δs := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy]
  have hl := liftAuthPrim1_size_le (cpaSendPreInner S F opk)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _)
  have hz := cpaSendSlotKB_size_le S F.K_on F.K_ro opk true
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  have hlt := cpaSendSlotKB_litSize_le S F.K_on F.K_ro opk true
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  let rSumTy := embedTy (.sum (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy cpaStTy)
    (.prod (.prod (B 158) (.prod (B 32) (B 32))) (.prod cpaPayloadTy cpaStTy)))
  let ΓL := [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy cpaStTy),
    rSumTy, authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
  have hr1 := fixedRoCacheE_size_le (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓL _))))
  have hr2 := fixedRootRoCacheE_size_le (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓL _))))
  have hs := syncRoBothC_size_le (I := pqAuthPrimIface) F.K_cap
    (fixedRoCacheE (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓL _)))))
    (fixedRootRoCacheE (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓL _))))) (.snd .v3)
  simp only [cpaSendPreInner, letV, bindV, caseSumV, v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v3, Nat.zero_add, Nat.add_zero]
    at hl hr1 hr2 hs ⊢
  omega

private theorem cpaSendPostArm_size_le (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    (Comp.bind (liftAuthPrim1 (cpaSendPostInner S F opk)
        (.pair (.fst .v1) .v0 :
          Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _))
      (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.snd (.snd (.snd .v0))))
          (fixedRootRoCacheE (.snd (.snd (.snd .v0)))) (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))).size ≤
      130000 + 300 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
  let Δs := [authHybridStateFixedTy, .nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy]
  have hl := liftAuthPrim1_size_le (cpaSendPostInner S F opk)
    (.pair (.fst .v1) .v0 :
      Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _)
  have hz := cpaSendSlotKB_size_le S F.K_on F.K_ro opk false
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  have hlt := cpaSendSlotKB_litSize_le S F.K_on F.K_ro opk false
    (.zero : Var [.nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var [.nat, .nat, sendQTy, cpaStTy, .prod cpaStTy sendQTy] _)
    (.zero : Var Δs _) (.zero : Var [sendQTy, cpaStTy, .prod cpaStTy sendQTy] _) (Δ := Δs)
  let ΓP := [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy cpaStTy),
    authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
  have hr1 := fixedRoCacheE_size_le (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓP _))))
  have hr2 := fixedRootRoCacheE_size_le (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓP _))))
  have hs := syncRoBothC_size_le (I := pqAuthPrimIface) F.K_cap
    (fixedRoCacheE (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓP _)))))
    (fixedRootRoCacheE (.snd (.snd (.snd (.v0 : Expr pqAtomicOps ΓP _))))) (.snd .v2)
  simp only [cpaSendPostInner, letV, bindV, caseSumV, v, aNone,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.size, Expr.size,
    compLitSize, exprLitSize, Expr.v0, Expr.v1, Expr.v2, Nat.zero_add, Nat.add_zero]
    at hl hr1 hr2 hs ⊢
  omega

end CpaSizeHelpers

theorem aeadCpa1KeyKindProg_size_le (S : Setup) (b : QueryBudget) :
    (aeadCpa1KeyKindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  let F := AuthKindFuels.ofBudget S b
  obtain ⟨hInitS, hInitL, hChS, hChL, hResS, hResL, hFinS, hFinL⟩ := cpaLeaf_sizes S b F
  obtain ⟨hIpS, hIpL, hCoS, hCoL, hGsS, hGsL, hGoS, hGoL, hRgS, hRgL⟩ := cpaFixedArmLeaf_sizes F
  obtain ⟨hbOn, hbRo, hbSend, hbDh, hbDh4, hbAvl⟩ := bits_fuels_le_stepCostBudget S b
  have hInit : (cpaKindInitC S b).size ≤ 3600 + 20 * bits (min b.q_total S.N_send_tot) := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (cpaInitC S b.q_total)
    have he := emptyRoBothAvlE_size_le (Γ := [.prod .unit (embedTy cpaStTy), .unit])
    unfold cpaKindInitC; simp only [Comp.size, Expr.size, Expr.v0]; omega
  have hCh : cpaKindChDoneC.size ≤ 600 := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe cpaDefaultChC
    unfold cpaKindChDoneC; simp only [Comp.size, Expr.size, Expr.v0, compRename_size]; omega
  have hRes : (cpaKindResumeC S).size ≤ 21000 := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe cpaResumeC
    unfold cpaKindResumeC; simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, compRename_size]; omega
  have hFin : (cpaKindFinishC S F).size ≤
      5100 + 80 * bits F.K_on + 50 * bits (min F.K_on S.N_dh) + 60 * bits (4 * min F.K_on S.N_dh) := by
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (cpaFinishC S F.K_on)
    unfold cpaKindFinishC; simp only [Comp.size, Expr.size, Expr.v0, compRename_size]; omega
  have hRoA : (Comp.bind
      (roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).size ≤
      2400 + 2 * bits (avlHeightCap F.K_cap) := by
    have h : (roFixedShadowArmC aiAuthPrim F.K_cap
        (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0 :
        Comp pqAtomicOps pqAuthPrimIface
          [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size ≤
        2350 + 2 * bits (avlHeightCap F.K_cap) +
          (Expr.pair (.snd (.snd (.fst .v1))) (.snd .v1) :
            Expr pqAtomicOps [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size +
          (Expr.v0 : Expr pqAtomicOps [PB 192, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size :=
      roFixedShadowArmC_size_le aiAuthPrim F.K_cap _ _
    simp only [cpaRebuildE, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h ⊢; omega
  have hRoRA : (Comp.bind
      (roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).size ≤
      2450 + 2 * bits (avlHeightCap F.K_cap) := by
    have h : (roRootFixedShadowArmC aiAuthPrim F.K_cap
        (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0 :
        Comp pqAtomicOps pqAuthPrimIface
          [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size ≤
        2400 + 2 * bits (avlHeightCap F.K_cap) +
          (Expr.pair (.snd (.snd (.fst .v1))) (.snd .v1) :
            Expr pqAtomicOps [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size +
          (Expr.v0 : Expr pqAtomicOps [.prod (PB 32) (PB 32), .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size :=
      roRootFixedShadowArmC_size_le aiAuthPrim F.K_cap _ _
    simp only [cpaRebuildE, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h ⊢; omega
  have hB1 := cpaBaseArmC_size_le S (fun fhst u => initPrin1KeyFixedKB F fhst u) (Γ := [(authCodec S).Q]) hIpS hIpL
  have hB2 := cpaBaseArmC_size_le S (fun fhst u => corruptFixedKB F fhst u) (Γ := [(authCodec S).Q]) hCoS hCoL
  have hB3 := cpaBaseArmC_size_le S (fun fhst x => genSpkFixedKB F fhst x) (Γ := [(authCodec S).Q]) hGsS hGsL
  have hB4 := cpaBaseArmC_size_le S (fun fhst x => genOpkFixedKB F fhst x) (Γ := [(authCodec S).Q]) hGoS hGoL
  have hB12 := cpaBaseArmC_size_le S (fun fhst sk => registerFixedKB fhst sk) (Γ := [(authCodec S).Q]) hRgS hRgL
  have hRcvT := cpaRecvArmC_size_le S F true (Γ := [(authCodec S).Q])
  have hRcvF := cpaRecvArmC_size_le S F false (Γ := [(authCodec S).Q])
  have hqE : (Expr.var (.succ .zero) :
      Expr pqAtomicOps [.prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q] _).size = 1 := rfl
  have hPost : (cpaKindHandlePostC S F).size ≤
      551000 + 1300 * bits F.K_on + 400 * bits F.K_ro + 20 * bits (avlHeightCap F.K_cap) := by
    have hChP : (Comp.ret (.pair aNoneAtomicE .v1) :
        Comp pqAtomicOps pqAuthPrimIface [.unit, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))).size ≤ 35 := by
      simp only [aNoneAtomicE, Comp.size, Expr.size, Expr.v1]; omega
    unfold cpaKindHandlePostC; dsimp only
    refine le_trans (dispatchAuthQ_size_le _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.le_of_eq hqE) hB1) hB2) hB3) hB4)
      (cpaSendPostArm_size_le S F true)) (cpaSendPostArm_size_le S F false))
      hRcvT) hRcvF) hRoA) hRoRA) hChP) hB12) 21) (by omega)
  have hPre : (cpaKindHandlePreC S F).size ≤
      551000 + 1300 * bits F.K_on + 400 * bits F.K_ro + 20 * bits (avlHeightCap F.K_cap) := by
    have hw : ∀ {a : Ty pqAtomicSig} {m : Comp pqAtomicOps pqAuthPrimIface
        [a, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))} {k : ℕ},
        m.size ≤ k →
        (Comp.bind m (.ret (.inl .v0)) :
          Comp pqAtomicOps pqAuthPrimIface [a, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
            (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))
              (.prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
                (.prod (embedTy cpaPayloadTy) (.prod (embedTy cpaStTy) roBothAvlTy))))).size ≤ k + 4 :=
      fun h => by rw [cpaWrapInl_size S]; exact Nat.add_le_add_right h 4
    have hChPre : (Comp.ret (.inl (.pair aNoneAtomicE .v1)) :
        Comp pqAtomicOps pqAuthPrimIface [.unit, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
          (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))
            (.prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
              (.prod (embedTy cpaPayloadTy) (.prod (embedTy cpaStTy) roBothAvlTy))))).size ≤ 36 := by
      simp only [aNoneAtomicE, Comp.size, Expr.size, Expr.v1]; omega
    unfold cpaKindHandlePreC; dsimp only
    refine le_trans (dispatchAuthQ_size_le _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.le_of_eq hqE) (hw hB1)) (hw hB2)) (hw hB3)) (hw hB4))
      (cpaSendPreArm_size_le S F true)) (cpaSendPreArm_size_le S F false))
      (hw hRcvT)) (hw hRcvF)) (hw hRoA)) (hw hRoRA)) hChPre) (hw hB12)) 21) (by omega)
  have hB : reductionSizeBudget = 2 ^ 24 := rfl
  unfold aeadCpa1KeyKindProg TwoStageCostedReduction.size
  dsimp only [F] at *; rw [hB]; omega

end CpaBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostCpa
