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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostHm
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseClampedFixed
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacProofs

/-!
# Per-Reduction `pqAtomicOps` PRF Bounds and Fuel Fold Lemmas

Proves fuel and bit-length bounds for `AuthKindFuels.ofBudget`, together with kind-split `costAt`,
static `cost`, primitive-query, and `CostedReduction.size` bounds over `pqAtomicOps` for
`prfCk1KeyKindProg`, `prfMsgKeys1KeyKindProg`, and `prfHmac1KeyKindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost

open _root_.ReductionDsl (Ty Comp Expr Env pqAtomicSig pqAtomicOps PB bits reductionSizeBudget)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface pqPrfMkIface pqPrfHmacIface)
open _root_.SignalPqxdh.Security
  (stepCostBudget authQueryKind authPrimIfacePrimQueryWeight authChalIfacePrimQueryWeight
   samplerZeroQueryWeight)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy mapComp tlAuthPrim tlPrfMk tlPrfHmac
   aiAuthPrim aiPrfMk aiPrfHmac
   tlAuthPrim_primW tlPrfMk_primW tlPrfHmac_primW
   tlAuthPrim_sizeLe tlPrfMk_sizeLe tlPrfHmac_sizeLe
   mapComp_cost_two_mul_le mapComp_cost_eleven_mul_le mapComp_queries_le mapComp_size_le
   compRename_cost compRename_queries compRename_size
   atomicSize_le_budget bits_le_bits_stepCostBudget
   sampR64W r64W castLegacySamp)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (prfCkStTy prfMkStTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac (hmStTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy emptyRoBothAvlE aNoneAtomicE fixedRoCacheE fixedRootRoCacheE
   syncFixedShadowRespC syncRoBothC authSendQAtomicTy authRecvQAtomicTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (prfCkKindInitC prfCkKindHandleC prfCkKindFinishC prfCk1KeyKindProg
   ckRebuildE ckBaseArmC liftAuthPrim1
   prfMkKindInitC prfMkKindHandleC prfMkKindFinishC prfMsgKeys1KeyKindProg
   mkRebuildE mkBaseArmC liftPrfMk1 mkPostRunC
   prfHmacKindInitC prfHmacKindHandleC prfHmacKindFinishC prfHmac1KeyKindProg
   hmRebuildE hmBaseArmC liftPrfHmac1 hmPostRunC
   authCkSendKB authCkRecvKB authMkSendPreKB authMkRecvPreKB hmSendKC hmRecvKC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostPrf
  (authCkSendKB_cost_le authCkSendKB_r64_le authCkSendKB_queries_prim_le
   authCkSendKB_size_le authCkSendKB_litSize_le
   authCkRecvKB_cost_le authCkRecvKB_r64_le authCkRecvKB_queries_prim_le
   authCkRecvKB_size_le authCkRecvKB_litSize_le
   authMkSendPreKB_cost_le authMkSendPreKB_r64_le authMkSendPreKB_queries_prim_le
   authMkSendPreKB_size_le authMkSendPreKB_litSize_le
   authMkRecvPreKB_cost_le authMkRecvPreKB_r64_le authMkRecvPreKB_queries_prim_le
   authMkRecvPreKB_size_le authMkRecvPreKB_litSize_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostHm
  (hmSendKC_cost_le hmSendKC_r64_le hmSendKC_queries_prim_le
   hmSendKC_size_le hmSendKC_litSize_le
   hmRecvKC_cost_le hmRecvKC_r64_le hmRecvKC_queries_prim_le
   hmRecvKC_size_le hmRecvKC_litSize_le)

/-! ## `AuthKindFuels.ofBudget` Cap and Fuel Bounds -/

section BudgetFuels

theorem ofBudget_K_cap_le (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_cap ≤ 3 * b.q_total + 1 := by
  dsimp [AuthKindFuels.ofBudget]
  have h1 : min b.q_on b.q_total ≤ b.q_total := Nat.min_le_right _ _
  have h2 : min (b.q_ro + b.q_roRoot) b.q_total ≤ b.q_total := Nat.min_le_right _ _
  omega

theorem ofBudget_bits_K_cap_le_bits (S : Setup) (b : QueryBudget) :
    bits (AuthKindFuels.ofBudget S b).K_cap ≤ bits b.q_total + 2 := by
  have hcap := ofBudget_K_cap_le S b
  rcases Nat.eq_zero_or_pos b.q_total with h0 | hpos
  · have hk : (AuthKindFuels.ofBudget S b).K_cap ≤ 1 := by omega
    have hlog : Nat.log 2 (AuthKindFuels.ofBudget S b).K_cap ≤ Nat.log 2 1 :=
      Nat.log_mono_right hk
    unfold bits
    have : Nat.log 2 1 = 0 := by decide
    omega
  · have h4 : (AuthKindFuels.ofBudget S b).K_cap ≤ 4 * b.q_total := by omega
    have hlog1 : Nat.log 2 (AuthKindFuels.ofBudget S b).K_cap ≤ Nat.log 2 (4 * b.q_total) :=
      Nat.log_mono_right h4
    have hlog2 : Nat.log 2 (4 * b.q_total) = Nat.log 2 b.q_total + 2 := by
      have h4eq : 4 * b.q_total = b.q_total * 2 * 2 := by ring
      rw [h4eq, Nat.log_mul_base (b := 2) (by decide) (by omega),
        Nat.log_mul_base (b := 2) (by decide) (by omega)]
    unfold bits
    omega

theorem ofBudget_bits_K_cap_le (S : Setup) (b : QueryBudget) :
    bits (AuthKindFuels.ofBudget S b).K_cap ≤ b.q_total + 3 := by
  have h := ofBudget_bits_K_cap_le_bits S b
  unfold bits at h ⊢
  rcases Nat.eq_zero_or_pos b.q_total with h0 | hpos
  · rw [h0] at h ⊢
    have : Nat.log 2 0 = 0 := rfl
    omega
  · have hself : Nat.log 2 b.q_total < b.q_total := Nat.log_lt_self 2 (by omega)
    omega

theorem ofBudget_K_on_le (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_on ≤ b.q_total :=
  Nat.min_le_left _ _

theorem ofBudget_K_on1_le (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_on1 ≤ b.q_total :=
  Nat.min_le_left _ _

theorem ofBudget_M_dh_le_M_on (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).M_dh ≤ (AuthKindFuels.ofBudget S b).M_on :=
  Nat.min_le_left _ _

theorem ofBudget_M_sess_le_M_on (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).M_sess ≤ (AuthKindFuels.ofBudget S b).M_on :=
  Nat.min_le_left _ _

theorem min_K_on_N_dh_le_K_on (S : Setup) (F : AuthKindFuels) :
    min F.K_on S.N_dh ≤ F.K_on :=
  Nat.min_le_left _ _

end BudgetFuels

/-! ## `prfCk1KeyKindProg` and `prfMsgKeys1KeyKindProg` Bounds -/

section PrfCkMkBounds

private theorem emptyRoBothAvlE_cost_eq {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).cost = (emptyRoBothAvlE (Γ := [])).cost :=
  rfl

private theorem emptyRoBothAvlE_cost_le {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).cost ≤ 500 := by
  rw [emptyRoBothAvlE_cost_eq]
  decide

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (prfCkInitDslK prfCkFinishDsl prfMsgKeysInitDslK prfMsgKeysFinishDsl
   prfCkFinishDsl_cost prfCkFinishDsl_queries
   prfMsgKeysFinishDsl_cost prfMsgKeysFinishDsl_queries_prim
   finalizeAuthFixedDsl finalizeAuthFixedBodyDsl allHonestEcPksAuthDslK
   emptyAuthHybridStFixedE emptyAuthHybridStE emptyAuthStE emptyAuthSlotStE
   ahsfMk ahsfMkSlots assMk ahsMk stMk mkcMk
   cost_samplePrim cost_sampleChal cost_letC v
   bindV letV liftPrimComp samplePrim sampleChal queryPrim queries_letC)

private theorem sampR64W_bool :
    sampR64W tlAuthPrim.hsmp _root_.SignalPqxdh.LegacyCosted.PSamp.bool = 0 := rfl

private theorem sampR64W_index (n : ℕ) :
    sampR64W tlAuthPrim.hsmp (_root_.SignalPqxdh.LegacyCosted.PSamp.index n) = 0 := rfl

private theorem sampR64W_mk_bool :
    sampR64W tlPrfMk.hsmp _root_.SignalPqxdh.LegacyCosted.PSamp.bool = 0 := rfl

private theorem sampR64W_mk_index (n : ℕ) :
    sampR64W tlPrfMk.hsmp (_root_.SignalPqxdh.LegacyCosted.PSamp.index n) = 0 := rfl

private theorem bits_succ_le_log_add_two {x y : ℕ} (h : x ≤ y) :
    bits (x + 1) ≤ Nat.log 2 y + 2 := by
  unfold bits
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h1 : Nat.log 2 (x + 1) ≤ Nat.log 2 (x * 2) := Nat.log_mono_right (by omega)
    have h2 : Nat.log 2 (x * 2) = Nat.log 2 x + 1 := Nat.log_mul_base (by omega) (by omega)
    have h3 : Nat.log 2 x ≤ Nat.log 2 y := Nat.log_mono_right h
    omega

private theorem queries_liftPrimComp_r64 :
    ∀ {Γ t} (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t),
      (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.msgKeyPrfOracle) c).queries
        (fun _ => 0) (sampR64W tlPrfMk.hsmp) =
      c.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp)
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp only [liftPrimComp, Comp.queries, queries_liftPrimComp_r64 m, queries_liftPrimComp_r64 k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [liftPrimComp, Comp.queries, queries_liftPrimComp_r64 t, queries_liftPrimComp_r64 e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [liftPrimComp, Comp.queries, queries_liftPrimComp_r64 b]

private theorem tlPrfMk_mkPrimW {Γ : List (Ty pqAtomicSig)}
    (g : _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface.Tag)
    (e : Expr _root_.ReductionDsl.pqAtomicOps Γ
      (embedTy (_root_.SignalPqxdh.LegacyCosted.pqPrfMkIface.dom g))) :
    (tlPrfMk.mapQuery g e).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW g := by
  rcases g with g | g <;> exact tlPrfMk_primW _ e

theorem prfCkKindInitC_cost_le (S : Setup) (b : QueryBudget) :
    (prfCkKindInitC S b).cost ≤ 1000 + 2 * Nat.log 2 S.N_sess_tot := by
  have hc : (prfCkInitDslK S b.q_total).cost = 71 + bits (min b.q_total S.N_sess_tot) := by
    simp only [prfCkInitDslK, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
      ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, cost_samplePrim,
      _root_.SignalPqxdh.LegacyCosted.PSamp.cost, _root_.SignalPqxdh.LegacyCosted.Ty.wd,
      v, Comp.cost, Expr.cost, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bits_0]
    omega
  have hr64 : (prfCkInitDslK S b.q_total).queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
    simp [prfCkInitDslK, bindV, samplePrim, sampR64W_bool, sampR64W_index, Comp.queries]
  have hlog : bits (min b.q_total S.N_sess_tot) ≤ Nat.log 2 S.N_sess_tot + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_right b.q_total S.N_sess_tot)) 1
  have hm := mapComp_cost_two_mul_le tlAuthPrim (prfCkInitDslK S b.q_total)
  have he := emptyRoBothAvlE_cost_le
    (Γ := [embedTy (.prod .unit prfCkStTy), .prod (PB 32) (PB 32)])
  unfold prfCkKindInitC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  omega

theorem prfCkKindHandleC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy prfCkStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 1) :
    (prfCkKindHandleC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  unfold prfCkKindHandleC
  dsimp only
  refine le_trans (AuthCoreKCostBase.dispatchAuthQ_v1_costAt_kind1_le
    _ _ _ _ _ _ _ _ _ _ _ _ s q .nil (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roRootFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega

private theorem liftAuthPrim1_cost_le
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {B R M : ℕ}
    (hc : c.cost ≤ B) (hr : c.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) ≤ R)
    (hM : 3 * B + 78 * R ≤ 2 * M) :
    (liftAuthPrim1 c e).cost ≤ M + e.cost + 2 := by
  have hm := mapComp_cost_two_mul_le tlAuthPrim c
  unfold liftAuthPrim1
  simp only [Comp.cost, compRename_cost]
  omega

private theorem liftAuthPrim1_queries_le
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {Q : ℕ}
    (hq : c.queries (fun _ => 1) (fun _ => 0) ≤ Q) :
    (liftAuthPrim1 c e).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
    _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authPrimIfacePrimQueryWeight tlAuthPrim_primW c
  have hq' : c.queries _root_.SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
      _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ Q := hq
  unfold liftAuthPrim1
  simp only [Comp.queries, Nat.zero_add, compRename_queries]
  exact le_trans hm hq'

private theorem ckBaseArmC_cost_le (S : Setup) (F : AuthKindFuels)
    {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy →
      _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
        _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)}
    (hc : (step
      (Δ := [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var
        [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).cost ≤
      9500 + F.K_on * 50)
    (hr : (step
      (Δ := [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var
        [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).queries
      (fun _ => 0) (sampR64W rfl) ≤ 3) :
    (ckBaseArmC S step (Γ := Γ)).cost ≤ 14440 + 75 * F.K_on := by
  unfold ckBaseArmC
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (liftAuthPrim1_cost_le _ _ (B := 9508 + F.K_on * 50) (R := 3) (M := 14390 + 75 * F.K_on)
      (by simp only [letV, cost_letC, Expr.cost]; omega)
      (by simp only [letV, queries_letC]; exact hr)
      (by omega)) _) 1) ?_
  simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem ckBaseArmC_queries_le (S : Setup)
    {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy →
      _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
        _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)} {Q : ℕ}
    (hq : (step
      (Δ := [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var
        [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).queries
      (fun _ => 1) (fun _ => 0) ≤ Q) :
    (ckBaseArmC S step (Γ := Γ)).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  unfold ckBaseArmC
  simp only [Comp.queries, Nat.add_zero]
  apply liftAuthPrim1_queries_le
  simp only [letV, queries_letC]
  exact hq

private theorem letC_cost_step {ι : Type} {T : _root_.OracleSpec ι}
    {I : _root_.ReductionDsl.Iface _root_.SignalPqxdh.LegacyCosted.pqSig T}
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Γ a)
    (body : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps I (a :: Γ) r)
    {B : ℕ} (hb : body.cost ≤ B) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC e body).cost ≤
      e.cost + B + 2 := by
  rw [cost_letC]; omega

private theorem prfCkKindHandleC_cost_le_aux (S : Setup) (F : AuthKindFuels) :
    (prfCkKindHandleC S F).cost ≤
      29000 + 20300 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) := by
  have hSend : ∀ opk : Bool,
      (.bind (.bind (liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkSendKB S F.K_on F.K_ro opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
        (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))) :
        Comp pqAtomicOps pqAuthPrimIface
          [authSendQAtomicTy, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy))).cost ≤
      29000 + 20300 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2058) := by
    intro opk
    simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right
        (liftAuthPrim1_cost_le _ _
          (B := 19035 + 13469 * F.K_on + 16000 * min F.K_on S.N_dh + 531 * F.K_ro)
          (R := 2)
          (M := 28640 + 20204 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro)
          ?_ ?_ (by omega)) _) 1) _) 1) ?_
    · dsimp only [letV]
      refine le_trans (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _
        (letC_cost_step _ _ (letC_cost_step _ _ (authCkSendKB_cost_le S F.K_on F.K_ro opk _ _ _ _)))))) ?_
      simp only [v, Expr.cost]; omega
    · simp only [letV, queries_letC]
      exact authCkSendKB_r64_le S F.K_on F.K_ro opk _ _ _ _
    · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left
          (AuthCoreKCostBase.syncFixedShadowRespC_cost_le (I := pqAuthPrimIface) F.K_cap _ _) _) 1) _) 1) ?_
      simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
      omega
  have hRecv : ∀ opk : Bool,
      (.bind (.bind (liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkRecvKB S F.K_on F.K_ro opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
        (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))) :
        Comp pqAtomicOps pqAuthPrimIface
          [authRecvQAtomicTy, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy))).cost ≤
      29000 + 20300 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2058) := by
    intro opk
    simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right
        (liftAuthPrim1_cost_le _ _
          (B := 19035 + 13469 * F.K_on + 16000 * min F.K_on S.N_dh + 531 * F.K_ro)
          (R := 2)
          (M := 28640 + 20204 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro)
          ?_ ?_ (by omega)) _) 1) _) 1) ?_
    · dsimp only [letV]
      refine le_trans (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _
        (letC_cost_step _ _ (letC_cost_step _ _ (authCkRecvKB_cost_le S F.K_on F.K_ro opk _ _ _ _)))))) ?_
      simp only [v, Expr.cost]; omega
    · simp only [letV, queries_letC]
      exact authCkRecvKB_r64_le S F.K_on F.K_ro opk _ _ _ _
    · refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left
          (AuthCoreKCostBase.syncFixedShadowRespC_cost_le (I := pqAuthPrimIface) F.K_cap _ _) _) 1) _) 1) ?_
      simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
      omega
  unfold prfCkKindHandleC
  dsimp only
  refine le_trans (AuthCoreKCostBase.dispatchAuthQ_cost_le
    _ _ _ _ _ _ _ _ _ _ _ _ _
    (B := 29000 + 20300 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro +
      (8500 * bits F.K_cap + 2058))
    ?_ ?_ ?_ ?_ (hSend true) (hSend false) (hRecv true) (hRecv false) ?_ ?_ ?_ ?_) ?_
  · exact le_trans (ckBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.initPrin1KeyFixedKB_cost_le F _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.initPrin1KeyFixedKB_r64_le]; omega)) (by omega)
  · exact le_trans (ckBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.corruptFixedKB_cost_le F _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.corruptFixedKB_r64_le]; omega)) (by omega)
  · exact le_trans (ckBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.genSpkFixedKB_cost_le F _ _) (by omega))
      (le_trans (AuthCoreKCostBaseClampedFixed.genSpkFixedKB_r64_le F _ _) (by decide))) (by omega)
  · exact le_trans (ckBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.genOpkFixedKB_cost_le F _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.genOpkFixedKB_r64_le]; omega)) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roRootFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [ckRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost, aNoneAtomicE, Expr.cost, Expr.v1]; omega
  · exact le_trans (ckBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.registerFixedKB_cost_le _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.registerFixedKB_r64_le]; omega)) (by omega)
  · simp only [Expr.cost]; omega

theorem prfCkKindHandleC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy prfCkStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (_hk : authQueryKind q = 0) :
    (prfCkKindHandleC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      29000 + 20300 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  (Comp.costAt_le_cost _ _).trans (prfCkKindHandleC_cost_le_aux S F)

theorem prfCkKindHandleC_cost_le (S : Setup) (F : AuthKindFuels) :
    (prfCkKindHandleC S F).cost ≤
      29000 + 20300 * F.K_on + 24000 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  prfCkKindHandleC_cost_le_aux S F

theorem prfCkKindFinishC_cost_le (S : Setup) (F : AuthKindFuels) :
    (prfCkKindFinishC S F).cost ≤
      200 + 620 * min F.K_on S.N_dh + 1632 * (min F.K_on S.N_dh) ^ 2 +
        150 * F.K_on + 14267 * F.K_on ^ 2 := by
  have hc := prfCkFinishDsl_cost S F.K_on
  have hr64 : (prfCkFinishDsl S F.K_on).queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
    simp [prfCkFinishDsl, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
      allHonestEcPksAuthDslK, letV, queries_letC, samplePrim, queryPrim,
      sampR64W_bool, Comp.queries]
  have hm := mapComp_cost_two_mul_le tlAuthPrim (prfCkFinishDsl S F.K_on)
  unfold prfCkKindFinishC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  rw [compRename_cost]
  omega

theorem prfCkKindInitC_queries_prim_le (S : Setup) (b : QueryBudget) :
    (prfCkKindInitC S b).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : (prfCkInitDslK S b.q_total).queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS = 0 := by
    simp [prfCkInitDslK, bindV, samplePrim,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS, Comp.queries]
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW (prfCkInitDslK S b.q_total)
  apply Nat.eq_zero_of_le_zero
  unfold prfCkKindInitC
  simp only [Comp.queries, Nat.add_zero]
  exact le_trans hm (by omega)

theorem prfCkKindHandleC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (prfCkKindHandleC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh := by
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hSend : ∀ opk : Bool,
      (.bind (.bind (liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkSendKB S F.K_on F.K_ro opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
        (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))) :
        Comp pqAtomicOps pqAuthPrimIface
          [authSendQAtomicTy, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy))).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ 40 + 30 * S.N_dh := by
    intro opk
    simp only [Comp.queries, Nat.add_zero]
    rw [AuthCoreKCostBase.syncFixedShadowRespC_queries_zero, Nat.add_zero]
    refine le_trans (liftAuthPrim1_queries_le _ _ (Q := 20 + 26 * min F.K_on S.N_dh) ?_) (by omega)
    simp only [letV, queries_letC]
    exact authCkSendKB_queries_prim_le S F.K_on F.K_ro opk _ _ _ _
  have hRecv : ∀ opk : Bool,
      (.bind (.bind (liftAuthPrim1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (.snd (v s))) fun idx =>
           letV (.fst (.snd (.snd (v s)))) fun chalP =>
           letV (.snd (.snd (.snd (v s)))) fun fhst =>
           authCkRecvKB S F.K_on F.K_ro opk idx chalP fhst x)
          (.pair (.fst .v1) .v0))
        (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
        (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))) :
        Comp pqAtomicOps pqAuthPrimIface
          [authRecvQAtomicTy, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy))).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤ 40 + 30 * S.N_dh := by
    intro opk
    simp only [Comp.queries, Nat.add_zero]
    rw [AuthCoreKCostBase.syncFixedShadowRespC_queries_zero, Nat.add_zero]
    refine le_trans (liftAuthPrim1_queries_le _ _ (Q := 20 + 26 * min F.K_on S.N_dh) ?_) (by omega)
    simp only [letV, queries_letC]
    exact authCkRecvKB_queries_prim_le S F.K_on F.K_ro opk _ _ _ _
  unfold prfCkKindHandleC
  dsimp only
  refine AuthCoreKCostBase.dispatchAuthQ_queries_le
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ?_ ?_ ?_ ?_ (hSend true) (hSend false) (hRecv true) (hRecv false) ?_ ?_ ?_ ?_
  · exact le_trans (ckBaseArmC_queries_le S _ (AuthCoreKCostBaseClampedFixed.initPrin1KeyFixedKB_queries_prim_le F _ _)) (by omega)
  · exact le_trans (ckBaseArmC_queries_le S _ (by rw [AuthCoreKCostBaseClampedFixed.corruptFixedKB_queries_prim_le])) (by omega)
  · exact le_trans (ckBaseArmC_queries_le S _ (AuthCoreKCostBaseClampedFixed.genSpkFixedKB_queries_prim_le F _ _)) (by omega)
  · exact le_trans (ckBaseArmC_queries_le S _ (AuthCoreKCostBaseClampedFixed.genOpkFixedKB_queries_prim_le F _ _)) (by omega)
  · simp only [Comp.queries]
    exact le_trans (Nat.add_le_add_right
      (le_of_eq (AuthCoreKCostBase.roFixedShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap _ _)) 0)
      (by omega)
  · simp only [Comp.queries]
    exact le_trans (Nat.add_le_add_right
      (le_of_eq (AuthCoreKCostBase.roRootFixedShadowArmC_queries_zero aiAuthPrim authPrimIfacePrimQueryWeight F.K_cap _ _)) 0)
      (by omega)
  · simp only [Comp.queries]; omega
  · exact le_trans (ckBaseArmC_queries_le S _ (AuthCoreKCostBaseClampedFixed.registerFixedKB_queries_prim_le _ _)) (by omega)

theorem prfCkKindFinishC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (prfCkKindFinishC S F).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 20 * S.N_dh := by
  have hq := prfCkFinishDsl_queries S F.K_on
  have hm := mapComp_queries_le tlAuthPrim
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
    authPrimIfacePrimQueryWeight tlAuthPrim_primW (prfCkFinishDsl S F.K_on)
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  unfold prfCkKindFinishC
  simp only [Comp.queries, Nat.zero_add]
  rw [compRename_queries]
  exact le_trans hm (by omega)

section SharedSizeHelpers

open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (compLitSize exprLitSize pqOpLitSize exprRename_size mapExpr_size)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (avlHeightCap)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqBytesOps pqU32Ops)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT RSF authHybridStateFixedTy ckSecb ckFhst mkcSecb mkcFhst
   initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB registerFixedB
   allHonestEcPksAuthDsl hasDuplicateBytesDsl hasBadSigAuthDsl hasKemPkCollisionAuthDsl
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
   aNone aInitPrin aPk aCorr aBundle boolOr boolBeq natEq nat2Eq nat3Eq isSomeE optFst optSnd
   caseOptV findMV anyMV eLet eCaseOpt eCaseSum eFind eAny eMap
   litB catB bytesCons widenB takeKB bytesLen bytesBeq bytesVarint u32OfNat u32Beq encEC encKEM)

private theorem emptyRoBothAvlE_size_le {Γ : List (Ty pqAtomicSig)} :
    (emptyRoBothAvlE (Γ := Γ)).size ≤ 500 := by
  have h : (emptyRoBothAvlE (Γ := Γ)).size = (emptyRoBothAvlE (Γ := [])).size := rfl
  rw [h]; decide

private theorem ofBudget_size_bits (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    let B := bits (stepCostBudget S b)
    bits F.K_on ≤ B ∧ bits F.K_ro ≤ B ∧
      bits (min b.q_total S.N_sess_tot) ≤ B ∧
      bits (min b.q_total S.N_recv_tot + 1) ≤ B ∧
      bits (min F.K_on S.N_dh) ≤ B ∧
      bits (4 * min F.K_on S.N_dh) ≤ B + 3 ∧
      bits (avlHeightCap F.K_cap) ≤ B := by
  dsimp only
  have hq : bits b.q_total ≤ bits (stepCostBudget S b) :=
    bits_le_bits_stepCostBudget S b (by omega)
  have hkon : bits (AuthKindFuels.ofBudget S b).K_on ≤ bits (stepCostBudget S b) :=
    (_root_.ReductionDsl.bits_mono (AuthCoreK.AuthKindFuels.K_on_le_q_total S b)).trans hq
  have hkro : bits (AuthKindFuels.ofBudget S b).K_ro ≤ bits (stepCostBudget S b) :=
    (_root_.ReductionDsl.bits_mono (AuthCoreK.AuthKindFuels.K_ro_le_q_total S b)).trans hq
  have hsess : bits (min b.q_total S.N_sess_tot) ≤ bits (stepCostBudget S b) :=
    (_root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)).trans hq
  have hrecv : bits (min b.q_total S.N_recv_tot + 1) ≤ bits (stepCostBudget S b) := by
    have hm : min b.q_total S.N_recv_tot ≤ b.q_total := Nat.min_le_left _ _
    exact bits_le_bits_stepCostBudget S b (by omega)
  have hmdh : bits (min (AuthKindFuels.ofBudget S b).K_on S.N_dh) ≤ bits (stepCostBudget S b) :=
    (_root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)).trans hkon
  have h4mdh : bits (4 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh) ≤
      bits (stepCostBudget S b) + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 (min (AuthKindFuels.ofBudget S b).K_on S.N_dh)
    have hb4 : bits 4 = 3 := by decide
    omega
  have havl : bits (avlHeightCap (AuthKindFuels.ofBudget S b).K_cap) ≤
      bits (stepCostBudget S b) := by
    have h1 : 65536 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right (2 ^ 16 * (b.q_total + 1)) (Nat.succ_pos b.q_total)
    have h2 : 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) ≤ stepCostBudget S b := by
      unfold stepCostBudget; dsimp only
      exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
    have hbk := ofBudget_bits_K_cap_le S b
    apply _root_.ReductionDsl.bits_mono
    unfold avlHeightCap; omega
  exact ⟨hkon, hkro, hsess, hrecv, hmdh, h4mdh, havl⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem finalizeAuthFixedDsl_size_le (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).size ≤
      4 * bits (min K S.N_dh) + 5 * bits (4 * min K S.N_dh) + 7 * bits K + 300 := by
  simp only [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDsl,
    allHonestEcPksAuthDslK, hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    asHasWonAuth, asSessions, asSpkBundles, asPrincipals, asOpkEntries,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    aseFresh, aseSpkHonest, asePqspkHonest, aseChallenged, aseEkASk,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    boolOr, boolBeq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV,
    eLet, eAny, eMap, bytesBeq, samplePrim, queryPrim, Comp.size, Expr.size]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem finalizeAuthFixedDsl_litSize_eq (S : Setup) (K : Nat) {Γ : List PT} :
    compLitSize (finalizeAuthFixedDsl S K (Γ := Γ)) = 0 := by
  simp only [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDsl,
    allHonestEcPksAuthDslK, hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    asHasWonAuth, asSessions, asSpkBundles, asPrincipals, asOpkEntries,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    aseFresh, aseSpkHonest, asePqspkHonest, aseChallenged, aseEkASk,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    boolOr, boolBeq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV,
    eLet, eAny, eMap, bytesBeq, Expr.bytesBeq, samplePrim, queryPrim,
    compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]

private theorem liftAuthPrim1_size_le {a r : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {S0 L0 : ℕ}
    (hs : c.size ≤ S0) (hl : compLitSize c ≤ L0) :
    (liftAuthPrim1 c e).size ≤ 10 * S0 + L0 + e.size + 2 := by
  have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe c
  unfold liftAuthPrim1
  simp only [Comp.size, compRename_size]
  omega

private theorem ckBaseArmC_size_le (S : Setup) (F : AuthKindFuels) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy → _root_.ReductionDsl.Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ RSF)
    (hs : (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)).size ≤
      600 + 2 * bits F.K_on)
    (hl : compLitSize (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)) ≤ 20) :
    (ckBaseArmC S step (Γ := [(authCodec S).Q])).size ≤ 6200 + 20 * bits F.K_on := by
  unfold ckBaseArmC
  simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (liftAuthPrim1_size_le _ _ (S0 := 610 + 2 * bits F.K_on) (L0 := 20)
      (by simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
            Comp.size, Expr.size]; omega)
      (by simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
            compLitSize, exprLitSize]; omega)) _) 1) ?_
  simp only [ckRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem ckOnlineArm_size_le (S : Setup) (F : AuthKindFuels) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ],
      _root_.ReductionDsl.Var Γ₁ .nat →
      _root_.ReductionDsl.Var Γ₂ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)) →
      _root_.ReductionDsl.Var Γ₃ authHybridStateFixedTy → _root_.ReductionDsl.Var Γ₄ arg →
      Comp pqxdhOps pqPrimIface Δ RSF)
    (hs : (step
      (Δ := [authHybridStateFixedTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        .nat, arg, prfCkStTy, .prod prfCkStTy arg])
      (.zero : _root_.ReductionDsl.Var [.nat, arg, prfCkStTy, .prod prfCkStTy arg] _)
      (.zero : _root_.ReductionDsl.Var [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        .nat, arg, prfCkStTy, .prod prfCkStTy arg] _)
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy,
        .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        .nat, arg, prfCkStTy, .prod prfCkStTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, prfCkStTy, .prod prfCkStTy arg] _)).size ≤
      20000 + 64 * bits F.K_on + 10 * bits F.K_ro)
    (hl : compLitSize (step
      (Δ := [authHybridStateFixedTy, .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        .nat, arg, prfCkStTy, .prod prfCkStTy arg])
      (.zero : _root_.ReductionDsl.Var [.nat, arg, prfCkStTy, .prod prfCkStTy arg] _)
      (.zero : _root_.ReductionDsl.Var [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        .nat, arg, prfCkStTy, .prod prfCkStTy arg] _)
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy,
        .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32),
        .nat, arg, prfCkStTy, .prod prfCkStTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, prfCkStTy, .prod prfCkStTy arg] _)) ≤ 4000) :
    (.bind (.bind (liftAuthPrim1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (.snd (v s))) fun idx =>
         letV (.fst (.snd (.snd (v s)))) fun chalP =>
         letV (.snd (.snd (.snd (v s)))) fun fhst =>
         step idx chalP fhst x)
        (.pair (.fst .v1) .v0))
      (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))) :
      Comp pqAtomicOps pqAuthPrimIface
        [embedTy arg, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy))).size ≤
      208500 + 640 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := by
  simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add
      (liftAuthPrim1_size_le _ _ (S0 := 20030 + 64 * bits F.K_on + 10 * bits F.K_ro) (L0 := 4000)
        (by simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
              v, Comp.size, Expr.size]; omega)
        (by simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
              v, compLitSize, exprLitSize]; omega))
      (AuthCoreKCostBase.syncFixedShadowRespC_size_le (I := pqAuthPrimIface) F.K_cap _ _)) 1) _) 1) ?_
  simp only [ckRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem dispatchAuthQ_size_of_bounds {ι : Type} {T : _root_.OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {r : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ AuthCoreK.authQueryAtomicTy)
    (a1 a2 : Comp pqAtomicOps I (Ty.nat :: Γ) r)
    (a3 : Comp pqAtomicOps I (Ty.nat.prod Ty.nat :: Γ) r)
    (a4 : Comp pqAtomicOps I (Ty.nat.prod (Ty.nat.prod Ty.nat) :: Γ) r)
    (a5 a6 : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) r)
    (a7 a8 : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) r)
    (a9 : Comp pqAtomicOps I (PB 192 :: Γ) r)
    (a10 : Comp pqAtomicOps I ((PB 32).prod (PB 32) :: Γ) r)
    (a11 : Comp pqAtomicOps I (Ty.unit :: Γ) r)
    (a12 : Comp pqAtomicOps I (PB 32 :: Γ) r)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 B : ℕ}
    (h0 : qE.size ≤ b0) (h1 : a1.size ≤ b1) (h2 : a2.size ≤ b2) (h3 : a3.size ≤ b3)
    (h4 : a4.size ≤ b4) (h5 : a5.size ≤ b5) (h6 : a6.size ≤ b6) (h7 : a7.size ≤ b7)
    (h8 : a8.size ≤ b8) (h9 : a9.size ≤ b9) (h10 : a10.size ≤ b10) (h11 : a11.size ≤ b11)
    (h12 : a12.size ≤ b12)
    (hB : b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + 21 ≤ B) :
    (AuthCoreK.dispatchAuthQ qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12).size ≤ B := by
  have hd := AuthCoreKCostBase.dispatchAuthQ_size_le qE a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  omega

private theorem F_X25519_len_eq : _root_.SignalPqxdh.F_X25519.length = 32 := by decide

set_option linter.unusedSimpArgs false in
local macro "fixed_kb_sz" : tactic => `(tactic| (
  simp (config := { maxSteps := 500000 }) only [
    AuthCoreK.initPrin1KeyFixedKB, AuthCoreK.corruptFixedKB, AuthCoreK.genSpkFixedKB,
    AuthCoreK.genOpkFixedKB, AuthCoreK.registerFixedKB,
    initPrin1KeyFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, registerFixedB,
    findHonestC, fhstSetBase, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, sbMk, oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd, buMk,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, stUpd, ahsUpd, ahsfUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, boolOr, boolBeq, natEq, nat2Eq, nat3Eq, isSomeE, optFst, optSnd,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV, anyMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM, Comp.size, Expr.size, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, F_X25519_len_eq,
    Nat.add_zero, Nat.zero_add, ↓reduceIte]
  try dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  omega))

section FixedKBSize
variable {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]

private theorem initPrin1KeyFixedKB_size_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy) (u : _root_.ReductionDsl.Var Γ₂ .nat) :
    (AuthCoreK.initPrin1KeyFixedKB F (Δ := Δ) fhst u).size ≤ 600 + 2 * bits F.K_on := by fixed_kb_sz
private theorem initPrin1KeyFixedKB_litSize_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy) (u : _root_.ReductionDsl.Var Γ₂ .nat) :
    compLitSize (AuthCoreK.initPrin1KeyFixedKB F (Δ := Δ) fhst u) ≤ 20 := by fixed_kb_sz
private theorem corruptFixedKB_size_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy) (u : _root_.ReductionDsl.Var Γ₂ .nat) :
    (AuthCoreK.corruptFixedKB F (Δ := Δ) fhst u).size ≤ 600 + 2 * bits F.K_on := by fixed_kb_sz
private theorem corruptFixedKB_litSize_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy) (u : _root_.ReductionDsl.Var Γ₂ .nat) :
    compLitSize (AuthCoreK.corruptFixedKB F (Δ := Δ) fhst u) ≤ 20 := by fixed_kb_sz
private theorem genSpkFixedKB_size_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy) (x : _root_.ReductionDsl.Var Γ₂ (.prod .nat .nat)) :
    (AuthCoreK.genSpkFixedKB F (Δ := Δ) fhst x).size ≤ 600 + 2 * bits F.K_on := by fixed_kb_sz
private theorem genSpkFixedKB_litSize_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy) (x : _root_.ReductionDsl.Var Γ₂ (.prod .nat .nat)) :
    compLitSize (AuthCoreK.genSpkFixedKB F (Δ := Δ) fhst x) ≤ 20 := by fixed_kb_sz
private theorem genOpkFixedKB_size_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy)
    (x : _root_.ReductionDsl.Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    (AuthCoreK.genOpkFixedKB F (Δ := Δ) fhst x).size ≤ 600 + 2 * bits F.K_on := by fixed_kb_sz
private theorem genOpkFixedKB_litSize_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy)
    (x : _root_.ReductionDsl.Var Γ₂ (.prod .nat (.prod .nat .nat))) :
    compLitSize (AuthCoreK.genOpkFixedKB F (Δ := Δ) fhst x) ≤ 20 := by fixed_kb_sz
private theorem registerFixedKB_size_le (F : AuthKindFuels)
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy)
    (sk : _root_.ReductionDsl.Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32)) :
    (AuthCoreK.registerFixedKB (Δ := Δ) fhst sk).size ≤ 600 + 2 * bits F.K_on := by fixed_kb_sz
private theorem registerFixedKB_litSize_le
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy)
    (sk : _root_.ReductionDsl.Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32)) :
    compLitSize (AuthCoreK.registerFixedKB (Δ := Δ) fhst sk) ≤ 20 := by fixed_kb_sz
end FixedKBSize

end SharedSizeHelpers

theorem prfCk1KeyKindProg_size_le (S : Setup) (b : QueryBudget) :
    (prfCk1KeyKindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  rcases ofBudget_size_bits S b with ⟨hkon, hkro, hsess, _hrecv, hmdh, h4mdh, havl⟩
  let F := AuthKindFuels.ofBudget S b
  have hInit : (prfCkKindInitC S b).size ≤ 2600 + 20 * bits (min b.q_total S.N_sess_tot) := by
    have hs : (prfCkInitDslK S b.q_total).size ≤ 200 + 2 * bits (min b.q_total S.N_sess_tot) := by
      simp only [prfCkInitDslK, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
        ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, samplePrim, v,
        Comp.size, Expr.size]
      have : bits 0 = 1 := by decide
      omega
    have hl : _root_.Computational.Proofs.SignalPqxdh.AtomicLift.compLitSize
        (prfCkInitDslK S b.q_total) = 0 := by
      simp only [prfCkInitDslK, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
        ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, samplePrim, v,
        _root_.Computational.Proofs.SignalPqxdh.AtomicLift.compLitSize,
        _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprLitSize, Nat.add_zero]
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (prfCkInitDslK S b.q_total)
    have he := emptyRoBothAvlE_size_le
      (Γ := [embedTy (.prod .unit prfCkStTy), .prod (PB 32) (PB 32)])
    unfold prfCkKindInitC
    simp only [Comp.size, Expr.size, Expr.v0]; omega
  have hFin : (prfCkKindFinishC S F).size ≤
      3400 + 40 * bits (min F.K_on S.N_dh) + 50 * bits (4 * min F.K_on S.N_dh) +
        70 * bits F.K_on := by
    have hs : (prfCkFinishDsl S F.K_on).size ≤
        330 + 4 * bits (min F.K_on S.N_dh) + 5 * bits (4 * min F.K_on S.N_dh) +
          7 * bits F.K_on := by
      have hf := finalizeAuthFixedDsl_size_le S F.K_on
        (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkStTy, .bool])
      simp only [prfCkFinishDsl, letV,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckSecb,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckFhst,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid,
        Comp.size, Expr.size]
      omega
    have hl : _root_.Computational.Proofs.SignalPqxdh.AtomicLift.compLitSize
        (prfCkFinishDsl S F.K_on) = 0 := by
      simp only [prfCkFinishDsl, letV,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckSecb,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ckFhst,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid,
        finalizeAuthFixedDsl_litSize_eq,
        _root_.Computational.Proofs.SignalPqxdh.AtomicLift.compLitSize,
        _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprLitSize, Nat.add_zero]
    have hm := mapComp_size_le tlAuthPrim tlAuthPrim_sizeLe (prfCkFinishDsl S F.K_on)
    unfold prfCkKindFinishC
    simp only [Comp.size, Expr.size, Expr.v0, compRename_size]; omega
  have hHandle : (prfCkKindHandleC S F).size ≤
      880000 + 2660 * bits F.K_on + 400 * bits F.K_ro +
        20 * bits (_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlHeightCap F.K_cap) := by
    unfold prfCkKindHandleC
    dsimp only
    exact dispatchAuthQ_size_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ (b0 := 1) (by rfl)
      (ckBaseArmC_size_le S F (fun fhst u => AuthCoreK.initPrin1KeyFixedKB F fhst u)
        (initPrin1KeyFixedKB_size_le F _ _) (initPrin1KeyFixedKB_litSize_le F _ _))
      (ckBaseArmC_size_le S F (fun fhst u => AuthCoreK.corruptFixedKB F fhst u)
        (corruptFixedKB_size_le F _ _) (corruptFixedKB_litSize_le F _ _))
      (ckBaseArmC_size_le S F (fun fhst x => AuthCoreK.genSpkFixedKB F fhst x)
        (genSpkFixedKB_size_le F _ _) (genSpkFixedKB_litSize_le F _ _))
      (ckBaseArmC_size_le S F (fun fhst x => AuthCoreK.genOpkFixedKB F fhst x)
        (genOpkFixedKB_size_le F _ _) (genOpkFixedKB_litSize_le F _ _))
      (ckOnlineArm_size_le S F
        (fun idx chalP fhst x => authCkSendKB S F.K_on F.K_ro true idx chalP fhst x)
        (le_trans (authCkSendKB_size_le S F.K_on F.K_ro true _ _ _ _) (by omega))
        (authCkSendKB_litSize_le S F.K_on F.K_ro true _ _ _ _))
      (ckOnlineArm_size_le S F
        (fun idx chalP fhst x => authCkSendKB S F.K_on F.K_ro false idx chalP fhst x)
        (le_trans (authCkSendKB_size_le S F.K_on F.K_ro false _ _ _ _) (by omega))
        (authCkSendKB_litSize_le S F.K_on F.K_ro false _ _ _ _))
      (ckOnlineArm_size_le S F
        (fun idx chalP fhst x => authCkRecvKB S F.K_on F.K_ro true idx chalP fhst x)
        (authCkRecvKB_size_le S F.K_on F.K_ro true _ _ _ _)
        (authCkRecvKB_litSize_le S F.K_on F.K_ro true _ _ _ _))
      (ckOnlineArm_size_le S F
        (fun idx chalP fhst x => authCkRecvKB S F.K_on F.K_ro false idx chalP fhst x)
        (authCkRecvKB_size_le S F.K_on F.K_ro false _ _ _ _)
        (authCkRecvKB_litSize_le S F.K_on F.K_ro false _ _ _ _))
      (b9 := 2400 + 2 * bits (_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlHeightCap F.K_cap))
      (by have h := AuthCoreKCostBase.roFixedShadowArmC_size_le aiAuthPrim F.K_cap
            (Γ := [PB 192, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q])
            (.pair (.snd (.snd (.snd (.fst .v1)))) (.snd .v1)) .v0
          simp only [Comp.size, ckRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h ⊢; omega)
      (b10 := 2450 + 2 * bits (_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs.avlHeightCap F.K_cap))
      (by have h := AuthCoreKCostBase.roRootFixedShadowArmC_size_le aiAuthPrim F.K_cap
            (Γ := [.prod (PB 32) (PB 32), .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q])
            (.pair (.snd (.snd (.snd (.fst .v1)))) (.snd .v1)) .v0
          simp only [Comp.size, ckRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h ⊢; omega)
      (b11 := 25)
      (by simp only [Comp.size, aNoneAtomicE, Expr.size, Expr.v1]; decide)
      (ckBaseArmC_size_le S F (fun fhst sk => AuthCoreK.registerFixedKB fhst sk)
        (registerFixedKB_size_le F _ _) (registerFixedKB_litSize_le _ _))
      (by omega)
  have hB : reductionSizeBudget = 2 ^ 24 := rfl
  rw [hB]
  change (prfCkKindInitC S b).size + (prfCkKindHandleC S F).size + (prfCkKindFinishC S F).size ≤
    2 ^ 24 + 2 ^ 12 * bits (stepCostBudget S b)
  dsimp only [F] at hFin hHandle ⊢
  omega

theorem prfMkKindInitC_cost_le (S : Setup) (b : QueryBudget) :
    (prfMkKindInitC S b).cost ≤ 1000 + 4 * Nat.log 2 S.N_sess_tot := by
  have hc : (prfMsgKeysInitDslK S b.q_total).cost =
      72 + bits (min b.q_total S.N_sess_tot) + bits (min b.q_total S.N_recv_tot + 1) := by
    simp only [prfMsgKeysInitDslK, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
      emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, cost_sampleChal,
      _root_.SignalPqxdh.LegacyCosted.PSamp.cost, _root_.SignalPqxdh.LegacyCosted.Ty.wd,
      v, Comp.cost, Expr.cost, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bits_0]
    omega
  have hr64 : (prfMsgKeysInitDslK S b.q_total).queries
      (fun _ => 0) (sampR64W tlPrfMk.hsmp) = 0 := by
    simp [prfMsgKeysInitDslK, bindV, sampleChal, sampR64W_mk_bool, sampR64W_mk_index, Comp.queries]
  have hlog1 : bits (min b.q_total S.N_sess_tot) ≤ Nat.log 2 S.N_sess_tot + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_right b.q_total S.N_sess_tot)) 1
  have hrecv : min b.q_total S.N_recv_tot ≤ S.N_sess_tot := by
    unfold Setup.N_sess_tot; omega
  have hlog2 : bits (min b.q_total S.N_recv_tot + 1) ≤ Nat.log 2 S.N_sess_tot + 2 :=
    bits_succ_le_log_add_two hrecv
  have hm := mapComp_cost_two_mul_le tlPrfMk (prfMsgKeysInitDslK S b.q_total)
  have hhm : (mapComp tlPrfMk (prfMsgKeysInitDslK S b.q_total)).cost ≤
      120 + 4 * Nat.log 2 S.N_sess_tot := by omega
  have he := emptyRoBothAvlE_cost_le (Γ := [embedTy (.prod .unit prfMkStTy), .unit])
  unfold prfMkKindInitC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hhm _) 1) (by omega)

theorem prfMkKindHandleC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy prfMkStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 1) :
    (prfMkKindHandleC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  unfold prfMkKindHandleC
  dsimp only
  refine le_trans (AuthCoreKCostBase.dispatchAuthQ_v1_costAt_kind1_le
    _ _ _ _ _ _ _ _ _ _ _ _ s q .nil (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [mkRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roRootFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [mkRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega

section MkCostHelpers

open _root_.SignalPqxdh.LegacyCosted (PSamp)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT RSF prfMkCoreTy prfMkStepPreTy prfMkChalContTy msgKeysTy authRespTy
   authHybridStateFixedTy sendQTy recvQTy sessionIdTy principalEntryTy preKeyBundleTy
   keys6Ty drKeyTy preKeyMsgTy preparedAuthRecvTy authMkSaltCacheTy
   prfMkStepPostC finishAuthSendMkC finishAuthRecvMkC finishAuthHybridSendC recvFinishTagRunC
   checkBundleProvenanceExactC checkBundleSpkHonIdealC findHonestC matchSentOPKC matchSentNoOPKC
   firstMsgADE_cost finishAuthHybridSendC_cost recvFinishTagRunC_cost
   caseOptV caseSumV findMV anyMV consumeFirstMV eCaseOpt
   natEq aNone queryDeriveMk cost_liftPrimComp cost_queryDeriveMk cost_queryPrim cost_litB
   ahsfHybrid ahsBase peIkAPk pkbIkB asRoCache asRootRoCache ahsfUpd ahsfUpdSlots
   ahsfRecvCount ahsfMkSaltCache ahsfSlots parHstDec parFinishTag parKEntry
   hdrIkAPk pkmHdr pkmEphAPk pkmPqRatchetMsg pkmAeadCt bits_0 bits_1)

private theorem liftExpr1_cost_le {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a] b)
    (argE : Expr pqAtomicOps Γ (embedTy a)) {C : ℕ}
    (h : (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.mapExpr e).cost + 1 ≤ C) :
    (_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.liftExpr1 e argE).cost ≤
      argE.cost + C := by
  simp only [_root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.liftExpr1,
    Expr.cost, _root_.Computational.Proofs.SignalPqxdh.AtomicLift.exprRename_cost]; omega

private theorem fixedRoCacheE_cost_le {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ
      _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authFixedAtomicTy) :
    (fixedRoCacheE e).cost ≤ e.cost + 22 := by
  rw [fixedRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem fixedRootRoCacheE_cost_le {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ
      _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authFixedAtomicTy) :
    (fixedRootRoCacheE e).cost ≤ e.cost + 22 := by
  rw [fixedRootRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem syncRoBoth_fixed_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ
      _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authFixedAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := pqPrfMkIface) cap
      (fixedRoCacheE fhstE) (fixedRootRoCacheE fhstE) roBothE).cost ≤
      8500 * bits cap + 1894 + 2 * fhstE.cost + roBothE.cost := by
  have h := AuthCoreKCostBase.syncRoBothC_cost_le (I := pqPrfMkIface) cap
    (fixedRoCacheE fhstE) (fixedRootRoCacheE fhstE) roBothE
  have h1 := fixedRoCacheE_cost_le fhstE
  have h2 := fixedRootRoCacheE_cost_le fhstE
  omega

private theorem bind2_ret_cost_le {ι : Type} {T : _root_.OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {a b c : Ty pqAtomicSig}
    (m1 : Comp pqAtomicOps I Γ a) (m2 : Comp pqAtomicOps I (a :: Γ) b)
    (r : Expr pqAtomicOps (b :: a :: Γ) c) {B1 B2 : ℕ}
    (h1 : m1.cost ≤ B1) (h2 : m2.cost ≤ B2) :
    (Comp.bind m1 (.bind m2 (.ret r))).cost ≤ B1 + B2 + r.cost + 3 := by
  simp only [Comp.cost]; omega

private theorem liftPrfMk1_cost_le
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {B R M : ℕ}
    (hc : c.cost ≤ B) (hr : c.queries (fun _ => 0) (sampR64W tlPrfMk.hsmp) ≤ R)
    (hM : 3 * B + 78 * R ≤ 2 * M) :
    (liftPrfMk1 c e).cost ≤ M + e.cost + 2 := by
  have hm := mapComp_cost_two_mul_le tlPrfMk c
  have hhm : (mapComp tlPrfMk c).cost ≤ M := by omega
  unfold liftPrfMk1
  simp only [Comp.cost]
  erw [compRename_cost]
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left hhm _) 1) (by omega)

private theorem mkBaseArmC_cost_le (S : Setup) (F : AuthKindFuels)
    {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy →
      _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
        _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ RSF)
    {Γ : List (Ty pqAtomicSig)}
    (hc : (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)).cost ≤
      9500 + F.K_on * 50)
    (hr : (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)).queries
      (fun _ => 0) (sampR64W rfl) ≤ 3) :
    (mkBaseArmC S step (Γ := Γ)).cost ≤ 14500 + 75 * F.K_on := by
  unfold mkBaseArmC
  simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (liftPrfMk1_cost_le _ _ (B := 9508 + F.K_on * 50) (R := 3) (M := 14390 + 75 * F.K_on)
      (by rw [cost_liftPrimComp]; simp only [letV, cost_letC, Expr.cost]; omega)
      (by rw [queries_liftPrimComp_r64]; simp only [letV, queries_letC]; exact hr)
      (by omega)) _) 1) ?_
  simp only [mkRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem finishAuthSendMkC_cost_tight_aux (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (fhst : _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy)
    (sid : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ sessionIdTy)
    (uE : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ principalEntryTy)
    (pp : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ (.opt (.prod .nat principalEntryTy)))
    (isFresh : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ .bool)
    (bu : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ preKeyBundleTy)
    (m01 : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)))
    (keys6 : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ keys6Ty)
    (drKey : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ drKeyTy)
    (rk1 mkSeed ck1_1 : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (spqrSalt? : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)))
    (pqMsg msgPlain : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (mks : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ msgKeysTy) [Ext Γ₁ Δ] :
    (finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
      spqrSalt? pqMsg msgPlain mks).cost =
      sid.cost + uE.cost + pp.cost + isFresh.cost + bu.cost + m01.cost + keys6.cost +
      drKey.cost + rk1.cost + mkSeed.cost + ck1_1.cost + spqrSalt?.cost + pqMsg.cost +
      msgPlain.cost + mks.cost + 2354 + min K S.N_dh * 920 + K * 3239 := by
  simp only [finishAuthSendMkC, bindV, letV, firstMsgADE_cost, finishAuthHybridSendC_cost,
    ahsfHybrid, ahsBase, peIkAPk, pkbIkB, asRoCache, asRootRoCache, ahsfUpd, ahsfMkSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    cost_letC, cost_queryPrim, cost_litB, v, Comp.cost, Expr.cost,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, List.length_nil]
  omega

private theorem finishAuthRecvMkC_cost_tight_aux (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : _root_.ReductionDsl.Var Γ₁ preKeyMsgTy)
    (prep : _root_.ReductionDsl.Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ drKeyTy)
    (rk1 ck1_1 : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (rc' : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ .nat)
    (cache' : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ authMkSaltCacheTy)
    (mks : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).cost =
      drKey.cost + rk1.cost + ck1_1.cost + rc'.cost + cache'.cost + mks.cost +
      1679 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvMkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    recvFinishTagRunC_cost, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

private theorem prfMkStepPostC_cost_le_aux (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : _root_.ReductionDsl.Var Γ₁ prfMkChalContTy)
    (mk : _root_.ReductionDsl.Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K (Δ := Δ) cont mk).cost ≤
      3500 + K * 4000 + min K S.N_dh * 9000 := by
  simp only [prfMkStepPostC, finishAuthSendMkC_cost_tight_aux, finishAuthRecvMkC_cost_tight_aux,
    bindV, letV, caseSumV, eCaseOpt, mkcMk, ahsfUpdSlots, ahsfMkSlots,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, cost_letC, cost_litB,
    v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem prfMkStepPostC_r64_eq (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : _root_.ReductionDsl.Var Γ₁ prfMkChalContTy)
    (mk : _root_.ReductionDsl.Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K (Δ := Δ) cont mk).queries
      (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := by
  simp only [prfMkStepPostC, finishAuthSendMkC, finishAuthRecvMkC,
    finishAuthHybridSendC, recvFinishTagRunC,
    checkBundleProvenanceExactC, checkBundleSpkHonIdealC, findHonestC,
    matchSentOPKC, matchSentNoOPKC,
    bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, Comp.iteC, Comp.caseOptC, Comp.caseSumC,
    Comp.findBoundedM, Comp.anyBoundedM,
    queryPrim, samplePrim, sampR64W_bool, sampR64W_index, r64W,
    Comp.queries, Nat.max_self, Nat.add_zero, Nat.mul_zero]

private theorem mkPostRunC_cost_le (S : Setup) (K_on : ℕ) {Δ : List PT}
    (bud : _root_.ReductionDsl.Var Δ .nat)
    (core : _root_.ReductionDsl.Var Δ prfMkCoreTy)
    (pre : _root_.ReductionDsl.Var Δ prfMkStepPreTy) :
    (mkPostRunC S K_on bud core pre).cost ≤
      3680 + 4000 * K_on + 9000 * min K_on S.N_dh := by
  unfold mkPostRunC
  have hPost := prfMkStepPostC_cost_le_aux S K_on
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ)
    (.zero : _root_.ReductionDsl.Var (prfMkChalContTy ::
      .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ) prfMkChalContTy)
    (.zero : _root_.ReductionDsl.Var (msgKeysTy :: prfMkChalContTy ::
      .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ) msgKeysTy)
  simp only [bindV, letV, caseSumV, natEq, aNone,
    cost_liftPrimComp, cost_letC, cost_queryDeriveMk,
    v, Comp.cost, Expr.cost, bits_0, bits_1]
  omega

private theorem mkPostRunC_r64_eq (S : Setup) (K_on : ℕ) {Δ : List PT}
    (bud : _root_.ReductionDsl.Var Δ .nat)
    (core : _root_.ReductionDsl.Var Δ prfMkCoreTy)
    (pre : _root_.ReductionDsl.Var Δ prfMkStepPreTy) :
    (mkPostRunC S K_on bud core pre).queries (fun _ => 0) (sampR64W tlPrfMk.hsmp) = 0 := by
  unfold mkPostRunC
  dsimp only [caseSumV, bindV, letV]
  simp only [Comp.queries, queries_letC, queryDeriveMk, queries_liftPrimComp_r64,
    prfMkStepPostC_r64_eq, Nat.add_zero, Nat.max_self]

private theorem mkOnlineArm_cost_le (S : Setup) (F : AuthKindFuels) {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (preStep : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ prfMkCoreTy → _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
        _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ prfMkStepPreTy)
    (hc : (preStep
      (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
      (.zero : _root_.ReductionDsl.Var [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg] prfMkCoreTy)
      (.zero : _root_.ReductionDsl.Var [arg, prfMkStTy, .prod prfMkStTy arg] arg)).cost ≤
      15000 + 9469 * F.K_on + 16000 * min F.K_on S.N_dh + 531 * F.K_ro)
    (hr : (preStep
      (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
      (.zero : _root_.ReductionDsl.Var [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg] prfMkCoreTy)
      (.zero : _root_.ReductionDsl.Var [arg, prfMkStTy, .prod prfMkStTy arg] arg)).queries
      (fun _ => 0) (sampR64W tlAuthPrim.hsmp) ≤ 2) :
    (.bind (liftPrfMk1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun _bud =>
         letV (.snd (v s)) fun core =>
         bindV (liftPrimComp (preStep core x)) fun _pre =>
         mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)
        (.pair (.fst .v1) .v0))
      (.bind (syncRoBothC F.K_cap
          (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
          (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
          (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
      Comp pqAtomicOps pqPrfMkIface
        [embedTy arg, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy))).cost ≤
      28200 + 20300 * F.K_on + 37500 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2058) := by
  refine le_trans (bind2_ret_cost_le _ _ _
    (liftPrfMk1_cost_le _ _
      (B := 18710 + 13469 * F.K_on + 25000 * min F.K_on S.N_dh + 531 * F.K_ro)
      (R := 2)
      (M := 28144 + 20204 * F.K_on + 37500 * min F.K_on S.N_dh + 797 * F.K_ro)
      ?_ ?_ (by omega))
    (syncRoBoth_fixed_cost_le F.K_cap _ _)) ?_
  · dsimp only [letV, bindV]
    have hInner : (Comp.bind (liftPrimComp (preStep
        (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
        (.zero : _root_.ReductionDsl.Var [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg] prfMkCoreTy)
        (.zero : _root_.ReductionDsl.Var [arg, prfMkStTy, .prod prfMkStTy arg] arg)))
        (mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)).cost ≤
        (15000 + 9469 * F.K_on + 16000 * min F.K_on S.N_dh + 531 * F.K_ro) +
          (3680 + 4000 * F.K_on + 9000 * min F.K_on S.N_dh) + 1 := by
      simp only [Comp.cost, cost_liftPrimComp]
      exact Nat.add_le_add_right (Nat.add_le_add hc (mkPostRunC_cost_le S F.K_on _ _ _)) 1
    refine le_trans (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _
      (letC_cost_step _ _ hInner)))) ?_
    simp only [v, Expr.cost]; omega
  · simp only [letV, bindV, queries_letC, Comp.queries, queries_liftPrimComp_r64,
      mkPostRunC_r64_eq, Nat.add_zero]
    exact hr
  · simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem prfMkKindHandleC_cost_le_aux (S : Setup) (F : AuthKindFuels) :
    (prfMkKindHandleC S F).cost ≤
      28200 + 20300 * F.K_on + 37500 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) := by
  unfold prfMkKindHandleC
  dsimp only
  refine le_trans (AuthCoreKCostBase.dispatchAuthQ_cost_le
    _ _ _ _ _ _ _ _ _ _ _ _ _
    (B := 28200 + 20300 * F.K_on + 37500 * min F.K_on S.N_dh + 797 * F.K_ro +
      (8500 * bits F.K_cap + 2058))
    ?_ ?_ ?_ ?_
    (mkOnlineArm_cost_le S F (fun core x => authMkSendPreKB S F.K_on F.K_ro true core x)
      (authMkSendPreKB_cost_le S F.K_on F.K_ro true _ _)
      (authMkSendPreKB_r64_le S F.K_on F.K_ro true _ _))
    (mkOnlineArm_cost_le S F (fun core x => authMkSendPreKB S F.K_on F.K_ro false core x)
      (authMkSendPreKB_cost_le S F.K_on F.K_ro false _ _)
      (authMkSendPreKB_r64_le S F.K_on F.K_ro false _ _))
    (mkOnlineArm_cost_le S F (fun core x => authMkRecvPreKB S F.K_on F.K_ro true core x)
      (authMkRecvPreKB_cost_le S F.K_on F.K_ro true _ _)
      (authMkRecvPreKB_r64_le S F.K_on F.K_ro true _ _))
    (mkOnlineArm_cost_le S F (fun core x => authMkRecvPreKB S F.K_on F.K_ro false core x)
      (authMkRecvPreKB_cost_le S F.K_on F.K_ro false _ _)
      (authMkRecvPreKB_r64_le S F.K_on F.K_ro false _ _))
    ?_ ?_ ?_ ?_) ?_
  · exact le_trans (mkBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.initPrin1KeyFixedKB_cost_le F _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.initPrin1KeyFixedKB_r64_le]; omega)) (by omega)
  · exact le_trans (mkBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.corruptFixedKB_cost_le F _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.corruptFixedKB_r64_le]; omega)) (by omega)
  · exact le_trans (mkBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.genSpkFixedKB_cost_le F _ _) (by omega))
      (le_trans (AuthCoreKCostBaseClampedFixed.genSpkFixedKB_r64_le F _ _) (by decide))) (by omega)
  · exact le_trans (mkBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.genOpkFixedKB_cost_le F _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.genOpkFixedKB_r64_le]; omega)) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [mkRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roRootFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [mkRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost, aNoneAtomicE, Expr.cost, Expr.v1]; omega
  · exact le_trans (mkBaseArmC_cost_le S F _
      (le_trans (AuthCoreKCostBaseClampedFixed.registerFixedKB_cost_le _ _) (by omega))
      (by rw [AuthCoreKCostBaseClampedFixed.registerFixedKB_r64_le]; omega)) (by omega)
  · simp only [Expr.cost]; omega

end MkCostHelpers

theorem prfMkKindHandleC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy prfMkStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (_hk : authQueryKind q = 0) :
    (prfMkKindHandleC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      28200 + 20300 * F.K_on + 37500 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  (Comp.costAt_le_cost _ _).trans (prfMkKindHandleC_cost_le_aux S F)

theorem prfMkKindHandleC_cost_le (S : Setup) (F : AuthKindFuels) :
    (prfMkKindHandleC S F).cost ≤
      28200 + 20300 * F.K_on + 37500 * min F.K_on S.N_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) :=
  prfMkKindHandleC_cost_le_aux S F

theorem prfMkKindFinishC_cost_le (S : Setup) (F : AuthKindFuels) :
    (prfMkKindFinishC S F).cost ≤
      200 + 620 * min F.K_on S.N_dh + 1632 * (min F.K_on S.N_dh) ^ 2 +
        150 * F.K_on + 14267 * F.K_on ^ 2 := by
  have hc := prfMsgKeysFinishDsl_cost S F.K_on
  have hr64 : (prfMsgKeysFinishDsl S F.K_on).queries (fun _ => 0) (sampR64W tlPrfMk.hsmp) = 0 := by
    unfold prfMsgKeysFinishDsl
    rw [queries_liftPrimComp_r64]
    simp [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
      allHonestEcPksAuthDslK, letV, queries_letC, samplePrim, queryPrim,
      sampR64W_bool, Comp.queries]
  have hm := mapComp_cost_two_mul_le tlPrfMk (prfMsgKeysFinishDsl S F.K_on)
  have hhm : (mapComp tlPrfMk (prfMsgKeysFinishDsl S F.K_on)).cost ≤
      180 + 620 * min F.K_on S.N_dh + 1632 * (min F.K_on S.N_dh) ^ 2 +
        150 * F.K_on + 14267 * F.K_on ^ 2 := by omega
  unfold prfMkKindFinishC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  erw [compRename_cost]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left hhm _) _) (by omega)

theorem prfMkKindInitC_queries_prim_le (S : Setup) (b : QueryBudget) :
    (prfMkKindInitC S b).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : (prfMsgKeysInitDslK S b.q_total).queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS = 0 := by
    simp [prfMsgKeysInitDslK, bindV, sampleChal,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS, Comp.queries]
  have hm := mapComp_queries_le tlPrfMk
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS
    authChalIfacePrimQueryWeight tlPrfMk_mkPrimW (prfMsgKeysInitDslK S b.q_total)
  apply Nat.eq_zero_of_le_zero
  unfold prfMkKindInitC
  simp only [Comp.queries, Nat.add_zero]
  exact le_trans hm (by omega)

private theorem liftPrfMk1_queries_le
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {Q : ℕ}
    (hq : c.queries _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS ≤ Q) :
    (liftPrfMk1 c e).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  have hm := mapComp_queries_le tlPrfMk
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS
    authChalIfacePrimQueryWeight tlPrfMk_mkPrimW c
  unfold liftPrfMk1
  simp only [Comp.queries, Nat.zero_add]
  erw [compRename_queries]
  exact le_trans hm hq

private theorem mkBaseArmC_queries_le (S : Setup)
    {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy →
      _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
        _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)} {Q : ℕ}
    (hq : (step
      (Δ := [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var
        [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).queries
      (fun _ => 1) (fun _ => 0) ≤ Q) :
    (mkBaseArmC S step (Γ := Γ)).queries
      authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
  unfold mkBaseArmC
  simp only [Comp.queries, Nat.add_zero]
  apply liftPrfMk1_queries_le
  rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queries_liftPrimComp_mkPrim]
  simp only [letV, queries_letC]
  exact hq

private theorem prfMkStepPostC_queries_le_aux (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (cont : _root_.ReductionDsl.Var Γ₁
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkChalContTy)
    (mk : _root_.ReductionDsl.Var Γ₂
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.msgKeysTy)
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkStepPostC S K (Δ := Δ) cont mk).queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS ≤
      1 + S.N_dh * 12 := by
  have hmin : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkStepPostC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthSendMkC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthRecvMkC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finishAuthHybridSendC_queries,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvFinishTagRunC_queries,
    bindV, letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV,
    queries_letC, queryPrim, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW,
    Comp.queries]
  omega

private theorem mkPostRunC_queries_le (S : Setup) (K_on : ℕ)
    {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (bud : _root_.ReductionDsl.Var Δ .nat)
    (core : _root_.ReductionDsl.Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkCoreTy)
    (pre : _root_.ReductionDsl.Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkStepPreTy) :
    (mkPostRunC S K_on bud core pre).queries
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS ≤
      1 + S.N_dh * 12 := by
  unfold mkPostRunC
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV, bindV, letV]
  simp only [Comp.queries, queries_letC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queryDeriveMk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queries_liftPrimComp_mkPrim,
    Nat.zero_add, Nat.add_zero]
  exact Nat.max_le.mpr ⟨Nat.zero_le _,
    Nat.max_le.mpr ⟨Nat.zero_le _, prfMkStepPostC_queries_le_aux S K_on _ _⟩⟩

theorem prfMkKindHandleC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (prfMkKindHandleC S F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 40 * S.N_dh := by
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hSend : ∀ opk : Bool,
      (.bind (liftPrfMk1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun _bud =>
           letV (.snd (v s)) fun core =>
           bindV (liftPrimComp (authMkSendPreKB S F.K_on F.K_ro opk core x)) fun _pre =>
           mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
            (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
        Comp pqAtomicOps pqPrfMkIface
          [authSendQAtomicTy, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy))).queries
        authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 40 + 40 * S.N_dh := by
    intro opk
    simp only [Comp.queries, Nat.add_zero]
    rw [AuthCoreKCostBase.syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (liftPrfMk1_queries_le _ _
      (Q := (20 + 26 * min F.K_on S.N_dh) + (1 + S.N_dh * 12)) ?_) (by omega)
    simp only [letV, bindV, queries_letC, Comp.queries,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queries_liftPrimComp_mkPrim]
    exact Nat.add_le_add (authMkSendPreKB_queries_prim_le S F.K_on F.K_ro opk _ _)
      (mkPostRunC_queries_le S F.K_on _ _ _)
  have hRecv : ∀ opk : Bool,
      (.bind (liftPrfMk1
          (letV (.fst (.var .zero)) fun s =>
           letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun _bud =>
           letV (.snd (v s)) fun core =>
           bindV (liftPrimComp (authMkRecvPreKB S F.K_on F.K_ro opk core x)) fun _pre =>
           mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
            (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
            (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
        Comp pqAtomicOps pqPrfMkIface
          [authRecvQAtomicTy, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy))).queries
        authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 40 + 40 * S.N_dh := by
    intro opk
    simp only [Comp.queries, Nat.add_zero]
    rw [AuthCoreKCostBase.syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (liftPrfMk1_queries_le _ _
      (Q := (20 + 26 * min F.K_on S.N_dh) + (1 + S.N_dh * 12)) ?_) (by omega)
    simp only [letV, bindV, queries_letC, Comp.queries,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queries_liftPrimComp_mkPrim]
    exact Nat.add_le_add (authMkRecvPreKB_queries_prim_le S F.K_on F.K_ro opk _ _)
      (mkPostRunC_queries_le S F.K_on _ _ _)
  unfold prfMkKindHandleC
  dsimp only
  refine AuthCoreKCostBase.dispatchAuthQ_queries_le
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ?_ ?_ ?_ ?_ (hSend true) (hSend false) (hRecv true) (hRecv false) ?_ ?_ ?_ ?_
  · exact le_trans (mkBaseArmC_queries_le S _
      (AuthCoreKCostBaseClampedFixed.initPrin1KeyFixedKB_queries_prim_le F _ _)) (by omega)
  · exact le_trans (mkBaseArmC_queries_le S _
      (by rw [AuthCoreKCostBaseClampedFixed.corruptFixedKB_queries_prim_le])) (by omega)
  · exact le_trans (mkBaseArmC_queries_le S _
      (AuthCoreKCostBaseClampedFixed.genSpkFixedKB_queries_prim_le F _ _)) (by omega)
  · exact le_trans (mkBaseArmC_queries_le S _
      (AuthCoreKCostBaseClampedFixed.genOpkFixedKB_queries_prim_le F _ _)) (by omega)
  · simp only [Comp.queries]
    exact le_trans (Nat.add_le_add_right
      (le_of_eq (AuthCoreKCostBase.roFixedShadowArmC_queries_zero aiPrfMk
        authChalIfacePrimQueryWeight F.K_cap _ _)) 0) (by omega)
  · simp only [Comp.queries]
    exact le_trans (Nat.add_le_add_right
      (le_of_eq (AuthCoreKCostBase.roRootFixedShadowArmC_queries_zero aiPrfMk
        authChalIfacePrimQueryWeight F.K_cap _ _)) 0) (by omega)
  · simp only [Comp.queries]; omega
  · exact le_trans (mkBaseArmC_queries_le S _
      (AuthCoreKCostBaseClampedFixed.registerFixedKB_queries_prim_le _ _)) (by omega)

theorem prfMkKindFinishC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (prfMkKindFinishC S F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 20 * S.N_dh := by
  have hq := prfMsgKeysFinishDsl_queries_prim S F.K_on
  have hm := mapComp_queries_le tlPrfMk
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkPrimW
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.mkWS
    authChalIfacePrimQueryWeight tlPrfMk_mkPrimW (prfMsgKeysFinishDsl S F.K_on)
  have hmin : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  unfold prfMkKindFinishC
  simp only [Comp.queries, Nat.zero_add]
  erw [compRename_queries]
  exact le_trans hm (by omega)

section MkSizeHelpers

open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (compLitSize exprLitSize pqOpLitSize exprRename_size mapExpr_size)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (avlHeightCap)
open _root_.SignalPqxdh (F_X25519)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqBytesOps pqU32Ops)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT RSF prfMkCoreTy prfMkStepPreTy prfMkChalContTy msgKeysTy authRespTy
   authHybridStateTy authHybridStateFixedTy sendQTy recvQTy recvFinishTagTy recvFinishResTy
   finishSendArgsTy preparedAuthRecvTy
   prfMkStepPostC finishAuthSendMkC finishAuthRecvMkC finishRecvUnmatchedMkPreC
   finishAuthHybridSendC recvFinishTagRunC prepareAuthHybridRecvC
   checkBundleProvenanceExactC checkBundleSpkHonIdealC findHonestC isAdvRegC isGameSpkC isGameOpkC
   koskBundleOkC koskSenderOkC resolveSigPkC hkdfRoC rootRoC matchSentOPKC matchSentNoOPKC
   matchIdealAuthHandshakeC
   caseOptV caseSumV findMV anyMV consumeFirstMV
   eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
   litB catB bytesCons widenB takeKB bytesLen bytesBeq bytesVarint u32OfNat u32Beq
   encEC encKEM boolOr boolBeq F_X25519_length
   firstMsgADE buildSecretsE sidEq optU32Eq saltBytesE sameSaltKeyE kyberEq kyberCheckE sendGuardE
   mkcSecb mkcIdx mkcSentChal mkcFhst mkcMk
   parKEntry parSecrets parDhRatchet parIsUncorrSender parMatchedSess? parSameEph parHstDec
   parFinishTag fhstSetBase
   peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted
   sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk oeOpkSk oeOpkPk oeConsumed
   pkbIkB pkbSpkId pkbSpkB pkbSpkSig pkbOpkB? pkbPqspkId pkbPqspkB pkbPqspkSig
   hdrIkAPk hdrEkAPk hdrSpkId hdrOpkId? hdrPqspkId hdrKemCt
   pkmHdr pkmEphAPk pkmPqRatchetMsg pkmAeadCt
   soA0 soB0 soSb soOb soA1 soPk1 soCt soM soMatched soMarkMatched
   snoA0 snoB0 snoSb snoA1 snoPk1 snoCt snoM snoMatched snoMarkMatched
   roBCorr roA0 roB0 roSb roOb roA1 roPk1 roCt roM
   rnoBCorr rnoA0 rnoB0 rnoSb rnoA1 rnoPk1 rnoCt rnoM
   aseSpkHonest asePqspkHonest aseEkASk aseFresh aseChallenged
   ikrPqspkPk ikrKemCt ikrKemSs rkrPqspkPk rkrKemCt rkrKemSs
   iasSid iasIkAPk iasPeerIkPk iasPeerSpkPk iasPeerOpkPk? iasEkAPk iasPeerPqspkPk
   iasKemCt iasEphAPk iasSpqrSalt? iasDrKey iasRk1 iasMkSeed iasCk1_1 iasMsgKeys
   asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
   asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
   asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
   asAdvKeys asRoCache asRootRoCache
   ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions
   ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots
   assNext assSendOpk assSendNoOpk assRecv assMk emptyAuthSlotStE
   lookupSendSlotE lookupSendSlotOrZeroE allocSendSlotE
   lookupRecvSlotE lookupRecvSlotOrZeroE allocRecvSlotE ahsfMkSlots ahsfUpdSlots
   natEq natLt nat2Eq nat3Eq bytes2Eq isSomeE optFst optSnd sessionSlotIndexE
   peMk peUpd sbMk oeMk oeUpd buMk hdMk pmMk seMk iasMk soMk snoMk roMk rnoMk
   ikrMk rkrMk stMk stUpd ahsMk ahsUpd ahsfMk ahsfUpd
   aNone aInitPrin aPk aCorr aBundle aSendFresh aSendUnfresh aRecvHonest aRecvUnfresh
   aDrKey aRootKdf queryDeriveMk)

private theorem size_liftPrimComp :
    ∀ {Γ t} (c : Comp pqxdhOps pqPrimIface Γ t),
      (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.msgKeyPrfOracle) c).size = c.size
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by simp only [liftPrimComp, Comp.size, size_liftPrimComp m, size_liftPrimComp k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [liftPrimComp, Comp.size, size_liftPrimComp t, size_liftPrimComp e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [liftPrimComp, Comp.size, size_liftPrimComp b]

private theorem litSize_liftPrimComp :
    ∀ {Γ t} (c : Comp pqxdhOps pqPrimIface Γ t),
      compLitSize (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.msgKeyPrfOracle) c) =
        compLitSize c
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp only [liftPrimComp, compLitSize, litSize_liftPrimComp m, litSize_liftPrimComp k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [liftPrimComp, compLitSize, litSize_liftPrimComp t, litSize_liftPrimComp e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [liftPrimComp, compLitSize, litSize_liftPrimComp b]

@[local simp] private theorem v_litSize {Γ Δ : List PT} {τ : PT} [Ext Γ Δ]
    (x : _root_.ReductionDsl.Var Γ τ) : exprLitSize (v (Δ := Δ) x) = 0 := rfl

private theorem liftExpr1_size_le {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a)) {C : ℕ}
    (h : (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.mapExpr e).size + 1 ≤ C) :
    (AuthCoreK.liftExpr1 e argE).size ≤ argE.size + C := by
  simp only [AuthCoreK.liftExpr1, Expr.size, exprRename_size]; omega

private theorem fixedRoCacheE_size_le {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ AuthCoreK.authFixedAtomicTy) :
    (fixedRoCacheE e).size ≤ e.size + 22 := by
  rw [fixedRoCacheE]; refine liftExpr1_size_le _ e ?_; decide

private theorem fixedRootRoCacheE_size_le {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ AuthCoreK.authFixedAtomicTy) :
    (fixedRootRoCacheE e).size ≤ e.size + 22 := by
  rw [fixedRootRoCacheE]; refine liftExpr1_size_le _ e ?_; decide

private theorem syncRoBoth_fixed_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ AuthCoreK.authFixedAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := pqPrfMkIface) cap
      (fixedRoCacheE fhstE) (fixedRootRoCacheE fhstE) roBothE).size ≤
      3750 + 4 * bits (avlHeightCap cap) + 2 * fhstE.size + roBothE.size := by
  have h := AuthCoreKCostBase.syncRoBothC_size_le (I := pqPrfMkIface) cap
    (fixedRoCacheE fhstE) (fixedRootRoCacheE fhstE) roBothE
  have h1 := fixedRoCacheE_size_le fhstE
  have h2 := fixedRootRoCacheE_size_le fhstE
  omega

private theorem liftPrfMk1_size_le {a r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {S0 L0 : ℕ}
    (hs : c.size ≤ S0) (hl : compLitSize c ≤ L0) :
    (liftPrfMk1 c e).size ≤ 10 * S0 + L0 + e.size + 2 := by
  have hm := mapComp_size_le tlPrfMk tlPrfMk_sizeLe c
  have hhm : (mapComp tlPrfMk c).size ≤ 10 * S0 + L0 := by omega
  unfold liftPrfMk1
  simp only [Comp.size]
  erw [compRename_size]
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left hhm _) 1) (by omega)

private theorem mkBaseArmC_size_le (S : Setup) (F : AuthKindFuels) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy → _root_.ReductionDsl.Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ RSF)
    (hs : (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)).size ≤
      600 + 2 * bits F.K_on)
    (hl : compLitSize (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)) ≤ 20) :
    (mkBaseArmC S step (Γ := [(authCodec S).Q])).size ≤ 6250 + 20 * bits F.K_on := by
  unfold mkBaseArmC
  simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (liftPrfMk1_size_le _ _ (S0 := 610 + 2 * bits F.K_on) (L0 := 20)
      (by rw [size_liftPrimComp]; simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
            Comp.size, Expr.size]; omega)
      (by rw [litSize_liftPrimComp]; simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
            compLitSize, exprLitSize]; omega)) _) 1) ?_
  simp only [mkRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[local simp] private theorem recvFinishTagRunC_size_aux (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : _root_.ReductionDsl.Var Γ₁ recvFinishTagTy)
    (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).size = res?.size + bits K + 4 * bits (min K S.N_dh) + 1864 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC, natEq, nat2Eq, nat3Eq,
    oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd, aNone, aRecvHonest, aRecvUnfresh,
    peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot,
    Expr.boolAnd, Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded,
    Expr.mapBounded, Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
    Comp.mapBoundedM, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[local simp] private theorem finishAuthHybridSendC_size_aux (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : _root_.ReductionDsl.Var Γ₁ authHybridStateTy)
    (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).size =
      args.size + 4 * bits (min K S.N_dh) + 2 * bits K + 1040 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr, optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk,
    ikrMk, stMk, stUpd, ahsMk, ahsUpd, aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk,
    sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId, pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents,
    asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE,
    Expr.boolNot, Expr.boolAnd, Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded,
    Expr.anyBounded, Expr.mapBounded, Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM,
    Comp.anyBoundedM, Comp.mapBoundedM, v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, findMV, anyMV, eCaseOpt, eAny, bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem recvFinishTagRunC_litSize_aux (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : _root_.ReductionDsl.Var Γ₁ recvFinishTagTy)
    (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    compLitSize (recvFinishTagRunC S K tag res?) = exprLitSize res? := by
  simp (config := { maxSteps := 1000000 }) only [recvFinishTagRunC, findHonestC, matchSentOPKC,
    matchSentNoOPKC, natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk,
    hdrIkAPk, hdrEkAPk, hdrKemCt, pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM,
    soMatched, soMarkMatched, snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched,
    snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM, rnoBCorr, rnoA0,
    rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents,
    asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs,
    ahsRecvKemRecs, ahsIdealSessions, boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE,
    Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr, Expr.listNil, Expr.listCons,
    Expr.findBounded, Expr.anyBounded, Expr.mapBounded, Comp.iteC, Comp.caseOptC, Comp.caseSumC,
    Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM, v_litSize, v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, caseSumV, findMV, consumeFirstMV, eMap, bytesBeq, Expr.bytesBeq,
    queryPrim, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem finishAuthHybridSendC_litSize_aux (S : Setup) (K : Nat)
    {Γ₁ Δ : List PT} (hst : _root_.ReductionDsl.Var Γ₁ authHybridStateTy)
    (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    compLitSize (finishAuthHybridSendC S K hst args) = exprLitSize args := by
  simp (config := { maxSteps := 1000000 }) only [finishAuthHybridSendC,
    checkBundleProvenanceExactC, checkBundleSpkHonIdealC, findHonestC, natEq, isSomeE, boolOr,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, Expr.litUnit,
    Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr,
    Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded, Comp.iteC,
    Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM, v_litSize,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, findMV, anyMV, eCaseOpt, eAny, bytesBeq, Expr.bytesBeq, queryPrim,
    compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem prfMkStepPostC_size_le_aux (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : _root_.ReductionDsl.Var Γ₁ prfMkChalContTy)
    (mk : _root_.ReductionDsl.Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K (Δ := Δ) cont mk).size ≤ 12 * bits K + 12000 := by
  simp only [prfMkStepPostC, finishAuthSendMkC, finishAuthRecvMkC, mkcSecb, mkcIdx, mkcSentChal,
    mkcFhst, mkcMk, recvFinishTagRunC_size_aux, finishAuthHybridSendC_size_aux,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC, resolveSigPkC,
    hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC, parKEntry, parSecrets,
    parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph, parHstDec, parFinishTag,
    fhstSetBase, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, sbSpkSk, sbSpkPk,
    sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed, pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig,
    pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?,
    hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt, aseSpkHonest,
    asePqspkHonest, aseEkASk, aseFresh, aseChallenged, ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk,
    rkrKemCt, rkrKemSs, iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1,
    iasMsgKeys, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples, asSentOPKEvents,
    asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsfHybrid, ahsfRecvCount,
    ahsfMkSaltCache, ahsfSlots, assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE, lookupRecvSlotE, lookupRecvSlotOrZeroE,
    allocRecvSlotE, ahsfMkSlots, ahsfUpdSlots, natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq,
    sidEq, saltBytesE, sameSaltKeyE, kyberEq, isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE,
    kyberCheckE, sessionSlotIndexE, peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk,
    soMk, snoMk, roMk, rnoMk, ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd, aNone,
    aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh, aDrKey,
    aRootKdf, sendGuardE, boolOr, boolBeq, eLet2, Expr.litUnit, Expr.litBool, Expr.litNat,
    Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr, Expr.listNil, Expr.listCons,
    Expr.findBounded, Expr.anyBounded, Expr.mapBounded, Comp.iteC, Comp.caseOptC, Comp.caseSumC,
    Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM, Comp.foldBoundedM, v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap, litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint,
    u32OfNat, u32Beq, samplePrim, queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte,
    Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min K S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
private theorem prfMkStepPostC_litSize_le_aux (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : _root_.ReductionDsl.Var Γ₁ prfMkChalContTy)
    (mk : _root_.ReductionDsl.Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (prfMkStepPostC S K (Δ := Δ) cont mk) ≤ 2000 := by
  simp (config := { maxSteps := 1000000 }) only [prfMkStepPostC, finishAuthSendMkC,
    finishAuthRecvMkC, recvFinishTagRunC_litSize_aux, finishAuthHybridSendC_litSize_aux,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
    koskBundleOkC, koskSenderOkC, resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC,
    checkBundleSpkHonIdealC, parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase, peSecIKA0, peIkAPk,
    peSecIKAsign, peIkSignPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk,
    oeOpkPk, oeConsumed, pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB,
    pkbPqspkSig, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    pkmPqRatchetMsg, pkmAeadCt, aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs, iasSid, iasIkAPk, iasPeerIkPk,
    iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt, iasEphAPk, iasSpqrSalt?,
    iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys, asSecb, asHasWonAuth, asPrincipals,
    asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, assNext, assSendOpk, assSendNoOpk,
    assRecv, assMk, emptyAuthSlotStE, lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE, ahsfMkSlots, ahsfUpdSlots, natEq,
    natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq, isSomeE,
    optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE, peMk, peUpd, sbMk,
    oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk, ikrMk, rkrMk, stMk,
    stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd, aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh,
    aSendUnfresh, aRecvHonest, aRecvUnfresh, aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM, v_litSize, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap, litB, catB, bytesCons, widenB, takeKB, bytesLen,
    bytesBeq, bytesVarint, u32OfNat, u32Beq, Expr.litBytes, Expr.bytesAppend, Expr.bytesCons,
    Expr.bytesWiden, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
    Expr.bytesVarint, Expr.u32OfNat, Expr.u32Beq, samplePrim, queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize, List.length_nil, List.length_cons,
    List.length_replicate, F_X25519_length, Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem authMkRecvPreKB_size_tight_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : _root_.ReductionDsl.Var Γ₁ prfMkCoreTy)
    (x : _root_.ReductionDsl.Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x).size ≤
      38000 + 96 * bits K_on + 2 * bits K_ro := by
  cases opk <;>
  · simp only [authMkRecvPreKB,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase.authMkRecvPreKB,
      finishAuthRecvMkC, finishRecvUnmatchedMkPreC, recvFinishTagRunC_size_aux,
      prepareAuthHybridRecvC, matchIdealAuthHandshakeC, mkcSecb, mkcIdx, mkcSentChal, mkcFhst,
      mkcMk, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, fhstSetBase, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk,
      peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed, pkbIkB,
      pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig, hdrIkAPk,
      hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
      pkmAeadCt, aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged, ikrPqspkPk,
      ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs, iasSid, iasIkAPk, iasPeerIkPk,
      iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt, iasEphAPk, iasSpqrSalt?,
      iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys, asSecb, asHasWonAuth, asPrincipals,
      asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
      asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
      asRecvdNoOPKEvents, asAdvKeys, asRoCache, asRootRoCache, ahsBase, ahsInitKemRecs,
      ahsRecvKemRecs, ahsIdealSessions, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
      assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE, lookupSendSlotE,
      lookupSendSlotOrZeroE, allocSendSlotE, lookupRecvSlotE, lookupRecvSlotOrZeroE,
      allocRecvSlotE, ahsfMkSlots, ahsfUpdSlots, natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq,
      sidEq, saltBytesE, sameSaltKeyE, kyberEq, isSomeE, optFst, optSnd, firstMsgADE,
      buildSecretsE, kyberCheckE, sessionSlotIndexE, peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk,
      pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk, ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd,
      ahsfMk, ahsfUpd, aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh,
      aRecvHonest, aRecvUnfresh, aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded,
      Expr.mapBounded, Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM,
      Comp.anyBoundedM, Comp.mapBoundedM, Comp.foldBoundedM, v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV, eLet, eCaseOpt, eCaseSum,
      eFind, eAny, eMap, litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint,
      u32OfNat, u32Beq, samplePrim, queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte,
      Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
    dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have hmdh : bits (min K_on S.N_dh) ≤ bits K_on :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    have hmsess : bits (min K_on S.N_sess_tot) ≤ bits K_on :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    omega

private theorem mkPostRunC_size_le (S : Setup) (K_on : ℕ) {Δ : List PT}
    (bud : _root_.ReductionDsl.Var Δ .nat)
    (core : _root_.ReductionDsl.Var Δ prfMkCoreTy)
    (pre : _root_.ReductionDsl.Var Δ prfMkStepPreTy) :
    (mkPostRunC S K_on bud core pre).size ≤ 12100 + 12 * bits K_on := by
  unfold mkPostRunC
  have hp := prfMkStepPostC_size_le_aux S K_on
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ)
    (.zero : _root_.ReductionDsl.Var (prfMkChalContTy ::
      .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ) prfMkChalContTy)
    (.zero : _root_.ReductionDsl.Var (msgKeysTy :: prfMkChalContTy ::
      .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ) msgKeysTy)
  simp only [caseSumV, letV, bindV, natEq, aNone, queryDeriveMk, size_liftPrimComp,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, v, Comp.size, Expr.size]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  omega

private theorem mkPostRunC_litSize_le (S : Setup) (K_on : ℕ) {Δ : List PT}
    (bud : _root_.ReductionDsl.Var Δ .nat)
    (core : _root_.ReductionDsl.Var Δ prfMkCoreTy)
    (pre : _root_.ReductionDsl.Var Δ prfMkStepPreTy) :
    compLitSize (mkPostRunC S K_on bud core pre) ≤ 2100 := by
  unfold mkPostRunC
  have hp := prfMkStepPostC_litSize_le_aux S K_on
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ)
    (.zero : _root_.ReductionDsl.Var (prfMkChalContTy ::
      .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ) prfMkChalContTy)
    (.zero : _root_.ReductionDsl.Var (msgKeysTy :: prfMkChalContTy ::
      .opt (_root_.SignalPqxdh.LegacyCosted.B 32) ::
      (.prod (.opt (_root_.SignalPqxdh.LegacyCosted.B 32)) prfMkChalContTy) :: Δ) msgKeysTy)
  simp only [caseSumV, letV, bindV, natEq, aNone, queryDeriveMk, litSize_liftPrimComp,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    v, compLitSize, exprLitSize, Nat.add_zero]
  omega

private theorem mkOnlineArm_size_le (S : Setup) (F : AuthKindFuels) {arg : Ty pqSig} {S_pre : ℕ}
    (preStep : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ prfMkCoreTy → _root_.ReductionDsl.Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy)
    (hs : (preStep
      (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
      (.zero : _root_.ReductionDsl.Var [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg] prfMkCoreTy)
      (.zero : _root_.ReductionDsl.Var [arg, prfMkStTy, .prod prfMkStTy arg] arg)).size ≤ S_pre)
    (hl : compLitSize (preStep
      (Δ := [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
      (.zero : _root_.ReductionDsl.Var [prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg] prfMkCoreTy)
      (.zero : _root_.ReductionDsl.Var [arg, prfMkStTy, .prod prfMkStTy arg] arg)) ≤ 4000) :
    (.bind (liftPrfMk1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun _bud =>
         letV (.snd (v s)) fun core =>
         bindV (liftPrimComp (preStep core x)) fun _pre =>
         mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)
        (.pair (.fst .v1) .v0))
      (.bind (syncRoBothC F.K_cap
          (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
          (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
          (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
      Comp pqAtomicOps pqPrfMkIface
        [embedTy arg, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy))).size ≤
      10 * S_pre + 131250 + 120 * bits F.K_on + 4 * bits (avlHeightCap F.K_cap) := by
  simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add
    (liftPrfMk1_size_le _ _ (S0 := S_pre + 12130 + 12 * bits F.K_on) (L0 := 6100)
      (by have hp := mkPostRunC_size_le S F.K_on
            (Δ := [prfMkStepPreTy, prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
            (.succ (.succ .zero)) (.succ .zero) .zero
          simp only [letV, bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
            size_liftPrimComp, v, Comp.size, Expr.size]; omega)
      (by have hp := mkPostRunC_litSize_le S F.K_on
            (Δ := [prfMkStepPreTy, prfMkCoreTy, .nat, arg, prfMkStTy, .prod prfMkStTy arg])
            (.succ (.succ .zero)) (.succ .zero) .zero
          simp only [letV, bindV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
            litSize_liftPrimComp, v, compLitSize, exprLitSize]; omega))
    (Nat.add_le_add_right (Nat.add_le_add_right
      (syncRoBoth_fixed_size_le F.K_cap _ _) _) 1)) 1) ?_
  simp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

theorem prfMsgKeys1KeyKindProg_size_le (S : Setup) (b : QueryBudget) :
    (prfMsgKeys1KeyKindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  rcases ofBudget_size_bits S b with ⟨hkon, hkro, hsess, hrecv, hmdh, h4mdh, havl⟩
  let F := AuthKindFuels.ofBudget S b
  have hInit : (prfMkKindInitC S b).size ≤
      3100 + 20 * bits (min b.q_total S.N_sess_tot) + 20 * bits (min b.q_total S.N_recv_tot + 1) := by
    have hs : (prfMsgKeysInitDslK S b.q_total).size ≤
        250 + 2 * bits (min b.q_total S.N_sess_tot) + 2 * bits (min b.q_total S.N_recv_tot + 1) := by
      simp only [prfMsgKeysInitDslK, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
        emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, sampleChal, v,
        Comp.size, Expr.size]
      have : bits 0 = 1 := by decide
      omega
    have hl : compLitSize (prfMsgKeysInitDslK S b.q_total) = 0 := by
      simp only [prfMsgKeysInitDslK, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
        emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, sampleChal, v,
        compLitSize, exprLitSize, Nat.add_zero]
    have hm := mapComp_size_le tlPrfMk tlPrfMk_sizeLe (prfMsgKeysInitDslK S b.q_total)
    have hhm : (mapComp tlPrfMk (prfMsgKeysInitDslK S b.q_total)).size ≤
        2500 + 20 * bits (min b.q_total S.N_sess_tot) + 20 * bits (min b.q_total S.N_recv_tot + 1) := by omega
    have he := emptyRoBothAvlE_size_le (Γ := [embedTy (.prod .unit prfMkStTy), .unit])
    unfold prfMkKindInitC
    simp only [Comp.size, Expr.size, Expr.v0]
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add hhm
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left he _) _) 1)) 1) (by omega)
  have hFin : (prfMkKindFinishC S F).size ≤
      3600 + 40 * bits (min F.K_on S.N_dh) + 50 * bits (4 * min F.K_on S.N_dh) +
        70 * bits F.K_on := by
    have hstep : ∀ {a r : Ty pqSig} {Γ : List PT} (e : Expr pqxdhOps Γ a)
        (body : Comp pqxdhOps pqPrimIface (a :: Γ) r) {B : ℕ},
        body.size ≤ B → (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC e body).size ≤
          e.size + B + 2 := by
      intro _ _ _ e body _ hb
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.size]; omega
    have hs : (prfMsgKeysFinishDsl S F.K_on).size ≤
        350 + 4 * bits (min F.K_on S.N_dh) + 5 * bits (4 * min F.K_on S.N_dh) +
          7 * bits F.K_on := by
      unfold prfMsgKeysFinishDsl
      rw [size_liftPrimComp]
      dsimp only [letV]
      refine le_trans (hstep _ _ (hstep _ _ (hstep _ _ (hstep _ _
        (finalizeAuthFixedDsl_size_le S F.K_on))))) ?_
      simp only [mkcFhst, ahsfHybrid, v, Expr.size]; omega
    have hl : compLitSize (prfMsgKeysFinishDsl S F.K_on) = 0 := by
      unfold prfMsgKeysFinishDsl
      rw [litSize_liftPrimComp]
      simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
        mkcSecb, mkcFhst, ahsfHybrid, finalizeAuthFixedDsl_litSize_eq,
        v, compLitSize, exprLitSize, Nat.add_zero]
    have hm := mapComp_size_le tlPrfMk tlPrfMk_sizeLe (prfMsgKeysFinishDsl S F.K_on)
    have hhm : (mapComp tlPrfMk (prfMsgKeysFinishDsl S F.K_on)).size ≤
        3500 + 40 * bits (min F.K_on S.N_dh) + 50 * bits (4 * min F.K_on S.N_dh) +
          70 * bits F.K_on := by omega
    unfold prfMkKindFinishC
    simp only [Comp.size, Expr.size, Expr.v0]
    erw [compRename_size]
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left hhm _) 1) (by omega)
  have hHandle : (prfMkKindHandleC S F).size ≤
      1610000 + 3500 * bits F.K_on + 240 * bits F.K_ro + 20 * bits (avlHeightCap F.K_cap) := by
    unfold prfMkKindHandleC
    dsimp only
    exact dispatchAuthQ_size_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ (b0 := 1) (by rfl)
      (mkBaseArmC_size_le S F (fun fhst u => AuthCoreK.initPrin1KeyFixedKB F fhst u)
        (initPrin1KeyFixedKB_size_le F _ _) (initPrin1KeyFixedKB_litSize_le F _ _))
      (mkBaseArmC_size_le S F (fun fhst u => AuthCoreK.corruptFixedKB F fhst u)
        (corruptFixedKB_size_le F _ _) (corruptFixedKB_litSize_le F _ _))
      (mkBaseArmC_size_le S F (fun fhst x => AuthCoreK.genSpkFixedKB F fhst x)
        (genSpkFixedKB_size_le F _ _) (genSpkFixedKB_litSize_le F _ _))
      (mkBaseArmC_size_le S F (fun fhst x => AuthCoreK.genOpkFixedKB F fhst x)
        (genOpkFixedKB_size_le F _ _) (genOpkFixedKB_litSize_le F _ _))
      (mkOnlineArm_size_le S F
        (fun core x => authMkSendPreKB S F.K_on F.K_ro true core x)
        (authMkSendPreKB_size_le S F.K_on F.K_ro true _ _)
        (authMkSendPreKB_litSize_le S F.K_on F.K_ro true _ _))
      (mkOnlineArm_size_le S F
        (fun core x => authMkSendPreKB S F.K_on F.K_ro false core x)
        (authMkSendPreKB_size_le S F.K_on F.K_ro false _ _)
        (authMkSendPreKB_litSize_le S F.K_on F.K_ro false _ _))
      (mkOnlineArm_size_le S F
        (fun core x => authMkRecvPreKB S F.K_on F.K_ro true core x)
        (authMkRecvPreKB_size_tight_le S F.K_on F.K_ro true _ _)
        (authMkRecvPreKB_litSize_le S F.K_on F.K_ro true _ _))
      (mkOnlineArm_size_le S F
        (fun core x => authMkRecvPreKB S F.K_on F.K_ro false core x)
        (authMkRecvPreKB_size_tight_le S F.K_on F.K_ro false _ _)
        (authMkRecvPreKB_litSize_le S F.K_on F.K_ro false _ _))
      (b9 := 2420 + 2 * bits (avlHeightCap F.K_cap))
      (by simp only [Comp.size]
          refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
            (AuthCoreKCostBase.roFixedShadowArmC_size_le aiPrfMk F.K_cap _ _) _) 1) ?_
          simp only [mkRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega)
      (b10 := 2470 + 2 * bits (avlHeightCap F.K_cap))
      (by simp only [Comp.size]
          refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
            (AuthCoreKCostBase.roRootFixedShadowArmC_size_le aiPrfMk F.K_cap _ _) _) 1) ?_
          simp only [mkRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega)
      (b11 := 25)
      (by simp only [Comp.size, aNoneAtomicE, Expr.size, Expr.v1]; decide)
      (mkBaseArmC_size_le S F (fun fhst sk => AuthCoreK.registerFixedKB fhst sk)
        (registerFixedKB_size_le F _ _) (registerFixedKB_litSize_le _ _))
      (by omega)
  have hB : reductionSizeBudget = 2 ^ 24 := rfl
  rw [hB]
  change (prfMkKindInitC S b).size + (prfMkKindHandleC S F).size + (prfMkKindFinishC S F).size ≤
    2 ^ 24 + 2 ^ 12 * bits (stepCostBudget S b)
  dsimp only [F] at hFin hHandle ⊢
  omega

end MkSizeHelpers

end PrfCkMkBounds

/-! ## `prfHmac1KeyKindProg` Bounds -/

section PrfHmacBounds

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (hmInitC hmFinishC hm_init_cost hm_finish_cost hm_init_queries_prim hm_finish_queries_prim)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (chalPrimW)

private def zeroSetup : Setup := ⟨0, 0, 0, 0, 0, 0⟩

private theorem tlPrfHmac_chalPrimW {Γ : List (Ty pqAtomicSig)}
    (g : _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface.Tag)
    (e : Expr _root_.ReductionDsl.pqAtomicOps Γ
      (embedTy (_root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface.dom g))) :
    (tlPrfHmac.mapQuery g e).queries authChalIfacePrimQueryWeight (fun _ => 0) ≤
      chalPrimW g := by
  rcases g with g | g <;> exact tlPrfHmac_primW _ e

theorem prfHmacKindInitC_cost_le (S : Setup) :
    (prfHmacKindInitC S).cost ≤ 1000 + 4 * Nat.log 2 S.N_sess_tot := by
  have hc : (hmInitC S).cost = 75 + bits S.N_sess_tot := hm_init_cost S 0
  have hb : bits S.N_sess_tot = Nat.log 2 S.N_sess_tot + 1 := rfl
  have hm := mapComp_cost_eleven_mul_le tlPrfHmac (hmInitC S)
  have hhm : (mapComp tlPrfHmac (hmInitC S)).cost ≤ 160 + 4 * Nat.log 2 S.N_sess_tot := by omega
  have he := emptyRoBothAvlE_cost_le (Γ := [embedTy (.prod .unit hmStTy), .unit])
  unfold prfHmacKindInitC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hhm _) 1) (by omega)

theorem prfHmacKindHandleC_costAt_kind1_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy hmStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 1) :
    (prfHmacKindHandleC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      4420 * bits F.K_cap + 1650 := by
  unfold prfHmacKindHandleC
  dsimp only
  refine le_trans (AuthCoreKCostBase.dispatchAuthQ_v1_costAt_kind1_le
    _ _ _ _ _ _ _ _ _ _ _ _ s q .nil (B₁ := 4420 * bits F.K_cap + 1630) hk ?_ ?_) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [hmRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (AuthCoreKCostBase.roRootFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [hmRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    omega

private theorem queries_liftPrimComp_hm_r64 :
    ∀ {Γ t} (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t),
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle) c).queries
        (fun _ => 0) (sampR64W tlPrfHmac.hsmp) =
      c.queries (fun _ => 0) (sampR64W tlAuthPrim.hsmp)
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.queries,
      queries_liftPrimComp_hm_r64 m, queries_liftPrimComp_hm_r64 k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.queries,
      queries_liftPrimComp_hm_r64 t, queries_liftPrimComp_hm_r64 e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.queries,
      queries_liftPrimComp_hm_r64 b]

private theorem hmPostRunC_cost_le (K_on : ℕ)
    {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (jt : _root_.ReductionDsl.Var Δ .nat)
    (pre : _root_.ReductionDsl.Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPreTy) :
    (hmPostRunC K_on jt pre).cost ≤ 4020 + 1582 * K_on := by
  unfold hmPostRunC
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.cost_queryHmacEval,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmContX0E_cost,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.cost_liftPrimComp,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPostC_cost, Comp.cost, Expr.cost]
  omega

private theorem hmPostRunC_r64 (K_on : ℕ)
    {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (jt : _root_.ReductionDsl.Var Δ .nat)
    (pre : _root_.ReductionDsl.Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPreTy) :
    (hmPostRunC K_on jt pre).queries (fun _ => 0) (sampR64W tlPrfHmac.hsmp) = 0 := by
  have hp : ∀ {Δ' : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      (a : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ'
        (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmSendContTy
          (_root_.SignalPqxdh.LegacyCosted.B 32))),
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPostC K_on a).queries
        (fun _ => 0) (sampR64W tlAuthPrim.hsmp) = 0 := fun _ => by
    simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPostC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.encPostC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.finishIntC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.queries]
  unfold hmPostRunC
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
  simp only [Comp.queries, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.queryHmacEval,
    queries_liftPrimComp_hm_r64, hp]; omega

private theorem liftPrfHmac1_cost_le {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {B R M : ℕ}
    (hc : c.cost ≤ B) (hr : c.queries (fun _ => 0) (sampR64W tlPrfHmac.hsmp) ≤ R)
    (hM : 3 * B + 78 * R ≤ 2 * M) :
    (liftPrfHmac1 c e).cost ≤ M + e.cost + 2 := by
  have hmc : (mapComp tlPrfHmac c).cost ≤ M := by
    have hm := mapComp_cost_two_mul_le tlPrfHmac c; omega
  unfold liftPrfHmac1; simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left ((compRename_cost _ _).le.trans hmc) _) 1) ?_
  omega

private theorem hmBaseArmC_cost_le (S : Setup) (F : AuthKindFuels)
    {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy →
      _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)}
    (hc : (step (Δ := [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var
        [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).cost ≤
      9500 + F.K_on * 50) :
    (hmBaseArmC S step (Γ := Γ)).cost ≤ 20200 + 110 * F.K_on := by
  have hc' : (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
      (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       step fhst x) :
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface
        [.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _).cost ≤
      9510 + F.K_on * 50 := by
    rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.cost_liftPrimComp]
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV]
    refine le_trans (letC_cost_step _ _ (letC_cost_step _ _ hc)) ?_
    simp only [Expr.cost]; omega
  have hmc : (mapComp tlPrfHmac (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       step fhst x) :
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface
        [.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).cost ≤
      20066 + 110 * F.K_on := by
    have hm := mapComp_cost_eleven_mul_le tlPrfHmac
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         step fhst x) :
        Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface
          [.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
    omega
  unfold hmBaseArmC liftPrfHmac1; simp only [Comp.cost]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add_left ((compRename_cost _ _).le.trans hmc) _) 1) (le_refl _)) 1) ?_
  simp only [hmRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega

private theorem prfHmacKindHandleC_cost_le_aux (S : Setup) (F : AuthKindFuels) :
    (prfHmacKindHandleC S F).cost ≤
      40000 + 15000 * F.K_on + 3300 * min F.K_on S.N_dh + 15500 * min F.K_on S.N_sess_tot +
        1111 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  have hSend : ∀ opk : Bool,
      (.bind (liftPrfHmac1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)) fun jt =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun fhst =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun mst =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV
             (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x))
             fun _pre => hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0)))) (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
        Comp pqAtomicOps pqPrfHmacIface [authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy))).cost ≤
      40000 + 15000 * F.K_on + 3300 * min F.K_on S.N_dh + 15500 * min F.K_on S.N_sess_tot +
        1111 * F.K_ro + (8500 * bits F.K_cap + 2058) := fun opk => by
    have hL : (liftPrfHmac1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)) fun jt =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun fhst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun mst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV
           (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x))
           fun _pre => hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
        (.pair (.fst .v1) .v0 : Expr pqAtomicOps
          [authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _)).cost ≤
        27400 + 10400 * F.K_on + 2310 * min F.K_on S.N_dh + 797 * F.K_ro +
          (Expr.pair (.fst .v1) .v0 : Expr pqAtomicOps
            [authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
            (embedTy (.prod hmStTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sendQTy))).cost + 2 := by
      refine liftPrfHmac1_cost_le _ _
        (B := 18160 + 6901 * F.K_on + 1540 * min F.K_on S.N_dh + 531 * F.K_ro) (R := 2) ?_ ?_ (by omega)
      · dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
        refine le_trans (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _
          (by simp only [Comp.cost, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.cost_liftPrimComp]
              exact Nat.add_le_add_right (Nat.add_le_add (hmSendKC_cost_le S F.K_on F.K_ro opk _ _ _ _) (hmPostRunC_cost_le F.K_on _ _)) 1)))))) ?_
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v, Expr.cost]; omega
      · dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
        simp only [Comp.queries, queries_liftPrimComp_hm_r64, hmPostRunC_r64, Nat.zero_add, Nat.add_zero]
        exact hmSendKC_r64_le S F.K_on F.K_ro opk _ _ _ _
    have hs := AuthCoreKCostBase.syncRoBothC_cost_le (I := pqPrfHmacIface) F.K_cap
      (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy),
         authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _)))))
      (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps _ _))))) (.snd .v2)
    have hr1 : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy),
         authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).cost ≤ 30 := by
      exact (by decide : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy)] _))))).cost ≤ 30)
    have hr2 : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy),
         authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).cost ≤ 30 := by
      exact (by decide : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy)] _))))).cost ≤ 30)
    simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hL hs hr1 hr2 ⊢; omega
  have hRecv : ∀ opk : Bool,
      (.bind (liftPrfHmac1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)) fun jt =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun fhst =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun mst =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV
             (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x))
             fun _pre => hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0)))) (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
        Comp pqAtomicOps pqPrfHmacIface [authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy))).cost ≤
      40000 + 15000 * F.K_on + 3300 * min F.K_on S.N_dh + 15500 * min F.K_on S.N_sess_tot +
        1111 * F.K_ro + (8500 * bits F.K_cap + 2058) := fun opk => by
    have hL : (liftPrfHmac1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)) fun jt =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun fhst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun mst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV
           (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x))
           fun _pre => hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
        (.pair (.fst .v1) .v0 : Expr pqAtomicOps
          [authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _)).cost ≤
        30500 + 4600 * F.K_on + 950 * min F.K_on S.N_dh + 11025 * min F.K_on S.N_sess_tot + 797 * F.K_ro +
          (Expr.pair (.fst .v1) .v0 : Expr pqAtomicOps
            [authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
            (embedTy (.prod hmStTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.recvQTy))).cost + 2 := by
      refine liftPrfHmac1_cost_le _ _
        (B := 20260 + 3051 * F.K_on + 630 * min F.K_on S.N_dh + 7350 * min F.K_on S.N_sess_tot + 531 * F.K_ro)
        (R := 2) ?_ ?_ (by omega)
      · dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
        refine le_trans (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _ (letC_cost_step _ _
          (by simp only [Comp.cost, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.cost_liftPrimComp]
              exact Nat.add_le_add_right (Nat.add_le_add (hmRecvKC_cost_le S F.K_on F.K_ro opk _ _ _ _) (hmPostRunC_cost_le F.K_on _ _)) 1)))))) ?_
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v, Expr.cost]; omega
      · dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
        simp only [Comp.queries, queries_liftPrimComp_hm_r64, hmPostRunC_r64, Nat.zero_add, Nat.add_zero]
        exact hmRecvKC_r64_le S F.K_on F.K_ro opk _ _ _ _
    have hs := AuthCoreKCostBase.syncRoBothC_cost_le (I := pqPrfHmacIface) F.K_cap
      (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy),
         authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _)))))
      (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps _ _))))) (.snd .v2)
    have hr1 : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy),
         authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).cost ≤ 30 := by
      exact (by decide : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy)] _))))).cost ≤ 30)
    have hr2 : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy),
         authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).cost ≤ 30 := by
      exact (by decide : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy)] _))))).cost ≤ 30)
    simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hL hs hr1 hr2 ⊢; omega
  unfold prfHmacKindHandleC; dsimp only
  refine le_trans (AuthCoreKCostBase.dispatchAuthQ_cost_le _ _ _ _ _ _ _ _ _ _ _ _ _
    (B := 40000 + 15000 * F.K_on + 3300 * min F.K_on S.N_dh + 15500 * min F.K_on S.N_sess_tot +
      1111 * F.K_ro + (8500 * bits F.K_cap + 2058))
    ?_ ?_ ?_ ?_ (hSend true) (hSend false) (hRecv true) (hRecv false) ?_ ?_ ?_ ?_) ?_
  · refine le_trans (hmBaseArmC_cost_le S F _ ?_) (by omega)
    exact le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.initPrin1KeyFixedB_cost_le F.K_on _ _)
      (le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.initPrinFixedB_cost_le F.K_on _ _) (by omega))
  · refine le_trans (hmBaseArmC_cost_le S F _ ?_) (by omega)
    exact le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.corruptFixedB_cost_le F.K_on _ _) (by omega)
  · refine le_trans (hmBaseArmC_cost_le S F _ ?_) (by omega)
    exact le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genSpkFixedB_cost_le F.K_on _ _) (by omega)
  · refine le_trans (hmBaseArmC_cost_le S F _ ?_) (by omega)
    exact le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genOpkFixedB_cost_le F.K_on _ _) (by omega)
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (AuthCoreKCostBase.roFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [hmRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (AuthCoreKCostBase.roRootFixedShadowArmC_cost_le _ _ _ _) _) 1) ?_
    simp only [hmRebuildE, Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega
  · simp only [Comp.cost, aNoneAtomicE, Expr.cost, Expr.v1]; omega
  · refine le_trans (hmBaseArmC_cost_le S F _ ?_) (by omega)
    exact le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.registerFixedB_cost_le _ _) (by omega)
  · simp only [Expr.cost]; omega

theorem prfHmacKindHandleC_costAt_kind0_le (S : Setup) (F : AuthKindFuels)
    (s : (Ty.prod (embedTy hmStTy) roBothAvlTy).denote) (q : AuthQuery S)
    (hk : authQueryKind q = 0) :
    (prfHmacKindHandleC S F).costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      40000 + 15000 * F.K_on + 3300 * min F.K_on S.N_dh + 15500 * min F.K_on S.N_sess_tot +
        1111 * F.K_ro + (8500 * bits F.K_cap + 2080) := by
  let _ := hk; exact (Comp.costAt_le_cost _ _).trans (prfHmacKindHandleC_cost_le_aux S F)

theorem prfHmacKindHandleC_cost_le (S : Setup) (F : AuthKindFuels) :
    (prfHmacKindHandleC S F).cost ≤
      40000 + 15000 * F.K_on + 3300 * min F.K_on S.N_dh + 15500 * min F.K_on S.N_sess_tot +
        1111 * F.K_ro + (8500 * bits F.K_cap + 2080) :=
  prfHmacKindHandleC_cost_le_aux S F

theorem prfHmacKindFinishC_cost_le (F : AuthKindFuels) :
    (prfHmacKindFinishC F).cost ≤
      100 + 910 * F.K_on + 3300 * F.K_on ^ 2 := by
  have hc : (hmFinishC F.K_on).cost = 35 + F.K_on * 432 + F.K_on ^ 2 * 1575 :=
    hm_finish_cost zeroSetup F.K_on
  have hm := mapComp_cost_eleven_mul_le tlPrfHmac (hmFinishC F.K_on)
  have hhm : (mapComp tlPrfHmac (hmFinishC F.K_on)).cost ≤
      80 + 910 * F.K_on + 3300 * F.K_on ^ 2 := by omega
  unfold prfHmacKindFinishC
  simp only [Comp.cost, Expr.cost, Expr.v0]
  erw [compRename_cost]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left hhm _) _) (by omega)

theorem prfHmacKindInitC_queries_prim_le (S : Setup) :
    (prfHmacKindInitC S).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : (hmInitC S).queries chalPrimW _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    hm_init_queries_prim S 0
  have hm := mapComp_queries_le tlPrfHmac
    chalPrimW _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfacePrimQueryWeight tlPrfHmac_chalPrimW (hmInitC S)
  apply Nat.eq_zero_of_le_zero
  unfold prfHmacKindInitC
  simp only [Comp.queries, Nat.add_zero]
  exact le_trans hm (by omega)

private theorem letC_queries {ι : Type} {T : _root_.OracleSpec ι}
    {I : _root_.ReductionDsl.Iface _root_.SignalPqxdh.LegacyCosted.pqSig T}
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Γ a)
    (body : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps I (a :: Γ) r)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC e body).queries w ws =
      body.queries w ws := by
  simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.queries]

private theorem queries_liftPrimComp_chalPrim :
    ∀ {Γ t} (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t),
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle) c).queries
        chalPrimW _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      c.queries _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.queries,
      queries_liftPrimComp_chalPrim m, queries_liftPrimComp_chalPrim k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.queries,
      queries_liftPrimComp_chalPrim t, queries_liftPrimComp_chalPrim e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.queries,
      queries_liftPrimComp_chalPrim b]

private theorem hmPostRunC_queries (K_on : ℕ)
    {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (jt : _root_.ReductionDsl.Var Δ .nat)
    (pre : _root_.ReductionDsl.Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPreTy) :
    (hmPostRunC K_on jt pre).queries chalPrimW
      _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  have hp : ∀ {Δ' : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      (a : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Δ'
        (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmSendContTy
          (_root_.SignalPqxdh.LegacyCosted.B 32))),
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPostC K_on a).queries
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS = 0 := fun _ => by
    simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPostC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.encPostC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.finishIntC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.queries]
  unfold hmPostRunC
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
  simp only [Comp.queries, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.queryHmacEval,
    chalPrimW, queries_liftPrimComp_chalPrim, hp]; omega

theorem prfHmacKindHandleC_queries_prim_le (S : Setup) (F : AuthKindFuels) :
    (prfHmacKindHandleC S F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      40 + 30 * S.N_dh + 12 * S.N_sess_tot := by
  have hmin1 : min F.K_on S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hmin2 : min F.K_on S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hLift : ∀ {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
      (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a] r)
      {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) {Q : ℕ},
      c.queries chalPrimW _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ Q →
      (liftPrfHmac1 c e).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
    intro a r c Γ e Q hq
    have hm := mapComp_queries_le tlPrfHmac chalPrimW _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authChalIfacePrimQueryWeight tlPrfHmac_chalPrimW c
    unfold liftPrfHmac1; simp only [Comp.queries, Nat.zero_add]; erw [compRename_queries]
    exact le_trans hm hq
  have hBase : ∀ {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
      (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
        _root_.ReductionDsl.Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy →
        _root_.ReductionDsl.Var Γ₂ arg →
        Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
      {Γ : List (Ty pqAtomicSig)} {Q : ℕ},
      (step (Δ := [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg])
        (.zero : _root_.ReductionDsl.Var
          [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
            .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)
        (.zero : _root_.ReductionDsl.Var
          [arg, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy,
            .prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy arg] _)).queries
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primW
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.primWS ≤ Q →
      (hmBaseArmC S step (Γ := Γ)).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ Q := by
    intro arg step Γ Q hq; unfold hmBaseArmC; simp only [Comp.queries, Nat.add_zero]
    apply hLift; rw [queries_liftPrimComp_chalPrim]
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV]
    rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queries_letC,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.queries_letC]; exact hq
  unfold prfHmacKindHandleC; dsimp only
  refine AuthCoreKCostBase.dispatchAuthQ_queries_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine le_trans (hBase _ (Q := 2) ?_) (by omega)
    exact le_trans (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.initPrin1KeyFixedB_queries_le F.K_on _ _ _ _)
      (le_of_eq (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.initPrinFixedB_queries F.K_on _ _))
  · exact le_trans (hBase _ (Q := 0) (le_of_eq (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.corruptFixedB_queries F.K_on _ _))) (by omega)
  · exact le_trans (hBase _ (Q := 4) (le_of_eq (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genSpkFixedB_queries F.K_on _ _))) (by omega)
  · exact le_trans (hBase _ (Q := 1) (le_of_eq (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genOpkFixedB_queries F.K_on _ _))) (by omega)
  · simp only [Comp.queries, AuthCoreKCostBase.syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (hLift _ _ (Q := 30 + 20 * min F.K_on S.N_dh) ?_) (by omega)
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
    simp only [Comp.queries, queries_liftPrimComp_chalPrim, hmPostRunC_queries, Nat.zero_add, Nat.add_zero]
    exact hmSendKC_queries_prim_le S F.K_on F.K_ro true _ _ _ _
  · simp only [Comp.queries, AuthCoreKCostBase.syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (hLift _ _ (Q := 30 + 20 * min F.K_on S.N_dh) ?_) (by omega)
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
    simp only [Comp.queries, queries_liftPrimComp_chalPrim, hmPostRunC_queries, Nat.zero_add, Nat.add_zero]
    exact hmSendKC_queries_prim_le S F.K_on F.K_ro false _ _ _ _
  · simp only [Comp.queries, AuthCoreKCostBase.syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (hLift _ _ (Q := 30 + 10 * min F.K_on S.N_dh + 10 * min F.K_on S.N_sess_tot) ?_) (by omega)
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
    simp only [Comp.queries, queries_liftPrimComp_chalPrim, hmPostRunC_queries, Nat.zero_add, Nat.add_zero]
    exact hmRecvKC_queries_prim_le S F.K_on F.K_ro true _ _ _ _
  · simp only [Comp.queries, AuthCoreKCostBase.syncRoBothC_queries_zero, Nat.add_zero]
    refine le_trans (hLift _ _ (Q := 30 + 10 * min F.K_on S.N_dh + 10 * min F.K_on S.N_sess_tot) ?_) (by omega)
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV]
    simp only [Comp.queries, queries_liftPrimComp_chalPrim, hmPostRunC_queries, Nat.zero_add, Nat.add_zero]
    exact hmRecvKC_queries_prim_le S F.K_on F.K_ro false _ _ _ _
  · simp only [Comp.queries, Nat.add_zero]
    exact (AuthCoreKCostBase.roFixedShadowArmC_queries_zero aiPrfHmac authChalIfacePrimQueryWeight F.K_cap _ _).le.trans (Nat.zero_le _)
  · simp only [Comp.queries, Nat.add_zero]
    exact (AuthCoreKCostBase.roRootFixedShadowArmC_queries_zero aiPrfHmac authChalIfacePrimQueryWeight F.K_cap _ _).le.trans (Nat.zero_le _)
  · simp only [Comp.queries]; omega
  · exact le_trans (hBase _ (Q := 2) (le_of_eq (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.registerFixedB_queries _ _))) (by omega)

theorem prfHmacKindFinishC_queries_prim_le (F : AuthKindFuels) :
    (prfHmacKindFinishC F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have hq : (hmFinishC F.K_on).queries chalPrimW
      _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    hm_finish_queries_prim zeroSetup F.K_on
  have hm := mapComp_queries_le tlPrfHmac
    chalPrimW _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfacePrimQueryWeight tlPrfHmac_chalPrimW (hmFinishC F.K_on)
  apply Nat.eq_zero_of_le_zero
  unfold prfHmacKindFinishC
  simp only [Comp.queries, Nat.zero_add]
  erw [compRename_queries]
  exact le_trans hm (by omega)

private theorem size_liftPrimComp_hm :
    ∀ {Γ t} (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t),
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle) c).size = c.size
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.size,
      size_liftPrimComp_hm m, size_liftPrimComp_hm k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.size,
      size_liftPrimComp_hm t, size_liftPrimComp_hm e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, Comp.size,
      size_liftPrimComp_hm b]

private theorem litSize_liftPrimComp_hm :
    ∀ {Γ t} (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ t),
      AtomicLift.compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle) c) = AtomicLift.compLitSize c
  | _, _, .ret _ | _, _, .sample _ _ | _, _, .query _ _ => rfl
  | _, _, .bind m k => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, AtomicLift.compLitSize,
      litSize_liftPrimComp_hm m, litSize_liftPrimComp_hm k]
  | _, _, .ite _ t e | _, _, .caseOpt _ t e | _, _, .caseSum _ t e => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, AtomicLift.compLitSize,
      litSize_liftPrimComp_hm t, litSize_liftPrimComp_hm e]
  | _, _, .iter _ _ b | _, _, .findM _ _ b | _, _, .anyM _ _ b | _, _, .mapM _ _ b
  | _, _, .consumeFirstM _ _ b _ | _, _, .foldM _ _ _ b => by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp, AtomicLift.compLitSize,
      litSize_liftPrimComp_hm b]

section HmSize

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (initPrin1KeyFixedB initPrinFixedB corruptFixedB genSpkFixedB genOpkFixedB registerFixedB
   fhstSetBase buMk u32OfNat emptyAuthHybridStFixedE emptyAuthHybridStE emptyAuthStE emptyAuthSlotStE
   ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots ahsfMk ahsfMkSlots ahsfUpd assMk
   ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions ahsMk ahsUpd
   asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
   asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
   asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
   asRoCache asRootRoCache asAdvKeys stMk stUpd
   peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted peMk peUpd
   sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk sbMk oeOpkSk oeOpkPk oeConsumed oeMk oeUpd
   pkbIkB pkbSpkId pkbSpkB pkbOpkB? pkbPqspkId pkbPqspkB hdMk pmMk seMk ikrMk iasMk
   aNone aInitPrin aPk aCorr aBundle aSendFresh aSendUnfresh encEC encKEM
   natEq natLt nat2Eq nat3Eq boolOr isSomeE optFst optSnd eLet2 v
   bindV letV caseOptV caseSumV eLet eCaseOpt eCaseSum eFind eAny eMap
   litB catB bytesCons widenB takeKB bytesLen bytesBeq bytesVarint
   samplePrim sampleChal queryPrim Ext authHybridStateFixedTy RSF liftPrimComp sendQTy recvQTy authRespTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (hmInitC hmFinishC hmPostC encPostC finishIntC hmContX0E hmPreTy
   macInputE etmBodyE etmBody24E pendFilterE pendHitE dedupE
   emptyMuE queryHmacEval muKeys muChal muPend muBad muMk muKeyIdEq natLe bytesTake bytesDrop
   ipUEntry ipPeer ipFim ipFresh ipIdeal ipMsgPlain ipT3 ipKeys6 ipDrKey
   ipRks4 ipSalt ipPqMsg ipAd ipProv ipRoC ipRootC mapMV bits_firstMsgHdrLen)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (getDBytes defaultMsgKeysE defaultMsgKeys_cipherKey_length
   defaultMsgKeys_macKey_length defaultMsgKeys_iv_length)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (avlHeightCap)

set_option linter.unusedSimpArgs false in
local macro "hm_leaf_sz" : tactic => `(tactic| (
  simp (config := { maxSteps := 500000 }) only [
    hmInitC, hmFinishC, hmPostRunC, hmPostC, encPostC, finishIntC, hmContX0E,
    macInputE, etmBodyE, etmBody24E, pendFilterE, pendHitE, dedupE, defaultMsgKeysE,
    emptyMuE, queryHmacEval, muKeys, muChal, muPend, muBad, muMk, muKeyIdEq, natLe,
    bytesTake, bytesDrop, getDBytes,
    initPrin1KeyFixedB, initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, registerFixedB,
    fhstSetBase, buMk, u32OfNat, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE, emptyAuthSlotStE,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMk, ahsfMkSlots, ahsfUpd, assMk,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, sbMk, oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    pkbIkB, pkbSpkId, pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB,
    ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey,
    ipRks4, ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC, hdMk, pmMk, seMk, ikrMk, iasMk,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, encEC, encKEM,
    natEq, natLt, nat2Eq, nat3Eq, boolOr, isSomeE, optFst, optSnd, eLet2, v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, caseSumV, mapMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint,
    samplePrim, sampleChal, queryPrim,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.mapBoundedM,
    size_liftPrimComp_hm, litSize_liftPrimComp_hm,
    Comp.size, Expr.size, AtomicLift.compLitSize, AtomicLift.exprLitSize, AtomicLift.pqOpLitSize,
    bits_firstMsgHdrLen,
    defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
    List.length_nil, List.length_cons, List.length_replicate,
    Nat.add_zero, Nat.zero_add, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  try dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have : bits 0 = 1 := by decide
  have : bits 1 = 1 := by decide
  have : bits 8 = 4 := by decide
  have : bits 24 = 5 := by decide
  have : bits 32 = 6 := by decide
  have : bits 158 = 8 := by decide
  omega))

private theorem liftPrfHmac1_size_le {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps
      _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) :
    (liftPrfHmac1 c e).size ≤ 10 * c.size + AtomicLift.compLitSize c + e.size + 2 := by
  have hm := mapComp_size_le tlPrfHmac tlPrfHmac_sizeLe c
  unfold liftPrfHmac1; simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left ((compRename_size _ _).le.trans hm) _) 1) ?_
  omega

private theorem letC_size_step {ι : Type} {T : _root_.OracleSpec ι}
    {I : _root_.ReductionDsl.Iface _root_.SignalPqxdh.LegacyCosted.pqSig T}
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig} {Γ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Γ a)
    (body : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps I (a :: Γ) r) {B : ℕ} (hb : body.size ≤ B) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC e body).size ≤ e.size + B + 2 := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.size]; omega

private theorem letC_litSize_step {ι : Type} {T : _root_.OracleSpec ι}
    {I : _root_.ReductionDsl.Iface _root_.SignalPqxdh.LegacyCosted.pqSig T}
    {a r : Ty _root_.SignalPqxdh.LegacyCosted.pqSig} {Γ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps Γ a)
    (body : Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps I (a :: Γ) r)
    {B : ℕ} (hb : AtomicLift.compLitSize body ≤ B) :
    AtomicLift.compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC e body) ≤
      AtomicLift.exprLitSize e + B := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, AtomicLift.compLitSize]; omega

set_option linter.unusedSimpArgs false in
private theorem hmLeaf_sizes (S : Setup) (F : AuthKindFuels) :
    (hmInitC S).size ≤ 300 ∧ AtomicLift.compLitSize (hmInitC S) ≤ 50 ∧
    (hmFinishC F.K_on).size ≤ 600 + 10 * bits F.K_on ∧
    AtomicLift.compLitSize (hmFinishC F.K_on) ≤ 200 ∧
    (∀ {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
      (jt : _root_.ReductionDsl.Var Δ .nat) (pre : _root_.ReductionDsl.Var Δ hmPreTy),
      (hmPostRunC F.K_on jt pre).size ≤ 1200 + 10 * bits F.K_on ∧
      AtomicLift.compLitSize (hmPostRunC F.K_on jt pre) ≤ 600) := by
  refine ⟨by hm_leaf_sz, by hm_leaf_sz, by hm_leaf_sz, by hm_leaf_sz, fun jt pre => ⟨by hm_leaf_sz, by hm_leaf_sz⟩⟩

private theorem hmBaseArmC_size_le (S : Setup) (F : AuthKindFuels)
    {arg : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      _root_.ReductionDsl.Var Γ₁ authHybridStateFixedTy → _root_.ReductionDsl.Var Γ₂ arg →
      Comp _root_.SignalPqxdh.LegacyCosted.pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Δ RSF)
    {Γ : List (Ty pqAtomicSig)}
    (hs : (step (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)).size ≤
      2000 + 10 * bits F.K_on)
    (hl : AtomicLift.compLitSize (step
      (Δ := [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg])
      (.zero : _root_.ReductionDsl.Var [authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)
      (.zero : _root_.ReductionDsl.Var [arg, authHybridStateFixedTy, .prod authHybridStateFixedTy arg] _)) ≤ 300) :
    (hmBaseArmC S step (Γ := Γ)).size ≤ 21000 + 100 * bits F.K_on := by
  have hm := liftPrfHmac1_size_le
    (liftPrimComp (letV (.fst (.var .zero)) fun fhst => letV (.snd (.var (.succ .zero))) fun x => step fhst x))
    (.pair (.fst (.snd (.fst .v1))) .v0 : Expr pqAtomicOps (embedTy arg :: .prod (embedTy hmStTy) roBothAvlTy :: Γ) _)
  have hs' : (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle)
      (letV (.fst (.var .zero)) fun fhst => letV (.snd (.var (.succ .zero))) fun x => step fhst x) :
      Comp _ _ [.prod authHybridStateFixedTy arg] _).size ≤ 2010 + 10 * bits F.K_on := by
    rw [size_liftPrimComp_hm]; dsimp only [letV]
    refine le_trans (letC_size_step _ _ (letC_size_step _ _ hs)) ?_; simp only [Expr.size]; omega
  have hl' : AtomicLift.compLitSize (liftPrimComp (C := _root_.SignalPqxdh.LegacyCosted.hmacPrfOracle)
      (letV (.fst (.var .zero)) fun fhst => letV (.snd (.var (.succ .zero))) fun x => step fhst x) :
      Comp _ _ [.prod authHybridStateFixedTy arg] _) ≤ 300 := by
    rw [litSize_liftPrimComp_hm]; dsimp only [letV]
    refine le_trans (letC_litSize_step _ _ (letC_litSize_step _ _ hl)) ?_
    simp only [AtomicLift.exprLitSize]; omega
  unfold hmBaseArmC; simp only [Comp.size]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add hm (le_refl _)) 1) ?_
  simp only [hmRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

theorem prfHmac1KeyKindProg_size_le (S : Setup) (b : QueryBudget) :
    (prfHmac1KeyKindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  let F := AuthKindFuels.ofBudget S b
  obtain ⟨hInitS, hInitL, hFinS, hFinL, hPostSL⟩ := hmLeaf_sizes S F
  rcases ofBudget_size_bits S b with ⟨hbOn, hbRo, _, _, _, _, hbAvl⟩
  have heSz : (emptyRoBothAvlE (Γ := [embedTy (.prod .unit hmStTy), .unit])).size ≤ 500 :=
    emptyRoBothAvlE_size_le
  have haSz : (aNoneAtomicE (Γ := [.unit, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q])).size ≤ 30 := by
    exact (by decide : (aNoneAtomicE (Γ := [])).size ≤ 30)
  have hInit : (prfHmacKindInitC S).size ≤ 4000 := by
    have hm := mapComp_size_le tlPrfHmac tlPrfHmac_sizeLe (hmInitC S)
    unfold prfHmacKindInitC; simp only [Comp.size]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add hm (le_refl _)) 1) ?_
    simp only [Expr.size, Expr.v0]; omega
  have hFin : (prfHmacKindFinishC F).size ≤ 6500 + 100 * bits F.K_on := by
    have hm := mapComp_size_le tlPrfHmac tlPrfHmac_sizeLe (hmFinishC F.K_on)
    unfold prfHmacKindFinishC; simp only [Comp.size]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left ((compRename_size _ _).le.trans hm) _) 1) ?_
    simp only [Expr.size, Expr.v0]; omega
  have hSend : ∀ opk : Bool,
      (.bind (liftPrfHmac1
          (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
           letV (.snd (.snd (v s))) fun mst =>
           bindV (liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
           hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0)))) (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
        Comp pqAtomicOps pqPrfHmacIface [authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy))).size ≤
      200000 + 500 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := fun opk => by
    obtain ⟨hPS, hPL⟩ := hPostSL (.succ (.succ (.succ .zero)) : _root_.ReductionDsl.Var _ .nat) .zero
    have hm := liftPrfHmac1_size_le
      (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
       letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
       letV (.snd (.snd (v s))) fun mst =>
       bindV (liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
       hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero : Comp _ _ [.prod hmStTy sendQTy] _)
      (.pair (.fst .v1) .v0 : Expr pqAtomicOps [authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _)
    have hcS : (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
        letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
        letV (.snd (.snd (v s))) fun mst =>
        bindV (liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
        hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero :
        Comp _ _ [.prod hmStTy sendQTy] _).size ≤ 16300 + 50 * bits F.K_on + 10 * bits F.K_ro := by
      dsimp only [letV, bindV]
      refine le_trans (letC_size_step _ _ (letC_size_step _ _ (letC_size_step _ _ (letC_size_step _ _ (letC_size_step _ _
        (by simp only [Comp.size, size_liftPrimComp_hm]
            exact Nat.add_le_add_right (Nat.add_le_add (hmSendKC_size_le S F.K_on F.K_ro opk _ _ _ _) hPS) 1)))))) ?_
      simp only [v, Expr.size]; omega
    have hcL : AtomicLift.compLitSize (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
        letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
        letV (.snd (.snd (v s))) fun mst =>
        bindV (liftPrimComp (hmSendKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
        hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero : Comp _ _ [.prod hmStTy sendQTy] _) ≤ 5600 := by
      dsimp only [letV, bindV]
      refine le_trans (letC_litSize_step _ _ (letC_litSize_step _ _ (letC_litSize_step _ _ (letC_litSize_step _ _ (letC_litSize_step _ _
        (by simp only [AtomicLift.compLitSize, litSize_liftPrimComp_hm]
            exact Nat.add_le_add (hmSendKC_litSize_le S F.K_on F.K_ro opk _ _ _ _) hPL)))))) ?_
      simp only [v, AtomicLift.exprLitSize]; omega
    have hr1 : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod authRespTy hmStTy), authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).size ≤ 30 :=
      (by decide : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps [embedTy (.prod authRespTy hmStTy)] _))))).size ≤ 30)
    have hr2 : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod authRespTy hmStTy), authSendQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).size ≤ 30 :=
      (by decide : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps [embedTy (.prod authRespTy hmStTy)] _))))).size ≤ 30)
    simp only [Comp.size]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add hm
      (Nat.add_le_add_right (Nat.add_le_add (AuthCoreKCostBase.syncRoBothC_size_le F.K_cap _ _ _) (le_refl _)) 1)) 1) ?_
    simp only [Expr.size, Expr.v0, Expr.v1, Expr.v2] at hm hr1 hr2 ⊢; omega
  have hRecv : ∀ opk : Bool,
      (.bind (liftPrfHmac1
          (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
           letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
           letV (.snd (.snd (v s))) fun mst =>
           bindV (liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
           hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
          (.pair (.fst .v1) .v0))
        (.bind (syncRoBothC F.K_cap (fixedRoCacheE (.fst (.snd (.snd .v0))))
            (fixedRootRoCacheE (.fst (.snd (.snd .v0)))) (.snd .v2))
          (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0)))) :
        Comp pqAtomicOps pqPrfHmacIface [authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
          (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy))).size ≤
      200000 + 500 * bits F.K_on + 100 * bits F.K_ro + 4 * bits (avlHeightCap F.K_cap) := fun opk => by
    obtain ⟨hPS, hPL⟩ := hPostSL (.succ (.succ (.succ .zero)) : _root_.ReductionDsl.Var _ .nat) .zero
    have hm := liftPrfHmac1_size_le
      (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
       letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
       letV (.snd (.snd (v s))) fun mst =>
       bindV (liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
       hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero : Comp _ _ [.prod hmStTy recvQTy] _)
      (.pair (.fst .v1) .v0 : Expr pqAtomicOps [authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _)
    have hcS : (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
        letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
        letV (.snd (.snd (v s))) fun mst =>
        bindV (liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
        hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero :
        Comp _ _ [.prod hmStTy recvQTy] _).size ≤ 17300 + 50 * bits F.K_on + 10 * bits F.K_ro := by
      dsimp only [letV, bindV]
      refine le_trans (letC_size_step _ _ (letC_size_step _ _ (letC_size_step _ _ (letC_size_step _ _ (letC_size_step _ _
        (by simp only [Comp.size, size_liftPrimComp_hm]
            exact Nat.add_le_add_right (Nat.add_le_add (hmRecvKC_size_le S F.K_on F.K_ro opk _ _ _ _) hPS) 1)))))) ?_
      simp only [v, Expr.size]; omega
    have hcL : AtomicLift.compLitSize (letV (.fst (.var .zero)) fun s => letV (.snd (.var (.succ .zero))) fun x =>
        letV (.fst (v s)) fun jt => letV (.fst (.snd (v s))) fun fhst =>
        letV (.snd (.snd (v s))) fun mst =>
        bindV (liftPrimComp (hmRecvKC S F.K_on F.K_ro opk jt fhst mst x)) fun _pre =>
        hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero : Comp _ _ [.prod hmStTy recvQTy] _) ≤ 5600 := by
      dsimp only [letV, bindV]
      refine le_trans (letC_litSize_step _ _ (letC_litSize_step _ _ (letC_litSize_step _ _ (letC_litSize_step _ _ (letC_litSize_step _ _
        (by simp only [AtomicLift.compLitSize, litSize_liftPrimComp_hm]
            exact Nat.add_le_add (hmRecvKC_litSize_le S F.K_on F.K_ro opk _ _ _ _) hPL)))))) ?_
      simp only [v, AtomicLift.exprLitSize]; omega
    have hr1 : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod authRespTy hmStTy), authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).size ≤ 30 :=
      (by decide : (fixedRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps [embedTy (.prod authRespTy hmStTy)] _))))).size ≤ 30)
    have hr2 : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps
        [embedTy (.prod authRespTy hmStTy), authRecvQAtomicTy, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q] _))))).size ≤ 30 :=
      (by decide : (fixedRootRoCacheE (.fst (.snd (.snd (.v0 : Expr pqAtomicOps [embedTy (.prod authRespTy hmStTy)] _))))).size ≤ 30)
    simp only [Comp.size]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add hm
      (Nat.add_le_add_right (Nat.add_le_add (AuthCoreKCostBase.syncRoBothC_size_le F.K_cap _ _ _) (le_refl _)) 1)) 1) ?_
    simp only [Expr.size, Expr.v0, Expr.v1, Expr.v2] at hm hr1 hr2 ⊢; omega
  have hHandle : (prfHmacKindHandleC S F).size ≤
      920000 + 2500 * bits F.K_on + 400 * bits F.K_ro + 20 * bits (avlHeightCap F.K_cap) := by
    unfold prfHmacKindHandleC; dsimp only
    exact dispatchAuthQ_size_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ (b0 := 1) (by rfl)
      (hmBaseArmC_size_le S F (fun fhst u => AuthCoreK.initPrin1KeyFixedKB F fhst u)
        (le_trans (initPrin1KeyFixedKB_size_le F _ _) (by omega))
        (le_trans (initPrin1KeyFixedKB_litSize_le F _ _) (by omega)))
      (hmBaseArmC_size_le S F (fun fhst u => AuthCoreK.corruptFixedKB F fhst u)
        (le_trans (corruptFixedKB_size_le F _ _) (by omega))
        (le_trans (corruptFixedKB_litSize_le F _ _) (by omega)))
      (hmBaseArmC_size_le S F (fun fhst x => AuthCoreK.genSpkFixedKB F fhst x)
        (le_trans (genSpkFixedKB_size_le F _ _) (by omega))
        (le_trans (genSpkFixedKB_litSize_le F _ _) (by omega)))
      (hmBaseArmC_size_le S F (fun fhst x => AuthCoreK.genOpkFixedKB F fhst x)
        (le_trans (genOpkFixedKB_size_le F _ _) (by omega))
        (le_trans (genOpkFixedKB_litSize_le F _ _) (by omega)))
      (hSend true) (hSend false) (hRecv true) (hRecv false)
      (b9 := 2600 + 2 * bits (avlHeightCap F.K_cap))
      (by simp only [Comp.size]
          refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
            (AuthCoreKCostBase.roFixedShadowArmC_size_le aiPrfHmac F.K_cap _ _) _) 1) ?_
          simp only [hmRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega)
      (b10 := 2600 + 2 * bits (avlHeightCap F.K_cap))
      (by simp only [Comp.size]
          refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
            (AuthCoreKCostBase.roRootFixedShadowArmC_size_le aiPrfHmac F.K_cap _ _) _) 1) ?_
          simp only [hmRebuildE, Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega)
      (b11 := 40)
      (by simp only [Comp.size]
          refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add haSz (le_refl _)) 1) 1) ?_
          simp only [Expr.size, Expr.v1]; omega)
      (hmBaseArmC_size_le S F (fun fhst sk => AuthCoreK.registerFixedKB fhst sk)
        (le_trans (registerFixedKB_size_le F _ _) (by omega))
        (le_trans (registerFixedKB_litSize_le _ _) (by omega)))
      (by omega)
  have hB : reductionSizeBudget = 2 ^ 24 := rfl
  unfold prfHmac1KeyKindProg _root_.ReductionDsl.CostedReduction.size
  dsimp only [F] at *; rw [hB]; omega

end HmSize

end PrfHmacBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost
