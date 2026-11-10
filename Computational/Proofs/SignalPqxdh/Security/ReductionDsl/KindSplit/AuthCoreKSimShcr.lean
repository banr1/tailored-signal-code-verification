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

/-!
# Two-Stage Forgetful Simulation for `AuthHandshakeShCr`

Proves `TwoStageForgetSim` between the kind-split shadow-indexed reduction
`shcrAuth1KeyKindProg` and the reference atomic reduction `shcrOldAtomicProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimShcr

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open Computational.Proofs.ReductionDsl.StepSimTwoStage (TwoStageForgetSim forgetPreOut)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedCtx embedEnv mapComp
   comp_queries_zero_of_zero mapComp_eval liftAuthHandle_eval
   aiAuthPrim tlAuthPrim)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery authSpec)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy preKeyBundleTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext shcrStTy pauseTy
   stRo stRoot stAdv isAdvRegC koskSenderOkC hkdfOrRoC rootRoC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy authBaseShadowStTy forgetAuthBaseShadow emptyRoBothAvlE)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (shcrAuth1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv
   AuthBaseValOnlineBounded AuthBaseAtomOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache
   RoBothShadowRel CacheStepAtMostOne
   authShcrShadowStTy forgetShcr shcrOldAtomicProg
   AuthBaseShadowAt shcrShadowBase AuthShcrShadowAt
   AuthShcrInv AuthShcrPauseInv dispatchAuthQEval dispatchAuthQ_eval_qenc)

private theorem bumpPred_online_slots {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    bumpPred (authSimPred S) c t 0 = c 0 + 1 ∧
    bumpPred (authSimPred S) c t 1 = c 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bumpPred, hOn]
  · simp [bumpPred, hNotRo]
  · simp [bumpPred, hNotRt]

private theorem bumpPred_ro_slots {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hNotOn : ¬ authSimPred S 0 t)
    (hRo : authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    bumpPred (authSimPred S) c t 0 = c 0 ∧
    bumpPred (authSimPred S) c t 1 = c 1 + 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bumpPred, hNotOn]
  · simp [bumpPred, hRo]
  · simp [bumpPred, hNotRt]

private theorem bumpPred_roRoot_slots {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S)
    (hNotOn : ¬ authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hRt : authSimPred S 2 t) :
    bumpPred (authSimPred S) c t 0 = c 0 ∧
    bumpPred (authSimPred S) c t 1 = c 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bumpPred, hNotOn]
  · simp [bumpPred, hNotRo]
  · simp [bumpPred, hRt]

private theorem AuthShcrShadowAt.mono {S : Setup} {b : QueryBudget}
    {nOn nOn' nRo nRo' nRoot nRoot' : ℕ}
    (hOn : nOn ≤ nOn') (hRo : nRo ≤ nRo') (hRt : nRoot ≤ nRoot')
    {s' : authShcrShadowStTy.denote}
    (h : AuthShcrShadowAt S b nOn nRo nRoot s') :
    AuthShcrShadowAt S b nOn' nRo' nRoot' s' :=
  ⟨h.base_ok.mono hOn hRo hRt, Nat.le_trans h.ir_le hOn, Nat.le_trans h.rr_le hOn⟩

private theorem shcr_pauseInv_of_online {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {t : AuthQuery S} {p' : (embedTy pauseTy).denote} {s' : authShcrShadowStTy.denote}
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t)
    (hroom : ∀ j : Fin 4, authSimPred S j t → c j + 1 ≤ authSimBounds b j) :
    AuthShcrPauseInv S b (bumpPred (authSimPred S) c t) p' s' := by
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c t hOn hNotRo hNotRt
  refine ⟨hInv.counter_inv.bump t hroom, ?_, ?_, trivial⟩
  · omega
  · have hsub : bumpPred (authSimPred S) c t 0 - 1 = c 0 := by omega
    rw [hsub, hc1, hc2]
    exact hInv.shadow_ok

private theorem pause_counter_bounds (S : Setup) (b : QueryBudget) {c : Fin 4 → ℕ}
    (hCnt : AuthCounterInv b c) (hOne : 1 ≤ c 0) :
    let F := AuthKindFuels.ofBudget S b
    (c 0 - 1) + 1 = c 0 ∧
    c 0 ≤ F.K_on ∧
    c 0 ≤ b.q_total ∧
    c 0 + c 1 ≤ F.K_ro ∧
    c 0 + c 2 ≤ F.K_ro ∧
    F.K_ro ≤ b.q_total ∧
    F.K_ro ≤ F.K_cap := by
  have := hCnt.on_le
  have := hCnt.ro_le
  have := hCnt.roRoot_le
  have := hCnt.tot_le
  have := hCnt.sum_eq
  dsimp only [AuthKindFuels.ofBudget]
  omega

private def projEnv : {Γ : List (Ty pqSig)} → Env (embedCtx Γ) → Env Γ
  | [], .nil => .nil
  | t :: _, .cons y ρ => .cons (projVal t y) (projEnv ρ)

private theorem embedEnv_projEnv :
    ∀ {Γ : List (Ty pqSig)} (ρ : Env (embedCtx Γ)), embedEnv (projEnv ρ) = ρ
  | [], .nil => rfl
  | t :: _, .cons y ρ => by
    simp [projEnv, embedEnv, embedEnv_projEnv ρ]

private theorem tlAuthPrim_unsupported_zero :
    ∀ g, tlAuthPrim.unsupportedW g = 0 := fun _ => rfl

private theorem mapComp_tlAuthPrim_eval_embed {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env Γ) :
    (mapComp tlAuthPrim c).eval (embedEnv ρ) = embedVal t <$> c.eval ρ :=
  mapComp_eval tlAuthPrim c (comp_queries_zero_of_zero tlAuthPrim_unsupported_zero c) ρ

private theorem mapComp_tlAuthPrim_eval {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env (embedCtx Γ)) :
    (mapComp tlAuthPrim c).eval ρ = embedVal t <$> c.eval (projEnv ρ) := by
  conv_lhs => rw [← embedEnv_projEnv ρ]
  exact mapComp_tlAuthPrim_eval_embed c (projEnv ρ)

private theorem mapComp_tlAuthPrim_congr {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c₁ c₂ : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env (embedCtx Γ))
    (h : c₁.eval (projEnv ρ) = c₂.eval (projEnv ρ)) :
    (mapComp tlAuthPrim c₁).eval ρ = (mapComp tlAuthPrim c₂).eval ρ := by
  rw [mapComp_tlAuthPrim_eval, mapComp_tlAuthPrim_eval, h]

private theorem mem_support_mapComp_tlAuthPrim {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env (embedCtx Γ)) (y : (embedTy t).denote)
    (hy : y ∈ support ((mapComp tlAuthPrim c).eval ρ)) :
    ∃ x ∈ support (c.eval (projEnv ρ)), y = embedVal t x := by
  rw [mapComp_tlAuthPrim_eval] at hy
  simp only [support_map, Set.mem_image] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

private theorem atomRoCache_embedVal (st : authStateTy.denote) :
    atomRoCache (embedVal authStateTy st) = valRoCache st := by
  change List.map (embedVal (.prod (B 192) _)) (valRoCache st) = valRoCache st
  have hid : embedVal (.prod (B 192) (.prod (B 32) (.prod (B 32) (B 32)))) = id := by
    funext ⟨k, a, b, c⟩
    rfl
  simp [hid]

private theorem atomRootRoCache_embedVal (st : authStateTy.denote) :
    atomRootRoCache (embedVal authStateTy st) = valRootRoCache st := by
  change List.map (embedVal (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))
    (valRootRoCache st) = valRootRoCache st
  have hid : embedVal (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))) = id := by
    funext ⟨⟨k1, k2⟩, v1, v2⟩
    rfl
  simp [hid]

private theorem take_eq_of_length_le {α : Type} {l : List α} {K Q : ℕ}
    (hK : l.length ≤ K) (hQ : l.length ≤ Q) :
    l.take K = l.take Q := by
  rw [List.take_of_length_le hK, List.take_of_length_le hQ]

private theorem take_min_eq_of_length_le {α : Type} {l : List α} {K Q N : ℕ}
    (hL : l.length ≤ K) (hKQ : K ≤ Q) :
    l.take (min K N) = l.take (min Q N) := by
  by_cases hKN : K ≤ N
  · rw [Nat.min_eq_left hKN, List.take_of_length_le hL]
    by_cases hQN : Q ≤ N
    · rw [Nat.min_eq_left hQN, List.take_of_length_le (Nat.le_trans hL hKQ)]
    · have hKLN : l.length ≤ min Q N := by omega
      exact (List.take_of_length_le hKLN).symm
  · have h1 : min K N = N := by omega
    have h2 : min Q N = N := by omega
    rw [h1, h2]

private theorem hs_letV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e k).eval ρ =
      (k .zero).eval (.cons (e.eval ρ) ρ) := by
  simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV,
    Comp.letC, Comp.eval]

private theorem hs_bindV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m k).eval ρ =
      (m.eval ρ >>= fun x => (k .zero).eval (.cons x ρ)) :=
  rfl

private theorem hs_caseOptV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o kn ks).eval ρ =
      match o.eval ρ with
      | none => kn.eval ρ
      | some x => (ks .zero).eval (.cons x ρ) := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV, Comp.eval]
  cases o.eval ρ <;> rfl

private theorem hs_eFind_eq {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (ρ : Env Γ)
    (hK : (xs.eval ρ).length ≤ K) (hQ : (xs.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind K xs p).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind Q xs p).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind,
    Expr.findBounded, Expr.eval, take_eq_of_length_le hK hQ]

private theorem hs_eAny_eq {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (ρ : Env Γ)
    (hK : (xs.eval ρ).length ≤ K) (hQ : (xs.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eAny K xs p).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eAny Q xs p).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eAny,
    Expr.anyBounded, Expr.eval, take_eq_of_length_le hK hQ]

private theorem hs_eMap_eq {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (K Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (ρ : Env Γ)
    (hK : (xs.eval ρ).length ≤ K) (hQ : (xs.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eMap K xs f).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eMap Q xs f).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eMap,
    Expr.mapBounded, Expr.eval, take_eq_of_length_le hK hQ]

private theorem isAdvRegC_hs_fuel_eq (K Q : ℕ) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hK : n ≤ K) (hKQ : K ≤ Q) :
    (isAdvRegC K st pk).eval env = (isAdvRegC Q st pk).eval env := by
  have hlenK : (env.get (h.wk st)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.length ≤ K :=
    Nat.le_trans hb.advKeys_le hK
  have hlenQ : (env.get (h.wk st)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.length ≤ Q :=
    Nat.le_trans hlenK hKQ
  unfold isAdvRegC
  rw [hs_bindV_eval, hs_bindV_eval]
  congr 1; funext p
  simp only [Comp.eval]
  have hAdv : (stAdv (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v st)).eval
      (Env.cons p env) = (env.get (h.wk st)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 := rfl
  rw [hs_eAny_eq K Q _ _ (Env.cons p env) (by rw [hAdv]; exact hlenK) (by rw [hAdv]; exact hlenQ)]

private theorem koskSenderOkC_hs_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (koskSenderOkC S (AuthKindFuels.ofBudget S b).K_on st ik).eval env =
      (koskSenderOkC S b.q_total st ik).eval env := by
  have hKQ := AuthKindFuels.K_on_le_q_total S b
  unfold koskSenderOkC
  rw [hs_letV_eval, hs_letV_eval]
  rw [hs_bindV_eval, hs_bindV_eval,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.findHonestC_fuel_eq
      S b st _ (Env.cons (ik.eval env) env) hb hn]
  congr 1; funext f
  rw [hs_bindV_eval, hs_bindV_eval,
    isAdvRegC_hs_fuel_eq _ _ st _ (Env.cons f (Env.cons (ik.eval env) env)) hb hn hKQ]

private theorem hkdfOrRoC_fuel_eq (K Q : ℕ) (useRo : Bool)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hK : (valRoCache (env.get (h.wk st))).length ≤ K)
    (hQ : (valRoCache (env.get (h.wk st))).length ≤ Q) :
    (hkdfOrRoC K useRo st sec).eval env = (hkdfOrRoC Q useRo st sec).eval env := by
  unfold hkdfOrRoC
  rw [hs_letV_eval, hs_letV_eval]
  cases useRo with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    have hRo : (stRo (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v st)).eval
        (Env.cons (sec.eval env) env) = valRoCache (env.get (h.wk st)) := rfl
    rw [hs_caseOptV_eval, hs_caseOptV_eval,
      hs_eFind_eq K Q _ _ (Env.cons (sec.eval env) env)
        (by rw [hRo]; exact hK) (by rw [hRo]; exact hQ)]

private theorem hkdfOrRoC_step (K : ℕ) (useRo : Bool)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hK : (valRoCache (env.get (h.wk st))).length ≤ K) :
    ∀ out ∈ support ((hkdfOrRoC K useRo st sec).eval env),
      CacheStepAtMostOne (valRoCache (env.get (h.wk st))) out.2 := by
  intro out hout
  unfold hkdfOrRoC at hout
  rw [hs_letV_eval] at hout
  set l := valRoCache (env.get (h.wk st))
  set k := sec.eval env
  cases useRo with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hout
    rw [hs_bindV_eval] at hout
    simp only [Comp.eval, Expr.eval, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hout
    rcases hout with ⟨dk, _, rfl⟩
    exact CacheStepAtMostOne.refl l
  | true =>
    simp only [↓reduceIte] at hout
    rw [hs_caseOptV_eval] at hout
    have hfind : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind K
        (stRo (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v st))
        (fun e => Expr.bytesBeq (.fst (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v e))
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v
            (Var.zero : Var (B 192 :: Δ) (B 192))))).eval
          (Env.cons k env) =
        l.find? (fun p => p.1 == k) := by
      change List.find? (fun p => p.1 == k) (List.take K l) = l.find? (fun p => p.1 == k)
      rw [List.take_of_length_le hK]
    rw [hfind] at hout
    cases hopt : l.find? (fun p => p.1 == k) with
    | none =>
      rw [hopt] at hout
      rw [hs_bindV_eval] at hout
      simp only [Comp.eval, Expr.eval, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] at hout
      rcases hout with ⟨dk, _, rfl⟩
      exact Or.inr ⟨k, dk, Option.isNone_iff_eq_none.mpr hopt, rfl⟩
    | some kv =>
      rw [hopt] at hout
      simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact CacheStepAtMostOne.refl l

private theorem rootRoC_hs_fuel_eq (K Q : ℕ)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hK : (valRootRoCache (env.get (h.wk st))).length ≤ K)
    (hQ : (valRootRoCache (env.get (h.wk st))).length ≤ Q) :
    (rootRoC K st rk dh).eval env = (rootRoC Q st rk dh).eval env := by
  unfold rootRoC
  rw [hs_letV_eval, hs_letV_eval, hs_caseOptV_eval, hs_caseOptV_eval]
  have hRt : (stRoot (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v st)).eval
      (Env.cons ((rk.pair dh).eval env) env) = valRootRoCache (env.get (h.wk st)) := rfl
  rw [hs_eFind_eq K Q _ _ (Env.cons ((rk.pair dh).eval env) env)
    (by rw [hRt]; exact hK) (by rw [hRt]; exact hQ)]

private theorem rootRoC_hs_step (K : ℕ)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hK : (valRootRoCache (env.get (h.wk st))).length ≤ K) :
    ∀ out ∈ support ((rootRoC K st rk dh).eval env),
      CacheStepAtMostOne (valRootRoCache (env.get (h.wk st))) out.2 := by
  intro out hout
  unfold rootRoC at hout
  rw [hs_letV_eval, hs_caseOptV_eval] at hout
  set l := valRootRoCache (env.get (h.wk st))
  set k : (Ty.prod (B 32) (B 32)).denote := (rk.eval env, dh.eval env)
  have hfind : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind K
        (stRoot (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v st))
        (fun e => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bytes2Eq
          (.fst (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v e))
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v
            (Var.zero : Var (.prod (B 32) (B 32) :: Δ) (.prod (B 32) (B 32)))))).eval
          (Env.cons ((rk.pair dh).eval env) env) =
      l.find? (fun p => p.1 == k) := by
    change List.find? (fun p => (p.1.1 == rk.eval env && p.1.2 == dh.eval env)) (List.take K l) =
      l.find? (fun p => p.1 == k)
    rw [List.take_of_length_le hK]
    exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine.pair32_find?_beq_eq
      l (rk.eval env) (dh.eval env)
  rw [hfind] at hout
  cases hopt : l.find? (fun p => p.1 == k) with
  | none =>
    rw [hopt] at hout
    rw [hs_bindV_eval] at hout
    simp only [hs_bindV_eval, Comp.eval, Expr.eval, Expr.listCons, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨rk1, _, ck1, _, rfl⟩
    exact Or.inr ⟨k, (rk1, ck1), Option.isNone_iff_eq_none.mpr hopt, rfl⟩
  | some kv =>
    rw [hopt] at hout
    simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact CacheStepAtMostOne.refl l

private theorem hs_letV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e₁ e₂ : Expr pqxdhOps Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (he : e₁.eval ρ = e₂.eval ρ)
    (hk : ∀ x, (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e₂ k₂).eval ρ := by
  rw [hs_letV_eval, hs_letV_eval, he, hk]

private theorem hs_letV_congr_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e₁ e₂ : Expr pqxdhOps Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (he : e₁.eval ρ = e₂.eval ρ)
    (hk : ∀ x, x = e₁.eval ρ → (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e₂ k₂).eval ρ := by
  rw [hs_letV_eval, hs_letV_eval, ← he]
  exact hk (e₁.eval ρ) rfl

private theorem hs_bindV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m₁ m₂ : Comp pqxdhOps I Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (hm : m₁.eval ρ = m₂.eval ρ)
    (hk : ∀ x, (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m₂ k₂).eval ρ := by
  rw [hs_bindV_eval, hs_bindV_eval, hm]
  congr 1; funext x; exact hk x

private theorem hs_ite_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    {c₁ c₂ : Expr pqxdhOps Γ .bool} {t₁ t₂ f₁ f₂ : Comp pqxdhOps I Γ τ} {ρ : Env Γ}
    (hc : c₁.eval ρ = c₂.eval ρ) (ht : t₁.eval ρ = t₂.eval ρ) (hf : f₁.eval ρ = f₂.eval ρ) :
    (Comp.ite c₁ t₁ f₁).eval ρ = (Comp.ite c₂ t₂ f₂).eval ρ := by
  simp only [Comp.eval, hc, ht, hf]

private theorem hs_caseOptV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {o₁ o₂ : Expr pqxdhOps Γ (.opt τ₁)} {kn₁ kn₂ : Comp pqxdhOps I Γ τ₂}
    {ks₁ ks₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (ho : o₁.eval ρ = o₂.eval ρ) (hkn : kn₁.eval ρ = kn₂.eval ρ)
    (hks : ∀ x, (ks₁ .zero).eval (.cons x ρ) = (ks₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o₁ kn₁ ks₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o₂ kn₂ ks₂).eval ρ := by
  rw [hs_caseOptV_eval, hs_caseOptV_eval, ho]
  cases o₂.eval ρ with
  | none => exact hkn
  | some x => exact hks x

private theorem support_hs_letV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e : Expr pqxdhOps Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x, x = e.eval ρ → ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e k).eval ρ), P y := by
  intro y hy; rw [hs_letV_eval] at hy; exact h (e.eval ρ) rfl y hy

private theorem support_hs_letV_any {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e : Expr pqxdhOps Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x, ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e k).eval ρ), P y :=
  support_hs_letV fun x _ => h x

private theorem support_hs_bindV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m : Comp pqxdhOps I Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x ∈ support (m.eval ρ), ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m k).eval ρ), P y := by
  intro y hy; simp only [hs_bindV_eval, support_bind, Set.mem_iUnion, exists_prop] at hy
  rcases hy with ⟨x, hx, hy⟩; exact h x hx y hy

private theorem support_hs_bindV_any {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m : Comp pqxdhOps I Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x, ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m k).eval ρ), P y :=
  support_hs_bindV fun x _ => h x

private theorem support_hs_ite {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    {c : Expr pqxdhOps Γ .bool} {t f : Comp pqxdhOps I Γ τ} {ρ : Env Γ} {P : τ.denote → Prop}
    (ht : c.eval ρ = true → ∀ y ∈ support (t.eval ρ), P y)
    (hf : c.eval ρ = false → ∀ y ∈ support (f.eval ρ), P y) :
    ∀ y ∈ support ((Comp.ite c t f).eval ρ), P y := by
  intro y hy; simp only [Comp.eval] at hy
  cases hc : c.eval ρ
  · rw [hc] at hy; exact hf hc y hy
  · rw [hc] at hy; exact ht hc y hy

private theorem support_hs_caseOptV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {o : Expr pqxdhOps Γ (.opt τ₁)} {kn : Comp pqxdhOps I Γ τ₂}
    {ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ} {P : τ₂.denote → Prop}
    (hkn : ∀ y ∈ support (kn.eval ρ), P y)
    (hks : ∀ x, ∀ y ∈ support ((ks .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o kn ks).eval ρ),
      P y := by
  intro y hy; rw [hs_caseOptV_eval] at hy
  cases ho : o.eval ρ
  · rw [ho] at hy; exact hkn y hy
  · rw [ho] at hy; exact hks _ y hy

private theorem support_hs_ret {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig} {e : Expr pqxdhOps Γ τ} {ρ : Env Γ}
    {P : τ.denote → Prop} (h : P (e.eval ρ)) :
    ∀ y ∈ support ((Comp.ret (I := I) e).eval ρ), P y := by
  intro y hy; simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hy; rwa [hy]

private theorem hs_eMap_length_le {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (K : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (ρ : Env Γ) {n : ℕ}
    (hL : (xs.eval ρ).length ≤ n) :
    ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eMap K xs f).eval ρ).length ≤ n := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eMap, Expr.mapBounded, Expr.eval,
    List.length_map, List.length_take]
  exact Nat.le_trans (Nat.min_le_right _ _) hL

private theorem liftAuthPrim1_eval {a r : Ty pqSig} (c : Comp pqxdhOps pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      c e).eval ρ = embedVal r <$> c.eval (.cons (projVal a (e.eval ρ)) .nil) := by
  simp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1,
    Comp.eval, pure_bind]
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval
    (mapComp tlAuthPrim c) _ (.cons (e.eval ρ) .nil) (.cons (e.eval ρ) ρ)
    (fun v => by cases v with | zero => rfl | succ v => nomatch v)]
  rw [mapComp_tlAuthPrim_eval]
  rfl

set_option linter.constructorNameAsVariable false in
private theorem syncShcrShadowRespC_bind_sim {Γ : List (Ty pqAtomicSig)} (cap : ℕ)
    (s' : authShcrShadowStTy.denote)
    (c_leg : Comp pqAtomicOps pqAuthPrimIface Γ
      (.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
             (embedTy shcrStTy)))
    (roBothE : Expr pqAtomicOps
      (.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
             (embedTy shcrStTy) :: Γ) roBothAvlTy)
    (ρ : Env Γ)
    (hRel : RoBothShadowRel cap s'.1.1 s'.2)
    (hBothE : ∀ rs, roBothE.eval (.cons rs ρ) = s'.2)
    (hStep : ∀ rs ∈ support (c_leg.eval ρ),
      CacheStepAtMostOne (atomRoCache s'.1.1) (atomRoCache rs.2.1) ∧
      CacheStepAtMostOne (atomRootRoCache s'.1.1) (atomRootRoCache rs.2.1) ∧
      (atomRoCache rs.2.1).length ≤ cap ∧
      (atomRootRoCache rs.2.1).length ≤ cap) :
    let synced := Comp.bind c_leg
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
        cap .v0 roBothE)
    Prod.map id forgetShcr <$> synced.eval ρ = c_leg.eval ρ ∧
    ∀ p ∈ support (synced.eval ρ),
      ∃ rs ∈ support (c_leg.eval ρ), p.1 = rs.1 ∧ p.2.1 = rs.2 ∧
        RoBothShadowRel cap p.2.1.1 p.2.2 := by
  have hEach : ∀ rs ∈ support (c_leg.eval ρ),
      ∃ avls' : roBothAvlTy.denote,
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          cap .v0 roBothE).eval (.cons rs ρ) = pure (rs.1, (rs.2, avls')) ∧
        RoBothShadowRel cap rs.2.1 avls' := by
    intro rs hrs
    rcases hStep rs hrs with ⟨hRoS, hRtS, hRoC, hRtC⟩
    simp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC,
      Comp.eval, pure_bind]
    have hSub : ((Expr.v0.pair roBothE).eval (.cons rs ρ)) = (rs, s'.2) := by
      simp [Expr.eval, Expr.v0, Env.get, hBothE rs]
    rw [hSub]
    obtain ⟨avls', hSyncEval, hRel'⟩ :=
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.syncRoBothC_sim
        (I := pqAuthPrimIface) cap s'.1.1 rs.2.1 s'.2
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.baseRoCacheE
          (.fst (.snd (.fst .v0))))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.baseRootRoCacheE
          (.fst (.snd (.fst .v0))))
        (.snd .v0)
        (.cons (rs, s'.2) (.cons rs ρ))
        hRel hRoS hRtS hRoC hRtC rfl rfl rfl
    rw [hSyncEval, pure_bind]
    exact ⟨avls', rfl, hRel'⟩
  constructor
  · dsimp only [Comp.eval]
    rw [map_bind]
    conv_rhs => rw [← bind_pure (c_leg.eval ρ)]
    refine OracleComp.bind_congr_of_forall_mem_support (c_leg.eval ρ) fun rs hrs => ?_
    obtain ⟨avls', hEval, _⟩ := hEach rs hrs
    rw [hEval]
    rfl
  · intro p hp
    dsimp only [Comp.eval] at hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨rs, hrs, hp'⟩
    obtain ⟨avls', hEval, hRel'⟩ := hEach rs hrs
    rw [hEval, support_pure, Set.mem_singleton_iff] at hp'
    subst hp'
    exact ⟨rs, hrs, rfl, rfl, hRel'⟩

private theorem emptyAuthSt_online_ro (secb : Bool) :
    let st : authStateTy.denote :=
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.emptyAuthStE
        (.var .zero : Expr pqxdhOps [.bool] .bool)).eval (.cons secb .nil)
    AuthBaseValOnlineBounded 0 st ∧ valRoCache st = [] ∧ valRootRoCache st = [] := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩ <;>
    simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.emptyAuthStE,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk, Expr.eval]

private theorem shcr_hInit (S : Setup) (b : QueryBudget)
    (x : ((PB 1568).prod (PB 3168)).denote) :
    Prod.map id forgetShcr <$> (shcrAuth1KeyKindProg S b).init.eval (.cons x .nil) =
      (shcrOldAtomicProg S b).init.eval (.cons x .nil) ∧
    ∀ as' ∈ support ((shcrAuth1KeyKindProg S b).init.eval (.cons x .nil)),
      AuthShcrInv S b 0 as'.2 := by
  let F := AuthKindFuels.ofBudget S b
  have hInitDef :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S F.K_on F.K_on).init =
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S b.q_total b.q_total).init :=
    rfl
  dsimp only [shcrAuth1KeyKindProg, shcrOldAtomicProg,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindInitC,
    Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key,
    Comp.eval]
  rw [hInitDef]
  set mInit := (mapComp tlAuthPrim
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S b.q_total b.q_total).init).eval
    (.cons x .nil)
  constructor
  · rw [map_bind]
    conv_rhs => rw [← bind_pure mInit]
    exact OracleComp.bind_congr_of_forall_mem_support mInit fun _ _ => rfl
  · intro as' has'
    erw [mem_support_bind_iff] at has'
    rcases has' with ⟨us, hus, has'⟩
    simp only [Expr.eval, Env.get, Expr.v0, support_pure, Set.mem_singleton_iff] at has'
    subst has'
    obtain ⟨v, hv, rfl⟩ := mem_support_mapComp_tlAuthPrim (Γ := [.prod (B 1568) (B 3168)])
      (t := .prod .unit shcrStTy)
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S b.q_total b.q_total).init
      (.cons x .nil) us hus
    have hvProps :
        AuthBaseValOnlineBounded 0 v.2.1 ∧
        valRoCache v.2.1 = [] ∧
        valRootRoCache v.2.1 = [] ∧
        v.2.2.2.2.2.2.1 = [] ∧
        v.2.2.2.2.2.2.2.1 = [] := by
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg] at hv
      split_ifs at hv
      · rw [hs_bindV_eval] at hv
        simp only [Comp.eval, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hv
        rcases hv with ⟨secb, _, rfl⟩
        obtain ⟨hOn, hRo, hRt⟩ := emptyAuthSt_online_ro secb
        exact ⟨hOn, hRo, hRt, rfl, rfl⟩
      · rw [hs_bindV_eval] at hv
        simp only [hs_bindV_eval, Comp.eval, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hv
        rcases hv with ⟨uIdx, _, jIdx, _, sIdx, _, secb, _, rfl⟩
        obtain ⟨hOn, hRo, hRt⟩ := emptyAuthSt_online_ro secb
        exact ⟨hOn, hRo, hRt, rfl, rfl⟩
    rcases hvProps with ⟨hOn, hRo, hRt, hIR, hRR⟩
    have hAtomOn : AuthBaseAtomOnlineBounded 0 (embedVal authStateTy v.2.1) :=
      (AuthBaseAtomOnlineBounded.iff_embedVal v.2.1).mpr hOn
    have hAtomRo : atomRoCache (embedVal authStateTy v.2.1) = [] :=
      (atomRoCache_embedVal v.2.1).trans hRo
    have hAtomRt : atomRootRoCache (embedVal authStateTy v.2.1) = [] :=
      (atomRootRoCache_embedVal v.2.1).trans hRt
    refine ⟨AuthCounterInv.zero b, ⟨⟨hAtomOn, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · change (atomRoCache (embedVal authStateTy v.2.1)).length ≤ 0
      rw [hAtomRo]; exact Nat.le_refl 0
    · change (atomRootRoCache (embedVal authStateTy v.2.1)).length ≤ 0
      rw [hAtomRt]; exact Nat.le_refl 0
    · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.emptyRoBothAvlE_roBothShadowRel
        F.K_cap (embedVal authStateTy v.2.1) _ hAtomRo hAtomRt
    · simp [shcrStTy, embedVal, hIR]
    · simp [shcrStTy, embedVal, hRR]

private theorem shcr_hChDone (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (bOut : Ty.bool.denote)
    (_hc : ∀ j, c j ≤ authSimBounds b j) (_hInv : AuthShcrInv S b c s') :
    (shcrAuth1KeyKindProg S b).chDone.eval (.cons s' (.cons bOut .nil)) =
      (shcrOldAtomicProg S b).chDone.eval (.cons (forgetShcr s') (.cons bOut .nil)) := by
  simp only [shcrAuth1KeyKindProg, shcrOldAtomicProg, forgetShcr,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindChDoneC,
    Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key,
    Comp.eval, Expr.eval, Env.get, Expr.v0, pure_bind]
  exact Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval
    (mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S b.q_total b.q_total).chDone)
    (fun {a} => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.dropShadow1)
    (.cons s'.1 (.cons bOut .nil)) (.cons s'.1 (.cons s' (.cons bOut .nil)))
    (fun v => by cases v with | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v)

private theorem shcr_hFinish (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (bOut : Ty.bool.denote)
    (y : ((PB 32).prod (PB 1568)).denote)
    (_hc : ∀ j, c j ≤ authSimBounds b j) (hInv : AuthShcrInv S b c s') :
    (shcrAuth1KeyKindProg S b).finish.eval (.cons s' (.cons bOut (.cons y .nil))) =
      (shcrOldAtomicProg S b).finish.eval (.cons (forgetShcr s') (.cons bOut (.cons y .nil))) := by
  let F := AuthKindFuels.ofBudget S b
  simp only [shcrAuth1KeyKindProg, shcrOldAtomicProg, forgetShcr,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindFinishC,
    Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg,
    Comp.eval, Expr.eval, Env.get, Expr.v0, pure_bind]
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval
    (mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrExtractC
        (Γ₁ := [.prod (B 32) (B 1568)]) (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
        (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) F.K_on .vz .vz))
    (fun {a} => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.dropShadow1)
    (.cons s'.1 (.cons bOut (.cons y .nil)))
    (.cons s'.1 (.cons s' (.cons bOut (.cons y .nil))))
    (fun v => by
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => cases v with
          | zero => rfl
          | succ v => nomatch v)]
  let ρFin : Env (embedCtx [shcrStTy, .bool, .prod (B 32) (B 1568)]) :=
    .cons s'.1 (.cons bOut (.cons y .nil))
  refine mapComp_tlAuthPrim_congr _ _ ρFin ?_
  have hc0 : c 0 ≤ F.K_on := by
    have := hInv.counter_inv.on_le
    dsimp [F, AuthKindFuels.ofBudget]
    omega
  have hRR : ((projEnv ρFin).get .zero).2.2.2.2.2.2.1.length ≤ c 0 := by
    have hEq : ((projEnv ρFin).get .zero).2.2.2.2.2.2.1.length = s'.1.2.2.2.2.2.2.1.length :=
      List.length_map _
    rw [hEq]
    exact hInv.shadow_ok.rr_le
  exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.shcrExtractC_fuel_eq
    S b .vz .vz (projEnv ρFin) hRR hc0

set_option maxRecDepth 4096 in
private theorem shcrFinishSendKC_fuel_eq (K_on K_ro Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hOnK : n ≤ K_on) (hOnQ : n ≤ Q)
    (hRoK : (valRoCache (env.get (h₁.wk st))).length ≤ K_ro)
    (hRoQ : (valRoCache (env.get (h₁.wk st))).length ≤ Q)
    (hRtK : (valRootRoCache (env.get (h₁.wk st))).length ≤ K_ro)
    (hRtQ : (valRootRoCache (env.get (h₁.wk st))).length ≤ Q) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrFinishSendKC
      K_on K_ro st d ks sc).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC Q st d ks sc).eval env := by
  have hSpkK : (env.get (h₁.wk st)).2.2.2.1.length ≤ K_on :=
    Nat.le_trans hb.spkBundles_le hOnK
  have hSpkQ : (env.get (h₁.wk st)).2.2.2.1.length ≤ Q :=
    Nat.le_trans hb.spkBundles_le hOnQ
  unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrFinishSendKC
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC
  refine hs_letV_congr rfl fun sid => hs_letV_congr rfl fun bu =>
    hs_letV_congr rfl fun m0 => hs_letV_congr rfl fun m1 =>
    hs_letV_congr rfl fun uE => hs_letV_congr rfl fun pp =>
    hs_letV_congr rfl fun pt => hs_letV_congr rfl fun ekSk =>
    hs_letV_congr rfl fun ephSk => hs_letV_congr rfl fun spqrCoins =>
    hs_letV_congr rfl fun fresh =>
    hs_bindV_congr rfl fun ekPk => hs_bindV_congr rfl fun dh1 =>
    hs_bindV_congr rfl fun dh2 => hs_bindV_congr rfl fun dh3 =>
    hs_bindV_congr rfl fun dh4 =>
    hs_bindV_congr (hkdfOrRoC_fuel_eq K_ro Q true st _ _ hRoK hRoQ) fun dr =>
    hs_bindV_congr rfl fun ephPk => hs_bindV_congr rfl fun dhR =>
    hs_bindV_congr (rootRoC_hs_fuel_eq K_ro Q st _ _ _ hRtK hRtQ) fun rkOut =>
    hs_bindV_congr rfl fun mkSeed => hs_bindV_congr rfl fun ck11 =>
    hs_bindV_congr rfl fun sp? =>
    hs_caseOptV_congr rfl rfl fun sp =>
    hs_bindV_congr rfl fun mk => hs_letV_congr rfl fun ad =>
    hs_bindV_congr rfl fun ct => hs_letV_congr rfl fun wm =>
    hs_letV_congr ?_ fun hon =>
    hs_letV_congr rfl fun se => rfl
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt, Expr.eval]
  cases pp with
  | none => rfl
  | some _ =>
    exact Prod.ext (hs_eAny_eq K_on Q _ _ _ hSpkK hSpkQ) (hs_eAny_eq K_on Q _ _ _ hSpkK hSpkQ)

private theorem finishC_preserves (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hRoQ : (valRoCache (env.get (h₁.wk st))).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk st))).length ≤ Q) :
    ∀ out ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC Q st d ks sc).eval env),
      match out.2 with
      | none => True
      | some b' =>
          AuthBaseValOnlineBounded (n + 1) b' ∧
          CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) (valRoCache b') ∧
          CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st))) (valRootRoCache b') := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC
  refine support_hs_letV_any fun sid => support_hs_letV_any fun bu =>
    support_hs_letV_any fun m0 => support_hs_letV_any fun m1 =>
    support_hs_letV_any fun uE => support_hs_letV_any fun pp =>
    support_hs_letV_any fun pt => support_hs_letV_any fun ekSk =>
    support_hs_letV_any fun ephSk => support_hs_letV_any fun spqrCoins =>
    support_hs_letV_any fun fresh => ?_
  refine support_hs_bindV_any fun ekPk => support_hs_bindV_any fun dh1 =>
    support_hs_bindV_any fun dh2 => support_hs_bindV_any fun dh3 =>
    support_hs_bindV_any fun dh4 => ?_
  refine support_hs_bindV fun dr hdr => ?_
  let ρ16 := Env.cons dh4 (Env.cons dh3 (Env.cons dh2 (Env.cons dh1 (Env.cons ekPk
    (Env.cons fresh (Env.cons spqrCoins (Env.cons ephSk (Env.cons ekSk (Env.cons pt
      (Env.cons pp (Env.cons uE (Env.cons m1 (Env.cons m0 (Env.cons bu
        (Env.cons sid env)))))))))))))))
  have hdrStep : CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) dr.2 :=
    hkdfOrRoC_step Q true st _ ρ16 hRoQ dr hdr
  refine support_hs_bindV_any fun ephPk => support_hs_bindV_any fun dhR => ?_
  refine support_hs_bindV fun rkOut hrk => ?_
  let ρ19 := Env.cons dhR (Env.cons ephPk (Env.cons dr ρ16))
  have hrkStep : CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st))) rkOut.2 :=
    rootRoC_hs_step Q st _ _ ρ19 hRtQ rkOut hrk
  refine support_hs_bindV_any fun mkSeed => support_hs_bindV_any fun ck11 =>
    support_hs_bindV_any fun sp? => ?_
  refine support_hs_caseOptV ?_ fun sp => ?_
  · refine support_hs_ret ?_
    trivial
  · refine support_hs_bindV_any fun mk => support_hs_letV_any fun ad =>
      support_hs_bindV_any fun ct => support_hs_letV_any fun wm =>
      support_hs_letV_any fun hon => support_hs_letV_any fun se => ?_
    refine support_hs_ret ?_
    let ρ29 := Env.cons se (Env.cons hon (Env.cons wm (Env.cons ct (Env.cons ad
      (Env.cons mk (Env.cons sp (Env.cons sp? (Env.cons ck11 (Env.cons mkSeed
        (Env.cons rkOut ρ19))))))))))
    have hPairSnd {α β : Ty pqSig} {Δ' : List (Ty pqSig)} (x : Expr pqxdhOps Δ' α)
        (y : Expr pqxdhOps Δ' (.opt β)) (ρ : Env Δ') :
        ((Expr.pair x y).eval ρ).2 = y.eval ρ := rfl
    have hSt : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v st).eval ρ29 =
        env.get (h₁.wk st) := rfl
    rw [hPairSnd]
    simp only [Expr.eval]
    rw [hSt]
    exact ⟨{ principals_le        := Nat.le_succ_of_le hb.principals_le
             spkBundles_le        := Nat.le_succ_of_le hb.spkBundles_le
             opkEntries_le        := Nat.le_succ_of_le hb.opkEntries_le
             sessions_le          := Nat.succ_le_succ hb.sessions_le
             usedSendSessions_le  := Nat.succ_le_succ hb.usedSendSessions_le
             usedRecvOPK_le       := Nat.le_succ_of_le hb.usedRecvOPK_le
             usedRecvNoOPK_le     := Nat.le_succ_of_le hb.usedRecvNoOPK_le
             seenKyberBaseKeys_le := Nat.le_succ_of_le hb.seenKyberBaseKeys_le
             sentOPKEvents_le     := Nat.le_succ_of_le hb.sentOPKEvents_le
             sentNoOPKEvents_le   := Nat.le_succ_of_le hb.sentNoOPKEvents_le
             recvdOPKEvents_le    := Nat.le_succ_of_le hb.recvdOPKEvents_le
             recvdNoOPKEvents_le  := Nat.le_succ_of_le hb.recvdNoOPKEvents_le
             advKeys_le           := Nat.le_succ_of_le hb.advKeys_le },
           hdrStep, hrkStep⟩




private theorem ext_step_wk {Γ Δ : List (Ty pqSig)} {σ τ : Ty pqSig} [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (σ := σ) (Γ := Γ) (Δ := Δ)).wk x = .succ (h.wk x) := rfl

private theorem ext_refl_wk {Γ : List (Ty pqSig)} {τ : Ty pqSig} (x : Var Γ τ) :
    (Ext.refl (Γ := Γ)).wk x = x := rfl

private theorem env_cons_get_succ {Δ : List (Ty pqSig)} {σ τ : Ty pqSig}
    (val : σ.denote) (ρ : Env Δ) (x : Var Δ τ) :
    (Env.cons val ρ).get (.succ x) = ρ.get x := rfl

private theorem env_cons_get_zero {Δ : List (Ty pqSig)} {τ : Ty pqSig}
    (val : τ.denote) (ρ : Env Δ) :
    (Env.cons val ρ).get .zero = val := rfl

private theorem shcrResumeKC_fuel_eq (K_on1 K_ro Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₃.wk s)).1)
    (hOnK : n ≤ K_on1) (hOnQ : n ≤ Q)
    (hRoK : (valRoCache (env.get (h₃.wk s)).1).length ≤ K_ro)
    (hRoQ : (valRoCache (env.get (h₃.wk s)).1).length ≤ Q)
    (hRtK : (valRootRoCache (env.get (h₃.wk s)).1).length ≤ K_ro)
    (hRtQ : (valRootRoCache (env.get (h₃.wk s)).1).length ≤ Q) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrResumeKC
      K_on1 K_ro sc d s).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC Q sc d s).eval env := by
  unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrResumeKC
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC
  refine hs_letV_congr_eq rfl fun st hst =>
    hs_bindV_congr rfl fun ekSk =>
    hs_bindV_congr rfl fun ephSk =>
    hs_bindV_congr rfl fun spqrCoins =>
    hs_letV_congr rfl fun ks =>
    hs_bindV_congr ?_ fun out => rfl
  have hst' : st = (env.get (h₃.wk s)).1 := hst
  exact shcrFinishSendKC_fuel_eq K_on1 K_ro Q Var.zero d Var.zero sc _
    (by exact hst' ▸ hb) hOnK hOnQ
    (by exact hst' ▸ hRoK) (by exact hst' ▸ hRoQ)
    (by exact hst' ▸ hRtK) (by exact hst' ▸ hRtQ)

private theorem shcrResumeC_preserves (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₃.wk s)).1)
    (hRoQ : (valRoCache (env.get (h₃.wk s)).1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₃.wk s)).1).length ≤ Q)
    (hIR : (env.get (h₃.wk s)).2.2.2.2.2.1.length ≤ n)
    (hRR : (env.get (h₃.wk s)).2.2.2.2.2.2.1.length ≤ n) :
    ∀ rs ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC Q sc d s).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2.1 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₃.wk s)).1) (valRoCache rs.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₃.wk s)).1) (valRootRoCache rs.2.1) ∧
      (rs.2).2.2.2.2.2.1.length ≤ n + 1 ∧
      (rs.2).2.2.2.2.2.2.1.length ≤ n + 1 := by
  set s0 := env.get (h₃.wk s)
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC
  refine support_hs_letV fun st hst =>
    support_hs_bindV_any fun ekSk =>
    support_hs_bindV_any fun ephSk =>
    support_hs_bindV_any fun spqrCoins =>
    support_hs_letV_any fun ks =>
    support_hs_bindV fun out hout => ?_
  have hst' : st = s0.1 := hst
  have hFin := finishC_preserves Q Var.zero d Var.zero sc _
    (by exact hst' ▸ hb) (by exact hst' ▸ hRoQ) (by exact hst' ▸ hRtQ) out hout
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrFinC
  refine support_hs_bindV fun r hr => support_hs_ret ?_
  rw [hs_letV_eval, hs_caseOptV_eval] at hr
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Comp.eval, Expr.eval,
    ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero] at hr ⊢
  cases hopt : out.2 with
  | none =>
    rw [hopt] at hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hb.mono (Nat.le_succ n), CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _,
      Nat.le_trans hIR (Nat.le_succ n), Nat.le_trans hRR (Nat.le_succ n)⟩
  | some b' =>
    rw [hopt] at hr hFin
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rcases hFin with ⟨hb', hRoS, hRtS⟩
    exact ⟨hb', hst' ▸ hRoS, hst' ▸ hRtS,
      Nat.succ_le_succ hIR, Nat.le_trans hRR (Nat.le_succ n)⟩

private abbrev scTy : Ty pqSig := .prod (B 32) (B 1568)

private theorem hs_letV_congr2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Γ' : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e₁ : Expr pqxdhOps Γ τ₁} {e₂ : Expr pqxdhOps Γ' τ₁}
    {k₁ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {k₂ : Var (τ₁ :: Γ') τ₁ → Comp pqxdhOps I (τ₁ :: Γ') τ₂}
    {ρ : Env Γ} {ρ' : Env Γ'}
    (he : e₁.eval ρ = e₂.eval ρ')
    (hk : ∀ x, (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ')) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV e₂ k₂).eval ρ' := by
  rw [hs_letV_eval, hs_letV_eval, he, hk]

private theorem hs_bindV_congr2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Γ' : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m₁ : Comp pqxdhOps I Γ τ₁} {m₂ : Comp pqxdhOps I Γ' τ₁}
    {k₁ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {k₂ : Var (τ₁ :: Γ') τ₁ → Comp pqxdhOps I (τ₁ :: Γ') τ₂}
    {ρ : Env Γ} {ρ' : Env Γ'}
    (hm : m₁.eval ρ = m₂.eval ρ')
    (hk : ∀ x, (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ')) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV m₂ k₂).eval ρ' := by
  rw [hs_bindV_eval, hs_bindV_eval, hm]
  congr 1; funext x; exact hk x

private theorem hs_caseOptV_congr2 {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Γ' : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {o₁ : Expr pqxdhOps Γ (.opt τ₁)} {o₂ : Expr pqxdhOps Γ' (.opt τ₁)}
    {kn₁ : Comp pqxdhOps I Γ τ₂} {kn₂ : Comp pqxdhOps I Γ' τ₂}
    {ks₁ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ks₂ : Var (τ₁ :: Γ') τ₁ → Comp pqxdhOps I (τ₁ :: Γ') τ₂}
    {ρ : Env Γ} {ρ' : Env Γ'}
    (ho : o₁.eval ρ = o₂.eval ρ') (hkn : kn₁.eval ρ = kn₂.eval ρ')
    (hks : ∀ x, (ks₁ .zero).eval (.cons x ρ) = (ks₂ .zero).eval (.cons x ρ')) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o₁ kn₁ ks₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o₂ kn₂ ks₂).eval ρ' := by
  rw [hs_caseOptV_eval, hs_caseOptV_eval, ho]
  cases o₂.eval ρ' with
  | none => exact hkn
  | some x => exact hks x

private theorem hkdfOrRoC_eval_congr (K : ℕ) (useRo : Bool)
    {Γ Δ Γ' Δ' : List (Ty pqSig)}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (st' : Var Γ' authStateTy) [h' : Ext Γ' Δ'] (sec' : Expr pqxdhOps Δ' (B 192)) (env' : Env Δ')
    (hst : env.get (h.wk st) = env'.get (h'.wk st'))
    (hsec : sec.eval env = sec'.eval env') :
    (hkdfOrRoC K useRo st sec).eval env = (hkdfOrRoC K useRo st' sec').eval env' := by
  unfold hkdfOrRoC
  refine hs_letV_congr2 hsec fun k => ?_
  cases useRo with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine hs_bindV_congr2 rfl fun dk => ?_
    simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
      ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero, hst]
  | true =>
    simp only [↓reduceIte]
    refine hs_caseOptV_congr2 ?_ ?_ fun kv => ?_
    · simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, ext_refl_wk, env_cons_get_succ, hst]
      congr 1
    · refine hs_bindV_congr2 rfl fun dk => ?_
      simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero, hst]
    · simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, env_cons_get_succ, hst]
      rfl

private theorem rootRoC_eval_congr (K : ℕ)
    {Γ Δ Γ' Δ' : List (Ty pqSig)}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (st' : Var Γ' authStateTy) [h' : Ext Γ' Δ'] (rk' dh' : Expr pqxdhOps Δ' (B 32)) (env' : Env Δ')
    (hst : env.get (h.wk st) = env'.get (h'.wk st'))
    (hrk : rk.eval env = rk'.eval env') (hdh : dh.eval env = dh'.eval env') :
    (rootRoC K st rk dh).eval env = (rootRoC K st' rk' dh').eval env' := by
  unfold rootRoC
  refine hs_letV_congr2 (Prod.ext hrk hdh) fun k => hs_caseOptV_congr2 ?_ ?_ fun kv => ?_
  · simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
      ext_step_wk, ext_refl_wk, env_cons_get_succ, hst]
    congr 1
  · refine hs_bindV_congr2 rfl fun rk1 => hs_bindV_congr2 rfl fun ck1 => ?_
    simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
      ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero, hst]
  · simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
      ext_step_wk, env_cons_get_succ, hst]
    rfl

private theorem finishC_eval_congr (Q : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ Γ₁' Γ₂' Γ₃' Γ₄' Δ' : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32)))) (sc : Var Γ₄ scTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (st' : Var Γ₁' authStateTy) (d' : Var Γ₂' pauseTy)
    (ks' : Var Γ₃' (.prod (B 32) (.prod (B 32) (B 32)))) (sc' : Var Γ₄' scTy)
    [h₁' : Ext Γ₁' Δ'] [h₂' : Ext Γ₂' Δ'] [h₃' : Ext Γ₃' Δ'] [h₄' : Ext Γ₄' Δ'] (env' : Env Δ')
    (hst : env.get (h₁.wk st) = env'.get (h₁'.wk st'))
    (hd  : env.get (h₂.wk d)  = env'.get (h₂'.wk d'))
    (hks : env.get (h₃.wk ks) = env'.get (h₃'.wk ks'))
    (hsc : env.get (h₄.wk sc) = env'.get (h₄'.wk sc')) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC Q st d ks sc).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC Q st' d' ks' sc').eval env' := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.finishC
  refine hs_letV_congr2 (congrArg (fun x => x.1) hd) fun sid =>
    hs_letV_congr2 (congrArg (fun x => x.2.1) hd) fun bu =>
    hs_letV_congr2 (congrArg (fun x => x.2.2.1.1) hd) fun m0 =>
    hs_letV_congr2 (congrArg (fun x => x.2.2.1.2) hd) fun m1 =>
    hs_letV_congr2 (congrArg (fun x => x.2.2.2.1) hd) fun uE =>
    hs_letV_congr2 (congrArg (fun x => x.2.2.2.2.1) hd) fun pp =>
    hs_letV_congr2 (congrArg (fun x => x.2.2.2.2.2) hd) fun pt =>
    hs_letV_congr2 (congrArg (fun x => x.1) hks) fun ekSk =>
    hs_letV_congr2 (congrArg (fun x => x.2.1) hks) fun ephSk =>
    hs_letV_congr2 (congrArg (fun x => x.2.2) hks) fun spqrCoins =>
    hs_letV_congr2 rfl fun fresh =>
    hs_bindV_congr2 rfl fun ekPk => hs_bindV_congr2 rfl fun dh1 =>
    hs_bindV_congr2 rfl fun dh2 => hs_bindV_congr2 rfl fun dh3 =>
    hs_bindV_congr2 rfl fun dh4 =>
    hs_bindV_congr2 (by
      apply hkdfOrRoC_eval_congr
      · simp only [ext_step_wk, env_cons_get_succ]; exact hst
      · simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.buildSecretsE_eval,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
          ext_step_wk, env_cons_get_succ, hsc]
        rfl) fun dr =>
    hs_bindV_congr2 rfl fun ephPk => hs_bindV_congr2 rfl fun dhR =>
    hs_bindV_congr2 (by
      apply rootRoC_eval_congr
      · simp only [ext_step_wk, env_cons_get_succ]; exact hst
      · rfl
      · rfl) fun rkOut =>
    hs_bindV_congr2 rfl fun mkSeed => hs_bindV_congr2 rfl fun ck11 =>
    hs_bindV_congr2 rfl fun sp? =>
    hs_caseOptV_congr2 rfl rfl fun sp =>
    hs_bindV_congr2 rfl fun mk => hs_letV_congr2 rfl fun ad =>
    hs_bindV_congr2 rfl fun ct =>
    hs_letV_congr2 (by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, env_cons_get_succ, hsc]
      rfl) fun wm =>
    hs_letV_congr2 (by
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval]
      cases pp with
      | none => rfl
      | some p =>
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eAny,
          Expr.eval, ext_step_wk, env_cons_get_succ, hst]
        refine Prod.ext ?_ ?_ <;> congr 1) fun hon =>
    hs_letV_congr2 rfl fun se => ?_
  simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
    ext_step_wk, env_cons_get_succ, hst]
  rfl

private theorem shcrResumeC_eval_congr (Q : ℕ)
    {Γ₁ Γ₂ Γ₃ Δ Γ₁' Γ₂' Γ₃' Δ' : List (Ty pqSig)}
    (sc : Var Γ₁ scTy) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (sc' : Var Γ₁' scTy) (d' : Var Γ₂' pauseTy) (s' : Var Γ₃' shcrStTy)
    [h₁' : Ext Γ₁' Δ'] [h₂' : Ext Γ₂' Δ'] [h₃' : Ext Γ₃' Δ'] (env' : Env Δ')
    (hsc : env.get (h₁.wk sc) = env'.get (h₁'.wk sc'))
    (hd  : env.get (h₂.wk d)  = env'.get (h₂'.wk d'))
    (hs  : env.get (h₃.wk s)  = env'.get (h₃'.wk s')) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC Q sc d s).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC Q sc' d' s').eval env' := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC
  refine hs_letV_congr2 (congrArg (fun x => x.1) hs) fun st =>
    hs_bindV_congr2 rfl fun ekSk =>
    hs_bindV_congr2 rfl fun ephSk =>
    hs_bindV_congr2 rfl fun spqrCoins =>
    hs_letV_congr2 rfl fun ks =>
    hs_bindV_congr2 (by
      apply finishC_eval_congr
      · rfl
      · simp only [ext_step_wk, env_cons_get_succ]; exact hd
      · rfl
      · simp only [ext_step_wk, env_cons_get_succ]; exact hsc) fun out => ?_
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrFinC
  refine hs_bindV_congr2 ?_ fun r => ?_
  · refine hs_letV_congr2 (by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, env_cons_get_succ, hd]) fun sp => ?_
    refine hs_caseOptV_congr2 rfl ?_ fun b' => ?_
    · simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero, hs]
    · simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
        ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero, hs, hsc]
  · simp only [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval,
      ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero, hd]

private theorem shcr_hResume (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (p' : (embedTy pauseTy).denote) (s' : authShcrShadowStTy.denote)
    (y : ((PB 32).prod (PB 1568)).denote)
    (hc : ∀ j, c j ≤ authSimBounds b j) (hPause : AuthShcrPauseInv S b c p' s') :
    Prod.map id forgetShcr <$>
        (shcrAuth1KeyKindProg S b).resume.eval (.cons s' (.cons p' (.cons y .nil))) =
      (shcrOldAtomicProg S b).resume.eval (.cons (forgetShcr s') (.cons p' (.cons y .nil))) ∧
    ∀ vs' ∈ support ((shcrAuth1KeyKindProg S b).resume.eval (.cons s' (.cons p' (.cons y .nil)))),
      AuthShcrInv S b c vs'.2 := by
  let _ := hc
  let F := AuthKindFuels.ofBudget S b
  obtain ⟨hSub1, hc0On, hc0Q, hcRo, hcRt, hRoQ, hRoCap⟩ :=
    pause_counter_bounds S b hPause.counter_inv hPause.one_le_on
  have hOnK1 : c 0 - 1 ≤ F.K_on1 := by
    dsimp only [F, AuthKindFuels.ofBudget] at hc0On ⊢
    omega
  have hOnQ : c 0 - 1 ≤ b.q_total := by omega
  let scsTy : Ty pqSig := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
  let sL := projVal shcrStTy s'.1
  let pL := projVal pauseTy p'
  let yL := projVal scTy y
  have hs1 : s'.1 = embedVal shcrStTy sL :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy sL.1 := by rw [hs1]; rfl
  have hb : AuthBaseValOnlineBounded (c 0 - 1) sL.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal sL.1).mp
      (hs1_1 ▸ hPause.shadow_pre.base_ok.online_le)
  have hRoLen0 : (valRoCache sL.1).length ≤ (c 0 - 1) + c 1 := by
    have h := hPause.shadow_pre.base_ok.ro_len_le
    change (atomRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRoCache_embedVal] at h
  have hRtLen0 : (valRootRoCache sL.1).length ≤ (c 0 - 1) + c 2 := by
    have h := hPause.shadow_pre.base_ok.root_len_le
    change (atomRootRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRootRoCache_embedVal] at h
  have hIR0 : sL.2.2.2.2.2.1.length ≤ c 0 - 1 := by
    have h := hPause.shadow_pre.ir_le
    have hEq : s'.1.2.2.2.2.2.1.length = sL.2.2.2.2.2.1.length := by
      rw [hs1]; exact List.length_map _
    omega
  have hRR0 : sL.2.2.2.2.2.2.1.length ≤ c 0 - 1 := by
    have h := hPause.shadow_pre.rr_le
    have hEq : s'.1.2.2.2.2.2.2.1.length = sL.2.2.2.2.2.2.1.length := by
      rw [hs1]; exact List.length_map _
    omega
  have hRoK : (valRoCache sL.1).length ≤ F.K_ro := by dsimp only [F]; omega
  have hRoQt : (valRoCache sL.1).length ≤ b.q_total := by omega
  have hRtK : (valRootRoCache sL.1).length ≤ F.K_ro := by dsimp only [F]; omega
  have hRtQt : (valRootRoCache sL.1).length ≤ b.q_total := by omega
  let c_inner : Comp pqxdhOps pqPrimIface [.prod shcrStTy (.prod pauseTy scTy)]
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS :=
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.snd (.var (.succ .zero)))) fun d =>
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV
      (.snd (.snd (.var (.succ (.succ .zero))))) fun sc =>
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrResumeKC
      F.K_on1 F.K_ro sc d s
  let e_arg : Expr pqAtomicOps
      [authShcrShadowStTy, embedTy pauseTy, .prod (PB 32) (PB 1568)]
      (embedTy (.prod shcrStTy (.prod pauseTy scTy))) :=
    .pair (.fst .v0) (.pair .v1 .v2)
  let c_leg : Comp pqAtomicOps pqAuthPrimIface
      [authShcrShadowStTy, embedTy pauseTy, .prod (PB 32) (PB 1568)]
      (embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS) :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      c_inner e_arg
  let ρ : Env [authShcrShadowStTy, embedTy pauseTy, .prod (PB 32) (PB 1568)] :=
    .cons s' (.cons p' (.cons y .nil))
  let ρL : Env [shcrStTy, pauseTy, scTy] := .cons sL (.cons pL (.cons yL .nil))
  let c_ref := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrResumeC b.q_total
    (Γ₁ := [scTy]) (Γ₂ := [pauseTy, scTy]) (Γ₃ := [shcrStTy, pauseTy, scTy])
    (Δ := [shcrStTy, pauseTy, scTy]) .vz .vz .vz
  have hc_leg_eval : c_leg.eval ρ = embedVal scsTy <$> c_ref.eval ρL := by
    rw [liftAuthPrim1_eval]
    have harg : projVal (.prod shcrStTy (.prod pauseTy scTy)) (e_arg.eval ρ) = (sL, (pL, yL)) := rfl
    rw [harg]
    apply congrArg (embedVal scsTy <$> ·)
    dsimp only [c_inner]
    rw [hs_letV_eval, hs_letV_eval, hs_letV_eval]
    simp only [Expr.eval, env_cons_get_zero, env_cons_get_succ]
    let tup : (Ty.prod shcrStTy (.prod pauseTy scTy)).denote := (sL, (pL, yL))
    rw [shcrResumeKC_fuel_eq F.K_on1 F.K_ro b.q_total
      (Γ₁ := [scTy, pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy scTy)])
      (Γ₂ := [pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy scTy)])
      (Γ₃ := [shcrStTy, .prod shcrStTy (.prod pauseTy scTy)])
      .zero .zero .zero
      (.cons yL (.cons pL (.cons sL (.cons tup .nil))))
      hb hOnK1 hOnQ hRoK hRoQt hRtK hRtQt]
    exact shcrResumeC_eval_congr b.q_total
      (Γ₁ := [scTy, pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy scTy)])
      (Γ₂ := [pauseTy, shcrStTy, .prod shcrStTy (.prod pauseTy scTy)])
      (Γ₃ := [shcrStTy, .prod shcrStTy (.prod pauseTy scTy)])
      .zero .zero .zero (.cons yL (.cons pL (.cons sL (.cons tup .nil))))
      (Γ₁' := [scTy]) (Γ₂' := [pauseTy, scTy]) (Γ₃' := [shcrStTy, pauseTy, scTy])
      .vz .vz .vz ρL rfl rfl rfl
  have hOld_eval :
      (shcrOldAtomicProg S b).resume.eval (.cons (forgetShcr s') (.cons p' (.cons y .nil))) =
        embedVal scsTy <$> c_ref.eval ρL := by
    dsimp only [shcrOldAtomicProg, forgetShcr,
      Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg]
    exact mapComp_tlAuthPrim_eval c_ref (.cons s'.1 (.cons p' (.cons y .nil)))
  have hEachL : ∀ rL ∈ support (c_ref.eval ρL),
      AuthBaseValOnlineBounded (c 0) rL.2.1 ∧
      CacheStepAtMostOne (valRoCache sL.1) (valRoCache rL.2.1) ∧
      CacheStepAtMostOne (valRootRoCache sL.1) (valRootRoCache rL.2.1) ∧
      (valRoCache rL.2.1).length ≤ c 0 + c 1 ∧
      (valRootRoCache rL.2.1).length ≤ c 0 + c 2 ∧
      (rL.2).2.2.2.2.2.1.length ≤ c 0 ∧
      (rL.2).2.2.2.2.2.2.1.length ≤ c 0 := by
    intro rL hrL
    obtain ⟨hb1, hRoS, hRtS, hIR1, hRR1⟩ :=
      shcrResumeC_preserves b.q_total
        (Γ₁ := [scTy]) (Γ₂ := [pauseTy, scTy]) (Γ₃ := [shcrStTy, pauseTy, scTy])
        .vz .vz .vz ρL hb hRoQt hRtQt hIR0 hRR0 rL hrL
    rw [hSub1] at hb1 hIR1 hRR1
    change CacheStepAtMostOne (valRoCache sL.1) (valRoCache rL.2.1) at hRoS
    change CacheStepAtMostOne (valRootRoCache sL.1) (valRootRoCache rL.2.1) at hRtS
    have hRoL1 := hRoS.length_le
    have hRtL1 := hRtS.length_le
    exact ⟨hb1, hRoS, hRtS, by omega, by omega, hIR1, hRR1⟩
  have hSync := syncShcrShadowRespC_bind_sim F.K_cap s' c_leg (.snd .v1) ρ
    hPause.shadow_pre.base_ok.ro_shadow (fun _ => rfl) (by
      intro rs hrs
      rw [hc_leg_eval, support_map, Set.mem_image] at hrs
      rcases hrs with ⟨rL, hrL, rfl⟩
      obtain ⟨_, hRoS, hRtS, hRoL, hRtL, _, _⟩ := hEachL rL hrL
      have hRoA0 : atomRoCache s'.1.1 = valRoCache sL.1 := by rw [hs1_1, atomRoCache_embedVal]
      have hRtA0 : atomRootRoCache s'.1.1 = valRootRoCache sL.1 := by
        rw [hs1_1, atomRootRoCache_embedVal]
      have hRoA1 : atomRoCache (embedVal scsTy rL).2.1 = valRoCache rL.2.1 :=
        atomRoCache_embedVal rL.2.1
      have hRtA1 : atomRootRoCache (embedVal scsTy rL).2.1 = valRootRoCache rL.2.1 :=
        atomRootRoCache_embedVal rL.2.1
      rw [hRoA0, hRtA0, hRoA1, hRtA1]
      exact ⟨hRoS, hRtS, by dsimp only [F]; omega, by dsimp only [F]; omega⟩)
  have hKindDef : (shcrAuth1KeyKindProg S b).resume =
      Comp.bind c_leg
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          F.K_cap .v0 (.snd .v1)) := rfl
  rw [hKindDef]
  refine ⟨hSync.1.trans (hc_leg_eval.trans hOld_eval.symm), fun vs' hvs' => ?_⟩
  obtain ⟨rs, hrs, _, hrs2, hRel'⟩ := hSync.2 vs' hvs'
  rw [hc_leg_eval, support_map, Set.mem_image] at hrs
  rcases hrs with ⟨rL, hrL, rfl⟩
  obtain ⟨hb1, _, _, hRoL, hRtL, hIR1, hRR1⟩ := hEachL rL hrL
  have hvs21 : vs'.2.1 = embedVal shcrStTy rL.2 := hrs2
  have hvs211 : vs'.2.1.1 = embedVal authStateTy rL.2.1 := by rw [hvs21]; rfl
  refine ⟨hPause.counter_inv, ⟨⟨?_, ?_, ?_, hRel'⟩, ?_, ?_⟩⟩
  · change AuthBaseAtomOnlineBounded (c 0) vs'.2.1.1
    rw [hvs211]
    exact (AuthBaseAtomOnlineBounded.iff_embedVal rL.2.1).mpr hb1
  · change (atomRoCache vs'.2.1.1).length ≤ c 0 + c 1
    rw [hvs211, atomRoCache_embedVal]
    exact hRoL
  · change (atomRootRoCache vs'.2.1.1).length ≤ c 0 + c 2
    rw [hvs211, atomRootRoCache_embedVal]
    exact hRtL
  · have hEq : vs'.2.1.2.2.2.2.2.1.length = (rL.2).2.2.2.2.2.1.length := by
      rw [hvs21]; exact List.length_map _
    omega
  · have hEq : vs'.2.1.2.2.2.2.2.2.1.length = (rL.2).2.2.2.2.2.2.1.length := by
      rw [hvs21]; exact List.length_map _
    omega


private theorem hs_ext_refl_wk {Γ : List (Ty pqSig)} {τ : Ty pqSig} (x : Var Γ τ) :
    (@Ext.refl Γ).wk x = x := rfl

private theorem hs_ext_step_wk {Γ Δ : List (Ty pqSig)} {σ τ : Ty pqSig} [h : Ext Γ Δ]
    (x : Var Γ τ) : (@Ext.step Γ Δ σ h).wk x = .vs (h.wk x) := rfl

private theorem hs_env_get_zero {Γ : List (Ty pqSig)} {τ : Ty pqSig} (v₀ : τ.denote) (ρ : Env Γ) :
    (Env.cons v₀ ρ).get .vz = v₀ := rfl

private theorem hs_env_get_succ {Γ : List (Ty pqSig)} {σ τ : Ty pqSig} (v₀ : σ.denote)
    (ρ : Env Γ) (x : Var Γ τ) : (Env.cons v₀ ρ).get (.vs x) = ρ.get x := rfl

private theorem hs_kyberCheckE_eq {Γ : List (Ty pqSig)} (K Q : ℕ)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))
    (ρ : Env Γ)
    (hK : (used.eval ρ).length ≤ K) (hQ : (used.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.kyberCheckE K used entry).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.kyberCheckE Q used entry).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.kyberCheckE,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eLet2,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eLet,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eAny,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Expr.anyBounded, Expr.eval, hs_ext_step_wk, hs_ext_refl_wk,
    hs_env_get_succ, hs_env_get_zero, take_eq_of_length_le hK hQ]
  rfl

private theorem bool_ite_snd_len_le {α β : Type} (b : Bool) (x y : α) (u₁ u₂ : List β)
    {n : ℕ} (h₁ : u₁.length ≤ n + 1) (h₂ : u₂.length ≤ n + 1) :
    (if b = true then (x, u₁) else (y, u₂)).2.length ≤ n + 1 := by
  cases b
  · exact h₂
  · exact h₁

private theorem hs_kyberCheckE_snd_len_le {Γ : List (Ty pqSig)} (K : ℕ) {n : ℕ}
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))
    (ρ : Env Γ)
    (hL : (used.eval ρ).length ≤ n) :
    ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.kyberCheckE K used entry).eval ρ).2.length ≤
      n + 1 := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.kyberCheckE
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eLet2
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eLet
  dsimp only [Expr.eval]
  refine bool_ite_snd_len_le _ _ _ _ _ ?_ ?_
  · change (used.eval ρ).length ≤ n + 1
    exact Nat.le_trans hL (Nat.le_succ n)
  · change (entry.eval ρ :: used.eval ρ).length ≤ n + 1
    exact Nat.succ_le_succ hL

private theorem recvTailKC_fuel_eq (S : Setup) (b : QueryBudget) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    (kE : Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.principalEntryTy)
    (bE : Var Γ₄ _root_.SignalPqxdh.Security.ReductionDsl.spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hOnK : n ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRoK : (valRoCache (env.get (h₁.wk st))).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRtK : (valRootRoCache (env.get (h₁.wk st))).length ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.recvTailKC
      S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro opk st x kE bE oSk?).eval env =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvTailC
      S b.q_total opk st x kE bE oSk?).eval env := by
  have hOnQ := AuthKindFuels.K_on_le_q_total S b
  have hRoQ := AuthKindFuels.K_ro_le_q_total S b
  have hKybOn : (env.get (h₁.wk st)).2.2.2.2.2.2.2.2.2.1.length ≤
      (AuthKindFuels.ofBudget S b).K_on := Nat.le_trans hb.seenKyberBaseKeys_le hOnK
  have hOpkOn : (env.get (h₁.wk st)).2.2.2.2.1.length ≤
      (AuthKindFuels.ofBudget S b).K_on := Nat.le_trans hb.opkEntries_le hOnK
  unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.recvTailKC
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvTailC
  iterate 4 refine hs_letV_congr rfl fun _ => ?_
  iterate 2 refine hs_bindV_congr rfl fun _ => ?_
  refine hs_letV_congr (hs_kyberCheckE_eq _ _ _ _ _
    (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stKyb,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hKybOn)
    (Nat.le_trans (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stKyb,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hKybOn) hOnQ))
    fun _ => ?_
  refine hs_ite_congr rfl rfl ?_
  refine hs_bindV_congr rfl fun _ => ?_
  refine hs_caseOptV_congr rfl rfl fun _ => ?_
  iterate 4 refine hs_bindV_congr rfl fun _ => ?_
  refine hs_bindV_congr (hkdfOrRoC_fuel_eq _ _ true st _ _
    (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRoK)
    (Nat.le_trans (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRoK) hRoQ))
    fun _ => ?_
  refine hs_bindV_congr rfl fun _ => ?_
  refine hs_bindV_congr (rootRoC_hs_fuel_eq _ _ st _ _ _
    (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRtK)
    (Nat.le_trans (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRtK) hRoQ))
    fun _ => ?_
  iterate 3 refine hs_bindV_congr rfl fun _ => ?_
  refine hs_caseOptV_congr rfl rfl fun _ => ?_
  iterate 2 refine hs_bindV_congr rfl fun _ => ?_
  refine hs_caseOptV_congr rfl rfl fun _ => ?_
  refine hs_bindV_congr
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.findHonestC_fuel_eq
      S b st _ _
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hb) hOnK)
    fun _ => ?_
  refine hs_letV_congr ?_ fun _ => rfl
  cases opk
  · rfl
  · simp only [↓reduceIte, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk, Expr.eval]
    rw [hs_eMap_eq (AuthKindFuels.ofBudget S b).K_on b.q_total _ _ _
      (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stOpks,
            Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hOpkOn)
      (Nat.le_trans (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stOpks,
            Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hOpkOn) hOnQ)]

private theorem recvTailC_preserves (S : Setup) (Q : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    (kE : Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.principalEntryTy)
    (bE : Var Γ₄ _root_.SignalPqxdh.Security.ReductionDsl.spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hRoQ : (valRoCache (env.get (h₁.wk st))).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk st))).length ≤ Q) :
    ∀ out ∈ support
        ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvTailC
          S Q opk st x kE bE oSk?).eval env),
      AuthBaseValOnlineBounded (n + 1) out.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) (valRoCache out.2) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st))) (valRootRoCache out.2) ∧
      out.2.2.2.2.1 = (env.get (h₁.wk st)).2.2.2.1 := by
  have hb1 := hb.mono (Nat.le_succ n)
  have hAbort :
      AuthBaseValOnlineBounded (n + 1) (env.get (h₁.wk st)) ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) (valRoCache (env.get (h₁.wk st))) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st)))
        (valRootRoCache (env.get (h₁.wk st))) ∧
      (env.get (h₁.wk st)).2.2.2.1 = (env.get (h₁.wk st)).2.2.2.1 :=
    ⟨hb1, CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _, rfl⟩
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvTailC
  iterate 4 (apply support_hs_letV_any; intro _)
  iterate 2 (apply support_hs_bindV_any; intro _)
  apply support_hs_letV; intro kcVal hkc
  have hkcLen : kcVal.2.length ≤ n + 1 := by
    rw [hkc]
    exact hs_kyberCheckE_snd_len_le Q _ _ _
      (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stKyb,
            Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero]
          using hb.seenKyberBaseKeys_le)
  apply support_hs_ite
  · intro _; apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  apply support_hs_bindV_any; intro _
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  iterate 4 (apply support_hs_bindV_any; intro _)
  apply support_hs_bindV; intro dr hdr
  have hdrStep : CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) dr.2 := by
    simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using
      hkdfOrRoC_step Q true st _ _
        (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRoQ)
        dr hdr
  apply support_hs_bindV_any; intro _
  apply support_hs_bindV; intro rkOut hrk
  have hrkStep : CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st))) rkOut.2 := by
    simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using
      rootRoC_hs_step Q st _ _ _
        (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRtQ)
        rkOut hrk
  iterate 3 (apply support_hs_bindV_any; intro _)
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  iterate 2 (apply support_hs_bindV_any; intro _)
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  apply support_hs_bindV_any; intro _
  apply support_hs_letV; intro st' hst'
  apply support_hs_ret
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Expr.eval, hs_ext_refl_wk, hs_env_get_zero]
  subst hst'
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero,
      valRoCache, valRootRoCache]
    exact ⟨{ hb1 with
              usedRecvNoOPK_le := Nat.succ_le_succ hb.usedRecvNoOPK_le
              seenKyberBaseKeys_le := hkcLen },
      hdrStep, hrkStep, trivial⟩
  · simp only [↓reduceIte,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stMk,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero,
      valRoCache, valRootRoCache]
    exact ⟨{ hb1 with
              opkEntries_le := hs_eMap_length_le Q _ _ _
                (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
                      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stOpks,
                      Expr.eval, hs_ext_step_wk, hs_env_get_succ]
                    using hb1.opkEntries_le)
              usedRecvOPK_le := Nat.succ_le_succ hb.usedRecvOPK_le
              seenKyberBaseKeys_le := hkcLen },
      hdrStep, hrkStep, trivial⟩

private theorem recvKB_fuel_eq (S : Setup) (b : QueryBudget) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hOnK : n ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRoK : (valRoCache (env.get (h₁.wk st))).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRtK : (valRootRoCache (env.get (h₁.wk st))).length ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.recvKB
      S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro opk st x).eval env =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvB S b.q_total opk st x).eval env := by
  have hOnQ := AuthKindFuels.K_on_le_q_total S b
  have hPrinOn : (env.get (h₁.wk st)).2.2.1.length ≤ (AuthKindFuels.ofBudget S b).K_on :=
    Nat.le_trans hb.principals_le hOnK
  have hSpkOn : (env.get (h₁.wk st)).2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).K_on :=
    Nat.le_trans hb.spkBundles_le hOnK
  have hOpkOn : (env.get (h₁.wk st)).2.2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).K_on :=
    Nat.le_trans hb.opkEntries_le hOnK
  unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.recvKB
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvB
  iterate 3 refine hs_letV_congr rfl fun _ => ?_
  refine hs_ite_congr rfl rfl ?_
  refine hs_ite_congr ?_ rfl ?_
  · cases opk
    · have hL := Nat.le_trans hb.usedRecvNoOPK_le hOnK
      exact hs_eAny_eq _ _ _ _ _
        (by simpa only [Bool.false_eq_true, ↓reduceIte, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUsedN,
              Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hL)
        (Nat.le_trans (by simpa only [Bool.false_eq_true, ↓reduceIte,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUsedN,
              Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hL) hOnQ)
    · have hL := Nat.le_trans hb.usedRecvOPK_le hOnK
      exact hs_eAny_eq _ _ _ _ _
        (by simpa only [↓reduceIte, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUsedO,
              Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hL)
        (Nat.le_trans (by simpa only [↓reduceIte, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUsedO,
              Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hL) hOnQ)
  refine hs_bindV_congr (koskSenderOkC_hs_fuel_eq S b st _ _
    (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hb) hOnK)
    fun _ => ?_
  refine hs_ite_congr rfl rfl ?_
  refine hs_caseOptV_congr (hs_eFind_eq _ _ _ _ _
    (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stPrin,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hPrinOn)
    (Nat.le_trans (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stPrin,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hPrinOn) hOnQ))
    rfl fun _ => ?_
  refine hs_caseOptV_congr (hs_eFind_eq _ _ _ _ _
    (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stSpks,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hSpkOn)
    (Nat.le_trans (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stSpks,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hSpkOn) hOnQ))
    rfl fun _ => ?_
  iterate 2 refine hs_letV_congr rfl fun _ => ?_
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact recvTailKC_fuel_eq S b false st x _ _ _ _
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hb)
      hOnK
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRoK)
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRtK)
  · simp only [↓reduceIte]
    refine hs_caseOptV_congr (hs_eFind_eq _ _ _ _ _
      (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stOpks,
            Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hOpkOn)
      (Nat.le_trans (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stOpks,
            Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hOpkOn) hOnQ))
      rfl fun _ => ?_
    refine hs_ite_congr rfl rfl ?_
    exact recvTailKC_fuel_eq S b true st x _ _ _ _
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hb)
      hOnK
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRoK)
      (by simpa only [hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRtK)

private theorem recvB_preserves (S : Setup) (Q : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hRoQ : (valRoCache (env.get (h₁.wk st))).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk st))).length ≤ Q) :
    ∀ out ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvB S Q opk st x).eval env),
      AuthBaseValOnlineBounded (n + 1) out.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) (valRoCache out.2) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st))) (valRootRoCache out.2) ∧
      out.2.2.2.2.1 = (env.get (h₁.wk st)).2.2.2.1 := by
  have hb1 := hb.mono (Nat.le_succ n)
  have hAbort :
      AuthBaseValOnlineBounded (n + 1) (env.get (h₁.wk st)) ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk st))) (valRoCache (env.get (h₁.wk st))) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk st)))
        (valRootRoCache (env.get (h₁.wk st))) ∧
      (env.get (h₁.wk st)).2.2.2.1 = (env.get (h₁.wk st)).2.2.2.1 :=
    ⟨hb1, CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _, rfl⟩
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvB
  iterate 3 (apply support_hs_letV_any; intro _)
  apply support_hs_ite
  · intro _; apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  apply support_hs_ite
  · intro _; apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  apply support_hs_bindV_any; intro _
  apply support_hs_ite
  · intro _; apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hAbort
  intro _
  iterate 2 (apply support_hs_letV_any; intro _)
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro out hout
    simpa only [hs_ext_step_wk, hs_env_get_succ] using
      recvTailC_preserves S Q false st x _ _ _ _
        (by simpa only [hs_ext_step_wk, hs_env_get_succ] using hb)
        (by simpa only [hs_ext_step_wk, hs_env_get_succ] using hRoQ)
        (by simpa only [hs_ext_step_wk, hs_env_get_succ] using hRtQ)
        out hout
  · simp only [↓reduceIte]
    apply support_hs_caseOptV
    · apply support_hs_ret
      simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
        Expr.eval, hs_ext_step_wk, hs_env_get_succ] using hAbort
    intro _
    apply support_hs_ite
    · intro _; apply support_hs_ret
      simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.rs,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
        Expr.eval, hs_ext_step_wk, hs_env_get_succ] using hAbort
    intro _ out hout
    simpa only [hs_ext_step_wk, hs_env_get_succ] using
      recvTailC_preserves S Q true st x _ _ _ _
        (by simpa only [hs_ext_step_wk, hs_env_get_succ] using hb)
        (by simpa only [hs_ext_step_wk, hs_env_get_succ] using hRoQ)
        (by simpa only [hs_ext_step_wk, hs_env_get_succ] using hRtQ)
        out hout

private theorem onBase_recvB_preserves (S : Setup) (Q : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hRoQ : (valRoCache (env.get (h₁.wk s)).1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ Q) :
    ∀ r ∈ support
        ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase s fun g =>
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvB S Q opk g x).eval env),
      AuthBaseValOnlineBounded (n + 1) r.2.1 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk s)).1) (valRoCache r.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk s)).1) (valRootRoCache r.2.1) ∧
      r.2.1.2.2.2.1 = (env.get (h₁.wk s)).1.2.2.2.1 ∧
      r.2.2.2.2.2.2.1 = (env.get (h₁.wk s)).2.2.2.2.2.1 ∧
      r.2.2.2.2.2.2.2.1 = (env.get (h₁.wk s)).2.2.2.2.2.2.1 := by
  have hg : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v s)).eval env =
      (env.get (h₁.wk s)).1 := by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval]
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
  apply support_hs_bindV; intro r0 hr0
  rw [hs_letV_eval, hg] at hr0
  rcases recvB_preserves S Q opk .vz x (.cons (env.get (h₁.wk s)).1 env)
    (by simpa only [hs_ext_refl_wk, hs_env_get_zero] using hb)
    (by simpa only [hs_ext_refl_wk, hs_env_get_zero] using hRoQ)
    (by simpa only [hs_ext_refl_wk, hs_env_get_zero] using hRtQ) r0 hr0 with
    ⟨hB, hRoS, hRtS, hSpks⟩
  apply support_hs_ret
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero]
  exact ⟨hB, hRoS, hRtS, hSpks, trivial, trivial⟩

private theorem shcrAcceptKB_fuel_eq (S : Setup) (b : QueryBudget) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hOnK : n ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRoK : (valRoCache (env.get (h₁.wk s)).1).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRtK : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrAcceptKB
      S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro opk s x).eval env =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S b.q_total opk s x).eval env := by
  have hOnQ := AuthKindFuels.K_on_le_q_total S b
  have hRoQ := AuthKindFuels.K_ro_le_q_total S b
  have hg : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v s)).eval env =
      (env.get (h₁.wk s)).1 := by
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Expr.eval]
  have hOnBase :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase s fun g =>
        Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.recvKB
          S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro opk g x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase s fun g =>
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvB S b.q_total opk g x).eval env := by
    unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
    refine hs_bindV_congr ?_ fun _ => rfl
    rw [hs_letV_eval, hs_letV_eval, hg]
    exact recvKB_fuel_eq S b opk .vz x (.cons (env.get (h₁.wk s)).1 env)
      (by simpa only [hs_ext_refl_wk, hs_env_get_zero] using hb)
      hOnK
      (by simpa only [hs_ext_refl_wk, hs_env_get_zero] using hRoK)
      (by simpa only [hs_ext_refl_wk, hs_env_get_zero] using hRtK)
  unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrAcceptKB
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB
  rw [hs_bindV_eval, hs_bindV_eval, hOnBase]
  refine Computational.Proofs.ReductionDsl.StepSim.bind_congr_support _ _ _ fun r hr => ?_
  have hSpksEq := (onBase_recvB_preserves S b.q_total opk s x env hb
    (Nat.le_trans hRoK hRoQ) (Nat.le_trans hRtK hRoQ) r hr).2.2.2.1
  have hSpkOn : r.2.1.2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).K_on :=
    hSpksEq ▸ Nat.le_trans hb.spkBundles_le hOnK
  refine hs_letV_congr rfl fun _ => ?_
  refine hs_caseOptV_congr (hs_eFind_eq _ _ _ _ _
    (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stSpks,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hSpkOn)
    (Nat.le_trans (by simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stSpks,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase,
          Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hSpkOn) hOnQ))
    rfl fun _ => rfl

private theorem shcrAcceptB_preserves (S : Setup) (Q : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hRoQ : (valRoCache (env.get (h₁.wk s)).1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ Q) :
    ∀ scs ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S Q opk s x).eval env),
      AuthBaseValOnlineBounded (n + 1) scs.2.1 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk s)).1) (valRoCache scs.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk s)).1) (valRootRoCache scs.2.1) ∧
      scs.2.2.2.2.2.2.1 = (env.get (h₁.wk s)).2.2.2.2.2.1 ∧
      scs.2.2.2.2.2.2.2.1.length ≤ (env.get (h₁.wk s)).2.2.2.2.2.2.1.length + 1 := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB
  apply support_hs_bindV; intro r hr
  rcases onBase_recvB_preserves S Q opk s x env hb hRoQ hRtQ r hr with
    ⟨hB, hRoS, hRtS, _, hIR, hRR⟩
  have hRetR :
      AuthBaseValOnlineBounded (n + 1) r.2.1 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk s)).1) (valRoCache r.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk s)).1) (valRootRoCache r.2.1) ∧
      r.2.2.2.2.2.2.1 = (env.get (h₁.wk s)).2.2.2.2.2.1 ∧
      r.2.2.2.2.2.2.2.1.length ≤ (env.get (h₁.wk s)).2.2.2.2.2.2.1.length + 1 :=
    ⟨hB, hRoS, hRtS, hIR, by rw [hRR]; exact Nat.le_succ _⟩
  apply support_hs_letV_any; intro _
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRetR
  intro _
  apply support_hs_bindV_any; intro _
  apply support_hs_caseOptV
  · apply support_hs_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
      Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero] using hRetR
  intro _
  apply support_hs_ret
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Expr.eval, hs_ext_step_wk, hs_ext_refl_wk, hs_env_get_succ, hs_env_get_zero,
    List.length_cons]
  exact ⟨hB, hRoS, hRtS, hIR, by rw [hRR]⟩

private theorem tryPauseC_fuel_eq (S : Setup) (b : QueryBudget) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC
      S (AuthKindFuels.ofBudget S b).K_on opk s x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S b.q_total opk s x).eval env := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC
  apply hs_ite_congr rfl rfl
  apply hs_letV_congr_eq rfl; intro st hst
  have hbSt : AuthBaseValOnlineBounded n st := by
    have : st = (env.get (h₁.wk s)).1 := hst
    rwa [this]
  apply hs_bindV_congr
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.preCheckC_fuel_eq
      S b opk (Var.zero : Var (authStateTy :: Δ) authStateTy) x (.cons st env) hbSt hn
  intro pc
  apply hs_caseOptV_congr rfl rfl; intro d
  apply hs_letV_congr rfl; intro bu
  apply hs_bindV_congr
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.checkSigsC_fuel_eq
      S b (Γ₁ := authStateTy :: Δ)
      (Var.zero : Var (authStateTy :: Δ) authStateTy)
      (Var.zero : Var (preKeyBundleTy :: pauseTy :: .opt pauseTy :: authStateTy :: Δ) preKeyBundleTy)
      (.cons bu (.cons d (.cons pc (.cons st env)))) hbSt hn
  intro ok
  rfl

private def twoVarRen {A B : Ty pqSig} {Δ : List (Ty pqSig)}
    (vA : Var Δ A) (vB : Var Δ B) : ∀ {t}, Var [A, B] t → Var Δ t
  | _, .zero => vA
  | _, .succ .zero => vB

private theorem twoVarRen_eval {P R : Ty pqSig} {Δ₁ Δ₂ : List (Ty pqSig)}
    (c : Comp pqxdhOps pqPrimIface [P, shcrStTy] R)
    (x₁ : Var Δ₁ P) (s₁ : Var Δ₁ shcrStTy) (env₁ : Env Δ₁)
    (x₂ : Var Δ₂ P) (s₂ : Var Δ₂ shcrStTy) (env₂ : Env Δ₂)
    (hx : env₁.get x₁ = env₂.get x₂) (hs : env₁.get s₁ = env₂.get s₂) :
    (Computational.Proofs.SignalPqxdh.AtomicLift.compRename (twoVarRen x₁ s₁) c).eval env₁ =
      (Computational.Proofs.SignalPqxdh.AtomicLift.compRename (twoVarRen x₂ s₂) c).eval env₂ := by
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval c _
        (.cons (env₁.get x₁) (.cons (env₁.get s₁) .nil)) env₁
        (fun v => by cases v with
          | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v),
      Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval c _
        (.cons (env₂.get x₂) (.cons (env₂.get s₂) .nil)) env₂
        (fun v => by cases v with
          | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v),
      hx, hs]

private theorem arm2_wk_eval {P R : Ty pqSig}
    (arm0 : Comp pqxdhOps pqPrimIface [P, shcrStTy] R)
    {Γs₁ Γs₂ Δ₁ Δ₂ : List (Ty pqSig)} [h₁ : Ext Γs₁ (P :: Δ₁)] [h₂ : Ext Γs₂ (P :: Δ₂)]
    (s₁ : Var Γs₁ shcrStTy) (s₂ : Var Γs₂ shcrStTy)
    {c₁ : Comp pqxdhOps pqPrimIface (P :: Δ₁) R}
    {c₂ : Comp pqxdhOps pqPrimIface (P :: Δ₂) R}
    (env₁ : Env (P :: Δ₁)) (env₂ : Env (P :: Δ₂))
    (hc₁ : Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (twoVarRen .zero (h₁.wk s₁)) arm0 = c₁)
    (hc₂ : Computational.Proofs.SignalPqxdh.AtomicLift.compRename
      (twoVarRen .zero (h₂.wk s₂)) arm0 = c₂)
    (hx : env₁.get .zero = env₂.get .zero)
    (hs : env₁.get (h₁.wk s₁) = env₂.get (h₂.wk s₂)) :
    c₁.eval env₁ = c₂.eval env₂ := by
  rw [← hc₁, ← hc₂]
  exact twoVarRen_eval arm0 _ _ env₁ _ _ env₂ hx hs

private theorem hs_caseSumV_inl_eval {Δ : List (Ty pqSig)} {A B R : Ty pqSig}
    (e : Expr pqxdhOps Δ (.sum A B))
    (kl : Var (A :: Δ) A → Comp pqxdhOps pqPrimIface (A :: Δ) R)
    (kr : Var (B :: Δ) B → Comp pqxdhOps pqPrimIface (B :: Δ) R)
    {env : Env Δ} {a : A.denote} (he : e.eval env = .inl a) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseSumV e kl kr).eval env =
      (kl .zero).eval (.cons a env) := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseSumV, Comp.eval, he]

private theorem hs_caseSumV_inr_eval {Δ : List (Ty pqSig)} {A B R : Ty pqSig}
    (e : Expr pqxdhOps Δ (.sum A B))
    (kl : Var (A :: Δ) A → Comp pqxdhOps pqPrimIface (A :: Δ) R)
    (kr : Var (B :: Δ) B → Comp pqxdhOps pqPrimIface (B :: Δ) R)
    {env : Env Δ} {b : B.denote} (he : e.eval env = .inr b) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseSumV e kl kr).eval env =
      (kr .zero).eval (.cons b env) := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseSumV, Comp.eval, he]

private theorem tryPauseC_env_eq (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy)
    [h₁ : Ext Γ₁ (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ)]
    (env : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S K opk s
      (Var.zero : Var (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ) _)).eval env =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S K opk
      (Γ₁ := [shcrStTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy])
      .vz .vz).eval (.cons (env.get .zero) (.cons (env.get (h₁.wk s)) .nil)) := by
  cases opk with
  | false =>
    exact arm2_wk_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S K false
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy]) .vz .vz)
      (Γs₂ := [shcrStTy]) s .vz env (.cons (env.get .zero) (.cons (env.get (h₁.wk s)) .nil))
      rfl rfl rfl rfl
  | true =>
    exact arm2_wk_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S K true
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy]) .vz .vz)
      (Γs₂ := [shcrStTy]) s .vz env (.cons (env.get .zero) (.cons (env.get (h₁.wk s)) .nil))
      rfl rfl rfl rfl

set_option maxRecDepth 4096 in
private theorem shcrSendC_wk_eval (S : Setup) (K : ℕ) (opk : Bool)
    {Δ₁ Δ₂ : List (Ty pqSig)}
    [Ext [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ₁)]
    [Ext [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ₂)]
    (env₁ : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ₁))
    (env₂ : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ₂))
    (hx : env₁.get .zero = env₂.get .zero)
    (hs : env₁.get (Ext.wk (Var.zero :
            Var [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy] shcrStTy)) =
          env₂.get (Ext.wk (Var.zero :
            Var [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy] shcrStTy))) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K opk
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Γ₂ := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ₁) .vz .vz).eval env₁ =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K opk
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Γ₂ := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ₂) .vz .vz).eval env₂ := by
  let Γs := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
  cases opk with
  | false =>
    exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K false
      (Γ₁ := [shcrStTy]) (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy])
      .vz .vz) (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz env₁ env₂ rfl rfl hx hs
  | true =>
    exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K true
      (Γ₁ := [shcrStTy]) (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy])
      .vz .vz) (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz env₁ env₂ rfl rfl hx hs

private theorem shcrAcceptB_wk_eval (S : Setup) (K : ℕ) (opk : Bool)
    {Δ₁ Δ₂ : List (Ty pqSig)}
    [Ext [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ₁)]
    [Ext [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ₂)]
    (env₁ : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ₁))
    (env₂ : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ₂))
    (hx : env₁.get .zero = env₂.get .zero)
    (hs : env₁.get (Ext.wk (Var.zero :
            Var [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy] shcrStTy)) =
          env₂.get (Ext.wk (Var.zero :
            Var [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy] shcrStTy))) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K opk
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Γ₂ := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ₁) .vz .vz).eval env₁ =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K opk
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Γ₂ := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ₂) .vz .vz).eval env₂ := by
  let Γs := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
  cases opk with
  | false =>
    exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K false
      (Γ₁ := [shcrStTy]) (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy, shcrStTy])
      .vz .vz) (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz env₁ env₂ rfl rfl hx hs
  | true =>
    exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K true
      (Γ₁ := [shcrStTy]) (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy, shcrStTy])
      .vz .vz) (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz env₁ env₂ rfl rfl hx hs

private theorem shcrPost1KeyC_wk_eval (S : Setup) (K : ℕ)
    (p : (Ty.opt pauseTy).denote) (s0 : shcrStTy.denote) (t : AuthQuery S) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S K
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Δ := .opt pauseTy :: [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      .vz .vz).eval
      (.cons p (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t :
        _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy.denote) .nil))) =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S K
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
      .vz .vz).eval
      (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t :
        _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy.denote) .nil)) := by
  let Γs := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
  cases t with
  | initPrin u =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inl_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
        fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.initPrin1KeyB K g
          (Var.zero : Var [.nat, shcrStTy] .nat)) (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl
  | corruptIK u =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
        fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB K g
          (Var.zero : Var [.nat, shcrStTy] .nat)) (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl
  | genSPK u j =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S K
        (Γ₁ := [shcrStTy]) (Γ₂ := [.prod .nat .nat, shcrStTy]) .vz .vz)
        (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl
  | genOPK u j o =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
        fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB K g
          (Var.zero : Var [.prod .nat (.prod .nat .nat), shcrStTy] _))
        (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl
  | sendOPK u i bu m0 m1 =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      exact shcrSendC_wk_eval S K true _ _ rfl rfl
  | sendNoOPK u i bu m0 m1 =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      exact shcrSendC_wk_eval S K false _ _ rfl rfl
  | recvOPK k j o msg =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      exact shcrAcceptB_wk_eval S K true _ _ rfl rfl
  | recvNoOPK k j l msg =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      exact shcrAcceptB_wk_eval S K false _ _ rfl rfl
  | roQuery sec =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
        fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB K g
          (Var.zero : Var [B 192, shcrStTy] _))
        (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl
  | roRootQuery rk dh =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
        fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB K g
          (Var.zero : Var [.prod (B 32) (B 32), shcrStTy] _))
        (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl
  | revealDhSecrets =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inl_eval _ _ _ rfl]
      rfl
  | registerKey sk =>
      conv_lhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl]
      conv_rhs => dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
                  rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
                      hs_caseSumV_inr_eval _ _ _ rfl]
      exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
        fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB g
          (Var.zero : Var [B 32, shcrStTy] _))
        (Γs₁ := Γs) (Γs₂ := Γs) .vz .vz _ _ rfl rfl rfl rfl

private theorem syncShcrShadowRespC_wk_eval (cap : ℕ) {τ : Ty pqAtomicSig}
    {Γ : List (Ty pqAtomicSig)}
    (rs : (Ty.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
      (embedTy shcrStTy)).denote)
    (p : τ.denote)
    (x : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authSendQAtomicTy.denote)
    (s' : authShcrShadowStTy.denote) (ρ : Env Γ) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
      cap .v0 (.snd .v3)).eval (.cons rs (.cons p (.cons x (.cons s' ρ)))) =
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
      cap .v0 (.snd .v2)).eval (.cons rs (.cons x (.cons s' ρ))) := by
  have hRen :
      Computational.Proofs.SignalPqxdh.AtomicLift.compRename
        (Computational.Proofs.SignalPqxdh.AtomicLift.liftRen (fun {_} => Var.succ))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          cap .v0 (.snd .v2) :
          Comp pqAtomicOps pqAuthPrimIface
            (_ :: Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authSendQAtomicTy ::
              authShcrShadowStTy :: Γ) _) =
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
        cap .v0 (.snd .v3) :
        Comp pqAtomicOps pqAuthPrimIface
          (_ :: τ :: Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authSendQAtomicTy ::
            authShcrShadowStTy :: Γ) _) := rfl
  rw [← hRen]
  exact Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval _ _
    (.cons rs (.cons x (.cons s' ρ))) (.cons rs (.cons p (.cons x (.cons s' ρ))))
    (fun v => by cases v <;> rfl)

private theorem wrapInl_eval {S : Setup} {A : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (m : Comp pqAtomicOps pqAuthPrimIface (A :: Γ)
      (.prod (authCodec S).R authShcrShadowStTy))
    (env : Env (A :: Γ)) :
    (Comp.bind m (.ret (.inl .v0)) :
      Comp pqAtomicOps pqAuthPrimIface (A :: Γ)
        (.sum (.prod (authCodec S).R authShcrShadowStTy)
          (.prod (PB 1568) (.prod (embedTy pauseTy) authShcrShadowStTy)))).eval env =
    Sum.inl <$> m.eval env := by
  change (m.eval env >>= (pure ∘ Sum.inl)) = Sum.inl <$> m.eval env
  rw [← map_eq_bind_pure_comp]

private theorem hs_caseOptV_none_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ)
    (ho : o.eval ρ = none) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o kn ks).eval ρ = kn.eval ρ := by
  rw [hs_caseOptV_eval, ho]

private theorem hs_caseOptV_some_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) (x : τ₁.denote)
    (ho : o.eval ρ = some x) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV o kn ks).eval ρ =
      (ks .zero).eval (.cons x ρ) := by
  rw [hs_caseOptV_eval, ho]

private theorem forgetPreOut_map_inl {ι : Type} {spec : OracleSpec ι}
    {R S₁ S₂ C P₁ P₂ : Type}
    (fP : P₁ → P₂) (fS : S₁ → S₂) (mx : OracleComp spec (R × S₁)) :
    forgetPreOut fP fS <$> (Sum.inl <$> mx : OracleComp spec ((R × S₁) ⊕ (C × P₁ × S₁))) =
      Sum.inl <$> (Prod.map id fS <$> mx) := by
  rw [Functor.map_map, Functor.map_map]; rfl

private theorem oc_map_pure {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (f : α → β) (x : α) : f <$> (pure x : OracleComp spec α) = pure (f x) :=
  map_pure f x

private theorem inl_map_embedVal_bind_eq {ι : Type} {spec : OracleSpec ι}
    (A B : Ty pqSig) (mx : OracleComp spec A.denote)
    (k : A.denote → OracleComp spec (A.denote ⊕ B.denote))
    (hk : ∀ x, k x = pure (Sum.inl x)) :
    (Sum.inl <$> (embedVal A <$> mx) : OracleComp spec ((embedTy A).denote ⊕ (embedTy B).denote)) =
      embedVal (.sum A B) <$> (mx >>= k) := by
  have hk' : k = pure ∘ Sum.inl := funext hk
  rw [hk', ← map_eq_bind_pure_comp, Functor.map_map, Functor.map_map]
  rfl

private theorem map_bind_congr {ι : Type} {spec : OracleSpec ι} {α β₁ β₂ γ : Type}
    (f₁ : β₁ → γ) (f₂ : β₂ → γ) (mx : OracleComp spec α)
    (g₁ : α → OracleComp spec β₁) (g₂ : α → OracleComp spec β₂)
    (h : ∀ a ∈ support mx, f₁ <$> g₁ a = f₂ <$> g₂ a) :
    f₁ <$> (mx >>= g₁) = f₂ <$> (mx >>= g₂) := by
  rw [map_bind, map_bind]
  exact OracleComp.bind_congr_of_forall_mem_support mx h

private theorem map_bind_bind_congr {ι : Type} {spec : OracleSpec ι} {α β₁ β₂ γ : Type}
    (e : β₁ → β₂) (mx : OracleComp spec α)
    (f : α → OracleComp spec β₁) (g : β₂ → OracleComp spec γ) (h : α → OracleComp spec γ)
    (H : ∀ a ∈ support mx, (e <$> f a) >>= g = h a) :
    (e <$> (mx >>= f)) >>= g = mx >>= h := by
  rw [map_bind, bind_assoc]
  exact OracleComp.bind_congr_of_forall_mem_support mx H

private theorem RoBothShadowRel.of_cache_eq {cap : ℕ}
    {st st' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authBaseAtomicTy.denote}
    {avls : roBothAvlTy.denote}
    (h : RoBothShadowRel cap st avls)
    (hRo : atomRoCache st' = atomRoCache st)
    (hRt : atomRootRoCache st' = atomRootRoCache st) :
    RoBothShadowRel cap st' avls := by
  rcases h with ⟨hV, hN1, hN2⟩
  refine ⟨?_, ?_, ?_⟩
  · rwa [hRo, hRt]
  · rwa [hRo]
  · rwa [hRt]

private def twoBaseRen {P : Ty pqSig} {Δ : List (Ty pqSig)}
    (vSt : Var Δ authStateTy) (vX : Var Δ P) : ∀ {t}, Var [authStateTy, P] t → Var Δ t
  | _, .zero => vSt
  | _, .succ .zero => vX

private theorem twoBaseRen_eval {P R : Ty pqSig} {Δ₁ Δ₂ : List (Ty pqSig)}
    (c0 : Comp pqxdhOps pqPrimIface [authStateTy, P] R)
    (vSt₁ : Var Δ₁ authStateTy) (vX₁ : Var Δ₁ P)
    (vSt₂ : Var Δ₂ authStateTy) (vX₂ : Var Δ₂ P)
    {c₁ : Comp pqxdhOps pqPrimIface Δ₁ R}
    {c₂ : Comp pqxdhOps pqPrimIface Δ₂ R}
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hc₁ : Computational.Proofs.SignalPqxdh.AtomicLift.compRename (twoBaseRen vSt₁ vX₁) c0 = c₁)
    (hc₂ : Computational.Proofs.SignalPqxdh.AtomicLift.compRename (twoBaseRen vSt₂ vX₂) c0 = c₂)
    (hSt : env₁.get vSt₁ = env₂.get vSt₂)
    (hX : env₁.get vX₁ = env₂.get vX₂) :
    c₁.eval env₁ = c₂.eval env₂ := by
  rw [← hc₁, ← hc₂]
  rw [Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval c0 _
        (.cons (env₁.get vSt₁) (.cons (env₁.get vX₁) .nil)) env₁
        (fun v => by cases v with
          | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v),
      Computational.Proofs.SignalPqxdh.AtomicLift.compRename_eval c0 _
        (.cons (env₂.get vSt₂) (.cons (env₂.get vX₂) .nil)) env₂
        (fun v => by cases v with
          | zero => rfl | succ v => cases v with | zero => rfl | succ v => nomatch v),
      hSt, hX]

private theorem shcrBaseArmC_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S) (xL : arg.denote)
    (stepK stepRef :
      ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
        Var Γ₁ authStateTy → Var Γ₂ arg →
        Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t)
    (hFuel :
      (stepK (Γ₁ := [authStateTy, .prod authStateTy arg])
             (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
             (Δ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval
        (.cons xL (.cons (projVal shcrStTy s'.1).1 (.cons ((projVal shcrStTy s'.1).1, xL) .nil))) =
      (stepRef (Γ₁ := [authStateTy, .prod authStateTy arg])
               (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
               (Δ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval
        (.cons xL (.cons (projVal shcrStTy s'.1).1 (.cons ((projVal shcrStTy s'.1).1, xL) .nil))))
    (hWk :
      (stepRef (Γ₁ := [authStateTy, .prod authStateTy arg])
               (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
               (Δ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval
        (.cons xL (.cons (projVal shcrStTy s'.1).1 (.cons ((projVal shcrStTy s'.1).1, xL) .nil))) =
      (stepRef (Γ₁ := [authStateTy, arg, shcrStTy])
               (Γ₂ := [arg, shcrStTy])
               (Δ := [authStateTy, arg, shcrStTy])
               .zero .zero).eval
        (Env.cons (t := authStateTy) (projVal shcrStTy s'.1).1
          (Env.cons (t := arg) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil))))
    (hPres : ∀ r ∈ support
        ((stepRef (Γ₁ := [authStateTy, .prod authStateTy arg])
                  (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
                  (Δ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval
          (.cons xL (.cons (projVal shcrStTy s'.1).1 (.cons ((projVal shcrStTy s'.1).1, xL) .nil)))),
      AuthBaseValOnlineBounded (c 0 + 1) r.2 ∧
      valRoCache r.2 = valRoCache (projVal shcrStTy s'.1).1 ∧
      valRootRoCache r.2 = valRootRoCache (projVal shcrStTy s'.1).1) :
    let ρ_arm : Env [embedTy arg, authShcrShadowStTy, (authCodec S).Q] :=
      .cons (embedVal arg xL) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let env_old : Env [arg, shcrStTy] :=
      Env.cons (t := arg) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    Prod.map id forgetShcr <$>
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
          (S := S) (fun st x => stepK st x)).eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
          (Γ₁ := [shcrStTy])
          .vz (fun g => stepRef g
            (Var.zero : Var [arg, shcrStTy] arg))).eval env_old ∧
    ∀ p ∈ support
        ((Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
          (S := S) (fun st x => stepK st x)).eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro ρ_arm env_old
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hs1_2 : s'.1.2 = (embedVal shcrStTy s0).2 := by rw [hs1]
  let env_in : Env [arg, authStateTy, .prod authStateTy arg] :=
    .cons xL (.cons s0.1 (.cons (s0.1, xL) .nil))
  have hArgProj :
      projVal (.prod authStateTy arg)
        ((Expr.pair (.fst (.fst .v1)) .v0 :
          Expr pqAtomicOps [embedTy arg, authShcrShadowStTy, (authCodec S).Q]
            (embedTy (.prod authStateTy arg))).eval ρ_arm) = (s0.1, xL) := by
    change (projVal authStateTy s'.1.1, projVal arg (embedVal arg xL)) = (s0.1, xL)
    rw [hs1_1, Computational.Proofs.SignalPqxdh.AtomicLift.projVal_embedVal,
        Computational.Proofs.SignalPqxdh.AtomicLift.projVal_embedVal]
  have hLift :
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         stepK st x)
        (.pair (.fst (.fst .v1)) .v0)).eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$>
        (stepRef (Γ₁ := [authStateTy, .prod authStateTy arg])
                 (Γ₂ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval env_in := by
    rw [liftAuthPrim1_eval, hArgProj]
    apply congrArg (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$> ·)
    rw [hs_letV_eval, hs_letV_eval]
    exact hFuel
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c t hOn hNotRo hNotRt
  have hArm :
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
        (S := S) (fun st x => stepK st x)).eval ρ_arm =
      (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$>
        (stepRef (Γ₁ := [authStateTy, .prod authStateTy arg])
                 (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
                 (Δ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval env_in) >>=
        fun rs => pure ((rs.1, ((rs.2, s'.1.2), s'.2)) :
          (Ty.prod (authCodec S).R authShcrShadowStTy).denote) := by
    change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      _ _).eval ρ_arm >>= _ = _
    rw [hLift]
    rfl
  have hOnBase :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
        (Γ₁ := [shcrStTy])
        .vz (fun g => stepRef g
          (Var.zero : Var [arg, shcrStTy] arg))).eval env_old =
      (stepRef (Γ₁ := [authStateTy, .prod authStateTy arg])
               (Γ₂ := [arg, authStateTy, .prod authStateTy arg])
               (Δ := [arg, authStateTy, .prod authStateTy arg]) .zero .zero).eval env_in >>=
        fun r => pure ((r.1, (r.2, s0.2)) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) := by
    unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
    rw [hs_bindV_eval, hs_letV_eval]
    have hSc : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v
          (Var.zero : Var [shcrStTy] shcrStTy))).eval env_old =
        s0.1 := rfl
    rw [hSc, ← hWk]
    rfl
  constructor
  · rw [hArm, hOnBase]
    erw [bind_map_left, map_bind, map_bind]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun r _ => ?_
    rw [oc_map_pure, oc_map_pure]
    exact congrArg pure (Prod.ext rfl (Prod.ext rfl hs1_2))
  · intro p hp
    rw [hArm] at hp
    erw [bind_map_left, mem_support_bind_iff] at hp
    rcases hp with ⟨r, hr, hp'⟩
    erw [mem_support_pure_iff] at hp'
    subst hp'
    obtain ⟨hb1, hRoEq, hRtEq⟩ := hPres r hr
    have hRoA : atomRoCache (embedVal authStateTy r.2) = atomRoCache s'.1.1 := by
      rw [hs1_1, atomRoCache_embedVal, atomRoCache_embedVal, hRoEq]
    have hRtA : atomRootRoCache (embedVal authStateTy r.2) = atomRootRoCache s'.1.1 := by
      rw [hs1_1, atomRootRoCache_embedVal, atomRootRoCache_embedVal, hRtEq]
    refine ⟨hInv.counter_inv.bump t hroom, ?_⟩
    rw [hc0, hc1, hc2]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (AuthBaseAtomOnlineBounded.iff_embedVal r.2).mpr hb1
    · change (atomRoCache (embedVal authStateTy r.2)).length ≤ (c 0 + 1) + c 1
      rw [hRoA]
      exact Nat.le_trans hInv.shadow_ok.base_ok.ro_len_le (by omega)
    · change (atomRootRoCache (embedVal authStateTy r.2)).length ≤ (c 0 + 1) + c 2
      rw [hRtA]
      exact Nat.le_trans hInv.shadow_ok.base_ok.root_len_le (by omega)
    · exact RoBothShadowRel.of_cache_eq hInv.shadow_ok.base_ok.ro_shadow hRoA hRtA
    · exact Nat.le_trans hInv.shadow_ok.ir_le (Nat.le_succ (c 0))
    · exact Nat.le_trans hInv.shadow_ok.rr_le (Nat.le_succ (c 0))

private theorem genSpkB_fuel_eq_two (K Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hK : n ≤ K) (hQ : n ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB K st x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB Q st x).eval env := by
  have hSK := List.take_of_length_le (Nat.le_trans hb.spkBundles_le hK)
  have hSQ := List.take_of_length_le (Nat.le_trans hb.spkBundles_le hQ)
  have hPK := List.take_of_length_le (Nat.le_trans hb.principals_le hK)
  have hPQ := List.take_of_length_le (Nat.le_trans hb.principals_le hQ)
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB, Comp.iteC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.caseOptV, Comp.caseOptC,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eAny, Expr.anyBounded,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eFind, Expr.findBounded,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stSpks,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stPrin,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v, Comp.eval, Expr.eval, hSK, hSQ, hPK, hPQ]

private theorem shcrGenSpkB_fuel_eq (S : Setup) (K Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hK : n ≤ K) (hQ : n ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S K s x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S Q s x).eval env := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB
  apply hs_caseOptV_congr rfl
  · unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
    apply hs_bindV_congr
    · apply hs_letV_congr_eq rfl; intro g hg
      have hbG : AuthBaseValOnlineBounded n g := hg.symm ▸ hb
      exact genSpkB_fuel_eq_two K Q (Γ₁ := authStateTy :: Δ) .zero x (.cons g env) hbG hK hQ
    · intro _; rfl
  · intro bPair
    have hb' : AuthBaseValOnlineBounded n ((Env.cons bPair env).get (Ext.step.wk s)).1 := hb
    apply hs_ite_congr rfl
    · unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
      apply hs_bindV_congr
      · apply hs_letV_congr_eq rfl; intro g hg
        have hbG : AuthBaseValOnlineBounded n g := hg.symm ▸ hb'
        exact genSpkB_fuel_eq_two K Q (Γ₁ := authStateTy :: .prod .nat .nat :: Δ)
          .zero x (.cons g (.cons bPair env)) hbG hK hQ
      · intro _; rfl
    · apply hs_ite_congr
        (hs_eAny_eq K Q _ _ (.cons bPair env)
          (Nat.le_trans hb'.spkBundles_le hK) (Nat.le_trans hb'.spkBundles_le hQ)) rfl
      exact hs_caseOptV_congr
        (hs_eFind_eq K Q _ _ (.cons bPair env)
          (Nat.le_trans hb'.principals_le hK) (Nat.le_trans hb'.principals_le hQ)) rfl (fun _ => rfl)

private theorem onBase_genSpkB_preserves (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1) :
    ∀ r ∈ support
        ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase s
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB Q g x).eval env),
      AuthBaseValOnlineBounded (n + 1) r.2.1 ∧
      valRoCache r.2.1 = valRoCache (env.get (h₁.wk s)).1 ∧
      valRootRoCache r.2.1 = valRootRoCache (env.get (h₁.wk s)).1 ∧
      r.2.2 = (env.get (h₁.wk s)).2 := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
  refine support_hs_bindV fun rsOut hrsOut => support_hs_ret ?_
  rw [hs_letV_eval] at hrsOut
  have hSc : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v s)).eval env =
      (env.get (h₁.wk s)).1 := rfl
  rw [hSc] at hrsOut
  obtain ⟨hb1, hRo, hRt⟩ :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.genSpkB_preserves_online_ro
      Q (Γ₁ := authStateTy :: Δ) .zero x (.cons (env.get (h₁.wk s)).1 env) hb rsOut hrsOut
  exact ⟨hb1, hRo, hRt, rfl⟩

private theorem shcrGenSpkB_preserves (S : Setup) (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1) :
    ∀ r ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S Q s x).eval env),
      AuthBaseValOnlineBounded (n + 1) r.2.1 ∧
      valRoCache r.2.1 = valRoCache (env.get (h₁.wk s)).1 ∧
      valRootRoCache r.2.1 = valRootRoCache (env.get (h₁.wk s)).1 ∧
      r.2.2 = (env.get (h₁.wk s)).2 := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB
  refine support_hs_caseOptV (onBase_genSpkB_preserves Q s x env hb) fun bPair => ?_
  refine support_hs_ite (fun _ => onBase_genSpkB_preserves Q s x (.cons bPair env) hb) fun _ => ?_
  refine support_hs_ite (fun _ => support_hs_ret ⟨hb.mono (Nat.le_succ n), rfl, rfl, rfl⟩) fun _ => ?_
  refine support_hs_caseOptV (support_hs_ret ⟨hb.mono (Nat.le_succ n), rfl, rfl, rfl⟩) fun uE => ?_
  refine support_hs_bindV_any fun spkSk =>
    support_hs_bindV_any fun spkPk =>
    support_hs_bindV_any fun r1 =>
    support_hs_bindV_any fun sig1 =>
    support_hs_bindV_any fun r2 =>
    support_hs_bindV_any fun sig2 => ?_
  intro y hy
  simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hy
  subst hy
  let ρ8 := Env.cons sig2 (Env.cons r2 (Env.cons sig1
    (Env.cons r1 (Env.cons spkPk (Env.cons spkSk (Env.cons uE (Env.cons bPair env)))))))
  have hPairSnd {α β : Ty pqSig} {Δ' : List (Ty pqSig)} (a : Expr pqxdhOps Δ' α)
      (b : Expr pqxdhOps Δ' β) (ρ : Env Δ') :
      ((Expr.pair a b).eval ρ).2 = b.eval ρ := rfl
  have hSt : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v s).eval ρ8 =
      env.get (h₁.wk s) := rfl
  rw [hPairSnd]
  simp only [Expr.eval, Prod.mk.eta]
  rw [hSt]
  refine ⟨{ principals_le        := Nat.le_succ_of_le hb.principals_le
            spkBundles_le        := Nat.succ_le_succ hb.spkBundles_le
            opkEntries_le        := Nat.le_succ_of_le hb.opkEntries_le
            sessions_le          := Nat.le_succ_of_le hb.sessions_le
            usedSendSessions_le  := Nat.le_succ_of_le hb.usedSendSessions_le
            usedRecvOPK_le       := Nat.le_succ_of_le hb.usedRecvOPK_le
            usedRecvNoOPK_le     := Nat.le_succ_of_le hb.usedRecvNoOPK_le
            seenKyberBaseKeys_le := Nat.le_succ_of_le hb.seenKyberBaseKeys_le
            sentOPKEvents_le     := Nat.le_succ_of_le hb.sentOPKEvents_le
            sentNoOPKEvents_le   := Nat.le_succ_of_le hb.sentNoOPKEvents_le
            recvdOPKEvents_le    := Nat.le_succ_of_le hb.recvdOPKEvents_le
            recvdNoOPKEvents_le  := Nat.le_succ_of_le hb.recvdNoOPKEvents_le
            advKeys_le           := Nat.le_succ_of_le hb.advKeys_le },
          rfl, rfl, rfl⟩

private theorem shcrGenSpk_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (xL : (Ty.prod .nat .nat).denote)
    (hroom : ∀ k, authSimPred S k t → c k + 1 ≤ authSimBounds b k)
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    let F := AuthKindFuels.ofBudget S b
    let ρ_arm : Env [.prod .nat .nat, authShcrShadowStTy, (authCodec S).Q] :=
      .cons xL (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let env_old : Env [.prod .nat .nat, shcrStTy] :=
      Env.cons (t := .prod .nat .nat) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    let arm : Comp pqAtomicOps pqAuthPrimIface
        [.prod .nat .nat, authShcrShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authShcrShadowStTy) :=
      .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S F.K_on s x)
          (.pair (.fst .v1) .v0))
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))
    Prod.map id forgetShcr <$> arm.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
          (Γ₁ := [shcrStTy])
          (Γ₂ := [.prod .nat .nat, shcrStTy])
          .vz .vz).eval env_old ∧
    ∀ p ∈ support (arm.eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F ρ_arm env_old arm
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hb0 : AuthBaseValOnlineBounded (c 0) s0.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal s0.1).mp
      (hs1_1 ▸ hInv.shadow_ok.base_ok.online_le)
  obtain ⟨hc0On, _, _, _⟩ := hInv.counter_inv.online_step_bounds hOn hroom
  have hK : c 0 ≤ F.K_on := Nat.le_of_succ_le hc0On
  have hQ : c 0 ≤ b.q_total := Nat.le_trans hK (AuthKindFuels.K_on_le_q_total S b)
  let env_in : Env [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)] :=
    .cons xL (.cons s0 (.cons (s0, xL) .nil))
  have hArgProj :
      projVal (.prod shcrStTy (.prod .nat .nat))
        ((Expr.pair (.fst .v1) .v0 :
          Expr pqAtomicOps [.prod .nat .nat, authShcrShadowStTy, (authCodec S).Q]
            (embedTy (.prod shcrStTy (.prod .nat .nat)))).eval ρ_arm) = (s0, xL) := by
    change (projVal shcrStTy s'.1, xL) = (s0, xL); rfl
  have hWk :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
        (Γ₁ := [shcrStTy, .prod shcrStTy (.prod .nat .nat)])
        (Γ₂ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
        .zero .zero).eval env_in =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
        (Γ₁ := [shcrStTy])
        (Γ₂ := [.prod .nat .nat, shcrStTy])
        .vz .vz).eval env_old :=
    arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
      (Γ₁ := [shcrStTy]) (Γ₂ := [.prod .nat .nat, shcrStTy]) .vz .vz)
      (Γs₁ := [shcrStTy, .prod shcrStTy (.prod .nat .nat)])
      (Γs₂ := [shcrStTy])
      .zero .vz env_in env_old rfl rfl rfl rfl
  have hLift :
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S F.K_on s x)
        (.pair (.fst .v1) .v0)).eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
          (Γ₁ := [shcrStTy, .prod shcrStTy (.prod .nat .nat)])
          (Γ₂ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
          .zero .zero).eval env_in := by
    rw [liftAuthPrim1_eval, hArgProj]
    apply congrArg (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$> ·)
    rw [hs_letV_eval, hs_letV_eval]
    exact shcrGenSpkB_fuel_eq S F.K_on b.q_total
      (Γ₁ := [shcrStTy, .prod shcrStTy (.prod .nat .nat)])
      (Γ₂ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
      .zero .zero env_in hb0 hK hQ
  have hArm :
      arm.eval ρ_arm =
      (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
          (Γ₁ := [shcrStTy, .prod shcrStTy (.prod .nat .nat)])
          (Γ₂ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
          .zero .zero).eval env_in) >>=
        fun rs => pure ((rs.1, (rs.2, s'.2)) :
          (Ty.prod (authCodec S).R authShcrShadowStTy).denote) := by
    change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      _ _).eval ρ_arm >>= _ = _
    rw [hLift]
    rfl
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c t hOn hNotRo hNotRt
  constructor
  · rw [hArm, ← hWk]
    erw [bind_map_left, map_bind, map_eq_bind_pure_comp]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun r _ => ?_
    rw [oc_map_pure]
    rfl
  · intro p hp
    rw [hArm] at hp
    erw [bind_map_left, mem_support_bind_iff] at hp
    rcases hp with ⟨r, hr, hp'⟩
    erw [mem_support_pure_iff] at hp'
    subst hp'
    obtain ⟨hb1, hRoEq, hRtEq, hr2Eq⟩ :=
      shcrGenSpkB_preserves S b.q_total
        (Γ₁ := [shcrStTy, .prod shcrStTy (.prod .nat .nat)])
        (Γ₂ := [.prod .nat .nat, shcrStTy, .prod shcrStTy (.prod .nat .nat)])
        .zero .zero env_in hb0 r hr
    have hRoEq' : valRoCache r.2.1 = valRoCache s0.1 := hRoEq
    have hRtEq' : valRootRoCache r.2.1 = valRootRoCache s0.1 := hRtEq
    have hr2Eq' : r.2.2 = s0.2 := hr2Eq
    have hRoA : atomRoCache (embedVal shcrStTy r.2).1 = atomRoCache s'.1.1 := by
      change atomRoCache (embedVal authStateTy r.2.1) = _
      rw [hs1_1, atomRoCache_embedVal, atomRoCache_embedVal, hRoEq']
    have hRtA : atomRootRoCache (embedVal shcrStTy r.2).1 = atomRootRoCache s'.1.1 := by
      change atomRootRoCache (embedVal authStateTy r.2.1) = _
      rw [hs1_1, atomRootRoCache_embedVal, atomRootRoCache_embedVal, hRtEq']
    have hs2Eq : (embedVal shcrStTy r.2).2 = s'.1.2 := by
      have : r.2 = (r.2.1, s0.2) := Prod.ext rfl hr2Eq'
      rw [this, hs1]
      rfl
    refine ⟨hInv.counter_inv.bump t hroom, ?_⟩
    rw [hc0, hc1, hc2]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (AuthBaseAtomOnlineBounded.iff_embedVal r.2.1).mpr hb1
    · change (atomRoCache (embedVal shcrStTy r.2).1).length ≤ (c 0 + 1) + c 1
      rw [hRoA]; exact Nat.le_trans hInv.shadow_ok.base_ok.ro_len_le (by omega)
    · change (atomRootRoCache (embedVal shcrStTy r.2).1).length ≤ (c 0 + 1) + c 2
      rw [hRtA]; exact Nat.le_trans hInv.shadow_ok.base_ok.root_len_le (by omega)
    · exact RoBothShadowRel.of_cache_eq hInv.shadow_ok.base_ok.ro_shadow hRoA hRtA
    · change (embedVal shcrStTy r.2).2.2.2.2.2.1.length ≤ c 0 + 1
      rw [hs2Eq]; exact Nat.le_trans hInv.shadow_ok.ir_le (Nat.le_succ (c 0))
    · change (embedVal shcrStTy r.2).2.2.2.2.2.2.1.length ≤ c 0 + 1
      rw [hs2Eq]; exact Nat.le_trans hInv.shadow_ok.rr_le (Nat.le_succ (c 0))

private theorem ro_map_bind_eq {S : Setup} {ι : Type} {T : OracleSpec ι}
    (m : OracleComp T _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS.denote)
    (s' : authShcrShadowStTy.denote) (s0 : shcrStTy.denote)
    (hs1_2 : s'.1.2 = (embedVal shcrStTy s0).2) :
    ((embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$> m) >>= fun rs =>
      pure ((rs.1, (rs.2, s'.1.2)) :
        (Ty.prod (authCodec S).R (embedTy shcrStTy)).denote)) =
    embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
      (m >>= fun r =>
        pure ((r.1, (r.2, s0.2)) :
          _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote)) := by
  erw [bind_map_left, map_bind]
  refine OracleComp.bind_congr_of_forall_mem_support m fun r _ => ?_
  rw [oc_map_pure]
  exact congrArg pure (Prod.ext rfl (Prod.ext rfl hs1_2))

private theorem lhs_ro_bind_eq {S : Setup} {ι : Type} {T : OracleSpec ι}
    (m0 : OracleComp T
      (Ty.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
        authBaseShadowStTy).denote)
    (s' : authShcrShadowStTy.denote) :
    (Prod.map id forgetShcr <$> (m0 >>= fun q =>
      pure ((q.1, ((q.2.1, s'.1.2), q.2.2)) :
        (Ty.prod (authCodec S).R authShcrShadowStTy).denote))) =
    (Prod.map id forgetAuthBaseShadow <$> m0) >>= fun rs =>
      pure ((rs.1, (rs.2, s'.1.2)) :
        (Ty.prod (authCodec S).R (embedTy shcrStTy)).denote) := by
  erw [map_bind, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support m0 fun q _ => ?_
  rw [oc_map_pure]
  rfl

private theorem ro_arm_lhs_eq_rhs (S : Setup) {ι : Type} {T : OracleSpec ι}
    {m0 : OracleComp T
      (Ty.prod Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authRespAtomicTy
        authBaseShadowStTy).denote}
    {mL : OracleComp T _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS.denote}
    {mOn : OracleComp T _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote}
    (s' : authShcrShadowStTy.denote) (s0 : shcrStTy.denote)
    (hs1_2 : s'.1.2 = (embedVal shcrStTy s0).2)
    (hLeg : Prod.map id forgetAuthBaseShadow <$> m0 =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$> mL)
    (hOnBase : mOn = mL >>= fun r =>
      pure ((r.1, (r.2, s0.2)) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote)) :
    (Prod.map id forgetShcr <$> (m0 >>= fun q =>
      pure ((q.1, ((q.2.1, s'.1.2), q.2.2)) :
        (Ty.prod (authCodec S).R authShcrShadowStTy).denote))) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$> mOn := by
  refine (lhs_ro_bind_eq (S := S) m0 s').trans ?_
  refine ((congrArg (fun m => m >>= fun rs =>
      pure ((rs.1, (rs.2, s'.1.2)) :
        (Ty.prod (authCodec S).R (embedTy shcrStTy)).denote)) hLeg).trans
    (ro_map_bind_eq (S := S) mL s' s0 hs1_2)).trans ?_
  exact congrArg (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$> ·) hOnBase.symm

set_option linter.constructorNameAsVariable false in
private theorem shcrRoArm_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (sec : (PB 192).denote)
    (hroom : ∀ k, authSimPred S k (.roQuery sec) → c k + 1 ≤ authSimBounds b k)
    (hInv : AuthShcrInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let ρ_arm : Env [PB 192, authShcrShadowStTy, (authCodec S).Q] :=
      Env.cons (t := PB 192) sec (.cons s' (.cons ((authCodec S).qenc (.roQuery sec)) .nil))
    let env_old : Env [B 192, shcrStTy] :=
      Env.cons (t := B 192) sec (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    let arm : Comp pqAtomicOps pqAuthPrimIface
        [PB 192, authShcrShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authShcrShadowStTy) :=
      .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.roBaseShadowArmC
          aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
        (.ret (.pair (.fst .v0)
          (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0)))))
    Prod.map id forgetShcr <$> arm.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
          (Γ₁ := [shcrStTy])
          .vz (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total g
            (Var.zero : Var [B 192, shcrStTy] (B 192)))).eval env_old ∧
    ∀ p ∈ support (arm.eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c (.roQuery sec)) p.2 := by
  intro F ρ_arm env_old arm
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hs1_2 : s'.1.2 = (embedVal shcrStTy s0).2 := by rw [hs1]
  have hRo : authSimPred S 1 (.roQuery sec) := trivial
  obtain ⟨hRoK, hRoQ, hKCap⟩ := hInv.counter_inv.ro_step_bounds hRo hroom
  have hOld : (c 0 + c 1) + 1 ≤ b.q_total := by omega
  have hCap : (c 0 + c 1) + 1 ≤ F.K_cap := by dsimp only [F]; omega
  obtain ⟨hRoMap, hRoSup⟩ :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.roBaseShadowArmC_sim
      S b (.pair (.fst (.fst .v1)) (.snd .v1)) .v0 ρ_arm (shcrShadowBase s') sec
      rfl rfl hInv.shadow_ok.base_ok hOld hCap
  let arm0 := Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.roBaseShadowArmC
    aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap
    (Γ := [PB 192, authShcrShadowStTy, (authCodec S).Q])
    (.pair (.fst (.fst .v1)) (.snd .v1)) .v0
  let env_baseA : Env (embedCtx [authStateTy, B 192]) :=
    Env.cons (t := embedTy authStateTy) (shcrShadowBase s').1 (Env.cons (t := PB 192) sec .nil)
  let env_baseL : Env [authStateTy, B 192] :=
    Env.cons (t := authStateTy) s0.1 (Env.cons (t := B 192) sec .nil)
  have hLeg :
      (mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
          (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192])
          .zero .zero)).eval env_baseA =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
          (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192])
          .zero .zero).eval env_baseL := by
    have hEnvA : env_baseA = embedEnv env_baseL := by
      change Env.cons (t := embedTy authStateTy) s'.1.1 (Env.cons (t := PB 192) sec .nil) =
        Env.cons (t := embedTy authStateTy) (embedVal authStateTy s0.1) (Env.cons (t := PB 192) sec .nil)
      rw [hs1_1]
    rw [hEnvA, mapComp_tlAuthPrim_eval_embed]
  have hRoLeg :
      Prod.map id forgetAuthBaseShadow <$> arm0.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
          (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192])
          .zero .zero).eval env_baseL :=
    hRoMap.trans hLeg
  have hWk :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
        (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192])
        .zero .zero).eval env_baseL =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
        (Γ₁ := [authStateTy, B 192, shcrStTy])
        (Γ₂ := [B 192, shcrStTy])
        .zero .zero).eval (Env.cons (t := authStateTy) s0.1 env_old) :=
    twoBaseRen_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
        (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192]) .zero .zero)
      .zero (.succ .zero) .zero (.succ .zero)
      env_baseL (Env.cons (t := authStateTy) s0.1 env_old) rfl rfl rfl rfl
  have hOnBase :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
        (Γ₁ := [shcrStTy])
        .vz (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total g
          (Var.zero : Var [B 192, shcrStTy] (B 192)))).eval env_old =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total
        (Γ₁ := [authStateTy, B 192]) (Γ₂ := [B 192]) (Δ := [authStateTy, B 192])
        .zero .zero).eval env_baseL >>=
        fun r => pure ((r.1, (r.2, s0.2)) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) := by
    unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
    rw [hs_bindV_eval, hs_letV_eval]
    have hSc : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v
          (Var.zero : Var [shcrStTy] shcrStTy))).eval env_old =
        s0.1 := rfl
    rw [hSc, ← hWk]
    rfl
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_ro_slots c (.roQuery sec) nofun hRo nofun
  have hArm : arm.eval ρ_arm =
      arm0.eval ρ_arm >>= fun q =>
        pure ((q.1, ((q.2.1, s'.1.2), q.2.2)) :
          (Ty.prod (authCodec S).R authShcrShadowStTy).denote) := by
    dsimp only [arm, F, Comp.eval]
    exact congrArg (arm0.eval ρ_arm >>= ·) (funext fun _ => rfl)
  constructor
  · exact (congrArg (Prod.map id forgetShcr <$> ·) hArm).trans
      (ro_arm_lhs_eq_rhs S (m0 := arm0.eval ρ_arm) s' s0 hs1_2 hRoLeg hOnBase)
  · intro p hp
    rw [hArm] at hp
    change _ at hRoSup
    generalize hm0 : arm0.eval ρ_arm = m0 at hp hRoSup
    clear hm0
    erw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    erw [mem_support_pure_iff] at hp'
    subst hp'
    have hSh1 := hRoSup q hq
    refine ⟨hInv.counter_inv.bump (.roQuery sec) hroom, ?_⟩
    rw [hc0, hc1, hc2]
    have hAdd : c 0 + (c 1 + 1) = (c 0 + c 1) + 1 := by omega
    rw [hAdd]
    exact ⟨hSh1, hInv.shadow_ok.ir_le, hInv.shadow_ok.rr_le⟩

set_option linter.constructorNameAsVariable false in
private theorem shcrRoRootArm_sim (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (rk dh : (PB 32).denote)
    (hroom : ∀ k, authSimPred S k (.roRootQuery rk dh) → c k + 1 ≤ authSimBounds b k)
    (hInv : AuthShcrInv S b c s') :
    let F := AuthKindFuels.ofBudget S b
    let inp : ((PB 32).prod (PB 32)).denote := (rk, dh)
    let ρ_arm : Env [.prod (PB 32) (PB 32), authShcrShadowStTy, (authCodec S).Q] :=
      Env.cons (t := .prod (PB 32) (PB 32)) inp (.cons s' (.cons ((authCodec S).qenc (.roRootQuery rk dh)) .nil))
    let env_old : Env [.prod (B 32) (B 32), shcrStTy] :=
      Env.cons (t := .prod (B 32) (B 32)) inp (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    let arm : Comp pqAtomicOps pqAuthPrimIface
        [.prod (PB 32) (PB 32), authShcrShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authShcrShadowStTy) :=
      .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.roRootBaseShadowArmC
          aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
        (.ret (.pair (.fst .v0)
          (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0)))))
    Prod.map id forgetShcr <$> arm.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
          (Γ₁ := [shcrStTy])
          .vz (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total g
            (Var.zero : Var [.prod (B 32) (B 32), shcrStTy]
              (.prod (B 32) (B 32))))).eval env_old ∧
    ∀ p ∈ support (arm.eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c (.roRootQuery rk dh)) p.2 := by
  intro F inp ρ_arm env_old arm
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hs1_2 : s'.1.2 = (embedVal shcrStTy s0).2 := by rw [hs1]
  have hRt : authSimPred S 2 (.roRootQuery rk dh) := trivial
  obtain ⟨hRtK, hRtQ, hKCap⟩ := hInv.counter_inv.roRoot_step_bounds hRt hroom
  have hOld : (c 0 + c 2) + 1 ≤ b.q_total := by omega
  have hCap : (c 0 + c 2) + 1 ≤ F.K_cap := by dsimp only [F]; omega
  obtain ⟨hRtMap, hRtSup⟩ :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimRo.roRootBaseShadowArmC_sim
      S b (.pair (.fst (.fst .v1)) (.snd .v1)) .v0 ρ_arm (shcrShadowBase s') inp
      rfl rfl hInv.shadow_ok.base_ok hOld hCap
  let arm0 := Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.roRootBaseShadowArmC
    aiAuthPrim (AuthKindFuels.ofBudget S b).K_cap
    (Γ := [.prod (PB 32) (PB 32), authShcrShadowStTy, (authCodec S).Q])
    (.pair (.fst (.fst .v1)) (.snd .v1)) .v0
  let env_baseA : Env (embedCtx [authStateTy, .prod (B 32) (B 32)]) :=
    Env.cons (t := embedTy authStateTy) (shcrShadowBase s').1 (Env.cons (t := .prod (PB 32) (PB 32)) inp .nil)
  let env_baseL : Env [authStateTy, .prod (B 32) (B 32)] :=
    Env.cons (t := authStateTy) s0.1 (Env.cons (t := .prod (B 32) (B 32)) inp .nil)
  have hLeg :
      (mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
          (Γ₁ := [authStateTy, .prod (B 32) (B 32)]) (Γ₂ := [.prod (B 32) (B 32)])
          (Δ := [authStateTy, .prod (B 32) (B 32)]) .zero .zero)).eval env_baseA =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
          (Γ₁ := [authStateTy, .prod (B 32) (B 32)]) (Γ₂ := [.prod (B 32) (B 32)])
          (Δ := [authStateTy, .prod (B 32) (B 32)]) .zero .zero).eval env_baseL := by
    have hEnvA : env_baseA = embedEnv env_baseL := by
      change Env.cons (t := embedTy authStateTy) s'.1.1 (Env.cons (t := .prod (PB 32) (PB 32)) inp .nil) =
        Env.cons (t := embedTy authStateTy) (embedVal authStateTy s0.1) (Env.cons (t := .prod (PB 32) (PB 32)) inp .nil)
      rw [hs1_1]
    rw [hEnvA, mapComp_tlAuthPrim_eval_embed]
  have hRtLeg :
      Prod.map id forgetAuthBaseShadow <$> arm0.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
          (Γ₁ := [authStateTy, .prod (B 32) (B 32)]) (Γ₂ := [.prod (B 32) (B 32)])
          (Δ := [authStateTy, .prod (B 32) (B 32)]) .zero .zero).eval env_baseL :=
    hRtMap.trans hLeg
  have hWk :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
        (Γ₁ := [authStateTy, .prod (B 32) (B 32)]) (Γ₂ := [.prod (B 32) (B 32)])
        (Δ := [authStateTy, .prod (B 32) (B 32)]) .zero .zero).eval env_baseL =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
        (Γ₁ := [authStateTy, .prod (B 32) (B 32), shcrStTy])
        (Γ₂ := [.prod (B 32) (B 32), shcrStTy])
        .zero .zero).eval (Env.cons (t := authStateTy) s0.1 env_old) :=
    twoBaseRen_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
        (Γ₁ := [authStateTy, .prod (B 32) (B 32)]) (Γ₂ := [.prod (B 32) (B 32)])
        (Δ := [authStateTy, .prod (B 32) (B 32)]) .zero .zero)
      .zero (.succ .zero) .zero (.succ .zero)
      env_baseL (Env.cons (t := authStateTy) s0.1 env_old) rfl rfl rfl rfl
  have hOnBase :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
        (Γ₁ := [shcrStTy])
        .vz (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total g
          (Var.zero : Var [.prod (B 32) (B 32), shcrStTy]
            (.prod (B 32) (B 32))))).eval env_old =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total
        (Γ₁ := [authStateTy, .prod (B 32) (B 32)]) (Γ₂ := [.prod (B 32) (B 32)])
        (Δ := [authStateTy, .prod (B 32) (B 32)]) .zero .zero).eval env_baseL >>=
        fun r => pure ((r.1, (r.2, s0.2)) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) := by
    unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
    rw [hs_bindV_eval, hs_letV_eval]
    have hSc : (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scBase
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v
          (Var.zero : Var [shcrStTy] shcrStTy))).eval env_old =
        s0.1 := rfl
    rw [hSc, ← hWk]
    rfl
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_roRoot_slots c (.roRootQuery rk dh) nofun nofun hRt
  have hArm : arm.eval ρ_arm =
      arm0.eval ρ_arm >>= fun q =>
        pure ((q.1, ((q.2.1, s'.1.2), q.2.2)) :
          (Ty.prod (authCodec S).R authShcrShadowStTy).denote) := by
    dsimp only [arm, F, Comp.eval]
    exact congrArg (arm0.eval ρ_arm >>= ·) (funext fun _ => rfl)
  constructor
  · exact (congrArg (Prod.map id forgetShcr <$> ·) hArm).trans
      (ro_arm_lhs_eq_rhs S (m0 := arm0.eval ρ_arm) s' s0 hs1_2 hRtLeg hOnBase)
  · intro p hp
    rw [hArm] at hp
    change _ at hRtSup
    generalize hm0 : arm0.eval ρ_arm = m0 at hp hRtSup
    clear hm0
    erw [mem_support_bind_iff] at hp
    rcases hp with ⟨q, hq, hp'⟩
    erw [mem_support_pure_iff] at hp'
    subst hp'
    have hSh1 := hRtSup q hq
    refine ⟨hInv.counter_inv.bump (.roRootQuery rk dh) hroom, ?_⟩
    rw [hc0, hc1, hc2]
    have hAdd : c 0 + (c 2 + 1) = (c 0 + c 2) + 1 := by omega
    rw [hAdd]
    exact ⟨hSh1, hInv.shadow_ok.ir_le, hInv.shadow_ok.rr_le⟩

private theorem shcrSendKC_fuel_eq (S : Setup) (b : QueryBudget) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hOnK : n ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hRoK : (valRoCache (env.get (h₁.wk s)).1).length ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hRtK : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ (AuthKindFuels.ofBudget S b).K_ro) :
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrSendKC
      S (AuthKindFuels.ofBudget S b).K_on (AuthKindFuels.ofBudget S b).K_ro opk s x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S b.q_total opk s x).eval env := by
  let F := AuthKindFuels.ofBudget S b
  have hOnQ : n ≤ b.q_total := Nat.le_trans hOnK (AuthKindFuels.K_on_le_q_total S b)
  have hRoQ : (valRoCache (env.get (h₁.wk s)).1).length ≤ b.q_total :=
    Nat.le_trans hRoK (AuthKindFuels.K_ro_le_q_total S b)
  have hRtQ : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ b.q_total :=
    Nat.le_trans hRtK (AuthKindFuels.K_ro_le_q_total S b)
  unfold Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs.shcrSendKC
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC
  apply hs_ite_congr rfl rfl
  refine hs_letV_congr_eq rfl fun st hst => ?_
  have hst' : st = (env.get (h₁.wk s)).1 := hst
  have hbSt : AuthBaseValOnlineBounded n st := hst' ▸ hb
  apply hs_bindV_congr
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.preCheckC_fuel_eq
      S b opk (Γ₁ := authStateTy :: Δ) .zero x (.cons st env) hbSt hOnK
  intro pc
  apply hs_caseOptV_congr rfl rfl; intro d
  refine hs_bindV_congr rfl fun ekSk =>
    hs_bindV_congr rfl fun coins =>
    hs_bindV_congr rfl fun ephSk =>
    hs_bindV_congr rfl fun spqrCoins =>
    hs_letV_congr rfl fun bu => ?_
  apply hs_bindV_congr
  · exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.checkSigsC_fuel_eq
      S b (Γ₁ := authStateTy :: Δ)
      (Var.zero : Var (authStateTy :: Δ) authStateTy)
      .zero _ hbSt hOnK
  intro ok
  apply hs_ite_congr rfl rfl
  refine hs_bindV_congr rfl fun enc => ?_
  apply hs_caseOptV_congr rfl rfl; intro sc
  refine hs_letV_congr rfl fun ks => ?_
  refine hs_bindV_congr ?_ fun out => rfl
  exact shcrFinishSendKC_fuel_eq F.K_on F.K_ro b.q_total
    (Γ₁ := authStateTy :: Δ)
    (Γ₂ := pauseTy :: .opt pauseTy :: authStateTy :: Δ)
    .zero .zero .zero .zero _
    hbSt hOnK hOnQ (hst' ▸ hRoK) (hst' ▸ hRoQ) (hst' ▸ hRtK) (hst' ▸ hRtQ)

private theorem shcrSendC_preserves (S : Setup) (Q : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hRoQ : (valRoCache (env.get (h₁.wk s)).1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ Q)
    (hIR : (env.get (h₁.wk s)).2.2.2.2.2.1.length ≤ n)
    (hRR : (env.get (h₁.wk s)).2.2.2.2.2.2.1.length ≤ n) :
    ∀ rs ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S Q opk s x).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2.1 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk s)).1) (valRoCache rs.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk s)).1) (valRootRoCache rs.2.1) ∧
      (rs.2).2.2.2.2.2.1.length ≤ n + 1 ∧
      (rs.2).2.2.2.2.2.2.1.length ≤ n + 1 := by
  set s0 := env.get (h₁.wk s)
  have hNoop : AuthBaseValOnlineBounded (n + 1) s0.1 ∧
      CacheStepAtMostOne (valRoCache s0.1) (valRoCache s0.1) ∧
      CacheStepAtMostOne (valRootRoCache s0.1) (valRootRoCache s0.1) ∧
      s0.2.2.2.2.2.1.length ≤ n + 1 ∧
      s0.2.2.2.2.2.2.1.length ≤ n + 1 :=
    ⟨hb.mono (Nat.le_succ n), CacheStepAtMostOne.refl _, CacheStepAtMostOne.refl _,
      Nat.le_trans hIR (Nat.le_succ n), Nat.le_trans hRR (Nat.le_succ n)⟩
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC
  refine support_hs_ite (fun _ => support_hs_ret hNoop) fun _ =>
    support_hs_letV fun st hst =>
    support_hs_bindV_any fun pc =>
    support_hs_caseOptV (support_hs_ret hNoop) fun d =>
    support_hs_bindV_any fun ekSk =>
    support_hs_bindV_any fun coins =>
    support_hs_bindV_any fun ephSk =>
    support_hs_bindV_any fun spqrCoins =>
    support_hs_letV_any fun bu =>
    support_hs_bindV_any fun ok =>
    support_hs_ite (fun _ => support_hs_ret hNoop) fun _ =>
    support_hs_bindV_any fun enc =>
    support_hs_caseOptV (support_hs_ret hNoop) fun sc =>
    support_hs_letV_any fun ks =>
    support_hs_bindV fun out hout => ?_
  have hst' : st = s0.1 := hst
  have hFin := finishC_preserves Q
    (Γ₁ := authStateTy :: Δ)
    (Γ₂ := pauseTy :: .opt pauseTy :: authStateTy :: Δ)
    .zero .zero .zero .zero _
    (hst' ▸ hb) (hst' ▸ hRoQ) (hst' ▸ hRtQ) out hout
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrFinC
  intro y hy
  rw [hs_letV_eval, hs_caseOptV_eval] at hy
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Comp.eval, Expr.eval,
    ext_step_wk, ext_refl_wk, env_cons_get_succ, env_cons_get_zero] at hy ⊢
  cases hopt : out.2 with
  | none =>
      rw [hopt] at hy
      simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hNoop
  | some b' =>
      rw [hopt] at hy hFin
      simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      rcases hFin with ⟨hb', hRoS, hRtS⟩
      exact ⟨hb', hst' ▸ hRoS, hst' ▸ hRtS,
        Nat.succ_le_succ hIR, Nat.le_trans hRR (Nat.le_succ n)⟩

private theorem shcrSyncArm_sim (S : Setup) (b : QueryBudget) {arg : Ty pqSig}
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S) (xL : arg.denote)
    (stepK stepRef :
      ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
        Var Γ₁ shcrStTy → Var Γ₂ arg →
        Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t)
    (hFuel :
      (stepK (Γ₁ := [shcrStTy, .prod shcrStTy arg])
             (Γ₂ := [arg, shcrStTy, .prod shcrStTy arg])
             (Δ := [arg, shcrStTy, .prod shcrStTy arg]) .zero .zero).eval
        (.cons xL (.cons (projVal shcrStTy s'.1) (.cons (projVal shcrStTy s'.1, xL) .nil))) =
      (stepRef (Γ₁ := [shcrStTy, .prod shcrStTy arg])
               (Γ₂ := [arg, shcrStTy, .prod shcrStTy arg])
               (Δ := [arg, shcrStTy, .prod shcrStTy arg]) .zero .zero).eval
        (.cons xL (.cons (projVal shcrStTy s'.1) (.cons (projVal shcrStTy s'.1, xL) .nil))))
    (hWk :
      (stepRef (Γ₁ := [shcrStTy, .prod shcrStTy arg])
               (Γ₂ := [arg, shcrStTy, .prod shcrStTy arg])
               (Δ := [arg, shcrStTy, .prod shcrStTy arg]) .zero .zero).eval
        (.cons xL (.cons (projVal shcrStTy s'.1) (.cons (projVal shcrStTy s'.1, xL) .nil))) =
      (stepRef (Γ₁ := [shcrStTy])
               (Γ₂ := [arg, shcrStTy])
               (Δ := [arg, shcrStTy])
               .vz .vz).eval
        (Env.cons (t := arg) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)))
    (hPres : ∀ rL ∈ support
        ((stepRef (Γ₁ := [shcrStTy, .prod shcrStTy arg])
                  (Γ₂ := [arg, shcrStTy, .prod shcrStTy arg])
                  (Δ := [arg, shcrStTy, .prod shcrStTy arg]) .zero .zero).eval
          (.cons xL (.cons (projVal shcrStTy s'.1) (.cons (projVal shcrStTy s'.1, xL) .nil)))),
      AuthBaseValOnlineBounded (c 0 + 1) rL.2.1 ∧
      CacheStepAtMostOne (valRoCache (projVal shcrStTy s'.1).1) (valRoCache rL.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (projVal shcrStTy s'.1).1) (valRootRoCache rL.2.1) ∧
      (rL.2).2.2.2.2.2.1.length ≤ c 0 + 1 ∧
      (rL.2).2.2.2.2.2.2.1.length ≤ c 0 + 1) :
    let F := AuthKindFuels.ofBudget S b
    let ρ_arm : Env [embedTy arg, authShcrShadowStTy, (authCodec S).Q] :=
      .cons (embedVal arg xL) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let env_old : Env [arg, shcrStTy] :=
      Env.cons (t := arg) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    let arm : Comp pqAtomicOps pqAuthPrimIface
        [embedTy arg, authShcrShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authShcrShadowStTy) :=
      .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
           stepK s x)
          (.pair (.fst .v1) .v0))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          F.K_cap .v0 (.snd .v2))
    Prod.map id forgetShcr <$> arm.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (stepRef (Γ₁ := [shcrStTy])
                 (Γ₂ := [arg, shcrStTy])
                 .vz .vz).eval env_old ∧
    ∀ p ∈ support (arm.eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F ρ_arm env_old arm
  let scsTy : Ty pqSig := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hRoLen0 : (valRoCache s0.1).length ≤ c 0 + c 1 := by
    have h := hInv.shadow_ok.base_ok.ro_len_le
    change (atomRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRoCache_embedVal] at h
  have hRtLen0 : (valRootRoCache s0.1).length ≤ c 0 + c 2 := by
    have h := hInv.shadow_ok.base_ok.root_len_le
    change (atomRootRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRootRoCache_embedVal] at h
  obtain ⟨_, hcRo1, hcRt1, hKCap⟩ := hInv.counter_inv.online_step_bounds hOn hroom
  obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c t hOn hNotRo hNotRt
  let env_in : Env [arg, shcrStTy, .prod shcrStTy arg] :=
    .cons xL (.cons s0 (.cons (s0, xL) .nil))
  let c_leg := Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
     _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
     stepK s x)
    (Γ := [embedTy arg, authShcrShadowStTy, (authCodec S).Q])
    (.pair (.fst .v1) .v0)
  have hArgProj :
      projVal (.prod shcrStTy arg)
        ((Expr.pair (.fst .v1) .v0 :
          Expr pqAtomicOps [embedTy arg, authShcrShadowStTy, (authCodec S).Q]
            (embedTy (.prod shcrStTy arg))).eval ρ_arm) = (s0, xL) := by
    change (projVal shcrStTy s'.1, projVal arg (embedVal arg xL)) = (s0, xL)
    rw [Computational.Proofs.SignalPqxdh.AtomicLift.projVal_embedVal]
  have hc_leg :
      c_leg.eval ρ_arm =
      embedVal scsTy <$>
        (stepRef (Γ₁ := [shcrStTy, .prod shcrStTy arg])
                 (Γ₂ := [arg, shcrStTy, .prod shcrStTy arg])
                 (Δ := [arg, shcrStTy, .prod shcrStTy arg]) .zero .zero).eval env_in := by
    rw [liftAuthPrim1_eval, hArgProj]
    apply congrArg (embedVal scsTy <$> ·)
    rw [hs_letV_eval, hs_letV_eval]
    exact hFuel
  have hSync := syncShcrShadowRespC_bind_sim F.K_cap s' c_leg (.snd .v2) ρ_arm
    hInv.shadow_ok.base_ok.ro_shadow (fun _ => rfl) (by
      intro rs hrs
      rw [hc_leg, support_map, Set.mem_image] at hrs
      rcases hrs with ⟨rL, hrL, rfl⟩
      obtain ⟨_, hRoS, hRtS, _, _⟩ := hPres rL hrL
      have hRoA0 : atomRoCache s'.1.1 = valRoCache s0.1 := by rw [hs1_1, atomRoCache_embedVal]
      have hRtA0 : atomRootRoCache s'.1.1 = valRootRoCache s0.1 := by
        rw [hs1_1, atomRootRoCache_embedVal]
      have hRoA1 : atomRoCache (embedVal scsTy rL).2.1 = valRoCache rL.2.1 :=
        atomRoCache_embedVal rL.2.1
      have hRtA1 : atomRootRoCache (embedVal scsTy rL).2.1 = valRootRoCache rL.2.1 :=
        atomRootRoCache_embedVal rL.2.1
      have hRoS' : CacheStepAtMostOne (valRoCache s0.1) (valRoCache rL.2.1) := hRoS
      have hRtS' : CacheStepAtMostOne (valRootRoCache s0.1) (valRootRoCache rL.2.1) := hRtS
      have hRoL := hRoS'.length_le
      have hRtL := hRtS'.length_le
      rw [hRoA0, hRtA0, hRoA1, hRtA1]
      exact ⟨hRoS', hRtS', by dsimp only [F]; omega, by dsimp only [F]; omega⟩)
  constructor
  · exact hSync.1.trans (hc_leg.trans (congrArg (embedVal scsTy <$> ·) hWk))
  · intro p hp
    obtain ⟨rs, hrs, _, hrs2, hRel'⟩ := hSync.2 p hp
    rw [hc_leg, support_map, Set.mem_image] at hrs
    rcases hrs with ⟨rL, hrL, rfl⟩
    obtain ⟨hb1, hRoS, hRtS, hIR1, hRR1⟩ := hPres rL hrL
    have hp21 : p.2.1 = embedVal shcrStTy rL.2 := hrs2
    have hp211 : p.2.1.1 = embedVal authStateTy rL.2.1 := by rw [hp21]; rfl
    have hRoS' : CacheStepAtMostOne (valRoCache s0.1) (valRoCache rL.2.1) := hRoS
    have hRtS' : CacheStepAtMostOne (valRootRoCache s0.1) (valRootRoCache rL.2.1) := hRtS
    have hRoL := hRoS'.length_le
    have hRtL := hRtS'.length_le
    refine ⟨hInv.counter_inv.bump t hroom, ?_⟩
    rw [hc0, hc1, hc2]
    refine ⟨⟨?_, ?_, ?_, hRel'⟩, ?_, ?_⟩
    · change AuthBaseAtomOnlineBounded (c 0 + 1) p.2.1.1
      rw [hp211]
      exact (AuthBaseAtomOnlineBounded.iff_embedVal rL.2.1).mpr hb1
    · change (atomRoCache p.2.1.1).length ≤ (c 0 + 1) + c 1
      rw [hp211, atomRoCache_embedVal]; omega
    · change (atomRootRoCache p.2.1.1).length ≤ (c 0 + 1) + c 2
      rw [hp211, atomRootRoCache_embedVal]; omega
    · have hEq : p.2.1.2.2.2.2.2.1.length = (rL.2).2.2.2.2.2.1.length := by
        rw [hp21]; exact List.length_map _
      omega
    · have hEq : p.2.1.2.2.2.2.2.2.1.length = (rL.2).2.2.2.2.2.2.1.length := by
        rw [hp21]; exact List.length_map _
      omega

set_option maxRecDepth 4096 in
private theorem shcrSendC_env_eq (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy)
    [h₁ : Ext Γ₁ (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ)]
    (env : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K opk s
      (Var.zero : Var (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy :: Δ) _)).eval env =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K opk
      (Γ₁ := [shcrStTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy])
      .vz .vz).eval
      (Env.cons (t := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy) (env.get .zero)
        (Env.cons (t := shcrStTy) (env.get (h₁.wk s)) .nil)) := by
  cases opk with
  | false =>
    exact arm2_wk_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K false
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy]) .vz .vz)
      (Γs₂ := [shcrStTy]) s .vz env
      (Env.cons (t := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy) (env.get .zero)
        (Env.cons (t := shcrStTy) (env.get (h₁.wk s)) .nil))
      rfl rfl rfl rfl
  | true =>
    exact arm2_wk_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S K true
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy]) .vz .vz)
      (Γs₂ := [shcrStTy]) s .vz env
      (Env.cons (t := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy) (env.get .zero)
        (Env.cons (t := shcrStTy) (env.get (h₁.wk s)) .nil))
      rfl rfl rfl rfl

private theorem shcrAcceptB_env_eq (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy)
    [h₁ : Ext Γ₁ (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ)]
    (env : Env (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K opk s
      (Var.zero : Var (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy :: Δ) _)).eval env =
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K opk
      (Γ₁ := [shcrStTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy, shcrStTy])
      .vz .vz).eval
      (Env.cons (t := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy) (env.get .zero)
        (Env.cons (t := shcrStTy) (env.get (h₁.wk s)) .nil)) := by
  cases opk with
  | false =>
    exact arm2_wk_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K false
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy, shcrStTy]) .vz .vz)
      (Γs₂ := [shcrStTy]) s .vz env
      (Env.cons (t := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy) (env.get .zero)
        (Env.cons (t := shcrStTy) (env.get (h₁.wk s)) .nil))
      rfl rfl rfl rfl
  | true =>
    exact arm2_wk_eval
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S K true
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy, shcrStTy]) .vz .vz)
      (Γs₂ := [shcrStTy]) s .vz env
      (Env.cons (t := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy) (env.get .zero)
        (Env.cons (t := shcrStTy) (env.get (h₁.wk s)) .nil))
      rfl rfl rfl rfl

private theorem shcrSend_arm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (xL : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy.denote)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    let F := AuthKindFuels.ofBudget S b
    let sQTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy
    let ρ_arm : Env [embedTy sQTy, authShcrShadowStTy, (authCodec S).Q] :=
      .cons (embedVal sQTy xL) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let env_old : Env [sQTy, shcrStTy] :=
      Env.cons (t := sQTy) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    let arm : Comp pqAtomicOps pqAuthPrimIface
        [embedTy sQTy, authShcrShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authShcrShadowStTy) :=
      .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
           Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
             S F.K_on F.K_ro opk s x)
          (.pair (.fst .v1) .v0))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          F.K_cap .v0 (.snd .v2))
    Prod.map id forgetShcr <$> arm.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S b.q_total opk
          (Γ₁ := [shcrStTy]) (Γ₂ := [sQTy, shcrStTy]) .vz .vz).eval env_old ∧
    ∀ p ∈ support (arm.eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F sQTy ρ_arm env_old arm
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hb0 : AuthBaseValOnlineBounded (c 0) s0.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal s0.1).mp
      (hs1_1 ▸ hInv.shadow_ok.base_ok.online_le)
  have hRoLen0 : (valRoCache s0.1).length ≤ c 0 + c 1 := by
    have h := hInv.shadow_ok.base_ok.ro_len_le
    change (atomRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRoCache_embedVal] at h
  have hRtLen0 : (valRootRoCache s0.1).length ≤ c 0 + c 2 := by
    have h := hInv.shadow_ok.base_ok.root_len_le
    change (atomRootRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRootRoCache_embedVal] at h
  have hIR0 : s0.2.2.2.2.2.1.length ≤ c 0 := by
    have h := hInv.shadow_ok.ir_le
    have hEq : s'.1.2.2.2.2.2.1.length = s0.2.2.2.2.2.1.length := by
      rw [hs1]; exact List.length_map _
    omega
  have hRR0 : s0.2.2.2.2.2.2.1.length ≤ c 0 := by
    have h := hInv.shadow_ok.rr_le
    have hEq : s'.1.2.2.2.2.2.2.1.length = s0.2.2.2.2.2.2.1.length := by
      rw [hs1]; exact List.length_map _
    omega
  obtain ⟨hc0On, hcRo1, hcRt1, _⟩ := hInv.counter_inv.online_step_bounds hOn hroom
  have hOnK : c 0 ≤ F.K_on := Nat.le_of_succ_le hc0On
  have hRoK : (valRoCache s0.1).length ≤ F.K_ro := by dsimp only [F]; omega
  have hRtK : (valRootRoCache s0.1).length ≤ F.K_ro := by dsimp only [F]; omega
  have hRoQ : (valRoCache s0.1).length ≤ b.q_total :=
    Nat.le_trans hRoK (AuthKindFuels.K_ro_le_q_total S b)
  have hRtQ : (valRootRoCache s0.1).length ≤ b.q_total :=
    Nat.le_trans hRtK (AuthKindFuels.K_ro_le_q_total S b)
  exact shcrSyncArm_sim S b (arg := sQTy) c s' t xL
    (fun s x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
      S F.K_on F.K_ro opk s x)
    (fun s x => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S b.q_total opk s x)
    hroom hInv hOn hNotRo hNotRt
    (shcrSendKC_fuel_eq S b opk
      (Γ₁ := [shcrStTy, .prod shcrStTy sQTy])
      (Γ₂ := [sQTy, shcrStTy, .prod shcrStTy sQTy]) .zero .zero _ hb0 hOnK hRoK hRtK)
    (shcrSendC_env_eq S b.q_total opk
      (Γ₁ := [shcrStTy, .prod shcrStTy sQTy]) .zero _)
    (shcrSendC_preserves S b.q_total opk
      (Γ₁ := [shcrStTy, .prod shcrStTy sQTy])
      (Γ₂ := [sQTy, shcrStTy, .prod shcrStTy sQTy]) .zero .zero _ hb0 hRoQ hRtQ hIR0 hRR0)

private theorem shcrAcceptB_preserves_c0 (S : Setup) (Q : ℕ) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk s)).1)
    (hRoQ : (valRoCache (env.get (h₁.wk s)).1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₁.wk s)).1).length ≤ Q)
    (hIR : (env.get (h₁.wk s)).2.2.2.2.2.1.length ≤ n)
    (hRR : (env.get (h₁.wk s)).2.2.2.2.2.2.1.length ≤ n) :
    ∀ rs ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S Q opk s x).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2.1 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁.wk s)).1) (valRoCache rs.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁.wk s)).1) (valRootRoCache rs.2.1) ∧
      (rs.2).2.2.2.2.2.1.length ≤ n + 1 ∧
      (rs.2).2.2.2.2.2.2.1.length ≤ n + 1 := fun rs hrs =>
  let ⟨hb1, hRoS, hRtS, hIREq, hRRLe⟩ :=
    shcrAcceptB_preserves S Q opk s x env hb hRoQ hRtQ rs hrs
  ⟨hb1, hRoS, hRtS,
    Nat.le_trans (Nat.le_of_eq (congrArg List.length hIREq)) (Nat.le_trans hIR (Nat.le_succ n)),
    Nat.le_trans hRRLe (Nat.succ_le_succ hRR)⟩

private theorem shcrAccept_arm_sim (S : Setup) (b : QueryBudget) (opk : Bool)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (xL : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy.denote)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t)
    (hNotRo : ¬ authSimPred S 1 t)
    (hNotRt : ¬ authSimPred S 2 t) :
    let F := AuthKindFuels.ofBudget S b
    let rQTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy
    let ρ_arm : Env [embedTy rQTy, authShcrShadowStTy, (authCodec S).Q] :=
      .cons (embedVal rQTy xL) (.cons s' (.cons ((authCodec S).qenc t) .nil))
    let env_old : Env [rQTy, shcrStTy] :=
      Env.cons (t := rQTy) xL (Env.cons (t := shcrStTy) (projVal shcrStTy s'.1) .nil)
    let arm : Comp pqAtomicOps pqAuthPrimIface
        [embedTy rQTy, authShcrShadowStTy, (authCodec S).Q]
        (.prod (authCodec S).R authShcrShadowStTy) :=
      .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
           Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrAcceptKB
             S F.K_on F.K_ro opk s x)
          (.pair (.fst .v1) .v0))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          F.K_cap .v0 (.snd .v2))
    Prod.map id forgetShcr <$> arm.eval ρ_arm =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S b.q_total opk
          (Γ₁ := [shcrStTy]) (Γ₂ := [rQTy, shcrStTy]) .vz .vz).eval env_old ∧
    ∀ p ∈ support (arm.eval ρ_arm),
      AuthShcrInv S b (bumpPred (authSimPred S) c t) p.2 := by
  intro F rQTy ρ_arm env_old arm
  let s0 := projVal shcrStTy s'.1
  have hs1 : s'.1 = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hb0 : AuthBaseValOnlineBounded (c 0) s0.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal s0.1).mp
      (hs1_1 ▸ hInv.shadow_ok.base_ok.online_le)
  have hRoLen0 : (valRoCache s0.1).length ≤ c 0 + c 1 := by
    have h := hInv.shadow_ok.base_ok.ro_len_le
    change (atomRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRoCache_embedVal] at h
  have hRtLen0 : (valRootRoCache s0.1).length ≤ c 0 + c 2 := by
    have h := hInv.shadow_ok.base_ok.root_len_le
    change (atomRootRoCache s'.1.1).length ≤ _ at h
    rwa [hs1_1, atomRootRoCache_embedVal] at h
  have hIR0 : s0.2.2.2.2.2.1.length ≤ c 0 := by
    have h := hInv.shadow_ok.ir_le
    have hEq : s'.1.2.2.2.2.2.1.length = s0.2.2.2.2.2.1.length := by
      rw [hs1]; exact List.length_map _
    omega
  have hRR0 : s0.2.2.2.2.2.2.1.length ≤ c 0 := by
    have h := hInv.shadow_ok.rr_le
    have hEq : s'.1.2.2.2.2.2.2.1.length = s0.2.2.2.2.2.2.1.length := by
      rw [hs1]; exact List.length_map _
    omega
  obtain ⟨hc0On, hcRo1, hcRt1, _⟩ := hInv.counter_inv.online_step_bounds hOn hroom
  have hOnK : c 0 ≤ F.K_on := Nat.le_of_succ_le hc0On
  have hRoK : (valRoCache s0.1).length ≤ F.K_ro := by dsimp only [F]; omega
  have hRtK : (valRootRoCache s0.1).length ≤ F.K_ro := by dsimp only [F]; omega
  have hRoQ : (valRoCache s0.1).length ≤ b.q_total :=
    Nat.le_trans hRoK (AuthKindFuels.K_ro_le_q_total S b)
  have hRtQ : (valRootRoCache s0.1).length ≤ b.q_total :=
    Nat.le_trans hRtK (AuthKindFuels.K_ro_le_q_total S b)
  exact shcrSyncArm_sim S b (arg := rQTy) c s' t xL
    (fun s x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrAcceptKB
      S F.K_on F.K_ro opk s x)
    (fun s x => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S b.q_total opk s x)
    hroom hInv hOn hNotRo hNotRt
    (shcrAcceptKB_fuel_eq S b opk
      (Γ₁ := [shcrStTy, .prod shcrStTy rQTy])
      (Γ₂ := [rQTy, shcrStTy, .prod shcrStTy rQTy]) .zero .zero _ hb0 hOnK hRoK hRtK)
    (shcrAcceptB_env_eq S b.q_total opk
      (Γ₁ := [shcrStTy, .prod shcrStTy rQTy]) .zero _)
    (shcrAcceptB_preserves_c0 S b.q_total opk
      (Γ₁ := [shcrStTy, .prod shcrStTy rQTy])
      (Γ₂ := [rQTy, shcrStTy, .prod shcrStTy rQTy]) .zero .zero _ hb0 hRoQ hRtQ hIR0 hRR0)

private theorem post_sim_congr {ι : Type} {T : OracleSpec ι} {A B C : Type}
    {m₁ m₂ : OracleComp T A} {n₁ n₂ : OracleComp T B}
    {f : A → C} {g : B → C} {P : A → Prop}
    (hm : m₁ = m₂) (hn : n₁ = n₂)
    (h : f <$> m₂ = g <$> n₂ ∧ ∀ p ∈ support m₂, P p) :
    f <$> m₁ = g <$> n₁ ∧ ∀ p ∈ support m₁, P p := by
  rw [hm, hn]; exact h

private theorem revealDh_pure_sim (S : Setup) {ι : Type} {T : OracleSpec ι}
    (s' : authShcrShadowStTy.denote) (s0 : shcrStTy.denote)
    (hs1 : s'.1 = embedVal shcrStTy s0) :
    Prod.map id forgetShcr <$>
        (pure ((.inl (), s') : (Ty.prod (authCodec S).R authShcrShadowStTy).denote) :
          OracleComp T (Ty.prod (authCodec S).R authShcrShadowStTy).denote) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (pure ((.inl (), s0) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) :
          OracleComp T _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) := by
  have h1 := oc_map_pure (spec := T) (Prod.map id forgetShcr)
    ((.inl (), s') : (Ty.prod (authCodec S).R authShcrShadowStTy).denote)
  have h2 := oc_map_pure (spec := T) (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS)
    ((.inl (), s0) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote)
  have hEq : Prod.map id forgetShcr
      ((.inl (), s') : (Ty.prod (authCodec S).R authShcrShadowStTy).denote) =
    embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
      ((.inl (), s0) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) :=
    Prod.ext rfl hs1
  exact h1.trans ((congrArg pure hEq).trans h2.symm)

private theorem shcr_hPost (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s') :
    Prod.map id forgetShcr <$>
        (shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (shcrOldAtomicProg S b).handlePost.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) ∧
    ∀ p ∈ support
        ((shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))),
      AuthShcrInv S b (bumpPred (authSimPred S) c t) p.2 := by
  let _ := hc
  let F := AuthKindFuels.ofBudget S b
  let scsTy : Ty pqSig := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
  let s0 := projVal shcrStTy s'.1
  have hs0 : forgetShcr s' = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hs1 : s'.1 = embedVal shcrStTy s0 := hs0
  have hs1_1 : s'.1.1 = embedVal authStateTy s0.1 := by rw [hs1]; rfl
  have hb0 : AuthBaseValOnlineBounded (c 0) s0.1 :=
    (AuthBaseAtomOnlineBounded.iff_embedVal s0.1).mp
      (hs1_1 ▸ hInv.shadow_ok.base_ok.online_le)
  have hZero : ∀ g, tlAuthPrim.unsupportedW g = 0 := fun g => by cases g <;> rfl
  have hOldPost :
      (shcrOldAtomicProg S b).handlePost.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal scsTy <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
          (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
          (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
          (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
          (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) := by
    dsimp only [shcrOldAtomicProg, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key]
    rw [hs0]
    exact liftAuthHandle_eval tlAuthPrim S hZero _ s0 t
  rw [hOldPost]
  let Γs := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]
  cases t with
  | initPrin u =>
      obtain ⟨hc0On, _, _, _⟩ :=
        hInv.counter_inv.online_step_bounds (t := .initPrin u) trivial hroom
      have hOnK : c 0 ≤ F.K_on := Nat.le_of_succ_le hc0On
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.initPrin u)) .nil)) =
          (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
            (S := S) (arg := .nat)
            (fun st x =>
              Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.initPrin1KeyKB
                F st x)).eval
            (.cons (embedVal .nat u.val)
              (.cons s' (.cons ((authCodec S).qenc (.initPrin u)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.initPrin u) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.initPrin u)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
            (Γ₁ := [shcrStTy]) .vz
            (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.initPrin1KeyB b.q_total g
              (Var.zero : Var [.nat, shcrStTy] .nat))).eval
            (Env.cons (t := .nat) u.val (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inl_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.initPrin1KeyB b.q_total g
            (Var.zero : Var [.nat, shcrStTy] .nat))
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld (shcrBaseArmC_sim S b (arg := .nat) c s' (.initPrin u) u.val
        (fun st x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.initPrin1KeyKB F st x)
        (fun st x => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.initPrin1KeyB b.q_total st x)
        hroom hInv trivial nofun nofun
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.initPrin1KeyKB_fuel_eq
          S b (Γ₁ := [authStateTy, .prod authStateTy .nat])
          (Γ₂ := [.nat, authStateTy, .prod authStateTy .nat]) .zero .zero _ hb0 hOnK)
        (twoBaseRen_eval
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.initPrin1KeyB b.q_total
            (Γ₁ := [authStateTy, .nat]) (Γ₂ := [.nat]) (Δ := [authStateTy, .nat]) .zero .zero)
          (.succ .zero) .zero .zero (.succ .zero) _ _ rfl rfl rfl rfl)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.initPrin1KeyB_preserves_online_ro
          b.q_total (Γ₁ := [authStateTy, .prod authStateTy .nat])
          (Γ₂ := [.nat, authStateTy, .prod authStateTy .nat]) .zero .zero _ hb0))
  | corruptIK u =>
      obtain ⟨hc0On, _, _, _⟩ :=
        hInv.counter_inv.online_step_bounds (t := .corruptIK u) trivial hroom
      have hOnK : c 0 ≤ F.K_on := Nat.le_of_succ_le hc0On
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.corruptIK u)) .nil)) =
          (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
            (S := S) (arg := .nat)
            (fun st x =>
              Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.corruptKB
                F st x)).eval
            (.cons (embedVal .nat u.val)
              (.cons s' (.cons ((authCodec S).qenc (.corruptIK u)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.corruptIK u) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.corruptIK u)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
            (Γ₁ := [shcrStTy]) .vz
            (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB b.q_total g
              (Var.zero : Var [.nat, shcrStTy] .nat))).eval
            (Env.cons (t := .nat) u.val (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB b.q_total g
            (Var.zero : Var [.nat, shcrStTy] .nat))
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld (shcrBaseArmC_sim S b (arg := .nat) c s' (.corruptIK u) u.val
        (fun st x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.corruptKB F st x)
        (fun st x => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB b.q_total st x)
        hroom hInv trivial nofun nofun
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.corruptKB_fuel_eq
          S b (Γ₁ := [authStateTy, .prod authStateTy .nat])
          (Γ₂ := [.nat, authStateTy, .prod authStateTy .nat]) .zero .zero _ hb0 hOnK)
        (twoBaseRen_eval
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB b.q_total
            (Γ₁ := [authStateTy, .nat]) (Γ₂ := [.nat]) (Δ := [authStateTy, .nat]) .zero .zero)
          (.succ .zero) .zero .zero (.succ .zero) _ _ rfl rfl rfl rfl)
        (fun r hr =>
          let ⟨hbN, hRo, hRt⟩ :=
            Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.corruptB_preserves_online_ro
              b.q_total (Γ₁ := [authStateTy, .prod authStateTy .nat])
              (Γ₂ := [.nat, authStateTy, .prod authStateTy .nat]) .zero .zero _ hb0 r hr
          ⟨hbN.mono (Nat.le_succ (c 0)), hRo, hRt⟩))
  | genSPK u j =>
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.genSPK u j)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
              (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
               _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
               _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S F.K_on s x)
              (.pair (.fst .v1) .v0))
            (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))).eval
            (.cons (u.val, j.val)
              (.cons s' (.cons ((authCodec S).qenc (.genSPK u j)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.genSPK u j) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.genSPK u j)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
            (Γ₁ := [shcrStTy])
            (Γ₂ := [.prod .nat .nat, shcrStTy])
            .vz .vz).eval
            (Env.cons (t := .prod .nat .nat) (u.val, j.val) (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inl_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S b.q_total
          (Γ₁ := [shcrStTy]) (Γ₂ := [.prod .nat .nat, shcrStTy]) .vz .vz)
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld
        (shcrGenSpk_sim S b c s' (.genSPK u j) (u.val, j.val) hroom hInv trivial nofun nofun)
  | genOPK u j o =>
      obtain ⟨hc0On, _, _, _⟩ :=
        hInv.counter_inv.online_step_bounds (t := .genOPK u j o) trivial hroom
      have hOnK : c 0 ≤ F.K_on := Nat.le_of_succ_le hc0On
      let argTy : Ty pqSig := .prod .nat (.prod .nat .nat)
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.genOPK u j o)) .nil)) =
          (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
            (S := S) (arg := argTy)
            (fun st x =>
              Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.genOpkKB
                F st x)).eval
            (.cons (embedVal argTy (u.val, (j.val, o.val)))
              (.cons s' (.cons ((authCodec S).qenc (.genOPK u j o)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.genOPK u j o) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.genOPK u j o)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
            (Γ₁ := [shcrStTy]) .vz
            (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB b.q_total g
              (Var.zero : Var [argTy, shcrStTy] argTy))).eval
            (Env.cons (t := argTy) (u.val, (j.val, o.val)) (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB b.q_total g
            (Var.zero : Var [argTy, shcrStTy] argTy))
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld (shcrBaseArmC_sim S b (arg := argTy) c s' (.genOPK u j o) (u.val, (j.val, o.val))
        (fun st x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.genOpkKB F st x)
        (fun st x => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB b.q_total st x)
        hroom hInv trivial nofun nofun
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.genOpkKB_fuel_eq
          S b (Γ₁ := [authStateTy, .prod authStateTy argTy])
          (Γ₂ := [argTy, authStateTy, .prod authStateTy argTy]) .zero .zero _ hb0 hOnK)
        (twoBaseRen_eval
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB b.q_total
            (Γ₁ := [authStateTy, argTy]) (Γ₂ := [argTy]) (Δ := [authStateTy, argTy]) .zero .zero)
          (.succ .zero) .zero .zero (.succ .zero) _ _ rfl rfl rfl rfl)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.genOpkB_preserves_online_ro
          b.q_total (Γ₁ := [authStateTy, .prod authStateTy argTy])
          (Γ₂ := [argTy, authStateTy, .prod authStateTy argTy]) .zero .zero _ hb0))
  | sendOPK u i bu m0 m1 =>
      let sQTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy
      let xL : sQTy.denote := (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.sendOPK u i bu m0 m1)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
              (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
               _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
               Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
                 S F.K_on F.K_ro true s x)
              (.pair (.fst .v1) .v0))
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
              F.K_cap .v0 (.snd .v2))).eval
            (.cons (embedVal sQTy xL)
              (.cons s' (.cons ((authCodec S).qenc (.sendOPK u i bu m0 m1)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.sendOPK u i bu m0 m1) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.sendOPK u i bu m0 m1)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S b.q_total true
            (Γ₁ := [shcrStTy])
            (Γ₂ := [sQTy, shcrStTy])
            .vz .vz).eval
            (Env.cons (t := sQTy) xL (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inl_eval _ _ _ rfl]
        exact shcrSendC_env_eq S b.q_total true (Γ₁ := Γs) .vz _
      exact post_sim_congr hKind hOld
        (shcrSend_arm_sim S b true c s' (.sendOPK u i bu m0 m1) xL hroom hInv trivial nofun nofun)
  | sendNoOPK u i bu m0 m1 =>
      let sQTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy
      let xL : sQTy.denote := (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.sendNoOPK u i bu m0 m1)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
              (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
               _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
               Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
                 S F.K_on F.K_ro false s x)
              (.pair (.fst .v1) .v0))
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
              F.K_cap .v0 (.snd .v2))).eval
            (.cons (embedVal sQTy xL)
              (.cons s' (.cons ((authCodec S).qenc (.sendNoOPK u i bu m0 m1)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.sendNoOPK u i bu m0 m1) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.sendNoOPK u i bu m0 m1)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrSendC S b.q_total false
            (Γ₁ := [shcrStTy])
            (Γ₂ := [sQTy, shcrStTy])
            .vz .vz).eval
            (Env.cons (t := sQTy) xL (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
        exact shcrSendC_env_eq S b.q_total false (Γ₁ := Γs) .vz _
      exact post_sim_congr hKind hOld
        (shcrSend_arm_sim S b false c s' (.sendNoOPK u i bu m0 m1) xL hroom hInv trivial nofun nofun)
  | recvOPK k j o msg =>
      let rQTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy
      let xL : rQTy.denote := (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.recvOPK k j o msg)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
              (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
               _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
               Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrAcceptKB
                 S F.K_on F.K_ro true s x)
              (.pair (.fst .v1) .v0))
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
              F.K_cap .v0 (.snd .v2))).eval
            (.cons (embedVal rQTy xL)
              (.cons s' (.cons ((authCodec S).qenc (.recvOPK k j o msg)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.recvOPK k j o msg) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.recvOPK k j o msg)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S b.q_total true
            (Γ₁ := [shcrStTy])
            (Γ₂ := [rQTy, shcrStTy])
            .vz .vz).eval
            (Env.cons (t := rQTy) xL (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inl_eval _ _ _ rfl]
        exact shcrAcceptB_env_eq S b.q_total true (Γ₁ := Γs) .vz _
      exact post_sim_congr hKind hOld
        (shcrAccept_arm_sim S b true c s' (.recvOPK k j o msg) xL hroom hInv trivial nofun nofun)
  | recvNoOPK k j l msg =>
      let rQTy := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy
      let xL : rQTy.denote := (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.preKeyMsgV msg)))
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.recvNoOPK k j l msg)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
              (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
               _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
               Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrAcceptKB
                 S F.K_on F.K_ro false s x)
              (.pair (.fst .v1) .v0))
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
              F.K_cap .v0 (.snd .v2))).eval
            (.cons (embedVal rQTy xL)
              (.cons s' (.cons ((authCodec S).qenc (.recvNoOPK k j l msg)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.recvNoOPK k j l msg) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.recvNoOPK k j l msg)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAcceptB S b.q_total false
            (Γ₁ := [shcrStTy])
            (Γ₂ := [rQTy, shcrStTy])
            .vz .vz).eval
            (Env.cons (t := rQTy) xL (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
        exact shcrAcceptB_env_eq S b.q_total false (Γ₁ := Γs) .vz _
      exact post_sim_congr hKind hOld
        (shcrAccept_arm_sim S b false c s' (.recvNoOPK k j l msg) xL hroom hInv trivial nofun nofun)
  | roQuery sec =>
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.roQuery sec)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.roBaseShadowArmC
              aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
            (.ret (.pair (.fst .v0)
              (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0)))))).eval
            (Env.cons (t := PB 192) sec (.cons s' (.cons ((authCodec S).qenc (.roQuery sec)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.roQuery sec) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.roQuery sec)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
            (Γ₁ := [shcrStTy]) .vz
            (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total g
              (Var.zero : Var [B 192, shcrStTy] (B 192)))).eval
            (Env.cons (t := B 192) sec (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inl_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roB b.q_total g
            (Var.zero : Var [B 192, shcrStTy] (B 192)))
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld (shcrRoArm_sim S b c s' sec hroom hInv)
  | roRootQuery rk dh =>
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.roRootQuery rk dh)) .nil)) =
          (Comp.bind
            (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.roRootBaseShadowArmC
              aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
            (.ret (.pair (.fst .v0)
              (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0)))))).eval
            (Env.cons (t := .prod (PB 32) (PB 32)) (rk, dh)
              (.cons s' (.cons ((authCodec S).qenc (.roRootQuery rk dh)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.roRootQuery rk dh) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.roRootQuery rk dh)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
            (Γ₁ := [shcrStTy]) .vz
            (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total g
              (Var.zero : Var [.prod (B 32) (B 32), shcrStTy]
                (.prod (B 32) (B 32))))).eval
            (Env.cons (t := .prod (B 32) (B 32)) (rk, dh) (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.roRootB b.q_total g
            (Var.zero : Var [.prod (B 32) (B 32), shcrStTy] _))
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld (shcrRoRootArm_sim S b c s' rk dh hroom hInv)
  | revealDhSecrets =>
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc .revealDhSecrets) .nil)) =
          pure ((.inl (), s') : (Ty.prod (authCodec S).R authShcrShadowStTy).denote) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ .revealDhSecrets rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc .revealDhSecrets) .nil)) =
          pure ((.inl (), s0) : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS.denote) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inl_eval _ _ _ rfl]
        rfl
      refine post_sim_congr hKind hOld ?_
      obtain ⟨hc0, hc1, hc2⟩ := bumpPred_online_slots c .revealDhSecrets trivial nofun nofun
      constructor
      · exact revealDh_pure_sim S s' s0 hs1
      · intro p hp
        erw [mem_support_pure_iff] at hp
        subst hp
        refine ⟨hInv.counter_inv.bump .revealDhSecrets hroom, ?_⟩
        rw [hc0, hc1, hc2]
        exact AuthShcrShadowAt.mono (Nat.le_succ (c 0)) (by omega) (by omega) hInv.shadow_ok
  | registerKey sk =>
      have hKind :
          (shcrAuth1KeyKindProg S b).handlePost.eval
            (.cons s' (.cons ((authCodec S).qenc (.registerKey sk)) .nil)) =
          (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrBaseArmC
            (S := S) (arg := B 32)
            (fun st x =>
              Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.registerKB
                st x)).eval
            (.cons (embedVal (B 32) sk)
              (.cons s' (.cons ((authCodec S).qenc (.registerKey sk)) .nil))) := by
        change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
          S F).eval _ = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.registerKey sk) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      have hOld :
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc (.registerKey sk)) .nil)) =
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase
            (Γ₁ := [shcrStTy]) .vz
            (fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB g
              (Var.zero : Var [B 32, shcrStTy] (B 32)))).eval
            (Env.cons (t := B 32) sk (Env.cons (t := shcrStTy) s0 .nil)) := by
        dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl]
        exact arm2_wk_eval (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.onBase (Γ₁ := [shcrStTy]) .vz
          fun g => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB g
            (Var.zero : Var [B 32, shcrStTy] _))
          (Γs₁ := Γs) (Γs₂ := [shcrStTy]) .vz .vz _ _ rfl rfl rfl rfl
      exact post_sim_congr hKind hOld (shcrBaseArmC_sim S b (arg := B 32) c s' (.registerKey sk) sk
        (fun st x => Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.registerKB st x)
        (fun st x => _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB st x)
        hroom hInv trivial nofun nofun
        rfl
        (twoBaseRen_eval
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB
            (Γ₁ := [authStateTy, B 32]) (Γ₂ := [B 32]) (Δ := [authStateTy, B 32]) .zero .zero)
          (.succ .zero) .zero .zero (.succ .zero) _ _ rfl rfl rfl rfl)
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms.registerKB_preserves_online_ro
          (Γ₁ := [authStateTy, .prod authStateTy (B 32)])
          (Γ₂ := [B 32, authStateTy, .prod authStateTy (B 32)]) .zero .zero _ hb0))

private theorem shcr_hPre_of_inl (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s')
    (hKindInl :
      (shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      Sum.inl <$>
        (shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)))
    (hNoPause :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC S b.q_total
        (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
        (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
        .vz .vz).eval
        (.cons (projVal shcrStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t :
            _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy.denote) .nil)) =
      pure none) :
    forgetPreOut id forgetShcr <$>
        (shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (shcrOldAtomicProg S b).handlePre.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) ∧
    (∀ v s'₁,
      .inl (v, s'₁) ∈ support
        ((shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthShcrInv S b (bumpPred (authSimPred S) c t) s'₁) ∧
    (∀ c_out p' s'₁,
      .inr (c_out, p', s'₁) ∈ support
        ((shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthShcrPauseInv S b (bumpPred (authSimPred S) c t) p' s'₁) := by
  have hPostSim := shcr_hPost S b c s' t hc hroom hInv
  have hZero : ∀ g, tlAuthPrim.unsupportedW g = 0 := fun g => by cases g <;> rfl
  let s0 := projVal shcrStTy s'.1
  let q0 : _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy.denote :=
    (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
  have hs0 : forgetShcr s' = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hOldPre :
      (shcrOldAtomicProg S b).handlePre.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal (.sum _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
        (.prod (B 1568) (.prod pauseTy shcrStTy))) <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPre1KeyC S b.q_total
          (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
          (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
          (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
          (.cons s0 (.cons q0 .nil)) := by
    dsimp only [shcrOldAtomicProg, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key]
    rw [hs0]
    exact liftAuthHandle_eval tlAuthPrim S hZero _ s0 t
  have hOldPost :
      (shcrOldAtomicProg S b).handlePost.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) =
      embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
          (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
          (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
          (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
          (.cons s0 (.cons q0 .nil)) := by
    dsimp only [shcrOldAtomicProg, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key]
    rw [hs0]
    exact liftAuthHandle_eval tlAuthPrim S hZero _ s0 t
  refine ⟨?_, ?_, ?_⟩
  · rw [hKindInl, hOldPre]
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPre1KeyC]
    rw [hs_bindV_eval, hNoPause, pure_bind, hs_caseOptV_none_eval _ _ _ _ rfl,
        hs_bindV_eval, shcrPost1KeyC_wk_eval S b.q_total none s0 t]
    trans (Sum.inl <$>
      (Prod.map id forgetShcr <$>
        (shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))))
    · exact forgetPreOut_map_inl id forgetShcr _
    · refine Eq.trans (congrArg (Sum.inl <$> ·) hPostSim.1) ?_
      rw [hOldPost]
      exact inl_map_embedVal_bind_eq _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
        (.prod (B 1568) (.prod pauseTy shcrStTy)) _ _ (fun _ => rfl)
  · intro vOut s'₁ hMem
    rw [hKindInl, map_eq_bind_pure_comp] at hMem
    erw [mem_support_bind_iff] at hMem
    rcases hMem with ⟨p, hp, hEq⟩
    dsimp only [Function.comp_def] at hEq
    erw [mem_support_pure_iff] at hEq
    cases hEq
    exact hPostSim.2 (vOut, s'₁) hp
  · intro cOut p' s'₁ hMem
    rw [hKindInl, map_eq_bind_pure_comp] at hMem
    erw [mem_support_bind_iff] at hMem
    rcases hMem with ⟨_, _, hEq⟩
    dsimp only [Function.comp_def] at hEq
    erw [mem_support_pure_iff] at hEq
    cases hEq

private def sendPostArmC (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqAtomicOps pqAuthPrimIface
      [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authSendQAtomicTy,
       authShcrShadowStTy, (authCodec S).Q]
      (.prod (authCodec S).R authShcrShadowStTy) :=
  .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
       Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
         S F.K_on F.K_ro opk s x)
      (.pair (.fst .v1) .v0))
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
      F.K_cap .v0 (.snd .v2))

private def sendPreArmC (S : Setup) (F : AuthKindFuels) (opk : Bool) :
    Comp pqAtomicOps pqAuthPrimIface
      [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authSendQAtomicTy,
       authShcrShadowStTy, (authCodec S).Q]
      (.sum (.prod (authCodec S).R authShcrShadowStTy)
        (.prod (PB 1568) (.prod (embedTy pauseTy) authShcrShadowStTy))) :=
  .bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV
         (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S F.K_on opk s x) fun p =>
       .ret (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt
         (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v p) .noneE fun d =>
         .someE (.pair (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.buPqspkB
           (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pdBu
             (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d)))
           (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d))))
      (.pair (.fst .v1) .v0))
    (.caseOpt .v0
      (.bind (.bind (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
           Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
             S F.K_on F.K_ro opk s x)
          (.pair (.fst .v2) .v1))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          F.K_cap .v0 (.snd .v3)))
        (.ret (.inl .v0)))
      (.ret (.inr (.pair (.fst .v0) (.pair (.snd .v0) .v3)))))

private theorem sendPre_none_eq_inl_sendPost (S : Setup) (F : AuthKindFuels) (opk : Bool)
    (optVal : (embedTy (.opt (.prod (B 1568) pauseTy))).denote)
    (x0' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK.authSendQAtomicTy.denote)
    (s' : authShcrShadowStTy.denote) (q' : (authCodec S).Q.denote) :
    (Comp.bind
      (Comp.bind
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
           _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
           Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
             S F.K_on F.K_ro opk s x)
          (.pair (.fst .v2) .v1))
        (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.syncShcrShadowRespC
          F.K_cap .v0 (.snd .v3)))
      (Comp.ret (.inl .v0) :
        Comp pqAtomicOps pqAuthPrimIface _
          (.sum (.prod (authCodec S).R authShcrShadowStTy)
            (.prod (PB 1568) (.prod (embedTy pauseTy) authShcrShadowStTy))))).eval
      (.cons optVal (.cons x0' (.cons s' (.cons q' .nil)))) =
    Sum.inl <$> (sendPostArmC S F opk).eval (.cons x0' (.cons s' (.cons q' .nil))) := by
  unfold sendPostArmC
  dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0]
  rw [map_eq_bind_pure_comp]
  dsimp only [Function.comp_def]
  refine congrArg (· >>= fun x => pure (Sum.inl x)) ?_
  have hLift :
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
           S F.K_on F.K_ro opk s x)
        (.pair (.fst .v2) .v1)).eval (.cons optVal (.cons x0' (.cons s' (.cons q' .nil)))) =
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrSendKC
           S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0)).eval (.cons x0' (.cons s' (.cons q' .nil))) := by
    rw [liftAuthPrim1_eval, liftAuthPrim1_eval]; rfl
  rw [hLift]
  exact OracleComp.bind_congr_of_forall_mem_support _ fun rs _ =>
    syncShcrShadowRespC_wk_eval F.K_cap rs optVal x0' s' (.cons q' .nil)

private theorem shcr_hPre_of_send (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (opk : Bool) (x0 : _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy.denote)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s')
    (hOn : authSimPred S 0 t) (hNotRo : ¬ authSimPred S 1 t) (hNotRt : ¬ authSimPred S 2 t)
    (hKindPre :
      (shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (sendPreArmC S (AuthKindFuels.ofBudget S b) opk).eval
        (.cons (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy x0)
          (.cons s' (.cons ((authCodec S).qenc t) .nil))))
    (hKindPost :
      (shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (sendPostArmC S (AuthKindFuels.ofBudget S b) opk).eval
        (.cons (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy x0)
          (.cons s' (.cons ((authCodec S).qenc t) .nil))))
    (hPauseQ :
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC S b.q_total
        (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
        (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
        .vz .vz).eval
        (.cons (projVal shcrStTy s'.1)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t :
            _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy.denote) .nil)) =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S b.q_total opk
        (Γ₁ := [shcrStTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy])
        .vz .vz).eval (.cons x0 (.cons (projVal shcrStTy s'.1) .nil))) :
    forgetPreOut id forgetShcr <$>
        (shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (shcrOldAtomicProg S b).handlePre.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) ∧
    (∀ v s'₁,
      .inl (v, s'₁) ∈ support
        ((shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthShcrInv S b (bumpPred (authSimPred S) c t) s'₁) ∧
    (∀ c_out p' s'₁,
      .inr (c_out, p', s'₁) ∈ support
        ((shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthShcrPauseInv S b (bumpPred (authSimPred S) c t) p' s'₁) := by
  let F := AuthKindFuels.ofBudget S b
  let s0 := projVal shcrStTy s'.1
  let q0 : _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy.denote :=
    (_root_.SignalPqxdh.LegacyCosted.authCodec S).qenc t
  let ρ : Env [authShcrShadowStTy, (authCodec S).Q] := .cons s' (.cons ((authCodec S).qenc t) .nil)
  let ρP : Env [(shcrAuth1KeyKindProg S b).σ, (authCodec S).Q] :=
    .cons s' (.cons ((authCodec S).qenc t) .nil)
  let ρ₁ := Env.cons (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy x0) ρ
  let pkOf (d : pauseTy.denote) : (B 1568).denote :=
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.buPqspkB
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pdBu
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v (Var.zero : Var [pauseTy] pauseTy)))).eval
      (.cons d .nil)
  let M_pause :=
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S b.q_total opk
      (Γ₁ := [shcrStTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy])
      .vz .vz).eval (.cons x0 (.cons s0 .nil))
  have hPostSim := shcr_hPost S b c s' t hc hroom hInv
  have hZero : ∀ g, tlAuthPrim.unsupportedW g = 0 := fun g => by cases g <;> rfl
  have hs0 : forgetShcr s' = embedVal shcrStTy s0 :=
    (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1).symm
  have hb0 : AuthBaseValOnlineBounded (c 0) s0.1 := by
    have hEmb : embedVal authStateTy s0.1 = s'.1.1 := by
      change (embedVal shcrStTy s0).1 = s'.1.1
      exact congrArg Prod.fst (Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal shcrStTy s'.1)
    exact (AuthBaseAtomOnlineBounded.iff_embedVal s0.1).mp (by rw [hEmb]; exact hInv.shadow_ok.base_ok.online_le)
  have hc0 : c 0 ≤ F.K_on := by
    have h := hInv.counter_inv.on_le
    dsimp only [F, AuthKindFuels.ofBudget]
    omega
  have hSendPreEval :
      (sendPreArmC S F opk).eval ρ₁ =
      (M_pause >>= fun p =>
        match p with
        | none => Sum.inl <$> (shcrAuth1KeyKindProg S b).handlePost.eval ρP
        | some d => pure (.inr (embedVal (B 1568) (pkOf d), (embedVal pauseTy d, s')))) := by
    unfold sendPreArmC
    dsimp only [Comp.eval]
    rw [liftAuthPrim1_eval]
    have hPairProj :
        projVal (.prod shcrStTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy)
          ((Expr.pair (.fst .v1) .v0 : Expr pqAtomicOps _ _).eval ρ₁) = (s0, x0) := by
      change (projVal shcrStTy s'.1,
        projVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy
          (embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy x0)) = (s0, x0)
      rw [Computational.Proofs.SignalPqxdh.AtomicLift.projVal_embedVal]
    rw [hPairProj, hs_letV_eval, hs_letV_eval, hs_bindV_eval]
    let ρ2 : Env [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy,
        shcrStTy, .prod shcrStTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy] :=
      .cons x0 (.cons s0 (.cons (s0, x0) .nil))
    change (embedVal (.opt (.prod (B 1568) pauseTy)) <$>
      ((_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S F.K_on opk
        (Γ₁ := [shcrStTy, .prod shcrStTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy, shcrStTy,
          .prod shcrStTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy])
        .zero .zero).eval ρ2 >>= _)) >>= _ = _
    rw [tryPauseC_fuel_eq S b opk .zero .zero ρ2 hb0 hc0,
        tryPauseC_env_eq S b.q_total opk .zero ρ2]
    refine map_bind_bind_congr (embedVal (.opt (.prod (B 1568) pauseTy))) M_pause _ _ _ fun p _ => ?_
    cases p with
    | none =>
      change (embedVal (.opt (.prod (B 1568) pauseTy)) <$> pure none) >>= _ = _
      rw [map_pure, pure_bind]
      dsimp only
      refine Eq.trans (sendPre_none_eq_inl_sendPost S F opk none _ _ _) ?_
      rw [← hKindPost]
      rfl
    | some d =>
      change (embedVal (.opt (.prod (B 1568) pauseTy)) <$> pure (some (pkOf d, d))) >>= _ = _
      rw [map_pure, pure_bind]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hKindPre, hSendPreEval]
    have hOldPre :
        (shcrOldAtomicProg S b).handlePre.eval
          (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) =
        embedVal (.sum _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
          (.prod (B 1568) (.prod pauseTy shcrStTy))) <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPre1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons q0 .nil)) := by
      dsimp only [shcrOldAtomicProg, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key]
      rw [hs0]
      exact liftAuthHandle_eval tlAuthPrim S hZero _ s0 t
    have hOldPost :
        (shcrOldAtomicProg S b).handlePost.eval
          (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) =
        embedVal _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPost1KeyC S b.q_total
            (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.authQueryTy])
            (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy]) .vz .vz).eval
            (.cons s0 (.cons q0 .nil)) := by
      dsimp only [shcrOldAtomicProg, Computational.Proofs.SignalPqxdh.AtomicLift.liftAuth2Stage,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrAuth1KeyDslProg,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg1Key]
      rw [hs0]
      exact liftAuthHandle_eval tlAuthPrim S hZero _ s0 t
    rw [hOldPre]
    dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrPre1KeyC]
    rw [hs_bindV_eval, hPauseQ]
    refine map_bind_congr (forgetPreOut id forgetShcr)
      (embedVal (.sum _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
        (.prod (B 1568) (.prod pauseTy shcrStTy))))
      M_pause _ _ fun p _ => ?_
    cases p with
    | none =>
      dsimp only
      rw [hs_caseOptV_none_eval _ _ _ _ rfl,
          hs_bindV_eval, shcrPost1KeyC_wk_eval S b.q_total none s0 t]
      dsimp only [ρP]
      trans (Sum.inl <$>
        (Prod.map id forgetShcr <$>
          (shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))))
      · exact forgetPreOut_map_inl id forgetShcr _
      · refine Eq.trans (congrArg (Sum.inl <$> ·) hPostSim.1) ?_
        rw [hOldPost]
        exact inl_map_embedVal_bind_eq _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
          (.prod (B 1568) (.prod pauseTy shcrStTy)) _ _ (fun _ => rfl)
    | some d =>
      dsimp only
      rw [hs_caseOptV_some_eval _ _ _ _ d rfl]
      refine Eq.trans (oc_map_pure (forgetPreOut id forgetShcr) _) ?_
      refine Eq.symm (Eq.trans (oc_map_pure
        (embedVal (.sum _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.SCS
          (.prod (B 1568) (.prod pauseTy shcrStTy))))
        (.inr (pkOf d, (d, s0)))) ?_)
      exact congrArg
        (fun z => pure (Sum.inr (embedVal (B 1568) (pkOf d), embedVal pauseTy d, z))) hs0.symm
  · intro vOut s'₁ hMem
    rw [hKindPre, hSendPreEval] at hMem
    erw [mem_support_bind_iff] at hMem
    rcases hMem with ⟨p, _, hMem⟩
    cases p with
    | none =>
      rw [map_eq_bind_pure_comp] at hMem
      erw [mem_support_bind_iff] at hMem
      rcases hMem with ⟨q, hq, hEq⟩
      dsimp only [Function.comp_def] at hEq
      erw [mem_support_pure_iff] at hEq
      cases hEq
      exact hPostSim.2 (vOut, s'₁) hq
    | some d =>
      erw [mem_support_pure_iff] at hMem
      cases hMem
  · intro cOut p' s'₁ hMem
    rw [hKindPre, hSendPreEval] at hMem
    erw [mem_support_bind_iff] at hMem
    rcases hMem with ⟨p, _, hMem⟩
    cases p with
    | none =>
      rw [map_eq_bind_pure_comp] at hMem
      erw [mem_support_bind_iff] at hMem
      rcases hMem with ⟨_, _, hEq⟩
      dsimp only [Function.comp_def] at hEq
      erw [mem_support_pure_iff] at hEq
      cases hEq
    | some d =>
      erw [mem_support_pure_iff] at hMem
      cases hMem
      exact shcr_pauseInv_of_online hInv hOn hNotRo hNotRt hroom

private theorem shcrKindHandlePre_eq_inl_post (S : Setup) (b : QueryBudget)
    (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (hNotSendOpk : ∀ u i bu m0 m1, t ≠ .sendOPK u i bu m0 m1)
    (hNotSendNoOpk : ∀ u i bu m0 m1, t ≠ .sendNoOPK u i bu m0 m1) :
    (shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
    Sum.inl <$>
      (shcrAuth1KeyKindProg S b).handlePost.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) := by
  let F := AuthKindFuels.ofBudget S b
  change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePreC
      S F).eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
    Sum.inl <$>
      (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
        S F).eval (.cons s' (.cons ((authCodec S).qenc t) .nil))
  dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePreC,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
  refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ t rfl _ _ _ _ _ _ _ _ _ _ _ _)
    (Eq.symm (Eq.trans (congrArg (Sum.inl <$> ·)
      (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ t rfl _ _ _ _ _ _ _ _ _ _ _ _)) ?_))
  cases t with
  | sendOPK u i bu m0 m1 => exact False.elim (hNotSendOpk u i bu m0 m1 rfl)
  | sendNoOPK u i bu m0 m1 => exact False.elim (hNotSendNoOpk u i bu m0 m1 rfl)
  | revealDhSecrets =>
      dsimp only [dispatchAuthQEval, authCodec, Comp.eval]
      exact oc_map_pure Sum.inl _
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _
  | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _ | registerKey _ =>
      dsimp only [dispatchAuthQEval, authCodec]
      exact (wrapInl_eval (S := S) _ _).symm

private theorem shcr_hPre (S : Setup) (b : QueryBudget)
    (c : Fin 4 → ℕ) (s' : authShcrShadowStTy.denote) (t : AuthQuery S)
    (hc : ∀ j, c j ≤ authSimBounds b j)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : AuthShcrInv S b c s') :
    forgetPreOut id forgetShcr <$>
        (shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil)) =
      (shcrOldAtomicProg S b).handlePre.eval
        (.cons (forgetShcr s') (.cons ((authCodec S).qenc t) .nil)) ∧
    (∀ v s'₁,
      .inl (v, s'₁) ∈ support
        ((shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthShcrInv S b (bumpPred (authSimPred S) c t) s'₁) ∧
    (∀ c_out p' s'₁,
      .inr (c_out, p', s'₁) ∈ support
        ((shcrAuth1KeyKindProg S b).handlePre.eval (.cons s' (.cons ((authCodec S).qenc t) .nil))) →
      AuthShcrPauseInv S b (bumpPred (authSimPred S) c t) p' s'₁) := by
  let F := AuthKindFuels.ofBudget S b
  cases t with
  | initPrin u =>
      refine shcr_hPre_of_inl S b c s' (.initPrin u) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.initPrin u) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inl_eval _ _ _ rfl]; rfl
  | corruptIK u =>
      refine shcr_hPre_of_inl S b c s' (.corruptIK u) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.corruptIK u) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]; rfl
  | genSPK u j =>
      refine shcr_hPre_of_inl S b c s' (.genSPK u j) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.genSPK u j) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inl_eval _ _ _ rfl]; rfl
  | genOPK u j o =>
      refine shcr_hPre_of_inl S b c s' (.genOPK u j o) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.genOPK u j o) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]; rfl
  | sendOPK u i bu m0 m1 =>
      refine shcr_hPre_of_send S b c s' (.sendOPK u i bu m0 m1) true
        (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
        hc hroom hInv trivial (fun h => False.elim h) (fun h => False.elim h) ?_ ?_ ?_
      · change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePreC
            S F).eval (.cons s' (.cons ((authCodec S).qenc (.sendOPK u i bu m0 m1)) .nil)) = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePreC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.sendOPK u i bu m0 m1) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      · change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
            S F).eval (.cons s' (.cons ((authCodec S).qenc (.sendOPK u i bu m0 m1)) .nil)) = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.sendOPK u i bu m0 m1) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      · dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inl_eval _ _ _ rfl]
        exact tryPauseC_env_eq S b.q_total true .vz _
  | sendNoOPK u i bu m0 m1 =>
      refine shcr_hPre_of_send S b c s' (.sendNoOPK u i bu m0 m1) false
        (u.val, (i.val, (_root_.SignalPqxdh.LegacyCosted.bundleV bu, (m0, m1))))
        hc hroom hInv trivial (fun h => False.elim h) (fun h => False.elim h) ?_ ?_ ?_
      · change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePreC
            S F).eval (.cons s' (.cons ((authCodec S).qenc (.sendNoOPK u i bu m0 m1)) .nil)) = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePreC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.sendNoOPK u i bu m0 m1) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      · change (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC
            S F).eval (.cons s' (.cons ((authCodec S).qenc (.sendNoOPK u i bu m0 m1)) .nil)) = _
        dsimp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms.shcrKindHandlePostC]
        refine Eq.trans (dispatchAuthQ_eval_qenc (.var (.succ .zero)) _ (.sendNoOPK u i bu m0 m1) rfl
          _ _ _ _ _ _ _ _ _ _ _ _) ?_
        dsimp only [dispatchAuthQEval]
        rw [Computational.Proofs.SignalPqxdh.AtomicLift.authQenc_eq]; rfl
      · dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
        rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
            hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inl_eval _ _ _ rfl]
        exact tryPauseC_env_eq S b.q_total false .vz _
  | recvOPK k j o msg =>
      refine shcr_hPre_of_inl S b c s' (.recvOPK k j o msg) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.recvOPK k j o msg) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl]; rfl
  | recvNoOPK k j l msg =>
      refine shcr_hPre_of_inl S b c s' (.recvNoOPK k j l msg) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.recvNoOPK k j l msg) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl]; rfl
  | roQuery sec =>
      refine shcr_hPre_of_inl S b c s' (.roQuery sec) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.roQuery sec) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl]; rfl
  | roRootQuery rk dh =>
      refine shcr_hPre_of_inl S b c s' (.roRootQuery rk dh) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.roRootQuery rk dh) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl]; rfl
  | revealDhSecrets =>
      refine shcr_hPre_of_inl S b c s' .revealDhSecrets hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' .revealDhSecrets (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl]; rfl
  | registerKey sk =>
      refine shcr_hPre_of_inl S b c s' (.registerKey sk) hc hroom hInv
        (shcrKindHandlePre_eq_inl_post S b s' (.registerKey sk) (fun _ _ _ _ _ => nofun) (fun _ _ _ _ _ => nofun)) ?_
      dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pauseCheckC]
      rw [hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl,
          hs_caseSumV_inr_eval _ _ _ rfl, hs_caseSumV_inr_eval _ _ _ rfl]; rfl

/-- Two-stage forgetful simulation from `shcrAuth1KeyKindProg` to `shcrOldAtomicProg`. -/
theorem shcrAuth1KeyKindProg_twoStageForgetSim
    (S : Setup) (b : QueryBudget) (x : ((PB 1568).prod (PB 3168)).denote) :
    TwoStageForgetSim (shcrAuth1KeyKindProg S b) (shcrOldAtomicProg S b)
      id forgetShcr (authSimPred S) (authSimBounds b) x
      (AuthShcrInv S b) (AuthShcrPauseInv S b) where
  hInit := shcr_hInit S b x
  hPre := shcr_hPre S b
  hChDone := shcr_hChDone S b
  hResume := shcr_hResume S b
  hPost := shcr_hPost S b
  hFinish := shcr_hFinish S b

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimShcr
