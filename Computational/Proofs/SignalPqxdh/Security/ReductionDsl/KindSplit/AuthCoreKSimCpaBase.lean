/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase

/-!
# Shared `AuthAeadCpa` Fuel and Preservation Lemmas

`tlAuthPrim` `mapComp` bridges, linear `AuthPrf` combinators, and fuel-equivalence and
support-preservation lemmas for `cpaInitC`, `finishCpaC`, and `cpaSendSlotKB`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpaBase

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedCtx embedEnv mapComp
   comp_queries_zero_of_zero mapComp_eval tlAuthPrim)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy preKeyBundleTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext authHybridStateFixedTy emptyAuthHybridStFixedE
   hkdfRoC rootRoC findHonestC
   koskBundleOkC koskSenderOkC checkBundleProvenanceExactC)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (cpaPayloadTy finishCpaC spkHonIdealFromPeerC cpaInitC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (AuthBaseValOnlineBounded AuthFixedValOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache
   CacheStepAtMostOne cpaPayloadRoCache cpaPayloadRootRoCache)

@[expose] def projEnv : {Γ : List (Ty pqSig)} → Env (embedCtx Γ) → Env Γ
  | [], .nil => .nil
  | t :: _, .cons y ρ => .cons (projVal t y) (projEnv ρ)

theorem embedEnv_projEnv :
    ∀ {Γ : List (Ty pqSig)} (ρ : Env (embedCtx Γ)), embedEnv (projEnv ρ) = ρ
  | [], .nil => rfl
  | t :: _, .cons y ρ => by
    simp [projEnv, embedEnv, embedEnv_projEnv ρ]

theorem tlAuthPrim_unsupported_zero :
    ∀ g, tlAuthPrim.unsupportedW g = 0 := fun _ => rfl

theorem mapComp_tlAuthPrim_eval_embed {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env Γ) :
    (mapComp tlAuthPrim c).eval (embedEnv ρ) = embedVal t <$> c.eval ρ :=
  mapComp_eval tlAuthPrim c (comp_queries_zero_of_zero tlAuthPrim_unsupported_zero c) ρ

theorem mapComp_tlAuthPrim_eval {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env (embedCtx Γ)) :
    (mapComp tlAuthPrim c).eval ρ = embedVal t <$> c.eval (projEnv ρ) := by
  conv_lhs => rw [← embedEnv_projEnv ρ]
  exact mapComp_tlAuthPrim_eval_embed c (projEnv ρ)

theorem mapComp_tlAuthPrim_congr {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c₁ c₂ : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env (embedCtx Γ))
    (h : c₁.eval (projEnv ρ) = c₂.eval (projEnv ρ)) :
    (mapComp tlAuthPrim c₁).eval ρ = (mapComp tlAuthPrim c₂).eval ρ := by
  rw [mapComp_tlAuthPrim_eval, mapComp_tlAuthPrim_eval, h]

theorem mem_support_mapComp_tlAuthPrim {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) (ρ : Env (embedCtx Γ)) (y : (embedTy t).denote)
    (hy : y ∈ support ((mapComp tlAuthPrim c).eval ρ)) :
    ∃ x ∈ support (c.eval (projEnv ρ)), y = embedVal t x := by
  rw [mapComp_tlAuthPrim_eval] at hy
  simp only [support_map, Set.mem_image] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

theorem atomRoCache_embedVal (st : authStateTy.denote) :
    atomRoCache (embedVal authStateTy st) = valRoCache st := by
  change List.map (embedVal (.prod (B 192) _)) (valRoCache st) = valRoCache st
  have hid : embedVal (.prod (B 192) (.prod (B 32) (.prod (B 32) (B 32)))) = id := by
    funext ⟨k, a, b, c⟩
    rfl
  simp [hid]

theorem atomRootRoCache_embedVal (st : authStateTy.denote) :
    atomRootRoCache (embedVal authStateTy st) = valRootRoCache st := by
  change List.map (embedVal (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))
    (valRootRoCache st) = valRootRoCache st
  have hid : embedVal (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))) = id := by
    funext ⟨⟨k1, k2⟩, v1, v2⟩
    rfl
  simp [hid]

theorem cpaPayloadRoCache_embedVal (p : cpaPayloadTy.denote) :
    cpaPayloadRoCache (embedVal cpaPayloadTy p) = p.2.2.2.2.2.2.2.2.2.2.2.2.1 := by
  change List.map (embedVal (.prod (B 192) _)) p.2.2.2.2.2.2.2.2.2.2.2.2.1 =
    p.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hid : embedVal (.prod (B 192) (.prod (B 32) (.prod (B 32) (B 32)))) = id := by
    funext ⟨k, a, b, c⟩
    rfl
  simp [hid]

theorem cpaPayloadRootRoCache_embedVal (p : cpaPayloadTy.denote) :
    cpaPayloadRootRoCache (embedVal cpaPayloadTy p) = p.2.2.2.2.2.2.2.2.2.2.2.2.2 := by
  change List.map (embedVal (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))
    p.2.2.2.2.2.2.2.2.2.2.2.2.2 = p.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hid : embedVal (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))) = id := by
    funext ⟨⟨k1, k2⟩, v1, v2⟩
    rfl
  simp [hid]

theorem take_eq_of_length_le {α : Type} {l : List α} {K Q : ℕ}
    (hK : l.length ≤ K) (hQ : l.length ≤ Q) :
    l.take K = l.take Q := by
  rw [List.take_of_length_le hK, List.take_of_length_le hQ]

theorem take_min_eq_of_length_le {α : Type} {l : List α} {K Q N : ℕ}
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

theorem prf_letV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e k).eval ρ =
      (k .zero).eval (.cons (e.eval ρ) ρ) := by
  simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.eval]

theorem prf_bindV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV m k).eval ρ =
      (m.eval ρ >>= fun x => (k .zero).eval (.cons x ρ)) :=
  rfl

theorem prf_caseOptV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV o kn ks).eval ρ =
      match o.eval ρ with
      | none => kn.eval ρ
      | some x => (ks .zero).eval (.cons x ρ) := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV, Comp.eval]
  cases o.eval ρ <;> rfl

theorem prf_eFind_eq {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (ρ : Env Γ)
    (hK : (xs.eval ρ).length ≤ K) (hQ : (xs.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind K xs p).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind Q xs p).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eFind, Expr.eval,
    take_eq_of_length_le hK hQ]

theorem prf_eAny_eq {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (ρ : Env Γ)
    (hK : (xs.eval ρ).length ≤ K) (hQ : (xs.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eAny K xs p).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eAny Q xs p).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eAny, Expr.eval,
    take_eq_of_length_le hK hQ]

theorem prf_eMap_eq {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (K Q : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (ρ : Env Γ)
    (hK : (xs.eval ρ).length ≤ K) (hQ : (xs.eval ρ).length ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eMap K xs f).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eMap Q xs f).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eMap, Expr.eval,
    take_eq_of_length_le hK hQ]

theorem prf_findMV_min_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K Q N : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) (ρ : Env Γ)
    (hL : (xs.eval ρ).length ≤ K) (hKQ : K ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.findMV (min K N) xs p).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.findMV (min Q N) xs p).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.findMV, Comp.eval,
    take_min_eq_of_length_le hL hKQ]

theorem prf_anyMV_min_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K Q N : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) (ρ : Env Γ)
    (hL : (xs.eval ρ).length ≤ K) (hKQ : K ≤ Q) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.anyMV (min K N) xs p).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.anyMV (min Q N) xs p).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.anyMV, Comp.eval,
    take_min_eq_of_length_le hL hKQ]

theorem findHonestC_prf_fuel_eq (S : Setup) (K Q : ℕ) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hK : n ≤ K) (hKQ : K ≤ Q) :
    (findHonestC S K st ik).eval env = (findHonestC S Q st ik).eval env :=
  AuthCoreKSimPrfBase.findHonestC_prf_fuel_eq S st ik env hb hK (Nat.le_trans hK hKQ)

theorem prf_letV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e₁ e₂ : Expr pqxdhOps Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (he : e₁.eval ρ = e₂.eval ρ)
    (hk : ∀ x, (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e₂ k₂).eval ρ := by
  rw [prf_letV_eval, prf_letV_eval, he, hk]

theorem prf_letV_congr_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e₁ e₂ : Expr pqxdhOps Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (he : e₁.eval ρ = e₂.eval ρ)
    (hk : ∀ x, x = e₁.eval ρ → (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e₂ k₂).eval ρ := by
  rw [prf_letV_eval, prf_letV_eval, ← he]
  exact hk (e₁.eval ρ) rfl

theorem prf_bindV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m₁ m₂ : Comp pqxdhOps I Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (hm : m₁.eval ρ = m₂.eval ρ)
    (hk : ∀ x, (k₁ .zero).eval (.cons x ρ) = (k₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV m₁ k₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV m₂ k₂).eval ρ := by
  rw [prf_bindV_eval, prf_bindV_eval, hm]
  congr 1; funext x; exact hk x

theorem prf_ite_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    {c₁ c₂ : Expr pqxdhOps Γ .bool} {t₁ t₂ f₁ f₂ : Comp pqxdhOps I Γ τ} {ρ : Env Γ}
    (hc : c₁.eval ρ = c₂.eval ρ) (ht : t₁.eval ρ = t₂.eval ρ) (hf : f₁.eval ρ = f₂.eval ρ) :
    (Comp.ite c₁ t₁ f₁).eval ρ = (Comp.ite c₂ t₂ f₂).eval ρ := by
  simp only [Comp.eval, hc, ht, hf]

theorem prf_caseOptV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {o₁ o₂ : Expr pqxdhOps Γ (.opt τ₁)} {kn₁ kn₂ : Comp pqxdhOps I Γ τ₂}
    {ks₁ ks₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ}
    (ho : o₁.eval ρ = o₂.eval ρ) (hkn : kn₁.eval ρ = kn₂.eval ρ)
    (hks : ∀ x, (ks₁ .zero).eval (.cons x ρ) = (ks₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV o₁ kn₁ ks₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV o₂ kn₂ ks₂).eval ρ := by
  rw [prf_caseOptV_eval, prf_caseOptV_eval, ho]
  cases o₂.eval ρ with
  | none => exact hkn
  | some x => exact hks x

theorem koskBundleOkC_fuel_eq (S : Setup) (K Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hK : n ≤ K) (hKQ : K ≤ Q) :
    (koskBundleOkC S K st bu).eval env = (koskBundleOkC S Q st bu).eval env :=
  AuthCoreKSimPrfBase.koskBundleOkC_fuel_eq S st bu env hb hK (Nat.le_trans hK hKQ)

theorem koskSenderOkC_fuel_eq (S : Setup) (K Q : ℕ) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hK : n ≤ K) (hKQ : K ≤ Q) :
    (koskSenderOkC S K st ik).eval env = (koskSenderOkC S Q st ik).eval env :=
  AuthCoreKSimPrfBase.koskSenderOkC_fuel_eq S st ik env hb hK (Nat.le_trans hK hKQ)

theorem checkBundleProvenanceExactC_fuel_eq (S : Setup) (K Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hK : n ≤ K) (hKQ : K ≤ Q) :
    (checkBundleProvenanceExactC S K st bu).eval env =
      (checkBundleProvenanceExactC S Q st bu).eval env :=
  AuthCoreKSimPrfBase.checkBundleProvenanceExactC_fuel_eq S st bu env hb hK (Nat.le_trans hK hKQ)

theorem spkHonIdealFromPeerC_fuel_eq (S : Setup) (K Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (pp : Var Γ₂ (.opt (.prod .nat _root_.SignalPqxdh.Security.ReductionDsl.principalEntryTy)))
    (bu : Var Γ₃ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hK : n ≤ K) (hKQ : K ≤ Q) :
    (spkHonIdealFromPeerC S K st pp bu).eval env =
      (spkHonIdealFromPeerC S Q st pp bu).eval env :=
  AuthCoreKSimPrfBase.spkHonIdealFromPeerC_fuel_eq S st pp bu env hb hK (Nat.le_trans hK hKQ)

theorem hkdfRoC_fuel_eq (K Q : ℕ)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hK : (valRoCache (env.get (h.wk st))).length ≤ K)
    (hQ : (valRoCache (env.get (h.wk st))).length ≤ Q) :
    (hkdfRoC K st sec).eval env = (hkdfRoC Q st sec).eval env :=
  AuthCoreKSimPrfBase.hkdfRoC_fuel_eq st sec env (le_refl _) hK hQ

theorem hkdfRoC_step (K : ℕ)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hK : (valRoCache (env.get (h.wk st))).length ≤ K) :
    ∀ out ∈ support ((hkdfRoC K st sec).eval env),
      CacheStepAtMostOne (valRoCache (env.get (h.wk st))) out.2 :=
  AuthCoreKSimPrfBase.hkdfRoC_step st sec env hK

theorem rootRoC_fuel_eq (K Q : ℕ)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hK : (valRootRoCache (env.get (h.wk st))).length ≤ K)
    (hQ : (valRootRoCache (env.get (h.wk st))).length ≤ Q) :
    (rootRoC K st rk dh).eval env = (rootRoC Q st rk dh).eval env :=
  AuthCoreKSimPrfBase.rootRoC_fuel_eq st rk dh env (le_refl _) hK hQ

theorem rootRoC_step (K : ℕ)
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hK : (valRootRoCache (env.get (h.wk st))).length ≤ K) :
    ∀ out ∈ support ((rootRoC K st rk dh).eval env),
      CacheStepAtMostOne (valRootRoCache (env.get (h.wk st))) out.2 :=
  AuthCoreKSimPrfBase.rootRoC_step st rk dh env hK

theorem prf_caseSumV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ τ₃ : Ty pqSig}
    {s₁ s₂ : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl₁ kl₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₃}
    {kr₁ kr₂ : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ₃} {ρ : Env Γ}
    (hs : s₁.eval ρ = s₂.eval ρ)
    (hkl : ∀ x, (kl₁ .zero).eval (.cons x ρ) = (kl₂ .zero).eval (.cons x ρ))
    (hkr : ∀ x, (kr₁ .zero).eval (.cons x ρ) = (kr₂ .zero).eval (.cons x ρ)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV s₁ kl₁ kr₁).eval ρ =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV s₂ kl₂ kr₂).eval ρ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV, Comp.eval, hs]
  cases s₂.eval ρ with
  | inl x => exact hkl x
  | inr x => exact hkr x

theorem support_prf_letV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e : Expr pqxdhOps Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x, x = e.eval ρ → ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e k).eval ρ), P y := by
  intro y hy; rw [prf_letV_eval] at hy; exact h (e.eval ρ) rfl y hy

theorem support_prf_letV_any {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {e : Expr pqxdhOps Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x, ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV e k).eval ρ), P y :=
  support_prf_letV fun x _ => h x

theorem support_prf_bindV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m : Comp pqxdhOps I Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x ∈ support (m.eval ρ), ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV m k).eval ρ), P y := by
  intro y hy; simp only [prf_bindV_eval, support_bind, Set.mem_iUnion, exists_prop] at hy
  rcases hy with ⟨x, hx, hy⟩; exact h x hx y hy

theorem support_prf_bindV_any {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {m : Comp pqxdhOps I Γ τ₁} {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂}
    {ρ : Env Γ} {P : τ₂.denote → Prop}
    (h : ∀ x, ∀ y ∈ support ((k .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.bindV m k).eval ρ), P y :=
  support_prf_bindV fun x _ => h x

theorem support_prf_ite {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    {c : Expr pqxdhOps Γ .bool} {t f : Comp pqxdhOps I Γ τ} {ρ : Env Γ} {P : τ.denote → Prop}
    (ht : c.eval ρ = true → ∀ y ∈ support (t.eval ρ), P y)
    (hf : c.eval ρ = false → ∀ y ∈ support (f.eval ρ), P y) :
    ∀ y ∈ support ((Comp.ite c t f).eval ρ), P y := by
  intro y hy; simp only [Comp.eval] at hy
  cases hc : c.eval ρ
  · rw [hc] at hy; exact hf hc y hy
  · rw [hc] at hy; exact ht hc y hy

theorem support_prf_caseOptV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    {o : Expr pqxdhOps Γ (.opt τ₁)} {kn : Comp pqxdhOps I Γ τ₂}
    {ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {ρ : Env Γ} {P : τ₂.denote → Prop}
    (hkn : ∀ y ∈ support (kn.eval ρ), P y)
    (hks : ∀ x, ∀ y ∈ support ((ks .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseOptV o kn ks).eval ρ),
      P y := by
  intro y hy; rw [prf_caseOptV_eval] at hy
  cases ho : o.eval ρ
  · rw [ho] at hy; exact hkn y hy
  · rw [ho] at hy; exact hks _ y hy

theorem support_prf_caseSumV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ₁ τ₂ τ₃ : Ty pqSig}
    {s : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₃}
    {kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ₃} {ρ : Env Γ} {P : τ₃.denote → Prop}
    (hkl : ∀ x, ∀ y ∈ support ((kl .zero).eval (.cons x ρ)), P y)
    (hkr : ∀ x, ∀ y ∈ support ((kr .zero).eval (.cons x ρ)), P y) :
    ∀ y ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV s kl kr).eval ρ),
      P y := by
  intro y hy; simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.caseSumV, Comp.eval] at hy
  cases hs : s.eval ρ
  · rw [hs] at hy; exact hkl _ y hy
  · rw [hs] at hy; exact hkr _ y hy

theorem support_prf_ret {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {τ : Ty pqSig} {e : Expr pqxdhOps Γ τ} {ρ : Env Γ}
    {P : τ.denote → Prop} (h : P (e.eval ρ)) :
    ∀ y ∈ support ((Comp.ret (I := I) e).eval ρ), P y := by
  intro y hy; simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hy; rwa [hy]

theorem cpaInitC_preserves (S : Setup) (Q : ℕ) :
    ∀ us ∈ support ((cpaInitC S Q).eval (.cons () .nil)),
      AuthFixedValOnlineBounded 0 us.2.2.2 ∧
      valRoCache us.2.2.2.1.1 = [] ∧
      valRootRoCache us.2.2.2.1.1 = [] := by
  intro us hus
  unfold cpaInitC at hus
  rw [prf_bindV_eval] at hus
  simp only [Comp.eval, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hus
  rcases hus with ⟨idx, _, rfl⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩ <;>
    simp [emptyAuthHybridStFixedE, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.emptyAuthHybridStE,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.emptyAuthStE, Expr.eval]

theorem ext_step_wk {Γ Δ : List (Ty pqSig)} {σ τ : Ty pqSig}
    [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (σ := σ) (Γ := Γ) (Δ := Δ)).wk x = .succ (h.wk x) := rfl

theorem ext_refl_wk {Γ : List (Ty pqSig)} {τ : Ty pqSig} (x : Var Γ τ) :
    (Ext.refl (Γ := Γ)).wk x = x := rfl

theorem env_get_succ {Γ : List (Ty pqSig)} {σ τ : Ty pqSig} (x : Var Γ τ) (a : σ.denote)
    (env : Env Γ) : Env.get (.cons a env) (.succ x) = Env.get env x := rfl

theorem env_get_zero {Γ : List (Ty pqSig)} {σ : Ty pqSig} (a : σ.denote) (env : Env Γ) :
    Env.get (.cons a env) .zero = a := rfl

theorem finishCpaC_preserves {n : ℕ}
    {Γ₁ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) [h₁ : Ext Γ₁ Δ]
    (fresh isIdeal : Expr pqxdhOps Δ .bool)
    (p : Expr pqxdhOps Δ cpaPayloadTy)
    (aeadCt : Expr pqxdhOps Δ (B 32))
    (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst))) :
    ∀ rsf ∈ support ((finishCpaC fhst fresh isIdeal p aeadCt).eval env),
      AuthFixedValOnlineBounded (n + 1) rsf.2 ∧
      valRoCache rsf.2.1.1 = (p.eval env).2.2.2.2.2.2.2.2.2.2.2.2.1 ∧
      valRootRoCache rsf.2.1.1 = (p.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2 := by
  unfold finishCpaC
  apply support_prf_letV; intro aVal ha
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro isIdealVal hisIdeal
  apply support_prf_letV; intro pVal hp
  have hp₀ : pVal = p.eval env := by
    simp only [hp, ha, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro hstVal hhst
  have hhst₀ : hstVal = (env.get (h₁.wk fhst)).1 := by
    simp only [hhst, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid,
      Expr.eval, ext_step_wk, env_get_succ]
  apply support_prf_letV; intro stVal hst
  have hst₀ : stVal = (env.get (h₁.wk fhst)).1.1 := by
    simp only [hst, hhst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      Expr.eval, ext_refl_wk, env_get_zero]
  iterate 12 (apply support_prf_letV; intro _ _)
  apply support_prf_letV; intro roCVal hroC
  have hroC₀ : roCVal = (p.eval env).2.2.2.2.2.2.2.2.2.2.2.2.1 := by
    simp only [hroC, hp₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  apply support_prf_letV; intro rootCVal hrootC
  have hrootC₀ : rootCVal = (p.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2 := by
    simp only [hrootC, hp₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  iterate 14 (apply support_prf_letV; intro _ _)
  apply support_prf_letV; intro idealVal hideal
  have hidealLen : idealVal.length ≤ n + 1 := by
    simp only [hideal, hhst₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    cases isIdealVal <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
    · exact Nat.le_succ_of_le hb.idealSessions_le
    · exact Nat.succ_le_succ hb.idealSessions_le
  apply support_prf_letV; intro hst'Val hhst'
  apply support_prf_letV; intro _ _
  apply support_prf_ret
  simp only [hhst', hhst₀, hst₀, hroC₀, hrootC₀,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfRecvCount,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfMkSaltCache,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSecb,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asHasWonAuth,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asPrincipals,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSpkBundles,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asOpkEntries,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSessions,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedSendSessions,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvOPK,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedRecvNoOPK,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asUsedKyberTriples,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asSentNoOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRecvdNoOPKEvents,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asAdvKeys,
    Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  have hb' := hb.mono (Nat.le_succ n)
  exact ⟨⟨⟨hb'.base_le.principals_le, hb'.base_le.spkBundles_le, hb'.base_le.opkEntries_le,
    Nat.succ_le_succ hb.base_le.sessions_le, Nat.succ_le_succ hb.base_le.usedSendSessions_le,
    hb'.base_le.usedRecvOPK_le, hb'.base_le.usedRecvNoOPK_le,
    hb'.base_le.seenKyberBaseKeys_le, hb'.base_le.sentOPKEvents_le,
    hb'.base_le.sentNoOPKEvents_le, hb'.base_le.recvdOPKEvents_le,
    hb'.base_le.recvdNoOPKEvents_le, hb'.base_le.advKeys_le⟩,
    Nat.succ_le_succ hb.initKemRecs_le, hb'.recvKemRecs_le, hidealLen, hb'.mkSaltCache_le⟩,
    rfl, rfl⟩

theorem cpaSendSlotKB_fuel_eq (S : Setup) (K_on K_ro Q : ℕ) {n : ℕ}
    (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy)
    (x : Var Γ₄ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₃.wk fhst)))
    (hOn : n ≤ K_on) (hOnQ : K_on ≤ Q)
    (hRo : (valRoCache (env.get (h₃.wk fhst)).1.1).length ≤ K_ro)
    (hRt : (valRootRoCache (env.get (h₃.wk fhst)).1.1).length ≤ K_ro)
    (hRoQ : K_ro ≤ Q) :
    (AuthCoreKArms.cpaSendSlotKB S K_on K_ro opk allowPause idx ns fhst x).eval env =
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S Q opk allowPause idx ns fhst x).eval env := by
  have hUsedOn : (env.get (h₃.wk fhst)).1.1.2.2.2.2.2.2.1.length ≤ K_on :=
    Nat.le_trans hb.base_le.usedSendSessions_le hOn
  have hPrinOn : (env.get (h₃.wk fhst)).1.1.2.2.1.length ≤ K_on :=
    Nat.le_trans hb.base_le.principals_le hOn
  unfold AuthCoreKArms.cpaSendSlotKB AuthCoreKArmsBase.cpaSendSlotKB
    _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB
  refine prf_letV_congr rfl fun _ => ?_
  refine prf_ite_congr rfl rfl ?_
  rw [prf_letV_eval, prf_letV_eval]
  iterate 4 refine prf_letV_congr rfl fun _ => ?_
  refine prf_ite_congr rfl rfl ?_
  refine prf_ite_congr (prf_eAny_eq K_on Q _ _ _ hUsedOn (Nat.le_trans hUsedOn hOnQ)) rfl ?_
  refine prf_caseOptV_congr (prf_eFind_eq K_on Q _ _ _ hPrinOn (Nat.le_trans hPrinOn hOnQ)) rfl fun _ => ?_
  refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr (findHonestC_prf_fuel_eq S K_on Q _ _ _ hb.base_le hOn hOnQ) fun _ => ?_
  refine prf_letV_congr rfl fun _ => ?_
  refine prf_ite_congr rfl rfl ?_
  refine prf_bindV_congr (koskBundleOkC_fuel_eq S K_on Q _ _ _ hb.base_le hOn hOnQ) fun _ => ?_
  refine prf_ite_congr rfl rfl ?_
  iterate 4 refine prf_bindV_congr rfl fun _ => ?_
  refine prf_letV_congr rfl fun _ => ?_
  iterate 2 refine prf_bindV_congr rfl fun _ => ?_
  refine prf_ite_congr rfl rfl ?_
  refine prf_bindV_congr rfl fun _ => ?_
  refine prf_caseOptV_congr rfl rfl fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  refine prf_bindV_congr rfl fun _ => ?_
  refine prf_bindV_congr (checkBundleProvenanceExactC_fuel_eq S K_on Q _ _ _ hb.base_le hOn hOnQ) fun _ => ?_
  refine prf_bindV_congr (spkHonIdealFromPeerC_fuel_eq S K_on Q _ _ _ _ hb.base_le hOn hOnQ) fun _ => ?_
  refine prf_letV_congr rfl fun _ => ?_
  iterate 4 refine prf_bindV_congr rfl fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  iterate 2 refine prf_bindV_congr rfl fun _ => ?_
  refine prf_bindV_congr (prf_ite_congr rfl rfl (hkdfRoC_fuel_eq K_ro Q _ _ _ hRo (Nat.le_trans hRo hRoQ))) fun _ => ?_
  iterate 2 refine prf_letV_congr rfl fun _ => ?_
  exact prf_bindV_congr (prf_ite_congr rfl rfl (rootRoC_fuel_eq K_ro Q _ _ _ _ hRt (Nat.le_trans hRt hRoQ))) fun _ => rfl

@[expose] def CpaSendSlotPost (n : ℕ) (allowPause : Bool)
    (fhst₀ : authHybridStateFixedTy.denote)
    (out : _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSlotSendResTy.denote) : Prop :=
  match out with
  | .inl (_, _, fhst') =>
      AuthFixedValOnlineBounded (n + 1) fhst' ∧
      CacheStepAtMostOne (valRoCache fhst₀.1.1) (valRoCache fhst'.1.1) ∧
      CacheStepAtMostOne (valRootRoCache fhst₀.1.1) (valRootRoCache fhst'.1.1)
  | .inr (_, pl, _, fhst') =>
      allowPause = true ∧
      fhst' = fhst₀ ∧
      pl.2.2.2.2.2.2.2.2.2.2.2.2.1 = valRoCache fhst₀.1.1 ∧
      pl.2.2.2.2.2.2.2.2.2.2.2.2.2 = valRootRoCache fhst₀.1.1

theorem cpaSendSlotB_preserves (S : Setup) (Q : ℕ) {n : ℕ}
    (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy)
    (x : Var Γ₄ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₃.wk fhst)))
    (hRoQ : (valRoCache (env.get (h₃.wk fhst)).1.1).length ≤ Q)
    (hRtQ : (valRootRoCache (env.get (h₃.wk fhst)).1.1).length ≤ Q) :
    ∀ out ∈ support
        ((_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB S Q opk allowPause idx ns fhst x).eval env),
      CpaSendSlotPost n allowPause (env.get (h₃.wk fhst)) out := by
  unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaSendSlotB
  apply support_prf_letV; intro noneDoneVal hNoneDone
  have hAbort : CpaSendSlotPost n allowPause (env.get (h₃.wk fhst)) noneDoneVal := by
    simp only [hNoneDone, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, CpaSendSlotPost]
    exact ⟨hb.mono (Nat.le_succ n), .refl _, .refl _⟩
  apply support_prf_ite
  · intro _; apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  apply support_prf_letV; intro hstVal hhst
  apply support_prf_letV; intro stVal hst
  have hst₀ : stVal = (env.get (h₃.wk fhst)).1.1 := by
    simp only [hst, hhst, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  iterate 4 (apply support_prf_letV; intro _ _)
  apply support_prf_ite
  · intro _; apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  apply support_prf_ite
  · intro _; apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  apply support_prf_caseOptV
  · apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  apply support_prf_letV; intro _ _
  apply support_prf_bindV_any; intro _
  apply support_prf_letV; intro isFreshVal _
  apply support_prf_ite
  · intro _; apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  apply support_prf_bindV_any; intro _
  apply support_prf_ite
  · intro _; apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  iterate 4 (apply support_prf_bindV_any; intro _)
  apply support_prf_letV; intro _ _
  iterate 2 (apply support_prf_bindV_any; intro _)
  apply support_prf_ite
  · intro _; apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  apply support_prf_bindV_any; intro _
  apply support_prf_caseOptV
  · apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  iterate 2 (apply support_prf_letV; intro _ _)
  iterate 3 (apply support_prf_bindV_any; intro _)
  apply support_prf_letV; intro isIdealVal hisIdeal
  have hFreshImpIdeal : isFreshVal = true → isIdealVal = true := by
    intro hf
    simp only [hisIdeal, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.boolOr,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hf, ite_true]
  iterate 4 (apply support_prf_bindV_any; intro _)
  iterate 2 (apply support_prf_letV; intro _ _)
  iterate 2 (apply support_prf_bindV_any; intro _)
  apply support_prf_bindV; intro drOut hdrOut
  have hdr : CacheStepAtMostOne (valRoCache (env.get (h₃.wk fhst)).1.1) drOut.2 ∧
      (isIdealVal = true → drOut.2 = valRoCache (env.get (h₃.wk fhst)).1.1) := by
    revert hdrOut
    apply support_prf_ite
    · intro hid d hd
      revert hd; apply support_prf_bindV_any; intro _
      apply support_prf_ret
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRoCache,
        Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hst₀]
      exact ⟨.refl _, fun _ => rfl⟩
    · intro hnid d hd
      have hnid' : isIdealVal = false := by
        simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hnid
      have hstep := fun hlen => hkdfRoC_step Q _ _ _ hlen d hd
      have hstep' : CacheStepAtMostOne (valRoCache (env.get (h₃.wk fhst)).1.1) d.2 := by
        simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hst₀] using
          hstep (by simp only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hst₀]; exact hRoQ)
      exact ⟨hstep', fun ht => by simp [hnid'] at ht⟩
  apply support_prf_letV; intro _ _
  apply support_prf_letV; intro roCVal hroC
  have hroC₀ : roCVal = drOut.2 := by
    simp only [hroC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  apply support_prf_bindV; intro rkOut hrkOut
  have hrk : CacheStepAtMostOne (valRootRoCache (env.get (h₃.wk fhst)).1.1) rkOut.2 ∧
      (isIdealVal = true → rkOut.2 = valRootRoCache (env.get (h₃.wk fhst)).1.1) := by
    revert hrkOut
    apply support_prf_ite
    · intro _ r hr
      revert hr; iterate 2 (apply support_prf_bindV_any; intro _)
      apply support_prf_ret
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
        _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRootRoCache,
        Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hst₀]
      exact ⟨.refl _, fun _ => rfl⟩
    · intro hnid r hr
      have hnid' : isIdealVal = false := by
        simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hnid
      have hstep := fun hlen => rootRoC_step Q _ _ _ _ hlen r hr
      have hstep' : CacheStepAtMostOne (valRootRoCache (env.get (h₃.wk fhst)).1.1) r.2 := by
        simpa only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hst₀] using
          hstep (by simp only [ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hst₀]; exact hRtQ)
      exact ⟨hstep', fun ht => by simp [hnid'] at ht⟩
  iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_letV; intro rootCVal hrootC
  have hrootC₀ : rootCVal = rkOut.2 := by
    simp only [hrootC, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
  apply support_prf_bindV_any; intro _
  iterate 2 (apply support_prf_letV; intro _ _)
  apply support_prf_bindV_any; intro _
  apply support_prf_caseOptV
  · apply support_prf_ret
    simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hAbort
  intro _
  iterate 3 (apply support_prf_letV; intro _ _)
  apply support_prf_letV; intro plVal hpl
  have hplRo : plVal.2.2.2.2.2.2.2.2.2.2.2.2.1 = drOut.2 ∧
      plVal.2.2.2.2.2.2.2.2.2.2.2.2.2 = rkOut.2 := by
    simp only [hpl, hroC₀, hrootC₀, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, and_self]
  apply support_prf_ite
  · intro hFresh
    have hFresh' : isFreshVal = true := by
      simpa only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
        Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] using hFresh
    have hid := hFreshImpIdeal hFresh'
    apply support_prf_letV; intro _ _
    cases allowPause
    · simp only [Bool.false_eq_true, ↓reduceIte, id_eq]
      iterate 2 (apply support_prf_bindV_any; intro _)
      apply support_prf_bindV; intro res hres
      have hfin := fun hfhst => finishCpaC_preserves (n := n) fhst _ _ _ _ _ hfhst res hres
      obtain ⟨hb', hro', hrt'⟩ := hfin (by
        simp only [ext_step_wk, env_get_succ]; exact hb)
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
        Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] at hro' hrt'
      apply support_prf_ret
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
        Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, CpaSendSlotPost]
      exact ⟨hb', hro'.trans hplRo.1 ▸ hdr.1, hrt'.trans hplRo.2 ▸ hrk.1⟩
    · apply support_prf_ite
      · intro _
        apply support_prf_ret
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, CpaSendSlotPost,
          true_and]
        exact ⟨hplRo.1.trans (hdr.2 hid), hplRo.2.trans (hrk.2 hid)⟩
      · intro _
        iterate 2 (apply support_prf_bindV_any; intro _)
        apply support_prf_bindV; intro res hres
        have hfin := fun hfhst => finishCpaC_preserves (n := n) fhst _ _ _ _ _ hfhst res hres
        obtain ⟨hb', hro', hrt'⟩ := hfin (by
          simp only [ext_step_wk, env_get_succ]; exact hb)
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] at hro' hrt'
        apply support_prf_ret
        simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
          Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, CpaSendSlotPost]
        exact ⟨hb', hro'.trans hplRo.1 ▸ hdr.1, hrt'.trans hplRo.2 ▸ hrk.1⟩
  · intro _
    iterate 2 (apply support_prf_bindV_any; intro _)
    apply support_prf_bindV; intro res hres
    have hfin := fun hfhst => finishCpaC_preserves (n := n) fhst _ _ _ _ _ hfhst res hres
    obtain ⟨hb', hro', hrt'⟩ := hfin (by
      simp only [ext_step_wk, env_get_succ]; exact hb)
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero] at hro' hrt'
    apply support_prf_ret
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v,
      Expr.eval, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, CpaSendSlotPost]
    exact ⟨hb', hro'.trans hplRo.1 ▸ hdr.1, hrt'.trans hplRo.2 ▸ hrk.1⟩


end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimCpaBase
