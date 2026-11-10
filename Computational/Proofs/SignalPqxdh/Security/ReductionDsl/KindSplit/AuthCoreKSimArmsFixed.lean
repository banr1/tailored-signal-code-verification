/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine

/-!
# Clamped `AuthPrf` Fixed Non-Session Arms

Fuel-equivalence and `AuthFixedShadowAt` preservation lemmas for the clamped `AuthPrf` fixed
non-session oracle arms (`initPrin`, `corrupt`, `genSpk`, `genOpk`, and `register`) shared across
the `ck`, `mk`, `cpa`, and `int` kind-split reductions.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal mapComp)
open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl
  (authStateTy preKeyBundleTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateFixedTy
   initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB registerFixedB)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels authFixedShadowStTy
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (AuthFixedValOnlineBounded valRoCache valRootRoCache AuthFixedShadowAt)

section FixedNonSession

open _root_.SignalPqxdh.Security.ReductionDsl
  (principalEntryTy spkBundleEntryTy opkEntryTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext RSF v letV_eval bindV_eval caseOptV_eval eAny eFind eMap
   ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions ahsUpd ahsMk
   ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots ahsfUpd ahsfMkSlots fhstSetBase
   asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
   asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
   asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
   asRoCache asRootRoCache asAdvKeys stUpd stMk)

@[local simp] private theorem env_cons_get_ext_step {Γ Δ : List (Ty pqSig)} {σ τ : Ty pqSig}
    [h : Ext Γ Δ] (x : σ.denote) (env : Env Δ) (w : Var Γ τ) :
    (Env.cons x env).get ((@Ext.step Γ Δ σ h).wk w) = env.get (h.wk w) := rfl

@[local simp] private theorem env_get_ext_refl {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    (env : Env Γ) (w : Var Γ τ) :
    env.get ((@Ext.refl Γ).wk w) = env.get w := rfl

private theorem fixedTuple_preserves_online_ro {m n : ℕ}
    (f0 : authHybridStateFixedTy.denote)
    (prin : List (ℕ × principalEntryTy.denote))
    (spks : List ((ℕ × ℕ) × spkBundleEntryTy.denote))
    (opks : List ((ℕ × ℕ × ℕ) × opkEntryTy.denote))
    (adv : List ((B 32).denote × (B 32).denote))
    (hb : AuthFixedValOnlineBounded m f0) (hmn : m ≤ n)
    (hp : prin.length ≤ n) (hs : spks.length ≤ n)
    (ho : opks.length ≤ n) (ha : adv.length ≤ n) :
    let base' : authStateTy.denote :=
      (f0.1.1.1, f0.1.1.2.1, prin, spks, opks,
       f0.1.1.2.2.2.2.2.1, f0.1.1.2.2.2.2.2.2.1, f0.1.1.2.2.2.2.2.2.2.1,
       f0.1.1.2.2.2.2.2.2.2.2.1, f0.1.1.2.2.2.2.2.2.2.2.2.1,
       f0.1.1.2.2.2.2.2.2.2.2.2.2.1, f0.1.1.2.2.2.2.2.2.2.2.2.2.2.1,
       f0.1.1.2.2.2.2.2.2.2.2.2.2.2.2.1, f0.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
       f0.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, f0.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
       adv)
    let f' : authHybridStateFixedTy.denote :=
      ((base', f0.1.2.1, f0.1.2.2.1, f0.1.2.2.2), f0.2.1, f0.2.2.1, f0.2.2.2)
    AuthFixedValOnlineBounded n f' ∧
    valRoCache f'.1.1 = valRoCache f0.1.1 ∧
    valRootRoCache f'.1.1 = valRootRoCache f0.1.1 :=
  ⟨{ base_le :=
       { principals_le        := hp
         spkBundles_le        := hs
         opkEntries_le        := ho
         sessions_le          := Nat.le_trans hb.base_le.sessions_le hmn
         usedSendSessions_le  := Nat.le_trans hb.base_le.usedSendSessions_le hmn
         usedRecvOPK_le       := Nat.le_trans hb.base_le.usedRecvOPK_le hmn
         usedRecvNoOPK_le     := Nat.le_trans hb.base_le.usedRecvNoOPK_le hmn
         seenKyberBaseKeys_le := Nat.le_trans hb.base_le.seenKyberBaseKeys_le hmn
         sentOPKEvents_le     := Nat.le_trans hb.base_le.sentOPKEvents_le hmn
         sentNoOPKEvents_le   := Nat.le_trans hb.base_le.sentNoOPKEvents_le hmn
         recvdOPKEvents_le    := Nat.le_trans hb.base_le.recvdOPKEvents_le hmn
         recvdNoOPKEvents_le  := Nat.le_trans hb.base_le.recvdNoOPKEvents_le hmn
         advKeys_le           := ha }
     initKemRecs_le   := Nat.le_trans hb.initKemRecs_le hmn
     recvKemRecs_le   := Nat.le_trans hb.recvKemRecs_le hmn
     idealSessions_le := Nat.le_trans hb.idealSessions_le hmn
     mkSaltCache_le   := Nat.le_trans hb.mkSaltCache_le hmn },
   rfl, rfl⟩

private theorem eAny_eq_of_le {Γ : List (Ty pqSig)} {τ : Ty pqSig} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eAny K₁ xs p).eval env = (eAny K₂ xs p).eval env := by
  simp only [eAny, Expr.eval, List.take_of_length_le hLen,
    List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem eFind_eq_of_le {Γ : List (Ty pqSig)} {τ : Ty pqSig} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eFind K₁ xs p).eval env = (eFind K₂ xs p).eval env := by
  simp only [eFind, Expr.eval, List.take_of_length_le hLen,
    List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem eMap_eq_of_le {Γ : List (Ty pqSig)} {τ σ : Ty pqSig} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (f : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) σ) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eMap K₁ xs f).eval env = (eMap K₂ xs f).eval env := by
  simp only [eMap, Expr.eval, List.take_of_length_le hLen,
    List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem fhstSetBase_stUpd_principals_congr {Γ : List (Ty pqSig)}
    (fhstE : Expr pqxdhOps Γ authHybridStateFixedTy)
    (stE : Expr pqxdhOps Γ authStateTy)
    (p₁ p₂ : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy))) (ρ : Env Γ)
    (hp : p₁.eval ρ = p₂.eval ρ) :
    (fhstSetBase fhstE (stUpd stE (asSecb stE) (asHasWonAuth stE) p₁)).eval ρ =
      (fhstSetBase fhstE (stUpd stE (asSecb stE) (asHasWonAuth stE) p₂)).eval ρ := by
  simp only [fhstSetBase, ahsfUpd, ahsfMkSlots, ahsUpd, ahsMk, stUpd, stMk, Expr.eval, hp]

theorem initPrin1KeyFixedKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (initPrin1KeyFixedKB (AuthKindFuels.ofBudget S b) fhst u).eval env =
      (initPrin1KeyFixedB b.q_total fhst u).eval env := by
  simp only [initPrin1KeyFixedKB, initPrin1KeyFixedB, letV_eval, Comp.eval]
  rw [eAny_eq_of_le _ _ _
    (by simp only [ahsBase, ahsfHybrid, asPrincipals, v, Expr.eval, env_get_ext_refl, Env.get]
        exact Nat.le_trans hb.base_le.principals_le hn)
    (AuthKindFuels.K_on_le_q_total S b)]

theorem initPrin1KeyFixedB_preserves_online_ro (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst))) :
    ∀ rsf ∈ support ((initPrin1KeyFixedB Q fhst u).eval env),
      AuthFixedValOnlineBounded (n + 1) rsf.2 ∧
      valRoCache rsf.2.1.1 = valRoCache (env.get (h₁.wk fhst)).1.1 ∧
      valRootRoCache rsf.2.1.1 = valRootRoCache (env.get (h₁.wk fhst)).1.1 := by
  intro out hout
  simp only [initPrin1KeyFixedB, letV_eval, bindV_eval, Comp.eval] at hout
  split_ifs at hout
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
    rcases hout with ⟨s0, _, ik, _, rfl⟩
    simp only [fhstSetBase, ahsfUpd, ahsfMkSlots, ahsUpd, ahsMk, ahsfHybrid, ahsfRecvCount,
      ahsfMkSaltCache, ahsfSlots, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asRoCache, asRootRoCache, asAdvKeys, v, Expr.eval,
      env_cons_get_ext_step, env_get_ext_refl]
    exact fixedTuple_preserves_online_ro (env.get (h₁.wk fhst)) _ _ _ _ hb (Nat.le_succ n)
      (Nat.succ_le_succ hb.base_le.principals_le)
      (Nat.le_trans hb.base_le.spkBundles_le (Nat.le_succ n))
      (Nat.le_trans hb.base_le.opkEntries_le (Nat.le_succ n))
      (Nat.le_trans hb.base_le.advKeys_le (Nat.le_succ n))

theorem corruptFixedKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (corruptFixedKB (AuthKindFuels.ofBudget S b) fhst u).eval env =
      (corruptFixedB b.q_total fhst u).eval env := by
  simp only [corruptFixedKB, corruptFixedB, letV_eval, caseOptV_eval, Comp.eval]
  rw [eFind_eq_of_le _ _ _
    (by simp only [ahsBase, ahsfHybrid, asPrincipals, v, Expr.eval, env_get_ext_refl, Env.get]
        exact Nat.le_trans hb.base_le.principals_le hn)
    (AuthKindFuels.K_on_le_q_total S b)]
  split_ifs
  · rfl
  · cases (eFind _ _ _).eval _ with
    | none => rfl
    | some a =>
      dsimp only [Expr.eval]
      rw [fhstSetBase_stUpd_principals_congr _ _ _ _ _
        (eMap_eq_of_le _ _ _
          (by simp only [ahsBase, ahsfHybrid, asPrincipals, v, Expr.eval,
                env_cons_get_ext_step, env_get_ext_refl, Env.get]
              exact Nat.le_trans hb.base_le.principals_le hn)
          (AuthKindFuels.K_on_le_q_total S b))]

theorem corruptFixedB_preserves_online_ro (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst))) :
    ∀ rsf ∈ support ((corruptFixedB Q fhst u).eval env),
      AuthFixedValOnlineBounded n rsf.2 ∧
      valRoCache rsf.2.1.1 = valRoCache (env.get (h₁.wk fhst)).1.1 ∧
      valRootRoCache rsf.2.1.1 = valRootRoCache (env.get (h₁.wk fhst)).1.1 := by
  intro out hout
  simp only [corruptFixedB, letV_eval, caseOptV_eval, Comp.eval] at hout
  split_ifs at hout
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb, rfl, rfl⟩
  · split at hout
    · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
      subst hout; exact ⟨hb, rfl, rfl⟩
    · simp only [mem_support_pure_iff] at hout
      subst hout
      simp only [fhstSetBase, ahsfUpd, ahsfMkSlots, ahsUpd, ahsMk, ahsfHybrid, ahsfRecvCount,
        ahsfMkSaltCache, ahsfSlots, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
        stUpd, stMk, eMap, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
        asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
        asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
        asRoCache, asRootRoCache, asAdvKeys, v, Expr.eval,
        env_cons_get_ext_step, env_get_ext_refl]
      exact fixedTuple_preserves_online_ro (env.get (h₁.wk fhst)) _ _ _ _ hb (Nat.le_refl n)
        (by rw [List.length_map, List.length_take]; exact Nat.le_trans (Nat.min_le_right _ _) hb.base_le.principals_le)
        hb.base_le.spkBundles_le hb.base_le.opkEntries_le hb.base_le.advKeys_le

theorem genSpkFixedKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (genSpkFixedKB (AuthKindFuels.ofBudget S b) fhst x).eval env =
      (genSpkFixedB b.q_total fhst x).eval env := by
  simp only [genSpkFixedKB, genSpkFixedB, letV_eval, caseOptV_eval, Comp.eval]
  rw [eAny_eq_of_le _ _ _
    (by simp only [ahsBase, ahsfHybrid, asSpkBundles, v, Expr.eval, env_get_ext_refl, Env.get]
        exact Nat.le_trans hb.base_le.spkBundles_le hn)
    (AuthKindFuels.K_on_le_q_total S b),
    eFind_eq_of_le _ _ _
    (by simp only [ahsBase, ahsfHybrid, asPrincipals, v, Expr.eval, env_get_ext_refl, Env.get]
        exact Nat.le_trans hb.base_le.principals_le hn)
    (AuthKindFuels.K_on_le_q_total S b)]

theorem genSpkFixedB_preserves_online_ro (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst))) :
    ∀ rsf ∈ support ((genSpkFixedB Q fhst x).eval env),
      AuthFixedValOnlineBounded (n + 1) rsf.2 ∧
      valRoCache rsf.2.1.1 = valRoCache (env.get (h₁.wk fhst)).1.1 ∧
      valRootRoCache rsf.2.1.1 = valRootRoCache (env.get (h₁.wk fhst)).1.1 := by
  intro out hout
  simp only [genSpkFixedB, letV_eval, caseOptV_eval, bindV_eval, Comp.eval] at hout
  split_ifs at hout
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · split at hout
    · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
      subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
      rcases hout with ⟨spkSk, _, spkPk, _, r1, _, sig1, _, seed, _, kp, _, r2, _, sig2, _, rfl⟩
      simp only [fhstSetBase, ahsfUpd, ahsfMkSlots, ahsUpd, ahsMk, ahsfHybrid, ahsfRecvCount,
        ahsfMkSaltCache, ahsfSlots, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
        stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
        asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
        asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
        asRoCache, asRootRoCache, asAdvKeys, v, Expr.eval,
        env_cons_get_ext_step, env_get_ext_refl]
      exact fixedTuple_preserves_online_ro (env.get (h₁.wk fhst)) _ _ _ _ hb (Nat.le_succ n)
        (Nat.le_trans hb.base_le.principals_le (Nat.le_succ n))
        (Nat.succ_le_succ hb.base_le.spkBundles_le)
        (Nat.le_trans hb.base_le.opkEntries_le (Nat.le_succ n))
        (Nat.le_trans hb.base_le.advKeys_le (Nat.le_succ n))

theorem genOpkFixedKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (genOpkFixedKB (AuthKindFuels.ofBudget S b) fhst x).eval env =
      (genOpkFixedB b.q_total fhst x).eval env := by
  simp only [genOpkFixedKB, genOpkFixedB, letV_eval, Comp.eval]
  rw [eAny_eq_of_le _ _ _
    (by simp only [ahsBase, ahsfHybrid, asOpkEntries, v, Expr.eval, env_get_ext_refl, Env.get]
        exact Nat.le_trans hb.base_le.opkEntries_le hn)
    (AuthKindFuels.K_on_le_q_total S b)]

theorem genOpkFixedB_preserves_online_ro (Q : ℕ) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst))) :
    ∀ rsf ∈ support ((genOpkFixedB Q fhst x).eval env),
      AuthFixedValOnlineBounded (n + 1) rsf.2 ∧
      valRoCache rsf.2.1.1 = valRoCache (env.get (h₁.wk fhst)).1.1 ∧
      valRootRoCache rsf.2.1.1 = valRootRoCache (env.get (h₁.wk fhst)).1.1 := by
  intro out hout
  simp only [genOpkFixedB, letV_eval, bindV_eval, Comp.eval] at hout
  split_ifs at hout
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
    rcases hout with ⟨sk, _, pk, _, rfl⟩
    simp only [fhstSetBase, ahsfUpd, ahsfMkSlots, ahsUpd, ahsMk, ahsfHybrid, ahsfRecvCount,
      ahsfMkSaltCache, ahsfSlots, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asRoCache, asRootRoCache, asAdvKeys, v, Expr.eval,
      env_cons_get_ext_step, env_get_ext_refl]
    exact fixedTuple_preserves_online_ro (env.get (h₁.wk fhst)) _ _ _ _ hb (Nat.le_succ n)
      (Nat.le_trans hb.base_le.principals_le (Nat.le_succ n))
      (Nat.le_trans hb.base_le.spkBundles_le (Nat.le_succ n))
      (Nat.succ_le_succ hb.base_le.opkEntries_le)
      (Nat.le_trans hb.base_le.advKeys_le (Nat.le_succ n))

theorem registerFixedKB_preserves_online_ro {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32))
    [h₁ : _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthFixedValOnlineBounded n (env.get (h₁.wk fhst))) :
    ∀ rsf ∈ support ((registerFixedKB fhst sk).eval env),
      AuthFixedValOnlineBounded (n + 1) rsf.2 ∧
      valRoCache rsf.2.1.1 = valRoCache (env.get (h₁.wk fhst)).1.1 ∧
      valRootRoCache rsf.2.1.1 = valRootRoCache (env.get (h₁.wk fhst)).1.1 := by
  intro out hout
  simp only [registerFixedKB, registerFixedB, letV_eval, bindV_eval, Comp.eval] at hout
  split_ifs at hout
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [v, Expr.eval, env_cons_get_ext_step, mem_support_pure_iff] at hout
    subst hout; exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
    rcases hout with ⟨pk, _, p8, _, rfl⟩
    simp only [fhstSetBase, ahsfUpd, ahsfMkSlots, ahsUpd, ahsMk, ahsfHybrid, ahsfRecvCount,
      ahsfMkSaltCache, ahsfSlots, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asRoCache, asRootRoCache, asAdvKeys, v, Expr.eval,
      env_cons_get_ext_step, env_get_ext_refl]
    exact fixedTuple_preserves_online_ro (env.get (h₁.wk fhst)) _ _ _ _ hb (Nat.le_succ n)
      (Nat.le_trans hb.base_le.principals_le (Nat.le_succ n))
      (Nat.le_trans hb.base_le.spkBundles_le (Nat.le_succ n))
      (Nat.le_trans hb.base_le.opkEntries_le (Nat.le_succ n))
      (Nat.succ_le_succ hb.base_le.advKeys_le)

private theorem embedVal_fst_eq {t u : Ty pqSig} (p : (Ty.prod t u).denote) :
    (embedVal (.prod t u) p).1 = embedVal t p.1 := rfl

private theorem embedVal_snd_eq {t u : Ty pqSig} (p : (Ty.prod t u).denote) :
    (embedVal (.prod t u) p).2 = embedVal u p.2 := rfl

private theorem atomRoCache_embedFixed (s : authHybridStateFixedTy.denote) :
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRoCache
      (embedVal authHybridStateFixedTy s).1.1 =
    embedVal (.list (.prod (B 192) _root_.SignalPqxdh.Security.ReductionDsl.drKeyTy))
      (valRoCache s.1.1) := by
  simp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRoCache,
    valRoCache, embedVal_fst_eq, embedVal_snd_eq]

private theorem atomRootRoCache_embedFixed (s : authHybridStateFixedTy.denote) :
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRootRoCache
      (embedVal authHybridStateFixedTy s).1.1 =
    embedVal (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))
      (valRootRoCache s.1.1) := by
  simp only [Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRootRoCache,
    valRootRoCache, embedVal_fst_eq, embedVal_snd_eq]

private theorem fixedShadow_preserve_of_val {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hsupp : ∀ {Δ out} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ) (y : out.denote),
      y ∈ support ((liftPrim c).eval env) → ∃ x ∈ support (c.eval env), x = y)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    {XTy : Ty pqSig}
    (c0 : Comp pqxdhOps pqPrimIface [authHybridStateFixedTy, XTy] RSF)
    (fs : authFixedShadowStTy.denote) (x : (embedTy XTy).denote)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hUnsup : ∀ g, tl.unsupportedW g = 0)
    (hPres : ∀ (fhst0 : authHybridStateFixedTy.denote) (x0 : XTy.denote),
      AuthFixedValOnlineBounded nOn fhst0 →
      ∀ y ∈ support (c0.eval (.cons fhst0 (.cons x0 .nil))),
        AuthFixedValOnlineBounded (nOn + 1) y.2 ∧
        valRoCache y.2.1.1 = valRoCache fhst0.1.1 ∧
        valRootRoCache y.2.1.1 = valRootRoCache fhst0.1.1) :
    ∀ rsf ∈ support ((mapComp tl (liftPrim c0)).eval (.cons fs.1 (.cons x .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, fs.2) := by
  let fhst0 := Computational.Proofs.SignalPqxdh.AtomicLift.projVal authHybridStateFixedTy fs.1
  let x0 := Computational.Proofs.SignalPqxdh.AtomicLift.projVal XTy x
  let ρ0 : Env [authHybridStateFixedTy, XTy] := .cons fhst0 (.cons x0 .nil)
  have hfs1 : embedVal authHybridStateFixedTy fhst0 = fs.1 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy fs.1
  have hx : embedVal XTy x0 = x :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal XTy x
  have hEnv : (.cons fs.1 (.cons x .nil) : Env [embedTy authHybridStateFixedTy, embedTy XTy]) =
      Computational.Proofs.SignalPqxdh.AtomicLift.embedEnv ρ0 := by
    simp only [ρ0, Computational.Proofs.SignalPqxdh.AtomicLift.embedEnv, hfs1, hx]
  have hb0 : AuthFixedValOnlineBounded nOn fhst0 := by
    have hOn := hSh.online_le
    rw [← hfs1] at hOn
    exact (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.AuthFixedAtomOnlineBounded.iff_embedVal fhst0).mp hOn
  intro rsf hrsf
  rw [hEnv, Computational.Proofs.SignalPqxdh.AtomicLift.mapComp_eval tl (liftPrim c0)
    (Computational.Proofs.SignalPqxdh.AtomicLift.comp_queries_zero_of_zero hUnsup (liftPrim c0)) ρ0,
    map_eq_bind_pure_comp] at hrsf
  simp only [Function.comp_apply, mem_support_bind_iff, mem_support_pure_iff] at hrsf
  rcases hrsf with ⟨y, hyLift, rfl⟩
  rcases hsupp c0 ρ0 y hyLift with ⟨y', hy0, rfl⟩
  rcases hPres fhst0 x0 hb0 y' hy0 with ⟨hOn', hRo', hRoot'⟩
  have hrsf2 : (embedVal RSF y').2 = embedVal authHybridStateFixedTy y'.2 := embedVal_snd_eq y'
  have hAtomRo :
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRoCache
        (embedVal RSF y').2.1.1 =
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRoCache
        fs.1.1.1 := by
    rw [hrsf2, ← hfs1, atomRoCache_embedFixed, atomRoCache_embedFixed, hRo']
  have hAtomRoot :
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRootRoCache
        (embedVal RSF y').2.1.1 =
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.atomRootRoCache
        fs.1.1.1 := by
    rw [hrsf2, ← hfs1, atomRootRoCache_embedFixed, atomRootRoCache_embedFixed, hRoot']
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrsf2]
    exact (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.AuthFixedAtomOnlineBounded.iff_embedVal y'.2).mpr hOn'
  · rw [hAtomRo]; exact hSh.ro_len_le
  · rw [hAtomRoot]; exact hSh.root_len_le
  · exact ⟨by rw [hAtomRo, hAtomRoot]; exact hSh.ro_shadow.both_valid,
      by rw [hAtomRo]; exact hSh.ro_shadow.ro_nodup,
      by rw [hAtomRoot]; exact hSh.ro_shadow.root_nodup⟩

private theorem fixedShadow_eval_eq_of_val {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hlift : ∀ {Δ out} (c₁ c₂ : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ),
      c₁.eval env = c₂.eval env → (liftPrim c₁).eval env = (liftPrim c₂).eval env)
    {nOn : ℕ} {XTy : Ty pqSig}
    (c₁ c₂ : Comp pqxdhOps pqPrimIface [authHybridStateFixedTy, XTy] RSF)
    (fs1 : (embedTy authHybridStateFixedTy).denote) (x : (embedTy XTy).denote)
    (hOn : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.AuthFixedAtomOnlineBounded nOn fs1)
    (hUnsup : ∀ g, tl.unsupportedW g = 0)
    (hEq : ∀ (fhst0 : authHybridStateFixedTy.denote) (x0 : XTy.denote),
      AuthFixedValOnlineBounded nOn fhst0 →
      c₁.eval (.cons fhst0 (.cons x0 .nil)) = c₂.eval (.cons fhst0 (.cons x0 .nil))) :
    (mapComp tl (liftPrim c₁)).eval (.cons fs1 (.cons x .nil)) =
      (mapComp tl (liftPrim c₂)).eval (.cons fs1 (.cons x .nil)) := by
  let fhst0 := Computational.Proofs.SignalPqxdh.AtomicLift.projVal authHybridStateFixedTy fs1
  let x0 := Computational.Proofs.SignalPqxdh.AtomicLift.projVal XTy x
  let ρ0 : Env [authHybridStateFixedTy, XTy] := .cons fhst0 (.cons x0 .nil)
  have hfs1 : embedVal authHybridStateFixedTy fhst0 = fs1 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal authHybridStateFixedTy fs1
  have hx : embedVal XTy x0 = x :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal XTy x
  have hEnv : (.cons fs1 (.cons x .nil) : Env [embedTy authHybridStateFixedTy, embedTy XTy]) =
      Computational.Proofs.SignalPqxdh.AtomicLift.embedEnv ρ0 := by
    simp only [ρ0, Computational.Proofs.SignalPqxdh.AtomicLift.embedEnv, hfs1, hx]
  have hb0 : AuthFixedValOnlineBounded nOn fhst0 := by
    have h := hOn
    rw [← hfs1] at h
    exact (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase.AuthFixedAtomOnlineBounded.iff_embedVal fhst0).mp h
  rw [hEnv,
    Computational.Proofs.SignalPqxdh.AtomicLift.mapComp_eval tl (liftPrim c₁)
      (Computational.Proofs.SignalPqxdh.AtomicLift.comp_queries_zero_of_zero hUnsup (liftPrim c₁)) ρ0,
    Computational.Proofs.SignalPqxdh.AtomicLift.mapComp_eval tl (liftPrim c₂)
      (Computational.Proofs.SignalPqxdh.AtomicLift.comp_queries_zero_of_zero hUnsup (liftPrim c₂)) ρ0,
    hlift c₁ c₂ ρ0 (hEq fhst0 x0 hb0)]

/-- Atomic `mapComp` shadow simulation for `initPrin1KeyFixedKB` on `authFixedShadowStTy`. -/
theorem initPrinFixedShadowB_sim {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hlift : ∀ {Δ out} (c₁ c₂ : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ),
      c₁.eval env = c₂.eval env → (liftPrim c₁).eval env = (liftPrim c₂).eval env)
    (hsupp : ∀ {Δ out} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ) (y : out.denote),
      y ∈ support ((liftPrim c).eval env) → ∃ x ∈ support (c.eval env), x = y)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    (fs : authFixedShadowStTy.denote) (u : ℕ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hUnsup : ∀ g, tl.unsupportedW g = 0 := by intro; rfl) :
    let F := AuthKindFuels.ofBudget S b
    let cK := mapComp tl (liftPrim
      (initPrin1KeyFixedKB F (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero))
    let cOld := mapComp tl (liftPrim
      (initPrin1KeyFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero))
    cK.eval (.cons fs.1 (.cons u .nil)) = cOld.eval (.cons fs.1 (.cons u .nil)) ∧
    ∀ rsf ∈ support (cK.eval (.cons fs.1 (.cons u .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, fs.2) := by
  intro F cK cOld
  have hEq : cK.eval (.cons fs.1 (.cons u .nil)) = cOld.eval (.cons fs.1 (.cons u .nil)) :=
    fixedShadow_eval_eq_of_val tl liftPrim hlift (XTy := .nat)
      (initPrin1KeyFixedKB F (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero)
      (initPrin1KeyFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero)
      fs.1 u hSh.online_le hUnsup
      (fun fhst0 u0 hb0 => initPrin1KeyFixedKB_fuel_eq S b
        (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero (.cons fhst0 (.cons u0 .nil))
        hb0 (Nat.le_of_succ_le hn))
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact fixedShadow_preserve_of_val tl liftPrim hsupp S b (XTy := .nat)
    (initPrin1KeyFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .nat])
      (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero)
    fs u hSh hUnsup
    (fun fhst0 u0 hb0 => initPrin1KeyFixedB_preserves_online_ro b.q_total
      (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
      (Δ := [authHybridStateFixedTy, .nat]) .zero .zero (.cons fhst0 (.cons u0 .nil)) hb0)

/-- Atomic `mapComp` shadow simulation for `corruptFixedKB` on `authFixedShadowStTy`. -/
theorem corruptFixedShadowB_sim {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hlift : ∀ {Δ out} (c₁ c₂ : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ),
      c₁.eval env = c₂.eval env → (liftPrim c₁).eval env = (liftPrim c₂).eval env)
    (hsupp : ∀ {Δ out} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ) (y : out.denote),
      y ∈ support ((liftPrim c).eval env) → ∃ x ∈ support (c.eval env), x = y)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    (fs : authFixedShadowStTy.denote) (u : ℕ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hUnsup : ∀ g, tl.unsupportedW g = 0 := by intro; rfl) :
    let F := AuthKindFuels.ofBudget S b
    let cK := mapComp tl (liftPrim
      (corruptFixedKB F (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero))
    let cOld := mapComp tl (liftPrim
      (corruptFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero))
    cK.eval (.cons fs.1 (.cons u .nil)) = cOld.eval (.cons fs.1 (.cons u .nil)) ∧
    ∀ rsf ∈ support (cK.eval (.cons fs.1 (.cons u .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, fs.2) := by
  intro F cK cOld
  have hEq : cK.eval (.cons fs.1 (.cons u .nil)) = cOld.eval (.cons fs.1 (.cons u .nil)) :=
    fixedShadow_eval_eq_of_val tl liftPrim hlift (XTy := .nat)
      (corruptFixedKB F (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero)
      (corruptFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .nat])
        (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero)
      fs.1 u hSh.online_le hUnsup
      (fun fhst0 u0 hb0 => corruptFixedKB_fuel_eq S b
        (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero (.cons fhst0 (.cons u0 .nil))
        hb0 (Nat.le_of_succ_le hn))
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact fixedShadow_preserve_of_val tl liftPrim hsupp S b (XTy := .nat)
    (corruptFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .nat])
      (Γ₂ := [.nat]) (Δ := [authHybridStateFixedTy, .nat]) .zero .zero)
    fs u hSh hUnsup
    (fun fhst0 u0 hb0 y hy => by
      rcases corruptFixedB_preserves_online_ro b.q_total
        (Γ₁ := [authHybridStateFixedTy, .nat]) (Γ₂ := [.nat])
        (Δ := [authHybridStateFixedTy, .nat]) .zero .zero (.cons fhst0 (.cons u0 .nil)) hb0 y hy
        with ⟨h1, h2, h3⟩
      exact ⟨h1.mono (Nat.le_succ nOn), h2, h3⟩)

/-- Atomic `mapComp` shadow simulation for `genSpkFixedKB` on `authFixedShadowStTy`. -/
theorem genSpkFixedShadowB_sim {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hlift : ∀ {Δ out} (c₁ c₂ : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ),
      c₁.eval env = c₂.eval env → (liftPrim c₁).eval env = (liftPrim c₂).eval env)
    (hsupp : ∀ {Δ out} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ) (y : out.denote),
      y ∈ support ((liftPrim c).eval env) → ∃ x ∈ support (c.eval env), x = y)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    (fs : authFixedShadowStTy.denote) (x : ℕ × ℕ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hUnsup : ∀ g, tl.unsupportedW g = 0 := by intro; rfl) :
    let F := AuthKindFuels.ofBudget S b
    let cK := mapComp tl (liftPrim
      (genSpkFixedKB F (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
        (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero))
    let cOld := mapComp tl (liftPrim
      (genSpkFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
        (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero))
    cK.eval (.cons fs.1 (.cons x .nil)) = cOld.eval (.cons fs.1 (.cons x .nil)) ∧
    ∀ rsf ∈ support (cK.eval (.cons fs.1 (.cons x .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, fs.2) := by
  intro F cK cOld
  have hEq : cK.eval (.cons fs.1 (.cons x .nil)) = cOld.eval (.cons fs.1 (.cons x .nil)) :=
    fixedShadow_eval_eq_of_val tl liftPrim hlift (XTy := .prod .nat .nat)
      (genSpkFixedKB F (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
        (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero)
      (genSpkFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
        (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero)
      fs.1 x hSh.online_le hUnsup
      (fun fhst0 x0 hb0 => genSpkFixedKB_fuel_eq S b
        (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
        (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero
        (.cons fhst0 (.cons x0 .nil)) hb0 (Nat.le_of_succ_le hn))
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact fixedShadow_preserve_of_val tl liftPrim hsupp S b (XTy := .prod .nat .nat)
    (genSpkFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat])
      (Γ₂ := [.prod .nat .nat]) (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero)
    fs x hSh hUnsup
    (fun fhst0 x0 hb0 => genSpkFixedB_preserves_online_ro b.q_total
      (Γ₁ := [authHybridStateFixedTy, .prod .nat .nat]) (Γ₂ := [.prod .nat .nat])
      (Δ := [authHybridStateFixedTy, .prod .nat .nat]) .zero .zero
      (.cons fhst0 (.cons x0 .nil)) hb0)

/-- Atomic `mapComp` shadow simulation for `genOpkFixedKB` on `authFixedShadowStTy`. -/
theorem genOpkFixedShadowB_sim {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hlift : ∀ {Δ out} (c₁ c₂ : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ),
      c₁.eval env = c₂.eval env → (liftPrim c₁).eval env = (liftPrim c₂).eval env)
    (hsupp : ∀ {Δ out} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ) (y : out.denote),
      y ∈ support ((liftPrim c).eval env) → ∃ x ∈ support (c.eval env), x = y)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    (fs : authFixedShadowStTy.denote) (x : ℕ × ℕ × ℕ)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hn : nOn + 1 ≤ (AuthKindFuels.ofBudget S b).K_on)
    (hUnsup : ∀ g, tl.unsupportedW g = 0 := by intro; rfl) :
    let F := AuthKindFuels.ofBudget S b
    let XTy := Ty.prod .nat (.prod .nat .nat)
    let cK := mapComp tl (liftPrim
      (genOpkFixedKB F (Γ₁ := [authHybridStateFixedTy, XTy])
        (Γ₂ := [XTy]) (Δ := [authHybridStateFixedTy, XTy]) .zero .zero))
    let cOld := mapComp tl (liftPrim
      (genOpkFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, XTy])
        (Γ₂ := [XTy]) (Δ := [authHybridStateFixedTy, XTy]) .zero .zero))
    cK.eval (.cons fs.1 (.cons x .nil)) = cOld.eval (.cons fs.1 (.cons x .nil)) ∧
    ∀ rsf ∈ support (cK.eval (.cons fs.1 (.cons x .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, fs.2) := by
  intro F XTy cK cOld
  have hEq : cK.eval (.cons fs.1 (.cons x .nil)) = cOld.eval (.cons fs.1 (.cons x .nil)) :=
    fixedShadow_eval_eq_of_val tl liftPrim hlift (XTy := XTy)
      (genOpkFixedKB F (Γ₁ := [authHybridStateFixedTy, XTy])
        (Γ₂ := [XTy]) (Δ := [authHybridStateFixedTy, XTy]) .zero .zero)
      (genOpkFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, XTy])
        (Γ₂ := [XTy]) (Δ := [authHybridStateFixedTy, XTy]) .zero .zero)
      fs.1 x hSh.online_le hUnsup
      (fun fhst0 x0 hb0 => genOpkFixedKB_fuel_eq S b
        (Γ₁ := [authHybridStateFixedTy, XTy]) (Γ₂ := [XTy])
        (Δ := [authHybridStateFixedTy, XTy]) .zero .zero
        (.cons fhst0 (.cons x0 .nil)) hb0 (Nat.le_of_succ_le hn))
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact fixedShadow_preserve_of_val tl liftPrim hsupp S b (XTy := XTy)
    (genOpkFixedB b.q_total (Γ₁ := [authHybridStateFixedTy, XTy])
      (Γ₂ := [XTy]) (Δ := [authHybridStateFixedTy, XTy]) .zero .zero)
    fs x hSh hUnsup
    (fun fhst0 x0 hb0 => genOpkFixedB_preserves_online_ro b.q_total
      (Γ₁ := [authHybridStateFixedTy, XTy]) (Γ₂ := [XTy])
      (Δ := [authHybridStateFixedTy, XTy]) .zero .zero
      (.cons fhst0 (.cons x0 .nil)) hb0)

/-- Atomic `mapComp` shadow preservation for `registerFixedKB` on `authFixedShadowStTy`. -/
theorem registerFixedShadowB_sim {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂)
    (liftPrim : ∀ {Γ out}, Comp pqxdhOps pqPrimIface Γ out → Comp pqxdhOps I₁ Γ out)
    (hsupp : ∀ {Δ out} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ) (y : out.denote),
      y ∈ support ((liftPrim c).eval env) → ∃ x ∈ support (c.eval env), x = y)
    (S : Setup) (b : QueryBudget) {nOn nRo nRoot : ℕ}
    (fs : authFixedShadowStTy.denote) (sk : (PB 32).denote)
    (hSh : AuthFixedShadowAt S b nOn nRo nRoot fs)
    (hUnsup : ∀ g, tl.unsupportedW g = 0 := by intro; rfl) :
    let cReg := mapComp tl (liftPrim
      (registerFixedKB (Γ₁ := [authHybridStateFixedTy, B 32])
        (Γ₂ := [B 32]) (Δ := [authHybridStateFixedTy, B 32]) .zero .zero))
    ∀ rsf ∈ support (cReg.eval (.cons fs.1 (.cons sk .nil))),
      AuthFixedShadowAt S b (nOn + 1) nRo nRoot (rsf.2, fs.2) := by
  intro cReg
  exact fixedShadow_preserve_of_val tl liftPrim hsupp S b (XTy := B 32)
    (registerFixedKB (Γ₁ := [authHybridStateFixedTy, B 32])
      (Γ₂ := [B 32]) (Δ := [authHybridStateFixedTy, B 32]) .zero .zero)
    fs sk hSh hUnsup
    (fun fhst0 sk0 hb0 => registerFixedKB_preserves_online_ro
      (Γ₁ := [authHybridStateFixedTy, B 32]) (Γ₂ := [B 32])
      (Δ := [authHybridStateFixedTy, B 32]) .zero .zero
      (.cons fhst0 (.cons sk0 .nil)) hb0)

end FixedNonSession

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArmsFixed
