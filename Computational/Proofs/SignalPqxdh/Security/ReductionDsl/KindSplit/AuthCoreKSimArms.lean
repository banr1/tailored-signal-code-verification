/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine

/-!
# Clamped Non-Session Arms, Handshake Helpers, and `finish` Fuel Equivalences

Fuel-equivalence and online-list/RO-cache preservation lemmas for clamped `AuthHs` base arms,
handshake helpers, and `finish` steps (`finalizeAuthFixedKDsl`, `shcrExtractC`, and `hmFinishC`).
Fixed non-session arm lemmas live in `AuthCoreKSimArmsFixed`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal mapComp)
open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl
  (authStateTy preKeyBundleTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext sendQTy shcrStTy
   initPrin1KeyB corruptB genSpkB genOpkB registerB
   findHonestC isGameOpkC extractC preCheckC checkSigsC shcrExtractC)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateTy authHybridStateFixedTy
   initPrin1KeyFixedB corruptFixedB genSpkFixedB genOpkFixedB registerFixedB
   finalizeAuthFixedDsl)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (hmStTy hmFinishC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels authFixedShadowStTy forgetAuthFixedShadow
   initPrin1KeyFuelB initPrin1KeyKB corruptKB genSpkKB genOpkKB registerKB extractKC
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB
   finalizeAuthFixedKDsl)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (AuthBaseValOnlineBounded AuthFixedValOnlineBounded
   valRoCache valRootRoCache AuthFixedShadowAt)

section BaseArms

open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (take_min_left_of_length_le)
open _root_.SignalPqxdh.Security.ReductionDsl
  (principalEntryTy spkBundleEntryTy opkEntryTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (v eAny eFind eMap letV bindV caseOptV findMV anyMV
   stSecb stHasWon stPrin stSpks stOpks stSess stUsedS stUsedO stUsedN
   stKyb stSOE stSNE stROE stRNE stRo stRoot stAdv stMk stUpd rs
   isAdvRegC isGameSpkC koskBundleOkC resolveSigPkC honestPeerC)

private theorem baseTuple_preserves_online_ro {m n : ℕ}
    (s0 : authStateTy.denote)
    (prin : (Ty.list (.prod .nat principalEntryTy)).denote)
    (spks : (Ty.list (.prod (.prod .nat .nat) spkBundleEntryTy)).denote)
    (opks : (Ty.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)).denote)
    (adv : (Ty.list (.prod (B 32) (B 32))).denote)
    (hb : AuthBaseValOnlineBounded m s0) (hmn : m ≤ n)
    (hp : prin.length ≤ n) (hs : spks.length ≤ n)
    (ho : opks.length ≤ n) (ha : adv.length ≤ n) :
    let s' : authStateTy.denote :=
      (s0.1, s0.2.1, prin, spks, opks, s0.2.2.2.2.2.1, s0.2.2.2.2.2.2.1,
       s0.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.2.1,
       s0.2.2.2.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.2.2.2.1,
       s0.2.2.2.2.2.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
       s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, adv)
    AuthBaseValOnlineBounded n s' ∧
    valRoCache s' = valRoCache s0 ∧
    valRootRoCache s' = valRootRoCache s0 :=
  ⟨{ principals_le        := hp
     spkBundles_le        := hs
     opkEntries_le        := ho
     sessions_le          := Nat.le_trans hb.sessions_le hmn
     usedSendSessions_le  := Nat.le_trans hb.usedSendSessions_le hmn
     usedRecvOPK_le       := Nat.le_trans hb.usedRecvOPK_le hmn
     usedRecvNoOPK_le     := Nat.le_trans hb.usedRecvNoOPK_le hmn
     seenKyberBaseKeys_le := Nat.le_trans hb.seenKyberBaseKeys_le hmn
     sentOPKEvents_le     := Nat.le_trans hb.sentOPKEvents_le hmn
     sentNoOPKEvents_le   := Nat.le_trans hb.sentNoOPKEvents_le hmn
     recvdOPKEvents_le    := Nat.le_trans hb.recvdOPKEvents_le hmn
     recvdNoOPKEvents_le  := Nat.le_trans hb.recvdNoOPKEvents_le hmn
     advKeys_le           := ha },
   rfl, rfl⟩

theorem initPrin1KeyFuelB_fuel_eq (K Q : ℕ) {n : ℕ} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hK : n ≤ K) (hQ : n ≤ Q) :
    (initPrin1KeyFuelB K st u).eval env = (initPrin1KeyB Q st u).eval env := by
  have hTK := List.take_of_length_le (Nat.le_trans hb.principals_le hK)
  have hTQ := List.take_of_length_le (Nat.le_trans hb.principals_le hQ)
  simp only [initPrin1KeyFuelB, initPrin1KeyB, eAny, stPrin, v, Comp.eval, Expr.eval, hTK, hTQ]

theorem initPrin1KeyKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (initPrin1KeyKB (AuthKindFuels.ofBudget S b) st u).eval env =
      (initPrin1KeyB b.q_total st u).eval env := by
  exact initPrin1KeyFuelB_fuel_eq _ _ st u env hb hn
    (Nat.le_trans hn (AuthKindFuels.K_on_le_q_total S b))

theorem initPrin1KeyB_preserves_online_ro (Q : ℕ) {n : ℕ} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st))) :
    ∀ rs ∈ support ((initPrin1KeyB Q st u).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2 ∧
      valRoCache rs.2 = valRoCache (env.get (h₁.wk st)) ∧
      valRootRoCache rs.2 = valRootRoCache (env.get (h₁.wk st)) := by
  intro out hout
  simp only [initPrin1KeyB, Comp.iteC, bindV, Comp.eval] at hout
  split_ifs at hout
  · simp only [rs, v, Expr.eval, mem_support_pure_iff] at hout
    subst hout
    exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
    rcases hout with ⟨s0, _, ik, _, rfl⟩
    simp only [rs, stUpd, stMk, stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS,
      stUsedO, stUsedN, stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
      Expr.listCons, v, Expr.eval]
    exact baseTuple_preserves_online_ro (env.get (h₁.wk st)) _ _ _ _ hb (Nat.le_succ n)
      (Nat.succ_le_succ hb.principals_le)
      (Nat.le_trans hb.spkBundles_le (Nat.le_succ n))
      (Nat.le_trans hb.opkEntries_le (Nat.le_succ n))
      (Nat.le_trans hb.advKeys_le (Nat.le_succ n))

theorem corruptKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (corruptKB (AuthKindFuels.ofBudget S b) st u).eval env =
      (corruptB b.q_total st u).eval env := by
  have hK := Nat.le_trans hb.principals_le hn
  have hQ := Nat.le_trans hK (AuthKindFuels.K_on_le_q_total S b)
  have hget : ∀ (x : (Ty.prod .nat principalEntryTy).denote),
      (Env.cons x env).get ((@Ext.step _ _ _ h₁).wk st) = env.get (h₁.wk st) := fun _ => rfl
  simp only [corruptKB, corruptB, caseOptV, Comp.caseOptC, eFind, Expr.findBounded,
    stPrin, v, Comp.eval, Expr.eval, List.take_of_length_le hK, List.take_of_length_le hQ]
  split
  · rfl
  · simp only [rs, stUpd, stMk, eMap, Expr.mapBounded, Expr.eval, hget,
      List.take_of_length_le hK, List.take_of_length_le hQ]

theorem corruptB_preserves_online_ro (Q : ℕ) {n : ℕ} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st))) :
    ∀ rs ∈ support ((corruptB Q st u).eval env),
      AuthBaseValOnlineBounded n rs.2 ∧
      valRoCache rs.2 = valRoCache (env.get (h₁.wk st)) ∧
      valRootRoCache rs.2 = valRootRoCache (env.get (h₁.wk st)) := by
  intro out hout
  simp only [corruptB, caseOptV, Comp.caseOptC, Comp.eval] at hout
  split at hout
  · simp only [rs, v, Expr.eval, mem_support_pure_iff] at hout
    subst hout
    exact ⟨hb, rfl, rfl⟩
  · rename_i eVal _
    simp only [mem_support_pure_iff] at hout
    subst hout
    simp only [rs, stUpd, stMk, stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS,
      stUsedO, stUsedN, stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
      eMap, Expr.mapBounded, v, Expr.eval]
    refine baseTuple_preserves_online_ro (env.get (h₁.wk st)) _ _ _ _ hb (Nat.le_refl n)
      ?_ hb.spkBundles_le hb.opkEntries_le hb.advKeys_le
    simp only [List.length_map, List.length_take]
    exact Nat.le_trans (Nat.min_le_right _ _) hb.principals_le

theorem genSpkKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (genSpkKB (AuthKindFuels.ofBudget S b) st x).eval env =
      (genSpkB b.q_total st x).eval env := by
  have hSK := List.take_of_length_le (Nat.le_trans hb.spkBundles_le hn)
  have hSQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.spkBundles_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hPK := List.take_of_length_le (Nat.le_trans hb.principals_le hn)
  have hPQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.principals_le hn) (AuthKindFuels.K_on_le_q_total S b))
  simp only [genSpkKB, genSpkB, Comp.iteC, caseOptV, Comp.caseOptC, eAny, Expr.anyBounded,
    eFind, Expr.findBounded, stSpks, stPrin, v, Comp.eval, Expr.eval, hSK, hSQ, hPK, hPQ]

theorem genSpkB_preserves_online_ro (Q : ℕ) {n : ℕ} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st))) :
    ∀ rs ∈ support ((genSpkB Q st x).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2 ∧
      valRoCache rs.2 = valRoCache (env.get (h₁.wk st)) ∧
      valRootRoCache rs.2 = valRootRoCache (env.get (h₁.wk st)) := by
  intro out hout
  simp only [genSpkB, Comp.iteC, caseOptV, Comp.caseOptC, bindV, Comp.eval] at hout
  split_ifs at hout
  · simp only [rs, v, Expr.eval, mem_support_pure_iff] at hout
    subst hout
    exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · split at hout
    · simp only [rs, v, Expr.eval, mem_support_pure_iff] at hout
      subst hout
      exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
      rcases hout with ⟨spkSk, _, spkPk, _, r1, _, sig1, _, seed, _, kp, _, r2, _, sig2, _, rfl⟩
      simp only [rs, stUpd, stMk, stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS,
        stUsedO, stUsedN, stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
        Expr.listCons, v, Expr.eval]
      exact baseTuple_preserves_online_ro (env.get (h₁.wk st)) _ _ _ _ hb (Nat.le_succ n)
        (Nat.le_trans hb.principals_le (Nat.le_succ n))
        (Nat.succ_le_succ hb.spkBundles_le)
        (Nat.le_trans hb.opkEntries_le (Nat.le_succ n))
        (Nat.le_trans hb.advKeys_le (Nat.le_succ n))

theorem genOpkKB_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (genOpkKB (AuthKindFuels.ofBudget S b) st x).eval env =
      (genOpkB b.q_total st x).eval env := by
  have hOK := List.take_of_length_le (Nat.le_trans hb.opkEntries_le hn)
  have hOQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.opkEntries_le hn) (AuthKindFuels.K_on_le_q_total S b))
  simp only [genOpkKB, genOpkB, eAny, stOpks, v, Comp.eval, Expr.eval, hOK, hOQ]

theorem genOpkB_preserves_online_ro (Q : ℕ) {n : ℕ} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st))) :
    ∀ rs ∈ support ((genOpkB Q st x).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2 ∧
      valRoCache rs.2 = valRoCache (env.get (h₁.wk st)) ∧
      valRootRoCache rs.2 = valRootRoCache (env.get (h₁.wk st)) := by
  intro out hout
  simp only [genOpkB, Comp.iteC, bindV, Comp.eval] at hout
  split_ifs at hout
  · simp only [rs, v, Expr.eval, mem_support_pure_iff] at hout
    subst hout
    exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
    rcases hout with ⟨sk, _, pk, _, rfl⟩
    simp only [rs, stUpd, stMk, stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS,
      stUsedO, stUsedN, stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
      Expr.listCons, v, Expr.eval]
    exact baseTuple_preserves_online_ro (env.get (h₁.wk st)) _ _ _ _ hb (Nat.le_succ n)
      (Nat.le_trans hb.principals_le (Nat.le_succ n))
      (Nat.le_trans hb.spkBundles_le (Nat.le_succ n))
      (Nat.succ_le_succ hb.opkEntries_le)
      (Nat.le_trans hb.advKeys_le (Nat.le_succ n))

theorem registerKB_preserves_online_ro {n : ℕ} {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (B 32))
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st))) :
    ∀ rs ∈ support ((registerKB st sk).eval env),
      AuthBaseValOnlineBounded (n + 1) rs.2 ∧
      valRoCache rs.2 = valRoCache (env.get (h₁.wk st)) ∧
      valRootRoCache rs.2 = valRootRoCache (env.get (h₁.wk st)) := by
  intro out hout
  simp only [registerKB, registerB, Comp.iteC, bindV, Comp.eval] at hout
  split_ifs at hout
  · simp only [rs, v, Expr.eval, mem_support_pure_iff] at hout
    subst hout
    exact ⟨hb.mono (Nat.le_succ n), rfl, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hout
    rcases hout with ⟨pk, _, p8, _, rfl⟩
    simp only [rs, stUpd, stMk, stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS,
      stUsedO, stUsedN, stKyb, stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv,
      Expr.listCons, v, Expr.eval]
    exact baseTuple_preserves_online_ro (env.get (h₁.wk st)) _ _ _ _ hb (Nat.le_succ n)
      (Nat.le_trans hb.principals_le (Nat.le_succ n))
      (Nat.le_trans hb.spkBundles_le (Nat.le_succ n))
      (Nat.le_trans hb.opkEntries_le (Nat.le_succ n))
      (Nat.succ_le_succ hb.advKeys_le)

theorem findHonestC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (findHonestC S (AuthKindFuels.ofBudget S b).K_on st ik).eval env =
      (findHonestC S b.q_total st ik).eval env := by
  have hPK := take_min_left_of_length_le S.N_dh (Nat.le_trans hb.principals_le hn)
  have hPQ := take_min_left_of_length_le S.N_dh
    (Nat.le_trans (Nat.le_trans hb.principals_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hget : (Env.cons (ik.eval env) env).get ((@Ext.step _ _ _ h).wk st) = env.get (h.wk st) := rfl
  simp only [findHonestC, letV, Comp.letC, findMV, Comp.findBoundedM, stPrin, v,
    Comp.eval, Expr.eval, pure_bind, hget, hPK, hPQ]

theorem isGameOpkC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (isGameOpkC S (AuthKindFuels.ofBudget S b).K_on st pk).eval env =
      (isGameOpkC S b.q_total st pk).eval env := by
  have hOK := take_min_left_of_length_le S.N_dh (Nat.le_trans hb.opkEntries_le hn)
  have hOQ := take_min_left_of_length_le S.N_dh
    (Nat.le_trans (Nat.le_trans hb.opkEntries_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hget : (Env.cons (pk.eval env) env).get ((@Ext.step _ _ _ h).wk st) = env.get (h.wk st) := rfl
  simp only [isGameOpkC, letV, Comp.letC, anyMV, Comp.anyBoundedM, stOpks, v,
    Comp.eval, Expr.eval, pure_bind, hget, hOK, hOQ]

private theorem isAdvRegC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (isAdvRegC (AuthKindFuels.ofBudget S b).K_on st pk).eval env =
      (isAdvRegC b.q_total st pk).eval env := by
  have hAK := List.take_of_length_le (Nat.le_trans hb.advKeys_le hn)
  have hAQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.advKeys_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hget : ∀ (p : (B 32).denote),
      (Env.cons p env).get ((@Ext.step _ _ _ h).wk st) = env.get (h.wk st) := fun _ => rfl
  simp only [isAdvRegC, bindV, eAny, Expr.anyBounded, stAdv, v,
    Comp.eval, Expr.eval, hget, hAK, hAQ]

private theorem isGameSpkC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (isGameSpkC S (AuthKindFuels.ofBudget S b).K_on st pk).eval env =
      (isGameSpkC S b.q_total st pk).eval env := by
  have hSK := take_min_left_of_length_le S.N_dh (Nat.le_trans hb.spkBundles_le hn)
  have hSQ := take_min_left_of_length_le S.N_dh
    (Nat.le_trans (Nat.le_trans hb.spkBundles_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hget : (Env.cons (pk.eval env) env).get ((@Ext.step _ _ _ h).wk st) = env.get (h.wk st) := rfl
  simp only [isGameSpkC, letV, Comp.letC, anyMV, Comp.anyBoundedM, stSpks, v,
    Comp.eval, Expr.eval, pure_bind, hget, hSK, hSQ]

private theorem koskBundleOkC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (koskBundleOkC S (AuthKindFuels.ofBudget S b).K_on st bu).eval env =
      (koskBundleOkC S b.q_total st bu).eval env := by
  dsimp only [koskBundleOkC, bindV, caseOptV, Comp.caseOptC, Comp.eval]
  rw [findHonestC_fuel_eq S b st _ env hb hn]; congr 1; funext f
  rw [isAdvRegC_fuel_eq S b st _ (.cons f env) hb hn]; congr 1; funext idA
  rw [isGameSpkC_fuel_eq S b st _ (.cons idA (.cons f env)) hb hn]; congr 1; funext spkG
  rw [isAdvRegC_fuel_eq S b st _ (.cons spkG (.cons idA (.cons f env))) hb hn]; congr 1; funext spkA
  split
  · rfl
  · rename_i o _
    rw [isGameOpkC_fuel_eq S b st _ (.cons o (.cons spkA (.cons spkG (.cons idA (.cons f env))))) hb hn]
    congr 1; funext opkG
    rw [isAdvRegC_fuel_eq S b st _
      (.cons opkG (.cons o (.cons spkA (.cons spkG (.cons idA (.cons f env)))))) hb hn]

private theorem resolveSigPkC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (resolveSigPkC S (AuthKindFuels.ofBudget S b).K_on st ik).eval env =
      (resolveSigPkC S b.q_total st ik).eval env := by
  dsimp only [resolveSigPkC, letV, Comp.letC, bindV, Comp.eval]
  simp only [pure_bind]
  rw [findHonestC_fuel_eq S b st (h := @Ext.step _ _ _ h) (v Var.vz) (.cons (ik.eval env) env) hb hn]

private theorem honestPeerC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ Δ : List (Ty pqSig)} (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (honestPeerC S (AuthKindFuels.ofBudget S b).K_on st ik).eval env =
      (honestPeerC S b.q_total st ik).eval env := by
  dsimp only [honestPeerC, bindV, Comp.eval]
  rw [findHonestC_fuel_eq S b st ik env hb hn]

theorem extractKC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32))
    (st : Var Γ₃ authStateTy) (bu : Var Γ₄ preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₃.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (extractKC S (AuthKindFuels.ofBudget S b) tp tpk st bu).eval env =
      (extractC S b.q_total tp tpk st bu).eval env := by
  have hSK := List.take_of_length_le (Nat.le_trans hb.spkBundles_le hn)
  have hSQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.spkBundles_le hn) (AuthKindFuels.K_on_le_q_total S b))
  dsimp only [extractKC, extractC, bindV, Comp.eval]
  rw [honestPeerC_fuel_eq S b st _ env hb hn]
  refine congrArg (_ >>= ·) (funext fun peer =>
    congrArg (_ >>= ·) (funext fun v1 =>
      congrArg (_ >>= ·) (funext fun v2 => ?_)))
  have hpeer : (Env.cons (t := .bool) v2
      (Env.cons (t := .bool) v1 (Env.cons (t := .opt .nat) peer env))).get
      ((@Ext.step _ _ _ (@Ext.step _ _ _ (@Ext.refl _))).wk Var.vz) = peer := rfl
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt, v, Expr.eval, hpeer]
  cases peer with
  | none => rfl
  | some k =>
    have hget : (Env.cons (t := .nat) k
        (Env.cons (t := .bool) v2 (Env.cons (t := .bool) v1 (Env.cons (t := .opt .nat) (some k) env)))).get
        ((@Ext.step _ _ _ (@Ext.step _ _ _ (@Ext.step _ _ _ (@Ext.step _ _ _ h₃)))).wk st) =
      env.get (h₃.wk st) := rfl
    simp only [eAny, Expr.anyBounded, stSpks, Expr.eval, hget, hSK, hSQ]

theorem preCheckC_fuel_eq (S : Setup) (b : QueryBudget) (opk : Bool) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (preCheckC S (AuthKindFuels.ofBudget S b).K_on opk st x).eval env =
      (preCheckC S b.q_total opk st x).eval env := by
  have hUK := List.take_of_length_le (Nat.le_trans hb.usedSendSessions_le hn)
  have hUQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.usedSendSessions_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hPK := List.take_of_length_le (Nat.le_trans hb.principals_le hn)
  have hPQ := List.take_of_length_le
    (Nat.le_trans (Nat.le_trans hb.principals_le hn) (AuthKindFuels.K_on_le_q_total S b))
  have hget4 : ∀ {τ₁ τ₂ τ₃ τ₄ : Ty pqSig}
      (a : τ₁.denote) (b1 : τ₂.denote) (c : τ₃.denote) (d : τ₄.denote),
      (Env.cons a (Env.cons b1 (Env.cons c (Env.cons d env)))).get
        ((@Ext.step _ _ _ (@Ext.step _ _ _ (@Ext.step _ _ _ (@Ext.step _ _ _ h₁)))).wk st) =
      env.get (h₁.wk st) := fun _ _ _ _ => rfl
  dsimp only [preCheckC, letV, Comp.letC, Comp.iteC, caseOptV, Comp.caseOptC, bindV, Comp.eval]
  simp only [pure_bind]
  refine congrArg _ ?_
  simp only [eAny, Expr.anyBounded, eFind, Expr.findBounded, stUsedS, stPrin, v,
    Expr.eval, hget4, hUK, hUQ, hPK, hPQ]
  refine congrArg _ ?_
  refine congrArg _ (funext fun uE => ?_)
  rw [findHonestC_fuel_eq S b st _ (.cons uE (.cons _ (.cons _ (.cons _ (.cons _ env))))) hb hn]
  refine congrArg (_ >>= ·) (funext fun pp => ?_)
  refine congrArg _ ?_
  rw [koskBundleOkC_fuel_eq S b st _
    (.cons _ (.cons pp (.cons uE (.cons _ (.cons _ (.cons _ (.cons _ env))))))) hb hn]

theorem checkSigsC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁.wk st)))
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (checkSigsC S (AuthKindFuels.ofBudget S b).K_on st bu).eval env =
      (checkSigsC S b.q_total st bu).eval env := by
  dsimp only [checkSigsC, bindV, Comp.eval]
  rw [resolveSigPkC_fuel_eq S b st _ env hb hn]

end BaseArms

section FinishFuelEq

open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (take_min_left_of_length_le)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (allHonestEcPksAuthDslK asPrincipals asSpkBundles asOpkEntries asSessions
   ahsBase ahsInitKemRecs ahsRecvKemRecs sbPqspkPk
   hasDuplicateBytesDsl_eval finalizeAuthFixedBodyDsl hasBadSigAuthDsl
   hasKemPkCollisionAuthDsl hasBadKemShCrRecordsDsl notAllChallengedCleanDsl
   eLet eMap eAny v letV_eval bindV_eval natEq_eval bytesBeq_eval boolOr_eval)

private theorem bind_congr_of_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a ∈ support mx, f a = g a) :
    (mx >>= f) = (mx >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    congr 1; ext u
    exact ih u (fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩))

private theorem mapML_length_eq {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (f : α → OracleComp spec β) (xs : List α) :
    ∀ ys ∈ support (_root_.ReductionDsl.mapML f xs), ys.length = xs.length := by
  induction xs with
  | nil =>
    intro ys hys
    simp [_root_.ReductionDsl.mapML] at hys
    simp [hys]
  | cons x xs ih =>
    intro ys hys
    simp only [_root_.ReductionDsl.mapML, mem_support_bind_iff, mem_support_pure_iff] at hys
    rcases hys with ⟨y, _, ys', hys', rfl⟩
    simp [ih ys' hys']

private theorem allHonestEcPksAuthDslK_fuel_indep (S : Setup) {K₁ K₂ n : ℕ}
    {Γ : List (Ty pqSig)} (st : authStateTy.denote) (env : Env Γ)
    (hBase : AuthBaseValOnlineBounded n st) (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (allHonestEcPksAuthDslK S K₁).eval (.cons st env) =
      (allHonestEcPksAuthDslK S K₂).eval (.cons st env) ∧
    ∀ ecPks ∈ support ((allHonestEcPksAuthDslK S K₁).eval (.cons st env)),
      ecPks.length ≤ 4 * min n S.N_dh := by
  have hP1 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.principals_le h₁)
  have hP2 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.principals_le h₂)
  have hS1 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.spkBundles_le h₁)
  have hS2 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.spkBundles_le h₂)
  have hO1 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.opkEntries_le h₁)
  have hO2 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.opkEntries_le h₂)
  have hSe1 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.sessions_le h₁)
  have hSe2 := take_min_left_of_length_le S.N_dh (Nat.le_trans hBase.sessions_le h₂)
  have hLP : (st.2.2.1.take S.N_dh).length ≤ min n S.N_dh := by
    have := hBase.principals_le; simp only [List.length_take]; omega
  have hLS : (st.2.2.2.1.take S.N_dh).length ≤ min n S.N_dh := by
    have := hBase.spkBundles_le; simp only [List.length_take]; omega
  have hLO : (st.2.2.2.2.1.take S.N_dh).length ≤ min n S.N_dh := by
    have := hBase.opkEntries_le; simp only [List.length_take]; omega
  have hLSe : (st.2.2.2.2.2.1.take S.N_dh).length ≤ min n S.N_dh := by
    have := hBase.sessions_le; simp only [List.length_take]; omega
  constructor
  · simp only [asPrincipals, asSpkBundles,
      asOpkEntries, asSessions, Comp.eval, Expr.eval, Env.get,
      hP1, hP2, hS1, hS2, hO1, hO2, hSe1, hSe2]
    refine bind_congr_of_support _ _ _ fun p1 hp1 =>
      bind_congr_of_support _ _ _ fun p2 hp2 =>
      bind_congr_of_support _ _ _ fun p3 hp3 =>
      bind_congr_of_support _ _ _ fun p4 hp4 => ?_
    have hp1L := mapML_length_eq _ _ p1 hp1
    have hp2L := mapML_length_eq _ _ p2 hp2
    have hp3L := mapML_length_eq _ _ p3 hp3
    have hp4L := mapML_length_eq _ _ p4 hp4
    have h12_1 : (p1 ++ p2).length ≤ 4 * min K₁ S.N_dh := by simp [List.length_append]; omega
    have h12_2 : (p1 ++ p2).length ≤ 4 * min K₂ S.N_dh := by simp [List.length_append]; omega
    have h123_1 : (p1 ++ p2 ++ p3).length ≤ 4 * min K₁ S.N_dh := by simp [List.length_append]; omega
    have h123_2 : (p1 ++ p2 ++ p3).length ≤ 4 * min K₂ S.N_dh := by simp [List.length_append]; omega
    have h1234_1 : (p1 ++ p2 ++ p3 ++ p4).length ≤ 4 * min K₁ S.N_dh := by
      simp [List.length_append]; omega
    have h1234_2 : (p1 ++ p2 ++ p3 ++ p4).length ≤ 4 * min K₂ S.N_dh := by
      simp [List.length_append]; omega
    rw [List.take_of_length_le h12_1, List.take_of_length_le h123_1, List.take_of_length_le h1234_1,
      List.take_of_length_le h12_2, List.take_of_length_le h123_2, List.take_of_length_le h1234_2]
  · intro ecPks hec
    simp only [asPrincipals, asSpkBundles,
      asOpkEntries, asSessions, Comp.eval, Expr.eval, Env.get,
      hP1, hS1, hO1, hSe1, mem_support_bind_iff, mem_support_pure_iff] at hec
    rcases hec with ⟨p1, hp1, p2, hp2, p3, hp3, p4, hp4, rfl⟩
    have hp1L := mapML_length_eq _ _ p1 hp1
    have hp2L := mapML_length_eq _ _ p2 hp2
    have hp3L := mapML_length_eq _ _ p3 hp3
    have hp4L := mapML_length_eq _ _ p4 hp4
    have h12_1 : (p1 ++ p2).length ≤ 4 * min K₁ S.N_dh := by simp [List.length_append]; omega
    have h123_1 : (p1 ++ p2 ++ p3).length ≤ 4 * min K₁ S.N_dh := by simp [List.length_append]; omega
    have h1234_1 : (p1 ++ p2 ++ p3 ++ p4).length ≤ 4 * min K₁ S.N_dh := by
      simp [List.length_append]; omega
    rw [List.take_of_length_le h12_1, List.take_of_length_le h123_1, List.take_of_length_le h1234_1]
    simp only [List.length_append]; omega

theorem finalizeAuthFixedKDsl_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ : List (Ty pqSig)}
    (hst : authHybridStateTy.denote) (b' secb : Bool) (env : Env Γ)
    (hBase : AuthBaseValOnlineBounded n hst.1)
    (hInitKem : hst.2.1.length ≤ n)
    (hRecvKem : hst.2.2.1.length ≤ n)
    (hIdeal : hst.2.2.2.length ≤ n)
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (finalizeAuthFixedKDsl S (AuthKindFuels.ofBudget S b)).eval
        (.cons hst (.cons b' (.cons secb env))) =
      (finalizeAuthFixedDsl S b.q_total).eval
        (.cons hst (.cons b' (.cons secb env))) := by
  let _ := hIdeal
  let K₁ := (AuthKindFuels.ofBudget S b).K_on
  let K₂ := b.q_total
  have h₂ : n ≤ K₂ := Nat.le_trans hn (AuthKindFuels.K_on_le_q_total S b)
  obtain ⟨hEcEq, hEcLen⟩ :=
    allHonestEcPksAuthDslK_fuel_indep S (Γ := authHybridStateTy :: .bool :: .bool :: Γ) hst.1
      (Env.cons (t := authHybridStateTy) hst
        (Env.cons (t := .bool) b' (Env.cons (t := .bool) secb env))) hBase hn h₂
  simp only [finalizeAuthFixedKDsl, finalizeAuthFixedDsl,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eval_letC, ahsBase,
    Expr.eval, Env.get]
  change ((allHonestEcPksAuthDslK S K₁).eval _ >>= fun ecPks =>
      (finalizeAuthFixedBodyDsl S K₁).eval (.cons ecPks _)) =
    ((allHonestEcPksAuthDslK S K₂).eval _ >>= fun ecPks =>
      (finalizeAuthFixedBodyDsl S K₂).eval (.cons ecPks _))
  rw [← hEcEq]
  refine bind_congr_of_support _ _ _ fun ecPks hec => ?_
  have hLenN := hEcLen ecPks hec
  have hEc1 : ecPks.length ≤ 4 * min K₁ S.N_dh := by omega
  have hEc2 : ecPks.length ≤ 4 * min K₂ S.N_dh := by omega
  let envBody : Env (.list (B 32) :: authStateTy :: authHybridStateTy :: .bool :: .bool :: Γ) :=
    Env.cons (t := .list (B 32)) ecPks
      (Env.cons (t := authStateTy) hst.1
        (Env.cons (t := authHybridStateTy) hst
          (Env.cons (t := .bool) b'
            (Env.cons (t := .bool) secb env))))
  have hDup1 := hasDuplicateBytesDsl_eval 32 (4 * min K₁ S.N_dh) (.var .zero) envBody hEc1
  have hDup2 := hasDuplicateBytesDsl_eval 32 (4 * min K₂ S.N_dh) (.var .zero) envBody hEc2
  have hSpk1 : hst.1.2.2.2.1.length ≤ K₁ := Nat.le_trans hBase.spkBundles_le hn
  have hSpk2 : hst.1.2.2.2.1.length ≤ K₂ := Nat.le_trans hBase.spkBundles_le h₂
  have hSess1 : hst.1.2.2.2.2.2.1.length ≤ K₁ := Nat.le_trans hBase.sessions_le hn
  have hSess2 : hst.1.2.2.2.2.2.1.length ≤ K₂ := Nat.le_trans hBase.sessions_le h₂
  have hIK1 : hst.2.1.length ≤ K₁ := Nat.le_trans hInitKem hn
  have hIK2 : hst.2.1.length ≤ K₂ := Nat.le_trans hInitKem h₂
  have hRK1 : hst.2.2.1.length ≤ K₁ := Nat.le_trans hRecvKem hn
  have hRK2 : hst.2.2.1.length ≤ K₂ := Nat.le_trans hRecvKem h₂
  have hKem1 := hasDuplicateBytesDsl_eval 1568 K₁
    (.mapB K₁ (asSpkBundles (ahsBase (.var (.succ (.succ .zero)))))
      (sbPqspkPk (.snd (.var .zero))))
    envBody
    (by simp only [envBody, asSpkBundles, ahsBase, Expr.eval, Env.get,
          List.take_of_length_le hSpk1, List.length_map]; exact hSpk1)
  have hKem2 := hasDuplicateBytesDsl_eval 1568 K₂
    (.mapB K₂ (asSpkBundles (ahsBase (.var (.succ (.succ .zero)))))
      (sbPqspkPk (.snd (.var .zero))))
    envBody
    (by simp only [envBody, asSpkBundles, ahsBase, Expr.eval, Env.get,
          List.take_of_length_le hSpk2, List.length_map]; exact hSpk2)
  change (finalizeAuthFixedBodyDsl S K₁).eval envBody =
    (finalizeAuthFixedBodyDsl S K₂).eval envBody
  simp only [finalizeAuthFixedBodyDsl, hasKemPkCollisionAuthDsl, boolOr_eval, Comp.eval,
    hDup1, hDup2, hKem1, hKem2]
  simp only [hasBadSigAuthDsl, hasBadKemShCrRecordsDsl,
    notAllChallengedCleanDsl, ahsBase, asSessions,
    asSpkBundles, ahsInitKemRecs, ahsRecvKemRecs,
    eLet, eAny, v, boolOr_eval, envBody, Expr.eval, Env.get,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.step_wk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.refl_wk,
    List.take_of_length_le hSpk1, List.take_of_length_le hSpk2,
    List.take_of_length_le hSess1, List.take_of_length_le hSess2,
    List.take_of_length_le hIK1, List.take_of_length_le hIK2,
    List.take_of_length_le hRK1, List.take_of_length_le hRK2]

theorem shcrExtractC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    {Γ₁ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (hRR : (env.get (h₃.wk s)).2.2.2.2.2.2.1.length ≤ n)
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (shcrExtractC (AuthKindFuels.ofBudget S b).K_on sc s).eval env =
      (shcrExtractC b.q_total sc s).eval env := by
  have hK : (env.get (h₃.wk s)).2.2.2.2.2.2.1.length ≤ (AuthKindFuels.ofBudget S b).K_on :=
    Nat.le_trans hRR hn
  have hQ : (env.get (h₃.wk s)).2.2.2.2.2.2.1.length ≤ b.q_total :=
    Nat.le_trans hK (AuthKindFuels.K_on_le_q_total S b)
  simp only [shcrExtractC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.findMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.scRR,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v,
    Comp.eval, Expr.eval, List.take_of_length_le hK, List.take_of_length_le hQ]

private theorem hmFinishC_fuel_indep {K₁ K₂ : ℕ} (s : hmStTy.denote) (b' : Bool)
    (h₁ : s.2.2.2.2.1.length ≤ K₁) (h₂ : s.2.2.2.2.1.length ≤ K₂) :
    (hmFinishC K₁).eval (.cons s (.cons b' .nil)) =
      (hmFinishC K₂).eval (.cons s (.cons b' .nil)) := by
  have hT1 : s.2.2.2.2.1.take K₁ = s.2.2.2.2.1 := List.take_of_length_le h₁
  have hT2 : s.2.2.2.2.1.take K₂ = s.2.2.2.2.1 := List.take_of_length_le h₂
  have hL1 : (s.2.2.2.2.1.map fun e => (e.1, e.2.1)).length ≤ K₁ := by simpa using h₁
  have hL2 : (s.2.2.2.2.1.map fun e => (e.1, e.2.1)).length ≤ K₂ := by simpa using h₂
  have hM1 : (s.2.2.2.2.1.map fun e => (e.1, e.2.1)).take K₁ =
      s.2.2.2.2.1.map fun e => (e.1, e.2.1) := List.take_of_length_le hL1
  have hM2 : (s.2.2.2.2.1.map fun e => (e.1, e.2.1)).take K₂ =
      s.2.2.2.2.1.map fun e => (e.1, e.2.1) := List.take_of_length_le hL2
  have hDL1 : (s.2.2.2.2.1.map fun e => (e.1, e.2.1)).dedup.length ≤ K₁ :=
    (List.dedup_sublist _).length_le.trans hL1
  have hDL2 : (s.2.2.2.2.1.map fun e => (e.1, e.2.1)).dedup.length ≤ K₂ :=
    (List.dedup_sublist _).length_le.trans hL2
  simp only [hmFinishC, letV_eval, bindV_eval,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.mapMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.dedupE,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.pendHitE,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.muPend,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.muBad,
    eMap, eAny, v,
    natEq_eval, bytesBeq_eval, boolOr_eval,
    Comp.eval, Expr.eval,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.step_wk,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext.refl_wk,
    Env.get, hT1, hT2]
  simp only [hM1, hM2]
  rw [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.foldr_dedup_eq K₁ _ hL1,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.foldr_dedup_eq K₂ _ hL2,
    List.take_of_length_le hDL1, List.take_of_length_le hDL2]
  refine bind_congr_of_support _ _ _ fun hits hhits => ?_
  have hHL := mapML_length_eq _ _ hits hhits
  rw [List.take_of_length_le (hHL.le.trans hDL1), List.take_of_length_le (hHL.le.trans hDL2)]

theorem hmFinishC_fuel_eq (S : Setup) (b : QueryBudget) {n : ℕ}
    (s : hmStTy.denote) (b' : Bool)
    (hPend : s.2.2.2.2.1.length ≤ n)
    (hn : n ≤ (AuthKindFuels.ofBudget S b).K_on) :
    (hmFinishC (AuthKindFuels.ofBudget S b).K_on).eval (.cons s (.cons b' .nil)) =
      (hmFinishC b.q_total).eval (.cons s (.cons b' .nil)) :=
  hmFinishC_fuel_indep s b' (Nat.le_trans hPend hn)
    (Nat.le_trans hPend (Nat.le_trans hn (AuthKindFuels.K_on_le_q_total S b)))

end FinishFuelEq

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimArms
