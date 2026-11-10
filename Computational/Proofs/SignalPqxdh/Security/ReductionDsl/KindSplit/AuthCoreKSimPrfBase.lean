/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval

/-!
# Fuel-Identity and Leaf-Preservation Helpers for `Auth` PRF Simulations

`mapComp` and `liftPrimComp` bridges, linear `AuthPrf` combinators, and shared handshake
fuel-equivalence and leaf-preservation lemmas supporting the kind-split `Auth` PRF reductions.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface pqAtomicSig pqAtomicOps PB)
open Computational.Proofs.SignalPqxdh.AtomicLift
  (AtomicIface TagLift embedTy embedVal projVal embedCtx embedEnv mapComp
   comp_queries_zero_of_zero mapComp_eval)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B U32)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext PT v letV bindV caseOptV caseSumV findMV anyMV consumeFirstMV
   eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
   eval_letC bytesBeq bytesBeq_eval bytes2Eq kyberCheckE
   AllLeaves liftPrimComp eval_liftPrimComp samplePrim queryPrim
   authStateTy preKeyBundleTy authHybridStateTy authHybridStateFixedTy
   recvFinishTagTy recvFinishResTy preparedAuthRecvTy finishSendArgsTy
   sendQTy recvQTy authRespTy msgKeysTy drKeyTy authMkSaltCacheTy
   prfMkCoreTy prfMkChalContTy prfMkStepPreTy
   asPrincipals asSpkBundles asOpkEntries asSessions asUsedSendSessions
   asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples asSentOPKEvents
   asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents asRoCache asRootRoCache asAdvKeys
   findHonestC isAdvRegC isGameSpkC isGameOpkC
   koskBundleOkC koskSenderOkC resolveSigPkC hkdfRoC rootRoC
   checkBundleProvenanceExactC checkBundleSpkHonIdealC
   recvFinishTagRunC prepareAuthHybridRecvC finishAuthHybridSendC)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (spkHonIdealFromPeerC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (AuthBaseValOnlineBounded AuthFixedValOnlineBounded
   valRoCache valRootRoCache atomRoCache atomRootRoCache CacheStepAtMostOne)

private abbrev env_get_succ := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_succ
private abbrev env_get_zero := @_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Env.get_zero

@[expose] def projEnv : ∀ {Γ : List (Ty pqSig)}, Env (embedCtx Γ) → Env Γ
  | [], .nil => .nil
  | t :: _, .cons x ρ => .cons (projVal t x) (projEnv ρ)

theorem embedEnv_projEnv : ∀ {Γ : List (Ty pqSig)} (ρ : Env (embedCtx Γ)),
    embedEnv (projEnv ρ) = ρ
  | [], .nil => rfl
  | t :: _, .cons x ρ => by
    simp only [projEnv, embedEnv, AtomicLift.embedVal_projVal, embedEnv_projEnv ρ]

theorem mapComp_eval_of_zero {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂) (hZero : ∀ g, tl.unsupportedW g = 0)
    {Γ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps I₁ Γ out) (ρ : Env (embedCtx Γ)) :
    (mapComp tl c).eval ρ = embedVal out <$> c.eval (projEnv ρ) := by
  conv_lhs => rw [← embedEnv_projEnv ρ]
  exact mapComp_eval tl c (comp_queries_zero_of_zero hZero c) (projEnv ρ)

theorem mapComp_congr_of_zero {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂) (hZero : ∀ g, tl.unsupportedW g = 0)
    {Γ : List (Ty pqSig)} {out : Ty pqSig}
    (c₁ c₂ : Comp pqxdhOps I₁ Γ out) (ρ : Env (embedCtx Γ))
    (h : c₁.eval (projEnv ρ) = c₂.eval (projEnv ρ)) :
    (mapComp tl c₁).eval ρ = (mapComp tl c₂).eval ρ := by
  rw [mapComp_eval_of_zero tl hZero c₁ ρ, mapComp_eval_of_zero tl hZero c₂ ρ, h]

theorem mem_support_mapComp_of_zero {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface pqSig T} {A₂ : AtomicIface T}
    (tl : TagLift I₁ A₂) (hZero : ∀ g, tl.unsupportedW g = 0)
    {Γ : List (Ty pqSig)} {out : Ty pqSig}
    (c : Comp pqxdhOps I₁ Γ out) (ρ : Env (embedCtx Γ)) {y : (embedTy out).denote}
    (hy : y ∈ support ((mapComp tl c).eval ρ)) :
    ∃ x ∈ support (c.eval (projEnv ρ)), embedVal out x = y := by
  rw [mapComp_eval_of_zero tl hZero c ρ, support_map, Set.mem_image] at hy
  exact hy

theorem AllLeaves_mem_support {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {m : OracleComp spec α} (h : AllLeaves P m) {y : α} (hy : y ∈ support m) :
    P y := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact h
  | query_bind q k ih =>
    rw [mem_support_bind_iff] at hy
    obtain ⟨u, -, hyk⟩ := hy
    exact ih u (h u) hyk

private theorem mem_support_embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (m : OracleComp _root_.SignalPqxdh.PrimBaseSpec α) {y : α}
    (hy : y ∈ support (_root_.SignalPqxdh.Security.FgGapDh.embedPrim (spec := spec) m)) :
    y ∈ support m := by
  have hAll : AllLeaves (fun x => x ∈ support m) m := by
    clear hy
    induction m using OracleComp.inductionOn with
    | pure a => exact AllLeaves.pure (by simp)
    | query_bind q k ih =>
      intro u
      exact (ih u).mono fun x hx => by
        rw [mem_support_bind_iff]
        exact ⟨u, mem_support_query q u, hx⟩
  exact AllLeaves_mem_support hAll.embedPrim hy

theorem liftPrimComp_eval_congr {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    {Δ : List PT} {out : PT} (c₁ c₂ : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ)
    (h : c₁.eval env = c₂.eval env) :
    (liftPrimComp (C := C) c₁).eval env = (liftPrimComp (C := C) c₂).eval env := by
  rw [eval_liftPrimComp, eval_liftPrimComp, h]

theorem mem_support_liftPrimComp {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    {Δ : List PT} {out : PT} (c : Comp pqxdhOps pqPrimIface Δ out) (env : Env Δ)
    (y : out.denote) (hy : y ∈ support ((liftPrimComp (C := C) c).eval env)) :
    ∃ x ∈ support (c.eval env), x = y := by
  rw [eval_liftPrimComp] at hy
  exact ⟨y, mem_support_embedPrim (c.eval env) hy, rfl⟩

theorem atomRoCache_embedVal (st : authStateTy.denote) :
    atomRoCache (embedVal authStateTy st) = valRoCache st := by
  rcases st with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ro, _, _⟩
  simp only [atomRoCache, valRoCache, embedVal]
  induction ro with
  | nil => rfl
  | cons p ps ih => cases p with | mk k d => cases d with | mk a b => cases b; exact congrArg _ ih

theorem atomRootRoCache_embedVal (st : authStateTy.denote) :
    atomRootRoCache (embedVal authStateTy st) = valRootRoCache st := by
  rcases st with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, root, _⟩
  simp only [atomRootRoCache, valRootRoCache, embedVal]
  induction root with
  | nil => rfl
  | cons p ps ih =>
    cases p with | mk k d => cases k; cases d; exact congrArg _ ih

theorem take_eq_of_le {α : Type} {l : List α} {K₁ K₂ : ℕ}
    (h₁ : l.length ≤ K₁) (h₂ : l.length ≤ K₂) :
    l.take K₁ = l.take K₂ := by
  rw [List.take_of_length_le h₁, List.take_of_length_le h₂]

theorem take_min_eq_of_le {α : Type} {l : List α} {K₁ K₂ N : ℕ}
    (h₁ : l.length ≤ K₁) (h₂ : l.length ≤ K₂) :
    l.take (min K₁ N) = l.take (min K₂ N) := by
  by_cases hN₁ : K₁ ≤ N <;> by_cases hN₂ : K₂ ≤ N
  · rw [Nat.min_eq_left hN₁, Nat.min_eq_left hN₂, take_eq_of_le h₁ h₂]
  · rw [Nat.min_eq_left hN₁, Nat.min_eq_right (Nat.le_of_not_ge hN₂),
      List.take_of_length_le h₁, List.take_of_length_le (Nat.le_trans h₁ hN₁)]
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hN₁), Nat.min_eq_left hN₂,
      List.take_of_length_le (Nat.le_trans h₂ hN₂), List.take_of_length_le h₂]
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hN₁), Nat.min_eq_right (Nat.le_of_not_ge hN₂)]

theorem findHonestC_prf_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (findHonestC S K₁ st ik).eval env = (findHonestC S K₂ st ik).eval env := by
  have hLen : ((asPrincipals (v st)).eval (.cons (ik.eval env) env)).length ≤ n := by
    simpa [asPrincipals, v, Expr.eval] using hb.principals_le
  simp only [findHonestC, letV, eval_letC, findMV, Comp.eval,
    take_min_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂)]

theorem isAdvRegC_fuel_eq {K₁ K₂ n : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (isAdvRegC K₁ st pk).eval env = (isAdvRegC K₂ st pk).eval env := by
  simp only [isAdvRegC, bindV, Comp.eval]
  refine bind_congr fun p => ?_
  have hLen : ((asAdvKeys (v st)).eval (.cons p env)).length ≤ n := by
    simpa [asAdvKeys, v, Expr.eval] using hb.advKeys_le
  simp only [eAny, Expr.eval, take_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂)]

theorem isGameSpkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (isGameSpkC S K₁ st pk).eval env = (isGameSpkC S K₂ st pk).eval env := by
  have hLen : ((asSpkBundles (v st)).eval (.cons (pk.eval env) env)).length ≤ n := by
    simpa [asSpkBundles, v, Expr.eval] using hb.spkBundles_le
  simp only [isGameSpkC, letV, eval_letC, anyMV, Comp.eval,
    take_min_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂)]

theorem isGameOpkC_prf_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (isGameOpkC S K₁ st pk).eval env = (isGameOpkC S K₂ st pk).eval env := by
  have hLen : ((asOpkEntries (v st)).eval (.cons (pk.eval env) env)).length ≤ n := by
    simpa [asOpkEntries, v, Expr.eval] using hb.opkEntries_le
  simp only [isGameOpkC, letV, eval_letC, anyMV, Comp.eval,
    take_min_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂)]

theorem koskBundleOkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁_ext.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (koskBundleOkC S K₁ st bu).eval env = (koskBundleOkC S K₂ st bu).eval env := by
  simp only [koskBundleOkC, bindV, caseOptV, Comp.eval]
  rw [findHonestC_prf_fuel_eq S st _ env hb h₁ h₂]
  refine bind_congr fun f => ?_
  rw [isAdvRegC_fuel_eq st _ (.cons f env) hb h₁ h₂]
  refine bind_congr fun idA => ?_
  rw [isGameSpkC_fuel_eq S st _ (.cons idA (.cons f env)) hb h₁ h₂]
  refine bind_congr fun spkG => ?_
  rw [isAdvRegC_fuel_eq st _ (.cons spkG (.cons idA (.cons f env))) hb h₁ h₂]
  refine bind_congr fun spkA => ?_
  cases (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbOpkB? (v bu)).eval
    (.cons spkA (.cons spkG (.cons idA (.cons f env)))) with
  | none => rfl
  | some o =>
    dsimp only
    rw [isGameOpkC_prf_fuel_eq S st _ (.cons o (.cons spkA (.cons spkG (.cons idA (.cons f env))))) hb h₁ h₂]
    refine bind_congr fun opkG => ?_
    rw [isAdvRegC_fuel_eq st _ (.cons opkG (.cons o (.cons spkA (.cons spkG (.cons idA (.cons f env)))))) hb h₁ h₂]

theorem koskSenderOkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (koskSenderOkC S K₁ st ik).eval env = (koskSenderOkC S K₂ st ik).eval env := by
  simp only [koskSenderOkC, letV, eval_letC, bindV, Comp.eval]
  rw [findHonestC_prf_fuel_eq S st _ (.cons (ik.eval env) env) hb h₁ h₂]
  refine bind_congr fun f => ?_
  rw [isAdvRegC_fuel_eq st _ (.cons f (.cons (ik.eval env) env)) hb h₁ h₂]

theorem resolveSigPkC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (resolveSigPkC S K₁ st ik).eval env = (resolveSigPkC S K₂ st ik).eval env := by
  simp only [resolveSigPkC, letV, eval_letC, bindV, Comp.eval]
  rw [findHonestC_prf_fuel_eq S st _ (.cons (ik.eval env) env) hb h₁ h₂]

theorem checkBundleProvenanceExactC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁_ext.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (checkBundleProvenanceExactC S K₁ st bu).eval env =
      (checkBundleProvenanceExactC S K₂ st bu).eval env := by
  simp only [checkBundleProvenanceExactC, bindV, caseOptV, letV, eval_letC, Comp.eval]
  rw [findHonestC_prf_fuel_eq S st _ env hb h₁ h₂]
  refine bind_congr fun f => ?_
  cases f with
  | none => rfl
  | some p =>
    simp only [eAny, anyMV, asSpkBundles, asOpkEntries, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
      take_eq_of_le (Nat.le_trans hb.spkBundles_le h₁) (Nat.le_trans hb.spkBundles_le h₂),
      take_min_eq_of_le (Nat.le_trans hb.opkEntries_le h₁) (Nat.le_trans hb.opkEntries_le h₂)]

theorem checkBundleSpkHonIdealC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁_ext.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (checkBundleSpkHonIdealC S K₁ st bu).eval env =
      (checkBundleSpkHonIdealC S K₂ st bu).eval env := by
  simp only [checkBundleSpkHonIdealC, bindV, caseOptV, letV, eval_letC, Comp.eval]
  rw [findHonestC_prf_fuel_eq S st _ env hb h₁ h₂]
  refine bind_congr fun f => ?_
  cases f with
  | none => rfl
  | some p =>
    simp only [anyMV, asSpkBundles, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
      take_min_eq_of_le (Nat.le_trans hb.spkBundles_le h₁) (Nat.le_trans hb.spkBundles_le h₂)]

theorem spkHonIdealFromPeerC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ}
    {Γ₁ Γ₂ Γ₃ Δ : List PT} (st : Var Γ₁ authStateTy)
    (pp : Var Γ₂ (.opt (.prod .nat _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.principalEntryTy)))
    (bu : Var Γ₃ preKeyBundleTy) [h₁_ext : Ext Γ₁ Δ] [h₂_ext : Ext Γ₂ Δ] [Ext Γ₃ Δ] (env : Env Δ)
    (hb : AuthBaseValOnlineBounded n (env.get (h₁_ext.wk st)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (spkHonIdealFromPeerC S K₁ st pp bu).eval env =
      (spkHonIdealFromPeerC S K₂ st pp bu).eval env := by
  simp only [spkHonIdealFromPeerC, caseOptV, letV, eval_letC, Comp.eval]
  cases (v pp).eval env with
  | none => rfl
  | some p =>
    simp only [anyMV, asSpkBundles, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
      take_min_eq_of_le (Nat.le_trans hb.spkBundles_le h₁) (Nat.le_trans hb.spkBundles_le h₂)]

theorem kyberCheckE_fuel_eq {K₁ K₂ n : ℕ} {Γ : List PT}
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32)))))
    (env : Env Γ) (hLen : (used.eval env).length ≤ n)
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (kyberCheckE K₁ used entry).eval env = (kyberCheckE K₂ used entry).eval env := by
  simp only [kyberCheckE, eLet2, eLet, eAny, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    env_get_succ, env_get_zero,
    take_eq_of_le (Nat.le_trans hLen h₁) (Nat.le_trans hLen h₂)]

theorem kyberCheckE_snd_len_le (K : ℕ) {n : ℕ} {Γ : List PT}
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32)))))
    (env : Env Γ) (hLen : (used.eval env).length ≤ n) :
    ((kyberCheckE K used entry).eval env).2.length ≤ n + 1 := by
  simp only [kyberCheckE, eLet2, eLet, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
    env_get_succ, env_get_zero]
  split <;> simp <;> omega

theorem hkdfRoC_fuel_eq {K₁ K₂ nRo : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hRo : (valRoCache (env.get (h.wk st))).length ≤ nRo)
    (h₁ : nRo ≤ K₁) (h₂ : nRo ≤ K₂) :
    (hkdfRoC K₁ st sec).eval env = (hkdfRoC K₂ st sec).eval env := by
  dsimp only [valRoCache] at hRo
  simp only [hkdfRoC, letV, eval_letC, caseOptV, eFind, asRoCache, v,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
    take_eq_of_le (Nat.le_trans hRo h₁) (Nat.le_trans hRo h₂)]

theorem hkdfRoC_step {K : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) (env : Env Δ)
    (hRo : (valRoCache (env.get (h.wk st))).length ≤ K) :
    ∀ p ∈ support ((hkdfRoC K st sec).eval env),
      CacheStepAtMostOne (valRoCache (env.get (h.wk st))) p.2 := by
  intro p hp
  dsimp only [valRoCache] at hRo ⊢
  simp only [hkdfRoC, letV, eval_letC, caseOptV, eFind, bindV, asRoCache, v, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
    List.take_of_length_le hRo] at hp
  cases hFind : (env.get (h.wk st)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.find? (fun a => a.1 == sec.eval env) with
  | none =>
    rw [hFind] at hp
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨dk, -, rfl⟩ := hp
    exact Or.inr ⟨sec.eval env, dk, by simp [hFind], rfl⟩
  | some e =>
    rw [hFind] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact CacheStepAtMostOne.refl _


theorem rootRoC_fuel_eq {K₁ K₂ nRoot : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hRoot : (valRootRoCache (env.get (h.wk st))).length ≤ nRoot)
    (h₁ : nRoot ≤ K₁) (h₂ : nRoot ≤ K₂) :
    (rootRoC K₁ st rk dh).eval env = (rootRoC K₂ st rk dh).eval env := by
  dsimp only [valRootRoCache] at hRoot
  simp only [rootRoC, letV, eval_letC, caseOptV, eFind, asRootRoCache, v,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
    take_eq_of_le (Nat.le_trans hRoot h₁) (Nat.le_trans hRoot h₂)]

theorem rootRoC_step {K : ℕ} {Γ Δ : List PT}
    (st : Var Γ authStateTy) [h : Ext Γ Δ]
    (rk dh : Expr pqxdhOps Δ (B 32)) (env : Env Δ)
    (hRoot : (valRootRoCache (env.get (h.wk st))).length ≤ K) :
    ∀ p ∈ support ((rootRoC K st rk dh).eval env),
      CacheStepAtMostOne (valRootRoCache (env.get (h.wk st))) p.2 := by
  intro p hp
  dsimp only [valRootRoCache] at hRoot ⊢
  simp only [rootRoC, letV, eval_letC, caseOptV, eFind, bindV, asRootRoCache, v, bytes2Eq, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
    List.take_of_length_le hRoot] at hp
  cases hFind : (env.get (h.wk st)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.find?
      (fun a => (a.1.1 == rk.eval env && a.1.2 == dh.eval env)) with
  | none =>
    rw [hFind] at hp
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨rk', -, ck', -, rfl⟩ := hp
    exact Or.inr ⟨(rk.eval env, dh.eval env), (rk', ck'), by simp [hFind], rfl⟩
  | some e =>
    rw [hFind] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact CacheStepAtMostOne.refl _

theorem letV_congr {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {e₁ e₂ : Expr pqxdhOps Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (he : e₁.eval env = e₂.eval env)
    (hk : ∀ x : τ₁.denote, (k₁ .zero).eval (.cons x env) = (k₂ .zero).eval (.cons x env)) :
    (letV e₁ k₁).eval env = (letV e₂ k₂).eval env := by
  simp only [letV, eval_letC, he]; exact hk (e₂.eval env)

theorem letV_congr_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {e₁ e₂ : Expr pqxdhOps Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (he : e₁.eval env = e₂.eval env)
    (hk : ∀ x : τ₁.denote, x = e₁.eval env →
      (k₁ .zero).eval (.cons x env) = (k₂ .zero).eval (.cons x env)) :
    (letV e₁ k₁).eval env = (letV e₂ k₂).eval env := by
  simp only [letV, eval_letC]; rw [← he]; exact hk (e₁.eval env) rfl

theorem letV_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT} {P : τ₂.denote → Prop}
    {e : Expr pqxdhOps Γ τ₁}
    {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hk : ∀ x : τ₁.denote, AllLeaves P ((k .zero).eval (.cons x env))) :
    AllLeaves P ((letV e k).eval env) := by
  simp only [letV, eval_letC]; exact hk (e.eval env)

theorem letV_allLeaves_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT} {P : τ₂.denote → Prop}
    {e : Expr pqxdhOps Γ τ₁}
    {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hk : ∀ x : τ₁.denote, x = e.eval env → AllLeaves P ((k .zero).eval (.cons x env))) :
    AllLeaves P ((letV e k).eval env) := by
  simp only [letV, eval_letC]; exact hk (e.eval env) rfl

theorem bindV_congr {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {m₁ m₂ : Comp pqxdhOps I Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hm : m₁.eval env = m₂.eval env)
    (hk : ∀ x : τ₁.denote, (k₁ .zero).eval (.cons x env) = (k₂ .zero).eval (.cons x env)) :
    (bindV m₁ k₁).eval env = (bindV m₂ k₂).eval env := by
  simp only [bindV, Comp.eval, hm]
  exact bind_congr hk

theorem bindV_congr_leaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT} {P : τ₁.denote → Prop}
    {m₁ m₂ : Comp pqxdhOps I Γ τ₁}
    {k₁ k₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hm : m₁.eval env = m₂.eval env) (hP : AllLeaves P (m₁.eval env))
    (hk : ∀ x : τ₁.denote, P x →
      (k₁ .zero).eval (.cons x env) = (k₂ .zero).eval (.cons x env)) :
    (bindV m₁ k₁).eval env = (bindV m₂ k₂).eval env := by
  simp only [bindV, Comp.eval, ← hm]
  exact _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.allLeaves_bind_congr hP hk

theorem bindV_allLeaves_const {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT} {P : τ₂.denote → Prop}
    {m : Comp pqxdhOps I Γ τ₁}
    {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hk : ∀ x : τ₁.denote, AllLeaves P ((k .zero).eval (.cons x env))) :
    AllLeaves P ((bindV m k).eval env) := by
  simp only [bindV, Comp.eval]
  exact AllLeaves.bind_const _ hk

theorem bindV_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {P : τ₁.denote → Prop} {Q : τ₂.denote → Prop}
    {m : Comp pqxdhOps I Γ τ₁}
    {k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hm : AllLeaves P (m.eval env))
    (hk : ∀ x : τ₁.denote, P x → AllLeaves Q ((k .zero).eval (.cons x env))) :
    AllLeaves Q ((bindV m k).eval env) := by
  simp only [bindV, Comp.eval]
  exact AllLeaves.bind hm hk

theorem caseSumV_congr {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ τ : PT}
    {s₁ s₂ : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl₁ kl₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ}
    {kr₁ kr₂ : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ} {env : Env Γ}
    (hs : s₁.eval env = s₂.eval env)
    (hkl : ∀ x : τ₁.denote, (kl₁ .zero).eval (.cons x env) = (kl₂ .zero).eval (.cons x env))
    (hkr : ∀ y : τ₂.denote, (kr₁ .zero).eval (.cons y env) = (kr₂ .zero).eval (.cons y env)) :
    (caseSumV s₁ kl₁ kr₁).eval env = (caseSumV s₂ kl₂ kr₂).eval env := by
  simp only [caseSumV, Comp.eval, hs]
  cases s₂.eval env with
  | inl x => exact hkl x
  | inr y => exact hkr y

theorem caseSumV_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ τ : PT} {P : τ.denote → Prop}
    {s : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ}
    {kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ} {env : Env Γ}
    (hkl : ∀ x : τ₁.denote, AllLeaves P ((kl .zero).eval (.cons x env)))
    (hkr : ∀ y : τ₂.denote, AllLeaves P ((kr .zero).eval (.cons y env))) :
    AllLeaves P ((caseSumV s kl kr).eval env) := by
  simp only [caseSumV, Comp.eval]
  cases s.eval env with
  | inl x => exact hkl x
  | inr y => exact hkr y

theorem caseOptV_congr {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    {o₁ o₂ : Expr pqxdhOps Γ (.opt τ₁)} {kn₁ kn₂ : Comp pqxdhOps I Γ τ₂}
    {ks₁ ks₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (ho : o₁.eval env = o₂.eval env)
    (hkn : kn₁.eval env = kn₂.eval env)
    (hks : ∀ x : τ₁.denote, (ks₁ .zero).eval (.cons x env) = (ks₂ .zero).eval (.cons x env)) :
    (caseOptV o₁ kn₁ ks₁).eval env = (caseOptV o₂ kn₂ ks₂).eval env := by
  simp only [caseOptV, Comp.eval, ho]
  cases o₂.eval env with
  | none => exact hkn
  | some x => exact hks x

theorem caseOptV_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT} {P : τ₂.denote → Prop}
    {o : Expr pqxdhOps Γ (.opt τ₁)} {kn : Comp pqxdhOps I Γ τ₂}
    {ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hkn : AllLeaves P (kn.eval env))
    (hks : ∀ x : τ₁.denote, AllLeaves P ((ks .zero).eval (.cons x env))) :
    AllLeaves P ((caseOptV o kn ks).eval env) := by
  simp only [caseOptV, Comp.eval]
  cases o.eval env with
  | none => exact hkn
  | some x => exact hks x

theorem ite_congr_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT}
    {c₁ c₂ : Expr pqxdhOps Γ .bool} {t₁ t₂ e₁ e₂ : Comp pqxdhOps I Γ τ} {env : Env Γ}
    (hc : c₁.eval env = c₂.eval env)
    (ht : t₁.eval env = t₂.eval env) (he : e₁.eval env = e₂.eval env) :
    (Comp.ite c₁ t₁ e₁).eval env = (Comp.ite c₂ t₂ e₂).eval env := by
  simp only [Comp.eval, hc]; split <;> assumption

theorem ite_allLeaves {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT} {P : τ.denote → Prop}
    {c : Expr pqxdhOps Γ .bool} {t e : Comp pqxdhOps I Γ τ} {env : Env Γ}
    (ht : AllLeaves P (t.eval env)) (he : AllLeaves P (e.eval env)) :
    AllLeaves P ((Comp.ite c t e).eval env) := by
  simp only [Comp.eval]; split <;> assumption

theorem caseSumV_congr_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ τ : PT}
    {s₁ s₂ : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl₁ kl₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ}
    {kr₁ kr₂ : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ} {env : Env Γ}
    (hs : s₁.eval env = s₂.eval env)
    (hkl : ∀ x : τ₁.denote, s₁.eval env = .inl x →
      (kl₁ .zero).eval (.cons x env) = (kl₂ .zero).eval (.cons x env))
    (hkr : ∀ y : τ₂.denote, s₁.eval env = .inr y →
      (kr₁ .zero).eval (.cons y env) = (kr₂ .zero).eval (.cons y env)) :
    (caseSumV s₁ kl₁ kr₁).eval env = (caseSumV s₂ kl₂ kr₂).eval env := by
  simp only [caseSumV, Comp.eval, ← hs]
  cases h : s₁.eval env with
  | inl x => exact hkl x h
  | inr y => exact hkr y h

theorem caseSumV_allLeaves_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ τ : PT} {P : τ.denote → Prop}
    {s : Expr pqxdhOps Γ (.sum τ₁ τ₂)}
    {kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ}
    {kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ} {env : Env Γ}
    (hkl : ∀ x : τ₁.denote, s.eval env = .inl x → AllLeaves P ((kl .zero).eval (.cons x env)))
    (hkr : ∀ y : τ₂.denote, s.eval env = .inr y → AllLeaves P ((kr .zero).eval (.cons y env))) :
    AllLeaves P ((caseSumV s kl kr).eval env) := by
  simp only [caseSumV, Comp.eval]
  cases h : s.eval env with
  | inl x => exact hkl x h
  | inr y => exact hkr y h

theorem caseOptV_allLeaves_eq {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT} {P : τ₂.denote → Prop}
    {o : Expr pqxdhOps Γ (.opt τ₁)} {kn : Comp pqxdhOps I Γ τ₂}
    {ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂} {env : Env Γ}
    (hkn : AllLeaves P (kn.eval env))
    (hks : ∀ x : τ₁.denote, o.eval env = some x → AllLeaves P ((ks .zero).eval (.cons x env))) :
    AllLeaves P ((caseOptV o kn ks).eval env) := by
  simp only [caseOptV, Comp.eval]
  cases h : o.eval env with
  | none => exact hkn
  | some x => exact hks x h

theorem consumeFirstML_allLeaves_len {ι : Type} {T : OracleSpec ι} {α : Type}
    (p : α → OracleComp T Bool) (mk : α → α) (xs : List α) :
    AllLeaves (fun r => r.2.length = xs.length) (_root_.ReductionDsl.consumeFirstML p mk xs) := by
  induction xs with
  | nil => exact AllLeaves.pure rfl
  | cons x tl ih =>
    simp only [_root_.ReductionDsl.consumeFirstML]
    refine AllLeaves.bind_const _ fun b => ?_
    cases b with
    | true => exact AllLeaves.pure (by simp)
    | false => exact AllLeaves.bind ih fun r hr => AllLeaves.pure (by simp [hr])

structure AuthHybridValOnlineBounded (n : ℕ) (hst : authHybridStateTy.denote) : Prop where
  base_le          : AuthBaseValOnlineBounded n hst.1
  initKemRecs_le   : hst.2.1.length ≤ n
  recvKemRecs_le   : hst.2.2.1.length ≤ n
  idealSessions_le : hst.2.2.2.length ≤ n

theorem AuthHybridValOnlineBounded.mono {m n : ℕ} (h : m ≤ n) {hst : authHybridStateTy.denote}
    (hb : AuthHybridValOnlineBounded m hst) : AuthHybridValOnlineBounded n hst where
  base_le          := hb.base_le.mono h
  initKemRecs_le   := Nat.le_trans hb.initKemRecs_le h
  recvKemRecs_le   := Nat.le_trans hb.recvKemRecs_le h
  idealSessions_le := Nat.le_trans hb.idealSessions_le h

theorem finishAuthHybridSendC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) [h₁_ext : Ext Γ₁ Δ]
    {args₁ args₂ : Expr pqxdhOps Δ finishSendArgsTy} {env : Env Δ}
    (heArgs : args₁.eval env = args₂.eval env)
    (hb : AuthHybridValOnlineBounded n (env.get (h₁_ext.wk hst)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (finishAuthHybridSendC S K₁ hst args₁).eval env =
      (finishAuthHybridSendC S K₂ hst args₂).eval env := by
  unfold finishAuthHybridSendC
  refine letV_congr heArgs fun _ => ?_
  refine letV_congr_eq rfl fun st hstEq => ?_
  have hbSt : AuthBaseValOnlineBounded n st := by
    have : st = (env.get (h₁_ext.wk hst)).1 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
    rw [this]; exact hb.base_le
  iterate 29 refine letV_congr rfl fun _ => ?_
  refine bindV_congr (checkBundleProvenanceExactC_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => ?_
  · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt
  refine bindV_congr (checkBundleSpkHonIdealC_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => rfl
  · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt

theorem finishAuthHybridSendC_leaves (S : Setup) (K : ℕ) {n : ℕ} {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) [h₁_ext : Ext Γ₁ Δ]
    (args : Expr pqxdhOps Δ finishSendArgsTy) (env : Env Δ)
    (hb : AuthHybridValOnlineBounded n (env.get (h₁_ext.wk hst)))
    (hRo : CacheStepAtMostOne (valRoCache (env.get (h₁_ext.wk hst)).1)
      (args.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (hRoot : CacheStepAtMostOne (valRootRoCache (env.get (h₁_ext.wk hst)).1)
      (args.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) :
    AllLeaves (fun p =>
      AuthHybridValOnlineBounded (n + 1) p.2 ∧
      CacheStepAtMostOne (valRoCache (env.get (h₁_ext.wk hst)).1) (valRoCache p.2.1) ∧
      CacheStepAtMostOne (valRootRoCache (env.get (h₁_ext.wk hst)).1) (valRootRoCache p.2.1))
      ((finishAuthHybridSendC S K hst args).eval env) := by
  unfold finishAuthHybridSendC
  refine letV_allLeaves_eq fun a ha => ?_
  refine letV_allLeaves_eq fun st hstEq => ?_
  have hstVal : st = (env.get (h₁_ext.wk hst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves fun pp => ?_
  refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves fun bu => ?_
  iterate 10 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun roC hRoCEq => ?_
  refine letV_allLeaves_eq fun rootC hRootCEq => ?_
  have hRoC : roC = (args.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, ha] using hRoCEq
  have hRootC : rootC = (args.eval env).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 := by
    simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, ha] using hRootCEq
  iterate 12 refine letV_allLeaves fun _ => ?_
  iterate 2 refine bindV_allLeaves_const fun _ => ?_
  iterate 4 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun sentEvs hSentEq => ?_
  have hSentBds : sentEvs.1.length ≤ n + 1 ∧ sentEvs.2.length ≤ n + 1 := by
    subst hSentEq
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.eCaseOpt,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.pkbOpkB?,
      asSentOPKEvents, asSentNoOPKEvents, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal]
    have hSO := hb.base_le.sentOPKEvents_le
    have hSN := hb.base_le.sentNoOPKEvents_le
    rcases pp with _ | ⟨_, _⟩
    · exact ⟨Nat.le_trans hSO (Nat.le_succ n), Nat.le_trans hSN (Nat.le_succ n)⟩
    · rcases bu.2.2.2.2.1 with _ | ⟨_, _⟩ <;> simp <;> omega
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun idealS' hIdealEq => ?_
  have hIdealBd : idealS'.length ≤ n + 1 := by
    subst hIdealEq
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    have hIS := hb.idealSessions_le
    split <;> simp <;> omega
  refine letV_allLeaves_eq fun hst' hHst'Eq => ?_
  refine letV_allLeaves fun resp => ?_
  simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
  refine AllLeaves.pure ?_
  subst hHst'Eq
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
    asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
    v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
    hstVal, hRoC, hRootC, valRoCache, valRootRoCache]
  have hb1 := hb.base_le.mono (Nat.le_succ n)
  exact ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le,
    by simp; exact hb.base_le.sessions_le,
    by simp; exact hb.base_le.usedSendSessions_le,
    hb1.usedRecvOPK_le, hb1.usedRecvNoOPK_le, hb1.seenKyberBaseKeys_le,
    hSentBds.1, hSentBds.2, hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
    by simp; exact hb.initKemRecs_le,
    Nat.le_trans hb.recvKemRecs_le (Nat.le_succ n),
    hIdealBd⟩, hRo, hRoot⟩

/-- Online list-length and random-oracle cache preservation invariant on `recvFinishTagTy.denote` values produced by `prepareAuthHybridRecvC`. -/
@[expose] def RecvTagValBounded (n : ℕ)
    (ro0 : List (List UInt8 × drKeyTy.denote))
    (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))
    (tag : recvFinishTagTy.denote) : Prop :=
  match tag with
  | .inl opkT =>
    opkT.2.2.2.2.1.length ≤ n + 1 ∧
      AuthBaseValOnlineBounded n opkT.2.2.2.2.2.2.1 ∧
      opkT.2.2.2.2.2.2.2.1.length ≤ n ∧
      opkT.2.2.2.2.2.2.2.2.1.length ≤ n + 1 ∧
      opkT.2.2.2.2.2.2.2.2.2.length ≤ n ∧
      valRoCache opkT.2.2.2.2.2.2.1 = ro0 ∧
      valRootRoCache opkT.2.2.2.2.2.2.1 = root0
  | .inr noOpkT =>
    noOpkT.2.2.2.1.length ≤ n + 1 ∧
      AuthBaseValOnlineBounded n noOpkT.2.2.2.2.2.1 ∧
      noOpkT.2.2.2.2.2.2.1.length ≤ n ∧
      noOpkT.2.2.2.2.2.2.2.1.length ≤ n + 1 ∧
      noOpkT.2.2.2.2.2.2.2.2.length ≤ n ∧
      valRoCache noOpkT.2.2.2.2.2.1 = ro0 ∧
      valRootRoCache noOpkT.2.2.2.2.2.1 = root0

theorem recvFinishTagRunC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ}
    {ro0 : List (List UInt8 × drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Δ : List PT} (tag : Var Γ₁ recvFinishTagTy) [h₁_ext : Ext Γ₁ Δ]
    {res₁ res₂ : Expr pqxdhOps Δ recvFinishResTy} {env : Env Δ}
    (heRes : res₁.eval env = res₂.eval env)
    (hbTag : RecvTagValBounded n ro0 root0 (env.get (h₁_ext.wk tag)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (recvFinishTagRunC S K₁ tag res₁).eval env =
      (recvFinishTagRunC S K₂ tag res₂).eval env := by
  unfold recvFinishTagRunC
  refine letV_congr heRes fun _ => ?_
  refine caseSumV_congr_eq rfl (fun opkT hTag => ?_) (fun noOpkT hTag => ?_)
  · have hTagVal : env.get (h₁_ext.wk tag) = .inl opkT := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hTag
    rw [hTagVal] at hbTag
    rcases hbTag with ⟨_, hbSt0, _, _, _, _, _⟩
    iterate 6 refine letV_congr rfl fun _ => ?_
    refine letV_congr_eq rfl fun hstDec hhstEq => ?_
    refine letV_congr_eq rfl fun st hstEq => ?_
    have hbSt : AuthBaseValOnlineBounded n st := by
      have h1 : hstDec = opkT.2.2.2.2.2.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
      have h2 : st = hstDec.1 := by
        simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
          Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
      rw [h2, h1]; exact hbSt0
    refine caseOptV_congr rfl rfl fun _ => ?_
    iterate 6 refine letV_congr rfl fun _ => ?_
    refine letV_congr ?_ fun _ => ?_
    · simp only [eMap, asOpkEntries, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero,
        take_eq_of_le (Nat.le_trans hbSt.opkEntries_le h₁) (Nat.le_trans hbSt.opkEntries_le h₂)]
    refine bindV_congr (findHonestC_prf_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => ?_
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt
    refine caseOptV_congr rfl rfl fun _ => ?_
    refine ite_congr_eval rfl ?_ rfl
    refine letV_congr rfl fun _ => ?_
    refine bindV_congr ?_ fun _ => rfl
    simp only [consumeFirstMV, asSentOPKEvents, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
      take_min_eq_of_le (Nat.le_trans hbSt.sentOPKEvents_le h₁)
        (Nat.le_trans hbSt.sentOPKEvents_le h₂)]
  · have hTagVal : env.get (h₁_ext.wk tag) = .inr noOpkT := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hTag
    rw [hTagVal] at hbTag
    rcases hbTag with ⟨_, hbSt0, _, _, _, _, _⟩
    iterate 5 refine letV_congr rfl fun _ => ?_
    refine letV_congr_eq rfl fun hstDec hhstEq => ?_
    refine letV_congr_eq rfl fun st hstEq => ?_
    have hbSt : AuthBaseValOnlineBounded n st := by
      have h1 : hstDec = noOpkT.2.2.2.2.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
      have h2 : st = hstDec.1 := by
        simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
          Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
      rw [h2, h1]; exact hbSt0
    refine caseOptV_congr rfl rfl fun _ => ?_
    iterate 6 refine letV_congr rfl fun _ => ?_
    refine bindV_congr (findHonestC_prf_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => ?_
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt
    refine caseOptV_congr rfl rfl fun _ => ?_
    refine ite_congr_eval rfl ?_ rfl
    refine letV_congr rfl fun _ => ?_
    refine bindV_congr ?_ fun _ => rfl
    simp only [consumeFirstMV, asSentNoOPKEvents, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
      take_min_eq_of_le (Nat.le_trans hbSt.sentNoOPKEvents_le h₁)
        (Nat.le_trans hbSt.sentNoOPKEvents_le h₂)]

theorem recvFinishTagRunC_leaves (S : Setup) (K : ℕ) {n : ℕ}
    {ro0 : List (List UInt8 × drKeyTy.denote)}
    {root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))}
    {Γ₁ Δ : List PT} (tag : Var Γ₁ recvFinishTagTy) [h₁_ext : Ext Γ₁ Δ]
    (res? : Expr pqxdhOps Δ recvFinishResTy) (env : Env Δ)
    (hbTag : RecvTagValBounded n ro0 root0 (env.get (h₁_ext.wk tag)))
    (hRes : ∀ r, res?.eval env = some r →
      CacheStepAtMostOne ro0 r.2.2.2.2.1 ∧ CacheStepAtMostOne root0 r.2.2.2.2.2) :
    AllLeaves (fun p =>
      AuthHybridValOnlineBounded (n + 1) p.2 ∧
      CacheStepAtMostOne ro0 (valRoCache p.2.1) ∧
      CacheStepAtMostOne root0 (valRootRoCache p.2.1))
      ((recvFinishTagRunC S K tag res?).eval env) := by
  unfold recvFinishTagRunC
  refine letV_allLeaves_eq fun rOpt hrOpt => ?_
  refine caseSumV_allLeaves_eq (fun opkT hTag => ?_) (fun noOpkT hTag => ?_)
  · have hTagVal : env.get (h₁_ext.wk tag) = .inl opkT := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hTag
    rw [hTagVal] at hbTag
    rcases hbTag with ⟨hUsedT, hbSt0, hInitR, hRecvR, hIdealS, hRo0, hRoot0⟩
    have hb1 := hbSt0.mono (Nat.le_succ n)
    iterate 4 refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun usedT hUsedTEq => ?_
    refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun hstDec hhstEq => ?_
    refine letV_allLeaves_eq fun st hstEq => ?_
    have hhstVal : hstDec = opkT.2.2.2.2.2.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
    have hstVal : st = opkT.2.2.2.2.2.2.1 := by
      have : st = hstDec.1 := by
        simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
          Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
      rw [this, hhstVal]
    have hUsedTVal : usedT = opkT.2.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hUsedTEq
    refine caseOptV_allLeaves_eq ?_ (fun res hSome => ?_)
    · simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal]
      exact AllLeaves.pure ⟨⟨hb1, Nat.le_trans hInitR (Nat.le_succ n), hRecvR,
        Nat.le_trans hIdealS (Nat.le_succ n)⟩,
        by rw [hRo0]; exact CacheStepAtMostOne.refl _,
        by rw [hRoot0]; exact CacheStepAtMostOne.refl _⟩
    · have ⟨hRoStep, hRootStep⟩ := hRes res (by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hrOpt] using hSome)
      iterate 4 refine letV_allLeaves fun _ => ?_
      refine letV_allLeaves_eq fun roC hRoCEq => ?_
      refine letV_allLeaves_eq fun rootC hRootCEq => ?_
      have hRoC : roC = res.2.2.2.2.1 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoCEq
      have hRootC : rootC = res.2.2.2.2.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRootCEq
      refine letV_allLeaves_eq fun opks' hopksEq => ?_
      have hopksBd : opks'.length ≤ n + 1 := by
        subst hopksEq
        simp only [eMap, asOpkEntries, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
          env_get_succ, env_get_zero, hstVal, List.length_map, List.length_take]
        have := hb1.opkEntries_le; omega
      refine bindV_allLeaves_const fun _ => ?_
      refine caseOptV_allLeaves ?_ (fun _ => ?_)
      · simp only [Comp.eval, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
          asPrincipals, asSpkBundles, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
          asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
          v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
          hhstVal, hstVal, hUsedTVal, hRoC, hRootC, valRoCache, valRootRoCache]
        exact AllLeaves.pure ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hopksBd,
          hb1.sessions_le, hb1.usedSendSessions_le,
          by simp; exact hbSt0.usedRecvOPK_le,
          hb1.usedRecvNoOPK_le, hUsedT, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
          hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
          Nat.le_trans hInitR (Nat.le_succ n), hRecvR, Nat.le_trans hIdealS (Nat.le_succ n)⟩,
          hRoStep, hRootStep⟩
      · refine ite_allLeaves ?_ ?_
        · refine letV_allLeaves fun _ => ?_
          refine bindV_allLeaves (P := fun r : Bool × _ => r.2.length ≤ n + 1) ?_ (fun mOut hmOut => ?_)
          · simp only [consumeFirstMV, Comp.eval, asSentOPKEvents, v, Expr.eval,
              Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal]
            exact (consumeFirstML_allLeaves_len _ _ _).mono fun r hr => by
              rw [hr, List.length_take]; have := hb1.sentOPKEvents_le; omega
          · refine letV_allLeaves fun _ => ?_
            simp only [Comp.eval, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
              asPrincipals, asSpkBundles, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
              asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
              v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
              hhstVal, hstVal, hUsedTVal, hRoC, hRootC, valRoCache, valRootRoCache]
            exact AllLeaves.pure ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hopksBd,
              hb1.sessions_le, hb1.usedSendSessions_le,
              by simp; exact hbSt0.usedRecvOPK_le,
              hb1.usedRecvNoOPK_le, hUsedT, hmOut, hb1.sentNoOPKEvents_le,
              by simp; exact hbSt0.recvdOPKEvents_le,
              hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
              Nat.le_trans hInitR (Nat.le_succ n), hRecvR, Nat.le_trans hIdealS (Nat.le_succ n)⟩,
              hRoStep, hRootStep⟩
        · simp only [Comp.eval, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
            asPrincipals, asSpkBundles, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
            asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
            v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
            hhstVal, hstVal, hUsedTVal, hRoC, hRootC, valRoCache, valRootRoCache]
          exact AllLeaves.pure ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hopksBd,
            hb1.sessions_le, hb1.usedSendSessions_le,
            by simp; exact hbSt0.usedRecvOPK_le,
            hb1.usedRecvNoOPK_le, hUsedT, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
            hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
            Nat.le_trans hInitR (Nat.le_succ n), hRecvR, Nat.le_trans hIdealS (Nat.le_succ n)⟩,
            hRoStep, hRootStep⟩
  · have hTagVal : env.get (h₁_ext.wk tag) = .inr noOpkT := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hTag
    rw [hTagVal] at hbTag
    rcases hbTag with ⟨hUsedT, hbSt0, hInitR, hRecvR, hIdealS, hRo0, hRoot0⟩
    have hb1 := hbSt0.mono (Nat.le_succ n)
    iterate 3 refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun usedT hUsedTEq => ?_
    refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun hstDec hhstEq => ?_
    refine letV_allLeaves_eq fun st hstEq => ?_
    have hhstVal : hstDec = noOpkT.2.2.2.2.2 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hhstEq
    have hstVal : st = noOpkT.2.2.2.2.2.1 := by
      have : st = hstDec.1 := by
        simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
          Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
      rw [this, hhstVal]
    have hUsedTVal : usedT = noOpkT.2.2.2.1 := by
      simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hUsedTEq
    refine caseOptV_allLeaves_eq ?_ (fun res hSome => ?_)
    · simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstVal]
      exact AllLeaves.pure ⟨⟨hb1, Nat.le_trans hInitR (Nat.le_succ n), hRecvR,
        Nat.le_trans hIdealS (Nat.le_succ n)⟩,
        by rw [hRo0]; exact CacheStepAtMostOne.refl _,
        by rw [hRoot0]; exact CacheStepAtMostOne.refl _⟩
    · have ⟨hRoStep, hRootStep⟩ := hRes res (by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hrOpt] using hSome)
      iterate 4 refine letV_allLeaves fun _ => ?_
      refine letV_allLeaves_eq fun roC hRoCEq => ?_
      refine letV_allLeaves_eq fun rootC hRootCEq => ?_
      have hRoC : roC = res.2.2.2.2.1 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRoCEq
      have hRootC : rootC = res.2.2.2.2.2 := by
        simpa [v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hRootCEq
      refine bindV_allLeaves_const fun _ => ?_
      refine caseOptV_allLeaves ?_ (fun _ => ?_)
      · simp only [Comp.eval, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
          _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
          asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK,
          asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
          v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
          hhstVal, hstVal, hUsedTVal, hRoC, hRootC, valRoCache, valRootRoCache]
        exact AllLeaves.pure ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le,
          hb1.sessions_le, hb1.usedSendSessions_le, hb1.usedRecvOPK_le,
          by simp; exact hbSt0.usedRecvNoOPK_le,
          hUsedT, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
          hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
          Nat.le_trans hInitR (Nat.le_succ n), hRecvR, Nat.le_trans hIdealS (Nat.le_succ n)⟩,
          hRoStep, hRootStep⟩
      · refine ite_allLeaves ?_ ?_
        · refine letV_allLeaves fun _ => ?_
          refine bindV_allLeaves (P := fun r : Bool × _ => r.2.length ≤ n + 1) ?_ (fun mOut hmOut => ?_)
          · simp only [consumeFirstMV, Comp.eval, asSentNoOPKEvents, v, Expr.eval,
              Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hstVal]
            exact (consumeFirstML_allLeaves_len _ _ _).mono fun r hr => by
              rw [hr, List.length_take]; have := hb1.sentNoOPKEvents_le; omega
          · refine letV_allLeaves fun _ => ?_
            simp only [Comp.eval, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
              _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
              asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK,
              asUsedRecvNoOPK, asSentOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
              v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
              hhstVal, hstVal, hUsedTVal, hRoC, hRootC, valRoCache, valRootRoCache]
            exact AllLeaves.pure ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le,
              hb1.sessions_le, hb1.usedSendSessions_le, hb1.usedRecvOPK_le,
              by simp; exact hbSt0.usedRecvNoOPK_le,
              hUsedT, hb1.sentOPKEvents_le, hmOut, hb1.recvdOPKEvents_le,
              by simp; exact hbSt0.recvdNoOPKEvents_le,
              hb1.advKeys_le⟩,
              Nat.le_trans hInitR (Nat.le_succ n), hRecvR, Nat.le_trans hIdealS (Nat.le_succ n)⟩,
              hRoStep, hRootStep⟩
        · simp only [Comp.eval, Expr.eval, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
            _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
            asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK,
            asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
            v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero,
            hhstVal, hstVal, hUsedTVal, hRoC, hRootC, valRoCache, valRootRoCache]
          exact AllLeaves.pure ⟨⟨⟨hb1.principals_le, hb1.spkBundles_le, hb1.opkEntries_le,
            hb1.sessions_le, hb1.usedSendSessions_le, hb1.usedRecvOPK_le,
            by simp; exact hbSt0.usedRecvNoOPK_le,
            hUsedT, hb1.sentOPKEvents_le, hb1.sentNoOPKEvents_le,
            hb1.recvdOPKEvents_le, hb1.recvdNoOPKEvents_le, hb1.advKeys_le⟩,
            Nat.le_trans hInitR (Nat.le_succ n), hRecvR, Nat.le_trans hIdealS (Nat.le_succ n)⟩,
            hRoStep, hRootStep⟩

structure PreparedRecvValBounded (n : ℕ)
    (ro0 : List (List UInt8 × drKeyTy.denote))
    (root0 : List ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))
    (prep : preparedAuthRecvTy.denote) : Prop where
  base_le     : AuthBaseValOnlineBounded n prep.2.2.2.2.2.2.2.2.1.1
  ro_eq       : valRoCache prep.2.2.2.2.2.2.2.2.1.1 = ro0
  root_eq     : valRootRoCache prep.2.2.2.2.2.2.2.2.1.1 = root0
  tag_bounded : RecvTagValBounded n ro0 root0 prep.2.2.2.2.2.2.2.2.2

theorem prepareAuthHybridRecvC_fuel_eq (S : Setup) {K₁ K₂ n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthHybridValOnlineBounded n (env.get (h₁_ext.wk hst)))
    (h₁ : n ≤ K₁) (h₂ : n ≤ K₂) :
    (prepareAuthHybridRecvC S K₁ opk hst x).eval env =
      (prepareAuthHybridRecvC S K₂ opk hst x).eval env := by
  unfold prepareAuthHybridRecvC
  refine letV_congr_eq rfl fun st hstEq => ?_
  have hstVal : st = (env.get (h₁_ext.wk hst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
  have hbSt : AuthBaseValOnlineBounded n st := hstVal ▸ hb.base_le
  refine ite_congr_eval rfl rfl ?_
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
  refine bindV_congr (koskSenderOkC_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => ?_
  · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt
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
  refine letV_congr (kyberCheckE_fuel_eq _ _ _ ?_ h₁ h₂) fun _ => ?_
  · simp only [asUsedKyberTriples, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero]
    exact hbSt.seenKyberBaseKeys_le
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iterate 2 refine bindV_congr rfl fun _ => ?_
    refine ite_congr_eval rfl rfl ?_
    refine bindV_congr rfl fun _ => ?_
    refine caseOptV_congr rfl rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    refine letV_congr_eq rfl fun hstDec hhstEq => ?_
    have hhstIS : hstDec.2.2.2 = (env.get (h₁_ext.wk hst)).2.2.2 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using congrArg (fun z => z.2.2.2) hhstEq
    iterate 3 refine bindV_congr rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    refine bindV_congr (findHonestC_prf_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => ?_
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt
    iterate 5 refine letV_congr rfl fun _ => ?_
    refine bindV_congr ?_ fun _ => rfl
    simp only [findMV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstIS,
      take_min_eq_of_le (Nat.le_trans hb.idealSessions_le h₁)
        (Nat.le_trans hb.idealSessions_le h₂)]
  · simp only [↓reduceIte]
    refine caseOptV_congr ?_ rfl fun _ => ?_
    · simp only [eFind, asOpkEntries, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
        env_get_succ, env_get_zero,
        take_eq_of_le (Nat.le_trans hbSt.opkEntries_le h₁) (Nat.le_trans hbSt.opkEntries_le h₂)]
    refine letV_congr rfl fun _ => ?_
    refine ite_congr_eval rfl rfl ?_
    iterate 2 refine bindV_congr rfl fun _ => ?_
    refine ite_congr_eval rfl rfl ?_
    refine bindV_congr rfl fun _ => ?_
    refine caseOptV_congr rfl rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    refine letV_congr_eq rfl fun hstDec hhstEq => ?_
    have hhstIS : hstDec.2.2.2 = (env.get (h₁_ext.wk hst)).2.2.2 := by
      simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions, v, Expr.eval,
        Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using congrArg (fun z => z.2.2.2) hhstEq
    iterate 4 refine bindV_congr rfl fun _ => ?_
    refine letV_congr rfl fun _ => ?_
    refine bindV_congr rfl fun _ => ?_
    refine bindV_congr (findHonestC_prf_fuel_eq S _ _ _ ?_ h₁ h₂) fun _ => ?_
    · simpa [Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hbSt
    iterate 5 refine letV_congr rfl fun _ => ?_
    refine bindV_congr ?_ fun _ => rfl
    simp only [findMV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero, hhstIS,
      take_min_eq_of_le (Nat.le_trans hb.idealSessions_le h₁)
        (Nat.le_trans hb.idealSessions_le h₂)]

theorem prepareAuthHybridRecvC_leaves (S : Setup) (K : ℕ) {n : ℕ} (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [h₁_ext : Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : AuthHybridValOnlineBounded n (env.get (h₁_ext.wk hst))) :
    AllLeaves (fun prep? => ∀ prep, prep? = some prep →
      PreparedRecvValBounded n
        (valRoCache (env.get (h₁_ext.wk hst)).1)
        (valRootRoCache (env.get (h₁_ext.wk hst)).1) prep)
      ((prepareAuthHybridRecvC S K opk hst x).eval env) := by
  have hNone : ∀ {Γ' : List PT} (ρ : Env Γ'),
      AllLeaves (fun prep? => ∀ prep, prep? = some prep →
        PreparedRecvValBounded n
          (valRoCache (env.get (h₁_ext.wk hst)).1)
          (valRootRoCache (env.get (h₁_ext.wk hst)).1) prep)
        ((Comp.ret (I := pqPrimIface) (Expr.none : Expr pqxdhOps Γ' (.opt preparedAuthRecvTy))).eval ρ) :=
    fun _ => AllLeaves.pure (by intro _ h; cases h)
  unfold prepareAuthHybridRecvC
  refine letV_allLeaves_eq fun st hstEq => ?_
  have hstVal : st = (env.get (h₁_ext.wk hst)).1 := by
    simpa [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase, v, Expr.eval,
      Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero] using hstEq
  refine ite_allLeaves (hNone _) ?_
  iterate 3 refine letV_allLeaves fun _ => ?_
  refine ite_allLeaves (hNone _) ?_
  refine ite_allLeaves (hNone _) ?_
  refine bindV_allLeaves_const fun _ => ?_
  refine ite_allLeaves (hNone _) ?_
  refine caseOptV_allLeaves (hNone _) fun _ => ?_
  refine caseOptV_allLeaves (hNone _) fun _ => ?_
  iterate 2 refine letV_allLeaves fun _ => ?_
  refine letV_allLeaves_eq fun kc hkcEq => ?_
  have hkcLen : kc.2.length ≤ n + 1 := by
    rw [hkcEq]
    refine kyberCheckE_snd_len_le K _ _ _ ?_
    simp only [asUsedKyberTriples, v, Expr.eval, Ext.step_wk, Ext.refl_wk,
      env_get_succ, env_get_zero, hstVal]
    exact hb.base_le.seenKyberBaseKeys_le
  cases opk
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iterate 2 refine bindV_allLeaves_const fun _ => ?_
    refine ite_allLeaves (hNone _) ?_
    refine bindV_allLeaves_const fun _ => ?_
    refine caseOptV_allLeaves (hNone _) fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun hstDec hhstEq => ?_
    iterate 3 refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    iterate 2 refine bindV_allLeaves_const fun _ => ?_
    iterate 5 refine letV_allLeaves fun _ => ?_
    iterate 2 refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves_eq fun fTag hfTagEq => ?_
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    refine AllLeaves.pure fun prep hSome => ?_
    cases hSome
    subst hfTagEq; subst hhstEq
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    exact ⟨hb.base_le, rfl, rfl, ⟨hkcLen, hb.base_le, hb.initKemRecs_le,
      by simp; exact hb.recvKemRecs_le, hb.idealSessions_le, rfl, rfl⟩⟩
  · simp only [↓reduceIte]
    refine caseOptV_allLeaves (hNone _) fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine ite_allLeaves (hNone _) ?_
    iterate 2 refine bindV_allLeaves_const fun _ => ?_
    refine ite_allLeaves (hNone _) ?_
    refine bindV_allLeaves_const fun _ => ?_
    refine caseOptV_allLeaves (hNone _) fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    refine letV_allLeaves_eq fun hstDec hhstEq => ?_
    iterate 4 refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves fun _ => ?_
    iterate 2 refine bindV_allLeaves_const fun _ => ?_
    iterate 5 refine letV_allLeaves fun _ => ?_
    iterate 2 refine bindV_allLeaves_const fun _ => ?_
    refine letV_allLeaves_eq fun fTag hfTagEq => ?_
    simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    refine AllLeaves.pure fun prep hSome => ?_
    cases hSome
    subst hfTagEq; subst hhstEq
    simp only [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsInitKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsRecvKemRecs,
      _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsIdealSessions,
      v, Expr.eval, Ext.step_wk, Ext.refl_wk, env_get_succ, env_get_zero]
    exact ⟨hb.base_le, rfl, rfl, ⟨hkcLen, hb.base_le, hb.initKemRecs_le,
      by simp; exact hb.recvKemRecs_le, hb.idealSessions_le, rfl, rfl⟩⟩

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimPrfBase
