/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2b
import VCVio.EvalDist.Monad.Basic

/-!
# Multi-Key `INT-CTXT` Unguarded Runner

Defines the explicit lazy-key runner `runMu` for the unguarded oracle of `aeadMuIntCtxtExp` and
proves closed-form query lemmas.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-- Unguarded `aeadMuIntSpec` oracle agreeing with `aeadMuIntCtxtExp` on first-message ADs. -/
noncomputable def aeadMuImpl (P : Primitives) :
    QueryImpl aeadMuIntSpec (StateT AeadMuIntState ProbComp) := fun q =>
    match q with
    | .encOnce i ad pt => do
      let (_, chal, _) ← get
      match chal.lookup i with
      | some _ => return none
      | none =>
        let mk ← aeadMuIntKey i
        let ct := P.aeadEnc mk ad pt
        let (keys, chal', w) ← get
        set (keys, (i, (ad, ct)) :: chal', w)
        return (some ct)
    | .tryForge i ad ct => do
      let (_, chal, _) ← get
      if chal.lookup i == some (ad, ct) then return false
      let mk ← aeadMuIntKey i
      match P.aeadDec mk ad ct with
      | some _ =>
        let (keys, chal', _) ← get
        set (keys, chal', true)
        return true
      | none => return false

noncomputable def aeadMuFullImpl (P : Primitives) :
    QueryImpl AeadMuIntSimSpec (StateT AeadMuIntState ProbComp) :=
  (primBaseImpl P).liftTarget (StateT AeadMuIntState ProbComp) + aeadMuImpl P

noncomputable abbrev runMu {α : Type} (P : Primitives) (oa : OracleComp AeadMuIntSimSpec α)
    (st : AeadMuIntState) : ProbComp (α × AeadMuIntState) :=
  (simulateQ (aeadMuFullImpl P) oa).run st

@[simp] theorem runMu_pure {α : Type} (P : Primitives) (a : α) (st : AeadMuIntState) :
    runMu P (pure a) st = pure (a, st) := rfl

@[simp] theorem runMu_bind {α β : Type} (P : Primitives)
    (oa : OracleComp AeadMuIntSimSpec α) (f : α → OracleComp AeadMuIntSimSpec β)
    (st : AeadMuIntState) :
    runMu P (oa >>= f) st = (runMu P oa st >>= fun p => runMu P (f p.1) p.2) := by
  simp [runMu, simulateQ_bind, StateT.run_bind]

@[simp] theorem runMu_query_inl (P : Primitives) (pq : PrimBaseSpec.Domain) (st : AeadMuIntState) :
    runMu P (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inl pq))) st =
      (primBaseImpl P pq >>= fun u => pure (u, st)) := by
  simp [runMu, aeadMuFullImpl, QueryImpl.liftTarget, StateT.run_monadLift, monadLift_self]

@[simp] theorem runMu_query_inr (P : Primitives) (iq : AeadMuIntQuery) (st : AeadMuIntState) :
    runMu P (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inr iq))) st =
      (aeadMuImpl P iq).run st := by
  simp [runMu, aeadMuFullImpl]

@[simp] theorem runMu_embedPrimMu {α : Type} (P : Primitives)
    (oa : OracleComp PrimBaseSpec α) (st : AeadMuIntState) :
    runMu P (embedPrimMu oa) st = (simulateQ (primBaseImpl P) oa >>= fun a => pure (a, st)) := by
  unfold embedPrimMu
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp [embedPrim_pure]
  | query_bind q mx ih =>
    have hSim : simulateQ (primBaseImpl P) (liftM (OracleSpec.query q) >>= mx) =
        (primBaseImpl P q >>= fun u => simulateQ (primBaseImpl P) (mx u)) := by
      simp [simulateQ_bind]
    rw [embedPrim_query_bind, runMu_bind, runMu_query_inl, hSim, bind_assoc, bind_assoc]
    congr 1; funext u
    rw [pure_bind]
    exact ih u st

theorem runMu_embedPrimMu_bind {α β : Type} (P : Primitives)
    (mx : OracleComp PrimBaseSpec α) (my : α → OracleComp AeadMuIntSimSpec β)
    (st : AeadMuIntState) :
    runMu P (embedPrimMu mx >>= my) st =
      (do let a ← simulateQ (primBaseImpl P) mx; runMu P (my a) st) := by
  rw [runMu_bind, runMu_embedPrimMu]
  simp only [bind_assoc, pure_bind]

@[simp] theorem runMu_unifMu {α : Type} (P : Primitives) (oa : ProbComp α) (st : AeadMuIntState) :
    runMu P (unifMu oa) st = (oa >>= fun a => pure (a, st)) := by
  rw [unifMu, runMu_embedPrimMu, simulateQ_embedUnif]

@[simp] theorem runMu_primMuQ (P : Primitives) (op : PrimQuery) (st : AeadMuIntState) :
    runMu P (primMuQ op) st =
      (simulateQ (primBaseImpl P) (primQ op) >>= fun a => pure (a, st)) := by
  rw [primMuQ, runMu_embedPrimMu]

@[simp] theorem runMu_aeadDec (P : Primitives) (mk : MessageKeys) (ad ct : Bytes)
    (st : AeadMuIntState) :
    @runMu (Option Bytes) P (primMuQ (.aeadDec mk ad ct)) st = pure (P.aeadDec mk ad ct, st) := by
  rw [runMu_primMuQ, sim_fg_aeadDec, pure_bind]

@[simp] theorem runMu_deriveMsgKeys (P : Primitives) (seed : Bytes) (salt? : Option Bytes)
    (st : AeadMuIntState) :
    @runMu MessageKeys P (primMuQ (.deriveMsgKeys seed salt?)) st =
      pure (P.deriveMsgKeys seed salt?, st) := by
  rw [runMu_primMuQ, sim_fg_deriveMsgKeys, pure_bind]

theorem runMu_encOnceMuQ_fresh (P : Primitives) (i : Nat) (ad pt : Bytes)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes))) (w : Bool)
    (hC : chal.lookup i = none) (hK : keys.lookup i = none) :
    runMu P (encOnceMuQ i ad pt) (keys, chal, w) =
      (sampleMessageKeys80 >>= fun mk =>
        pure (some (P.aeadEnc mk ad pt),
          ((i, mk) :: keys, (i, (ad, P.aeadEnc mk ad pt)) :: chal, w))) := by
  rw [encOnceMuQ, runMu_query_inr]
  simp [aeadMuImpl, aeadMuIntKey, hC, hK, StateT.run_bind, StateT.run_get, StateT.run_set,
    StateT.run_monadLift, monadLift_self]

theorem runMu_tryForgeMuQ_some (P : Primitives) (i : Nat) (ad ct : Bytes)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes))) (w : Bool)
    (mk : MessageKeys)
    (hC : (chal.lookup i == some (ad, ct)) = false) (hK : keys.lookup i = some mk) :
    runMu P (tryForgeMuQ i ad ct) (keys, chal, w) =
      match P.aeadDec mk ad ct with
      | some _ => pure (true, (keys, chal, true))
      | none => pure (false, (keys, chal, w)) := by
  rw [tryForgeMuQ, runMu_query_inr]
  simp only [aeadMuImpl, aeadMuIntKey, StateT.run_bind, StateT.run_get, pure_bind, hC,
    Bool.false_eq_true, ↓reduceIte, hK, StateT.run_pure]
  split <;> simp_all [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_map]

theorem runMu_tryForgeMuQ_fresh (P : Primitives) (i : Nat) (ad ct : Bytes)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes))) (w : Bool)
    (hC : chal.lookup i = none) (hK : keys.lookup i = none) :
    runMu P (tryForgeMuQ i ad ct) (keys, chal, w) =
      (sampleMessageKeys80 >>= fun mk =>
        match P.aeadDec mk ad ct with
        | some _ => pure (true, ((i, mk) :: keys, chal, true))
        | none => pure (false, ((i, mk) :: keys, chal, w))) := by
  rw [tryForgeMuQ, runMu_query_inr]
  have hC' : (chal.lookup i == some (ad, ct)) = false := by rw [hC]; rfl
  simp only [aeadMuImpl, aeadMuIntKey, StateT.run_bind, StateT.run_get, pure_bind, hC',
    Bool.false_eq_true, ↓reduceIte, hK, StateT.run_monadLift, monadLift_self, bind_assoc,
    StateT.run_set]
  congr 1; funext mk
  split <;> simp_all [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_map]

theorem aeadMuImpl_w_mono (P : Primitives) (q : AeadMuIntQuery)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes))) :
    ∀ y ∈ support ((aeadMuImpl P q).run (keys, chal, true)), y.2.2.2 = true := by
  intro y hy
  rcases q with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
  · simp only [aeadMuImpl, aeadMuIntKey, StateT.run_bind, StateT.run_get, pure_bind] at hy
    cases hC : chal.lookup i with
    | some _ => simp [hC, StateT.run_pure] at hy; subst hy; rfl
    | none =>
      cases hK : keys.lookup i with
      | some mk =>
        simp [hC, hK, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure] at hy
        subst hy; rfl
      | none =>
        simp [hC, hK, StateT.run_bind, StateT.run_get, StateT.run_set,
          StateT.run_monadLift, monadLift_self] at hy
        rcases hy with ⟨_, _, rfl⟩; rfl
  · simp only [aeadMuImpl, aeadMuIntKey, StateT.run_bind, StateT.run_get, pure_bind] at hy
    by_cases hC : (chal.lookup i == some (ad, ct)) = true
    · simp [hC, StateT.run_pure] at hy; subst hy; rfl
    · simp only [hC, Bool.false_eq_true, ↓reduceIte] at hy
      cases hK : keys.lookup i with
      | some mk =>
        simp only [hK, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind] at hy
        split at hy <;>
          simp_all [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            StateT.run_map]
      | none =>
        simp only [hK, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
          StateT.run_get, StateT.run_set, pure_bind, StateT.run_pure,
          MonadAttach.mem_support_bind] at hy
        rcases hy with ⟨mk, _, hy⟩
        split at hy <;>
          simp_all [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            StateT.run_map]

theorem runMu_w_mono {α : Type} (P : Primitives) (mx : OracleComp AeadMuIntSimSpec α)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes))) :
    ∀ y ∈ support (runMu P mx (keys, chal, true)), y.2.2.2 = true := by
  induction mx using OracleComp.inductionOn generalizing keys chal with
  | pure x =>
    intro y hy
    simp only [runMu_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; rfl
  | query_bind q mx ih =>
    intro y hy
    rcases q with pq | iq
    · rw [runMu_bind, runMu_query_inl, bind_assoc] at hy
      rcases MonadAttach.mem_support_bind.mp hy with ⟨u, _, hy'⟩
      rw [pure_bind] at hy'; exact ih u keys chal y hy'
    · rw [runMu_bind, runMu_query_inr] at hy
      rcases MonadAttach.mem_support_bind.mp hy with ⟨p, hq, hy'⟩
      have hw' := aeadMuImpl_w_mono P iq keys chal p hq
      rcases p with ⟨r, keys', chal', w'⟩; dsimp only at hw'; subst hw'
      exact ih r keys' chal' y hy'

end SignalPqxdh.Security
