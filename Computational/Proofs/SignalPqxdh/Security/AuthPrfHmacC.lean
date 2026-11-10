/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacB
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacA
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH authentication: generic hybrid machine for `prfHmacOfMu`

Generalizes `prfHmacMuStep j` to `gStep defer tag`, where deferred ranks (`defer r`) obtain tag
values from `tag` and record deferred forgery checks while non-deferred ranks use `aeadDec`. Also
reshapes `simulateQ` of `gRun` into a single stateful outer simulation of `B.run`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-- Generic multi-key INT-CTXT step: deferred ranks (`defer r`) get tag values from `tag`. -/
def gStep (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    (q : AeadMuIntQuery) (st : PrfHmacMuState) :
    OracleComp PrfHmacSimSpec (aeadMuIntSpec.Range q × PrfHmacMuState) :=
  match q with
  | .encOnce i ad pt =>
    match st.chal.lookup i with
    | some _ => pure (none, st)
    | none => do
      let ((r, mk), st) ← prfHmacMuKey i st
      let ct ← prfHmacPrimQ (.aeadEnc mk ad pt)
      if defer r then do
        let x0 := aeadMacInput ad (etmBody ct)
        let t ← tag r x0
        let ct' := etmBody ct ++ t.take 8
        pure (some ct',
          { st with
            chal := (i, (ad, ct')) :: st.chal
            pending := st.pending.filter (fun e => !(e.1 == r && e.2.1 == x0))
            bad := st.bad || prfHmacPendingHit st.pending r x0 t })
      else
        pure (some ct, { st with chal := (i, (ad, ct)) :: st.chal })
  | .tryForge i ad ct =>
    if st.chal.lookup i == some (ad, ct) then pure (false, st)
    else do
      let ((r, mk), st) ← prfHmacMuKey i st
      let x := aeadMacInput ad (etmBody ct)
      let fresh : Bool :=
        match st.chal.lookup i with
        | some (ad0, ct0) => x != aeadMacInput ad0 (etmBody ct0)
        | none => true
      if fresh ∧ 24 ≤ ct.length then
        if defer r then
          pure (false, { st with pending := (r, x, etmTag ct) :: st.pending })
        else do
          let res ← prfHmacPrimQ (.aeadDec mk ad ct)
          pure (false, { st with bad := st.bad || res.isSome })
      else pure (false, st)

def unifTag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes := fun _ _ => prfHmacUnif sampleBytes32

theorem gStep_prfHmacMuStep (j : ℕ) (q : AeadMuIntQuery) (st : PrfHmacMuState) :
    prfHmacMuStep j q st = gStep (fun r => r ≤ j) (prfHmacTagQ j) q st := rfl

def gRun (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) {α : Type}
    (mx : OracleComp AeadMuIntSimSpec α) (st : PrfHmacMuState) :
    OracleComp PrfHmacSimSpec (α × PrfHmacMuState) :=
  OracleComp.construct
    (C := fun _ => PrfHmacMuState → OracleComp PrfHmacSimSpec (α × PrfHmacMuState))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl pq => do
        let u ← liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl pq))
        r u s
      | Sum.inr mq => do
        let p ← gStep defer tag mq s
        r p.1 p.2)
    mx st

@[simp] theorem gRun_pure (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    {α : Type} (a : α) (st : PrfHmacMuState) :
    gRun defer tag (pure a : OracleComp AeadMuIntSimSpec α) st = pure (a, st) := rfl

theorem gRun_query_inl (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    {α : Type} (pq : ℕ ⊕ PrimQuery)
    (mx : AeadMuIntSimSpec.Range (Sum.inl pq) → OracleComp AeadMuIntSimSpec α)
    (st : PrfHmacMuState) :
    gRun defer tag (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inl pq)) >>= mx) st =
      (liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl pq)) >>= fun u =>
        gRun defer tag (mx u) st) := rfl

theorem gRun_query_inr (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    {α : Type} (mq : AeadMuIntQuery)
    (mx : AeadMuIntSimSpec.Range (Sum.inr mq) → OracleComp AeadMuIntSimSpec α)
    (st : PrfHmacMuState) :
    gRun defer tag (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inr mq)) >>= mx) st =
      (gStep defer tag mq st >>= fun p => gRun defer tag (mx p.1) p.2) := rfl

theorem prfMuRun_eq_gRun (j : ℕ) {α : Type} (mx : OracleComp AeadMuIntSimSpec α)
    (st : PrfHmacMuState) :
    prfMuRun j mx st = gRun (fun r => r ≤ j) (prfHmacTagQ j) mx st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind t mx ih =>
    rcases t with pq | mq
    · rw [gRun_query_inl, prfMuRun_query_inl]
      exact congrArg _ (funext fun u => ih u st)
    · change (prfHmacMuStep j mq st >>= fun p => prfMuRun j (mx p.1) p.2) =
        (gStep _ _ mq st >>= fun p => gRun _ _ (mx p.1) p.2)
      rw [gStep_prfHmacMuStep]
      exact congrArg _ (funext fun p => ih p.1 p.2)

/-- Deferred checks of `gStep` (`prfHmacFinish` with a generic tag source). -/
def gFinish (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    (pending : List (ℕ × Bytes × Bytes)) : List (ℕ × Bytes) → OracleComp PrfHmacSimSpec Bool
  | [] => pure false
  | (r, x) :: pts => do
    let t ← tag r x
    let rest ← gFinish tag pending pts
    pure (prfHmacPendingHit pending r x t || rest)

theorem prfHmacFinish_eq_gFinish (j : ℕ) (pending : List (ℕ × Bytes × Bytes)) :
    ∀ pts, prfHmacFinish j pending pts = gFinish (prfHmacTagQ j) pending pts
  | [] => rfl
  | (r, x) :: pts => by
    simp only [prfHmacFinish, gFinish, prfHmacFinish_eq_gFinish j pending pts]

def pendPts (pending : List (ℕ × Bytes × Bytes)) : List (ℕ × Bytes) :=
  (pending.map (fun e => (e.1, e.2.1))).dedup

/-- Full generic hybrid running `B`, performing deferred tag checks, and returning `bad || hit`. -/
def gAfter (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    (B : AeadMuIntCtxtAdv) : OracleComp PrfHmacSimSpec Bool := do
  let (_, st) ← gRun defer tag B.run {}
  let hit ← gFinish tag st.pending (pendPts st.pending)
  return (st.bad || hit)

theorem prfAfterRun_eq_gAfter (j : ℕ) (B : AeadMuIntCtxtAdv) :
    prfAfterRun j B = gAfter (fun r => r ≤ j) (prfHmacTagQ j) B := by
  unfold prfAfterRun gAfter
  rw [prfHmacOfMuRunAt_eq, prfMuRun_eq_gRun]
  simp only [prfHmacFinish_eq_gFinish, pendPts]

section Reshape

variable (P : Primitives) {σ : Type} (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))

noncomputable def gFull : QueryImpl PrfHmacSimSpec (StateT σ ProbComp) :=
  (primBaseImpl P).liftTarget (StateT σ ProbComp) + ev

noncomputable def gOuter (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes) :
    QueryImpl AeadMuIntSimSpec (StateT (PrfHmacMuState × σ) ProbComp) := fun q =>
  match q with
  | Sum.inl pq => StateT.mk fun s => (primBaseImpl P pq) >>= fun u => pure (u, s)
  | Sum.inr mq => StateT.mk fun s =>
      (simulateQ (gFull P ev) (gStep defer tag mq s.1)).run s.2 >>= fun z =>
        pure (z.1.1, (z.1.2, z.2))

theorem simulateQ_gRun (defer : ℕ → Prop) [DecidablePred defer]
    (tag : ℕ → Bytes → OracleComp PrfHmacSimSpec Bytes)
    {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (st : PrfHmacMuState) (c : σ) :
    (simulateQ (gFull P ev) (gRun defer tag mx st)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (gOuter P ev defer tag) mx).run (st, c) := by
  induction mx using OracleComp.inductionOn generalizing st c with
  | pure a => simp
  | query_bind t mx ih =>
    rcases t with pq | mq
    · rw [gRun_query_inl]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, map_bind, ih]
      simp [gOuter, gFull]
    · rw [gRun_query_inr]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, map_bind, ih]
      simp [gOuter]

end Reshape

end SignalPqxdh.Security
