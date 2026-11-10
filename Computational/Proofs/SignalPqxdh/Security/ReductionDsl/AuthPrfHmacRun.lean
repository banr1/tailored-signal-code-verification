/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacA
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
import VCVio.EvalDist.Monad.Basic

/-!
# Runner Fusion for the `PrfHmac` Reduction

Fuses the two nested interpreters `runWithMuStep` and `prfMuRun` into a single `runWithPrfHmacStep`
over paired state `(hst, mst)`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open SignalPqxdh SignalPqxdh.Security
open FgGapDh
open OracleSpec OracleComp

@[simp] theorem embedPrim_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (m : OracleComp PrimBaseSpec α) (k : α → OracleComp PrimBaseSpec β) :
    embedPrim (spec := spec) (m >>= k) =
      embedPrim (spec := spec) m >>= fun a => embedPrim (spec := spec) (k a) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    change (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := spec) (r u >>= k)) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := spec) (r u)) >>= fun a => embedPrim (spec := spec) (k a)
    rw [bind_assoc]
    congr 1; funext u
    exact ih u

@[simp] theorem embedPrim_map {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β) (m : OracleComp PrimBaseSpec α) :
    embedPrim (spec := spec) (f <$> m) = f <$> embedPrim (spec := spec) m := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, embedPrim_bind]
  rfl

theorem prfMuRun_bind (j : ℕ) {α β : Type} (mx : OracleComp AeadMuIntSimSpec α)
    (k : α → OracleComp AeadMuIntSimSpec β) (st : PrfHmacMuState) :
    prfMuRun j (mx >>= k) st = prfMuRun j mx st >>= fun p => prfMuRun j (k p.1) p.2 := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => simp only [pure_bind, prfMuRun_pure]
  | query_bind q mx ih =>
    rw [bind_assoc]
    rcases q with pq | mq
    · rw [prfMuRun_query_inl, prfMuRun_query_inl, bind_assoc]
      exact congrArg _ (funext fun u => ih u st)
    · rw [prfMuRun_query_inr, prfMuRun_query_inr, bind_assoc]
      exact congrArg _ (funext fun p => ih p.1 p.2)

theorem prfMuRun_embedPrim (j : ℕ) {α : Type} (m : OracleComp PrimBaseSpec α)
    (st : PrfHmacMuState) :
    prfMuRun j (embedPrim (spec := aeadMuIntSpec) m) st =
      (fun a => (a, st)) <$> embedPrim (spec := prfHmacSpec) m := by
  induction m using OracleComp.inductionOn with
  | pure a => simp only [embedPrim_pure, prfMuRun_pure, map_pure]
  | query_bind q r ih =>
    change prfMuRun j (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := aeadMuIntSpec) (r u)) st =
      (fun a => (a, st)) <$> (liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := prfHmacSpec) (r u))
    rw [prfMuRun_query_inl, map_bind]
    exact congrArg _ (funext fun u => ih u)

theorem prfMuRun_embedPrimMu (j : ℕ) {α : Type} (m : OracleComp PrimBaseSpec α)
    (st : PrfHmacMuState) :
    prfMuRun j (embedPrimMu m) st = (fun a => (a, st)) <$> embedPrim (spec := prfHmacSpec) m :=
  prfMuRun_embedPrim j m st

theorem prfMuRun_query (j : ℕ) (mq : AeadMuIntQuery) (st : PrfHmacMuState) :
    prfMuRun j (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inr mq))) st =
      prfHmacMuStep j mq st := by
  have h := prfMuRun_query_inr j mq (fun u => pure u) st
  rw [bind_pure] at h
  rw [h]
  simp only [prfMuRun_pure]
  exact bind_pure _

theorem prfMuRun_encOnceMuQ (j i : ℕ) (ad pt : Bytes) (st : PrfHmacMuState) :
    prfMuRun j (encOnceMuQ i ad pt) st = prfHmacMuStep j (.encOnce i ad pt) st :=
  prfMuRun_query j _ st

theorem prfMuRun_tryForgeMuQ (j i : ℕ) (ad ct : Bytes) (st : PrfHmacMuState) :
    prfMuRun j (tryForgeMuQ i ad ct) st = prfHmacMuStep j (.tryForge i ad ct) st :=
  prfMuRun_query j _ st

/-- Interprets `OracleComp (unifSpec + GSpec)` into `OracleComp PrfHmacSimSpec` using `step` for
game queries and forwarding uniform coin queries directly. -/
def runWithPrfHmacStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrfHmacSimSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp PrfHmacSimSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp PrfHmacSimSpec (α × St))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl (Sum.inl n)))
        r u s
      | Sum.inr gq => do
        let p ← step gq s
        r p.1 p.2)
    mx st

theorem runWithPrfHmacStep_pure {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St α : Type} (step : (q : ιI) → St → OracleComp PrfHmacSimSpec (GSpec.Range q × St))
    (a : α) (st : St) :
    runWithPrfHmacStep step (pure a : OracleComp (unifSpec + GSpec) α) st = pure (a, st) := rfl

theorem runWithPrfHmacStep_query_inl {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St α : Type} (step : (q : ιI) → St → OracleComp PrfHmacSimSpec (GSpec.Range q × St))
    (n : ℕ) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrfHmacStep step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) st =
      (liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => runWithPrfHmacStep step (mx u) st) := rfl

theorem runWithPrfHmacStep_query_inr {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St α : Type} (step : (q : ιI) → St → OracleComp PrfHmacSimSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrfHmacStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) st =
      (step gq st >>= fun p => runWithPrfHmacStep step (mx p.1) p.2) := rfl

/-- Runs a multi-key step and interprets its multi-key queries with `prfHmacMuStep j`. -/
def fuseStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St : Type} (j : ℕ)
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St)) :
    (q : ιI) → St × PrfHmacMuState →
      OracleComp PrfHmacSimSpec (GSpec.Range q × (St × PrfHmacMuState)) :=
  fun q s => (fun p => (p.1.1, (p.1.2, p.2))) <$> prfMuRun j (step q s.1) s.2

theorem prfMuRun_runWithMuStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (j : ℕ) (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (hst : St) (mst : PrfHmacMuState) :
    prfMuRun j (runWithMuStep step mx hst) mst =
      (fun p => ((p.1, p.2.1), p.2.2)) <$>
        runWithPrfHmacStep (fuseStep j step) mx (hst, mst) := by
  induction mx using OracleComp.inductionOn generalizing hst mst with
  | pure a => simp only [runWithMuStep_pure, prfMuRun_pure, runWithPrfHmacStep_pure, map_pure]
  | query_bind q mx ih =>
    rcases q with n | gq
    · rw [runWithMuStep_query_inl, prfMuRun_query_inl, runWithPrfHmacStep_query_inl, map_bind]
      exact congrArg _ (funext fun u => ih u hst mst)
    · rw [runWithMuStep_query_inr, prfMuRun_bind, runWithPrfHmacStep_query_inr, fuseStep,
        bind_map_left, map_bind]
      exact congrArg _ (funext fun p => ih p.1.1 p.1.2 p.2)

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
