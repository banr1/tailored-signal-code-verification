/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.CollisionsB
import Computational.Proofs.GameHop.StateSim
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.QueryTracking.SubSpec

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open Computational.Proofs.GameHop
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

theorem probExpect_map {α β : Type} (mx : ProbComp α) (f : α → β) (v : β → ℝ≥0∞) :
    probExpect (f <$> mx) v = probExpect mx (fun x => v (f x)) := by
  rw [map_eq_bind_pure_comp, probExpect_bind]
  congr 1; ext x
  exact probExpect_pure (f x) v

@[simp]
theorem embedPrim_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    embedPrim (spec := spec) (pure a) = pure a := rfl

@[simp]
theorem embedPrim_query_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (q : PrimBaseSpec.Domain)
    (k : PrimBaseSpec.Range q → OracleComp PrimBaseSpec α) :
    embedPrim (spec := spec) (liftM (OracleSpec.query q) >>= k) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := spec) (k u)) := rfl

/-- Shorthand for `IsQueryBoundP oa (fun q => isPrimQuery₀ q = true) n`. -/
abbrev PrimBounded {α : Type} (oa : OracleComp PrimBaseSpec α) (n : ℕ) : Prop :=
  IsQueryBoundP oa (fun q => isPrimQuery₀ q = true) n

theorem primBounded_pure {α : Type} (a : α) (n : ℕ) : PrimBounded (pure a) n :=
  (isQueryBoundP_pure (fun q => isPrimQuery₀ q = true) a 0).mono (Nat.zero_le n)

theorem primBounded_mono {α : Type} {oa : OracleComp PrimBaseSpec α} {m n : ℕ}
    (h : PrimBounded oa m) (hle : m ≤ n) : PrimBounded oa n :=
  h.mono hle

theorem primBounded_primQ (op : PrimQuery) : PrimBounded (primQ op) 1 :=
  (isQueryBoundP_query_iff (spec := PrimBaseSpec)
    (fun q => isPrimQuery₀ q = true) (Sum.inr op) 1).2 (fun _ => Nat.zero_lt_one)

theorem primBounded_embedUnif {α : Type} (mx : ProbComp α) (n : ℕ) :
    PrimBounded (embedUnif mx) n := by
  unfold embedUnif PrimBounded
  exact (IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun _ => ⟨False.elim, fun h => Bool.false_ne_true h⟩) (StateSim.isQueryBoundP_false mx 0)).mono
    (Nat.zero_le n)

theorem primBounded_bind {α β : Type} {oa : OracleComp PrimBaseSpec α}
    {k : α → OracleComp PrimBaseSpec β} {m n : ℕ}
    (h1 : PrimBounded oa m) (h2 : ∀ x, PrimBounded (k x) n) :
    PrimBounded (oa >>= k) (m + n) :=
  isQueryBoundP_bind h1 (fun x _ => h2 x)

theorem primBounded_pure' {α : Type} {a : α} {n : ℕ} : PrimBounded (pure a) n :=
  primBounded_pure a n

theorem primBounded_bind_le {α β : Type} {oa : OracleComp PrimBaseSpec α}
    {k : α → OracleComp PrimBaseSpec β} {m p : ℕ} (n : ℕ)
    (h1 : PrimBounded oa m) (h2 : ∀ x, PrimBounded (k x) n) (hp : m + n ≤ p := by omega) :
    PrimBounded (oa >>= k) p :=
  (primBounded_bind h1 h2).mono hp

theorem primBounded_findMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (c : ℕ)
    (hp : ∀ a, PrimBounded (p a) c) :
    ∀ (L : List α), PrimBounded (findMPrim p L) (L.length * c)
  | [] => by simp [findMPrim]
  | x :: xs => by
    simp only [findMPrim]
    refine primBounded_bind_le (xs.length * c) (hp x) (fun b => ?_)
      (by simp [Nat.succ_mul]; omega)
    cases b with
    | true => exact primBounded_pure (some x) (xs.length * c)
    | false => exact primBounded_findMPrim p c hp xs

theorem primBounded_findMPrim_take {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (c N : ℕ)
    (L : List α) (hp : ∀ a, PrimBounded (p a) c) :
    PrimBounded (findMPrim p (L.take N)) (N * c) :=
  (primBounded_findMPrim p c hp (L.take N)).mono
    (Nat.mul_le_mul_right c (List.length_take_le N L))

theorem primBounded_anyMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (c : ℕ)
    (hp : ∀ a, PrimBounded (p a) c) :
    ∀ (L : List α), PrimBounded (anyMPrim p L) (L.length * c)
  | [] => by simp [anyMPrim]
  | x :: xs => by
    simp only [anyMPrim]
    refine primBounded_bind_le (xs.length * c) (hp x) (fun b => ?_)
      (by simp [Nat.succ_mul]; omega)
    cases b with
    | true => exact primBounded_pure true (xs.length * c)
    | false => exact primBounded_anyMPrim p c hp xs

theorem primBounded_anyMPrim_take {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (c N : ℕ)
    (L : List α) (hp : ∀ a, PrimBounded (p a) c) :
    PrimBounded (anyMPrim p (L.take N)) (N * c) :=
  (primBounded_anyMPrim p c hp (L.take N)).mono
    (Nat.mul_le_mul_right c (List.length_take_le N L))

@[simp]
theorem simulateQ_primQ (P : Primitives) (op : PrimQuery) :
    simulateQ (primBaseImpl P) (primQ op) = primImpl P op :=
  QueryImpl.simulateQ_add_query_right _ _ op

@[simp]
theorem simulateQ_embedUnif {α : Type} (P : Primitives) (mx : ProbComp α) :
    simulateQ (primBaseImpl P) (embedUnif mx) = mx := by
  unfold embedUnif primBaseImpl
  rw [QueryImpl.simulateQ_add_liftComp_left]
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k _ => simp [simulateQ_bind]

theorem simulateQ_findMPrim {α : Type} (P : Primitives)
    (p : α → OracleComp PrimBaseSpec Bool) (f : α → Bool)
    (hp : ∀ a, simulateQ (primBaseImpl P) (p a) = pure (f a)) :
    ∀ (L : List α), simulateQ (primBaseImpl P) (findMPrim p L) = pure (L.find? f)
  | [] => by simp [findMPrim]
  | x :: xs => by
    simp only [findMPrim, simulateQ_bind, hp x, pure_bind, List.find?_cons]
    cases f x <;> simp [simulateQ_findMPrim P p f hp xs]

theorem simulateQ_anyMPrim {α : Type} (P : Primitives)
    (p : α → OracleComp PrimBaseSpec Bool) (f : α → Bool)
    (hp : ∀ a, simulateQ (primBaseImpl P) (p a) = pure (f a)) :
    ∀ (L : List α), simulateQ (primBaseImpl P) (anyMPrim p L) = pure (L.any f)
  | [] => by simp [anyMPrim]
  | x :: xs => by
    simp only [anyMPrim, simulateQ_bind, hp x, pure_bind, List.any_cons]
    cases f x <;> simp [simulateQ_anyMPrim P p f hp xs]

theorem isQueryBoundP_embedPrim_isRight {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) (n : ℕ) :
    IsQueryBoundP (embedPrim (spec := spec) mx)
      (fun q : (ℕ ⊕ PrimQuery) ⊕ ι => q.isRight = true) n := by
  induction mx using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q k ih =>
    rw [embedPrim_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (fun h => by cases h), fun u => ih u n⟩

theorem isQueryBoundP_embedPrim_isPrimQuery {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) (n : ℕ) (h : PrimBounded mx n) :
    IsQueryBoundP (embedPrim (spec := spec) mx)
      (fun q : (ℕ ⊕ PrimQuery) ⊕ ι => isPrimQuery q = true) n := by
  induction mx using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q k ih =>
    rw [PrimBounded, isQueryBoundP_query_bind_iff] at h
    rw [embedPrim_query_bind, isQueryBoundP_query_bind_iff]
    have h_eq : isPrimQuery (Sum.inl q : (ℕ ⊕ PrimQuery) ⊕ ι) = isPrimQuery₀ q := by
      cases q <;> rfl
    rw [h_eq]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem simulateQ_embedPrim_run {ι : Type} {spec : OracleSpec.{0, 0} ι} {α σ : Type}
    (P : Primitives) (impl : QueryImpl spec (StateT σ ProbComp))
    (mx : OracleComp PrimBaseSpec α) (st : σ) :
    (simulateQ ((primBaseImpl P).liftTarget (StateT σ ProbComp) + impl)
      (embedPrim mx)).run st = (fun a => (a, st)) <$> simulateQ (primBaseImpl P) mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    simp [embedPrim_query_bind, simulateQ_bind, StateT.run_bind, ih]

inductive SigStepResult (St R : Type) where
  | done (res : R) (st' : St)
  | signTwo
      (msg1 : Bytes)
      (k1 : Bytes → ProbComp (Bytes × (Bytes → R × St)))
      (fallback : R × St)

noncomputable def SigStepResultPrim.toProbComp {St R : Type} (P : Primitives) :
    SigStepResultPrim St R → SigStepResult St R
  | .done res st' => .done res st'
  | .signTwo msg1 k1 fb => .signTwo msg1 (fun sig1 => (fun pq => k1 pq sig1) <$> sampleKemKeyGen P)
      fb

theorem primBounded_sampleKemKeyGenPrim : PrimBounded sampleKemKeyGenPrim 1 :=
  primBounded_bind_le 1 (primBounded_embedUnif sampleRandom64 0)
    (fun seed => primBounded_primQ (.kemKeyGen seed))

@[simp]
theorem simulateQ_sampleKemKeyGenPrim (P : Primitives) :
    simulateQ (primBaseImpl P) sampleKemKeyGenPrim = sampleKemKeyGen P := by
  unfold sampleKemKeyGenPrim sampleKemKeyGen
  simp only [simulateQ_bind, simulateQ_embedUnif]
  rfl

theorem runWithSigBudgetPrim_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (a : α) (st : St) (budget : Nat) :
    runWithSigBudgetPrim step (pure a) st budget = pure (a, st) := rfl

theorem runWithSigBudgetPrim_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) (budget : Nat) :
    runWithSigBudgetPrim step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) st budget =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => runWithSigBudgetPrim step (mx u) st budget) := rfl

theorem runWithSigBudgetPrim_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) (budget : Nat) :
    runWithSigBudgetPrim step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) st budget =
      (do
        let sr ← embedPrim (spec := sigOracleSpec) (step gq st)
        match sr with
        | .done res st' => runWithSigBudgetPrim step (mx res) st' budget
        | .signTwo msg1 k1 fallback =>
          match budget with
          | 0 => runWithSigBudgetPrim step (mx fallback.1) fallback.2 0
          | b' + 1 => do
            let sig1 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg1))
            let pq ← embedPrim (spec := sigOracleSpec) sampleKemKeyGenPrim
            let (msg2, k2) := k1 pq sig1
            let sig2 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg2))
            let p := k2 sig2
            runWithSigBudgetPrim step (mx p.1) p.2 b') := rfl

theorem isQueryBoundP_runWithSigBudgetPrim_prim {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (C : Nat) (h_step : ∀ gq st, PrimBounded (step gq st) C)
    (mx : OracleComp (unifSpec + GSpec) α) (Q : Nat)
    (h_mx : IsQueryBoundP mx (fun q : Nat ⊕ ιI => q.isRight = true) Q)
    (st : St) (budget : Nat) :
    IsQueryBoundP (runWithSigBudgetPrim step mx st budget)
      (fun q : (Nat ⊕ PrimQuery) ⊕ SigQuery => isPrimQuery q = true) (Q * (C + 1)) := by
  induction mx using OracleComp.inductionOn generalizing Q st budget with
  | pure x =>
    simp [runWithSigBudgetPrim_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx
    cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      rw [runWithSigBudgetPrim_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u Q (h_cont u) st budget⟩
    | inr gq =>
      rcases h_mx with ⟨h_abs | hQpos, h_cont⟩
      · exfalso; exact h_abs rfl
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        simp only [Sum.isRight_inr, ↓reduceIte, Nat.add_sub_cancel] at h_cont
        rw [runWithSigBudgetPrim_query_inr]
        have h_st := isQueryBoundP_embedPrim_isPrimQuery (spec :=
            sigOracleSpec) (step gq st) C (h_step gq st)
        refine (isQueryBoundP_bind (m := Q' * (C + 1) + 1) h_st (fun sr _ => ?_)).mono
          (by rw [Nat.succ_mul]; omega)
        cases sr with
        | done res st' =>
          exact (ih res Q' (h_cont res) st' budget).mono (by omega)
        | signTwo msg1 k1 fallback =>
          cases budget with
          | zero =>
            exact (ih fallback.1 Q' (h_cont fallback.1) fallback.2 0).mono (by omega)
          | succ b' =>
            have h_sig1 : IsQueryBoundP (query (spec := PrimBaseSpec +
                sigOracleSpec) (Sum.inr (SigQuery.sign msg1)))
                (fun q : (Nat ⊕ PrimQuery) ⊕ SigQuery => isPrimQuery q = true) 0 :=
              (isQueryBoundP_query_iff (spec := PrimBaseSpec +
                  sigOracleSpec) _ (Sum.inr (SigQuery.sign msg1)) 0).2 (fun h => by cases h)
            refine (isQueryBoundP_bind (m := Q' * (C + 1) +
                1) h_sig1 (fun sig1 _ => ?_)).mono (by omega)
            have h_kem := isQueryBoundP_embedPrim_isPrimQuery (spec := sigOracleSpec)
              sampleKemKeyGenPrim 1 primBounded_sampleKemKeyGenPrim
            refine (isQueryBoundP_bind (m := Q' * (C + 1)) h_kem (fun pq _ => ?_)).mono (by omega)
            have h_sig2 : IsQueryBoundP (query (spec := PrimBaseSpec +
                sigOracleSpec) (Sum.inr (SigQuery.sign (k1 pq sig1).1)))
                (fun q : (Nat ⊕ PrimQuery) ⊕ SigQuery => isPrimQuery q = true) 0 :=
              (isQueryBoundP_query_iff (spec := PrimBaseSpec +
                  sigOracleSpec) _ (Sum.inr (SigQuery.sign (k1 pq sig1).1)) 0).2 (fun h => by cases
                  h)
            exact (isQueryBoundP_bind (m := Q' * (C + 1)) h_sig2 (fun sig2 _ =>
              ih ((k1 pq sig1).2 sig2).1 Q' (h_cont _) ((k1 pq sig1).2 sig2).2 b')).mono (by omega)

def sigEufCmaOracleImpl (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec (StateT (List Bytes) ProbComp) :=
  fun (.sign m) => do
    let r ← liftM sampleRandom64
    let sig := P.sigSign sk m r
    modify (m :: ·)
    return sig

def sigEufCmaFullImpl (P : Primitives) (sk : Bytes) :
    QueryImpl (PrimBaseSpec + sigOracleSpec) (StateT (List Bytes) ProbComp) :=
  (primBaseImpl P).liftTarget (StateT (List Bytes) ProbComp) +
    sigEufCmaOracleImpl P sk

@[simp] theorem StateT_modifyGet_run {σ α : Type} {m : Type → Type} [Monad m]
    (f : σ → α × σ) (s : σ) :
    (StateT.modifyGet (m := m) f).run s = pure (f s) := rfl

noncomputable def runSigStepSim {St R : Type} (P : Primitives) (sk : Bytes) (budget : Nat)
    (stepComp : ProbComp (SigStepResult St R)) (signedMsgs : List Bytes) :
    ProbComp ((R × St × Nat) × List Bytes) := do
  let res ← stepComp
  match res with
  | .done out st' =>
    return ((out, st', budget), signedMsgs)
  | .signTwo msg1 k1 (fbOut, fbSt) =>
    match budget with
    | 0 =>
      return ((fbOut, fbSt, 0), signedMsgs)
    | b + 1 =>
      let r1 ← sampleRandom64
      let sig1 := P.sigSign sk msg1 r1
      let (msg2, k2) ← k1 sig1
      let r2 ← sampleRandom64
      let sig2 := P.sigSign sk msg2 r2
      let (out, st') := k2 sig2
      return ((out, st', b), msg2 :: msg1 :: signedMsgs)

theorem probExpect_runWithSigBudgetPrim_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (sk : Bytes)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (a : α) (s : St) (budget : Nat) (signedMsgs : List Bytes)
    (f : (α × St) × List Bytes → ℝ≥0∞) :
    probExpect
      ((simulateQ (sigEufCmaFullImpl P sk)
        (runWithSigBudgetPrim step (pure a) s budget)).run signedMsgs) f =
    f ((a, s), signedMsgs) := by
  simp [runWithSigBudgetPrim_pure, probExpect_pure]

theorem probExpect_runWithSigBudgetPrim_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (sk : Bytes)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (s : St) (budget : Nat) (signedMsgs : List Bytes)
    (f : (α × St) × List Bytes → ℝ≥0∞) :
    probExpect
      ((simulateQ (sigEufCmaFullImpl P sk)
        (runWithSigBudgetPrim step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) s budget)).run
            signedMsgs) f =
    probExpect (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) (fun u =>
      probExpect
        ((simulateQ (sigEufCmaFullImpl P sk)
          (runWithSigBudgetPrim step (mx u) s budget)).run signedMsgs) f) := by
  rw [runWithSigBudgetPrim_query_inl]
  simp [sigEufCmaFullImpl, primBaseImpl, simulateQ_bind, StateT.run_bind, probExpect_bind]

theorem probExpect_runWithSigBudgetPrim_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (sk : Bytes)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (s : St) (budget : Nat) (signedMsgs : List Bytes)
    (f : (α × St) × List Bytes → ℝ≥0∞) :
    probExpect
      ((simulateQ (sigEufCmaFullImpl P sk)
        (runWithSigBudgetPrim step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) s budget)).run
            signedMsgs) f =
    probExpect (runSigStepSim P sk budget (SigStepResultPrim.toProbComp P <$> simulateQ
        (primBaseImpl P) (step gq s)) signedMsgs)
      (fun ((out, s', b'), msgs') =>
        probExpect
          ((simulateQ (sigEufCmaFullImpl P sk)
            (runWithSigBudgetPrim step (mx out) s' b')).run msgs') f) := by
  rw [runWithSigBudgetPrim_query_inr]
  unfold runSigStepSim
  simp only [simulateQ_bind, StateT.run_bind, probExpect_bind, probExpect_map]
  rw [sigEufCmaFullImpl, simulateQ_embedPrim_run, probExpect_map]
  apply congrArg (probExpect (simulateQ (primBaseImpl P) (step gq s)))
  ext sr
  cases sr with
  | done res st' =>
    simp [SigStepResultPrim.toProbComp]
  | signTwo msg1 k1 fb =>
    rcases fb with ⟨fbOut, fbSt⟩
    cases budget with
    | zero =>
      simp [SigStepResultPrim.toProbComp]
    | succ b' =>
      simp only [SigStepResultPrim.toProbComp, simulateQ_bind, StateT.run_bind, query,
        QueryImpl.simulateQ_add_query_right, sigEufCmaOracleImpl, StateT.run_monadLift,
        monadLift_self, modify, modifyGet, MonadStateOf.modifyGet, StateT_modifyGet_run,
        bind_assoc, pure_bind, probExpect_bind]
      apply congrArg (probExpect sampleRandom64)
      ext r1
      rw [simulateQ_embedPrim_run, simulateQ_sampleKemKeyGenPrim, probExpect_map, probExpect_map]
      apply congrArg (probExpect (sampleKemKeyGen P))
      ext ⟨pqspkPk, pqspkSk⟩
      simp only [probExpect_pure]

theorem primBounded_findHonestPrincipalPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    PrimBounded (findHonestPrincipalPrim S principals ikB) (S.N_dh * 2) := by
  unfold findHonestPrincipalPrim
  refine primBounded_findMPrim_take _ 2 S.N_dh principals (fun (_, entry) => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_findHonestPrincipalPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes)
    (hLen : principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (findHonestPrincipalPrim S principals ikB) =
      pure (findHonestPrincipal P principals ikB) := by
  unfold findHonestPrincipalPrim findHonestPrincipal
  rw [List.take_of_length_le hLen]
  exact simulateQ_findMPrim P _ _ (fun _ => rfl) principals

theorem primBounded_resolveSigPkPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    PrimBounded (resolveSigPkPrim S principals ikB) (S.N_dh * 2) := by
  unfold resolveSigPkPrim
  refine primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S principals ikB) (fun r => ?_)
  cases r <;> exact primBounded_pure'

theorem simulateQ_resolveSigPkPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes)
    (hLen : principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (resolveSigPkPrim S principals ikB) =
      pure (resolveSigPk P principals ikB) := by
  unfold resolveSigPkPrim resolveSigPk
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals ikB hLen, pure_bind]
  cases findHonestPrincipal P principals ikB <;> rfl

theorem primBounded_isHonestUncorruptedPeerPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    PrimBounded (isHonestUncorruptedPeerPrim S principals ikB) (S.N_dh * 2) := by
  unfold isHonestUncorruptedPeerPrim
  refine primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S principals ikB) (fun r => ?_)
  cases r <;> exact primBounded_pure'

theorem simulateQ_isHonestUncorruptedPeerPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes)
    (hLen : principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (isHonestUncorruptedPeerPrim S principals ikB) =
      pure (isHonestUncorruptedPeer P principals ikB) := by
  unfold isHonestUncorruptedPeerPrim isHonestUncorruptedPeer
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals ikB hLen, pure_bind]
  cases findHonestPrincipal P principals ikB <;> rfl

theorem primBounded_checkBundleProvenancePrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    PrimBounded (checkBundleProvenancePrim S principals spkBundles opkEntries bundle) (S.N_dh * 6)
        := by
  unfold checkBundleProvenancePrim
  refine primBounded_bind_le (S.N_dh * 4) (primBounded_findHonestPrincipalPrim S principals
      bundle.ikB) (fun r => ?_)
  cases r with
  | none => exact primBounded_pure'
  | some kp =>
    rcases kp with ⟨k, _⟩
    have h_spk : PrimBounded (anyMPrim (fun ((u, _), b) => do
        let p1 ← primQ (.pow8 b.spkPk)
        let p2 ← primQ (.pow8 bundle.spkB)
        return (u == k && p1 == p2)) (spkBundles.take S.N_dh)) (S.N_dh * 2) := by
      refine primBounded_anyMPrim_take _ 2 S.N_dh spkBundles (fun ((u, _), b) => ?_)
      refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
    refine primBounded_bind_le (S.N_dh * 2) h_spk (fun _ => ?_)
    cases bundle.opkB? with
    | none =>
      exact primBounded_bind_le 0 (primBounded_pure false 0) (fun _ => primBounded_pure')
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      have h_opk : PrimBounded (anyMPrim (fun ((u, _, _), e) => do
          let p1 ← primQ (.pow8 e.opkPk)
          let p2 ← primQ (.pow8 opkPk)
          return (u == k && p1 == p2)) (opkEntries.take S.N_dh)) (S.N_dh * 2) := by
        refine primBounded_anyMPrim_take _ 2 S.N_dh opkEntries (fun ((u, _, _), e) => ?_)
        refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
      exact primBounded_bind_le 0 h_opk (fun _ => primBounded_pure')

theorem simulateQ_checkBundleProvenancePrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh)
    (hSpk : spkBundles.length ≤ S.N_dh)
    (hOpk : opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (checkBundleProvenancePrim S principals spkBundles opkEntries bundle)
        =
      pure (checkBundleProvenance P principals spkBundles opkEntries bundle) := by
  unfold checkBundleProvenancePrim checkBundleProvenance
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals bundle.ikB hPrin, pure_bind]
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, _⟩
    dsimp only
    rw [List.take_of_length_le hSpk, simulateQ_bind,
        simulateQ_anyMPrim P _ (fun ((u, _), b) => u == k &&
            P.pow8 b.spkPk == P.pow8 bundle.spkB) (fun _ => rfl) spkBundles, pure_bind]
    cases bundle.opkB? with
    | none => simp
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      dsimp only
      rw [List.take_of_length_le hOpk, simulateQ_bind,
          simulateQ_anyMPrim P _ (fun ((u, _, _), e) => u == k &&
              P.pow8 e.opkPk == P.pow8 opkPk) (fun _ => rfl) opkEntries, pure_bind]
      rfl

def ValidAdvKeysPow8 (P : Primitives) (advKeys : List (Bytes × Bytes)) : Prop :=
  ∀ e ∈ advKeys, e.1 = P.pow8 e.2

theorem primBounded_isAdvRegisteredPrim (advKeys : List (Bytes × Bytes)) (pk : Bytes) :
    PrimBounded (isAdvRegisteredPrim advKeys pk) 1 := by
  unfold isAdvRegisteredPrim
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_isAdvRegisteredPrim (P : Primitives)
    (advKeys : List (Bytes × Bytes)) (pk : Bytes)
    (hAdv : ValidAdvKeysPow8 P advKeys) :
    simulateQ (primBaseImpl P) (isAdvRegisteredPrim advKeys pk) =
      pure (isAdvRegistered P advKeys pk) := by
  unfold isAdvRegisteredPrim isAdvRegistered
  change (pure (advKeys.any (fun (p8, _) => P.pow8 pk == p8)) : ProbComp Bool) =
    pure (advKeys.any (fun (_, pk') => P.pow8 pk == P.pow8 pk'))
  congr 1
  induction advKeys with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨p8, pk'⟩
    have h1 : p8 = P.pow8 pk' := hAdv (p8, pk') List.mem_cons_self
    simp only [List.any_cons, h1, ih (fun e he => hAdv e (List.mem_cons_of_mem _ he))]

theorem primBounded_isGameIdKeyPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (pk : Bytes) :
    PrimBounded (isGameIdKeyPrim S principals pk) (S.N_dh * 2) := by
  unfold isGameIdKeyPrim
  exact primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S principals pk) (fun _ =>
      primBounded_pure')

theorem simulateQ_isGameIdKeyPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (pk : Bytes)
    (hPrin : principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (isGameIdKeyPrim S principals pk) =
      pure (isGameIdKey P principals pk) := by
  unfold isGameIdKeyPrim isGameIdKey
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals pk hPrin, pure_bind]
  rfl

theorem primBounded_isGameSpkPrim (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    PrimBounded (isGameSpkPrim S spkBundles pk) (S.N_dh * 2) := by
  unfold isGameSpkPrim
  refine primBounded_anyMPrim_take _ 2 S.N_dh spkBundles (fun (_, b) => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_isGameSpkPrim (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes)
    (hSpk : spkBundles.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (isGameSpkPrim S spkBundles pk) =
      pure (isGameSpk P spkBundles pk) := by
  unfold isGameSpkPrim isGameSpk
  rw [List.take_of_length_le hSpk]
  refine simulateQ_anyMPrim P _ _ (fun _ => ?_) spkBundles
  rfl

theorem primBounded_isGameOpkPrim (S : Setup)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (pk : Bytes) :
    PrimBounded (isGameOpkPrim S opkEntries pk) (S.N_dh * 2) := by
  unfold isGameOpkPrim
  refine primBounded_anyMPrim_take _ 2 S.N_dh opkEntries (fun (_, e) => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_isGameOpkPrim (S : Setup) (P : Primitives)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (pk : Bytes)
    (hOpk : opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (isGameOpkPrim S opkEntries pk) =
      pure (isGameOpk P opkEntries pk) := by
  unfold isGameOpkPrim isGameOpk
  rw [List.take_of_length_le hOpk]
  refine simulateQ_anyMPrim P _ _ (fun _ => ?_) opkEntries
  rfl

theorem primBounded_koskBundleOkPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    PrimBounded (koskBundleOkPrim S principals spkBundles opkEntries advKeys bundle)
      (S.N_dh * 6 + 3) := by
  unfold koskBundleOkPrim
  refine primBounded_bind_le (S.N_dh * 4 +
      3) (primBounded_isGameIdKeyPrim S principals bundle.ikB) (fun _ => ?_)
  refine primBounded_bind_le (S.N_dh * 4 +
      2) (primBounded_isAdvRegisteredPrim advKeys bundle.ikB) (fun _ => ?_)
  refine primBounded_bind_le (S.N_dh * 2 +
      2) (primBounded_isGameSpkPrim S spkBundles bundle.spkB) (fun _ => ?_)
  refine primBounded_bind_le (S.N_dh * 2 +
      1) (primBounded_isAdvRegisteredPrim advKeys bundle.spkB) (fun _ => ?_)
  cases bundle.opkB? with
  | none => exact primBounded_pure'
  | some opkPair =>
    rcases opkPair with ⟨_, opkPk⟩
    dsimp only
    refine primBounded_bind_le 1 (primBounded_isGameOpkPrim S opkEntries opkPk) (fun _ => ?_)
    exact primBounded_bind_le 0 (primBounded_isAdvRegisteredPrim advKeys opkPk) (fun _ =>
        primBounded_pure')

theorem simulateQ_koskBundleOkPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh)
    (hSpk : spkBundles.length ≤ S.N_dh)
    (hOpk : opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P advKeys) :
    simulateQ (primBaseImpl P) (koskBundleOkPrim S principals spkBundles opkEntries advKeys bundle)
        =
      pure (koskBundleOk P principals spkBundles opkEntries advKeys bundle) := by
  unfold koskBundleOkPrim koskBundleOk
  rw [simulateQ_bind, simulateQ_isGameIdKeyPrim S P principals bundle.ikB hPrin, pure_bind,
      simulateQ_bind, simulateQ_isAdvRegisteredPrim P advKeys bundle.ikB hAdv, pure_bind,
      simulateQ_bind, simulateQ_isGameSpkPrim S P spkBundles bundle.spkB hSpk, pure_bind,
      simulateQ_bind, simulateQ_isAdvRegisteredPrim P advKeys bundle.spkB hAdv, pure_bind]
  cases bundle.opkB? with
  | none => rfl
  | some opkPair =>
    rcases opkPair with ⟨_, opkPk⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_isGameOpkPrim S P opkEntries opkPk hOpk, pure_bind,
        simulateQ_bind, simulateQ_isAdvRegisteredPrim P advKeys opkPk hAdv, pure_bind]
    rfl

theorem primBounded_koskSenderOkPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) :
    PrimBounded (koskSenderOkPrim S principals advKeys ikAPk) (S.N_dh * 2 + 1) := by
  unfold koskSenderOkPrim
  refine primBounded_bind_le 1 (primBounded_isGameIdKeyPrim S principals ikAPk) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_isAdvRegisteredPrim advKeys ikAPk) (fun _ =>
      primBounded_pure')

theorem simulateQ_koskSenderOkPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes)
    (hPrin : principals.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P advKeys) :
    simulateQ (primBaseImpl P) (koskSenderOkPrim S principals advKeys ikAPk) =
      pure (koskSenderOk P principals advKeys ikAPk) := by
  unfold koskSenderOkPrim koskSenderOk
  rw [simulateQ_bind, simulateQ_isGameIdKeyPrim S P principals ikAPk hPrin, pure_bind,
      simulateQ_bind, simulateQ_isAdvRegisteredPrim P advKeys ikAPk hAdv, pure_bind]
  rfl

theorem primBounded_extractBundleForgeryPrim (S : Setup)
    (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (prevForgery : Option (Bytes × Bytes)) :
    PrimBounded (extractBundleForgeryPrim S targetParty targetPk principals spkBundles bundle
        prevForgery)
      (S.N_dh * 2 + 2) := by
  unfold extractBundleForgeryPrim
  refine primBounded_bind_le 2 (primBounded_isHonestUncorruptedPeerPrim S principals bundle.ikB)
      (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_extractBundleForgeryPrim (S : Setup) (P : Primitives)
    (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (prevForgery : Option (Bytes × Bytes))
    (hPrin : principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (extractBundleForgeryPrim S targetParty targetPk principals spkBundles bundle prevForgery) =
      pure (extractBundleForgery P targetParty targetPk principals spkBundles bundle prevForgery) :=
          by
  unfold extractBundleForgeryPrim extractBundleForgery
  rw [simulateQ_bind, simulateQ_isHonestUncorruptedPeerPrim S P principals bundle.ikB hPrin,
      pure_bind]
  rfl

theorem primBounded_keyIndPartnerPrim {S : Setup}
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    PrimBounded (keyIndPartnerPrim s r) 8 := by
  unfold keyIndPartnerPrim
  refine primBounded_bind_le 7 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 6 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 4 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_keyIndPartnerPrim {S : Setup} (P : Primitives)
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    simulateQ (primBaseImpl P) (keyIndPartnerPrim s r) = pure (keyIndPartner P s r) := by
  unfold keyIndPartnerPrim keyIndPartner
  cases s.peerOpkPk? <;> cases r.opkPk? <;> rfl

theorem primBounded_recordKeyIndRespPrim (S : Setup) (r : KeyIndRespEntry S) (st : KeyIndState S) :
    PrimBounded ((recordKeyIndRespPrim S r).run st) (S.N_dh * 8) := by
  unfold recordKeyIndRespPrim
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    pure_bind, bind_assoc]
  have h_find :
      PrimBounded (findMPrim (fun s => keyIndPartnerPrim s r) (st.sessions.take S.N_dh)) (S.N_dh *
      8) :=
    primBounded_findMPrim_take _ 8 S.N_dh st.sessions (fun s => primBounded_keyIndPartnerPrim s r)
  refine primBounded_bind_le 0 h_find (fun found => ?_)
  cases found with
  | some s => exact primBounded_pure'
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
    exact primBounded_bind_le 0 (primBounded_embedUnif sampleDRKey96 0) (fun _ => primBounded_pure')

theorem simulateQ_recordKeyIndRespPrim (S : Setup) (P : Primitives)
    (r : KeyIndRespEntry S) (st : KeyIndState S)
    (hSess : st.sessions.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) ((recordKeyIndRespPrim S r).run st) =
      (recordKeyIndResp S P r).run st := by
  unfold recordKeyIndRespPrim recordKeyIndResp
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    pure_bind, bind_assoc, simulateQ_bind]
  rw [List.take_of_length_le hSess,
      simulateQ_findMPrim P _ (fun s => keyIndPartner P s r) (fun s => simulateQ_keyIndPartnerPrim P
          s r) st.sessions,
      pure_bind]
  cases st.sessions.find? (fun s => keyIndPartner P s r) with
  | some s => simp
  | none => simp [StateT.run_bind, StateT.run_monadLift, monadLift_self]

theorem primBounded_evalHkdfOrRoPrim (useRo : Bool) (roCache : List (Bytes × DRKey))
    (secrets : Bytes) :
    PrimBounded (evalHkdfOrRoPrim useRo roCache secrets) 1 := by
  unfold evalHkdfOrRoPrim
  cases useRo with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases roCache.find? (fun (inp, _) => inp == secrets) with
    | some p => exact primBounded_pure'
    | none => exact primBounded_bind_le 0 (primBounded_embedUnif sampleDRKey96 0) (fun _ =>
        primBounded_pure')

theorem simulateQ_evalHkdfOrRoPrim (useRo : Bool) (P : Primitives)
    (roCache : List (Bytes × DRKey)) (secrets : Bytes) :
    simulateQ (primBaseImpl P) (evalHkdfOrRoPrim useRo roCache secrets) =
      evalHkdfOrRo useRo P roCache secrets := by
  unfold evalHkdfOrRoPrim evalHkdfOrRo
  cases useRo with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases roCache.find? (fun (inp, _) => inp == secrets) with
    | some p => rfl
    | none => simp

theorem primBounded_acceptKeysPrim (inp : AcceptKeysInput) :
    PrimBounded (acceptKeysPrim inp) 7 := by
  unfold acceptKeysPrim
  refine primBounded_bind_le 6 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 4 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_acceptKeysPrim (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (inp : AcceptKeysInput) :
    simulateQ (primBaseImpl P) (acceptKeysPrim inp) = pure (Model.acceptKeys P inp) := by
  unfold acceptKeysPrim Model.acceptKeys
  change (pure _ : ProbComp (Option DRKey)) = pure _
  congr 1
  by_cases hct : inp.hdr.kemCt.length = kyberCtLen
  · have hbeq : (inp.hdr.kemCt.length == kyberCtLen) = true := beq_iff_eq.mpr hct
    rw [hbeq]
    cases inp.hdr.opkId? <;> cases inp.opkBSk? <;> cases P.kemDecaps inp.pqspkBSk inp.hdr.kemCt <;>
        rfl
  · have hbeq : (inp.hdr.kemCt.length == kyberCtLen) = false := beq_eq_false_iff_ne.mpr hct
    rw [hP.kemDecaps_len_reject inp.pqspkBSk inp.hdr.kemCt hct, hbeq]
    cases inp.hdr.opkId? <;> cases inp.opkBSk? <;> rfl

theorem primBounded_runKeyIndInitiatePrim (useRo : Bool) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    PrimBounded ((runKeyIndInitiatePrim useRo S sid u bundle).run st) (S.N_dh * 18 +
        S.N_sess_tot * 8 + 12) := by
  unfold runKeyIndInitiatePrim
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h_sid : st.sessions.any (fun e => e.sid == sid)
  · simp only [h_sid, ↓reduceIte]; exact primBounded_pure'
  · simp only [h_sid, Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact primBounded_pure'
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
      refine primBounded_bind_le (S.N_dh * 12 + S.N_sess_tot * 8 + 9)
        (primBounded_koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle)
            (fun koskOk => ?_)
      split_ifs
      · exact primBounded_pure'
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
        refine primBounded_bind_le (S.N_dh * 12 + S.N_sess_tot * 8 +
            9) (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
        refine primBounded_bind_le (S.N_dh * 12 + S.N_sess_tot * 8 +
            9) (primBounded_embedUnif sampleCoins32 0) (fun _ => ?_)
        refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
            9) (primBounded_resolveSigPkPrim S st.principals bundle.ikB) (fun _ => ?_)
        refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
            8) (primBounded_primQ _) (fun v1 => ?_)
        refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
            7) (primBounded_primQ _) (fun v2 => ?_)
        split_ifs
        · exact primBounded_pure'
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
          refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
              6) (primBounded_primQ _) (fun enc => ?_)
          rcases enc with ⟨enc, _⟩
          cases enc with
          | none => exact primBounded_pure'
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
            refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
                5) (primBounded_primQ _) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
                4) (primBounded_primQ _) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
                3) (primBounded_primQ _) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
                2) (primBounded_primQ _) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 10 + S.N_sess_tot * 8 +
                1) (primBounded_primQ _) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 10 +
                S.N_sess_tot * 8) (primBounded_evalHkdfOrRoPrim useRo st.roCache _) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 8 +
                S.N_sess_tot * 8) (primBounded_isHonestUncorruptedPeerPrim S st.principals
                bundle.ikB) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 2 +
                S.N_sess_tot * 8) (primBounded_checkBundleProvenancePrim S st.principals
                st.spkBundles st.opkEntries bundle) (fun _ => ?_)
            refine primBounded_bind_le (S.N_dh * 2)
              (primBounded_findMPrim_take _ 8 S.N_sess_tot st.respSessions (fun r =>
                  primBounded_keyIndPartnerPrim _ r))
              (fun found => ?_)
            cases found with
            | some r =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  pure_bind, bind_assoc]
              refine primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S st.principals
                  bundle.ikB) (fun hp => ?_)
              cases hp <;> exact primBounded_pure'
            | none =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  pure_bind, bind_assoc]
              refine primBounded_bind_le (S.N_dh * 2) (primBounded_embedUnif sampleDRKey96 0) (fun _
                  => ?_)
              refine primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S st.principals
                  bundle.ikB) (fun hp => ?_)
              cases hp <;> exact primBounded_pure'

@[simp] theorem simulateQ_primQ_x25519 (P : Primitives) (sk pk : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.x25519 sk pk)) =
      (pure (P.x25519 sk pk) : ProbComp (primSpec.Range (.x25519 sk pk))) := rfl
@[simp] theorem simulateQ_primQ_x25519Base (P : Primitives) (sk : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.x25519Base sk)) =
      (pure (P.x25519Base sk) : ProbComp (primSpec.Range (.x25519Base sk))) := rfl
@[simp] theorem simulateQ_primQ_pow8 (P : Primitives) (pk : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.pow8 pk)) =
      (pure (P.pow8 pk) : ProbComp (primSpec.Range (.pow8 pk))) := rfl
@[simp] theorem simulateQ_primQ_isCanonical (P : Primitives) (pk : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.isCanonical pk)) =
      (pure (P.isCanonical pk) : ProbComp (primSpec.Range (.isCanonical pk))) := rfl
@[simp] theorem simulateQ_primQ_sigVerify (P : Primitives) (pk msg sig : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.sigVerify pk msg sig)) =
      (pure (P.sigVerify pk msg sig) : ProbComp (primSpec.Range (.sigVerify pk msg sig))) := rfl
@[simp] theorem simulateQ_primQ_kemEncaps (P : Primitives) (ek m : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.kemEncaps ek m)) =
      (pure (P.kemEncaps ek m) : ProbComp (primSpec.Range (.kemEncaps ek m))) := rfl
@[simp] theorem simulateQ_primQ_kemDecaps (P : Primitives) (dk ct : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.kemDecaps dk ct)) =
      (pure (P.kemDecaps dk ct) : ProbComp (primSpec.Range (.kemDecaps dk ct))) := rfl
@[simp] theorem simulateQ_primQ_hkdfDerive96 (P : Primitives) (ikm : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.hkdfDerive96 ikm)) =
      (pure (P.hkdfDerive96 ikm) : ProbComp (primSpec.Range (.hkdfDerive96 ikm))) := rfl

theorem simulateQ_runKeyIndInitiatePrim (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S)
    (hPrin : st.principals.length ≤ S.N_dh)
    (hSpk : st.spkBundles.length ≤ S.N_dh)
    (hOpk : st.opkEntries.length ≤ S.N_dh)
    (hResp : st.respSessions.length ≤ S.N_sess_tot)
    (hAdv : ValidAdvKeysPow8 P st.advKeys) :
    simulateQ (primBaseImpl P) ((runKeyIndInitiatePrim useRo S sid u bundle).run st) =
      (runKeyIndInitiate useRo S P sid u bundle).run st := by
  unfold runKeyIndInitiatePrim runKeyIndInitiate
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h_sid : st.sessions.any (fun e => e.sid == sid)
  · simp only [h_sid, ↓reduceIte]; rfl
  · simp only [h_sid, Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rfl
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
        simulateQ_bind]
      rw [simulateQ_koskBundleOkPrim S P st.principals st.spkBundles st.opkEntries st.advKeys bundle
          hPrin hSpk hOpk hAdv,
          pure_bind]
      by_cases h_kosk :
          (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [h_kosk, ↓reduceIte]; rfl
      · simp only [h_kosk, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, pure_bind, bind_assoc, simulateQ_bind, simulateQ_embedUnif]
        congr 1; ext ekASk
        congr 1; ext kemCoins
        rw [simulateQ_resolveSigPkPrim S P st.principals bundle.ikB hPrin, pure_bind,
            simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
        split_ifs
        · rfl
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            simulateQ_bind, simulateQ_pure]
          rw [simulateQ_primQ_kemEncaps, pure_bind]
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => rfl
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
              simulateQ_bind]
            rw [simulateQ_primQ_x25519Base, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind]
            have h_dh4 :
                (bundle.opkB?.map (fun _ => P.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD [])))
                =
                bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk) := by
              cases bundle.opkB? <;> rfl
            rw [h_dh4, simulateQ_evalHkdfOrRoPrim]
            congr 1; ext ⟨drKeyReal, roCache'⟩
            rw [simulateQ_isHonestUncorruptedPeerPrim S P st.principals bundle.ikB hPrin, pure_bind,
                simulateQ_checkBundleProvenancePrim S P st.principals st.spkBundles st.opkEntries
                    bundle hPrin hSpk hOpk, pure_bind,
                List.take_of_length_le hResp,
                simulateQ_findMPrim P _ (fun r => keyIndPartner P _ r) (fun r =>
                    simulateQ_keyIndPartnerPrim P _ r) st.respSessions,
                pure_bind]
            unfold keyIndPartnerRandKey?
            cases st.respSessions.find? (fun r => keyIndPartner P _ r) with
            | some r =>
              dsimp only [Option.map]
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  pure_bind, simulateQ_bind]
              rw [simulateQ_findHonestPrincipalPrim S P st.principals bundle.ikB hPrin, pure_bind]
              cases findHonestPrincipal P st.principals bundle.ikB <;> rfl
            | none =>
              dsimp only [Option.map]
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  pure_bind, bind_assoc,
                simulateQ_bind, simulateQ_embedUnif]
              congr 1; ext drKeyRand
              rw [simulateQ_findHonestPrincipalPrim S P st.principals bundle.ikB hPrin, pure_bind]
              cases findHonestPrincipal P st.principals bundle.ikB <;> rfl

@[simp] theorem simulateQ_primQ_sigPkGen (P : Primitives) (sk : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.sigPkGen sk)) =
      (pure (P.sigPkGen sk) : ProbComp (primSpec.Range (.sigPkGen sk))) := rfl
@[simp] theorem simulateQ_primQ_sigSign (P : Primitives) (sk msg r : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.sigSign sk msg r)) =
      (pure (P.sigSign sk msg r) : ProbComp (primSpec.Range (.sigSign sk msg r))) := rfl
@[simp] theorem simulateQ_primQ_kemKeyGen (P : Primitives) (seed : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.kemKeyGen seed)) =
      (pure (P.kemKeyGen seed) : ProbComp (primSpec.Range (.kemKeyGen seed))) := rfl

def pqxdhKeyIndCachedImpl (useRo : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp) := fun q =>
  match q with
  | .registerKey sk => do
    let st ← get
    if sk.length != 32 then return .noneResp
    let pk := P.x25519Base sk
    set { st with advKeys := (P.pow8 pk, pk) :: st.advKeys }
    return .pkResp pk
  | q_other => pqxdhKeyIndImpl useRo S P q_other

theorem primBounded_pqxdhKeyIndImplPrim (useRo : Bool) (S : Setup)
    (q : KeyIndQuery S) (st : KeyIndState S) :
    PrimBounded ((pqxdhKeyIndImplPrim useRo S q).run st) (S.N_dh * 18 + S.N_sess_tot * 8 + 14) := by
  unfold pqxdhKeyIndImplPrim
  cases q with
  | initPrin u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind,
        bind_assoc]
      refine primBounded_bind_le 2 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | corruptIK u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) <;> exact primBounded_pure'
  | genSPK u j =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact primBounded_pure'
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            pure_bind, bind_assoc]
        refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
        refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
        refine primBounded_bind_le 3 (primBounded_embedUnif sampleRandom64 0) (fun _ => ?_)
        refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
        refine primBounded_bind_le 1 primBounded_sampleKemKeyGenPrim (fun _ => ?_)
        refine primBounded_bind_le 1 (primBounded_embedUnif sampleRandom64 0) (fun _ => ?_)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | genOPK u j o =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind,
        bind_assoc]
      refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | initiateOPK u i bundle =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · exact (primBounded_runKeyIndInitiatePrim useRo S (.sendOPK u i) u bundle st).mono (by omega)
  | initiateNoOPK u i bundle =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · exact (primBounded_runKeyIndInitiatePrim useRo S (.sendNoOPK u i) u bundle st).mono (by omega)
  | acceptOPK k j o hdr =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · exact primBounded_pure'
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
      refine primBounded_bind_le (S.N_dh * 12 + 13)
        (primBounded_koskSenderOkPrim S st.principals st.advKeys hdr.ikAPk) (fun koskOk => ?_)
      split_ifs
      · exact primBounded_pure'
      · cases st.principals.find? (fun (idx, _) => idx == k.val) with
        | none => exact primBounded_pure'
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          dsimp only
          cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => exact primBounded_pure'
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => exact primBounded_pure'
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              split_ifs
              · exact primBounded_pure'
              · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
                refine primBounded_bind_le (S.N_dh * 12 +
                    6) (primBounded_acceptKeysPrim _) (fun acc => ?_)
                rcases acc with ⟨acc, _⟩
                cases acc with
                | none => exact primBounded_pure'
                | some _ =>
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
                  refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_primQ _) (fun dec => ?_)
                  rcases dec with ⟨dec, _⟩
                  cases dec with
                  | none => exact primBounded_pure'
                  | some ss =>
                    dsimp only
                    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                        StateT.run_set, pure_bind, bind_assoc]
                    refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _) (fun _ => ?_)
                    refine primBounded_bind_le (S.N_dh * 12 + 3) (primBounded_primQ _) (fun _ => ?_)
                    refine primBounded_bind_le (S.N_dh * 12 + 2) (primBounded_primQ _) (fun _ => ?_)
                    refine primBounded_bind_le (S.N_dh * 12 + 1) (primBounded_primQ _) (fun _ => ?_)
                    refine primBounded_bind_le (S.N_dh * 12) (primBounded_evalHkdfOrRoPrim useRo
                        st.roCache _) (fun _ => ?_)
                    refine primBounded_bind_le (S.N_dh * 10) (primBounded_findHonestPrincipalPrim S
                        st.principals hdr.ikAPk) (fun _ => ?_)
                    refine primBounded_bind_le (S.N_dh * 2) (primBounded_recordKeyIndRespPrim S _ _)
                        (fun _ => ?_)
                    refine primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S _ hdr.ikAPk)
                        (fun hp => ?_)
                    cases hp <;> exact primBounded_pure'
  | acceptNoOPK k j l hdr =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · exact primBounded_pure'
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
      refine primBounded_bind_le (S.N_dh * 12 + 12)
        (primBounded_koskSenderOkPrim S st.principals st.advKeys hdr.ikAPk) (fun koskOk => ?_)
      split_ifs
      · exact primBounded_pure'
      · cases st.principals.find? (fun (idx, _) => idx == k.val) with
        | none => exact primBounded_pure'
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          dsimp only
          cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => exact primBounded_pure'
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
            refine primBounded_bind_le (S.N_dh * 12 +
                5) (primBounded_acceptKeysPrim _) (fun acc => ?_)
            rcases acc with ⟨acc, _⟩
            cases acc with
            | none => exact primBounded_pure'
            | some _ =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
              refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _) (fun dec => ?_)
              rcases dec with ⟨dec, _⟩
              cases dec with
              | none => exact primBounded_pure'
              | some ss =>
                dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    pure_bind, bind_assoc]
                refine primBounded_bind_le (S.N_dh * 12 + 3) (primBounded_primQ _) (fun _ => ?_)
                refine primBounded_bind_le (S.N_dh * 12 + 2) (primBounded_primQ _) (fun _ => ?_)
                refine primBounded_bind_le (S.N_dh * 12 + 1) (primBounded_primQ _) (fun _ => ?_)
                refine primBounded_bind_le (S.N_dh * 12) (primBounded_evalHkdfOrRoPrim useRo
                    st.roCache _) (fun _ => ?_)
                refine primBounded_bind_le (S.N_dh * 10) (primBounded_findHonestPrincipalPrim S
                    st.principals hdr.ikAPk) (fun _ => ?_)
                refine primBounded_bind_le (S.N_dh * 2) (primBounded_recordKeyIndRespPrim S _ _)
                    (fun _ => ?_)
                refine primBounded_bind_le 0 (primBounded_findHonestPrincipalPrim S _ hdr.ikAPk)
                    (fun hp => ?_)
                cases hp <;> exact primBounded_pure'
  | testSession sid =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h_fresh : !isKeyIndSessionTestable st sid
    · simp only [h_fresh, ↓reduceIte]; exact primBounded_pure'
    · simp only [h_fresh, Bool.false_eq_true, ↓reduceIte]
      cases st.sessions.find? (fun e => e.sid == sid) with
      | some e => exact primBounded_pure'
      | none =>
        cases st.respSessions.find? (fun r => r.sid == sid) <;> exact primBounded_pure'
  | revealSessionKey sid =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      split_ifs <;> exact primBounded_pure'
    | none =>
      cases st.respSessions.find? (fun r => r.sid == sid) with
      | none => exact primBounded_pure'
      | some r =>
        dsimp only
        split_ifs <;> exact primBounded_pure'
  | roQuery secrets =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind,
        bind_assoc]
      exact primBounded_bind_le 0 (primBounded_evalHkdfOrRoPrim true st.roCache secrets) (fun _ =>
          primBounded_pure')
  | revealDhSecrets =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> exact primBounded_pure'
  | registerKey sk =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact primBounded_pure'
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, pure_bind,
        bind_assoc]
      refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | revealSpkSk u j =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;> exact primBounded_pure'

theorem simulateQ_pqxdhKeyIndImplPrim (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (hPrin : st.principals.length ≤ S.N_dh)
    (hSpk : st.spkBundles.length ≤ S.N_dh)
    (hOpk : st.opkEntries.length ≤ S.N_dh)
    (hSess : st.sessions.length ≤ S.N_dh)
    (hResp : st.respSessions.length ≤ S.N_sess_tot)
    (hAdv : ValidAdvKeysPow8 P st.advKeys) :
    simulateQ (primBaseImpl P) ((pqxdhKeyIndImplPrim useRo S q).run st) =
      (pqxdhKeyIndCachedImpl useRo S P q).run st := by
  unfold pqxdhKeyIndImplPrim pqxdhKeyIndCachedImpl pqxdhKeyIndImpl
  cases q with
  | initPrin u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        simulateQ_embedUnif]
      congr 1
  | corruptIK u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
  | genSPK u j =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
          simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim]
        congr 1
  | genOPK u j o =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        simulateQ_embedUnif]
      congr 1
  | initiateOPK u i bundle =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · exact simulateQ_runKeyIndInitiatePrim useRo S P (.sendOPK u i) u bundle st hPrin hSpk hOpk
        hResp hAdv
  | initiateNoOPK u i bundle =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · exact simulateQ_runKeyIndInitiatePrim useRo S P (.sendNoOPK u i) u bundle st hPrin hSpk hOpk
        hResp hAdv
  | acceptOPK k j o hdr =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with h1 h2 h3
    · rfl
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
        simulateQ_bind]
      rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys hdr.ikAPk hPrin hAdv, pure_bind]
      simp [h3]
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
        simulateQ_bind]
      rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys hdr.ikAPk hPrin hAdv, pure_bind]
      have h3F : (!koskSenderOk P st.principals st.advKeys hdr.ikAPk) = false :=
          Bool.eq_false_iff.mpr h3
      simp only [h3F, Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == k.val) with
      | none => rfl
      | some kp =>
        rcases kp with ⟨_, kEntry⟩
        dsimp only
        cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => rfl
        | some bp =>
          rcases bp with ⟨_, bEntry⟩
          dsimp only
          cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => rfl
          | some op =>
            rcases op with ⟨_, oEntry⟩
            dsimp only
            split_ifs
            · rfl
            · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                simulateQ_bind, simulateQ_pure, simulateQ_acceptKeysPrim P hP, pure_bind]
              cases Model.acceptKeys P _ with
              | none => rfl
              | some _ =>
                dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  simulateQ_bind, simulateQ_pure]
                rw [simulateQ_primQ_kemDecaps, pure_bind]
                cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none => rfl
                | some ss =>
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    pure_bind, bind_assoc, simulateQ_bind]
                  rw [simulateQ_primQ_x25519, pure_bind,
                      simulateQ_primQ_x25519, pure_bind,
                      simulateQ_primQ_x25519, pure_bind,
                      simulateQ_primQ_x25519, pure_bind,
                      simulateQ_evalHkdfOrRoPrim]
                  congr 1; ext ⟨drKey, roCache'⟩
                  rw [simulateQ_findHonestPrincipalPrim S P st.principals hdr.ikAPk hPrin,
                      pure_bind,
                      simulateQ_recordKeyIndRespPrim S P _ _ (by exact hSess)]
                  congr 1; ext ⟨_, st2⟩
                  rw [pure_bind]
                  cases findHonestPrincipal P st.principals hdr.ikAPk <;> rfl
  | acceptNoOPK k j l hdr =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with h1 h2 h3
    · rfl
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
        simulateQ_bind]
      rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys hdr.ikAPk hPrin hAdv, pure_bind]
      simp [h3]
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
        simulateQ_bind]
      rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys hdr.ikAPk hPrin hAdv, pure_bind]
      have h3F : (!koskSenderOk P st.principals st.advKeys hdr.ikAPk) = false :=
          Bool.eq_false_iff.mpr h3
      simp only [h3F, Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == k.val) with
      | none => rfl
      | some kp =>
        rcases kp with ⟨_, kEntry⟩
        dsimp only
        cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => rfl
        | some bp =>
          rcases bp with ⟨_, bEntry⟩
          dsimp only
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            simulateQ_bind, simulateQ_pure, simulateQ_acceptKeysPrim P hP, pure_bind]
          cases Model.acceptKeys P _ with
          | none => rfl
          | some _ =>
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
              simulateQ_bind, simulateQ_pure]
            rw [simulateQ_primQ_kemDecaps, pure_bind]
            cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
            | none => rfl
            | some ss =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                pure_bind, bind_assoc, simulateQ_bind]
              rw [simulateQ_primQ_x25519, pure_bind,
                  simulateQ_primQ_x25519, pure_bind,
                  simulateQ_primQ_x25519, pure_bind,
                  simulateQ_evalHkdfOrRoPrim]
              congr 1; ext ⟨drKey, roCache'⟩
              rw [simulateQ_findHonestPrincipalPrim S P st.principals hdr.ikAPk hPrin, pure_bind,
                  simulateQ_recordKeyIndRespPrim S P _ _ (by exact hSess)]
              congr 1; ext ⟨_, st2⟩
              rw [pure_bind]
              cases findHonestPrincipal P st.principals hdr.ikAPk <;> rfl
  | testSession sid =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h_fresh : !isKeyIndSessionTestable st sid
    · simp only [h_fresh, ↓reduceIte]; rfl
    · simp only [h_fresh, Bool.false_eq_true, ↓reduceIte]
      cases st.sessions.find? (fun e => e.sid == sid) with
      | some e => rfl
      | none =>
        cases st.respSessions.find? (fun r => r.sid == sid) <;> rfl
  | revealSessionKey sid =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      split_ifs <;> rfl
    | none =>
      cases st.respSessions.find? (fun r => r.sid == sid) with
      | none => rfl
      | some r =>
        dsimp only
        split_ifs <;> rfl
  | roQuery secrets =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        pure_bind, bind_assoc, simulateQ_bind, simulateQ_evalHkdfOrRoPrim]
      rfl
  | revealDhSecrets =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> rfl
  | registerKey sk =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · rfl
  | revealSpkSk u j =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;> rfl

theorem le_probExpect_const_of_support {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, c ≤ f x) :
    c ≤ probExpect mx f := by
  calc c = probExpect mx (fun _ => c) := (probExpect_const mx c).symm
    _ ≤ probExpect mx f := probExpect_mono_of_support mx (fun _ => c) f h

theorem probExpect_eq_zero_of_support {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞)
    (h : ∀ x ∈ support mx, f x = 0) :
    probExpect mx f = 0 :=
  le_antisymm (probExpect_const_le_of_support mx f 0 (fun x hx => le_of_eq (h x hx))) bot_le

def noPrinPkColl (P : Primitives) (principals : List (Nat × PrincipalEntry)) : Bool :=
  !hasDuplicateBytes (principals.map (fun (_, e) => P.pow8 e.ikAPk))

theorem findHonestPrincipal_eq_some_of_noPrinPkColl (P : Primitives) :
    ∀ (principals : List (Nat × PrincipalEntry)) (k : Nat) (e : PrincipalEntry) (ikB : Bytes),
      noPrinPkColl P principals = true →
      (k, e) ∈ principals →
      P.pow8 e.ikAPk = P.pow8 ikB →
      findHonestPrincipal P principals ikB = some (k, e)
  | [], _, _, _, _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | (u, hd) :: tl, k, e, ikB, hnp, hmem, heq => by
    unfold noPrinPkColl at hnp
    simp only [List.map_cons, hasDuplicateBytes, Bool.not_or, Bool.and_eq_true,
      Bool.not_eq_true'] at hnp
    rcases hnp with ⟨hnot_in, hnp_tl⟩
    rcases List.mem_cons.mp hmem with hhead | htl
    · cases hhead
      unfold findHonestPrincipal
      simp [List.find?, heq]
    · have hne : (P.pow8 ikB == P.pow8 hd.ikAPk) = false := by
        rw [beq_eq_false_iff_ne]
        intro hcoll
        have hmem_map : P.pow8 hd.ikAPk ∈ List.map (fun x => P.pow8 x.2.ikAPk) tl := by
          rw [← hcoll, ← heq, List.mem_map]
          exact ⟨(k, e), htl, rfl⟩
        have hcont : List.contains (List.map (fun x => P.pow8 x.2.ikAPk) tl) (P.pow8 hd.ikAPk) =
            true :=
          List.contains_iff_mem.mpr hmem_map
        rw [hnot_in] at hcont
        cases hcont
      unfold findHonestPrincipal at *
      simp only [List.find?, hne]
      exact findHonestPrincipal_eq_some_of_noPrinPkColl P tl k e ikB
        (by simp [noPrinPkColl, hnp_tl]) htl heq

end SignalPqxdh.Security
