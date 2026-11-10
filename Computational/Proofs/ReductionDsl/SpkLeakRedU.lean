/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkLeakRedModel
public import Computational.Proofs.SpecLemmas.Reductions.E2E.CostedTables
public import Computational.Proofs.ReductionDsl.Soundness
public import Computational.Specifications.Session.StatementSpkModel
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.ReductionDsl.Size

/-!
# Costed `spkLeakRedU` Reduction

Defines `spkLeakRedUProg`, the `ReductionDsl.CostedReduction` implementation of the hop-3 wrapper
reduction `spkLeakRedU`, and proves its evaluation agreement, query, cost, size, and `GRedBounded`
bounds.
-/

@[expose] public section

namespace CryptoVerification.E2E.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.PRF.Costed
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E

variable {Pt : Type}

/-- Costed hop-3 wrapper reduction `spkLeakRedU` that samples a uniform `BitVec 256` scalar for the
inner PRF reduction and forwards PRF oracle queries unchanged. -/
def spkLeakRedUProg :
    CostedReduction
      (prfConstantInputOps (S := prfSig Pt (BitVec 256)) (.base .inp) Empty.elim)
      ((prfIface (S := prfSig Pt (BitVec 256)) (.base .inp) (.base .tag)).withSamp
        (unifSamplers (S := prfSig Pt (BitVec 256)) (fun _ : Unit => PrfSort.tag) (fun _ => 1)))
      (MACScheme.prfSpec Pt (BitVec 256))
      (prfCodec (S := prfSig Pt (BitVec 256)) (.base .inp) (.base .tag))
      .unit (.base .tag) .bool .bool where
  σ := .unit
  init :=
    let I := (prfIface (S := prfSig Pt (BitVec 256)) (.base .inp) (.base .tag)).withSamp
      (unifSamplers (S := prfSig Pt (BitVec 256)) (fun _ : Unit => PrfSort.tag) (fun _ => 1))
    rdsl [_] do
      x ← sample (I := I) (Sum.inr (UniformSamplerTag.base ())) ()
      return (x, ())
  handle :=
    rdsl [_, q] do
      r ← query () q
      return (r, ())
  finish := rdsl [_, guess] do return guess

@[simp] private theorem env_get_cons_zero {S : Sig} {Γ : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get Var.zero = x := rfl

@[simp] private theorem env_get_cons_succ {S : Sig} {Γ : List (Ty S)} {t u : Ty S}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

theorem spkLeakRedUOps_sizeHonest :
    OpsSizeHonest (prfConstantInputOps (S := prfSig Pt (BitVec 256)) (.base .inp) Empty.elim) :=
  fun o => o.elim

theorem spkLeakRedUSamp_sizeHonest :
    SampSizeHonest
      (unifSamplers (S := prfSig Pt (BitVec 256)) (fun _ : Unit => PrfSort.tag) (fun _ => 1)) := by
  intro s x B₀ hx y hy
  cases s with
  | bool => trivial
  | index N =>
    simp only [unifSamplers, sampleIndex] at hy
    split_ifs at hy with h
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
      obtain ⟨z, -, rfl⟩ := hy
      have hb := bits_mono (Nat.le_of_lt z.isLt)
      simp only [Ty.Fits]; omega
    · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      have h0 : bits 0 = 1 := rfl
      simp only [Ty.Fits]; omega
  | base u =>
    cases u
    simp only [Ty.Fits]; omega

theorem spkLeakRedUProg_impl :
    (spkLeakRedUProg (Pt := Pt)).impl =
      fun t => StateT.lift (liftM ((unifSpec + MACScheme.prfSpec Pt (BitVec 256)).query t)) := by
  funext t
  rcases t with n | q
  all_goals (apply StateT.ext; intro (s : Unit))
  · simp [CostedReduction.impl, handlerImpl, spkLeakRedUProg, prfIface, Iface.withSamp,
      StateT.run_lift, map_eq_bind_pure_comp, OracleSpec.query]
  · simp [CostedReduction.impl, handlerImpl, spkLeakRedUProg, prfCodec, prfIface, Iface.withSamp,
      Comp.eval, Expr.eval, Expr.v0, Expr.v1, StateT.run_lift, map_eq_bind_pure_comp,
      OracleSpec.query]

theorem spkLeakRedUProg_impl_run
    (t : (unifSpec + MACScheme.prfSpec Pt (BitVec 256)).Domain)
    (s : (spkLeakRedUProg (Pt := Pt)).σ.denote) :
    ((spkLeakRedUProg (Pt := Pt)).impl t).run s =
      (fun u => (u, s)) <$> liftM ((unifSpec + MACScheme.prfSpec Pt (BitVec 256)).query t) := by
  rw [spkLeakRedUProg_impl]
  simp [StateT.run_lift, map_eq_bind_pure_comp]

private theorem simulateQ_run_StateT_of_step {κ : Type} {spec : OracleSpec κ} {m : Type → Type}
    [Monad m] [LawfulMonad m] {σ α : Type}
    {impl : QueryImpl spec (StateT σ m)} {qi : QueryImpl spec m}
    (hstep : ∀ t s, (impl t).run s = (fun x => (x, s)) <$> qi t)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run s = (fun x => (x, s)) <$> simulateQ qi oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind]
    change ((impl t).run s >>= fun p => (simulateQ impl (mx p.1)).run p.2) =
      (fun x => (x, s)) <$> (qi t >>= fun u => simulateQ qi (mx u))
    rw [hstep, bind_map_left, map_bind]
    exact bind_congr fun u => ih u s

@[simp] private theorem simulateQ_query_id {κ : Type} {spec : OracleSpec κ} {α : Type}
    (oa : OracleComp spec α) :
    simulateQ (fun t => (liftM (spec.query t) : OracleComp spec (spec.Range t))) oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind]
    exact bind_congr ih

/-- Evaluating `spkLeakRedUProg` on the curried inner reduction agrees with `spkLeakRedU`. -/
theorem spkLeakRedUProg_eval {ℓ : ℕ} {PQC : Type} (D : SpkLeakRed Pt ℓ PQC) (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    (spkLeakRedUProg (Pt := Pt)).eval (fun x => D P Dh encPt encT decT qep x A) () =
      spkLeakRedU D P Dh encPt encT decT qep A := by
  simp only [CostedReduction.eval, spkLeakRedU,
    simulateQ_run_StateT_of_step (spkLeakRedUProg_impl_run (Pt := Pt))]
  simp [spkLeakRedUProg, Iface.withSamp, Samplers.sum, unifSamplers,
    Comp.eval, Expr.eval, Expr.v0, Expr.v1, bind_map_left]
  rfl

theorem spkLeakRedUProg_totalCost (q : ℕ) :
    (spkLeakRedUProg (Pt := Pt)).totalCost q = q * 8 + 9 := by
  simp [CostedReduction.totalCost, spkLeakRedUProg, prfCodec, prfIface, Iface.withSamp, Samplers.sum,
    unifSamplers, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem spkLeakRedUProg_size :
    (spkLeakRedUProg (Pt := Pt)).size = 16 := by
  simp [CostedReduction.size, spkLeakRedUProg, Comp.size, Expr.size, Expr.v0, Expr.v1]

theorem spkLeakRedUProg_size_le :
    (spkLeakRedUProg (Pt := Pt)).size ≤ reductionSizeBudget := by
  rw [spkLeakRedUProg_size]
  simp only [reductionSizeBudget]
  omega

theorem spkLeakRedUProg_queries (q : ℕ) :
    (spkLeakRedUProg (Pt := Pt)).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, spkLeakRedUProg, Comp.queries]

theorem spkLeakRedUProg_totalCost_le_budget (q : ℕ) :
    (spkLeakRedUProg (Pt := Pt)).totalCost (q + 1) ≤ spkLeakRedUBudget q := by
  rw [spkLeakRedUProg_totalCost]
  unfold spkLeakRedUBudget
  omega

/-- `spkLeakRedUProg` satisfies `GRedBounded` at query bound `q + 1` and cost budget
`spkLeakRedUBudget q`. -/
theorem spkLeakRedUProg_gRedBounded_tight (q : ℕ) :
    CryptoVerification.LibsignalSession.GRedBounded (spkLeakRedUProg (Pt := Pt))
      (fun _ => 1) (fun _ => 0) (q + 1) (q + 1) (spkLeakRedUBudget q) := by
  refine gRedBounded_of_bounds_const _ (fun _ => 1) (fun _ => 0) (q + 1) (q + 1)
    (spkLeakRedUBudget q) (spkLeakRedUProg_totalCost_le_budget q) spkLeakRedUProg_size_le ?_
    spkLeakRedUOps_sizeHonest
    (SampSizeHonest.sum SampSizeHonest.empty spkLeakRedUSamp_sizeHonest)
  rw [spkLeakRedUProg_queries]

end CryptoVerification.E2E.Costed
