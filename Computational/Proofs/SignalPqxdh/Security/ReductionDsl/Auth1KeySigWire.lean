/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigStepBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigEvalEq
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigSessionSplit
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeySigSigBound
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
import Computational.Proofs.ReductionDsl.Size

/-!
# One-Key `Auth` `GapSigEufCma` `ReductionDsl` Adversary Wiring

**Checked by Lean.** Defines `sigAuth1KeyDslAdv` from `sigAuth1KeyDslProg` and proves that it
equals the shallow reduction `sigReductionAuth1Key` with identical `GapSigEufCma` advantage and
`Bounded` compliance. Also establishes static step-cost, query-count, program-size, and output
block-size bounds for `sigAuth1KeyDslProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open Proofs.SignalPqxdh.Security
open OracleSpec OracleComp

/-- The context-generic `a1gStepC` bounds consumed by the sig program bounds. -/
structure A1gStepBounds (S : Setup) (K : Nat) : Prop where
  cost : A1gStepCostUB S K (80000 + 30000 * K + 10000 * S.N_dh)
  sig  : A1gStepQueries S K SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight 2
  ddh  : A1gStepQueries S K SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (5 * K)
  prim : A1gStepQueries S K SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight (174 + S.N_dh * 30)

/-- The `ReductionDsl` one-key `Auth` `GapSigEufCma` adversary (definitionally `(R.eval).sig b A`
    whenever `R.sig b = sigAuth1KeyDslProg S b`). -/
def sigAuth1KeyDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapSigEufCmaAdv where
  run pk := (sigAuth1KeyDslProg S b).eval (fun _ => A.1.run) pk
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := authGdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

/-- The DSL adversary equals the shallow `sigReductionAuth1Key`. -/
theorem sigAuth1KeyDslAdv_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    sigAuth1KeyDslAdv S b A = sigReductionAuth1Key S b A := by
  unfold sigAuth1KeyDslAdv sigReductionAuth1Key
  congr 1
  funext pk
  exact sigAuth1KeyProg_eval_eq S b A pk

theorem GapSigEufCma_sigAuth1KeyDslAdv (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    GapSigEufCma P isValidDhTriple (sigAuth1KeyDslAdv S b A) =
      GapSigEufCma P isValidDhTriple (sigReductionAuth1Key S b A) := by
  rw [sigAuth1KeyDslAdv_eq]

theorem sigAuth1Key_sig_le (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    GapSigEufCma P isValidDhTriple (sigReductionAuth1Key S b A) ≤
      GapSigEufCma P isValidDhTriple (sigAuth1KeyDslAdv S b A) :=
  (GapSigEufCma_sigAuth1KeyDslAdv P isValidDhTriple S b A).ge

theorem sigAuth1KeyDslProg_totalCost_le_of (S : Setup) (b : QueryBudget)
    (hG : A1gStepBounds S b.q_total) :
    (sigAuth1KeyDslProg S b).totalCost b.q_total ≤
      SignalPqxdh.LegacyCosted.stepCostBudget S b :=
  sigAuth1KeyProg_totalCost_le_of S b hG.cost

theorem sigAuth1KeyDslProg_totalSigQueries_le_of (S : Setup) (b : QueryBudget)
    (hG : A1gStepBounds S b.q_total) :
    (sigAuth1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total :=
  sigAuth1KeyProg_totalSigQueries_le_of S b hG.sig

theorem sigAuth1KeyDslProg_totalDdhQueries_le_of (S : Setup) (b : QueryBudget)
    (hG : A1gStepBounds S b.q_total) :
    (sigAuth1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
        5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  sigAuth1KeyProg_totalDdhQueries_le_of S b hG.ddh

theorem sigAuth1KeyDslProg_totalPrimQueries_le_of (S : Setup) (b : QueryBudget)
    (hG : A1gStepBounds S b.q_total) :
    (sigAuth1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b :=
  sigAuth1KeyProg_totalPrimQueries_le_of S b hG.prim

private theorem a1s_valFits_iff_fits {S : Sig} (B : ℕ) :
    ∀ (t : Ty S) (x : t.denote), ValFits B t x ↔ t.Fits B x
  | .base _, _ => Iff.rfl
  | .unit, _ => Iff.rfl
  | .bool, _ => Iff.rfl
  | .nat, _ => Iff.rfl
  | .opt _, none => Iff.rfl
  | .opt t, some a => a1s_valFits_iff_fits B t a
  | .prod t u, x => and_congr (a1s_valFits_iff_fits B t x.1) (a1s_valFits_iff_fits B u x.2)
  | .sum t _, .inl a => a1s_valFits_iff_fits B t a
  | .sum _ u, .inr b => a1s_valFits_iff_fits B u b
  | .list t, _ => and_congr Iff.rfl
      (forall_congr' fun x => imp_congr_right fun _ => a1s_valFits_iff_fits B t x)
  | .tbl t, m => forall_congr' fun i => a1s_valFits_iff_fits B t (m i)

private theorem a1s_one_le_pqSamplers_sCost (s : PSamp) : 1 ≤ pqSamplers.sCost s := by
  cases s <;> simp [pqSamplers, PSamp.cost]

private theorem a1s_one_le_pqChalIface_qCost {C : ChallengerOracle} (g : (pqChalIface C).Tag) :
    1 ≤ (pqChalIface C).qCost g := by
  cases g <;> simp only [pqChalIface, ChallengerOracle.qCost] <;> omega

private theorem a1s_comp_nq_le_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps I Γ t) : c.nq ≤ c.cost := by
  induction c with
  | ret _ => simp [Comp.nq, Comp.queries, Comp.cost]
  | bind c k ihc ihk => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | ite _ c d ihc ihd => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseOpt _ n s ihn ihs => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseSum _ l r ihl ihr => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | sample s _ => have := hs s; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | query g _ => have := hq g; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | iter n _ body ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) body ≤ body.cost + 1 := by omega
    have := Nat.mul_le_mul_left n h1
    omega
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | foldM K _ _ p ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega
  | consumeFirstM K _ p mk ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + mk.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega

private theorem a1s_gred_nq_le_totalCost {ι κ : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn aIn aOut out : Ty pqSig}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    (R : CostedReduction pqxdhOps I G C rIn aIn aOut out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hI := a1s_comp_nq_le_cost hq hs R.init
  have hH := a1s_comp_nq_le_cost hq hs R.handle
  have hF := a1s_comp_nq_le_cost hq hs R.finish
  have hMax : R.handle.nq ≤ max I.uCost (R.handle.cost + C.codecCost) :=
    le_trans hH (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left q hMax
  dsimp only [CostedReduction.nq, CostedReduction.totalQueries, CostedReduction.totalCost,
    Comp.nq] at *
  omega

theorem sigAuth1KeyDslProg_blocks_of (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (hG : A1gStepBounds S b.q_total) :
    SignalPqxdh.LegacyCosted.GRedBlockBounded S b ℓ (sigAuth1KeyDslProg S b) := by
  intro hq henc A hA x hx y hy
  rw [a1s_valFits_iff_fits]
  have hq' : ∀ g x u, (pqSigAndDdhIface.cod g).Fits ℓ (pqSigAndDdhIface.dec g x u) := fun g x u =>
    (a1s_valFits_iff_fits ℓ _ _).1 (hq g x u)
  have henc' : ∀ t, (authCodec S).Q.Fits ℓ ((authCodec S).qenc t) := fun t =>
    (a1s_valFits_iff_fits ℓ _ _).1 (henc t)
  have hx' : (B 32).Fits ℓ x := (a1s_valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (sigAuth1KeyDslProg S b).fits_eval
    pqO_sizeHonest SignalPqxdh.LegacyCosted.pqSamplers_sizeHonest ℓ hq' ℓ henc' 0 (fun _ => trivial)
    A b.q_total ℓ hA' x hx' y hy
  have hCost := sigAuth1KeyDslProg_totalCost_le_of S b hG
  have hNq := le_trans
    (a1s_gred_nq_le_totalCost a1s_one_le_pqChalIface_qCost a1s_one_le_pqSamplers_sCost
      (sigAuth1KeyDslProg S b) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (Ty.prod (B 1569) (B 64)) y hEval
  unfold SignalPqxdh.LegacyCosted.outputSizeBudget SignalPqxdh.LegacyCosted.stepCostBudget at *
  have hM := Nat.mul_le_mul_right ℓ hNq
  nlinarith

private theorem isQueryBoundP_sigReductionAuth1Key_ddh (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (hG : A1gStepBounds S b.q_total) (pk : Bytes) :
    ((sigAuth1KeyDslProg S b).eval (fun _ => A.1.run) pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (authGdhQueryBudget S b) := by
  let B_quad := (4 * min b.q_ro b.q_total + min b.q_roRoot b.q_total) *
      min (min b.q_on b.q_total) S.N_sess_tot +
    3 * min (min b.q_on b.q_total) S.N_sess_tot *
      (min (min b.q_on b.q_total) S.N_sess_tot - 1)
  by_cases hLe : 5 * b.q_total ^ 2 ≤ B_quad
  · refine (sigAuth1KeyProg_ddhBounded S b.q_total b.q_total (fun _ => A.1.run)
        (authAdv_gameBound S b A) pk).mono
      (le_trans (sigAuth1KeyDslProg_totalDdhQueries_le_of S b hG) ?_)
    unfold authGdhQueryBudget; dsimp only [B_quad] at hLe ⊢; rw [Nat.min_eq_left hLe]
  · have hMin : min (5 * b.q_total ^ 2) B_quad = B_quad := Nat.min_eq_right (Nat.le_of_not_le hLe)
    rw [sigAuth1KeyProg_eval_eq S b A pk]
    refine (isQueryBoundP_sigReductionAuth1Key_ddh_shallow S b A pk).mono ?_
    unfold authGdhQueryBudget; dsimp only [B_quad] at hMin ⊢; rw [hMin]; omega

theorem sigAuth1KeyDslAdv_bounded_of (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (hG : A1gStepBounds S b.q_total) :
    (sigAuth1KeyDslAdv S b A).Bounded := by
  refine ⟨fun pk => ?_, fun pk => ?_, fun pk => ?_⟩
  · dsimp only [sigAuth1KeyDslAdv]
    rw [sigAuth1KeyProg_eval_eq S b A pk]
    exact isQueryBoundP_sigReductionAuth1Key_sig S b A pk
  · exact isQueryBoundP_sigReductionAuth1Key_ddh S b A hG pk
  · exact sigAuth1KeyProg_primBounded_gdhPrimQueryBudget S b.q_total b A pk

theorem sigReductionAuth1Key_bounded_of (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (hG : A1gStepBounds S b.q_total) :
    (sigReductionAuth1Key S b A).Bounded := by
  rw [← sigAuth1KeyDslAdv_eq]
  exact sigAuth1KeyDslAdv_bounded_of S b A hG

theorem a1gStepBounds (S : Setup) (K : Nat) : A1gStepBounds S K where
  cost := fun st q => a1gStepC_costUB_le S K st q
  sig  := fun st q => a1gStepC_queries_sig_le S K st q
  ddh  := fun st q => a1gStepC_queries_ddh_le S K st q
  prim := fun st q => a1gStepC_queries_prim_le S K st q

theorem sigAuth1KeyDslProg_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total :=
  sigAuth1KeyDslProg_totalSigQueries_le_of S b (a1gStepBounds S b.q_total)

theorem sigAuth1KeyDslProg_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
        5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  sigAuth1KeyDslProg_totalDdhQueries_le_of S b (a1gStepBounds S b.q_total)

theorem sigAuth1KeyDslProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b :=
  sigAuth1KeyDslProg_totalPrimQueries_le_of S b (a1gStepBounds S b.q_total)

/-- Legacy output block-size bound for `sigAuth1KeyDslProg`. -/
theorem sigAuth1KeyDslProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    SignalPqxdh.LegacyCosted.GRedBlockBounded S b ℓ (sigAuth1KeyDslProg S b) :=
  sigAuth1KeyDslProg_blocks_of S b ℓ (a1gStepBounds S b.q_total)

/-- `sigAuth1KeyDslAdv` satisfies its declared `GapSigEufCmaAdv` query budgets. -/
theorem sigAuth1KeyDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : (sigAuth1KeyDslAdv S b A).Bounded :=
  sigAuth1KeyDslAdv_bounded_of S b A (a1gStepBounds S b.q_total)

/-- The shallow reduction `sigReductionAuth1Key` satisfies its declared query budgets. -/
theorem sigReductionAuth1Key_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : (sigReductionAuth1Key S b A).Bounded :=
  sigReductionAuth1Key_bounded_of S b A (a1gStepBounds S b.q_total)

section ClampedStepCost
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle

private theorem a1sDelegate2C_costUB_le_v2 (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sDelegate2C S K (Δ := Δ) s q).costUB ≤ 80500 + 30000 * K + 10000 * min K S.N_dh := by
  have hG := a1gStep2C_costUB_le S K (Γ₁ := a1g2StTy :: Δ) (Γ₂ := Γ₂) (Δ := a1g2StTy :: Δ) Var.vz q
  simp only [a1sDelegate2C, a1sCaseAPa2, bindV, letV, Comp.letC,
    a1sG, a1sMk, a1sTp, a1sTpk, a1sFg, v, Comp.costUB, Expr.costUB]
  generalize min K S.N_dh = md at hG ⊢
  omega

private theorem a1sStep2C_costUB_le_v2 (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) :
    (a1sStep2C S K (Δ := Δ) s q).costUB ≤ 106000 + 38000 * K + 10412 * min K S.N_dh := by
  have hP := a1sPreC_costUB_le_tight S K (Δ := Δ) s q
  have hD := a1sDelegate2C_costUB_le_v2 S K (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStep2C, bindV, caseSumV, isSomeE, a1sFg, aNone, v, Comp.costUB, Expr.costUB]
  generalize min K S.N_dh = md at hP hD ⊢
  omega

theorem a1s_handle_cost_le_v2 (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).handle.cost ≤ 106000 + 38000 * K + 10412 * min K S.N_dh :=
  Nat.le_trans (Comp.cost_le_costUB _)
    (a1sStep2C_costUB_le_v2 S K (Δ := [a1sStTy, authQueryTy]) _ _)

/-- Step-cost bound with 3/2 headroom for `sigAuth1KeyDslProg` against `stepCostBudget`. -/
theorem sigAuth1KeyDslProg_three_mul_totalCost_le_two_mul_stepCostBudget
    (S : Setup) (b : QueryBudget) :
    3 * (sigAuth1KeyDslProg S b).totalCost b.q_total + 400 * b.q_total ≤
      2 * _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hH := a1s_handle_cost_le_v2 S b.q_total
  have hF := a1s_finish_cost_le S b.q_total
  have hI := a1s_init_cost_le_tight S b.q_total
  change 3 * ((sigAuth1KeyProg S b.q_total).init.cost +
      b.q_total * max 1 ((sigAuth1KeyProg S b.q_total).handle.cost + 32) +
      (sigAuth1KeyProg S b.q_total).finish.cost) + 400 * b.q_total ≤
    2 * _root_.SignalPqxdh.Security.stepCostBudget S b
  generalize (sigAuth1KeyProg S b.q_total).init.cost = cI at hI ⊢
  generalize (sigAuth1KeyProg S b.q_total).handle.cost = cH at hH ⊢
  generalize (sigAuth1KeyProg S b.q_total).finish.cost = cF at hF ⊢
  have hMax : max 1 (cH + 32) = cH + 32 := by omega
  rw [hMax]
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize min b.q_total S.N_dh = md at hH ⊢
  generalize min b.q_total S.N_sess_tot = ms at ⊢
  generalize Nat.log 2 S.N_dh = ld at hI ⊢
  generalize Nat.log 2 S.N_sess_tot = ls at ⊢
  generalize b.q_total = q at *
  have hqH : q * (cH + 32) ≤ q * (106032 + 38000 * q + 10412 * md) :=
    Nat.mul_le_mul_left q (by omega)
  rcases q with _ | _ | _ | _ | q'
  · nlinarith [Nat.zero_le (md ^ 2), Nat.zero_le (md * ms)]
  · nlinarith [Nat.zero_le (md ^ 2), Nat.zero_le (md * ms)]
  · nlinarith [Nat.zero_le (md ^ 2), Nat.zero_le (md * ms)]
  · nlinarith [Nat.zero_le (md ^ 2), Nat.zero_le (md * ms)]
  · nlinarith [Nat.zero_le (q' * md), Nat.zero_le (q' * ms), Nat.zero_le (md ^ 2),
      Nat.zero_le (md * ms), Nat.zero_le (q' * ld), Nat.zero_le (q' * ls)]

/-- Step-cost bound for `sigAuth1KeyDslProg` against `SignalPqxdh.Security.stepCostBudget`. -/
theorem sigAuth1KeyDslProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyDslProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have := sigAuth1KeyDslProg_three_mul_totalCost_le_two_mul_stepCostBudget S b
  omega

end ClampedStepCost

section Auth1KeySigSizeAndWhen

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle

@[simp] private theorem a1s_pqxdhOps_opSize (o : pqxdhOps.Op) : pqxdhOps.opSize o = 0 := by
  cases o <;> rfl
@[simp] private theorem a1s_ops_sum_opSize_inl {S : Sig} (O₁ O₂ : Ops S) (o : O₁.Op) :
    (Ops.sum O₁ O₂).opSize (Sum.inl o) = O₁.opSize o := rfl
@[simp] private theorem a1s_ops_sum_opSize_inr {S : Sig} (O₁ O₂ : Ops S) (o : O₂.Op) :
    (Ops.sum O₁ O₂).opSize (Sum.inr o) = O₂.opSize o := rfl
@[simp] private theorem a1s_pqBytesOps_opSize (o : pqBytesOps.Op) : pqBytesOps.opSize o = 0 := rfl
@[simp] private theorem a1s_pqU32Ops_opSize (o : pqU32Ops.Op) : pqU32Ops.opSize o = 0 := rfl

@[simp] private theorem a1s_liftBase_size {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) : (KeyInd.liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [KeyInd.liftBase, Comp.size, pqChalIface, pqPrimIface]

@[simp] private theorem a1s_liftChal_size {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) : (Comp.liftChal (C := C) c).size = c.size := by
  induction c <;> simp_all [Comp.liftChal, Comp.size, pqChalIface, pqPrimIface]

@[simp] private theorem a1s_liftGdhComp_size {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t) : (KeyInd1KeyGapDh.liftGdhComp c).size = c.size :=
  KeyInd1KeyGapDh.liftGdhComp_size c

@[simp] private theorem a1s_sigChalQ_dsl_size {Γ : List (Ty pqSig)} (m : ℕ+)
    (e : Expr pqxdhOps Γ (B m)) : (KeyInd1KeyGapDh.sigChalQ_dsl m e).size = e.size + 1 := rfl

section A1sAtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {C : ChallengerOracle} {Γ Δ : List (Ty pqSig)} {τ τ₁ τ₂ : Ty pqSig}

@[simp] private theorem a1s_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem a1s_letC_size (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (Comp.letC e k).size = e.size + 1 + k.size + 1 := rfl
@[simp] private theorem a1s_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .vz).size + 1 := rfl
@[simp] private theorem a1s_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .vz).size + 1 := rfl
@[simp] private theorem a1s_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem a1s_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem a1s_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1s_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1s_mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem a1s_foldMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).size = xs.size + init.size + (f .vz (.vs .vz)).size + bits K + 1 := rfl
@[simp] private theorem a1s_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .vz).size + 1 := rfl
@[simp] private theorem a1s_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem a1s_eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem a1s_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1s_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1s_eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem a1s_litBytes_size (w : ℕ+) (bs : Bytes) :
    (Expr.litBytes w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_bytesAppend_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (Expr.bytesAppend a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem a1s_bytesCons_size {n : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesCons b a).size = a.size + 1 := rfl
@[simp] private theorem a1s_bytesWiden_size (w d : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesWiden w d a).size = a.size + 1 := rfl
@[simp] private theorem a1s_bytesTakeK_size {n : ℕ+} (k : ℕ+) (a : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesTakeK k a).size = a.size + 1 := rfl
@[simp] private theorem a1s_bytesDrop_size {n : ℕ+} (k : Expr pqxdhOps Γ .nat) (a : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesDrop k a).size = k.size + a.size + 2 := rfl
@[simp] private theorem a1s_bytesLen_size {n : ℕ+} (a : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesLen a).size = a.size + 1 := rfl
@[simp] private theorem a1s_bytesBeq_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (Expr.bytesBeq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem a1s_bytesVarint_size (a : Expr pqxdhOps Γ .nat) :
    (Expr.bytesVarint a).size = a.size + 1 := rfl
@[simp] private theorem a1s_u32OfNat_size (a : Expr pqxdhOps Γ .nat) :
    (Expr.u32OfNat a).size = a.size + 1 := rfl
@[simp] private theorem a1s_u32Beq_size (a b : Expr pqxdhOps Γ U32) :
    (Expr.u32Beq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem a1s_sampleBool_size : (Comp.sampleBool (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleBytes32_size : (Comp.sampleBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleRandom64_size : (Comp.sampleRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleDrKey96_size : (Comp.sampleDrKey96 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleIndex_size (N : ℕ) : (Comp.sampleIndex N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_queryPrim_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrim g e).size = e.size + 1 := rfl
@[simp] private theorem a1s_sampleBoolC_size : (Comp.sampleBoolC (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleBytes32C_size :
    (Comp.sampleBytes32C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleRandom64C_size :
    (Comp.sampleRandom64C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleDrKey96C_size :
    (Comp.sampleDrKey96C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_sampleIndexC_size (N : ℕ) :
    (Comp.sampleIndexC (C := C) N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1s_queryPrimC_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrimC (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem a1s_queryChal_size (t : C.Tag) (e : Expr pqxdhOps Γ (C.dom t)) :
    (Comp.queryChal (C := C) t e).size = e.size + 1 := rfl
@[simp] private theorem a1s_queryDdh_size (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (Comp.queryDdh e).size = e.size + 1 := rfl
@[simp] private theorem a1s_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem a1s_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) :
    (encKEM e).size = e.size + 1 := rfl

end A1sAtomicSizeSimp

set_option linter.unusedSimpArgs false in
private theorem a1s_firstMsgADE_size {Γ : List (Ty pqSig)}
    (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) :
    (firstMsgADE ikA ikB eph pq).size = ikA.size + ikB.size + eph.size + 3 * pq.size + 36 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [firstMsgADE, pbBytesField, encEC, Expr.bytesAppend, Expr.bytesCons, Expr.litBytes,
    Expr.bytesVarint, Expr.bytesLen, Expr.litNat, Expr.size, a1s_ops_sum_opSize_inl,
    a1s_ops_sum_opSize_inr, a1s_pqBytesOps_opSize, a1s_pqU32Ops_opSize, a1s_pqxdhOps_opSize, hb0]
  dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]; omega

private theorem a1s_hb_consts :
    bits 32 = 6 ∧ bits 64 = 7 ∧ bits 96 = 7 ∧ bits 128 = 8 ∧ bits 160 = 8 ∧ bits 192 = 8 := by decide

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
private theorem a1s_fgStep2C_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgStep2C (Δ := Δ) S K pa sim q).size ≤ 105 * bits K + 45 * bits (min K S.N_dh) + 18500 := by
  simp (config := { maxSteps := 4000000 }) only [
    fgStep2C, fgInitPrin2C, fgGenSpk2C, fgSend2C, fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC,
    onBaseF, sendGuardE, isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
    patchC, rootPatchC, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pa2U, pa2V, pa2Role, pa2TS, pa2Dh1, feP1, feP2, feP3, feP4, feSs, feDk,
    pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk, q4, bytesEmpty, slice32, zero32,
    emptySimE, initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB,
    roB, roRootB, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk, pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, a1s_firstMsgADE_size, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM, a1s_liftChal_size, a1s_v_size, a1s_letC_size, a1s_bindV_size, a1s_letV_size,
    a1s_caseOptV_size, a1s_caseSumV_size, a1s_findMV_size, a1s_anyMV_size, a1s_mapMV_size,
    a1s_foldMV_size, a1s_eLet_size, a1s_eCaseOpt_size, a1s_eCaseSum_size,
    a1s_eFind_size, a1s_eAny_size, a1s_eMap_size, a1s_litBytes_size, a1s_bytesAppend_size,
    a1s_bytesCons_size, a1s_bytesWiden_size, a1s_bytesTakeK_size, a1s_bytesDrop_size,
    a1s_bytesLen_size, a1s_bytesBeq_size, a1s_bytesVarint_size, a1s_u32OfNat_size, a1s_u32Beq_size,
    a1s_sampleBool_size, a1s_sampleBytes32_size, a1s_sampleRandom64_size, a1s_sampleDrKey96_size,
    a1s_sampleIndex_size, a1s_queryPrim_size, a1s_sampleBoolC_size, a1s_sampleBytes32C_size,
    a1s_sampleRandom64C_size, a1s_sampleDrKey96C_size, a1s_sampleIndexC_size, a1s_queryPrimC_size,
    a1s_queryChal_size, a1s_queryDdh_size, a1s_encEC_size, a1s_encKEM_size, Comp.size, Expr.size,
    a1s_pqxdhOps_opSize, bits_0, bits_1, ↓reduceIte, Bool.false_eq_true]
  have hb_consts := a1s_hb_consts; omega

set_option linter.unusedSimpArgs false in
private theorem a1s_a1gStep2C_size_le (S : Setup) (K : Nat) {Γs Γq Δ : List (Ty pqSig)}
    [Ext Γs Δ] [Ext Γq Δ] (st : Var Γs a1g2StTy) (q : Var Γq authQueryTy) :
    (a1gStep2C S K (Δ := Δ) st q).size ≤ 115 * bits K + 45 * bits (min K S.N_dh) + 20000 := by
  have hFg := a1s_fgStep2C_size_le S K (Γ₁ := a1gParams2Ty :: Δ) (Γ₂ := fgSimTy :: a1gParams2Ty :: Δ)
    (Γ₃ := Γq) (Δ := .unit :: (.sum RSB .unit) :: .nat :: fgSimTy :: a1gParams2Ty :: Δ) .vz .vz q
  simp only [a1gStep2C, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
    a1s_liftGdhComp_size, a1s_sigChalQ_dsl_size,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pa2U, pa2V, pa2Role, pa2TS, pa2Dh1,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    aNone, aInitPrin, aBundle, natEq, nat2Eq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Comp.iteC, a1s_v_size, a1s_letC_size, a1s_bindV_size,
    a1s_letV_size, a1s_caseOptV_size, a1s_caseSumV_size, a1s_eCaseOpt_size, a1s_eCaseSum_size,
    a1s_eFind_size, a1s_eAny_size, a1s_litBytes_size, a1s_u32OfNat_size,
    a1s_sampleBytes32C_size, a1s_sampleRandom64C_size, a1s_queryPrimC_size,
    a1s_encEC_size, a1s_encKEM_size, Comp.size, Expr.size, a1s_pqxdhOps_opSize, bits_0, bits_1]
  omega

set_option linter.unusedSimpArgs false in
private theorem a1sPreC_size_le_clamped (S : Setup) (K : Nat) {Γs Γq Δ : List (Ty pqSig)}
    [Ext Γs Δ] [Ext Γq Δ] (s : Var Γs a1sStTy) (q : Var Γq authQueryTy) :
    (a1sPreC S K (Δ := Δ) s q).size ≤ 8 * bits K + 4 * bits (min K S.N_dh) + 900 := by
  simp only [a1sPreC, a1sSendCheckC, a1sTp, a1sTpk, a1sBase, a1sG, a1sMk, fsBase,
    a1s_liftBase_size, AuthHs.extractC, honestPeerC, findHonestC,
    stPrin, stSpks, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    natEq, isSomeE, aNone,
    Expr.litUnit, Expr.litBool, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.bytesWiden, Expr.bytesCons, encEC, encKEM, Comp.iteC,
    a1s_v_size, a1s_letC_size, a1s_bindV_size, a1s_letV_size, a1s_caseSumV_size, a1s_findMV_size,
    a1s_eCaseOpt_size, a1s_eAny_size, a1s_bytesWiden_size, a1s_bytesBeq_size,
    a1s_queryPrim_size, a1s_encEC_size, a1s_encKEM_size, v, Comp.size, Expr.size,
    a1s_ops_sum_opSize_inl, a1s_ops_sum_opSize_inr,
    a1s_pqBytesOps_opSize, a1s_pqU32Ops_opSize, a1s_pqxdhOps_opSize, bits_0, bits_1]
  dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  have hEq : bits (K.min S.N_dh) = bits (min K S.N_dh) := rfl
  omega

set_option linter.unusedSimpArgs false in
private theorem a1sDelegate2C_size_le_clamped (S : Setup) (K : Nat) {Γs Γq Δ : List (Ty pqSig)}
    [Ext Γs Δ] [Ext Γq Δ] (s : Var Γs a1sStTy) (q : Var Γq authQueryTy) :
    (a1sDelegate2C S K (Δ := Δ) s q).size ≤
      115 * bits K + 45 * bits (min K S.N_dh) + 20100 := by
  have := a1s_a1gStep2C_size_le S K (Γs := a1g2StTy :: Δ) (Γq := Γq) (Δ := a1g2StTy :: Δ) Var.vz q
  simp only [a1sDelegate2C, a1sCaseAPa2, a1sG, a1sMk, a1sTp, a1sTpk, a1sFg,
    Expr.noneE, a1s_v_size, a1s_bindV_size, a1s_letV_size, Comp.size, Expr.size,
    a1s_pqxdhOps_opSize, bits_0]
  omega

set_option linter.unusedSimpArgs false in
private theorem a1sStep2C_size_le_clamped (S : Setup) (K : Nat) {Γs Γq Δ : List (Ty pqSig)}
    [Ext Γs Δ] [Ext Γq Δ] (s : Var Γs a1sStTy) (q : Var Γq authQueryTy) :
    (a1sStep2C S K (Δ := Δ) s q).size ≤
      123 * bits K + 49 * bits (min K S.N_dh) + 21100 := by
  have hP := a1sPreC_size_le_clamped S K (Δ := Δ) s q
  have hD := a1sDelegate2C_size_le_clamped S K (Δ := .unit :: (.sum a1sRS .unit) :: Δ) s q
  simp only [a1sStep2C, a1sFg, isSomeE, aNone, Expr.litUnit, Expr.litBool, Comp.iteC,
    a1s_v_size, a1s_bindV_size, a1s_caseSumV_size, Comp.size, Expr.size, a1s_pqxdhOps_opSize]
  omega

set_option linter.unusedSimpArgs false in
private theorem sigAuth1KeyProg_size_le_clamped (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).size ≤
      123 * bits K + 49 * bits (min K S.N_dh) +
        bits (min K (min S.N_spk_tot S.N_recv)) + 21400 := by
  have hH : (a1sHandle2Dsl S K).size ≤
      123 * bits K + 49 * bits (min K S.N_dh) + 21100 :=
    a1sStep2C_size_le_clamped S K (Δ := [a1sStTy, authQueryTy]) .vz (.vs .vz)
  have hI : (a1sInit2Dsl S K).size ≤ bits (min K (min S.N_spk_tot S.N_recv)) + 200 := by
    simp only [a1sInit2Dsl, a1sDummyPa, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.listNil,
      a1s_v_size, a1s_bindV_size, a1s_letV_size,
      a1s_sampleIndexC_size, a1s_sampleBoolC_size, Comp.size, Expr.size,
      a1s_pqxdhOps_opSize, bits_0, bits_1]
    omega
  have hF : a1sFinishDsl.size ≤ 100 := by
    simp only [a1sFinishDsl, a1sFg, a1s_eCaseOpt_size, a1s_litBytes_size,
      a1s_v_size, Comp.size, Expr.size, a1s_pqxdhOps_opSize]
    omega
  change (a1sInit2Dsl S K).size + (a1sHandle2Dsl S K).size + a1sFinishDsl.size ≤ _
  omega

/-- Program-size bound for `sigAuth1KeyProg` independent of `S`. -/
theorem sigAuth1KeyProg_size_le_v2 (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).size ≤ 173 * bits K + 21400 := by
  have h := sigAuth1KeyProg_size_le_clamped S K
  have hd : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have hb : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  omega

theorem sigAuth1KeyProg_size_le (S : Setup) (K : Nat) :
    (sigAuth1KeyProg S K).size ≤
      123 * bits K + 57 * bits S.N_dh + 15 * bits S.N_sess_tot + 21400 := by
  have h := sigAuth1KeyProg_size_le_clamped S K
  have hd : bits (min K S.N_dh) ≤ bits S.N_dh := bits_mono (Nat.min_le_right _ _)
  have hb : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits S.N_dh :=
    bits_mono (le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_left _ _) (by unfold Setup.N_dh; omega)))
  omega

theorem sigAuth1KeyDslProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigAuth1KeyDslProg S b).size ≤
      21400 + 195 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  unfold sigAuth1KeyDslProg
  have hP := sigAuth1KeyProg_size_le_v2 S b.q_total
  have hq : bits b.q_total ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
    apply bits_mono
    unfold _root_.SignalPqxdh.Security.stepCostBudget; dsimp only
    have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  omega

/-- Run-local output block-size bound for `sigAuth1KeyDslProg` against
    `SignalPqxdh.Security.outputSizeBudget`. -/
theorem sigAuth1KeyDslProg_blocks_when_security (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total)
    (hfit : ∀ u, AllGameQueriesFit ℓ (authCodec S) (A u))
    (x : (B 32).denote)
    (hx : ValFits ℓ (B 32) x)
    (y : (Ty.prod (B 1569) (B 64)).denote)
    (hy : y ∈ supportWhen (pqSigAndDdhIface.AnswerFits ℓ)
      ((sigAuth1KeyDslProg S b).eval A x)) :
    ValFits (_root_.SignalPqxdh.Security.outputSizeBudget S b ℓ) (Ty.prod (B 1569) (B 64)) y := by
  rw [a1s_valFits_iff_fits]
  have hx' : (B 32).Fits ℓ x := (a1s_valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (sigAuth1KeyDslProg S b).fits_eval_when
    pqO_sizeHonest SignalPqxdh.LegacyCosted.pqSamplers_sizeHonest ℓ ℓ 0 (fun _ => trivial)
    A b.q_total ℓ hA' hfit x hx' y hy
  have hCost := sigAuth1KeyDslProg_totalCost_le_stepCostBudget S b
  have hNq := le_trans
    (a1s_gred_nq_le_totalCost a1s_one_le_pqChalIface_qCost a1s_one_le_pqSamplers_sCost
      (sigAuth1KeyDslProg S b) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (Ty.prod (B 1569) (B 64)) y hEval
  unfold _root_.SignalPqxdh.Security.outputSizeBudget at *
  have hM := Nat.mul_le_mul_right ℓ hNq
  nlinarith

/-- Run-local output block-size bound for `sigAuth1KeyDslProg` against
    `LegacyCosted.outputSizeBudget`. -/
theorem sigAuth1KeyDslProg_blocks_when (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total)
    (hfit : ∀ u, AllGameQueriesFit ℓ (authCodec S) (A u))
    (x : (B 32).denote)
    (hx : ValFits ℓ (B 32) x)
    (y : (Ty.prod (B 1569) (B 64)).denote)
    (hy : y ∈ supportWhen (pqSigAndDdhIface.AnswerFits ℓ)
      ((sigAuth1KeyDslProg S b).eval A x)) :
    ValFits (SignalPqxdh.LegacyCosted.outputSizeBudget S b ℓ) (Ty.prod (B 1569) (B 64)) y := by
  rw [a1s_valFits_iff_fits]
  have hx' : (B 32).Fits ℓ x := (a1s_valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (sigAuth1KeyDslProg S b).fits_eval_when
    pqO_sizeHonest SignalPqxdh.LegacyCosted.pqSamplers_sizeHonest ℓ ℓ 0 (fun _ => trivial)
    A b.q_total ℓ hA' hfit x hx' y hy
  have hCost := sigAuth1KeyDslProg_totalCost_le_of S b (a1gStepBounds S b.q_total)
  have hNq := le_trans
    (a1s_gred_nq_le_totalCost a1s_one_le_pqChalIface_qCost a1s_one_le_pqSamplers_sCost
      (sigAuth1KeyDslProg S b) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (Ty.prod (B 1569) (B 64)) y hEval
  unfold SignalPqxdh.LegacyCosted.outputSizeBudget SignalPqxdh.LegacyCosted.stepCostBudget at *
  have hM := Nat.mul_le_mul_right ℓ hNq
  nlinarith

end Auth1KeySigSizeAndWhen

end SignalPqxdh.Security.ReductionDsl.AuthHs
