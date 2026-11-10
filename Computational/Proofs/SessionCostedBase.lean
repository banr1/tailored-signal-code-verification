/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Soundness
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
public import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
public import Computational.Proofs.ReductionDsl.Size
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Costed DSL Base Helpers and Ratchet Budget Bounds

Provides `gredBounded_of_bounds`, `gtwoStageBounded_of_bounds`, and `ratchetCostBudget` comparison
lemmas for the Libsignal session security proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme
  WireAEAD FSAEAD

section GRedBoundedHelper

variable {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S} {ι κ : Type}
  {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
  {C : ReductionDsl.GameCodec S G}

lemma costedFits_iff_fits (B : ℕ) (t : ReductionDsl.Ty S) (x : t.denote) :
    CostedFits B t x ↔ t.Fits B x :=
  Iff.rfl

lemma costedOpsSizeHonest_of_opsSizeHonest (hO : ReductionDsl.OpsSizeHonest O) :
    CostedOpsSizeHonest O :=
  hO

lemma costedSampSizeHonest_of_sampSizeHonest (hS : ReductionDsl.SampSizeHonest I.smp) :
    CostedSampSizeHonest I.smp :=
  hS

lemma expr_cost_pos {Γ : List (ReductionDsl.Ty S)} {t : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ t) : 1 ≤ e.cost := by
  induction e <;> simp only [ReductionDsl.Expr.cost]
  case nat n => exact ReductionDsl.one_le_bits n
  all_goals omega

lemma comp_nq_le_cost {Γ : List (ReductionDsl.Ty S)} {t : ReductionDsl.Ty S}
    (c : ReductionDsl.Comp O I Γ t) : c.nq ≤ c.cost := by
  induction c with
  | ret e => simp [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries]
  | bind c1 c2 ih1 ih2 =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | ite e c1 c2 ih1 ih2 =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | caseOpt e n s ihn ihs =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | caseSum e l r ihl ihr =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | sample s a =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost]
    have := expr_cost_pos a
    omega
  | query g a =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost]
    have := expr_cost_pos a
    omega
  | iter k init step ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * step.queries (fun _ => 1) (fun _ => 1) ≤ k * (step.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | findM k l pred ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * pred.queries (fun _ => 1) (fun _ => 1) ≤ k * (pred.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | anyM k xs pred ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * pred.queries (fun _ => 1) (fun _ => 1) ≤ k * (pred.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | mapM k xs body ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * body.queries (fun _ => 1) (fun _ => 1) ≤ k * (body.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | consumeFirstM k l p mk ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * p.queries (fun _ => 1) (fun _ => 1) ≤ k * (p.cost + mk.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | foldM k xs init step ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * step.queries (fun _ => 1) (fun _ => 1) ≤ k * (step.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega

lemma gredBounded_of_bounds {rIn aIn aOut out : ReductionDsl.Ty S}
    {R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut costBudget : ℕ}
    (hcost : R.totalCost q ≤ costBudget)
    (hsize : R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hq : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : ReductionDsl.OpsSizeHonest O)
    (hS : ReductionDsl.SampSizeHonest I.smp) :
    GRedBounded R wTag wSamp q qOut costBudget :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds R wTag wSamp q qOut costBudget
    hcost hsize hq hO hS

lemma comp_cost_pos {Γ : List (ReductionDsl.Ty S)} {t : ReductionDsl.Ty S}
    (c : ReductionDsl.Comp O I Γ t) : 1 ≤ c.cost := by
  induction c with
  | ret e => have := expr_cost_pos e; simp only [ReductionDsl.Comp.cost]; omega
  | bind _ _ _ _ | ite _ _ _ _ _ | caseOpt _ _ _ _ _ | caseSum _ _ _ _ _ =>
    simp only [ReductionDsl.Comp.cost]; omega
  | sample _ a | query _ a =>
    have := expr_cost_pos a; simp only [ReductionDsl.Comp.cost]; omega
  | iter _ s _ _ | findM _ s _ _ | anyM _ s _ _ | mapM _ s _ _
  | consumeFirstM _ s _ _ _ | foldM _ s _ _ _ =>
    have := expr_cost_pos s; simp only [ReductionDsl.Comp.cost]; omega

private lemma costedMidFits_of_fitsWhen {α : Type} {qB B B' : ℕ} (h : B ≤ B')
    {π σ ch : ReductionDsl.Ty S}
    (m : ReductionDsl.Mid G α π.denote σ.denote ch.denote)
    (hm : ReductionDsl.Mid.FitsWhen C π σ ch qB B m) :
    CostedMidFits B' π σ ch m := by
  cases m with
  | done _ s => exact ReductionDsl.Ty.fits_mono h _ s hm
  | paused _ c p s _ =>
    exact ⟨ReductionDsl.Ty.fits_mono h _ c hm.1,
      ReductionDsl.Ty.fits_mono h _ p hm.2.1,
      ReductionDsl.Ty.fits_mono h _ s hm.2.2.1⟩

lemma gtwoStageBounded_of_bounds {rIn aIn aOut ch rIn2 out : ReductionDsl.Ty S}
    {R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut costBudget : ℕ}
    (hcost : R.totalCost q ≤ costBudget)
    (hsize : R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hq : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : ReductionDsl.OpsSizeHonest O)
    (hS : ReductionDsl.SampSizeHonest I.smp) :
    GTwoStageBounded R wTag wSamp q qOut costBudget := by
  refine ⟨hcost, hsize, hq, costedOpsSizeHonest_of_opsSizeHonest hO,
    costedSampSizeHonest_of_sampSizeHonest hS,
    fun B haOut A hfit x hx dflt cm hcm => ?_⟩
  have haOut' : ∀ v, aOut.Fits B v :=
    fun v => (costedFits_iff_fits B _ _).mp (haOut v)
  have hx' : rIn.Fits B x := (costedFits_iff_fits B _ _).mp hx
  have hi1 := comp_cost_pos R.init
  have hres1 := comp_cost_pos R.resume
  have hfin1 := comp_cost_pos R.finish
  have hi_nq := comp_nq_le_cost R.init
  have hpre_nq := comp_nq_le_cost R.handlePre
  have hpost_nq := comp_nq_le_cost R.handlePost
  have hch_nq := comp_nq_le_cost R.chDone
  have hres_nq := comp_nq_le_cost R.resume
  have hfin_nq := comp_nq_le_cost R.finish
  have hnq_tot : R.nq q ≤ costBudget :=
    le_trans (CryptoVerification.E2E.Costed.TwoStageCostedReduction.nq_le_totalCost R q) hcost
  have hnq_tot_B : R.nq q * B ≤ costBudget * B := Nat.mul_le_mul_right B hnq_tot
  have hpre_c : q * R.handlePre.cost ≤
      q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q (le_trans (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
      (le_max_right _ _))
  have hpost_c : q * R.handlePost.cost ≤
      q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q (le_trans (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
      (le_max_right _ _))
  have hpre_nq_mul : q * R.handlePre.nq ≤ q * R.handlePre.cost := Nat.mul_le_mul_left q hpre_nq
  have hpost_nq_mul : q * R.handlePost.nq ≤ q * R.handlePost.cost := Nat.mul_le_mul_left q hpost_nq
  have hres_c : R.resume.cost ≤ max R.chDone.cost R.resume.cost := le_max_right _ _
  have hpre_cost_le : R.init.cost + q * R.handlePre.cost ≤ costBudget := by
    have := hcost; dsimp only [ReductionDsl.TwoStageCostedReduction.totalCost] at this; omega
  have hpre_nq_le : R.init.nq + q * R.handlePre.nq ≤ costBudget := by
    have := hcost; dsimp only [ReductionDsl.TwoStageCostedReduction.totalCost] at this; omega
  have hpre_nq_B : (R.init.nq + q * R.handlePre.nq) * B ≤ costBudget * B :=
    Nat.mul_le_mul_right B hpre_nq_le
  have hcost_sum :
      R.init.cost + q * R.handlePre.cost + R.resume.cost + q * R.handlePost.cost + R.finish.cost ≤
        2 * costBudget := by
    have := hcost; dsimp only [ReductionDsl.TwoStageCostedReduction.totalCost] at this; omega
  have hnq_sum :
      3 + R.init.nq + q * R.handlePre.nq + R.resume.nq + q * R.handlePost.nq + R.finish.nq ≤
        2 * costBudget := by
    have := hcost; dsimp only [ReductionDsl.TwoStageCostedReduction.totalCost] at this; omega
  have hnq_sum_B :
      (3 + R.init.nq + q * R.handlePre.nq + R.resume.nq + q * R.handlePost.nq + R.finish.nq) * B ≤
        2 * (costBudget * B) := by
    calc (3 + R.init.nq + q * R.handlePre.nq + R.resume.nq + q * R.handlePost.nq + R.finish.nq) * B
      _ ≤ (2 * costBudget) * B := Nat.mul_le_mul_right B hnq_sum
      _ = 2 * (costBudget * B) := by ring
  have hringW : 2 * (costBudget + 2 * q + 1) * (B + 1) =
      2 * (costBudget * B) + 4 * (q * B) + 2 * B + 2 * costBudget + 4 * q + 2 := by ring
  obtain ⟨hcFits, hmFits⟩ :=
    R.fits_eval1_when hO hS B B B haOut' A hfit q B x hx' dflt cm hcm
  refine ⟨?_, ?_, fun y hy z hz => ?_⟩
  · rw [costedFits_iff_fits]
    refine ReductionDsl.Ty.fits_mono ?_ _ _ hcFits
    rw [hringW]; omega
  · refine costedMidFits_of_fitsWhen ?_ cm.2 hmFits
    have hringM :
        B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) =
          B + q * B + (R.init.cost + q * R.handlePre.cost) +
            (R.init.nq + q * R.handlePre.nq) * B := by ring
    rw [hringM, hringW]; omega
  · rw [costedFits_iff_fits]
    have hy' : rIn2.Fits B y := (costedFits_iff_fits B _ _).mp hy
    have hz' := R.fits_eval2_when hO hS B B B haOut' cm.2 _ hmFits y B hy' q dflt z hz
    refine ReductionDsl.Ty.fits_mono ?_ _ _ hz'
    have hring2 :
        (B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B)) +
          B + B + q * B + (R.resume.cost + q * R.handlePost.cost + R.finish.cost) +
          (R.resume.nq + q * R.handlePost.nq + R.finish.nq) * B =
        2 * (q * B) +
          (R.init.cost + q * R.handlePre.cost + R.resume.cost + q * R.handlePost.cost + R.finish.cost) +
          (3 + R.init.nq + q * R.handlePre.nq + R.resume.nq + q * R.handlePost.nq + R.finish.nq) * B := by
      ring
    rw [hring2, hringW]; omega

end GRedBoundedHelper

section ChainCosted

lemma fsRatchetCostBudget_le_ratchetCostBudget (q qep : ℕ) :
    fsRatchetCostBudget q qep ≤ ratchetCostBudget q qep :=
  Nat.min_le_left _ _

lemma ratchetCostBudget_pos (q qep : ℕ) :
    16777216 * (q + 1) ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget maxForwardJumps
  have hb : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  nlinarith

theorem ratchetCostBudget_le_old (q qep : ℕ) :
    ratchetCostBudget q qep ≤ 2 ^ 24 * (q + 1) * (q + qep + maxForwardJumps + 1) ^ 2 := by
  unfold ratchetCostBudget
  set N := q + qep + maxForwardJumps + 1
  have hq : q + 1 ≤ N := by dsimp [N]; omega
  have hb : ReductionDsl.bits qep ≤ qep + 1 := ReductionDsl.bits_le_succ qep
  have hm : maxForwardJumps + ReductionDsl.bits qep ≤ N := by dsimp [N]; omega
  have hprod : (q + 1) * (maxForwardJumps + ReductionDsl.bits qep) ≤ N ^ 2 := by
    calc (q + 1) * (maxForwardJumps + ReductionDsl.bits qep)
      _ ≤ N * N := Nat.mul_le_mul hq hm
      _ = N ^ 2 := by ring
  calc 2 ^ 12 * (q + 1) ^ 2 * (maxForwardJumps + ReductionDsl.bits qep)
    _ = 2 ^ 12 * (q + 1) * ((q + 1) * (maxForwardJumps + ReductionDsl.bits qep)) := by ring
    _ ≤ 2 ^ 12 * (q + 1) * N ^ 2 := Nat.mul_le_mul_left _ hprod
    _ ≤ 2 ^ 24 * (q + 1) * N ^ 2 :=
      Nat.mul_le_mul_right (N ^ 2) (Nat.mul_le_mul_right (q + 1) (by decide))

end ChainCosted

section DDHCosted

variable {Pt : Type} [Zero Pt]

end DDHCosted

end CryptoVerification.LibsignalSession
