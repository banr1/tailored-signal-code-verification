/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Soundness
public import Computational.Proofs.ReductionDsl.Size

/-!
# `ReductionDsl` Size Bounds, Counterexamples, and Capped List Guards

Proves two-stage input-conditioned (`GameCodec.FitsOn`) and cost-independent leaf-width
(`Ty.BaseFits`) bounds for `TwoStageCostedReduction`, together with vacuity and nested-list
quadratic-blowup counterexamples (`global_fits_false_on_bytes`, `nested_list_quadratic_treeBlocks`).
Also defines an untrusted association-list table model (`AssocTable`) and runtime list-length cap
helpers (`withinCap`).
-/

@[expose] public section

namespace ReductionDsl

open OracleSpec OracleComp

section TwoStageHardening

variable {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}

/-- Base-block counterpart of `Mid.Fits`. -/
def Mid.BaseFits {κ : Type} {G : OracleSpec κ} {α : Type} (π σ ch : Ty S) (W : ℕ) :
    Mid G α π.denote σ.denote ch.denote → Prop
  | .done _ s => σ.BaseFits W s
  | .paused _ c p s _ => ch.BaseFits W c ∧ π.BaseFits W p ∧ σ.BaseFits W s

theorem TwoStageCostedReduction.fits_eval1Bounded_on {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {qPred : κ → Prop} (qB : ℕ) (henc : C.FitsOn qPred qB)
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hqp : ∀ a, AllGameQueries qPred (A a))
    (uFuel gFuel B : ℕ) (x : rIn.denote) (hx : rIn.Fits B x) (dflt : aOut.denote) :
    ∀ y ∈ support (R.eval1Bounded A x uFuel gFuel dflt),
      ch.Fits (B + aAdvB + gFuel * qB + R.totalCostBounded uFuel gFuel + R.nq gFuel * aB) y.1 ∧
      Mid.Fits R.π R.σ ch (B + R.init.cost + R.init.nq * aB +
        gFuel * (qB + R.handlePre.cost + R.handlePre.nq * aB)) y.2 ∧
      (match y.2 with | .done _ _ => True | .paused _ _ _ _ k => ∀ u, AllGameQueries qPred (k u)) := by
  intro y hy
  simp only [TwoStageCostedReduction.eval1Bounded, mem_support_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, m, hm, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval hO hS aB hq R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have hmPair := R.fits_run1Bounded_on hO hS aB hq qB henc dflt (hqp oAdv) uFuel gFuel _ s₀ h0 m hm
  have hmFits := hmPair.1
  have hmQp := hmPair.2
  have hleCost : gFuel * R.handlePre.cost ≤
      gFuel * (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left gFuel (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
  have hleNq : (gFuel * R.handlePre.nq) * aB ≤
      (gFuel * max R.handlePre.nq R.handlePost.nq) * aB :=
    Nat.mul_le_mul_right aB (Nat.mul_le_mul_left gFuel (le_max_left _ _))
  have hleChCost := le_max_left R.chDone.cost R.resume.cost
  have hleChNq := Nat.mul_le_mul_right aB (le_max_left R.chDone.nq R.resume.nq)
  have hring1 : gFuel * (qB + R.handlePre.cost + R.handlePre.nq * aB) =
      gFuel * qB + gFuel * R.handlePre.cost + (gFuel * R.handlePre.nq) * aB := by ring
  have hring2 : (R.init.nq + gFuel * max R.handlePre.nq R.handlePost.nq +
      max R.chDone.nq R.resume.nq + R.finish.nq) * aB =
      R.init.nq * aB + (gFuel * max R.handlePre.nq R.handlePost.nq) * aB +
        max R.chDone.nq R.resume.nq * aB + R.finish.nq * aB := by ring
  dsimp only [Comp.nq] at hleNq hleChNq hring1 hring2
  cases m with
  | done b s' =>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := Comp.fits_eval hO hS aB hq R.chDone _ (.cons s' (.cons b .nil))
      (Env.fits_pair hmFits (hA b)) c hc
    have hc'' : ch.Fits
        (B + aAdvB + gFuel * qB + R.totalCostBounded uFuel gFuel + R.nq gFuel * aB) c := by
      refine Ty.fits_mono ?_ _ _ hc'
      dsimp only [TwoStageCostedReduction.totalCostBounded, TwoStageCostedReduction.nq,
        TwoStageCostedReduction.totalQueries, Comp.nq] at *
      omega
    exact ⟨hc'', hmFits, trivial⟩
  | paused t c p s' k =>
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    have hc'' : ch.Fits
        (B + aAdvB + gFuel * qB + R.totalCostBounded uFuel gFuel + R.nq gFuel * aB) c := by
      refine Ty.fits_mono ?_ _ _ hmFits.1
      dsimp only [TwoStageCostedReduction.totalCostBounded, TwoStageCostedReduction.nq,
        TwoStageCostedReduction.totalQueries, Comp.nq] at *
      omega
    exact ⟨hc'', hmFits, hmQp⟩

theorem TwoStageCostedReduction.fits_eval2Bounded_on {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {qPred : κ → Prop} (qB : ℕ) (henc : C.FitsOn qPred qB)
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (B₁ : ℕ)
    (hm : Mid.Fits R.π R.σ ch B₁ m)
    (hmQp : match m with | .done _ _ => True | .paused _ _ _ _ k => ∀ u, AllGameQueries qPred (k u))
    (y : rIn2.denote) (B₂ : ℕ) (hy : rIn2.Fits B₂ y) (uFuel₂ gFuel₂ : ℕ) (dflt : aOut.denote) :
    ∀ z ∈ support (R.eval2Bounded m y uFuel₂ gFuel₂ dflt),
      out.Fits (B₁ + B₂ + aAdvB + gFuel₂ * qB +
        (R.resume.cost + gFuel₂ * R.handlePost.cost + R.finish.cost) +
        (R.resume.nq + gFuel₂ * R.handlePost.nq + R.finish.nq) * aB) z := by
  intro z hz
  have hring1 : gFuel₂ * (qB + R.handlePost.cost + R.handlePost.nq * aB) =
      gFuel₂ * qB + gFuel₂ * R.handlePost.cost + gFuel₂ * R.handlePost.nq * aB := by ring
  have hring2 : (R.resume.nq + gFuel₂ * R.handlePost.nq + R.finish.nq) * aB =
      R.resume.nq * aB + gFuel₂ * R.handlePost.nq * aB + R.finish.nq * aB := by ring
  dsimp only [Comp.nq] at hring1 hring2
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2Bounded, pure_bind] at hz
    have hf := Comp.fits_eval hO hS aB hq R.finish _ (.cons s (.cons b (.cons y .nil)))
      (Env.fits_triple hm (hA b) hy) z hz
    refine Ty.fits_mono ?_ _ _ hf
    dsimp only [Comp.nq] at *
    omega
  | paused t c p s k =>
    simp only [TwoStageCostedReduction.eval2Bounded, mem_support_bind_iff] at hz
    obtain ⟨⟨v, s₁⟩, hres, ⟨b, s₂⟩, hrun, hz⟩ := hz
    have hs₁' : R.σ.Fits (B₁ + B₂ + R.resume.cost + R.resume.nq * aB) s₁ := by
      have henv : Env.Fits (B₁ + B₂) (.cons s (.cons p (.cons y .nil))) :=
        ⟨Ty.fits_mono (by omega) _ _ hm.2.2, Ty.fits_mono (by omega) _ _ hm.2.1,
          Ty.fits_mono (by omega) _ _ hy, trivial⟩
      exact (Comp.fits_eval hO hS aB hq R.resume (B₁ + B₂) _ henv (v, s₁) hres).2
    have hs₂ := runFuelBounded_fits_on R.handlePost hO hS aB hq qB henc dflt
      (hmQp (C.rdec t v)) uFuel₂ gFuel₂ _ s₁ hs₁' (b, s₂) hrun
    have henv₂ : Env.Fits
        (B₁ + B₂ + R.resume.cost + R.resume.nq * aB +
          gFuel₂ * (qB + R.handlePost.cost + R.handlePost.nq * aB) + aAdvB)
        (.cons s₂ (.cons b (.cons y .nil))) :=
      ⟨Ty.fits_mono (by omega) _ _ hs₂, Ty.fits_mono (by omega) _ _ (hA b),
        Ty.fits_mono (by omega) _ _ hy, trivial⟩
    have hf := Comp.fits_eval hO hS aB hq R.finish _ (.cons s₂ (.cons b (.cons y .nil)))
      henv₂ z hz
    refine Ty.fits_mono ?_ _ _ hf
    dsimp only [Comp.nq] at *
    omega

/-- Cost-independent two-stage leaf-width (`BaseFits`) preservation across `eval1Bounded`. -/
theorem TwoStageCostedReduction.baseFits_eval1_on {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {W_op W_samp W : ℕ} (hO : OpsBaseBounded O W_op) (hS : SampBaseBounded I.smp W_samp)
    (hWop : W_op ≤ W) (hWsamp : W_samp ≤ W)
    (hq : ∀ g x u, (I.cod g).BaseFits W (I.dec g x u))
    {qPred : κ → Prop} (henc : C.BaseFitsOn qPred W)
    (hA : ∀ v : aOut.denote, aOut.BaseFits W v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hqp : ∀ a, AllGameQueries qPred (A a))
    (uFuel gFuel : ℕ) (x : rIn.denote) (hx : rIn.BaseFits W x) (dflt : aOut.denote) :
    ∀ y ∈ support (R.eval1Bounded A x uFuel gFuel dflt),
      ch.BaseFits W y.1 ∧ Mid.BaseFits R.π R.σ ch W y.2 ∧
      (match y.2 with | .done _ _ => True | .paused _ _ _ _ k => ∀ u, AllGameQueries qPred (k u)) := by
  have hRun1 : ∀ {α : Type} (d : α) {oa : OracleComp (unifSpec + G) α},
      AllGameQueries qPred oa → ∀ uf gf s, R.σ.BaseFits W s →
        ∀ m ∈ support (R.run1Bounded d oa uf gf s),
          Mid.BaseFits R.π R.σ ch W m ∧
          (match m with | .done _ _ => True | .paused _ _ _ _ k => ∀ u, AllGameQueries qPred (k u)) := by
    intro α d oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro _ uf gf s hs m hm
      simp only [TwoStageCostedReduction.run1Bounded, construct_pure, support_pure,
        Set.mem_singleton_iff] at hm
      subst hm; exact ⟨hs, trivial⟩
    | query_bind q mx ih =>
      intro hqp' uf gf s hs m hm
      simp only [AllGameQueries, construct_query_bind] at hqp'
      cases q with
      | inl n =>
        cases uf with
        | zero =>
          simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind, support_pure,
            Set.mem_singleton_iff] at hm
          subst hm; exact ⟨hs, trivial⟩
        | succ uf' =>
          simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind,
            mem_support_bind_iff] at hm
          obtain ⟨u, -, hm⟩ := hm
          exact ih u (hqp'.2 u) uf' gf s hs m hm
      | inr t =>
        cases gf with
        | zero =>
          simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind, support_pure,
            Set.mem_singleton_iff] at hm
          subst hm; exact ⟨hs, trivial⟩
        | succ gf' =>
          simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind,
            mem_support_bind_iff] at hm
          obtain ⟨res, hstep, hm⟩ := hm
          have hres := Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.handlePre
            (.cons s (.cons (C.qenc t) .nil)) ⟨hs, henc t hqp'.1, trivial⟩ res hstep
          rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
          · exact ih (C.rdec t v) (hqp'.2 _) uf gf' s' hres.2 m hm
          · simp only [support_pure, Set.mem_singleton_iff] at hm
            subst hm; exact ⟨⟨hres.1, hres.2.1, hres.2.2⟩, hqp'.2⟩
  intro y hy
  simp only [TwoStageCostedReduction.eval1Bounded, mem_support_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, m, hm, hy⟩ := hy
  have h0 := (Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.init (.cons x .nil)
    ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have hmPair := hRun1 dflt (hqp oAdv) uFuel gFuel s₀ h0 m hm
  cases m with
  | done b s' =>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.chDone
      (.cons s' (.cons b .nil)) ⟨hmPair.1, hA b, trivial⟩ c hc
    exact ⟨hc', hmPair.1, trivial⟩
  | paused t c p s' k =>
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hmPair.1.1, hmPair.1, hmPair.2⟩

theorem TwoStageCostedReduction.baseFits_eval2_on {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {W_op W_samp W : ℕ} (hO : OpsBaseBounded O W_op) (hS : SampBaseBounded I.smp W_samp)
    (hWop : W_op ≤ W) (hWsamp : W_samp ≤ W)
    (hq : ∀ g x u, (I.cod g).BaseFits W (I.dec g x u))
    {qPred : κ → Prop} (henc : C.BaseFitsOn qPred W)
    (hA : ∀ v : aOut.denote, aOut.BaseFits W v)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote)
    (hm : Mid.BaseFits R.π R.σ ch W m)
    (hmQp : match m with | .done _ _ => True | .paused _ _ _ _ k => ∀ u, AllGameQueries qPred (k u))
    (y : rIn2.denote) (hy : rIn2.BaseFits W y) (uFuel₂ gFuel₂ : ℕ) (dflt : aOut.denote) :
    ∀ z ∈ support (R.eval2Bounded m y uFuel₂ gFuel₂ dflt), out.BaseFits W z := by
  have hRunFuel : ∀ {α : Type} (d : α) {oa : OracleComp (unifSpec + G) α},
      AllGameQueries qPred oa → ∀ uf gf s, R.σ.BaseFits W s →
        ∀ r ∈ support (runFuelBounded R.handlePost d oa uf gf s), R.σ.BaseFits W r.2 := by
    intro α d oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro _ uf gf s hs r hr
      simp only [runFuelBounded, construct_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs
    | query_bind q mx ih =>
      intro hqp' uf gf s hs r hr
      simp only [AllGameQueries, construct_query_bind] at hqp'
      cases q with
      | inl n =>
        cases uf with
        | zero =>
          simp only [runFuelBounded, construct_query_bind, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hs
        | succ uf' =>
          simp only [runFuelBounded, construct_query_bind, mem_support_bind_iff] at hr
          obtain ⟨u, -, hr⟩ := hr
          exact ih u (hqp'.2 u) uf' gf s hs r hr
      | inr t =>
        cases gf with
        | zero =>
          simp only [runFuelBounded, construct_query_bind, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hs
        | succ gf' =>
          simp only [runFuelBounded, construct_query_bind, mem_support_bind_iff] at hr
          obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
          have hs' := (Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.handlePost
            (.cons s (.cons (C.qenc t) .nil)) ⟨hs, henc t hqp'.1, trivial⟩ (v, s') hstep).2
          exact ih (C.rdec t v) (hqp'.2 _) uf gf' s' hs' r hr
  intro z hz
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2Bounded, pure_bind] at hz
    exact Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.finish
      (.cons s (.cons b (.cons y .nil))) ⟨hm, hA b, hy, trivial⟩ z hz
  | paused t c p s k =>
    simp only [TwoStageCostedReduction.eval2Bounded, mem_support_bind_iff] at hz
    obtain ⟨⟨v, s₁⟩, hres, ⟨b, s₂⟩, hrun, hz⟩ := hz
    have hs₁ := (Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.resume
      (.cons s (.cons p (.cons y .nil))) ⟨hm.2.2, hm.2.1, hy, trivial⟩ (v, s₁) hres).2
    have hs₂ := hRunFuel dflt (hmQp (C.rdec t v)) uFuel₂ gFuel₂ s₁ hs₁ (b, s₂) hrun
    exact Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.finish
      (.cons s₂ (.cons b (.cons y .nil))) ⟨hs₂, hA b, hy, trivial⟩ z hz

end TwoStageHardening

/-! ## Counterexample witnesses -/

section CounterexamplesAndCappedOps

/-- Minimal byte-string signature counting 32-byte blocks. -/
def byteBlockSig : Sig where
  Base := Unit
  den := fun _ => List (BitVec 8)
  sz := fun _ bs => (bs.length + 31) / 32

def rawBytesCodec : GameCodec byteBlockSig (fun (_ : List (BitVec 8)) => Bool) where
  Q := .base ()
  R := .bool
  qenc := id
  rdec := fun _ b => b
  codecCost := 1

/-- For `rawBytesCodec`, the unconditioned global codec premise `∀ t, C.Q.Fits qB (C.qenc t)` is
false for every `qB`. -/
theorem global_fits_false_on_bytes (qB : ℕ) :
    ¬ (∀ t : List (BitVec 8), rawBytesCodec.Q.Fits qB (rawBytesCodec.qenc t)) := by
  intro h
  have hbad := h (List.replicate (32 * (qB + 1)) (0#8))
  simp only [rawBytesCodec, Ty.Fits, byteBlockSig, List.length_replicate, id_eq] at hbad
  omega

theorem fitsOn_bytes_capped (maxBlocks : ℕ) :
    rawBytesCodec.FitsOn (fun bs => bs.length ≤ 32 * maxBlocks) maxBlocks := by
  intro bs hbs
  simp only [rawBytesCodec, Ty.Fits, byteBlockSig, id_eq]
  omega

/-- Depth-2 nested list satisfying `Ty.Fits B` whose serialized `treeBlocks` exceeds `B * B`. -/
theorem nested_list_quadratic_treeBlocks {S : Sig} (B : ℕ) :
    let t : Ty S := .list (.list .unit)
    let v : t.denote := List.replicate B (List.replicate B ())
    t.Fits B v ∧ B * B < t.treeBlocks v := by
  refine ⟨?_, ?_⟩
  · refine ⟨by simp, fun row hrow => ?_⟩
    rw [List.mem_replicate] at hrow
    rcases hrow with ⟨_, rfl⟩
    exact ⟨by simp, fun _ _ => trivial⟩
  · simp only [Ty.treeBlocks, List.map_replicate, List.sum_replicate, smul_eq_mul, mul_one]
    have hr : 1 + B * (1 + B) = B * B + B + 1 := by ring
    omega

/-- Untrusted association-list model of `Ty.tbl` (default value plus newest-first writes), not
linked to `Comp.costWithTbl`. -/
structure AssocTable (α : Type) where
  defaultVal : α
  entries : List (ℕ × α)

def AssocTable.lookup {α : Type} (tbl : AssocTable α) (i : ℕ) : α :=
  match tbl.entries.find? (fun p => p.1 == i) with
  | some (_, v) => v
  | none => tbl.defaultVal

def AssocTable.update {α : Type} (tbl : AssocTable α) (i : ℕ) (v : α) : AssocTable α :=
  ⟨tbl.defaultVal, (i, v) :: tbl.entries⟩

theorem AssocTable.lookup_update_self {α : Type} (tbl : AssocTable α) (i : ℕ) (v : α) :
    (tbl.update i v).lookup i = v := by
  simp [AssocTable.lookup, AssocTable.update]

theorem AssocTable.lookup_update_ne {α : Type} (tbl : AssocTable α) {i j : ℕ} (h : i ≠ j) (v : α) :
    (tbl.update i v).lookup j = tbl.lookup j := by
  have hbeq : (i == j) = false := beq_false_of_ne h
  simp [AssocTable.lookup, AssocTable.update, hbeq]

def AssocTable.seqScanSteps {α : Type} (W_entry : ℕ) (tbl : AssocTable α) : ℕ :=
  (tbl.entries.length + 1) * W_entry

theorem AssocTable.seqScanSteps_after_writes {α : Type} (W_entry : ℕ) (a₀ : α) :
    ∀ (writes : List (ℕ × α)),
      let tbl : AssocTable α :=
        writes.foldl (fun (acc : AssocTable α) p => acc.update p.1 p.2) ⟨a₀, []⟩
      tbl.seqScanSteps W_entry = (writes.length + 1) * W_entry := by
  intro writes
  suffices hlen : ∀ (ws : List (ℕ × α)) (init : AssocTable α),
      (ws.foldl (fun (acc : AssocTable α) p => acc.update p.1 p.2) init).entries.length =
        init.entries.length + ws.length by
    dsimp only
    rw [AssocTable.seqScanSteps, hlen writes ⟨a₀, []⟩]
    simp
  intro ws
  induction ws with
  | nil => intro init; simp
  | cons p ws ih =>
    intro init
    rw [List.foldl_cons, ih (init.update p.1 p.2)]
    simp only [AssocTable.update, List.length_cons]
    omega

/-! ## List-length cap helpers -/

def withinCap {α : Type} (cap : ℕ) (xs : List α) : Bool :=
  (xs.drop cap).isEmpty

/-- Cell-visit count for `withinCap` (not tied to a machine step semantics). -/
def withinCapCells {α : Type} : ℕ → List α → ℕ
  | 0, _ => 1
  | _ + 1, [] => 1
  | k + 1, _ :: xs => 1 + withinCapCells k xs

theorem withinCap_iff_length_le {α : Type} (cap : ℕ) (xs : List α) :
    withinCap cap xs = true ↔ xs.length ≤ cap := by
  simp [withinCap, List.isEmpty_iff, List.drop_eq_nil_iff]

theorem withinCap_steps {α : Type} : ∀ (cap : ℕ) (xs : List α),
    withinCapCells cap xs ≤ cap + 1
  | 0, _ => le_rfl
  | _ + 1, [] => by simp [withinCapCells]
  | k + 1, _ :: xs => by
    have ih := withinCap_steps k xs
    simp only [withinCapCells]
    omega

theorem capped_unary_eq_of_le {α β : Type} (f : List α → β) (cap : ℕ) (xs : List α)
    (h : xs.length ≤ cap) :
    f (xs.take cap) = f xs ∧ (xs.take cap).length ≤ cap :=
  ⟨by rw [List.take_of_length_le h], List.length_take_le cap xs⟩

theorem capped_guard_eq_of_le {α β : Type} (f : List α → β) (fallback : β) (cap : ℕ) (xs : List α)
    (h : xs.length ≤ cap) :
    (if withinCap cap xs then f xs else fallback) = f xs := by
  have hw : withinCap cap xs = true := (withinCap_iff_length_le cap xs).2 h
  simp [hw]

theorem capped_eq_check_eq_of_le {α : Type} [BEq α] (m n : ℕ) (xs ys : List α)
    (hx : xs.length ≤ m) (hy : ys.length ≤ n) :
    (withinCap m xs && withinCap n ys && (xs == ys)) = (xs == ys) := by
  have hwx : withinCap m xs = true := (withinCap_iff_length_le m xs).2 hx
  have hwy : withinCap n ys = true := (withinCap_iff_length_le n ys).2 hy
  simp [hwx, hwy]

end CounterexamplesAndCappedOps

end ReductionDsl
