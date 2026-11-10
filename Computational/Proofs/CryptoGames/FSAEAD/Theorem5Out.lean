/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.FSAEAD.HybridOTReal
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5

/-!
# ACD19 Theorem 5 Hops with General Output

Generalizes the `t = 0` chain-PRG hops and multi-slot OT-CCA bridges of `Theorem5On` from the fixed
win predicate `hOut la` to an arbitrary key-free output function `F : Bool → HState → Bool`, so
multi-session reductions can return the adversary's raw output bit (`advBit`).
-/

set_option autoImplicit false

namespace Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

public section

open OracleComp OracleSpec
open MeasureTheory (Measure)
open _root_.CryptoGames (AEADScheme)
open _root_.CryptoGames.Lazy (DEq Idem Comm Rel fillSt map_fillOut)
open _root_.CryptoGames.FSAEAD (RatchetAdversary)
open _root_.CryptoGames.FSAEAD.Thm5.DEq (bind_right_supp)
open _root_.CryptoGames.FSAEAD.Thm5 (Params HState HSt Slot SpecialOps
  hInit implWith multiImplWith hp DG DU isLookaheadHop otOpsWith otImpl slotLift
  hRunWith multiRunWith hybridA cumulativeChainPrgReduction multiSlotOtccaReduction
  multiOtBranch genStep reveal comm_impl seedFill seedFill_idem rc_impl_L2_gen
  eqKnown_simulateQ matFill matFill_idem matFill_keys comm_genStep_mat comm_reveal_mat
  initOStM JM YM JStM jm_impl_ideal jmr_impl sampleKeys length_mem_support_sampleKeys
  implWithK liftK keysFill idem_keysFill comm_implWithK EqNone eqNone_implWithK
  fRM fixHM invM_init fRM_init)

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Output-parameterized hybrids -/

section Defs

variable (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Expresses `hOut la` as a function of the adversary output and final hybrid state. -/
@[expose] def hOutF (la : Bool) (a : Bool) (h : HState CK MK AD M C) : Bool :=
  if la then h.lf else (h.b == a || h.win)

/-- Output selector returning the adversary's `Bool` output directly. -/
@[expose] def advBit (a : Bool) (_h : HState CK MK AD M C) : Bool :=
  a

/-- Runs `implWith` from initial slot `sl` and applies output function `F`. -/
@[expose] def hRunOut {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (sl : Slot CK MK) : m Bool := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : m Bool)
  let z ← (simulateQ (implWith ideal ae G maxSkip P D ops) A).run (hInit b sl)
  pure (F z.1 z.2.1)

/-- Runs `multiImplWith` from initial slot `sl` and applies output function `F`. -/
@[expose] def multiRunOut {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C m)) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (sl : Slot CK MK) : m Bool := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : m Bool)
  let z ← (simulateQ (multiImplWith ideal ae G maxSkip P mSlot D ops) A).run (hInit b sl)
  pure (F z.1 z.2.1)

/-- `hybridA` with output `F`. -/
@[expose] def hybridAOut (k : ℕ) (la : Bool) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) : ProbComp Bool :=
  hRunOut ideal ae G maxSkip (hp k k la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) F A
    .unknown

/-- `cumulativeChainPrgReduction` with output `F`. -/
@[expose] def cumulativeChainPrgReductionOut (j : ℕ) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) : PRGScheme.PRGAdversary (CK × MK) := fun mt =>
  hRunOut ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
    (none : Option (SpecialOps AD M C ProbComp)) F A (.mat (j / 2) mt)

/-- `multiSlotOtccaReduction` with output `F`. -/
@[expose] def multiSlotOtccaReductionOut (N : ℕ) (la : Bool) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) : AEADScheme.OTCCAAdversary (ℕ × AD) M C :=
  multiRunOut ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) F A .unknown

/-- Predicate stating that `F` ignores the hybrid state's message-key list `keys`. -/
@[expose] def OutKeyFree (F : Bool → HState CK MK AD M C → Bool) : Prop :=
  ∀ (a : Bool) (h : HState CK MK AD M C) (ks : List MK), F a { h with keys := ks } = F a h

theorem outKeyFree_hOutF (la : Bool) : OutKeyFree (hOutF (CK := CK) (MK := MK) (AD := AD)
    (M := M) (C := C) la) := by
  intro a h ks
  cases la <;> rfl

theorem outKeyFree_advBit : OutKeyFree (advBit (CK := CK) (MK := MK) (AD := AD)
    (M := M) (C := C)) :=
  fun _ _ _ => rfl

theorem hRunOut_hOutF {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (A : RatchetAdversary CK MK AD M C) (sl : Slot CK MK) :
    hRunOut ideal ae G maxSkip P D ops (hOutF P.la) A sl =
      hRunWith ideal ae G maxSkip P D ops A sl :=
  rfl

theorem multiRunOut_hOutF {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] (P : Params)
    (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (A : RatchetAdversary CK MK AD M C) (sl : Slot CK MK) :
    multiRunOut ideal ae G maxSkip P mSlot D ops (hOutF P.la) A sl =
      multiRunWith ideal ae G maxSkip P mSlot D ops A sl :=
  rfl

theorem hybridAOut_hOutF (k : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C) :
    hybridAOut ideal ae G maxSkip k la (hOutF la) A = hybridA ideal ae G maxSkip k la A :=
  rfl

theorem cumulativeChainPrgReductionOut_hOutF (j : ℕ) (A : RatchetAdversary CK MK AD M C) :
    cumulativeChainPrgReductionOut ideal ae G maxSkip j (hOutF (isLookaheadHop j)) A =
      cumulativeChainPrgReduction ideal ae G maxSkip j A :=
  rfl

theorem multiSlotOtccaReductionOut_hOutF (N : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C) :
    multiSlotOtccaReductionOut ideal ae G maxSkip N la (hOutF la) A =
      multiSlotOtccaReduction ideal ae G maxSkip N la A :=
  rfl

end Defs

/-! ## Chain-PRG hops and multi-slot OT-CCA bridges -/

section BridgesOut

local notation "St" => HSt CK MK AD M C

variable (ideal : (ℕ × AD) → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK))
  (maxSkip : ℕ)
  (F : Bool → HState CK MK AD M C → Bool)

private theorem hRunOut_eq (A : RatchetAdversary CK MK AD M C) (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (sl : Slot CK MK) :
    hRunOut ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) F A sl =
      ($ᵗ Bool : ProbComp Bool) >>= fun b =>
        (fun z => F z.1 z.2.1) <$>
          (simulateQ (implWith ideal ae G maxSkip P D none) A).run (hInit b sl) := by
  simp only [hRunOut, map_eq_bind_pure_comp]
  rfl

private theorem out_fill (A : RatchetAdversary CK MK AD M C) (P : Params)
    (D : ℕ → ProbComp (CK × MK))
    {fill : HState CK MK AD M C → Slot CK MK → ProbComp (Slot CK MK)} (hI : Idem fill)
    (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length → fill h = fill h')
    (hGen : Comm fill (genStep G P D : StateT St ProbComp Unit))
    (hRev : Comm fill (reveal : StateT St ProbComp CK)) (s : St) :
    DEq ((fun z => F z.1 z.2.1) <$> (fillSt fill s >>=
        (simulateQ (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)))
          A).run))
      ((fun z => F z.1 z.2.1) <$> (simulateQ (implWith ideal ae G maxSkip P D none) A).run s) := by
  have hc := Comm.simulateQ hI (comm_impl ideal ae G maxSkip P D hI hK hGen hRev) A s
  exact (map_fillOut (fill := fill) F _).symm.trans
    ((DEq.map hc _).trans (map_fillOut (fill := fill) F _))

private theorem out_L2_gen (A : RatchetAdversary CK MK AD M C) (k t₀ : ℕ) (la : Bool) (b : Bool) :
    DEq ((fun z => F z.1 z.2.1) <$> (simulateQ (implWith ideal ae G maxSkip (hp k t₀ la) DU
        (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown))
      ((fun z => F z.1 z.2.1) <$> (simulateQ (implWith ideal ae G maxSkip (hp (k + 1) t₀ la)
        (DG G) (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown)) := by
  have hI := seedFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1)
  have hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length →
      seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1) h =
        seedFill (k + 1) h' := by
    intro h h' hl; funext sl; cases sl <;> simp [seedFill, hl]
  have hr := Rel.simulateQ hI (fun t => (rc_impl_L2_gen ideal ae G maxSkip k t₀ la hI hK t).1)
    (fun t => (rc_impl_L2_gen ideal ae G maxSkip k t₀ la hI hK t).2) A (hInit b .unknown)
  have h0 : fillSt (seedFill (k + 1)) (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
      b .unknown) = pure (hInit b .unknown) := by
    simp [fillSt, seedFill, hInit]
  rw [h0, pure_bind, pure_bind] at hr
  exact (DEq.map hr _).trans (map_fillOut (fill := seedFill (k + 1)) F _)

private theorem hRunOut_mat_eq (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK))
    (A : RatchetAdversary CK MK AD M C) (pos : ℕ) (mt : CK × MK) :
    hRunOut ideal ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) F A (.mat pos mt) =
      hRunOut ideal ae G maxSkip P D₂ (none : Option (SpecialOps AD M C ProbComp)) F A
        (.mat pos mt) := by
  unfold hRunOut
  refine bind_congr fun b => ?_
  exact eqKnown_simulateQ ideal ae G maxSkip P D₁ D₂ A (hInit b (.mat pos mt)) _ _
    (by simp [hInit]) (fun _ _ => rfl)

theorem hybZero_eq_prgRealOut (A : RatchetAdversary CK MK AD M C) (j : ℕ) :
    𝒟[hRunOut ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F A .unknown] =
      𝒟[(G (j / 2)).prgRealExperiment (cumulativeChainPrgReductionOut ideal ae G maxSkip j F A)] := by
  refine DEq.evalDist_eq ?_
  unfold PRGScheme.prgRealExperiment cumulativeChainPrgReductionOut
  simp only [hRunOut_eq]
  refine DEq.symm ((DEq.swap _ _ _).trans (DEq.bind_right _ fun b => ?_))
  set P := hp (j / 2) 0 (isLookaheadHop j)
  have hI := matFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (j / 2) (DG G)
  have h := out_fill ideal ae G maxSkip F A P (DG G) hI (matFill_keys _ _)
    (comm_genStep_mat G P (DG G)) (comm_reveal_mat (j / 2) (DG G)) (hInit b .unknown)
  refine DEq.trans ?_ h
  simp only [fillSt, matFill, hInit, DG, List.length_nil, Nat.max_zero, map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply, pure_bind]
  exact DEq.refl _

theorem prgIdeal_eq_hybZero_succOut (A : RatchetAdversary CK MK AD M C) (j : ℕ) :
    𝒟[PRGScheme.prgIdealExperiment (cumulativeChainPrgReductionOut ideal ae G maxSkip j F A)] =
      𝒟[hRunOut ideal ae G maxSkip (hp (j / 2 + 1) 0 (isLookaheadHop j)) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) F A .unknown] := by
  refine DEq.evalDist_eq ?_
  unfold PRGScheme.prgIdealExperiment cumulativeChainPrgReductionOut
  have heq : ∀ mt,
      hRunOut ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) F A (.mat (j / 2) mt) =
        hRunOut ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) DU
          (none : Option (SpecialOps AD M C ProbComp)) F A (.mat (j / 2) mt) :=
    hRunOut_mat_eq ideal ae G maxSkip F (hp (j / 2) 0 (isLookaheadHop j)) (DG G) DU A (j / 2)
  simp only [heq, hRunOut_eq]
  refine (DEq.swap _ _ _).trans (DEq.bind_right _ fun b => ?_)
  set k := j / 2
  set la := isLookaheadHop j
  set P := hp k 0 la
  have hI := matFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) k DU
  have hfill := out_fill ideal ae G maxSkip F A P DU hI (matFill_keys _ _)
    (comm_genStep_mat G P DU) (comm_reveal_mat k DU) (hInit b .unknown)
  have hprod : ($ᵗ (CK × MK) : ProbComp (CK × MK)) =
      (do let w ← $ᵗ CK; let K ← $ᵗ MK; pure (w, K)) := by
    simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply]
    rfl
  have hfill' : DEq
      (($ᵗ (CK × MK)) >>= fun x =>
        (fun z => F z.1 z.2.1) <$>
          (simulateQ (implWith ideal ae G maxSkip P DU none) A).run (hInit b (.mat k x)))
      ((fun z => F z.1 z.2.1) <$>
        (simulateQ (implWith ideal ae G maxSkip P DU none) A).run (hInit b .unknown)) := by
    refine DEq.trans ?_ hfill
    rw [hprod]
    simp only [fillSt, matFill, hInit, DU, List.length_nil, Nat.max_zero, map_eq_bind_pure_comp,
      bind_assoc, Function.comp_apply, pure_bind]
    exact DEq.refl _
  exact hfill'.trans (out_L2_gen ideal ae G maxSkip F A k 0 la b)

/-- Single chain-PRG hop distance bound at `t = 0` for output `F`. -/
theorem hop_prg_zero_leOut (A : RatchetAdversary CK MK AD M C) (j : ℕ) :
    𝒟[hRunOut ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F A .unknown].boolDist
      𝒟[hRunOut ideal ae G maxSkip (hp (j / 2 + 1) 0 (isLookaheadHop j)) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) F A .unknown] ≤
      (G (j / 2)).prgAdvantage (cumulativeChainPrgReductionOut ideal ae G maxSkip j F A) := by
  rw [hybZero_eq_prgRealOut ideal ae G maxSkip F A j,
    ← prgIdeal_eq_hybZero_succOut ideal ae G maxSkip F A j,
    PRGScheme.prgAdvantage]

/-- Cumulative distance bound across `N` chain-PRG hops at `t = 0` for output `F`. -/
theorem chain_prg_zero_leOut (A : RatchetAdversary CK MK AD M C) (la : Bool) (N : ℕ) :
    𝒟[hybridAOut ideal ae G maxSkip 0 la F A].boolDist
      𝒟[hRunOut ideal ae G maxSkip (hp N 0 la) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) F A .unknown] ≤
      ∑ k ∈ Finset.range N,
        (G ((2 * k + la.toNat) / 2)).prgAdvantage
          (cumulativeChainPrgReductionOut ideal ae G maxSkip (2 * k + la.toNat) F A) := by
  unfold hybridAOut
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[hRunOut ideal ae G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F A .unknown]) N).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : (2 * k + la.toNat) / 2 = k := by
    cases la <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have h2 : isLookaheadHop (2 * k + la.toNat) = la := by
    cases la <;> simp [isLookaheadHop, Nat.add_mod]
  have := hop_prg_zero_leOut ideal ae G maxSkip F A (2 * k + la.toNat)
  rw [h1, h2] at this
  rw [h1]
  exact this

/-- In the ideal world (`b = true`), `multiSlotOtccaReductionOut` has the same distribution as `hybridAOut … N la F A`. -/
theorem multiOtBranch_true_eq_hybAOut (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    𝒟[multiOtBranch ideal ae true N (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A)] =
      𝒟[hybridAOut ideal ae G maxSkip N la F A] := by
  refine DEq.evalDist_eq ?_
  unfold multiOtBranch multiSlotOtccaReductionOut multiRunOut hybridAOut
  simp only [hRunOut_eq, simulateQ_bind, simulateQ_pure, slotLift,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind]
  have hsim : ∀ (K₀ : MK) (ks : List MK) (b : Bool),
      DEq
        ((simulateQ (slotLift (otImpl ideal ae))
          ((simulateQ (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G)
            (some (otOpsWith ideal))) A).run (hInit b .unknown))).run
            (initOStM true K₀ ks) >>= fun x => pure (F x.1.1 x.1.2.1))
        ((simulateQ (implWith ideal ae G maxSkip (hp N N la) (DG G) none) A).run
          (hInit b .unknown) >>= fun z => pure (F z.1 z.2.1)) := by
    intro K₀ ks b
    have hJ := (JM.simulateQ (jm_impl_ideal ideal ae G maxSkip N la) A
      (hInit b .unknown, initOStM true K₀ ks) (fun _ => rfl)).1
    have hmap := DEq.map hJ.symm (fun z => F z.1 z.2.1)
    simpa only [YM, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
      Function.comp_apply, bind_assoc, pure_bind] using hmap
  refine (DEq.bind_right _ fun K₀ => DEq.bind_right _ fun ks =>
    DEq.bind_right _ fun b => hsim K₀ ks b).trans ?_
  exact (DEq.bind_const _ _).trans (DEq.bind_const _ _)

private theorem eagerKeys_deq_hRunOut (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    DEq
      (do
        let ks ← sampleKeys N
        let b ← $ᵗ Bool
        let z ← (simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run
          (hInit b .unknown, some ks)
        pure (F z.1 z.2.1.1))
      (hRunOut ideal ae G maxSkip (hp N 0 la) (DG G) none F A .unknown) := by
  unfold hRunOut
  refine (DEq.swap (sampleKeys N) ($ᵗ Bool) _).trans ?_
  refine DEq.bind_right ($ᵗ Bool) fun b => ?_
  have hcomm := Comm.simulateQ (idem_keysFill N)
    (comm_implWithK ideal ae G maxSkip (hp N 0 la) (DG G)) A (hInit b .unknown, none)
  have hfill1 := (map_fillOut (fill := keysFill N) (fun a h => F a h.1)
    (fillSt (keysFill N) (hInit b .unknown, none) >>=
      (simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run)).symm
  have hfill2 := map_fillOut (fill := keysFill N) (fun a h => F a h.1)
    ((simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run
      (hInit b .unknown, none))
  have hchain := (hfill1.trans (DEq.map hcomm (fun a => F a.1 a.2.1.1))).trans hfill2
  have heq := EqNone.simulateQ (eqNone_implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none)
    A (hInit b .unknown)
  have hfillInit : fillSt (keysFill N) (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
      b .unknown, none) = (fun ks => (hInit b .unknown, some ks)) <$> sampleKeys N := by
    simp [fillSt, keysFill, hInit, Functor.map_map]
  rw [hfillInit, heq] at hchain
  simpa only [liftK, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
    Function.comp_apply, bind_assoc, pure_bind] using hchain

private theorem out_fRM (hF : OutKeyFree F) (N : ℕ) (a : Bool) (σ : JStM CK MK AD M C) :
    F a (fRM N σ).1.1 = F a σ.1.1 := by
  simp only [fRM, fixHM]
  exact hF _ _ _

/-- For key-free `F`, `multiSlotOtccaReductionOut` in the real world (`b = false`) matches `hRunOut` at `hp N 0 la`. -/
theorem multiOtBranch_false_eq_hRunOut (hF : OutKeyFree F) (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    𝒟[multiOtBranch ideal ae false N (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A)] =
      𝒟[hRunOut ideal ae G maxSkip (hp N 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) F A .unknown] := by
  refine DEq.evalDist_eq ?_
  refine DEq.trans ?_ (eagerKeys_deq_hRunOut ideal ae G maxSkip F N la A)
  unfold multiOtBranch multiSlotOtccaReductionOut multiRunOut
  simp only [simulateQ_bind, simulateQ_pure, slotLift,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind]
  have hsim : ∀ (K₀ : MK) (ks : List MK), ks ∈ support (sampleKeys N) → ∀ (b : Bool),
      DEq
        ((simulateQ (slotLift (otImpl ideal ae))
          ((simulateQ (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G)
            (some (otOpsWith ideal))) A).run (hInit b .unknown))).run
            (initOStM false K₀ ks) >>= fun x => pure (F x.1.1 x.1.2.1))
        ((simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run
          (hInit b .unknown, some ks) >>= fun z => pure (F z.1 z.2.1.1)) := by
    intro K₀ ks hks b
    have hlen : ks.length = N := length_mem_support_sampleKeys hks
    have hJ := (JM.simulateQ (jmr_impl ideal ae G maxSkip N la) A
      (hInit b .unknown, initOStM false K₀ ks) (invM_init N la b K₀ ks)).1
    have hinit : fRM N (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown,
        initOStM false K₀ ks) = (hInit b .unknown, some ks) := by
      rw [← hlen, fRM_init]
    rw [hinit] at hJ
    have hmap := DEq.map hJ.symm (fun z => F z.1 z.2.1.1)
    simpa only [YM, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
      Function.comp_apply, bind_assoc, pure_bind, out_fRM F hF] using hmap
  refine (DEq.bind_right ($ᵗ MK) fun K₀ =>
    bind_right_supp (sampleKeys N) fun ks hks =>
      DEq.bind_right ($ᵗ Bool) fun b => hsim K₀ ks hks b).trans ?_
  exact DEq.bind_const ($ᵗ MK) _

/-- Bounds the distance from `hybridAOut 0` to `hybridAOut N` for key-free `F` by `N` chain-PRG hops plus one multi-slot OT-CCA hop. -/
theorem chain_le_out (hF : OutKeyFree F) (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    𝒟[hybridAOut ideal ae G maxSkip 0 la F A].boolDist
        𝒟[hybridAOut ideal ae G maxSkip N la F A] ≤
      (∑ k ∈ Finset.range N,
        (G ((2 * k + la.toNat) / 2)).prgAdvantage
          (cumulativeChainPrgReductionOut ideal ae G maxSkip (2 * k + la.toNat) F A)) +
        𝒟[multiOtBranch ideal ae true N
            (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A)].boolDist
          𝒟[multiOtBranch ideal ae false N
            (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A)] := by
  refine (Measure.boolDist_triangle
    𝒟[hybridAOut ideal ae G maxSkip 0 la F A]
    𝒟[hRunOut ideal ae G maxSkip (hp N 0 la) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) F A .unknown]
    𝒟[hybridAOut ideal ae G maxSkip N la F A]).trans ?_
  refine add_le_add (chain_prg_zero_leOut ideal ae G maxSkip F A la N) ?_
  rw [← multiOtBranch_false_eq_hRunOut ideal ae G maxSkip F hF,
    ← multiOtBranch_true_eq_hybAOut,
    Measure.boolDist_comm]

end BridgesOut

end

end Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
