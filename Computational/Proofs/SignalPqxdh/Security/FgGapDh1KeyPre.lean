/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkCoupling
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpkCoupling
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# One-Key `GapDhWithSign` Pre-Sampling and Pure Simulation

Provides pure `ProbComp` counterparts, signing/DDH query-budget bounds, and upfront scalar
pre-sampling equivalences (`dh1`–`dh4`) for the four-leg Fiedler-Günther `G3 → G3.5` hop in the
one-key `KeyInd` game (`runKeyIndFgSim1Key`). Also bounds `ValidSpkBundles` length by `S.N_spk_tot`
and proves that `fgKeyIndStepPure` commutes with clearing `secIKAsign` at the target principal.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.FgGapDh1Key

/-- Randomized XEdDSA signing-oracle implementation under challenge scalar `uSk`. -/
def gapDhSigImpl (P : Primitives) (uSk : Bytes) : QueryImpl sigOracleSpec ProbComp :=
  fun (.sign m) => do
    let r ← sampleRandom64
    return P.sigSign uSk m r

/-- Full `GdhSignSimSpec = PrimBaseSpec + (sigOracleSpec + gapDhOracleSpec)` interpreter matching
    `gapDhWithSignExp`. -/
def gapDhWithSignFullImpl (P : Primitives) (uSk : Bytes)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) : QueryImpl GdhSignSimSpec ProbComp :=
  primBaseImpl P + (gapDhSigImpl P uSk + gapDhDdhImpl isValidDhTriple)

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_liftGdhToSign {α : Type}
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (mx : OracleComp GdhSimSpec α) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (liftGdhToSign mx) =
      simulateQ (gapDhFullImpl P ddh) mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    cases q with
    | inl bq =>
      change simulateQ (gapDhWithSignFullImpl P uSk ddh)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
            fun u => liftGdhToSign (k u)) =
        simulateQ (gapDhFullImpl P ddh)
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl bq)) >>= k)
      rw [simulateQ_bind, simulateQ_bind]
      have hq : simulateQ (gapDhWithSignFullImpl P uSk ddh)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq))) =
          simulateQ (gapDhFullImpl P ddh)
            (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl bq))) := by
        simp [gapDhWithSignFullImpl, gapDhFullImpl]
      rw [hq]
      congr 1; funext u; exact ih u
    | inr dq =>
      change simulateQ (gapDhWithSignFullImpl P uSk ddh)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
            fun u => liftGdhToSign (k u)) =
        simulateQ (gapDhFullImpl P ddh)
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inr dq)) >>= k)
      rw [simulateQ_bind, simulateQ_bind]
      have hq : simulateQ (gapDhWithSignFullImpl P uSk ddh)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq)))) =
          simulateQ (gapDhFullImpl P ddh)
            (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inr dq))) := by
        simp [gapDhWithSignFullImpl, gapDhFullImpl]
      rw [hq]
      congr 1; funext u; exact ih u

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_unifGdhSign {α : Type}
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (mx : ProbComp α) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (unifGdhSign mx) = mx := by
  unfold unifGdhSign
  rw [simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_unifGdh]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_primGdhSignQ
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (op : PrimQuery) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (primGdhSignQ op) = primImpl P op := by
  unfold primGdhSignQ gapDhWithSignFullImpl
  simp [primBaseImpl]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    simulateQ (α := Bytes) (gapDhWithSignFullImpl P uSk ddh) (primGdhSignQ (.x25519Base sk)) =
      pure (P.x25519Base sk) := by
  rw [simulateQ_gapDhWithSignFullImpl_primGdhSignQ]; rfl

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (seed : Bytes) :
    simulateQ (α := Bytes × Bytes) (gapDhWithSignFullImpl P uSk ddh)
      (primGdhSignQ (.kemKeyGen seed)) = pure (P.kemKeyGen seed) := by
  rw [simulateQ_gapDhWithSignFullImpl_primGdhSignQ]; rfl

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_sigChalQ
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (msg : Bytes) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (sigChalQ msg) =
      (sampleRandom64 >>= fun r => pure (P.sigSign uSk msg r)) := by
  unfold sigChalQ gapDhWithSignFullImpl gapDhSigImpl
  simp

@[simp]
theorem runWithGdhSignStep_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSignSimSpec (GSpec.Range q × St))
    (a : α) (st : St) :
    runWithGdhSignStep step (pure a) st = pure (a, st) := rfl

@[simp]
theorem runWithGdhSignStep_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSignSimSpec (GSpec.Range q × St))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithGdhSignStep step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) st =
      (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => runWithGdhSignStep step (mx u) st) := rfl

@[simp]
theorem runWithGdhSignStep_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSignSimSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithGdhSignStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) st =
      (step gq st >>= fun p => runWithGdhSignStep step (mx p.1) p.2) := rfl

theorem isQueryBoundP_liftGdhToSign_sig {α : Type} (mx : OracleComp GdhSimSpec α) (n : ℕ) :
    IsQueryBoundP (liftGdhToSign mx) (fun q => isSigChalQuery q = true) n := by
  induction mx using OracleComp.inductionOn generalizing n with
  | pure a => simp [liftGdhToSign]
  | query_bind q k ih =>
    cases q with
    | inl bq =>
      change IsQueryBoundP
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (k u))
        (fun q => isSigChalQuery q = true) n
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u n⟩
    | inr dq =>
      change IsQueryBoundP
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (k u))
        (fun q => isSigChalQuery q = true) n
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u n⟩

theorem isQueryBoundP_unifGdhSign_sig {α : Type} (mx : ProbComp α) (n : ℕ) :
    IsQueryBoundP (unifGdhSign mx) (fun q => isSigChalQuery q = true) n :=
  isQueryBoundP_liftGdhToSign_sig (unifGdh mx) n

private theorem sigQb_pure {α : Type} (a : α) :
    IsQueryBoundP (pure a : OracleComp GdhSignSimSpec α) (fun q => isSigChalQuery q = true) 0 :=
  isQueryBoundP_pure _ a 0

private theorem sigQb_bind0 {α β : Type} {mx : OracleComp GdhSignSimSpec α}
    {k : α → OracleComp GdhSignSimSpec β} {n : ℕ}
    (h1 : IsQueryBoundP mx (fun q => isSigChalQuery q = true) 0)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (k x) (fun q => isSigChalQuery q = true) n) :
    IsQueryBoundP (mx >>= k) (fun q => isSigChalQuery q = true) n := by
  simpa using isQueryBoundP_bind h1 h2

private theorem sigQb_bind1 {α β : Type} {mx : OracleComp GdhSignSimSpec α}
    {k : α → OracleComp GdhSignSimSpec β} {n : ℕ}
    (h1 : IsQueryBoundP mx (fun q => isSigChalQuery q = true) 1)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (k x) (fun q => isSigChalQuery q = true) n) :
    IsQueryBoundP (mx >>= k) (fun q => isSigChalQuery q = true) (1 + n) :=
  isQueryBoundP_bind h1 h2

theorem isQueryBoundP_primGdhSignQ_sig (op : PrimQuery) (n : ℕ) :
    IsQueryBoundP (primGdhSignQ op) (fun q => isSigChalQuery q = true) n :=
  ((isQueryBoundP_query_iff (spec := GdhSignSimSpec) (fun q => isSigChalQuery q = true)
    (Sum.inl (Sum.inr op)) 0).2 (fun h => by cases h)).mono (Nat.zero_le n)

theorem isQueryBoundP_sigChalQ_sig (msg : Bytes) :
    IsQueryBoundP (sigChalQ msg) (fun q => isSigChalQuery q = true) 1 :=
  (isQueryBoundP_query_iff (spec := GdhSignSimSpec) (fun q => isSigChalQuery q = true)
    (Sum.inr (Sum.inl (.sign msg))) 1).2 (fun _ => Nat.zero_lt_one)

/-- Step-level signing-budget accounting invariant: a step consumes `k <= st.sigBudget` units of
    `sigBudget` and issues at most `2 * k` challenger `.sign` queries. -/
def SigBudgetStepInv {S : Setup} {R : Type}
    (m : OracleComp GdhSignSimSpec (R × FgKeyInd1KeySimState S)) (b : ℕ) : Prop :=
  ∃ k ≤ b,
    IsQueryBoundP m (fun q => isSigChalQuery q = true) (2 * k) ∧
    ∀ x ∈ support m, x.2.sigBudget ≤ b - k

theorem sigBudgetStepInv_liftSimStep1Key {S : Setup}
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (st : FgKeyInd1KeySimState S) :
    SigBudgetStepInv (liftSimStep1Key f st) st.sigBudget := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · unfold liftSimStep1Key
    exact (isQueryBoundP_bind (isQueryBoundP_liftGdhToSign_sig (f st.sim) 0)
      (fun _ _ => sigQb_pure _)).mono (by omega)
  · intro x hx
    unfold liftSimStep1Key at hx
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨_, _⟩, _, rfl⟩
    dsimp only; omega

theorem sigBudgetStepInv_fgInitPrin1KeyGdh {S : Setup}
    (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes) (u : Fin S.N_id)
    (st : FgKeyInd1KeySimState S) :
    SigBudgetStepInv (fgInitPrin1KeyGdh prinFlag prinIdx Up u st) st.sigBudget := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · unfold fgInitPrin1KeyGdh
    by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hAny, ↓reduceIte]
      exact sigQb_pure _
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      refine sigQb_bind0 (isQueryBoundP_unifGdhSign_sig sampleScalar32 0) (fun sk0 _ => ?_)
      exact sigQb_bind0 (isQueryBoundP_primGdhSignQ_sig (.x25519Base sk0) 0)
        (fun _ _ => sigQb_pure _)
  · intro x hx
    unfold fgInitPrin1KeyGdh at hx
    by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [hAny] at hx; subst hx; dsimp only; omega
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨_, _, _, _, rfl⟩
      dsimp only; omega

theorem sigBudgetStepInv_fgGenSPK1KeyGdh (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyInd1KeySimState S) :
    SigBudgetStepInv
      (fgGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st)
      st.sigBudget := by
  unfold fgGenSPK1KeyGdh
  by_cases hPrin : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hPrin, ↓reduceIte]
    by_cases hAny : (st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · simp only [hAny, ↓reduceIte]; exact sigQb_pure _
      · intro x hx; simp [hAny] at hx; subst hx; dsimp only; omega
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      cases hFind : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        refine ⟨0, Nat.zero_le _, sigQb_pure _, ?_⟩
        intro x hx; simp at hx; subst hx; dsimp only; omega
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        by_cases hZero : (st.sigBudget == 0) = true
        · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
          · simp only [hZero, ↓reduceIte]; exact sigQb_pure _
          · intro x hx; simp [hZero] at hx; subst hx; dsimp only; omega
        · have hPos : 1 ≤ st.sigBudget := by
            have hNe : st.sigBudget ≠ 0 := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hZero)
            omega
          simp only [hZero, Bool.false_eq_true, ↓reduceIte]
          refine ⟨1, hPos, ?_, ?_⟩
          · refine sigQb_bind0 (isQueryBoundP_unifGdhSign_sig sampleScalar32 0)
              (fun spkSkRaw _ => ?_)
            refine sigQb_bind0 (isQueryBoundP_primGdhSignQ_sig (.x25519Base spkSkRaw) 0)
              (fun spkPkRaw _ => ?_)
            change IsQueryBoundP _ _ (1 + (1 + 0))
            refine sigQb_bind1 (isQueryBoundP_sigChalQ_sig _) (fun _ _ => ?_)
            refine sigQb_bind0 (isQueryBoundP_unifGdhSign_sig sampleRandom64 0)
              (fun seedKem _ => ?_)
            refine sigQb_bind0 (isQueryBoundP_primGdhSignQ_sig (.kemKeyGen seedKem) 0)
              (fun pqPair _ => ?_)
            exact sigQb_bind1 (isQueryBoundP_sigChalQ_sig _) (fun _ _ => sigQb_pure _)
          · intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨_, _, _, _, _, _, _, _, ⟨_, _⟩, _, _, _, rfl⟩
            dsimp only; omega
  · simp only [hPrin, Bool.false_eq_true, ↓reduceIte]
    exact sigBudgetStepInv_liftSimStep1Key _ st

theorem isQueryBoundP_runWithGdhSignStep_sig {S : Setup} {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {α : Type}
    (step : (q : ιI) → FgKeyInd1KeySimState S →
      OracleComp GdhSignSimSpec (GSpec.Range q × FgKeyInd1KeySimState S))
    (h_step : ∀ gq st, SigBudgetStepInv (step gq st) st.sigBudget)
    (mx : OracleComp (unifSpec + GSpec) α) (st : FgKeyInd1KeySimState S) :
    IsQueryBoundP (runWithGdhSignStep step mx st)
      (fun q => isSigChalQuery q = true) (2 * st.sigBudget) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => simp [runWithGdhSignStep_pure]
  | query_bind q r ih =>
    cases q with
    | inl n =>
      rw [runWithGdhSignStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u st⟩
    | inr gq =>
      rw [runWithGdhSignStep_query_inr]
      rcases h_step gq st with ⟨k, hkLe, hQbStep, hSup⟩
      have hCont : ∀ p ∈ support (step gq st),
          IsQueryBoundP (runWithGdhSignStep step (r p.1) p.2)
            (fun q => isSigChalQuery q = true) (2 * (st.sigBudget - k)) :=
        fun p hp => (ih p.1 p.2).mono (by have := hSup p hp; omega)
      exact (isQueryBoundP_bind hQbStep hCont).mono (by omega)

theorem sigBudgetStepInv_fgKeyInd1KeyStep (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    SigBudgetStepInv (fgKeyInd1KeyStep useDh1 targetIdx targetSpkIdx S maxLen U V q st)
      st.sigBudget := by
  cases q with
  | initPrin u => exact sigBudgetStepInv_fgInitPrin1KeyGdh useDh1 targetIdx U u st
  | genSPK u j =>
    exact sigBudgetStepInv_fgGenSPK1KeyGdh useDh1 targetIdx useDh1 targetIdx targetSpkIdx S
      maxLen U V u j st
  | _ => exact sigBudgetStepInv_liftSimStep1Key _ st

theorem sigBudgetStepInv_fgKeyInd1KeyStepIk (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    SigBudgetStepInv (fgKeyInd1KeyStepIk targetIdx targetPrinIdx S maxLen U V q st)
      st.sigBudget := by
  cases q with
  | initPrin u => exact sigBudgetStepInv_fgInitPrin1KeyGdh true targetPrinIdx U u st
  | genSPK u j =>
    exact sigBudgetStepInv_fgGenSPK1KeyGdh true targetPrinIdx false targetIdx
      (FgGapDh.Ik.noSpkIdx S) S maxLen V U u j st
  | _ => exact sigBudgetStepInv_liftSimStep1Key _ st

theorem sigBudgetStepInv_fgKeyInd1KeyStepOpk (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    SigBudgetStepInv (fgKeyInd1KeyStepOpk targetIdx targetOpkIdx S maxLen U V q st)
      st.sigBudget := by
  cases q with
  | initPrin u => exact sigBudgetStepInv_fgInitPrin1KeyGdh false S.N_id U u st
  | genSPK u j =>
    exact sigBudgetStepInv_fgGenSPK1KeyGdh false S.N_id false targetIdx
      (FgGapDh.Opk.noSpkIdx S) S maxLen U V u j st
  | _ => exact sigBudgetStepInv_liftSimStep1Key _ st

theorem isQueryBoundP_fgKeyInd1KeyGapDhRunAt_sig (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgKeyInd1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold fgKeyInd1KeyGapDhRunAt
  refine sigQb_bind0 (isQueryBoundP_unifGdhSign_sig ($ᵗ Bool) 0) (fun secb _ => ?_)
  have hStep : IsQueryBoundP
      (runWithGdhSignStep (fgKeyInd1KeyStep useDh1 targetIdx targetSpkIdx S b.q_total U V)
        A.1.run (FgKeyInd1KeySimState.empty S secb))
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) :=
    isQueryBoundP_runWithGdhSignStep_sig _
      (sigBudgetStepInv_fgKeyInd1KeyStep useDh1 targetIdx targetSpkIdx S b.q_total U V)
      A.1.run (FgKeyInd1KeySimState.empty S secb)
  exact (isQueryBoundP_bind hStep
    (fun p _ => isQueryBoundP_liftGdhToSign_sig _ 0)).mono (by omega)

theorem isQueryBoundP_fgKeyInd1KeyGapDhRunAtIk_sig (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgKeyInd1KeyGapDhRunAtIk targetIdx targetPrinIdx S b A U V)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold fgKeyInd1KeyGapDhRunAtIk
  refine sigQb_bind0 (isQueryBoundP_unifGdhSign_sig ($ᵗ Bool) 0) (fun secb _ => ?_)
  have hStep : IsQueryBoundP
      (runWithGdhSignStep (fgKeyInd1KeyStepIk targetIdx targetPrinIdx S b.q_total U V)
        A.1.run (FgKeyInd1KeySimState.empty S secb))
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) :=
    isQueryBoundP_runWithGdhSignStep_sig _
      (sigBudgetStepInv_fgKeyInd1KeyStepIk targetIdx targetPrinIdx S b.q_total U V)
      A.1.run (FgKeyInd1KeySimState.empty S secb)
  exact (isQueryBoundP_bind hStep
    (fun p _ => isQueryBoundP_liftGdhToSign_sig _ 0)).mono (by omega)

theorem isQueryBoundP_fgKeyInd1KeyGapDhRunAtOpk_sig (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgKeyInd1KeyGapDhRunAtOpk targetIdx targetOpkIdx S b A U V)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold fgKeyInd1KeyGapDhRunAtOpk
  refine sigQb_bind0 (isQueryBoundP_unifGdhSign_sig ($ᵗ Bool) 0) (fun secb _ => ?_)
  have hStep : IsQueryBoundP
      (runWithGdhSignStep (fgKeyInd1KeyStepOpk targetIdx targetOpkIdx S b.q_total U V)
        A.1.run (FgKeyInd1KeySimState.empty S secb))
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) :=
    isQueryBoundP_runWithGdhSignStep_sig _
      (sigBudgetStepInv_fgKeyInd1KeyStepOpk targetIdx targetOpkIdx S b.q_total U V)
      A.1.run (FgKeyInd1KeySimState.empty S secb)
  exact (isQueryBoundP_bind hStep
    (fun p _ => isQueryBoundP_liftGdhToSign_sig _ 0)).mono (by omega)

theorem isQueryBoundP_fgKeyInd1KeyGapDhRunAtFlat_sig (idx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgKeyInd1KeyGapDhRunAtFlat idx S b A U V)
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold fgKeyInd1KeyGapDhRunAtFlat
  dsimp only
  split_ifs
  · exact isQueryBoundP_fgKeyInd1KeyGapDhRunAt_sig _ _ _ S b A U V
  · exact isQueryBoundP_fgKeyInd1KeyGapDhRunAt_sig _ _ _ S b A U V
  · exact isQueryBoundP_fgKeyInd1KeyGapDhRunAtIk_sig _ _ S b A U V
  · exact isQueryBoundP_fgKeyInd1KeyGapDhRunAtOpk_sig _ _ S b A U V

theorem isQueryBoundP_fgKeyInd1KeyGapDhAdv4_sig
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    IsQueryBoundP ((fgKeyInd1KeyGapDhAdv4 S b A).run U V)
      (fun q => isSigChalQuery q = true) (fgKeyInd1KeyGapDhAdv4 S b A).q_sig := by
  dsimp only [fgKeyInd1KeyGapDhAdv4]
  exact (isQueryBoundP_bind
    (isQueryBoundP_unifGdhSign_sig (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) 0)
    (fun idx _ => isQueryBoundP_fgKeyInd1KeyGapDhRunAtFlat_sig idx S b A U V)).mono (by omega)

theorem fgKeyInd1KeyGapDhAdv4_ddh_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyInd1KeyGapDhAdv4 S b A).q_ddh ≤ gdhQueryBudget S b :=
  le_rfl

theorem primQueryBudget_le_uniform8 (S : Setup) (b : QueryBudget) :
    primQueryBudget S b ≤ 2 ^ 8 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot + 1) := by
  unfold primQueryBudget
  have hEq :
      2 ^ 8 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot + 1) =
        16 * (b.q_total + 1) * (16 * (S.N_dh + S.N_sess_tot + 1)) := by ring
  rw [hEq]
  exact Nat.mul_le_mul_left _ (by omega)

theorem primQueryBudget_le_old (S : Setup) (b : QueryBudget) :
    primQueryBudget S b ≤ 2 ^ 10 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot + 1) :=
  (primQueryBudget_le_uniform8 S b).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))

theorem gdhQueryBudget_le_old (S : Setup) (b : QueryBudget) :
    gdhQueryBudget S b ≤
      8 * (b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 := by
  have hMin : gdhQueryBudget S b ≤ 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
    unfold gdhQueryBudget
    dsimp only
    have := Nat.min_le_left (4 * b.q_total ^ 2)
      (4 * min b.q_ro b.q_total * min (min b.q_on b.q_total) S.N_sess_tot +
        2 * min (min b.q_on b.q_total) S.N_sess_tot *
          (min (min b.q_on b.q_total) S.N_sess_tot - 1))
    omega
  have hQ : b.q_total ^ 2 ≤
      (b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hLin : b.q_total + S.N_dh + S.N_sess_tot ≤
      b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1 := by omega
  generalize b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1 = U at hQ hLin ⊢
  have hU1 : U ≤ U ^ 2 := Nat.le_self_pow (by decide) U
  omega

theorem fgKeyInd1KeyGapDhAdv4_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyInd1KeyGapDhAdv4 S b A).q_prim ≤ primQueryBudget S b := by
  dsimp [fgKeyInd1KeyGapDhAdv4, primQueryBudget]
  nlinarith

noncomputable def fgInitPrin1KeyPure {S : Setup} (P : Primitives)
    (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes)
    (u : Fin S.N_id) (st : FgKeyInd1KeySimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeySimState S) := do
  if st.sim.base.principals.any (fun (idx, _) => idx == u.val) then
    return (.noneResp, st)
  let isTargetPrin : Bool := prinFlag && (u.val == prinIdx)
  let sk0 ← sampleScalar32
  let pk0 := P.x25519Base sk0
  let sec0 := if isTargetPrin then [] else sk0
  let ikPk := if isTargetPrin then Up else pk0
  let entry : PrincipalEntry := {
    secIKA0    := sec0
    ikAPk      := ikPk
    secIKAsign := sec0
    ikSignPk   := ikPk
    corrupted  := false
  }
  let base' := { st.sim.base with principals := (u.val, entry) :: st.sim.base.principals }
  return (.initPrinResp ikPk ikPk, { st with sim := { st.sim with base := base' } })

noncomputable def fgGenSPK1KeyPure (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyInd1KeySimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeySimState S) := do
  if prinFlag && (u.val == prinIdx) then
    if st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, st)
    let some (_, uEntry) := st.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    if st.sigBudget == 0 then
      return (.noneResp, st)
    let isTargetSpk : Bool := FgGapDh.spkBundleFlatIdx S u j == targetSpkIdx
    let spkSkRaw ← sampleScalar32
    let spkPkRaw := P.x25519Base spkSkRaw
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let rSpk ← sampleRandom64
    let spkSig := P.sigSign uSk (encodeEC spkPk) rSpk
    let seedKem ← sampleRandom64
    let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
    let rPq ← sampleRandom64
    let pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry := {
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    let base' :=
      { st.sim.base with spkBundles := ((u.val, j.val), bEntry) :: st.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return (.bundleResp bundleOut,
      { sim := { st.sim with base := base' }, sigBudget := st.sigBudget - 1 })
  else
    let (resp, sim') ← fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V
      (.genSPK u j) st.sim
    return (resp, { st with sim := sim' })

/-- Pure `ProbComp` counterpart of `fgKeyInd1KeyStep` (Cases A and C). -/
noncomputable def fgKeyInd1KeyStepPure (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S)
    (st : FgKeyInd1KeySimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeySimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyPure P useDh1 targetIdx U u st
  | .genSPK u j =>
    fgGenSPK1KeyPure P uSk ddh useDh1 targetIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st
  | q => do
    let (resp, sim') ← fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st.sim
    return (resp, { st with sim := sim' })

/-- Pure `ProbComp` counterpart of `fgKeyInd1KeyStepIk` (Case B). -/
noncomputable def fgKeyInd1KeyStepPureIk (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S)
    (st : FgKeyInd1KeySimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeySimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyPure P true targetPrinIdx U u st
  | .genSPK u j =>
    fgGenSPK1KeyPure P uSk ddh true targetPrinIdx false targetIdx (FgGapDh.Ik.noSpkIdx S) S
      maxLen V U u j st
  | q => do
    let (resp, sim') ← fgKeyIndStepPure P ddh false targetIdx (FgGapDh.Ik.noSpkIdx S) S maxLen
      V U q st.sim
    return (resp, { st with sim := sim' })

/-- Pure `ProbComp` counterpart of `fgKeyInd1KeyStepOpk` (Case D). -/
noncomputable def fgKeyInd1KeyStepPureOpk (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S)
    (st : FgKeyInd1KeySimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeySimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyPure P false S.N_id U u st
  | .genSPK u j =>
    fgGenSPK1KeyPure P uSk ddh false S.N_id false targetIdx (FgGapDh.Opk.noSpkIdx S) S
      maxLen U V u j st
  | q => do
    let (resp, sim') ← fgKeyIndStepPureOpk P ddh targetIdx targetOpkIdx S maxLen U V q st.sim
    return (resp, { st with sim := sim' })

noncomputable def fgKeyInd1KeySimImpl (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyInd1KeySimState S) ProbComp) :=
  fun q => StateT.mk (fgKeyInd1KeyStepPure P uSk ddh useDh1 targetIdx targetSpkIdx S maxLen U V q)

noncomputable def fgKeyInd1KeySimImplIk (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyInd1KeySimState S) ProbComp) :=
  fun q => StateT.mk (fgKeyInd1KeyStepPureIk P uSk ddh targetIdx targetPrinIdx S maxLen U V q)

noncomputable def fgKeyInd1KeySimImplOpk (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyInd1KeySimState S) ProbComp) :=
  fun q => StateT.mk (fgKeyInd1KeyStepPureOpk P uSk ddh targetIdx targetOpkIdx S maxLen U V q)

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgInitPrin1KeyGdh {S : Setup}
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes) (u : Fin S.N_id)
    (st : FgKeyInd1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgInitPrin1KeyGdh prinFlag prinIdx Up u st) =
      fgInitPrin1KeyPure P prinFlag prinIdx Up u st := by
  unfold fgInitPrin1KeyGdh fgInitPrin1KeyPure
  by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
  · simp [hAny]
  · simp [hAny]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgGenSPK1KeyGdh
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (prinFlag : Bool) (prinIdx : ℕ) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyInd1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st) =
      fgGenSPK1KeyPure P uSk ddh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V
        u j st := by
  unfold fgGenSPK1KeyGdh fgGenSPK1KeyPure
  by_cases hPrin : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hPrin, ↓reduceIte]
    by_cases hAny : (st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [hAny]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      cases st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        by_cases hZero : (st.sigBudget == 0) = true
        · simp [hZero]
        · simp only [hZero, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
            simulateQ_gapDhWithSignFullImpl_unifGdhSign,
            simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base,
            simulateQ_gapDhWithSignFullImpl_sigChalQ,
            simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen,
            simulateQ_pure, pure_bind, bind_assoc]
  · simp only [hPrin, Bool.false_eq_true, ↓reduceIte]
    unfold liftSimStep1Key
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgKeyIndStep]
    simp

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyStep
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyStep useDh1 targetIdx targetSpkIdx S maxLen U V q st) =
      fgKeyInd1KeyStepPure P uSk ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st := by
  cases q with
  | initPrin u => exact simulateQ_gapDhWithSignFullImpl_fgInitPrin1KeyGdh P uSk ddh _ _ _ u st
  | genSPK u j =>
    exact simulateQ_gapDhWithSignFullImpl_fgGenSPK1KeyGdh P uSk ddh _ _ _ _ _ S maxLen U V u j st
  | _ =>
    simp only [fgKeyInd1KeyStep, fgKeyInd1KeyStepPure, liftSimStep1Key, simulateQ_bind,
      simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgKeyIndStep,
      simulateQ_pure]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyStepIk
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetPrinIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyStepIk targetIdx targetPrinIdx S maxLen U V q st) =
      fgKeyInd1KeyStepPureIk P uSk ddh targetIdx targetPrinIdx S maxLen U V q st := by
  cases q with
  | initPrin u => exact simulateQ_gapDhWithSignFullImpl_fgInitPrin1KeyGdh P uSk ddh _ _ _ u st
  | genSPK u j =>
    exact simulateQ_gapDhWithSignFullImpl_fgGenSPK1KeyGdh P uSk ddh _ _ _ _ _ S maxLen V U u j st
  | _ =>
    simp only [fgKeyInd1KeyStepIk, fgKeyInd1KeyStepPureIk, liftSimStep1Key, simulateQ_bind,
      simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgKeyIndStep,
      simulateQ_pure]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyStepOpk
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetOpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyStepOpk targetIdx targetOpkIdx S maxLen U V q st) =
      fgKeyInd1KeyStepPureOpk P uSk ddh targetIdx targetOpkIdx S maxLen U V q st := by
  cases q with
  | initPrin u => exact simulateQ_gapDhWithSignFullImpl_fgInitPrin1KeyGdh P uSk ddh _ _ _ u st
  | genSPK u j =>
    exact simulateQ_gapDhWithSignFullImpl_fgGenSPK1KeyGdh P uSk ddh _ _ _ _ _ S maxLen U V u j st
  | _ =>
    simp only [fgKeyInd1KeyStepOpk, fgKeyInd1KeyStepPureOpk, liftSimStep1Key, simulateQ_bind,
      simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgKeyIndStepOpk,
      simulateQ_pure]

theorem simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (step : (q : ιI) → St → OracleComp GdhSignSimSpec (GSpec.Range q × St))
    (stepPure : (q : ιI) → St → ProbComp (GSpec.Range q × St))
    (h_step : ∀ q st, simulateQ (gapDhWithSignFullImpl P uSk ddh) (step q st) = stepPure q st)
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      (fun q => StateT.mk (stepPure q))
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (runWithGdhSignStep step mx st) =
      (simulateQ impl mx).run st := by
  intro impl
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp [runWithGdhSignStep_pure, simulateQ_pure, StateT.run_pure]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      dsimp only [impl]
      rw [runWithGdhSignStep_query_inl, simulateQ_bind, simulateQ_run_query_inl]
      have hq : simulateQ (gapDhWithSignFullImpl P uSk ddh)
          (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n)))) =
          liftM (OracleSpec.query (spec := unifSpec) n) := by
        simp [gapDhWithSignFullImpl, primBaseImpl]
      rw [hq]
      congr 1; funext u
      exact ih u st
    | inr gq =>
      dsimp only [impl]
      rw [runWithGdhSignStep_query_inr, simulateQ_bind, h_step gq st, simulateQ_run_query_inr]
      dsimp only [StateT.run]
      congr 1; funext p
      exact ih p.1 p.2

theorem gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAt_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdvAt useDh1 targetIdx targetSpkIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyInd1KeySimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeySimState S) ProbComp) +
        fgKeyInd1KeySimImpl P u ddh useDh1 targetIdx targetSpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdhFromSimState S P ddh useDh1 b.q_total U V finalSt.sim) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhAdvAt
  congr 1; funext u
  congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh)
      (fgKeyInd1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A
        (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  unfold fgKeyInd1KeyGapDhRunAt
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  congr 1; funext secb
  rw [simulateQ_bind,
    simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P u ddh _ _
      (simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyStep P u ddh useDh1 targetIdx targetSpkIdx
        S b.q_total (P.x25519Base u) (P.x25519Base v)),
    bind_assoc]
  congr 1; funext ⟨_, finalSt⟩
  rw [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
    simulateQ_gapDhFullImpl_extractCdhFromSimState, pure_bind]

theorem gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAtIk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdvAtIk targetIdx targetPrinIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyInd1KeySimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeySimState S) ProbComp) +
        fgKeyInd1KeySimImplIk P u ddh targetIdx targetPrinIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdh2FromAdvRoLog ddh b.q_total V U finalSt.sim.advRoLog) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhAdvAtIk
  congr 1; funext u
  congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh)
      (fgKeyInd1KeyGapDhRunAtIk targetIdx targetPrinIdx S b A
        (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  unfold fgKeyInd1KeyGapDhRunAtIk
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  congr 1; funext secb
  rw [simulateQ_bind,
    simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P u ddh _ _
      (simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyStepIk P u ddh targetIdx targetPrinIdx
        S b.q_total (P.x25519Base u) (P.x25519Base v)),
    bind_assoc]
  congr 1; funext ⟨_, finalSt⟩
  rw [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
    simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog, pure_bind]

theorem gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAtOpk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhAdvAtOpk targetIdx targetOpkIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyInd1KeySimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeySimState S) ProbComp) +
        fgKeyInd1KeySimImplOpk P u ddh targetIdx targetOpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdh4FromAdvRoLog ddh b.q_total U V finalSt.sim.advRoLog) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhAdvAtOpk
  congr 1; funext u
  congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh)
      (fgKeyInd1KeyGapDhRunAtOpk targetIdx targetOpkIdx S b A
        (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  unfold fgKeyInd1KeyGapDhRunAtOpk
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  congr 1; funext secb
  rw [simulateQ_bind,
    simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P u ddh _ _
      (simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyStepOpk P u ddh targetIdx targetOpkIdx
        S b.q_total (P.x25519Base u) (P.x25519Base v)),
    bind_assoc]
  congr 1; funext ⟨_, finalSt⟩
  rw [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
    simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog, pure_bind]

/-- One-key `FgSim` oracle implementation overriding `.initPrin` with single-scalar key generation. -/
noncomputable def pqxdhKeyIndFgImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (pqxdhKeyIndImpl1KeyReal S P (.initPrin u))
  | q => pqxdhKeyIndFgImpl S P q

noncomputable def runKeyIndFgSim1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndFgCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndFgCutoffState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyIndFgImpl1Key S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

/-- Pre-sampled one-key `.initPrin` handler using `optPrinSk` at `prinIdx` when `prinFlag` holds. -/
noncomputable def fgPreInitPrin1Key (prinFlag : Bool) (prinIdx : ℕ) (optPrinSk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then
    return .noneResp
  let sk ← liftM (match optPrinSk with
    | some s => if prinFlag && (u.val == prinIdx) then pure s else sampleScalar32
    | none => sampleScalar32)
  let pk := P.x25519Base sk
  let entry : PrincipalEntry := {
    secIKA0    := sk
    ikAPk      := pk
    secIKAsign := sk
    ikSignPk   := pk
    corrupted  := false
  }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp pk pk

theorem fgPreInitPrin1Key_none_eq (prinFlag : Bool) (prinIdx : ℕ) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) :
    fgPreInitPrin1Key prinFlag prinIdx none S P u =
      pqxdhKeyIndImpl1KeyReal S P (.initPrin u) := rfl

theorem fgPreInitPrin1Key_false_eq (prinIdx : ℕ) (optPrinSk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    fgPreInitPrin1Key false prinIdx optPrinSk S P u =
      pqxdhKeyIndImpl1KeyReal S P (.initPrin u) := by
  cases optPrinSk <;> simp [fgPreInitPrin1Key, pqxdhKeyIndImpl1KeyReal]

/-- One-key pre-sampled `KeyInd` implementation for Cases A (`useDh1 = true`) and C
    (`useDh1 = false`). -/
noncomputable def pqxdhKeyIndFgPreImpl1Key (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (fgPreInitPrin1Key useDh1 targetIdx optUsk S P u)
  | q => pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q

/-- One-key pre-sampled `KeyInd` implementation for Case B (`DH2`): `optIkSk` is the responder
    identity scalar at `targetPrinIdx` (corresponding to `u` in `GapDhWithSign`), and `optEkSk` is
    the initiator ephemeral scalar at `targetIdx` (corresponding to `v`). -/
noncomputable def pqxdhKeyIndFgPreImpl1KeyIk (targetIdx targetPrinIdx : ℕ)
    (optIkSk optEkSk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (fgPreInitPrin1Key true targetPrinIdx optIkSk S P u)
  | q => pqxdhKeyIndFgPreImpl false targetIdx (FgGapDh.Ik.noSpkIdx S) optEkSk none S P q

/-- One-key pre-sampled `KeyInd` implementation for Case D (`DH4`). -/
noncomputable def pqxdhKeyIndFgPreImpl1KeyOpk (targetIdx targetOpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (fgPreInitPrin1Key false S.N_id none S P u)
  | q => pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk optVsk S P q

theorem pqxdhKeyIndFgPreImpl1Key_none_none_eq {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (P : Primitives) :
    pqxdhKeyIndFgPreImpl1Key useDh1 targetIdx targetSpkIdx none none S P =
      pqxdhKeyIndFgImpl1Key S P := by
  funext q
  cases q
  case initPrin u => rfl
  all_goals
    simpa [pqxdhKeyIndFgPreImpl1Key, pqxdhKeyIndFgImpl1Key] using
      congrFun (pqxdhKeyIndFgPreImpl_none_none_eq (S := S) useDh1 targetIdx targetSpkIdx P) _

theorem pqxdhKeyIndFgPreImpl1KeyIk_none_eq {S : Setup} (targetIdx targetPrinIdx : ℕ)
    (optEkSk : Option Bytes) (P : Primitives) :
    pqxdhKeyIndFgPreImpl1KeyIk targetIdx targetPrinIdx none optEkSk S P =
      pqxdhKeyIndFgPreImpl1Key false targetIdx (FgGapDh.Ik.noSpkIdx S) optEkSk none S P := by
  funext q
  cases q
  case initPrin u =>
    simp [pqxdhKeyIndFgPreImpl1KeyIk, pqxdhKeyIndFgPreImpl1Key,
      fgPreInitPrin1Key_none_eq, fgPreInitPrin1Key_false_eq]
  all_goals rfl

theorem pqxdhKeyIndFgPreImpl1KeyOpk_none_eq {S : Setup} (targetIdx targetOpkIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) :
    pqxdhKeyIndFgPreImpl1KeyOpk targetIdx targetOpkIdx optUsk none S P =
      pqxdhKeyIndFgPreImpl1Key false targetIdx (FgGapDh.Opk.noSpkIdx S) optUsk none S P := by
  funext q
  cases q
  case initPrin u =>
    simp [pqxdhKeyIndFgPreImpl1KeyOpk, pqxdhKeyIndFgPreImpl1Key,
      fgPreInitPrin1Key_none_eq, fgPreInitPrin1Key_false_eq]
  all_goals
    simpa [pqxdhKeyIndFgPreImpl1KeyOpk, pqxdhKeyIndFgPreImpl1Key] using
      congrFun (pqxdhKeyIndFgPreImplOpk_none_eq (S := S) targetIdx targetOpkIdx optUsk P) _

theorem fgPreInitPrin1Key_preserves_hasFired {S : Setup} (prinFlag : Bool) (prinIdx : ℕ)
    (optPrinSk : Option Bytes) (P : Primitives) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((liftFgBase (fgPreInitPrin1Key prinFlag prinIdx optPrinSk S P u)).run hst)) :
    (∀ bIdx, hasFiredSpk S bIdx hst → hasFiredSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredPrin S uIdx hst → hasFiredPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  unfold fgPreInitPrin1Key at hx
  rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
  revert hb
  cases hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    rintro ⟨sk, _, hEq⟩
    have hB := (Prod.mk.inj hEq).2
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; simp [List.any_cons, h],
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq; have hB := (Prod.mk.inj hEq).2
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩

theorem pqxdhKeyIndFgPreImpl1Key_preserves_hasFired {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    (∀ bIdx, hasFiredSpk S bIdx hst → hasFiredSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredPrin S uIdx hst → hasFiredPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  cases q
  case initPrin u =>
    exact fgPreInitPrin1Key_preserves_hasFired useDh1 targetIdx optUsk P u hst x hx
  all_goals
    exact pqxdhKeyIndFgPreImpl_preserves_hasFired useDh1 targetIdx targetSpkIdx optUsk optVsk
      P _ hst x hx

theorem pqxdhKeyIndFgPreImpl1KeyIk_preserves_hasFired {S : Setup}
    (targetIdx targetPrinIdx : ℕ) (optIkSk optEkSk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImpl1KeyIk targetIdx targetPrinIdx optIkSk optEkSk S P q).run hst)) :
    (∀ uIdx, hasFiredPrin S uIdx hst → hasFiredPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  cases q
  case initPrin u =>
    have h := fgPreInitPrin1Key_preserves_hasFired true targetPrinIdx optIkSk P u hst x hx
    exact ⟨h.2.1, h.2.2⟩
  all_goals
    have h := pqxdhKeyIndFgPreImpl_preserves_hasFired false targetIdx (FgGapDh.Ik.noSpkIdx S)
      optEkSk none P _ hst x hx
    exact ⟨h.2.1, h.2.2⟩

theorem pqxdhKeyIndFgPreImpl1KeyOpk_preserves {S : Setup}
    (targetIdx targetOpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImpl1KeyOpk targetIdx targetOpkIdx optUsk optVsk S P q).run hst)) :
    OpkKeysMono hst.base x.2.base ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  cases q
  case initPrin u =>
    unfold pqxdhKeyIndFgPreImpl1KeyOpk fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨sk, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      exact ⟨fun key h => by rw [hB]; exact h,
        fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact ⟨fun key h => by rw [hB]; exact h,
        fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
  all_goals
    exact pqxdhKeyIndFgPreImplOpk_preserves targetIdx targetOpkIdx optUsk optVsk P _ hst x hx

theorem evalDist_preSample_V_1Key {S : Setup} {α : Type}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredSpk S targetSpkIdx)
    (pqxdhKeyIndFgPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk none S P)
    (fun vSk => pqxdhKeyIndFgPreImpl1Key useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl1Key_preserves_hasFired useDh1 targetIdx targetSpkIdx optUsk none P
        q s x hx).1 targetSpkIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | genSPK u j =>
      unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hSlot : (_root_.SignalPqxdh.Security.FgGapDh.spkBundleFlatIdx S u j ==
          targetSpkIdx) = true
      · have hany := spkBundles_any_of_hasFiredSpk S targetSpkIdx s hFired u j hSlot
        simp [hany]
      · cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => rfl
  · cases q with
    | genSPK u j =>
      by_cases hSlot : (_root_.SignalPqxdh.Security.FgGapDh.spkBundleFlatIdx S u j ==
          targetSpkIdx) = true
      · unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => exact Or.inl (fun _ => rfl)
          | some p =>
            rcases p with ⟨_, uEntry⟩
            dsimp only
            refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
                support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨rSpk, _, pqPair, _, rPq, _, hEq⟩
              have hB := (Prod.mk.inj hEq).2
              exact ⟨u, j, beq_iff_eq.mp hSlot, by rw [hB]; simp⟩
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_U_dh1_1Key {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key true targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key true targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredPrin S targetIdx)
    (pqxdhKeyIndFgPreImpl1Key true targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhKeyIndFgPreImpl1Key true targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl1Key_preserves_hasFired true targetIdx targetSpkIdx none optVsk P
        q s x hx).2.1 targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initPrin u =>
      unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
      by_cases hSlot : (u.val == targetIdx) = true
      · have hany : s.base.principals.any (fun (idx, _) => idx == u.val) = true := by
          unfold hasFiredPrin at hFired
          rw [beq_iff_eq.mp hSlot]; exact hFired
        simp [hany]
      · cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => rfl
  · cases q with
    | initPrin u =>
      by_cases hSlot : (u.val == targetIdx) = true
      · unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun uSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind,
              support_pure, Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            unfold hasFiredPrin; rw [hB]; simp [hSlot]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun uSk => ?_)
        unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_U_dh3_1Key {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key false targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key false targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq_c0
    sampleScalar32
    sampleCoins32
    (hasFiredSess S targetIdx)
    (pqxdhKeyIndFgPreImpl1Key false targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhKeyIndFgPreImpl1Key false targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl1Key_preserves_hasFired false targetIdx targetSpkIdx none optVsk P
        q s x hx).2.2 targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initPrin u =>
      simp [pqxdhKeyIndFgPreImpl1Key, fgPreInitPrin1Key_false_eq]
    | initiateOPK u i bundle =>
      unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isNone
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          Bool.not_false, Bool.true_and]
        by_cases hSlot : (initSessionSlotIdx (.sendOPK u i) == targetIdx) = true
        · have hany := sessions_any_of_hasFiredSess targetIdx s hFired (.sendOPK u i) hSlot
            (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
          simp [hany]
        · simp only [hSlot, Bool.false_eq_true, ↓reduceIte]
      · rfl
    | initiateNoOPK u i bundle =>
      unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          Bool.not_false, Bool.true_and]
        by_cases hSlot : (initSessionSlotIdx (.sendNoOPK u i) == targetIdx) = true
        · have hany := sessions_any_of_hasFiredSess targetIdx s hFired (.sendNoOPK u i) hSlot
            (initSessionSlotIdx_sendNoOPK_lt u i)
          simp [hany]
        · simp only [hSlot, Bool.false_eq_true, ↓reduceIte]
      · rfl
    | _ => rfl
  · cases q with
    | initPrin u =>
      exact Or.inl (fun uSk => by simp [pqxdhKeyIndFgPreImpl1Key, fgPreInitPrin1Key_false_eq])
    | initiateOPK u i bundle =>
      dsimp only [pqxdhKeyIndFgPreImpl1Key, pqxdhKeyIndFgPreImpl]
      by_cases hOpt : bundle.opkB?.isNone = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftFgBase
        simp [hOpt]
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isNone then return .noneResp
            fgPreInitiate false targetIdx optU S P (.sendOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false targetIdx optU S P (.sendOPK u i) u bundle)).run s := by
          intro optU; unfold liftFgBase
          simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreInitiate_before_c0 targetIdx P (.sendOPK u i) u bundle s
    | initiateNoOPK u i bundle =>
      dsimp only [pqxdhKeyIndFgPreImpl1Key, pqxdhKeyIndFgPreImpl]
      by_cases hOpt : bundle.opkB?.isSome = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftFgBase
        simp [hOpt]
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isSome then return .noneResp
            fgPreInitiate false targetIdx optU S P (.sendNoOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false targetIdx optU S P (.sendNoOPK u i) u bundle)).run s := by
          intro optU; unfold liftFgBase
          simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreInitiate_before_c0 targetIdx P (.sendNoOPK u i) u bundle s
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_U_ik_1Key {S : Setup} {α : Type}
    (targetIdx targetPrinIdx : ℕ) (optEkSk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (ikSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyIk targetIdx targetPrinIdx (some ikSk) optEkSk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyIk targetIdx targetPrinIdx none optEkSk S P
    𝒟[sampleScalar32 >>= fun ikSk => (simulateQ (fullPre ikSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredPrin S targetPrinIdx)
    (pqxdhKeyIndFgPreImpl1KeyIk targetIdx targetPrinIdx none optEkSk S P)
    (fun ikSk => pqxdhKeyIndFgPreImpl1KeyIk targetIdx targetPrinIdx (some ikSk) optEkSk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl1KeyIk_preserves_hasFired targetIdx targetPrinIdx none optEkSk P
        q s x hx).1 targetPrinIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro ikSk
    cases q with
    | initPrin u =>
      unfold pqxdhKeyIndFgPreImpl1KeyIk fgPreInitPrin1Key liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
      by_cases hSlot : (u.val == targetPrinIdx) = true
      · have hany : s.base.principals.any (fun (idx, _) => idx == u.val) = true := by
          unfold hasFiredPrin at hFired
          rw [beq_iff_eq.mp hSlot]; exact hFired
        simp [hany]
      · cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => rfl
  · cases q with
    | initPrin u =>
      by_cases hSlot : (u.val == targetPrinIdx) = true
      · unfold pqxdhKeyIndFgPreImpl1KeyIk fgPreInitPrin1Key liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun ikSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind,
              support_pure, Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            unfold hasFiredPrin; rw [hB]; simp [hSlot]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun ikSk => ?_)
        unfold pqxdhKeyIndFgPreImpl1KeyIk fgPreInitPrin1Key liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_V_opk_1Key {S : Setup} {α : Type}
    (targetIdx targetOpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOpk targetIdx targetOpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOpk targetIdx targetOpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredOpk S targetOpkIdx)
    (pqxdhKeyIndFgPreImpl1KeyOpk targetIdx targetOpkIdx optUsk none S P)
    (fun vSk => pqxdhKeyIndFgPreImpl1KeyOpk targetIdx targetOpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx => hasFiredOpk_of_mono targetOpkIdx s x.2
      (pqxdhKeyIndFgPreImpl1KeyOpk_preserves targetIdx targetOpkIdx optUsk none P
        q s x hx).1 hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q
    case genOPK u j o =>
      unfold pqxdhKeyIndFgPreImpl1KeyOpk pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hSlot : (opkFlatIdx S u j o == targetOpkIdx) = true
      · have hany := opkEntries_any_of_hasFiredOpk S targetOpkIdx s hFired u j o hSlot
        simp [hany]
      · cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp [hSlot]
        · rfl
    all_goals rfl
  · cases q
    case genOPK u j o =>
      by_cases hSlot : (opkFlatIdx S u j o == targetOpkIdx) = true
      · unfold pqxdhKeyIndFgPreImpl1KeyOpk pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind,
              support_pure, Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            exact ⟨u, j, o, beq_iff_eq.mp hSlot, by rw [hB]; simp⟩
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold pqxdhKeyIndFgPreImpl1KeyOpk pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp [hSlot]
        · rfl
    all_goals exact Or.inl (fun _ => rfl)

theorem evalDist_runKeyIndFgSim1Key_eq_preSample_dh1 {S : Setup}
    (uIdx bIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_1Key true uIdx bIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh1_1Key uIdx bIdx none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl1Key_none_none_eq]
  simp only [pure_bind]

theorem evalDist_runKeyIndFgSim1Key_eq_preSample_dh3 {S : Setup}
    (sIdx bIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1Key false sIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl1Key false sIdx bIdx (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_1Key false sIdx bIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_1Key sIdx bIdx none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl1Key_none_none_eq]
  simp only [pure_bind]

/-- Case B (`DH2`) pre-sampling for one-key `FgSim`: samples `ikSk` first (matching `u` in
    `gapDhWithSignExp`) and `ekSk` second (matching `v`). -/
theorem evalDist_runKeyIndFgSim1Key_eq_preSample_dh2 {S : Setup}
    (sIdx kIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (ikSk ekSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P
    𝒟[do
        let ikSk ← sampleScalar32
        let ekSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre ikSk ekSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 sampleScalar32 _]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun ekSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hIk : ∀ ekSk,
      𝒟[sampleScalar32 >>= fun ikSk =>
        (simulateQ (fullPre ikSk ekSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl1Key false sIdx (FgGapDh.Ik.noSpkIdx S) (some ekSk) none S P)
          A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] := by
    intro ekSk
    rw [← pqxdhKeyIndFgPreImpl1KeyIk_none_eq sIdx kIdx (some ekSk) P]
    exact evalDist_preSample_U_ik_1Key sIdx kIdx (some ekSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun ekSk _ => hIk ekSk)]
  rw [evalDist_preSample_U_dh3_1Key sIdx (FgGapDh.Ik.noSpkIdx S) none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl1Key_none_none_eq]
  simp only [pure_bind]

theorem evalDist_runKeyIndFgSim1Key_eq_preSample_dh4 {S : Setup}
    (sIdx oIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl1Key false sIdx (FgGapDh.Opk.noSpkIdx S) (some uSk) none S P)
          A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] := by
    intro uSk
    rw [← pqxdhKeyIndFgPreImpl1KeyOpk_none_eq sIdx oIdx (some uSk) P]
    exact evalDist_preSample_V_opk_1Key sIdx oIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_1Key sIdx (FgGapDh.Opk.noSpkIdx S) none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl1Key_none_none_eq]
  simp only [pure_bind]

theorem validSpkBundles_length_le (S : Setup)
    {spkBundles : List ((Nat × Nat) × SpkBundleEntry)}
    (hValid : ValidSpkBundles S spkBundles) :
    spkBundles.length ≤ S.N_spk_tot := by
  have hNodup : (spkBundles.map (fun e => spkSlotFlatIdx S e.1)).Nodup := by
    have hMap : spkBundles.map (fun e => ecSpkSlotIdx S e.1) =
        (spkBundles.map (fun e => spkSlotFlatIdx S e.1)).map (fun k => S.N_id + k) := by
      simp [List.map_map, Function.comp_def, ecSpkSlotIdx]
    have hNd := hValid.2
    rw [hMap] at hNd
    exact hNd.of_map _
  have hSub : ∀ k ∈ spkBundles.map (fun e => spkSlotFlatIdx S e.1), k ∈ List.range S.N_spk_tot := by
    intro k hk
    rcases List.mem_map.mp hk with ⟨e, he, rfl⟩
    rcases hValid.1 e he with ⟨h1, h2⟩
    exact List.mem_range.mpr (spkSlotFlatIdx_lt S h1 h2)
  have hLen := (hNodup.subperm hSub).length_le
  simpa using hLen

def clearTargetPrinSecSign (tIdx idx : ℕ) (e : PrincipalEntry) : PrincipalEntry :=
  if idx == tIdx then { e with secIKAsign := [] } else e

def clearTargetSecIKAsignBase {S : Setup} (tIdx : ℕ) (st : KeyIndState S) : KeyIndState S :=
  { st with principals := st.principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) }

/-- Clear `secIKAsign` at principal `tIdx` in `FgKeyIndSimState S`, preserving public keys and `secIKA0`. -/
def clearTargetSecIKAsign {S : Setup} (tIdx : ℕ) (st : FgKeyIndSimState S) : FgKeyIndSimState S :=
  { st with base := clearTargetSecIKAsignBase tIdx st.base }

@[simp]
theorem clearTargetPrinSecSign_secIKA0 (tIdx idx : ℕ) (e : PrincipalEntry) :
    (clearTargetPrinSecSign tIdx idx e).secIKA0 = e.secIKA0 := by
  unfold clearTargetPrinSecSign; split_ifs <;> rfl

@[simp]
theorem clearTargetPrinSecSign_ikAPk (tIdx idx : ℕ) (e : PrincipalEntry) :
    (clearTargetPrinSecSign tIdx idx e).ikAPk = e.ikAPk := by
  unfold clearTargetPrinSecSign; split_ifs <;> rfl

@[simp]
theorem clearTargetPrinSecSign_ikSignPk (tIdx idx : ℕ) (e : PrincipalEntry) :
    (clearTargetPrinSecSign tIdx idx e).ikSignPk = e.ikSignPk := by
  unfold clearTargetPrinSecSign; split_ifs <;> rfl

@[simp]
theorem clearTargetPrinSecSign_corrupted (tIdx idx : ℕ) (e : PrincipalEntry) :
    (clearTargetPrinSecSign tIdx idx e).corrupted = e.corrupted := by
  unfold clearTargetPrinSecSign; split_ifs <;> rfl

theorem find?_idx_map_clearTargetPrinSecSign (tIdx uVal : ℕ)
    (L : List (Nat × PrincipalEntry)) :
    (L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).find?
      (fun (idx, _) => idx == uVal) =
      (L.find? (fun (idx, _) => idx == uVal)).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons, List.find?_cons]
    cases idx == uVal
    · exact ih
    · rfl

theorem findHonestPrincipal_map_clearTargetPrinSecSign (P : Primitives) (tIdx : ℕ)
    (L : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    findHonestPrincipal P (L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))) ikB =
      (findHonestPrincipal P L ikB).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := by
  unfold findHonestPrincipal
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons, List.find?_cons, clearTargetPrinSecSign_ikAPk]
    cases P.pow8 ikB == P.pow8 e.ikAPk
    · exact ih
    · rfl

@[simp]
theorem findHonestPrincipal_take_map_clearTargetPrinSecSign (P : Primitives) (tIdx n : ℕ)
    (L : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    findHonestPrincipal P
      ((L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).take n) ikB =
      (findHonestPrincipal P (L.take n) ikB).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := by
  rw [← List.map_take]
  exact findHonestPrincipal_map_clearTargetPrinSecSign P tIdx (L.take n) ikB

@[simp]
theorem resolveSigPk_take_map_clearTargetPrinSecSign (P : Primitives) (tIdx n : ℕ)
    (L : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    resolveSigPk P ((L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).take n) ikB =
      resolveSigPk P (L.take n) ikB := by
  unfold resolveSigPk
  rw [findHonestPrincipal_take_map_clearTargetPrinSecSign]
  cases findHonestPrincipal P (L.take n) ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; simp

@[simp]
theorem isHonestUncorruptedPeer_take_map_clearTargetPrinSecSign (P : Primitives) (tIdx n : ℕ)
    (L : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    isHonestUncorruptedPeer P
      ((L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).take n) ikB =
      isHonestUncorruptedPeer P (L.take n) ikB := by
  unfold isHonestUncorruptedPeer
  rw [findHonestPrincipal_take_map_clearTargetPrinSecSign]
  cases findHonestPrincipal P (L.take n) ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; simp

@[simp]
theorem checkBundleProvenanceTake_map_clearTargetPrinSecSign (S : Setup) (P : Primitives) (tIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    checkBundleProvenanceTake S P
      (principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)))
      spkBundles opkEntries bundle =
      checkBundleProvenanceTake S P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenanceTake
  rw [findHonestPrincipal_take_map_clearTargetPrinSecSign]
  cases findHonestPrincipal P (principals.take S.N_dh) bundle.ikB <;> rfl

@[simp]
theorem koskSenderOkTake_map_clearTargetPrinSecSign (S : Setup) (P : Primitives) (tIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows : List (Bytes × Bytes)) (ikAPk : Bytes) :
    koskSenderOkTake S P
      (principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)))
      advKeyPows ikAPk =
      koskSenderOkTake S P principals advKeyPows ikAPk := by
  unfold koskSenderOkTake
  rw [findHonestPrincipal_take_map_clearTargetPrinSecSign]
  cases findHonestPrincipal P (principals.take S.N_dh) ikAPk <;> rfl

@[simp]
theorem koskBundleOkTake_map_clearTargetPrinSecSign (S : Setup) (P : Primitives) (tIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    koskBundleOkTake S P
      (principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)))
      spkBundles opkEntries advKeyPows bundle =
      koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle := by
  unfold koskBundleOkTake
  rw [findHonestPrincipal_take_map_clearTargetPrinSecSign]
  cases findHonestPrincipal P (principals.take S.N_dh) bundle.ikB <;> rfl

@[simp] theorem clearTargetSecIKAsign_base_principals {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.principals =
      st.base.principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := rfl
@[simp] theorem clearTargetSecIKAsign_base_spkBundles {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.spkBundles = st.base.spkBundles := rfl
@[simp] theorem clearTargetSecIKAsign_base_opkEntries {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.opkEntries = st.base.opkEntries := rfl
@[simp] theorem clearTargetSecIKAsign_base_sessions {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.sessions = st.base.sessions := rfl
@[simp] theorem clearTargetSecIKAsign_base_respSessions {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.respSessions = st.base.respSessions := rfl
@[simp] theorem clearTargetSecIKAsign_base_usedRecvOPK {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.usedRecvOPK = st.base.usedRecvOPK := rfl
@[simp] theorem clearTargetSecIKAsign_base_usedRecvNoOPK {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.usedRecvNoOPK = st.base.usedRecvNoOPK := rfl
@[simp] theorem clearTargetSecIKAsign_base_seenKyberBaseKeys {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.seenKyberBaseKeys = st.base.seenKyberBaseKeys := rfl
@[simp] theorem clearTargetSecIKAsign_base_advKeys {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.advKeys = st.base.advKeys := rfl
@[simp] theorem clearTargetSecIKAsign_base_secb {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).base.secb = st.base.secb := rfl
@[simp] theorem clearTargetSecIKAsign_fgL {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).fgL = st.fgL := rfl
@[simp] theorem clearTargetSecIKAsign_rawRoCache {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).rawRoCache = st.rawRoCache := rfl
@[simp] theorem clearTargetSecIKAsign_advRoLog {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).advRoLog = st.advRoLog := rfl
@[simp] theorem clearTargetSecIKAsign_advKeyPows {S : Setup} (tIdx : ℕ)
    (st : FgKeyIndSimState S) :
    (clearTargetSecIKAsign tIdx st).advKeyPows = st.advKeyPows := rfl

theorem fgRunInitiatePure_clearTargetSecIKAsign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U : Bytes) (sid : SessionId S)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) :
    fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U sid u bundle (clearTargetSecIKAsign tIdx st) =
      (fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U sid u bundle st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  unfold fgRunInitiatePure
  simp only [clearTargetSecIKAsign_base_sessions, clearTargetSecIKAsign_base_principals,
    clearTargetSecIKAsign_base_spkBundles, clearTargetSecIKAsign_base_opkEntries,
    clearTargetSecIKAsign_base_respSessions, clearTargetSecIKAsign_fgL,
    clearTargetSecIKAsign_advKeyPows]
  by_cases hSid : (st.base.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hSid, ↓reduceIte, pure_bind]
  · simp only [hSid, Bool.false_eq_true, ↓reduceIte, find?_idx_map_clearTargetPrinSecSign]
    cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp only [Option.map_none, pure_bind]
    | some p =>
      rcases p with ⟨idx, uEntry⟩
      simp only [Option.map_some, koskBundleOkTake_map_clearTargetPrinSecSign,
        resolveSigPk_take_map_clearTargetPrinSecSign,
        isHonestUncorruptedPeer_take_map_clearTargetPrinSecSign,
        checkBundleProvenanceTake_map_clearTargetPrinSecSign,
        findHonestPrincipal_take_map_clearTargetPrinSecSign,
        clearTargetPrinSecSign_secIKA0, clearTargetPrinSecSign_ikAPk]
      by_cases hKosk : (!koskBundleOkTake S P st.base.principals st.base.spkBundles
          st.base.opkEntries st.advKeyPows bundle) = true
      · simp only [hKosk, ↓reduceIte, pure_bind]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, bind_assoc]
        congr 1; funext ekASkRaw
        congr 1; funext kemCoins
        by_cases hSig : (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hSig, ↓reduceIte, pure_bind]
        · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp only [pure_bind]
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩
            simp only [bind_assoc]
            congr 1; funext ⟨drKeyReal, fgL'⟩
            congr 1; funext drKeyRand
            cases findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;>
              simp only [Option.map_none, Option.map_some, pure_bind] <;> rfl

theorem fgRunAcceptOPKPure_clearTargetSecIKAsign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (tIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    fgRunAcceptOPKPure P ddh S maxLen k j o hdr (clearTargetSecIKAsign tIdx st) =
      (fgRunAcceptOPKPure P ddh S maxLen k j o hdr st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  unfold fgRunAcceptOPKPure
  simp only [clearTargetSecIKAsign_base_usedRecvOPK, clearTargetSecIKAsign_base_principals,
    clearTargetSecIKAsign_base_spkBundles, clearTargetSecIKAsign_base_opkEntries,
    clearTargetSecIKAsign_base_seenKyberBaseKeys, clearTargetSecIKAsign_base_sessions,
    clearTargetSecIKAsign_base_respSessions, clearTargetSecIKAsign_fgL,
    clearTargetSecIKAsign_advKeyPows]
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, pure_bind]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [hUsed, ↓reduceIte, pure_bind]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte,
        koskSenderOkTake_map_clearTargetPrinSecSign, find?_idx_map_clearTargetPrinSecSign]
      by_cases hKosk : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, pure_bind]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp only [Option.map_none, pure_bind]
        | some pk =>
          rcases pk with ⟨idx, kEntry⟩
          simp only [Option.map_some]
          cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp only [pure_bind]
          | some pb =>
            rcases pb with ⟨_, bEntry⟩
            dsimp only
            cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => simp only [pure_bind]
            | some po =>
              rcases po with ⟨_, oEntry⟩
              dsimp only
              by_cases hCons : oEntry.consumed = true
              · simp only [hCons, ↓reduceIte, pure_bind]
              · simp only [hCons, Bool.false_eq_true, ↓reduceIte]
                by_cases hChk : (!((checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
                    hdr.pqspkId hdr.spkId hdr.ekAPk).1 && P.isCanonical hdr.ekAPk &&
                     P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                     P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0 &&
                     P.x25519 oEntry.opkSk hdr.ekAPk != List.replicate 32 0)) = true
                · simp only [hChk, ↓reduceIte, pure_bind]
                · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none => simp only [pure_bind]
                  | some ss =>
                    simp only [clearTargetPrinSecSign_secIKA0, clearTargetPrinSecSign_ikAPk,
                      findHonestPrincipal_take_map_clearTargetPrinSecSign, bind_assoc]
                    congr 1; funext ⟨drKey, fgL'⟩
                    congr 1; funext drKeyRand
                    cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;>
                      simp only [Option.map_none, Option.map_some, Option.isSome_none,
                        Option.isSome_some, pure_bind] <;> rfl

theorem fgRunAcceptNoOPKPure_clearTargetSecIKAsign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (tIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    fgRunAcceptNoOPKPure P ddh S maxLen k j l hdr (clearTargetSecIKAsign tIdx st) =
      (fgRunAcceptNoOPKPure P ddh S maxLen k j l hdr st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  unfold fgRunAcceptNoOPKPure
  simp only [clearTargetSecIKAsign_base_usedRecvNoOPK, clearTargetSecIKAsign_base_principals,
    clearTargetSecIKAsign_base_spkBundles, clearTargetSecIKAsign_base_seenKyberBaseKeys,
    clearTargetSecIKAsign_base_sessions, clearTargetSecIKAsign_base_respSessions,
    clearTargetSecIKAsign_fgL, clearTargetSecIKAsign_advKeyPows]
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, pure_bind]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [hUsed, ↓reduceIte, pure_bind]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte,
        koskSenderOkTake_map_clearTargetPrinSecSign, find?_idx_map_clearTargetPrinSecSign]
      by_cases hKosk : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, pure_bind]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp only [Option.map_none, pure_bind]
        | some pk =>
          rcases pk with ⟨idx, kEntry⟩
          simp only [Option.map_some]
          cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp only [pure_bind]
          | some pb =>
            rcases pb with ⟨_, bEntry⟩
            dsimp only
            by_cases hChk : (!((checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
                hdr.pqspkId hdr.spkId hdr.ekAPk).1 && P.isCanonical hdr.ekAPk &&
                 P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                 P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
            · simp only [hChk, ↓reduceIte, pure_bind]
            · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
              | none => simp only [pure_bind]
              | some ss =>
                simp only [clearTargetPrinSecSign_secIKA0, clearTargetPrinSecSign_ikAPk,
                  findHonestPrincipal_take_map_clearTargetPrinSecSign, bind_assoc]
                congr 1; funext ⟨drKey, fgL'⟩
                congr 1; funext drKeyRand
                cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;>
                  simp only [Option.map_none, Option.map_some, Option.isSome_none,
                    Option.isSome_some, pure_bind] <;> rfl

def isNonIdentityQuery {S : Setup} : KeyIndQuery S → Bool
  | .initPrin _   => false
  | .corruptIK _  => false
  | .genSPK _ _   => false
  | _             => true

theorem fgKeyIndStepPure_clearTargetSecIKAsign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S)
    (hq : isNonIdentityQuery q = true) (st : FgKeyIndSimState S) :
    fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q
      (clearTargetSecIKAsign tIdx st) =
      (fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  cases q with
  | initPrin _ => cases hq
  | corruptIK _ => cases hq
  | genSPK _ _ => cases hq
  | genOPK u j o =>
    dsimp only [fgKeyIndStepPure]
    simp only [clearTargetSecIKAsign_base_opkEntries]
    by_cases hAny : (st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hAny, ↓reduceIte, pure_bind]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      rfl
  | initiateOPK u i bundle =>
    dsimp only [fgKeyIndStepPure]
    cases hOpt : bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgRunInitiatePure_clearTargetSecIKAsign P ddh useDh1 targetIdx tIdx S maxLen U
        (.sendOPK u i) u bundle st
    · simp only [↓reduceIte, pure_bind]
  | initiateNoOPK u i bundle =>
    dsimp only [fgKeyIndStepPure]
    cases hOpt : bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgRunInitiatePure_clearTargetSecIKAsign P ddh useDh1 targetIdx tIdx S maxLen U
        (.sendNoOPK u i) u bundle st
    · simp only [↓reduceIte, pure_bind]
  | acceptOPK k j o hdr =>
    exact fgRunAcceptOPKPure_clearTargetSecIKAsign P ddh tIdx S maxLen k j o hdr st
  | acceptNoOPK k j l hdr =>
    exact fgRunAcceptNoOPKPure_clearTargetSecIKAsign P ddh tIdx S maxLen k j l hdr st
  | testSession sid =>
    have hTest : isKeyIndSessionTestable (clearTargetSecIKAsign tIdx st).base sid =
        isKeyIndSessionTestable st.base sid := rfl
    dsimp only [fgKeyIndStepPure]
    rw [hTest]
    simp only [clearTargetSecIKAsign_base_sessions, clearTargetSecIKAsign_base_respSessions,
      clearTargetSecIKAsign_base_secb]
    by_cases hF : (!isKeyIndSessionTestable st.base sid) = true
    · simp only [hF, ↓reduceIte, pure_bind]
    · simp only [hF, Bool.false_eq_true, ↓reduceIte]
      cases st.base.sessions.find? (fun e => e.sid == sid) with
      | some e => dsimp only; simp only [pure_bind]; rfl
      | none =>
        dsimp only
        cases st.base.respSessions.find? (fun r => r.sid == sid) with
        | none => dsimp only; simp only [pure_bind]
        | some r => dsimp only; simp only [pure_bind]; rfl
  | revealSessionKey sid =>
    dsimp only [fgKeyIndStepPure]
    simp only [clearTargetSecIKAsign_base_sessions, clearTargetSecIKAsign_base_respSessions]
    cases st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      cases e.tested
      · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; rfl
      · simp only [↓reduceIte, pure_bind]
    | none =>
      dsimp only
      cases st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => dsimp only; simp only [pure_bind]
      | some r =>
        dsimp only
        cases r.tested
        · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; rfl
        · simp only [↓reduceIte, pure_bind]
  | roQuery secrets =>
    dsimp only [fgKeyIndStepPure]
    unfold fgRoQueryPure
    simp only [clearTargetSecIKAsign_advRoLog, clearTargetSecIKAsign_fgL,
      clearTargetSecIKAsign_rawRoCache]
    cases parseRoSecrets secrets with
    | none =>
      dsimp only
      cases st.rawRoCache.find? (fun (s, _) => s == secrets) with
      | some p => rcases p with ⟨_, dk⟩; dsimp only; simp only [pure_bind]; rfl
      | none => dsimp only; simp only [bind_assoc, pure_bind]; congr 1
    | some tup =>
      rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
      dsimp only; simp only [bind_assoc, pure_bind]; congr 1
  | revealDhSecrets =>
    dsimp only [fgKeyIndStepPure]; simp only [pure_bind]
  | registerKey sk =>
    dsimp only [fgKeyIndStepPure]
    simp only [clearTargetSecIKAsign_base_advKeys, clearTargetSecIKAsign_advKeyPows]
    cases sk.length != 32
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; rfl
    · simp only [↓reduceIte, pure_bind]
  | revealSpkSk u j =>
    dsimp only [fgKeyIndStepPure]
    simp only [clearTargetSecIKAsign_base_spkBundles]
    cases st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none => dsimp only; simp only [pure_bind]
    | some p => rcases p with ⟨_, bEntry⟩; dsimp only; simp only [pure_bind]; rfl

end Proofs.SignalPqxdh.Security.FgGapDh1Key
