/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH δ key indistinguishability: `G3 → G3.5` coupling

**Checked by Lean.** Proves `kiCoupling` (`KICouplingStmt`, DEV-PQ21), the `G3 → G3.5` up-to-bad
coupling bound incorporating the KEM correctness bad event `hasBadKemCorrRecords`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

namespace KICoupling

theorem evalDist_bind_pure_or_le {α : Type} (m : ProbComp α) (b1 b2 : α → Bool) :
    𝒟[m >>= fun x => pure (b1 x || b2 x)] {true} ≤
      𝒟[m >>= fun x => pure (b1 x)] {true} +
      𝒟[m >>= fun x => pure (b2 x)] {true} := by
  rw [evalDist_bind_true_eq_probExpect_comp m (fun x => pure (b1 x || b2 x)),
      evalDist_bind_true_eq_probExpect_comp m (fun x => pure (b1 x)),
      evalDist_bind_true_eq_probExpect_comp m (fun x => pure (b2 x))]
  refine probExpect_add_le_fg m _ _ _ (fun x => ?_)
  cases b1 x <;> cases b2 x <;> simp

theorem isInvariant_randLens_hasBadKemCorrRecords (S : Setup) (P : Primitives) :
    (randLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs)) :=
  CacheLens.IsInvariant.of_cache_indep (randLens S) _ (fun _ _ _ => rfl)

theorem isInvariant_roLens_hasBadKemCorrRecords (S : Setup) (P : Primitives) :
    (roLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs)) :=
  CacheLens.IsInvariant.of_cache_indep (roLens S) _ (fun _ _ _ => rfl)

theorem evalDist_simulateQ_testImpl_hasBadKemCorrRecords_eq_tagImpl_false_false {S : Setup}
    (testReal : Bool) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let initTrue : KeyIndAdvCutoffState S :=
      { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndAdvCutoffState S)
      ProbComp) +
      pqxdhKeyIndAdvTestImpl testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndLazyState S)
      ProbComp) +
      pqxdhKeyIndAdvTagImpl false false testReal S P
    𝒟[(_root_.simulateQ fullTest oa).run initTrue >>=
        fun p => pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] =
      𝒟[(_root_.simulateQ full00 oa).run (KeyIndLazyState.empty S) >>=
        fun p => pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs)] := by
  intro initTrue fullTest full00
  rw [evalDist_simulateQ_testImpl_eq_tagImpl_true_true testReal P
    (fun p => pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs))
    (fun p => pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs))
    (fun _ _ _ ⟨hEq, _⟩ => by
      subst hEq
      rfl)
    oa initTrue (KeyIndLazyState.empty S) (relEagerTag_empty S)]
  exact evalDist_simulateQ_pqxdhKeyIndAdvTagImpl_true_true_eq_false_false testReal P oa
    (isInvariant_randLens_hasBadKemCorrRecords S P)
    (isInvariant_roLens_hasBadKemCorrRecords S P)
    (KeyIndLazyState.empty S)

theorem hasBadKemCorrRecords_runKeyIndAdvG3Sim_eq_runKeyIndShCrSim
    (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    (runKeyIndAdvG3Sim S P A >>= fun x =>
      pure (hasBadKemCorrRecords S P x.2.2.shCr.initKemRecs x.2.2.shCr.recvKemRecs)) =
    (runKeyIndShCrSim S P A >>= fun x =>
      pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)) := by
  rw [← runKeyIndAdvG3Sim_shCr S P A, bind_map_left]
  rfl

theorem keyIndAdvG3_le_prob_badKeyIndFgAny_add_corr_of_tagImpl_false_false_relCoupled
    (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S)
    (R : Bool × KeyIndLazyState S → Bool × KeyIndLazyState S → Prop)
    (hRel :
      let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false false S P
      let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false true S P
      RelCoupled R
        ((simulateQ fullF A.run).run (KeyIndLazyState.empty S))
        ((simulateQ fullT A.run).run (KeyIndLazyState.empty S)))
    (hFin : ∀ p5 p6, R p5 p6 →
      𝒟[finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr] {true} =
        𝒟[finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr] {true} ∨
      (badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog ||
        hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs) = true ∨
      (badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog ||
        hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs) = true) :
    keyIndAdvG3 S P A ≤
      2 * (𝒟[runKeyIndFgSim S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal +
      2 * (𝒟[runKeyIndShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal := by
  let initFalse : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S false }, advRoLog := [] }
  let initTrue : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl S P
  let implF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl false S P
  let implT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl true S P
  let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false false S P
  let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false true S P
  have hSym := hRel.evalDist_bind_le_sym
    (fun p5 => badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog ||
      hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)
    (fun p6 => badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog ||
      hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)
    (fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr)
    (fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr)
    hFin
  have hOrF := evalDist_bind_pure_or_le
    ((simulateQ fullF A.run).run (KeyIndLazyState.empty S))
    (fun p5 => badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)
    (fun p5 => hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)
  have hOrT := evalDist_bind_pure_or_le
    ((simulateQ fullT A.run).run (KeyIndLazyState.empty S))
    (fun p6 => badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog)
    (fun p6 => hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)
  have hSym1 :
      𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
          fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr] {true} ≤
        𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
          fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr] {true} +
        ((𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)] {true} +
          𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog)] {true}) +
         (𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)] {true} +
          𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)] {true})) := by
    calc 𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr] {true}
        ≤ _ := hSym.1
      _ ≤ 𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr] {true} +
          (𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)] {true} +
           𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)] {true}) +
          (𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog)] {true} +
           𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)] {true}) :=
          add_le_add (add_le_add_right hOrF _) hOrT
      _ = _ := by ac_rfl
  have hSym2 :
      𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
          fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr] {true} ≤
        𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
          fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr] {true} +
        ((𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)] {true} +
          𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog)] {true}) +
         (𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)] {true} +
          𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)] {true})) := by
    calc 𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr] {true}
        ≤ _ := hSym.2
      _ ≤ 𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr] {true} +
          (𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)] {true} +
           𝒟[(simulateQ fullF A.run).run (KeyIndLazyState.empty S) >>=
            fun p5 => pure (hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)] {true}) +
          (𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog)] {true} +
           𝒟[(simulateQ fullT A.run).run (KeyIndLazyState.empty S) >>=
            fun p6 => pure (hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)] {true}) :=
          add_le_add (add_le_add_right hOrF _) hOrT
      _ = _ := by ac_rfl
  rw [← evalDist_simulateQ_testImpl_finalizeKeyIndG3_eq_tagImpl_false_false false P true A.run,
      ← evalDist_simulateQ_testImpl_finalizeKeyIndG3_eq_tagImpl_false_false true P true A.run,
      ← evalDist_simulateQ_testImpl_badKeyIndFgAny_eq_tagImpl_false_false false P maxLen A.run,
      ← evalDist_simulateQ_testImpl_badKeyIndFgAny_eq_tagImpl_false_false true P maxLen A.run,
      ← evalDist_simulateQ_testImpl_hasBadKemCorrRecords_eq_tagImpl_false_false false P A.run,
      ← evalDist_simulateQ_testImpl_hasBadKemCorrRecords_eq_tagImpl_false_false true P A.run]
        at hSym1 hSym2
  have hBrF : keyIndAdvG3Branch false S P A =
      ((simulateQ implF A.run).run initTrue >>= fun p => finalizeKeyIndG3 S P true p.1 p.2.shCr) := by
    unfold keyIndAdvG3Branch
    simp only [finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true]
    have hInit : ({ shCr :=
      { base := KeyIndState.empty S false }, advRoLog := [] } : KeyIndAdvCutoffState S) =
        withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv false P A.run initTrue, bind_map_left]
    rfl
  have hBrT : keyIndAdvG3Branch true S P A =
      ((simulateQ implT A.run).run initTrue >>= fun p => finalizeKeyIndG3 S P true p.1 p.2.shCr) := by
    unfold keyIndAdvG3Branch
    simp only [finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true]
    have hInit : ({ shCr :=
      { base := KeyIndState.empty S true }, advRoLog := [] } : KeyIndAdvCutoffState S) =
        withSecbAdv true initTrue := rfl
    conv_lhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  have hBadF : ((simulateQ implF A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) =
      ((simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) := by
    have hInit : initFalse = withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv false P A.run initTrue, bind_map_left]
    rfl
  have hBadT : ((simulateQ implT A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) =
      ((simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) := by
    have hInit : initTrue = withSecbAdv true initTrue := rfl
    conv_rhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  have hCorrF : ((simulateQ implF A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) =
      ((simulateQ impl A.run).run initFalse >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) := by
    have hInit : initFalse = withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv false P A.run initTrue, bind_map_left]
    rfl
  have hCorrT : ((simulateQ implT A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) =
      ((simulateQ impl A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) := by
    have hInit : initTrue = withSecbAdv true initTrue := rfl
    conv_rhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  rw [← hBrF, ← hBrT, hBadF, hBadT, hCorrF, hCorrT] at hSym1 hSym2
  have hBadSum :
      2 * (𝒟[runKeyIndFgSim S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal =
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}).toReal +
      (𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}).toReal := by
    rw [← badKeyIndFgAny_runKeyIndAdvG3Sim_eq_runKeyIndFgSim]
    unfold runKeyIndAdvG3Sim
    simp only [bind_assoc, pure_bind]
    exact two_mul_toReal_uniformBool_bind_eq_add_fg (fun secb =>
      (simulateQ impl A.run).run
        { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] } >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog))
  have hCorrSum :
      2 * (𝒟[runKeyIndShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal =
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true}).toReal +
      (𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true}).toReal := by
    rw [← hasBadKemCorrRecords_runKeyIndAdvG3Sim_eq_runKeyIndShCrSim]
    unfold runKeyIndAdvG3Sim
    simp only [bind_assoc, pure_bind]
    exact two_mul_toReal_uniformBool_bind_eq_add_fg (fun secb =>
      (simulateQ impl A.run).run
        { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] } >>=
        fun p => pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs))
  have hfin5 : 𝒟[keyIndAdvG3Branch false S P A] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfin6 : 𝒟[keyIndAdvG3Branch true S P A] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinB5 : 𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinB6 : 𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinC5 : 𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinC6 : 𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfinBad : 𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} +
     𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinB5, hfinB6⟩
  have hfinCorr : 𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true} +
     𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinC5, hfinC6⟩
  have hfinTot : (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true} +
     𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}) +
     (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true} +
     𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true}) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinBad, hfinCorr⟩
  have h1r := (ENNReal.toReal_le_toReal hfin5 (ENNReal.add_ne_top.mpr ⟨hfin6, hfinTot⟩)).mpr hSym1
  have h2r := (ENNReal.toReal_le_toReal hfin6 (ENNReal.add_ne_top.mpr ⟨hfin5, hfinTot⟩)).mpr hSym2
  rw [ENNReal.toReal_add hfin6 hfinTot, ENNReal.toReal_add hfinBad hfinCorr,
      ENNReal.toReal_add hfinB5 hfinB6, ENNReal.toReal_add hfinC5 hfinC6] at h1r
  rw [ENNReal.toReal_add hfin5 hfinTot, ENNReal.toReal_add hfinBad hfinCorr,
      ENNReal.toReal_add hfinB5 hfinB6, ENNReal.toReal_add hfinC5 hfinC6] at h2r
  rw [keyIndAdvG3_eq_abs_sub_branch, hBadSum, hCorrSum]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end KICoupling

/-- The `G3 → G3.5` key-indistinguishability coupling bound with the KEM correctness bad event. -/
theorem kiCoupling (S : Setup) : KICouplingStmt S := by
  intro P maxLen A hStop
  let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false false S P
  let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false true S P
  apply KICoupling.keyIndAdvG3_le_prob_badKeyIndFgAny_add_corr_of_tagImpl_false_false_relCoupled
    S P maxLen A
    (fun p5 p6 =>
      ((p5.1 = p6.1 ∧ LazyTagCacheAgree p5.2 p6.2) ∨
        (lazyStop p5.2.adv = true ∧ lazyStop p6.2.adv = true)) ∧
      p5 ∈ support ((simulateQ fullF A.run).run (KeyIndLazyState.empty S)) ∧
      p6 ∈ support ((simulateQ fullT A.run).run (KeyIndLazyState.empty S)))
  · exact (simulateQ_relCoupled_or_stop
      (pqxdhKeyIndAdvTagImpl false false false S P)
      (pqxdhKeyIndAdvTagImpl false false true S P)
      LazyTagCacheAgree (fun s => lazyStop s.adv) (fun s => lazyStop s.adv)
      (fun q s5 hStop5 _ hy =>
        lazyStop_mono_pqxdhKeyIndAdvTagImpl_false_false false P q s5 hStop5 hy)
      (fun q s6 hStop6 _ hy =>
        lazyStop_mono_pqxdhKeyIndAdvTagImpl_false_false true P q s6 hStop6 hy)
      (relCoupled_pqxdhKeyIndAdvTagImpl_false_false_step P)
      A.run
      (KeyIndLazyState.empty S) (KeyIndLazyState.empty S)
      (lazyTagCacheAgree_empty S)).and_support
  · rintro p5 p6 ⟨⟨hEq, hAg⟩ | ⟨hs5, hs6⟩, hp5, hp6⟩
    · left
      rw [hEq, finalizeKeyIndG3_eq_of_lazyTagCacheAgree P p6.1 p5.2 p6.2 hAg]
    · rcases hStop false p5 hp5 hs5 with hb5 | ha5 | hc5
      · exact Or.inr (Or.inl (by simp [hb5]))
      · rcases hStop true p6 hp6 hs6 with hb6 | ha6 | hc6
        · exact Or.inr (Or.inr (by simp [hb6]))
        · left
          rw [finalizeKeyIndG3_of_isKeyIndG3Abort S P true p5.1 p5.2.adv.shCr ha5,
              finalizeKeyIndG3_of_isKeyIndG3Abort S P true p6.1 p6.2.adv.shCr ha6]
        · exact Or.inr (Or.inr (by simp [hc6]))
      · exact Or.inr (Or.inl (by simp [hc5]))

end Proofs.SignalPqxdh.Security.PqxdhDelta
