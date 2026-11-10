/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key
public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.CorrAt
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.Coupling
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.Stop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-Key PQXDH `G3 -> G3.5` Hop under Imperfect KEM Correctness

**Checked by Lean.** Proves the one-key `G3 -> G3.5` `GapDhWithSign` bound
`keyIndAdvG3_1Key_le_gapDhWithSignδ` under `CryptoWellFormedPrimitivesδ` and `KemDeltaCorrect`,
accounting for the KEM decapsulation failure event `hasBadKemCorrRecords` in `runKeyIndShCrSim1Key`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-! ## `G3 -> G3.5` coupling -/

theorem evalDist_simulateQ_testImpl1Key_hasBadKemCorrRecords_eq_tagImpl1Key_false_false
    {S : Setup} (testReal : Bool) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let initTrue : KeyIndAdvCutoffState S :=
      { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false testReal S P
    𝒟[(_root_.simulateQ fullTest oa).run initTrue >>=
        fun p => pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] =
      𝒟[(_root_.simulateQ full00 oa).run (KeyIndLazyState.empty S) >>=
        fun p => pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs)]
      := by
  intro initTrue fullTest full00
  rw [evalDist_simulateQ_testImpl1Key_eq_tagImpl1Key_true_true testReal P
    (fun p => pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs))
    (fun p => pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs))
    (fun _ _ _ ⟨hEq, _⟩ => by
      subst hEq
      rfl)
    oa initTrue (KeyIndLazyState.empty S) (relEagerTag_empty S)]
  exact evalDist_simulateQ_pqxdhKeyIndAdvTagImpl1Key_true_true_eq_false_false testReal P oa
    (KICoupling.isInvariant_randLens_hasBadKemCorrRecords S P)
    (KICoupling.isInvariant_roLens_hasBadKemCorrRecords S P)
    (KeyIndLazyState.empty S)

theorem hasBadKemCorrRecords_runKeyIndAdvG3Sim1Key_eq_runKeyIndShCrSim1Key
    (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    (runKeyIndAdvG3Sim1Key S P A >>= fun x =>
      pure (hasBadKemCorrRecords S P x.2.2.shCr.initKemRecs x.2.2.shCr.recvKemRecs)) =
    (runKeyIndShCrSim1Key S P A >>= fun x =>
      pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)) := by
  rw [← runKeyIndAdvG3Sim1Key_shCr S P A, bind_map_left]
  rfl

theorem keyIndAdvG3_1Key_le_prob_badKeyIndFgAny_add_corr_of_tagImpl_false_false_relCoupled
    (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S)
    (R : Bool × KeyIndLazyState S → Bool × KeyIndLazyState S → Prop)
    (hRel :
      let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false false S P
      let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false true S P
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
    keyIndAdvG3_1Key S P A ≤
      2 * (𝒟[runKeyIndFgSim1Key S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal +
      2 * (𝒟[runKeyIndShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal := by
  let initFalse : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S false }, advRoLog := [] }
  let initTrue : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl1Key S P
  let implF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key false S P
  let implT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl1Key true S P
  let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false false S P
  let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false true S P
  have hSym := hRel.evalDist_bind_le_sym
    (fun p5 => badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog ||
      hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)
    (fun p6 => badKeyIndFgAny4 P maxLen p6.2.adv.shCr.base p6.2.adv.advRoLog ||
      hasBadKemCorrRecords S P p6.2.adv.shCr.initKemRecs p6.2.adv.shCr.recvKemRecs)
    (fun p5 => finalizeKeyIndG3 S P true p5.1 p5.2.adv.shCr)
    (fun p6 => finalizeKeyIndG3 S P true p6.1 p6.2.adv.shCr)
    hFin
  have hOrF := KICoupling.evalDist_bind_pure_or_le
    ((simulateQ fullF A.run).run (KeyIndLazyState.empty S))
    (fun p5 => badKeyIndFgAny4 P maxLen p5.2.adv.shCr.base p5.2.adv.advRoLog)
    (fun p5 => hasBadKemCorrRecords S P p5.2.adv.shCr.initKemRecs p5.2.adv.shCr.recvKemRecs)
  have hOrT := KICoupling.evalDist_bind_pure_or_le
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
  rw [← evalDist_simulateQ_testImpl1Key_finalizeKeyIndG3_eq_tagImpl1Key_false_false false P true
        A.run,
      ← evalDist_simulateQ_testImpl1Key_finalizeKeyIndG3_eq_tagImpl1Key_false_false true P true
        A.run,
      ← evalDist_simulateQ_testImpl1Key_badKeyIndFgAny_eq_tagImpl1Key_false_false false P maxLen
        A.run,
      ← evalDist_simulateQ_testImpl1Key_badKeyIndFgAny_eq_tagImpl1Key_false_false true P maxLen
        A.run,
      ← evalDist_simulateQ_testImpl1Key_hasBadKemCorrRecords_eq_tagImpl1Key_false_false false P
        A.run,
      ← evalDist_simulateQ_testImpl1Key_hasBadKemCorrRecords_eq_tagImpl1Key_false_false true P
        A.run] at hSym1 hSym2
  have hBrF : keyIndAdvG3Branch1Key false S P A =
      ((simulateQ implF A.run).run initTrue >>= fun p => finalizeKeyIndG3 S P true p.1 p.2.shCr) :=
    by
    unfold keyIndAdvG3Branch1Key
    simp only [finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true]
    have hInit : ({ shCr :=
      { base := KeyIndState.empty S false }, advRoLog := [] } : KeyIndAdvCutoffState S) =
        withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv false P A.run initTrue,
      bind_map_left]
    rfl
  have hBrT : keyIndAdvG3Branch1Key true S P A =
      ((simulateQ implT A.run).run initTrue >>= fun p => finalizeKeyIndG3 S P true p.1 p.2.shCr) :=
    by
    unfold keyIndAdvG3Branch1Key
    simp only [finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true]
    have hInit : ({ shCr :=
      { base := KeyIndState.empty S true }, advRoLog := [] } : KeyIndAdvCutoffState S) =
        withSecbAdv true initTrue := rfl
    conv_lhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  have hBadF : ((simulateQ implF A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) =
      ((simulateQ impl A.run).run initFalse >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) := by
    have hInit : initFalse = withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv false P A.run initTrue,
      bind_map_left]
    rfl
  have hBadT : ((simulateQ implT A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) =
      ((simulateQ impl A.run).run initTrue >>= fun p =>
      pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)) := by
    have hInit : initTrue = withSecbAdv true initTrue := rfl
    conv_rhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  have hCorrF : ((simulateQ implF A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) =
      ((simulateQ impl A.run).run initFalse >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) := by
    have hInit : initFalse = withSecbAdv false initTrue := rfl
    rw [hInit, simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv false P A.run initTrue,
      bind_map_left]
    rfl
  have hCorrT : ((simulateQ implT A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) =
      ((simulateQ impl A.run).run initTrue >>= fun p =>
      pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)) := by
    have hInit : initTrue = withSecbAdv true initTrue := rfl
    conv_rhs => rw [hInit]
    rw [simulateQ_pqxdhKeyIndAdvG3Impl1Key_withSecbAdv true P A.run initTrue, bind_map_left]
    rfl
  rw [← hBrF, ← hBrT, hBadF, hBadT, hCorrF, hCorrT] at hSym1 hSym2
  have hBadSum :
      2 * (𝒟[runKeyIndFgSim1Key S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal =
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}).toReal +
      (𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] {true}).toReal := by
    rw [← badKeyIndFgAny_runKeyIndAdvG3Sim1Key_eq_runKeyIndFgSim1Key]
    unfold runKeyIndAdvG3Sim1Key
    simp only [bind_assoc, pure_bind]
    exact two_mul_toReal_uniformBool_bind_eq_add_fg (fun secb =>
      (simulateQ impl A.run).run
        { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] } >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog))
  have hCorrSum :
      2 * (𝒟[runKeyIndShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal =
      (𝒟[(simulateQ impl A.run).run initFalse >>= fun p =>
        pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true}).toReal +
      (𝒟[(simulateQ impl A.run).run initTrue >>= fun p =>
        pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs)] {true}).toReal
    := by
    rw [← hasBadKemCorrRecords_runKeyIndAdvG3Sim1Key_eq_runKeyIndShCrSim1Key]
    unfold runKeyIndAdvG3Sim1Key
    simp only [bind_assoc, pure_bind]
    exact two_mul_toReal_uniformBool_bind_eq_add_fg (fun secb =>
      (simulateQ impl A.run).run
        { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] } >>=
        fun p => pure (hasBadKemCorrRecords S P p.2.shCr.initKemRecs p.2.shCr.recvKemRecs))
  have hfin5 : 𝒟[keyIndAdvG3Branch1Key false S P A] {true} ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ {true}
  have hfin6 : 𝒟[keyIndAdvG3Branch1Key true S P A] {true} ≠ ⊤ :=
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
  rw [keyIndAdvG3_1Key_eq_abs_sub_branch, hBadSum, hCorrSum]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- One-key `G3 -> G3.5` coupling bound with the KEM correctness bad event `hasBadKemCorrRecords`. -/
theorem kiCoupling1Key (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S)
    (hStop :
      ∀ (testReal : Bool),
        let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndLazyState S) ProbComp) +
          pqxdhKeyIndAdvTagImpl1Key false false testReal S P
        ∀ p ∈ support ((simulateQ full A.run).run (KeyIndLazyState.empty S)),
          lazyStop p.2.adv = true →
          badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog = true ∨
          isKeyIndG3Abort P p.2.adv.shCr = true ∨
          hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs = true) :
    keyIndAdvG3_1Key S P A ≤
      2 * (𝒟[runKeyIndFgSim1Key S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal +
      2 * (𝒟[runKeyIndShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal := by
  let fullF := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false false S P
  let fullT := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl1Key false false true S P
  apply keyIndAdvG3_1Key_le_prob_badKeyIndFgAny_add_corr_of_tagImpl_false_false_relCoupled
    S P maxLen A
    (fun p5 p6 =>
      ((p5.1 = p6.1 ∧ LazyTagCacheAgree p5.2 p6.2) ∨
        (lazyStop p5.2.adv = true ∧ lazyStop p6.2.adv = true)) ∧
      p5 ∈ support ((simulateQ fullF A.run).run (KeyIndLazyState.empty S)) ∧
      p6 ∈ support ((simulateQ fullT A.run).run (KeyIndLazyState.empty S)))
  · exact (simulateQ_relCoupled_or_stop
      (pqxdhKeyIndAdvTagImpl1Key false false false S P)
      (pqxdhKeyIndAdvTagImpl1Key false false true S P)
      LazyTagCacheAgree (fun s => lazyStop s.adv) (fun s => lazyStop s.adv)
      (fun q s5 hStop5 _ hy =>
        lazyStop_mono_pqxdhKeyIndAdvTagImpl1Key_false_false false P q s5 hStop5 hy)
      (fun q s6 hStop6 _ hy =>
        lazyStop_mono_pqxdhKeyIndAdvTagImpl1Key_false_false true P q s6 hStop6 hy)
      (relCoupled_pqxdhKeyIndAdvTagImpl1Key_false_false_step P)
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

/-! ## Single-slot KEM correctness reduction -/

def pqxdhKeyIndShCrCachedImpl1Key (checkG2 : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .initPrin u => liftKeyIndShCrBase (pqxdhKeyIndImpl1KeyReal S P (.initPrin u))
  | q => pqxdhKeyIndShCrCachedImpl checkG2 S P q

theorem pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin (checkG2 : Bool) (S : Setup)
    (P : Primitives) (q : KeyIndQuery S) (hNe : ∀ u, q ≠ .initPrin u) :
    pqxdhKeyIndShCrCachedImpl1Key checkG2 S P q = pqxdhKeyIndShCrCachedImpl checkG2 S P q := by
  cases q with
  | initPrin u => exact False.elim (hNe u rfl)
  | _ => rfl

noncomputable def tryPauseKeyIndQuery1Key (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) : Option (PausedShCrKem S (KeyIndState S)) :=
  match gq, cont with
  | .initiateOPK u i bundle, cont =>
    if bundle.opkB?.isNone then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyIndShCrCachedImpl1Key true S P)
      (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
      (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst
  | .initiateNoOPK u i bundle, cont =>
    if bundle.opkB?.isSome then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyIndShCrCachedImpl1Key true S P)
      (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
      (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst
  | _, _ => none

noncomputable def shcrChoosePkKeyInd1KeyAt (S : Setup) (P : Primitives)
    (bIdx sIdx : Nat) (A : KeyIndAdversary S) :
    Bytes → Bytes → ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes)) :=
  shcrChoosePkGenericAt P ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    (pqxdhKeyIndShCrCachedImpl1Key true S P) (tryPauseKeyIndQuery1Key S P) bIdx sIdx A.run

theorem pqxdhKeyIndImpl1KeyReal_initPrin_preserves_spkBundles (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) :
    ∀ y ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run st),
      y.2.spkBundles = st.spkBundles := by
  intro y hy
  unfold pqxdhKeyIndImpl1KeyReal at hy
  dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    rw [hFresh] at hy
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; rfl
  | false =>
    rw [hFresh] at hy
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩
    rfl

theorem pqxdhKeyIndImpl1KeyReal_initPrin_commutes_cache (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) :
    CommutesRel (cacheKeyIndAdvKeys S P) st
      (pqxdhKeyIndImpl1KeyReal S P (.initPrin u))
      (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) := by
  unfold CommutesRel pqxdhKeyIndImpl1KeyReal cacheKeyIndAdvKeys
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
    Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndShCrCachedImpl1Key_false_commutes_cache (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    CommutesRel (cacheShCrAdvKeys S P) hst
      (pqxdhKeyIndShCrCachedImpl1Key false S P q)
      (pqxdhKeyIndShCrImpl1Key false S P q) := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _
      (pqxdhKeyIndImpl1KeyReal_initPrin_commutes_cache S P u hst.base)
  · rw [pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin false S P q hNe,
        pqxdhKeyIndShCrImpl1Key_eq_of_ne_initPrin false S P q hNe]
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P q hst

theorem pqxdhKeyIndShCrCachedImpl1Key_clearFalse (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl1Key false S P q).run hst),
      clearShCrTarget x.2 = x.2 := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact liftShCrBase_clearFalse (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) hst hClear
  · rw [pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin false S P q hNe]
    exact pqxdhKeyIndShCrCachedImpl_clearFalse S P q hst hClear

theorem pqxdhKeyIndShCrCachedImpl1Key_afterGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst)
    (hGen : hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhKeyIndShCrCachedImpl1Key true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (pqxdhKeyIndShCrCachedImpl1Key false S P q).run hst) ∧
    (∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl1Key false S P q).run hst),
      hasGeneratedTargetBundle S bIdx x.2.base.spkBundles) := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact liftShCrBase_afterGen KeyIndState.spkBundles
      (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) bIdx hst
      (pqxdhKeyIndImpl1KeyReal_initPrin_preserves_spkBundles S P u hst.base) hGen
  · rw [pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin true S P q hNe,
        pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin false S P q hNe]
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx q hst hClear hGen

theorem pqxdhKeyIndShCrCachedImpl1Key_beforeGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst)
    (hNotGen : ¬ hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhKeyIndShCrCachedImpl1Key true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (pqxdhKeyIndShCrCachedImpl1Key false S P q).run hst) ∨
    ((∀ obs : (keyIndSpec S).Range q × KeyIndShCrState S → ProbComp Bool,
      𝒟[sampleKemKeyGen P >>= fun pair =>
        (pqxdhKeyIndShCrCachedImpl1Key true S P q).run (setShCrTarget hst bIdx pair.1 pair.2) >>=
          fun x => obs (x.1, clearShCrTarget x.2)] =
      𝒟[(pqxdhKeyIndShCrCachedImpl1Key false S P q).run hst >>= obs]) ∧
     (∀ pk sk,
       ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl1Key true S P q).run
         (setShCrTarget hst bIdx pk sk)),
       x.2 = setShCrTarget (clearShCrTarget x.2) bIdx pk sk ∧
       hasGeneratedTargetBundle S bIdx (clearShCrTarget x.2).base.spkBundles)) := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · left
    exact liftShCrBase_setShCrTarget (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) hst bIdx
  · rw [pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin true S P q hNe,
        pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin false S P q hNe]
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx q hst hClear hNotGen

theorem pqxdhKeyIndShCrCachedImpl1Key_validStep (S : Setup) (P : Primitives) (bIdx : Nat)
    (pk sk : Bytes) (q : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl1Key true S P q).run hst),
      ValidTargetRecv KeyIndState.spkBundles bIdx pk sk x.2 := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact liftShCrBase_validStep KeyIndState.spkBundles
      (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) bIdx pk sk hst
      (pqxdhKeyIndImpl1KeyReal_initPrin_preserves_spkBundles S P u hst.base) hV
  · rw [pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin true S P q hNe]
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk q hst hV

theorem pqxdhKeyIndShCrCachedImpl1Key_sendStep (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl1Key true S P q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact liftShCrBase_sendStep (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) hst
  · rw [pqxdhKeyIndShCrCachedImpl1Key_eq_of_ne_initPrin true S P q hNe]
    exact pqxdhKeyIndShCrCachedImpl_sendStep S P q hst

theorem pqxdhKeyIndShCrCachedImpl1Key_pauseNone (S : Setup) (P : Primitives) (sIdx : Nat)
    (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPauseKeyIndQuery1Key S P sIdx gq cont hst = none) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl1Key true S P gq).run hst),
      x.2.sendCount ≤ sIdx := by
  cases gq with
  | initPrin u =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndImpl1KeyReal S P (.initPrin u)) sIdx hst hLe
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery1Key] at hNone
    rw [show pqxdhKeyIndShCrCachedImpl1Key true S P (.initiateOPK u i bundle) =
      (if bundle.opkB?.isNone then pure .noneResp
       else runKeyIndShCrInitiate true S P (.sendOPK u i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyIndShCrCachedImpl1Key true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery1Key] at hNone
    rw [show pqxdhKeyIndShCrCachedImpl1Key true S P (.initiateNoOPK u i bundle) =
      (if bundle.opkB?.isSome then pure .noneResp
       else runKeyIndShCrInitiate true S P (.sendNoOPK u i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyIndShCrCachedImpl1Key true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | genSPK u j =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.genSPK u j) cont hst hLe rfl
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.acceptOPK k j o hdr) cont hst hLe rfl
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.acceptNoOPK k j l hdr) cont hst hLe rfl
  | corruptIK u =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.corruptIK u) cont hst hLe rfl
  | genOPK u j o =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.genOPK u j o) cont hst hLe rfl
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.testSession sid) cont hst hLe rfl
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.roQuery secrets) cont hst hLe rfl
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx .revealDhSecrets cont hst hLe rfl
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.revealSessionKey sid) cont hst hLe rfl
  | registerKey sk =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.registerKey sk) cont hst hLe rfl
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.revealSpkSk u j) cont hst hLe rfl

theorem pqxdhKeyIndShCrCachedImpl1Key_pauseSome (S : Setup) (P : Primitives) (bIdx sIdx : Nat)
    (pk sk : Bytes) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (paused : PausedShCrKem S (KeyIndState S))
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst)
    (hSome : tryPauseKeyIndQuery1Key S P sIdx gq cont hst = some paused) :
    ∃ (noneOut : (keyIndSpec S).Range gq)
      (postKem : Bytes → Bytes → ProbComp ((keyIndSpec S).Range gq × KeyIndShCrState S)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndShCrState S) ProbComp) +
              pqxdhKeyIndShCrCachedImpl1Key true S P) (cont y.1)).run y.2)) ∧
      (∀ obs : (keyIndSpec S).Range gq × KeyIndShCrState S → ProbComp Bool,
        𝒟[(pqxdhKeyIndShCrCachedImpl1Key true S P gq).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecv KeyIndState.spkBundles bIdx pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery1Key] at hSome
    rw [show pqxdhKeyIndShCrCachedImpl1Key true S P (.initiateOPK u i bundle) =
      (if bundle.opkB?.isNone then pure .noneResp
       else runKeyIndShCrInitiate true S P (.sendOPK u i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome P KeyIndState.principals KeyIndState.spkBundles
        (pqxdhKeyIndShCrCachedImpl1Key true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle)
        (.sendOPK u i) bundle (finishKeyIndBase S P (.sendOPK u i) bundle)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery1Key] at hSome
    rw [show pqxdhKeyIndShCrCachedImpl1Key true S P (.initiateNoOPK u i bundle) =
      (if bundle.opkB?.isSome then pure .noneResp
       else runKeyIndShCrInitiate true S P (.sendNoOPK u i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome P KeyIndState.principals KeyIndState.spkBundles
        (pqxdhKeyIndShCrCachedImpl1Key true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle)
        (.sendNoOPK u i) bundle (finishKeyIndBase S P (.sendNoOPK u i) bundle)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendNoOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | genSPK u j => cases hSome
  | acceptOPK k j o hdr => cases hSome
  | acceptNoOPK k j l hdr => cases hSome
  | initPrin u => cases hSome
  | corruptIK u => cases hSome
  | genOPK u j o => cases hSome
  | testSession sid => cases hSome
  | roQuery secrets => cases hSome
  | revealDhSecrets => cases hSome
  | revealSessionKey sid => cases hSome
  | registerKey sk => cases hSome
  | revealSpkSk u j => cases hSome

theorem badKemCorrProbKeyInd1KeyAt_le_kemCorrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) :
    (𝒟[runKeyIndShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
      {true}).toReal ≤
      (𝒟[kemCorrExpProb P (fun pk sk =>
          Prod.fst <$> shcrChoosePkKeyInd1KeyAt S P
            (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk)]
        {true}).toReal := by
  unfold shcrChoosePkKeyInd1KeyAt
  have hEq :
      (runKeyIndShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyIndShCrCachedImpl1Key false S P) A.run).run { base := b0 } >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    unfold runKeyIndShCrSim1Key
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hSim := CommutesRel.simulateQ_add_unif (cacheShCrAdvKeys S P)
      (pqxdhKeyIndShCrCachedImpl1Key false S P) (pqxdhKeyIndShCrImpl1Key false S P)
      (pqxdhKeyIndShCrCachedImpl1Key_false_commutes_cache S P)
      A.run { base := KeyIndState.empty S secb }
    unfold CommutesRel at hSim
    have hInit : cacheShCrAdvKeys S P { base := KeyIndState.empty S secb } =
        { base := KeyIndState.empty S secb } := rfl
    rw [hInit] at hSim
    rw [hSim, bind_map_left]
    rfl
  rw [hEq]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  exact KICorrAt.badKemCorrProbGenericAt_le_kemCorr P
    ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    KeyIndState.spkBundles
    (pqxdhKeyIndShCrCachedImpl1Key false S P)
    (pqxdhKeyIndShCrCachedImpl1Key true S P)
    (tryPauseKeyIndQuery1Key S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhKeyIndShCrCachedImpl1Key_clearFalse S P)
    (pqxdhKeyIndShCrCachedImpl1Key_afterGen S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl1Key_beforeGen S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl1Key_validStep S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl1Key_sendStep S P)
    (pqxdhKeyIndShCrCachedImpl1Key_pauseNone S P (idx % S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl1Key_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

theorem prob_hasBadKemCorrRecords_1Key_le (S : Setup) (P : Primitives)
    (δ : ℝ) (hδ : KemDeltaCorrectReal P δ) (A : KeyIndAdversary S) :
    (𝒟[runKeyIndShCrSim1Key S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
  have hU := _root_.SignalPqxdh.Security.toReal_any_range_le_sum (runKeyIndShCrSim1Key S P A)
    (S.N_spk_tot * S.N_send_tot)
    (fun idx x => hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)
  refine le_trans hU ?_
  calc (∑ k ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        (𝒟[runKeyIndShCrSim1Key S P A >>= fun x =>
          pure (hasBadKemCorrRecordsAt S P k x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal)
      ≤ ∑ _k ∈ Finset.range (S.N_spk_tot * S.N_send_tot), δ := by
        refine Finset.sum_le_sum (fun k _hk => ?_)
        exact le_trans (badKemCorrProbKeyInd1KeyAt_le_kemCorrProb S P k A)
          (kemCorrExpProb_le P δ hδ _)
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Proofs.SignalPqxdh.Security.PqxdhDelta

namespace Proofs.SignalPqxdh.Security

theorem keyIndAdvG3_1Key_le_prob_badKeyIndFgAny4_add_corr_1Key
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    keyIndAdvG3_1Key S P A.1 ≤
      2 * (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true}).toReal +
      2 * (𝒟[runKeyIndShCrSim1Key S P A.1 >>= fun x =>
        pure (PqxdhDelta.hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)]
          {true}).toReal := by
  apply PqxdhDelta.kiCoupling1Key S P b.q_ro A.1
  intro testReal full p hp hS
  exact PqxdhDelta.kiStop S P hP b.q_ro p.2.adv
    (validTagState_of_mem_support_simulateQ1Key P false false testReal b A p hp) hS

/-- One-key `G3 -> G3.5` `GapDhWithSign` bound under `CryptoWellFormedPrimitivesδ` and
    `KemDeltaCorrectReal`. -/
theorem keyIndAdvG3_1Key_le_gapDhWithSignδ
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    keyIndAdvG3_1Key S P A.1 ≤
      2 * (((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
            (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
            (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
            GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAdv4 S b A)) +
      kemDecapsFailureTermReal S δ := by
  have hC := keyIndAdvG3_1Key_le_prob_badKeyIndFgAny4_add_corr_1Key S P hP b A
  have hG := prob_badKeyIndFgAny4_1Key_le_gapDhWithSign S b P hP A
  have hCorr := PqxdhDelta.prob_hasBadKemCorrRecords_1Key_le S P δ hδ A.1
  have hTerm : 2 * ((S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ) = kemDecapsFailureTermReal S δ := by
    unfold kemDecapsFailureTermReal; ring
  linarith

end Proofs.SignalPqxdh.Security
