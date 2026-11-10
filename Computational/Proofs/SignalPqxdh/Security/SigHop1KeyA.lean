/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
public import Computational.Proofs.SignalPqxdh.Security.Collisions
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `KeyInd` Collision Hops and `GapSigEufCma` Simulation Infrastructure

**Checked by Lean.** Defines hybrids `G0` through `G2_1` for the one-key random-oracle handshake
game `pqxdhKeyIndImpl1KeyRo`, proves the birthday-collision bounds for `G0 → G0_1` and
`G2 → G2_1`, and establishes the `simulateQ` and `clearFgTargetSign` commutation lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp ENNReal MeasureTheory BigOperators
open SignalPqxdh.Security.RoKem
open SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh

/-! ## One-key hybrid games `G0` through `G2_1` -/

noncomputable def runKeyInd1KeySim (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp (Bool × Bool × KeyIndState S) := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl1KeyRo S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)

def keyInd1KeyAllTestedClean {S : Setup} (P : Primitives) (finalSt : KeyIndState S) : Bool :=
  finalSt.sessions.all (fun s =>
    !s.tested ||
      isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles finalSt.respSessions s) &&
  finalSt.respSessions.all (fun r =>
    !r.tested ||
      isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles finalSt.sessions r)

/-- One-key `KeyInd` hybrid `G0`: `pqxdhKeyInd1KeyExpForHandshake` on `pqxdhKeyIndImpl1KeyRo`. -/
noncomputable def keyInd1KeyExpG0 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  pqxdhKeyInd1KeyExpForHandshake S P (pqxdhKeyIndImpl1KeyRo S P) A

/-- One-key `KeyInd` hybrid `G0_1`: aborts with a uniform coin on `hasEcPkCollisionKeyInd`. -/
noncomputable def keyInd1KeyExpG0_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalSt) ← runKeyInd1KeySim S P A
  if !keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt then
    $ᵗ Bool
  else
    return (b' == secb)

/-- One-key `KeyInd` hybrid `G1`: additionally aborts on `hasBadSigKeyInd`. -/
noncomputable def keyInd1KeyExpG1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalSt) ← runKeyInd1KeySim S P A
  if (!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
     hasBadSigKeyInd finalSt then
    $ᵗ Bool
  else
    return (b' == secb)

/-- One-key `KeyInd` hybrid `G2`: syntactic alias of `keyInd1KeyExpG1`. -/
noncomputable def keyInd1KeyExpG2 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  keyInd1KeyExpG1 S P A

/-- One-key `KeyInd` hybrid `G2_1`: additionally aborts on `hasKemPkCollisionKeyInd`. -/
noncomputable def keyInd1KeyExpG2_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalSt) ← runKeyInd1KeySim S P A
  if ((!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
      hasBadSigKeyInd finalSt) ||
     hasKemPkCollisionKeyInd finalSt then
    $ᵗ Bool
  else
    return (b' == secb)

noncomputable def keyInd1KeyAdvG0 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG0 S P A].boolBias).toReal

noncomputable def keyInd1KeyAdvG0_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG0_1 S P A].boolBias).toReal

noncomputable def keyInd1KeyAdvG1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG1 S P A].boolBias).toReal

noncomputable def keyInd1KeyAdvG2 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG2 S P A].boolBias).toReal

noncomputable def keyInd1KeyAdvG2_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG2_1 S P A].boolBias).toReal

theorem keyInd1KeyAdvG0_eq (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyInd1KeyAdvG0 S P A = KeyInd1KeyRoAdvantageReal S P A := rfl

theorem keyInd1KeyAdvG1_eq_G2 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyInd1KeyAdvG1 S P A = keyInd1KeyAdvG2 S P A := rfl

noncomputable def ecCollProbKeyInd1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
    pure (hasEcPkCollisionKeyInd P finalSt)] {true}).toReal

noncomputable def kemCollProbKeyInd1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
    pure (hasKemPkCollisionKeyInd finalSt)] {true}).toReal

noncomputable def badSigProbKeyInd1Key (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeySim S P A >>= fun (_, _, finalSt) =>
    pure (hasBadSigKeyInd finalSt)] {true}).toReal

theorem keyInd1Key_hop_G0_G0_1_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG0 S P A - keyInd1KeyAdvG0_1 S P A| ≤ ecCollProbKeyInd1Key S P A := by
  have h1 : keyInd1KeyExpG0 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if !keyInd1KeyAllTestedClean P finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG0, pqxdhKeyInd1KeyExpForHandshake, runKeyInd1KeySim,
      keyInd1KeyAllTestedClean, bind_assoc]
  have h2 : keyInd1KeyExpG0_1 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if !keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG0_1]
  unfold keyInd1KeyAdvG0 keyInd1KeyAdvG0_1 ecCollProbKeyInd1Key
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyInd1KeySim S P A)
    (fun (_, _, finalSt) => !keyInd1KeyAllTestedClean P finalSt)
    (fun (_, _, finalSt) => hasEcPkCollisionKeyInd P finalSt)
    (fun (secb, b', _) => pure (b' == secb))

theorem keyInd1Key_hop_G0_1_G1_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG0_1 S P A - keyInd1KeyAdvG1 S P A| ≤ badSigProbKeyInd1Key S P A := by
  have h1 : keyInd1KeyExpG0_1 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if !keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG0_1]
  have h2 : keyInd1KeyExpG1 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if (!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
           hasBadSigKeyInd finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG1]
  unfold keyInd1KeyAdvG0_1 keyInd1KeyAdvG1 badSigProbKeyInd1Key
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyInd1KeySim S P A)
    (fun (_, _, finalSt) => !keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt)
    (fun (_, _, finalSt) => hasBadSigKeyInd finalSt)
    (fun (secb, b', _) => pure (b' == secb))

theorem keyInd1Key_hop_G2_G2_1_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG2 S P A - keyInd1KeyAdvG2_1 S P A| ≤ kemCollProbKeyInd1Key S P A := by
  have h1 : keyInd1KeyExpG2 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if (!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
           hasBadSigKeyInd finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG2, keyInd1KeyExpG1]
  have h2 : keyInd1KeyExpG2_1 S P A =
      (runKeyInd1KeySim S P A >>= fun (secb, b', finalSt) =>
        if ((!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
            hasBadSigKeyInd finalSt) ||
           hasKemPkCollisionKeyInd finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyInd1KeyExpG2_1]
  unfold keyInd1KeyAdvG2 keyInd1KeyAdvG2_1 kemCollProbKeyInd1Key
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyInd1KeySim S P A)
    (fun (_, _, finalSt) =>
      (!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
      hasBadSigKeyInd finalSt)
    (fun (_, _, finalSt) => hasKemPkCollisionKeyInd finalSt)
    (fun (secb, b', _) => pure (b' == secb))

/-! ## One-key birthday collision bounds -/

theorem pqxdhKeyIndImpl1KeyRo_kem_step (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (b1 b2 : Nat)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : ValidSpkBundlesKem S st.spkBundles) :
    (∀ x ∈ support ((pqxdhKeyIndImpl1KeyRo S P q).run st),
      ValidSpkBundlesKem S x.2.spkBundles) ∧
    probExpect ((pqxdhKeyIndImpl1KeyRo S P q).run st)
      (fun x => kemPairPotential S x.2.spkBundles b1 b2) ≤
      kemPairPotential S st.spkBundles b1 b2 := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      simp [StateT.run_pure, probExpect_pure, hV]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        probExpect_bind, probExpect_pure]
      refine ⟨?_, probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)⟩
      intro x hx
      rw [MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨_, _, hx⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact hV
  | _ =>
    exact pqxdhKeyIndImpl_valid_and_potential_le true S P hCWF b1 b2 _ st hV

theorem kemCollProbKeyInd1Key_le_bound (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    kemCollProbKeyInd1Key S P A ≤ ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  unfold kemCollProbKeyInd1Key runKeyInd1KeySim hasKemPkCollisionKeyInd
  exact kemCollProb_simulateQ_le S KeyIndState.spkBundles (KeyIndState.empty S)
    (fun _ => rfl) (pqxdhKeyIndImpl1KeyRo S P)
    (fun q st hV => (pqxdhKeyIndImpl1KeyRo_kem_step S P hCWF 0 0 q st hV).1)
    (fun b1 b2 q st hV => (pqxdhKeyIndImpl1KeyRo_kem_step S P hCWF b1 b2 q st hV).2)
    A.run

theorem keyInd1Key_hop_G2_G2_1_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG2 S P A - keyInd1KeyAdvG2_1 S P A| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
  (keyInd1Key_hop_G2_G2_1_le_prob S P A).trans (kemCollProbKeyInd1Key_le_bound S P hCWF A)

theorem pqxdhKeyIndImpl1KeyRo_ec_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S) (s1 s2 : Nat) (hV : ValidKeyIndEc S st) :
    (∀ x ∈ support ((pqxdhKeyIndImpl1KeyRo S P q).run st), ValidKeyIndEc S x.2) ∧
    probExpect ((pqxdhKeyIndImpl1KeyRo S P q).run st)
      (fun x => ecPairPotential P (ecTaggedKeyInd S P x.2) s1 s2) ≤
      ecPairPotential P (ecTaggedKeyInd S P st) s1 s2 := by
  cases q with
  | initPrin u =>
    rcases hV with ⟨hVP, hVS, hVO, hVSess⟩
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, _, rfl⟩
        exact ⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩
      · simp only [probExpect_bind, probExpect_pure]
        have hNotIn := (validPrincipals_cons S u
          { secIKA0 := [], ikAPk := [], secIKAsign := [], ikSignPk := [], corrupted := false }
          st.principals hVP hFresh).2
        exact probExpect_ecTaggedFromLists_cons_prin_le S P hP u
          st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st) hNotIn
          (fun sk => {
            secIKA0 := sk, ikAPk := P.x25519Base sk,
            secIKAsign := sk, ikSignPk := P.x25519Base sk, corrupted := false })
          (fun _ => rfl) s1 s2
    | true =>
      simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | _ =>
    exact pqxdhKeyIndImpl_ec_step true S P hP _ st s1 s2 hV

theorem pqxdhKeyIndImpl1KeyRo_dh2_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S) (s1 s2 : Nat) (hV : ValidKeyIndDh2 S P st) :
    (∀ x ∈ support ((pqxdhKeyIndImpl1KeyRo S P q).run st), ValidKeyIndDh2 S P x.2) ∧
    probExpect ((pqxdhKeyIndImpl1KeyRo S P q).run st)
      (fun x => dh2UpperPairPotential (dh2TaggedKeyInd S P x.2) s1 s2) ≤
      dh2UpperPairPotential (dh2TaggedKeyInd S P st) s1 s2 := by
  cases q with
  | initPrin u =>
    have hEcStep := (pqxdhKeyIndImpl1KeyRo_ec_step S P hP (.initPrin u) st 0 0 hV.1).1
    refine ⟨fun x hx => ⟨hEcStep x hx, ?_⟩, ?_⟩
    · unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hx; dsimp only at hx
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
      cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) with
      | false =>
        rw [hFresh] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, hSec0, rfl⟩
        refine ⟨?_, hV.2.2⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | hmem
        · exact ⟨length_of_mem_support_sampleScalar32_coll hSec0, rfl⟩
        · exact hV.2.1 e hmem
      | true =>
        rw [hFresh] at hx
        simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨hV.2.1, hV.2.2⟩
    · unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal; dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.principals.any (fun (idx, _) => idx == u.val) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          probExpect_bind, probExpect_pure]
        exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
      | true =>
        simp [StateT.run_pure, probExpect_pure]
  | _ =>
    exact pqxdhKeyIndImpl_dh2_step true S P hP _ st s1 s2 hV

theorem pqxdhKeyIndImpl1KeyRo_combined_ec_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S) (s1 s2 : Nat) (hV : ValidKeyIndDh2 S P st) :
    probExpect ((pqxdhKeyIndImpl1KeyRo S P q).run st)
      (fun x => ecKeyIndPairPotential S P x.2 s1 s2) ≤
      ecKeyIndPairPotential S P st s1 s2 := by
  unfold ecKeyIndPairPotential
  split_ifs
  · exact (pqxdhKeyIndImpl1KeyRo_ec_step S P hP q st s1 s2 hV.1).2
  · exact (pqxdhKeyIndImpl1KeyRo_dh2_step S P hP q st s1 s2 hV).2
  · simp [probExpect_const]

theorem simulateQ_1Key_valid_and_ecKeyIndPairPotential_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (s1 s2 : Nat)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) (st : KeyIndState S)
    (hV : ValidKeyIndDh2 S P st) :
    (∀ x ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) +
        pqxdhKeyIndImpl1KeyRo S P) oa).run st), ValidKeyIndDh2 S P x.2) ∧
    probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) +
        pqxdhKeyIndImpl1KeyRo S P) oa).run st)
      (fun x => ecKeyIndPairPotential S P x.2 s1 s2) ≤
      ecKeyIndPairPotential S P st s1 s2 := by
  let fullImpl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl1KeyRo S P
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [StateT.run_pure] at hx
      rcases hx with ⟨_, rfl⟩
      exact hV
    · simp [StateT.run_pure, probExpect_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      have hrun :
          (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
          (do let u ← liftM (unifSpec.query uq); (simulateQ fullImpl (oa u)).run st) := by
        simp [fullImpl, simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]
      rw [hrun]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨u, _, hx⟩
        exact (ih u st hV).1 x hx
      · rw [probExpect_bind]
        exact probExpect_const_le_of_support _ _ _ (fun u _ => (ih u st hV).2)
    | inr gq =>
      have hrun :
          (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
          (do
            let y ← (pqxdhKeyIndImpl1KeyRo S P gq).run st
            (simulateQ fullImpl (oa y.1)).run y.2) := by
        simp [fullImpl, simulateQ_bind, StateT.run_bind]
      rw [hrun]
      have hV_step := (pqxdhKeyIndImpl1KeyRo_dh2_step S P hP gq st 0 0 hV).1
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨y, hy, hx⟩
        exact (ih y.1 y.2 (hV_step y hy)).1 x hx
      · rw [probExpect_bind]
        calc probExpect ((pqxdhKeyIndImpl1KeyRo S P gq).run st)
              (fun y => probExpect ((simulateQ fullImpl (oa y.1)).run y.2)
                (fun x => ecKeyIndPairPotential S P x.2 s1 s2))
            ≤ probExpect ((pqxdhKeyIndImpl1KeyRo S P gq).run st)
                (fun y => ecKeyIndPairPotential S P y.2 s1 s2) :=
              probExpect_mono_of_support _ _ _ (fun y hy => (ih y.1 y.2 (hV_step y hy)).2)
          _ ≤ ecKeyIndPairPotential S P st s1 s2 :=
              pqxdhKeyIndImpl1KeyRo_combined_ec_step S P hP gq st s1 s2 hV

theorem ecCollProbKeyInd1Key_le_bound (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    ecCollProbKeyInd1Key S P A ≤
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  unfold ecCollProbKeyInd1Key
  let fullImpl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl1KeyRo S P
  let runSim := runKeyInd1KeySim S P A
  have hSim := fun s1 s2 secb =>
    simulateQ_1Key_valid_and_ecKeyIndPairPotential_le S P hCWF s1 s2 A.run
      (KeyIndState.empty S secb) (validKeyIndDh2_empty S P secb)
  have hV_runSim : ∀ x ∈ support runSim, ValidKeyIndDh2 S P x.2.2 := by
    intro x hx
    simp only [runSim, runKeyInd1KeySim, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨secb, _, ⟨b', finalSt⟩, hmem, rfl⟩
    exact (hSim 0 0 secb).1 (b', finalSt) hmem
  have hPair_base : ∀ s1 s2 : Nat,
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true}).toReal ≤
      Pfixed_pk_ec := by
    intro s1 s2
    have h_enn :
        𝒟[runSim >>= fun (_, _, finalSt) =>
          pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true} ≤
        ENNReal.ofReal Pfixed_pk_ec := by
      rw [evalDist_bind_true_eq_probExpect]
      simp only [runSim, runKeyInd1KeySim, probExpect_bind, probExpect_pure]
      apply probExpect_const_le_of_support; intro secb _
      calc probExpect ((simulateQ fullImpl A.run).run (KeyIndState.empty S secb))
            (fun x => 𝒟[(pure (hasKeyIndEcPairCollAt S P x.2 s1 s2) : ProbComp Bool)] {true})
          ≤ probExpect ((simulateQ fullImpl A.run).run (KeyIndState.empty S secb))
              (fun x => ecKeyIndPairPotential S P x.2 s1 s2) :=
            probExpect_mono_of_support _ _ _ (fun x _ =>
              evalDist_hasKeyIndEcPairCollAt_le_potential S P x.2 s1 s2)
        _ ≤ ecKeyIndPairPotential S P (KeyIndState.empty S secb) s1 s2 := (hSim s1 s2 secb).2
        _ ≤ ENNReal.ofReal Pfixed_pk_ec := ecKeyIndPairPotential_empty_le S P secb s1 s2
    have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h_enn
    rwa [ENNReal.toReal_ofReal pfixed_pk_ec_nonneg] at hreal
  have hPair_le : ∀ s1 s2 : Nat,
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true}).toReal ≤
      if s2 < s1 then Pfixed_pk_ec
      else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then Pfixed_pk_ec
      else 0 := by
    intro s1 s2
    by_cases h1 : s2 < s1
    · simp only [h1, ↓reduceIte]; exact hPair_base s1 s2
    · simp only [h1, ↓reduceIte]
      by_cases h2 : S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2
      · simp only [h2, and_self, ↓reduceIte]; exact hPair_base s1 s2
      · have h0 : 𝒟[runSim >>= fun (_, _, finalSt) =>
            pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true} ≤ 0 := by
          rw [evalDist_bind_true_eq_probExpect]
          refine probExpect_const_le_of_support _ _ 0 (fun _ _ => ?_)
          simp [hasKeyIndEcPairCollAt, h1, h2]
        simp only [le_antisymm h0 zero_le, h2, ↓reduceIte, ENNReal.toReal_zero, le_rfl]
  calc (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasEcPkCollisionKeyInd P finalSt)] {true}).toReal
      ≤ (𝒟[runSim >>= fun (_, _, finalSt) =>
          pure ((List.range S.N_dh).any (fun s1 =>
            (List.range S.N_dh).any (fun s2 =>
              hasKeyIndEcPairCollAt S P finalSt s1 s2)))] {true}).toReal :=
        toReal_bind_bool_mono_of_support runSim _ _ (fun x hx hdup =>
          hasEcPkCollisionKeyInd_imp_any_double_range S P x.2.2 (hV_runSim x hx) hdup)
    _ ≤ ∑ s1 ∈ Finset.range S.N_dh,
          (𝒟[runSim >>= fun (_, _, finalSt) =>
            pure ((List.range S.N_dh).any (fun s2 =>
              hasKeyIndEcPairCollAt S P finalSt s1 s2))] {true}).toReal :=
        toReal_any_range_le_sum runSim S.N_dh
          (fun s1 x => (List.range S.N_dh).any (fun s2 => hasKeyIndEcPairCollAt S P x.2.2 s1 s2))
    _ ≤ ∑ s1 ∈ Finset.range S.N_dh,
          ∑ s2 ∈ Finset.range S.N_dh,
            (𝒟[runSim >>= fun (_, _, finalSt) =>
              pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true}).toReal :=
        Finset.sum_le_sum (fun s1 _ =>
          toReal_any_range_le_sum runSim S.N_dh
            (fun s2 x => hasKeyIndEcPairCollAt S P x.2.2 s1 s2))
    _ ≤ ∑ s1 ∈ Finset.range S.N_dh,
          ∑ s2 ∈ Finset.range S.N_dh,
            (if s2 < s1 then Pfixed_pk_ec
             else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then Pfixed_pk_ec
             else 0) :=
        Finset.sum_le_sum (fun s1 _ => Finset.sum_le_sum (fun s2 _ => hPair_le s1 s2))
    _ = ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
        rw [sum_keyIndEcGrid_const]
        unfold Pfixed_pk_ec
        ring

theorem keyInd1Key_hop_G0_G0_1_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG0 S P A - keyInd1KeyAdvG0_1 S P A| ≤
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 :=
  (keyInd1Key_hop_G0_G0_1_le_prob S P A).trans (ecCollProbKeyInd1Key_le_bound S P hCWF A)

/-! ## `GapSigEufCma` oracle implementation and `simulateQ` lemmas -/

noncomputable def gapSigEufCmaSigImpl (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec (StateT (List Bytes) ProbComp) := fun (.sign m) => do
  let r ← liftM sampleRandom64
  let sig := P.sigSign sk m r
  modify (m :: ·)
  return sig

noncomputable def gapSigEufCmaDdhImpl (ddh : Bytes → Bytes → Bytes → Bool) :
    QueryImpl gapDhOracleSpec (StateT (List Bytes) ProbComp) := fun (X, Y, Z) =>
  pure (ddh X Y Z)

noncomputable def gapSigEufCmaFullImpl (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    QueryImpl SigDdhSimSpec (StateT (List Bytes) ProbComp) :=
  (primBaseImpl P).liftTarget (StateT (List Bytes) ProbComp) +
    (gapSigEufCmaSigImpl P sk + gapSigEufCmaDdhImpl ddh)

theorem gapSigEufCmaExp_eq_fullImpl (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaAdv) :
    gapSigEufCmaExp P ddh A = (do
      let sk ← sampleScalar32
      let pk := P.sigPkGen sk
      let ((mStar, sigStar), signedMsgs) ←
        (simulateQ (gapSigEufCmaFullImpl P ddh sk) (A.run pk)).run []
      return (P.sigVerify pk mStar sigStar && decide (mStar ∉ signedMsgs))) := rfl

@[simp]
theorem simulateQ_embedPrim_sigDdh_run {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (mx : OracleComp PrimBaseSpec α) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (embedPrim (spec := sigAndDdhSpec) mx)).run msgs =
      (fun a => (a, msgs)) <$> simulateQ (primBaseImpl P) mx :=
  simulateQ_embedPrim_run P (gapSigEufCmaSigImpl P sk + gapSigEufCmaDdhImpl ddh) mx msgs

@[simp]
theorem simulateQ_unifSigDdh_run {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (mx : ProbComp α) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (unifSigDdh mx)).run msgs =
      (fun a => (a, msgs)) <$> mx := by
  unfold unifSigDdh
  rw [simulateQ_embedPrim_sigDdh_run, simulateQ_embedUnif]

@[simp]
theorem simulateQ_primSigDdhQ_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (q : PrimQuery) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (primSigDdhQ q)).run msgs =
      (fun a => (a, msgs)) <$> primImpl P q := by
  unfold primSigDdhQ gapSigEufCmaFullImpl
  simp [QueryImpl.liftTarget, primBaseImpl, StateT.run_monadLift]

@[simp]
theorem simulateQ_sigChalQ_run (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (msg : Bytes) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (sigChalQ msg)).run msgs =
      (fun r => (P.sigSign sk msg r, msg :: msgs)) <$> sampleRandom64 := by
  unfold sigChalQ gapSigEufCmaFullImpl gapSigEufCmaSigImpl
  simp [StateT.run_bind, StateT.run_monadLift, StateT.run_modify, map_eq_bind_pure_comp]

theorem embedGdhSigDdh_pure {α : Type} (x : α) :
    embedGdhSigDdh (pure x) = pure x := rfl

theorem embedGdhSigDdh_query_inl {α : Type} (pq : PrimBaseSpec.Domain)
    (k : PrimBaseSpec.Range pq → OracleComp GdhSimSpec α) :
    embedGdhSigDdh (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl pq)) >>= k) =
      (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl pq)) >>=
        fun u => embedGdhSigDdh (k u)) := rfl

theorem embedGdhSigDdh_query_inr {α : Type} (dq : gapDhOracleSpec.Domain)
    (k : gapDhOracleSpec.Range dq → OracleComp GdhSimSpec α) :
    embedGdhSigDdh (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inr dq)) >>= k) =
      (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
        fun b => embedGdhSigDdh (k b)) := rfl

@[simp]
theorem simulateQ_embedGdhSigDdh_run {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (mx : OracleComp GdhSimSpec α) (msgs : List Bytes) :
    (simulateQ (gapSigEufCmaFullImpl P ddh sk) (embedGdhSigDdh mx)).run msgs =
      (fun a => (a, msgs)) <$> simulateQ (gapDhFullImpl P ddh) mx := by
  induction mx using OracleComp.inductionOn generalizing msgs with
  | pure a => simp [embedGdhSigDdh_pure]
  | query_bind q k ih =>
    cases q with
    | inl pq =>
      rw [embedGdhSigDdh_query_inl]
      simp only [gapSigEufCmaFullImpl, gapDhFullImpl, simulateQ_bind, StateT.run_bind,
        QueryImpl.simulateQ_add_query_left, QueryImpl.liftTarget_apply,
        StateT.run_monadLift, monadLift_self, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      congr 1; ext u
      rw [← map_eq_bind_pure_comp]
      exact ih u msgs
    | inr dq =>
      rcases dq with ⟨X, Y, Z⟩
      rw [embedGdhSigDdh_query_inr]
      have hqL :
          (simulateQ (gapSigEufCmaFullImpl P ddh sk)
            (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr (X, Y, Z)))))).run msgs =
          pure (ddh X Y Z, msgs) := rfl
      have hqR :
          simulateQ (gapDhFullImpl P ddh)
            (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inr (X, Y, Z)))) =
          pure (ddh X Y Z) := rfl
      simp only [simulateQ_bind, StateT.run_bind, hqL, hqR, pure_bind]
      exact ih (ddh X Y Z) msgs

theorem runWithSigDdhStep_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp SigDdhSimSpec (GSpec.Range q × St))
    (x : α) (st : St) :
    runWithSigDdhStep step (pure x) st = pure (x, st) := rfl

theorem runWithSigDdhStep_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp SigDdhSimSpec (GSpec.Range q × St))
    (n : ℕ) (k : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithSigDdhStep step (liftM (OracleSpec.query (Sum.inl n)) >>= k) st =
      (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => runWithSigDdhStep step (k u) st) := rfl

theorem runWithSigDdhStep_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp SigDdhSimSpec (GSpec.Range q × St))
    (gq : ιI) (k : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithSigDdhStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= k) st =
      (step gq st >>= fun p => runWithSigDdhStep step (k p.1) p.2) := rfl

/-! ## Erasing target `secIKAsign` on `FgKeyIndSimState` -/

def clearPrincipalsTargetSign (kIdx : ℕ) (principals : List (Nat × PrincipalEntry)) :
    List (Nat × PrincipalEntry) :=
  principals.map (fun (idx, e) =>
    if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e))

/-- Erase `secIKAsign := []` on target principal `kIdx` inside `FgKeyIndSimState S`. -/
def clearFgTargetSign {S : Setup} (kIdx : ℕ) (st : FgKeyIndSimState S) : FgKeyIndSimState S :=
  { st with base := { st.base with principals := clearPrincipalsTargetSign kIdx st.base.principals } }

@[simp]
theorem length_clearPrincipalsTargetSign (kIdx : ℕ) (principals : List (Nat × PrincipalEntry)) :
    (clearPrincipalsTargetSign kIdx principals).length = principals.length := by
  simp [clearPrincipalsTargetSign]

theorem clearPrincipalsTargetSign_take (kIdx n : ℕ) (principals : List (Nat × PrincipalEntry)) :
    (clearPrincipalsTargetSign kIdx principals).take n =
      clearPrincipalsTargetSign kIdx (principals.take n) := by
  simp [clearPrincipalsTargetSign, List.map_take]

theorem findHonestPrincipal_clearPrincipalsTargetSign (P : Primitives) (kIdx : ℕ) :
    ∀ (principals : List (Nat × PrincipalEntry)) (ikB : Bytes),
      findHonestPrincipal P (clearPrincipalsTargetSign kIdx principals) ikB =
        (findHonestPrincipal P principals ikB).map (fun (idx, e) =>
          if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e))
  | [], _ => rfl
  | (idx, e) :: tl, ikB => by
    have hcons :
        clearPrincipalsTargetSign kIdx ((idx, e) :: tl) =
        (if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e)) ::
          clearPrincipalsTargetSign kIdx tl := rfl
    rw [hcons]
    unfold findHonestPrincipal
    simp only [List.find?_cons]
    have hpow :
        (P.pow8 ikB ==
          P.pow8 (if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e)).2.ikAPk) =
        (P.pow8 ikB == P.pow8 e.ikAPk) := by
      cases idx == kIdx <;> rfl
    rw [hpow]
    cases P.pow8 ikB == P.pow8 e.ikAPk
    · exact findHonestPrincipal_clearPrincipalsTargetSign P kIdx tl ikB
    · rfl

@[simp]
theorem findHonestPrincipal_isSome_clearPrincipalsTargetSign (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    (findHonestPrincipal P (clearPrincipalsTargetSign kIdx principals) ikB).isSome =
      (findHonestPrincipal P principals ikB).isSome := by
  rw [findHonestPrincipal_clearPrincipalsTargetSign]
  cases findHonestPrincipal P principals ikB <;> rfl

@[simp]
theorem resolveSigPk_clearPrincipalsTargetSign (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    resolveSigPk P (clearPrincipalsTargetSign kIdx principals) ikB =
      resolveSigPk P principals ikB := by
  unfold resolveSigPk
  rw [findHonestPrincipal_clearPrincipalsTargetSign]
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    simp only [Option.map_some]
    cases idx == kIdx <;> rfl

@[simp]
theorem isHonestUncorruptedPeer_clearPrincipalsTargetSign (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    isHonestUncorruptedPeer P (clearPrincipalsTargetSign kIdx principals) ikB =
      isHonestUncorruptedPeer P principals ikB := by
  unfold isHonestUncorruptedPeer
  rw [findHonestPrincipal_clearPrincipalsTargetSign]
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    simp only [Option.map_some]
    cases idx == kIdx <;> rfl

@[simp]
theorem checkBundleProvenanceTake_clearPrincipalsTargetSign (S : Setup) (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    checkBundleProvenanceTake S P (clearPrincipalsTargetSign kIdx principals)
      spkBundles opkEntries bundle =
      checkBundleProvenanceTake S P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenanceTake
  rw [clearPrincipalsTargetSign_take, findHonestPrincipal_clearPrincipalsTargetSign]
  cases findHonestPrincipal P (principals.take S.N_dh) bundle.ikB with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    simp only [Option.map_some]
    cases idx == kIdx <;> rfl

@[simp]
theorem koskBundleOkTake_clearPrincipalsTargetSign (S : Setup) (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput) :
    koskBundleOkTake S P (clearPrincipalsTargetSign kIdx principals)
      spkBundles opkEntries advKeyPows bundle =
      koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle := by
  unfold koskBundleOkTake
  rw [clearPrincipalsTargetSign_take, findHonestPrincipal_isSome_clearPrincipalsTargetSign]

@[simp]
theorem koskSenderOkTake_clearPrincipalsTargetSign (S : Setup) (P : Primitives) (kIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows : List (Bytes × Bytes))
    (ikAPk : Bytes) :
    koskSenderOkTake S P (clearPrincipalsTargetSign kIdx principals) advKeyPows ikAPk =
      koskSenderOkTake S P principals advKeyPows ikAPk := by
  unfold koskSenderOkTake
  rw [clearPrincipalsTargetSign_take, findHonestPrincipal_isSome_clearPrincipalsTargetSign]

theorem find?_idx_clearPrincipalsTargetSign (kIdx u : ℕ) :
    ∀ (principals : List (Nat × PrincipalEntry)),
      (clearPrincipalsTargetSign kIdx principals).find? (fun (idx, _) => idx == u) =
        (principals.find? (fun (idx, _) => idx == u)).map (fun (idx, e) =>
          if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e))
  | [] => rfl
  | (idx, e) :: tl => by
    have hcons :
        clearPrincipalsTargetSign kIdx ((idx, e) :: tl) =
        (if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e)) ::
          clearPrincipalsTargetSign kIdx tl := rfl
    rw [hcons]
    simp only [List.find?_cons]
    have hidx :
        ((if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e)).1 == u) =
        (idx == u) := by
      cases idx == kIdx <;> rfl
    rw [hidx]
    cases idx == u
    · exact find?_idx_clearPrincipalsTargetSign kIdx u tl
    · rfl

theorem any_idx_clearPrincipalsTargetSign (kIdx u : ℕ) :
    ∀ (principals : List (Nat × PrincipalEntry)),
      (clearPrincipalsTargetSign kIdx principals).any (fun (idx, _) => idx == u) =
        principals.any (fun (idx, _) => idx == u)
  | [] => rfl
  | (idx, e) :: tl => by
    have hcons :
        clearPrincipalsTargetSign kIdx ((idx, e) :: tl) =
        (if idx == kIdx then (idx, { e with secIKAsign := [] }) else (idx, e)) ::
          clearPrincipalsTargetSign kIdx tl := rfl
    rw [hcons, List.any_cons, List.any_cons]
    cases idx == kIdx <;> simp [any_idx_clearPrincipalsTargetSign kIdx u tl]

theorem initSessionSlotIdx_lt_of_isSendSessionId {S : Setup} (sid : SessionId S)
    (hSend : IsSendSessionId S sid) : initSessionSlotIdx sid < S.N_send_tot := by
  cases sid with
  | sendOPK u' i' =>
    unfold initSessionSlotIdx Setup.N_send_tot Setup.N_send_opk_tot
    have hu1 : u'.val + 1 ≤ S.N_id := Nat.succ_le_of_lt u'.isLt
    calc u'.val * S.N_send_opk + i'.val
        < u'.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left i'.isLt _
      _ = (u'.val + 1) * S.N_send_opk := by ring
      _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu1
      _ ≤ S.N_id * S.N_send_opk + S.N_send_no_opk_tot := Nat.le_add_right _ _
  | sendNoOPK u' i' =>
    unfold initSessionSlotIdx Setup.N_send_tot Setup.N_send_no_opk_tot
    have hu1 : u'.val + 1 ≤ S.N_id := Nat.succ_le_of_lt u'.isLt
    have hlt : u'.val * S.N_send_no_opk + i'.val < S.N_id * S.N_send_no_opk :=
      calc u'.val * S.N_send_no_opk + i'.val
          < u'.val * S.N_send_no_opk + S.N_send_no_opk := Nat.add_lt_add_left i'.isLt _
        _ = (u'.val + 1) * S.N_send_no_opk := by ring
        _ ≤ S.N_id * S.N_send_no_opk := Nat.mul_le_mul_right S.N_send_no_opk hu1
    exact Nat.add_lt_add_left hlt S.N_send_opk_tot
  | recvOPK _ _ _ => cases hSend
  | recvNoOPK _ _ _ => cases hSend

theorem fgRunInitiatePure_false_N_send_tot_U_irrel (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : ℕ) (U1 U2 : Bytes)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) :
    fgRunInitiatePure P ddh false S.N_send_tot S maxLen U1 sid u bundle st =
      fgRunInitiatePure P ddh false S.N_send_tot S maxLen U2 sid u bundle st := by
  have hlt := initSessionSlotIdx_lt_of_isSendSessionId sid hSend
  have hne : (initSessionSlotIdx sid == S.N_send_tot) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
  unfold fgRunInitiatePure
  simp [hne]

theorem fgRunInitiatePure_clearFgTargetSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx kIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U : Bytes) (sid : SessionId S)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) :
    fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U sid u bundle (clearFgTargetSign kIdx st) =
      Prod.map id (clearFgTargetSign kIdx) <$>
        fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U sid u bundle st := by
  unfold fgRunInitiatePure clearFgTargetSign
  dsimp only
  by_cases hSid : (st.base.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hSid, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
  · simp only [hSid, Bool.false_eq_true, ↓reduceIte,
      find?_idx_clearPrincipalsTargetSign, koskBundleOkTake_clearPrincipalsTargetSign,
      clearPrincipalsTargetSign_take, resolveSigPk_clearPrincipalsTargetSign,
      isHonestUncorruptedPeer_clearPrincipalsTargetSign,
      checkBundleProvenanceTake_clearPrincipalsTargetSign,
      findHonestPrincipal_clearPrincipalsTargetSign]
    cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp
    | some p =>
      rcases p with ⟨idx, uEntry⟩
      simp only [Option.map_some]
      have hsec0 :
          (if idx == kIdx then (idx, { uEntry with secIKAsign := [] }) else (idx, uEntry)).2.secIKA0 =
            uEntry.secIKA0 := by
        cases idx == kIdx <;> rfl
      have hikA :
          (if idx == kIdx then (idx, { uEntry with secIKAsign := [] }) else (idx, uEntry)).2.ikAPk =
            uEntry.ikAPk := by
        cases idx == kIdx <;> rfl
      rw [hsec0, hikA]
      by_cases hKosk :
          (!koskBundleOkTake S P st.base.principals st.base.spkBundles st.base.opkEntries
            st.advKeyPows bundle) = true
      · simp only [hKosk, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc]
        congr 1; ext ekASkRaw
        congr 1; ext kemCoins
        by_cases hv :
            (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hv, ↓reduceIte, pure_bind]
          rfl
        · simp only [hv, Bool.false_eq_true, ↓reduceIte]
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩
            dsimp only
            simp only [bind_assoc]
            congr 1; ext ⟨drKeyReal, fgL'⟩
            congr 1; ext drKeyRand
            cases findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;> simp

theorem fgRunAcceptOPKPure_clearFgTargetSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (kIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    fgRunAcceptOPKPure P ddh S maxLen k j o hdr (clearFgTargetSign kIdx st) =
      Prod.map id (clearFgTargetSign kIdx) <$> fgRunAcceptOPKPure P ddh S maxLen k j o hdr st := by
  unfold fgRunAcceptOPKPure clearFgTargetSign
  dsimp only
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [hUsed, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte, koskSenderOkTake_clearPrincipalsTargetSign]
      by_cases hSender : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hSender, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
      · simp only [hSender, Bool.false_eq_true, ↓reduceIte, find?_idx_clearPrincipalsTargetSign]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp
        | some pk =>
          rcases pk with ⟨idx, kEntry⟩
          simp only [Option.map_some]
          have hsec0 :
              (if idx == kIdx then (idx, { kEntry with secIKAsign := [] }) else (idx, kEntry)).2.secIKA0 =
                kEntry.secIKA0 := by
            cases idx == kIdx <;> rfl
          have hikA :
              (if idx == kIdx then (idx, { kEntry with secIKAsign := [] }) else (idx, kEntry)).2.ikAPk =
                kEntry.ikAPk := by
            cases idx == kIdx <;> rfl
          rw [hsec0, hikA]
          cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp
          | some pb =>
            rcases pb with ⟨_, bEntry⟩
            dsimp only
            cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => simp
            | some po =>
              rcases po with ⟨_, oEntry⟩
              dsimp only
              by_cases hCons : oEntry.consumed = true
              · simp only [hCons, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
              · simp only [hCons, Bool.false_eq_true, ↓reduceIte]
                rcases checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId
                  hdr.spkId hdr.ekAPk with ⟨replayOk, usedTriples'⟩
                dsimp only
                by_cases hChk : (!(replayOk && P.isCanonical hdr.ekAPk &&
                     P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                     P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0 &&
                     P.x25519 oEntry.opkSk hdr.ekAPk != List.replicate 32 0)) = true
                · simp only [hChk, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
                · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none => simp
                  | some ss =>
                    dsimp only
                    simp only [clearPrincipalsTargetSign_take,
                      findHonestPrincipal_clearPrincipalsTargetSign,
                      Option.isSome_map, map_eq_bind_pure_comp, bind_assoc]
                    congr 1; ext ⟨drKey, fgL'⟩
                    congr 1; ext drKeyRand
                    cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;> simp

theorem fgRunAcceptNoOPKPure_clearFgTargetSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (kIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    fgRunAcceptNoOPKPure P ddh S maxLen k j l hdr (clearFgTargetSign kIdx st) =
      Prod.map id (clearFgTargetSign kIdx) <$> fgRunAcceptNoOPKPure P ddh S maxLen k j l hdr st := by
  unfold fgRunAcceptNoOPKPure clearFgTargetSign
  dsimp only
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [hUsed, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte, koskSenderOkTake_clearPrincipalsTargetSign]
      by_cases hSender : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hSender, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
      · simp only [hSender, Bool.false_eq_true, ↓reduceIte, find?_idx_clearPrincipalsTargetSign]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp
        | some pk =>
          rcases pk with ⟨idx, kEntry⟩
          simp only [Option.map_some]
          have hsec0 :
              (if idx == kIdx then (idx, { kEntry with secIKAsign := [] }) else (idx, kEntry)).2.secIKA0 =
                kEntry.secIKA0 := by
            cases idx == kIdx <;> rfl
          have hikA :
              (if idx == kIdx then (idx, { kEntry with secIKAsign := [] }) else (idx, kEntry)).2.ikAPk =
                kEntry.ikAPk := by
            cases idx == kIdx <;> rfl
          rw [hsec0, hikA]
          cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp
          | some pb =>
            rcases pb with ⟨_, bEntry⟩
            dsimp only
            rcases checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId
              hdr.spkId hdr.ekAPk with ⟨replayOk, usedTriples'⟩
            dsimp only
            by_cases hChk : (!(replayOk && P.isCanonical hdr.ekAPk &&
                 P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                 P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
            · simp only [hChk, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
            · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
              | none => simp
              | some ss =>
                dsimp only
                simp only [clearPrincipalsTargetSign_take,
                  findHonestPrincipal_clearPrincipalsTargetSign,
                  Option.isSome_map, map_eq_bind_pure_comp, bind_assoc]
                congr 1; ext ⟨drKey, fgL'⟩
                congr 1; ext drKeyRand
                cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;> simp

theorem fgKeyIndStepPure_false_N_send_tot_U_irrel (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U1 U2 V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    fgKeyIndStepPure P ddh false S.N_send_tot targetSpkIdx S maxLen U1 V q st =
      fgKeyIndStepPure P ddh false S.N_send_tot targetSpkIdx S maxLen U2 V q st := by
  cases q with
  | initPrin u => simp [fgKeyIndStepPure]
  | initiateOPK u i bundle =>
    unfold fgKeyIndStepPure
    dsimp only
    split_ifs
    · rfl
    · exact fgRunInitiatePure_false_N_send_tot_U_irrel P ddh S maxLen U1 U2
        (.sendOPK u i) trivial u bundle st
  | initiateNoOPK u i bundle =>
    unfold fgKeyIndStepPure
    dsimp only
    split_ifs
    · rfl
    · exact fgRunInitiatePure_false_N_send_tot_U_irrel P ddh S maxLen U1 U2
        (.sendNoOPK u i) trivial u bundle st
  | _ => rfl

/-- Commutation of `fgKeyIndStepPure` with `clearFgTargetSign kIdx` on every query that does not
    read the target principal's signing scalar (`q` not `.initPrin`, not target `.corruptIK`, and
    not target `.genSPK`). -/
theorem fgKeyIndStepPure_clearFgTargetSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetSpkIdx kIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyIndSimState S)
    (hNoInit : ∀ u, q ≠ .initPrin u)
    (hNoTargetCorr : ∀ u, q = .corruptIK u → (u.val == kIdx) = false)
    (hNoTargetSpk : ∀ u j, q = .genSPK u j → (u.val == kIdx) = false) :
    fgKeyIndStepPure P ddh false S.N_send_tot targetSpkIdx S maxLen U V q (clearFgTargetSign kIdx st) =
      Prod.map id (clearFgTargetSign kIdx) <$>
        fgKeyIndStepPure P ddh false S.N_send_tot targetSpkIdx S maxLen U V q st := by
  cases q with
  | initPrin u => exact False.elim (hNoInit u rfl)
  | corruptIK u =>
    have hne := hNoTargetCorr u rfl
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    rw [find?_idx_clearPrincipalsTargetSign]
    cases hfind : st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp
    | some p =>
      rcases p with ⟨idx, entry⟩
      have hidx_u : (idx == u.val) = true :=
        List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hfind
      have hidx_eq : idx = u.val := beq_iff_eq.mp hidx_u
      have hidx_k : (idx == kIdx) = false := by rwa [hidx_eq]
      simp only [Option.map_some, hidx_k, Bool.false_eq_true, ↓reduceIte, map_pure, Prod.map_apply,
        id_eq]
      congr 4
      unfold clearPrincipalsTargetSign
      simp only [List.map_map]
      refine List.map_congr_left (fun x _ => ?_)
      rcases x with ⟨idx', e'⟩
      dsimp only [Function.comp_def]
      by_cases h1 : (idx' == kIdx) = true <;> by_cases h2 : (idx' == u.val) = true <;> simp [h1, h2]
  | genSPK u j =>
    have hne := hNoTargetSpk u j rfl
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    by_cases hAny : (st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hAny, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte, find?_idx_clearPrincipalsTargetSign]
      cases hfind : st.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨idx, uEntry⟩
        have hidx_u : (idx == u.val) = true :=
          List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hfind
        have hidx_eq : idx = u.val := beq_iff_eq.mp hidx_u
        have hidx_k : (idx == kIdx) = false := by rwa [hidx_eq]
        simp only [Option.map_some, hidx_k, Bool.false_eq_true, ↓reduceIte]
        simp [map_eq_bind_pure_comp, bind_assoc]
  | genOPK u j o =>
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    by_cases hAny : (st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hAny, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp [hAny, map_eq_bind_pure_comp, bind_assoc]
  | initiateOPK u i bundle =>
    unfold fgKeyIndStepPure
    dsimp only
    by_cases hNone : bundle.opkB?.isNone = true
    · simp only [hNone, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp only [hNone, Bool.false_eq_true, ↓reduceIte]
      exact fgRunInitiatePure_clearFgTargetSign P ddh false S.N_send_tot kIdx S maxLen U
        (.sendOPK u i) u bundle st
  | initiateNoOPK u i bundle =>
    unfold fgKeyIndStepPure
    dsimp only
    by_cases hSome : bundle.opkB?.isSome = true
    · simp only [hSome, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp only [hSome, Bool.false_eq_true, ↓reduceIte]
      exact fgRunInitiatePure_clearFgTargetSign P ddh false S.N_send_tot kIdx S maxLen U
        (.sendNoOPK u i) u bundle st
  | acceptOPK k j o hdr =>
    exact fgRunAcceptOPKPure_clearFgTargetSign P ddh kIdx S maxLen k j o hdr st
  | acceptNoOPK k j l hdr =>
    exact fgRunAcceptNoOPKPure_clearFgTargetSign P ddh kIdx S maxLen k j l hdr st
  | testSession sid =>
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    have hTestEq :
        isKeyIndSessionTestable
          { st.base with principals := clearPrincipalsTargetSign kIdx st.base.principals } sid =
        isKeyIndSessionTestable st.base sid := rfl
    rw [hTestEq]
    by_cases hFresh : (!isKeyIndSessionTestable st.base sid) = true
    · simp only [hFresh, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte]
      cases st.base.sessions.find? (fun e => e.sid == sid) with
      | some e => simp
      | none =>
        dsimp only
        cases st.base.respSessions.find? (fun r => r.sid == sid) <;> simp
  | revealSessionKey sid =>
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    cases st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      by_cases hTest : e.tested = true
      · simp only [hTest, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
      · simp [hTest]
    | none =>
      dsimp only
      cases st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => simp
      | some r =>
        dsimp only
        by_cases hTest : r.tested = true
        · simp only [hTest, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
        · simp [hTest]
  | roQuery secrets =>
    unfold fgKeyIndStepPure fgRoQueryPure clearFgTargetSign
    dsimp only
    cases parseRoSecrets secrets with
    | none =>
      cases st.rawRoCache.find? (fun (s, _) => s == secrets) <;>
        simp [map_eq_bind_pure_comp]
    | some tup =>
      rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
      simp [map_eq_bind_pure_comp]
  | revealDhSecrets =>
    simp [fgKeyIndStepPure, clearFgTargetSign]
  | revealSpkSk u j =>
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    cases st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;> simp
  | registerKey sk =>
    unfold fgKeyIndStepPure clearFgTargetSign
    dsimp only
    by_cases hLen : (sk.length != 32) = true
    · simp only [hLen, ↓reduceIte, map_pure, Prod.map_apply, id_eq]
    · simp [hLen]

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  runKeyInd1KeySim
  keyInd1KeyAllTestedClean
  keyInd1KeyExpG0
  keyInd1KeyExpG0_1
  keyInd1KeyExpG1
  keyInd1KeyExpG2
  keyInd1KeyExpG2_1
  keyInd1KeyAdvG0
  keyInd1KeyAdvG0_1
  keyInd1KeyAdvG1
  keyInd1KeyAdvG2
  keyInd1KeyAdvG2_1
  keyInd1KeyAdvG0_eq
  keyInd1KeyAdvG1_eq_G2
  ecCollProbKeyInd1Key
  kemCollProbKeyInd1Key
  badSigProbKeyInd1Key
  keyInd1Key_hop_G0_G0_1_le_prob
  keyInd1Key_hop_G0_1_G1_le_prob
  keyInd1Key_hop_G2_G2_1_le_prob
  kemCollProbKeyInd1Key_le_bound
  keyInd1Key_hop_G2_G2_1_le
  ecCollProbKeyInd1Key_le_bound
  keyInd1Key_hop_G0_G0_1_le
)

end SignalPqxdh
