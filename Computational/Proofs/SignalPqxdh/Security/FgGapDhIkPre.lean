/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import Computational.Proofs.SignalPqxdh.Security.FgGapDhD
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIk -- shake: keep

/-!
# Case B (`DH2`) pre-sampled `KeyInd` implementation

Pre-sampled variant `pqxdhKeyIndFgPreImplIk sIdx kIdx optU optV` of `pqxdhKeyIndFgImpl`, which
uses `uSk` as the ephemeral secret of initiator slot `sIdx` and `vSk` as the identity DH secret
of principal `kIdx`, together with the pre-sampling equivalence
`evalDist_runKeyIndFgSim_eq_preSample_dh2`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Ik

open Proofs.SignalPqxdh.Security.FgGapDh

/-- Case B pre-sampled implementation: `uSk` as the ephemeral secret of initiator slot
    `targetIdx`, `vSk` as the identity DH secret of principal `targetPrinIdx`. -/
noncomputable def pqxdhKeyIndFgPreImplIk (targetIdx targetPrinIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u =>
      pqxdhKeyIndFgPreImpl true targetPrinIdx (noSpkIdx S) optVsk none S P (.initPrin u)
  | q => pqxdhKeyIndFgPreImpl false targetIdx (noSpkIdx S) optUsk none S P q

theorem fgPreInitPrin_false_eq_true_none (targetIdx targetPrinIdx : ℕ) (optUsk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    fgPreInitPrin false targetIdx optUsk S P u = fgPreInitPrin true targetPrinIdx none S P u := by
  cases optUsk <;> simp [fgPreInitPrin]

theorem pqxdhKeyIndFgPreImplIk_none_eq {S : Setup} (targetIdx targetPrinIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) :
    pqxdhKeyIndFgPreImplIk targetIdx targetPrinIdx optUsk none S P =
      pqxdhKeyIndFgPreImpl false targetIdx (noSpkIdx S) optUsk none S P := by
  funext q
  cases q
  case initPrin u =>
    simp only [pqxdhKeyIndFgPreImplIk, pqxdhKeyIndFgPreImpl,
      fgPreInitPrin_false_eq_true_none targetIdx targetPrinIdx optUsk S P u]
  all_goals rfl

theorem pqxdhKeyIndFgPreImplIk_preserves {S : Setup} (targetIdx targetPrinIdx : ℕ)
    (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImplIk targetIdx targetPrinIdx optUsk optVsk S P q).run hst)) :
    (∀ uIdx, hasFiredPrin S uIdx hst → hasFiredPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  cases q
  case initPrin u =>
    have h := pqxdhKeyIndFgPreImpl_preserves_hasFired true targetPrinIdx (noSpkIdx S) optVsk none P
      (.initPrin u) hst x hx
    exact ⟨h.2.1, h.2.2⟩
  all_goals
    have h := pqxdhKeyIndFgPreImpl_preserves_hasFired false targetIdx (noSpkIdx S) optUsk none P
      _ hst x hx
    exact ⟨h.2.1, h.2.2⟩

theorem evalDist_preSample_V_ik {S : Setup} {α : Type}
    (targetIdx targetPrinIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImplIk targetIdx targetPrinIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImplIk targetIdx targetPrinIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredPrin S targetPrinIdx)
    (pqxdhKeyIndFgPreImplIk targetIdx targetPrinIdx optUsk none S P)
    (fun vSk => pqxdhKeyIndFgPreImplIk targetIdx targetPrinIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImplIk_preserves targetIdx targetPrinIdx optUsk none P q s x hx).1
        targetPrinIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | initPrin u =>
      unfold pqxdhKeyIndFgPreImplIk pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase
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
      · unfold pqxdhKeyIndFgPreImplIk pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
              support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨secIKAsign, _, hEq⟩
            have hB := (Prod.mk.inj hEq).2
            unfold hasFiredPrin; rw [hB]; simp [hSlot]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold pqxdhKeyIndFgPreImplIk pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_runKeyIndFgSim_eq_preSample_dh2 {S : Setup}
    (sIdx kIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImplIk sIdx kIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim
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
        pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] := by
    intro uSk
    rw [← pqxdhKeyIndFgPreImplIk_none_eq sIdx kIdx (some uSk) P]
    exact evalDist_preSample_V_ik sIdx kIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_pqxdhKeyIndFgPreImpl sIdx (noSpkIdx S) none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl_none_none_eq]
  simp only [pure_bind]

end Proofs.SignalPqxdh.Security.FgGapDh.Ik
