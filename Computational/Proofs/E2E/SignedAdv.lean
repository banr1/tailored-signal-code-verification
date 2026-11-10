/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import VCVio.CryptoFoundations.PRG
import ProofLib.Lemmas

/-!
# Prefix-Averaged PRG and PRF Distinguishers

Defines the prefix-averaged distinguishers `prgAvg` and `prfAvg` (`o ← oa; D o`) and proves that
their PRG real/ideal and PRF branch distributions equal the `oa`-mixtures of the `D o` worlds.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

/-! ## PRG mixtures -/

section PRG

variable {S R : Type}

/-- Prefix-averaged PRG distinguisher sampling `o` from `oa` before running `D o`. -/
def prgAvg {α : Type} (oa : ProbComp α) (D : α → PRGScheme.PRGAdversary R) :
    PRGScheme.PRGAdversary R := fun r => oa >>= fun o => D o r

theorem prgReal_avg {α : Type} [SampleableType S] (prg : PRGScheme S R) (oa : ProbComp α)
    (D : α → PRGScheme.PRGAdversary R) :
    𝒟[prg.prgRealExperiment (prgAvg oa D)] =
      𝒟[oa >>= fun o => prg.prgRealExperiment (D o)] := by
  unfold PRGScheme.prgRealExperiment prgAvg
  exact evalDist_bind_bind_swap_of_uniform _ _ _

theorem prgIdeal_avg {α : Type} [SampleableType R] (oa : ProbComp α) (D : α →
PRGScheme.PRGAdversary R) :
    𝒟[PRGScheme.prgIdealExperiment (prgAvg oa D)] =
      𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D o)] := by
  unfold PRGScheme.prgIdealExperiment prgAvg
  exact evalDist_bind_bind_swap_of_uniform _ _ _

end PRG

/-! ## PRF mixtures -/

section PRF

open CryptoGames

variable {Key Input Tag : Type} [DecidableEq Input] [SampleableType Tag]

/-- Prefix-averaged PRF distinguisher sampling `o` from `oa` before running `D o`. -/
def prfAvg {α : Type} (oa : ProbComp α) (D : α → MACScheme.PRFAdversary Input Tag) :
    MACScheme.PRFAdversary Input Tag :=
  bind (m := OracleComp (unifSpec + MACScheme.prfSpec Input Tag))
    (liftM oa : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α) D

theorem simulateQ_prfImpl_liftM_run {α : Type} (mac : MACScheme Key Input Tag)
    (oa : ProbComp α) (st : MACScheme.PRFState Key Input Tag) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (MACScheme.PRFState Key Input Tag) ProbComp) + MACScheme.prfEval mac)
      (liftM oa : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α)).run st =
      oa >>= fun a => pure (a, st) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= fun u =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (MACScheme.PRFState Key Input Tag) ProbComp) + MACScheme.prfEval mac)
          (liftM (k u) : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α)).run st) = _
    simp only [ih, bind_assoc]

/-- World `b` of `prfAvg oa D` is the `oa`-mixture of the `D o` worlds. -/
theorem prfBranch_avg {α : Type} [SampleableType Key] (mac : MACScheme Key Input Tag) (b : Bool)
    (oa : ProbComp α) (D : α → MACScheme.PRFAdversary Input Tag) :
    𝒟[mac.branch b (prfAvg oa D)] = 𝒟[oa >>= fun o => mac.branch b (D o)] := by
  unfold MACScheme.branch prfAvg
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, simulateQ_prfImpl_liftM_run,
    bind_assoc, pure_bind, map_bind]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

end PRF

end CryptoVerification.E2E.Signed
