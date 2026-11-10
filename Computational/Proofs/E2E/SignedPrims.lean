/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRNG.PRNGProofDefs
import ProofLib.Lemmas
import VCVio.OracleComp.EvalDist.Measure

/-!
# Averaged adversaries for CKA and PRF-PRNG games

Defines the prefix-averaged adversary `advAvg oa D` and proves that its CKA and PRF-PRNG game
branches equal the `oa`-mixtures of the per-prefix branches.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames

theorem simulateQ_liftTarget_liftM_run {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : ProbComp α) (s : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl)
      (liftM oa : OracleComp (unifSpec + spec) α)).run s = oa >>= fun a => pure (a, s) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= fun u =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl)
          (liftM (k u) : OracleComp (unifSpec + spec) α)).run s) = _
    simp only [ih, bind_assoc]

/-- Averaged adversary that samples `o ← oa` with its own coins and runs `D o`. -/
def advAvg {ι : Type} {spec : OracleSpec ι} {α β : Type} (oa : ProbComp α)
    (D : α → OracleComp (unifSpec + spec) β) : OracleComp (unifSpec + spec) β :=
  bind (m := OracleComp (unifSpec + spec)) (liftM oa : OracleComp (unifSpec + spec) α) D

theorem simulateQ_advAvg_run' {ι : Type} {spec : OracleSpec ι} {σ α β : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : ProbComp α)
    (D : α → OracleComp (unifSpec + spec) β) (s : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl)
      (advAvg oa D)).run' s =
      oa >>= fun o =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl)
          (D o)).run' s := by
  unfold advAvg
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, simulateQ_liftTarget_liftM_run,
    bind_assoc, pure_bind, map_bind]

section CKA

variable {Key State Coins Msg CKey : Type} [SampleableType Key] [SampleableType Coins]
  [SampleableType CKey]

theorem ckaBranch_avg {α : Type} (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ)
    (b : Bool) (oa : ProbComp α) (D : α → CKA.Adversary State Coins Msg CKey) :
    𝒟[CKA.branch cka Δ tStar b (advAvg oa D)] =
      𝒟[oa >>= fun o => CKA.branch cka Δ tStar b (D o)] := by
  unfold CKA.branch
  simp only [simulateQ_advAvg_run']
  exact OracleComp.evalDist_bind_bind_swap _ _ _

end CKA

section PRNG

variable {Key State Input Output : Type} [DecidableEq Input] [SampleableType Key]
  [SampleableType Input] [SampleableType Output]

theorem prngBranch_avg {α : Type} (P : PRFPRNG Key State Input Output) (b : Bool)
    (oa : ProbComp α) (D : α → PRFPRNG.Adversary State Input Output) :
    𝒟[PRFPRNG.branch P b (advAvg oa D)] = 𝒟[oa >>= fun o => PRFPRNG.branch P b (D o)] := by
  unfold PRFPRNG.branch
  simp only [simulateQ_advAvg_run']
  exact OracleComp.evalDist_bind_bind_swap _ _ _

end PRNG

section FS

variable {Key SS RS AD M E : Type} [SampleableType Key] [DecidableEq AD] [DecidableEq M]
  [DecidableEq E]

end FS

end CryptoVerification.E2E.Signed
