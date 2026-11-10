/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Defs
public import Computational.Proofs.E2E.SignedPrims
public import Computational.Specifications.Session.StatementIdsModel
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm8

/-!
# Prefix integration helper for double finite sums

Integrates pointwise upper bounds by double finite sums of event probabilities over a prefix
distribution `oa`.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
  CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
  CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim

theorem evalDist_bind_apply_le_sum_sum {α ι κ : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (s : Finset ι) (u : ι → Finset κ) (g : ι → κ → α → ProbComp Bool)
    (H : ∀ a, 𝒟[f a] {true} ≤ ∑ i ∈ s, ∑ k ∈ u i, 𝒟[g i k a] {true}) :
    𝒟[oa >>= f] {true} ≤ ∑ i ∈ s, ∑ k ∈ u i, 𝒟[oa >>= g i k] {true} := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral]
  simp_rw [evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {true} ∂𝒟[oa]
      ≤ ∫⁻ a, ∑ i ∈ s, ∑ k ∈ u i, 𝒟[g i k a] {true} ∂𝒟[oa] := lintegral_mono H
    _ = _ := by
      rw [lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact lintegral_finsetSum _ fun _ _ => Measurable.of_discrete

section Fig8

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

end Fig8

end CryptoVerification.E2E.Signed
