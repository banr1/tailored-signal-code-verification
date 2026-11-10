/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.SpuriousBounds
public import Computational.Proofs.E2E.SignedAdv
public import Computational.Specifications.Session.StatementIdsModel
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.SignalWireRoundTrip

/-!
# Refinement slack constant and Boolean total-variation helper

Defines the prefix-independent session-refinement slack `refineConst` and relates per-outcome
Boolean probabilities to `Measure.boolDist`.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
open CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
open CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim

theorem apply_le_add_boolDist (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : Bool) : μ {v} ≤ ν {v} + μ.boolDist ν := by
  cases v
  · have h := Measure.apply_true_le_add_boolDist ν μ
    rw [Measure.boolDist_comm] at h
    have : μ {false} + μ {true} ≤ (ν {false} + μ.boolDist ν) + μ {true} :=
      calc μ {false} + μ {true} = 1 := by
            rw [add_comm]; exact Measure.apply_true_add_apply_false_eq_one μ
        _ = ν {true} + ν {false} := (Measure.apply_true_add_apply_false_eq_one ν).symm
        _ ≤ (μ {true} + μ.boolDist ν) + ν {false} := by gcongr
        _ = (ν {false} + μ.boolDist ν) + μ {true} := by ring
    exact (ENNReal.add_le_add_iff_right (measure_ne_top μ _)).1 this
  · exact Measure.apply_true_le_add_boolDist μ ν

section Refine

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Prefix-independent spurious-step and collision slack of the session refinement. -/
noncomputable def refineConst (Z : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (q qep : ℕ) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  forgedEpochStartSpuriousStepTerm Z.F encPt Dh q + spuriousStepTerm Z.F encPt Dh q qep +
    (qep + 2) * (q + qep + 2) * δ

end Refine

end CryptoVerification.E2E.Signed
