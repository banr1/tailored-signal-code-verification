/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimShallow
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# The refinement bound `LibSim`

**Checked by Lean.**

Defines `Refine.LibSim`, the advantage bound of the session-model refinement for the shallow
reduction `Refine.sim`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA

namespace Refine

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-- Advantage bound for the reduction `sim`: bounds `A`'s advantage in `configR1OnCurve` (DEV-LS5)
by the H1 advantage of `sim A` against `lFig8`, the Fig. 8 authenticity sum and forged epoch-start
term (DEV-LS12), the evicted-epoch term `spuriousStepTerm` (DEV-LS11), the signed-pre-key chain
term `epoch0Term` (DEV-LS26), and the ratchet-key collision term `εcoll` (DEV-LS18). -/
def LibSim (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (εcoll : ℝ≥0∞) : Prop :=
  ∀ A : LibAdv PQ PQC ℓ, SM.MakesAtMostQueries A q →
    hybridAdvantageR (libsignalSessionScheme P ℓ encPt lam) (2 + 1) qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) A ≤
        hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1)
          Config.h1 (sim P ℓ Dh encT decT qep A)
      + 2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (sim P ℓ Dh encT decT qep A))
      + 2 * LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q
      + 2 * LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep
      + 2 * LibsignalSim.epoch0Term P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q A + 2 * εcoll

end Refine

end CryptoGames.LibsignalSM
