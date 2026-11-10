/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrHyp
public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# Decision-C Refinement Simulator and SPQR Send-Totality Hypotheses

**Checked by Lean.**

Defines the decision-C simulator reduction `Refine.libsignalToModularSchemeSim` from the libsignal
session game to the ACD19 Fig. 8 instance, the graded SPQR send-totality hypotheses
`Corr.SpqrSendCorrect` and `Corr.SpqrSendCorrectQ`, and the refinement bound predicate
`Refine.LibSimC` (`DEV-LS36`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA

namespace Refine

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-- Decision-C reduction (`LibsignalSimC.runLibsignalToModularSchemeSim`) transforming a libsignal
session adversary into an ACD19 Fig. 8 adversary while tracking corrupted parties' chain states. -/
def libsignalToModularSchemeSim (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (A : LibAdv PQ PQC ℓ) : Fig8Adv Pt ℓ :=
  LibsignalSimC.runLibsignalToModularSchemeSim P Dh encPt encT decT idOf lam qep A

end Refine

end CryptoGames.LibsignalSM

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA

namespace Corr

/-- Unbounded SPQR send-totality and panic-freedom invariant closed under `init`, `send`, and `recv`. -/
def SpqrSendCorrect {PQ PQC : Type} (S : Spqr PQ PQC) : Prop :=
  ∃ Inv : PQ → Prop, SpqrInvClosed S Inv ∧ SpqrSendTotalOn S Inv ∧
    ∀ st r, Inv st → S.sendPanics st r = false

/-- SPQR state invariant graded by the number of successful sends. -/
structure SpqrInvClosedQ {PQ PQC : Type} (S : Spqr PQ PQC) (Inv : ℕ → PQ → Prop) : Prop where
  init : ∀ dir k, Inv 0 (S.init dir k)
  send : ∀ n st r st' salt msg, Inv n st → S.send st r = some (st', salt, msg) → Inv (n + 1) st'
  recv : ∀ n st msg st' salt, Inv n st → S.recv st msg = .ok (st', salt) → Inv n st'

/-- Graded SPQR send-totality and panic-freedom up to send budget `q`, accommodating SPQR V1's
`u32` chain-counter limit (`DEV-SPQR7`). -/
def SpqrSendCorrectQ {PQ PQC : Type} (S : Spqr PQ PQC) (q : ℕ) : Prop :=
  ∃ Inv : ℕ → PQ → Prop, SpqrInvClosedQ S Inv ∧
    (∀ n st r, n < q → Inv n st → (S.send st r).isSome) ∧
    ∀ n st r, n < q → Inv n st → S.sendPanics st r = false

end Corr

namespace Refine

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-- Decision-C libsignal-to-Fig. 8 refinement bound predicate including `2 * hiddenSaltTerm` (`DEV-LS36`). -/
def LibSimC (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (εcoll : ℝ≥0∞) : Prop :=
  ∀ A : LibAdv PQ PQC ℓ, SM.MakesAtMostQueries A q →
    hybridAdvantageR (libsignalSessionScheme P ℓ encPt lam) (2 + 1) qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) A ≤
        hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1)
          Config.h1 (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)
      + 2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A))
      + 2 * LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q
      + 2 * LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep
      + 2 * LibsignalSim.epoch0Term P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q A
      + 2 * LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A + 2 * εcoll

end Refine

end CryptoGames.LibsignalSM
