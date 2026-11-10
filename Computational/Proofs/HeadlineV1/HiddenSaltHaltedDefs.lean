/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound

/-!
# Online-Halted Hidden-Salt Definitions

**Checked by Lean.** Defines `kemFailBadLog` and re-exports the online-halted hidden-salt
simulators, games, and advantage terms from `HiddenSaltBound`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.HeadlineV1.HiddenSaltHaltedDefs

noncomputable section

open scoped ENNReal
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM.Construction.DeliverForge (AdversaryDF)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Params PublicKey IdentityKey GhostState)
open CryptoGames.LibsignalSM (LibAdv)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)

/-- `MlKem.KemFailBad` predicate lifted to a send-coin log `List (BitVec 512)`. -/
def kemFailBadLog (K : MlKem) (w : List (BitVec 512)) : Bool :=
  K.KemFailBad (w.map coinBytes)

abbrev simDeliverForgeTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ (BitVec 512) ℓ) :
    AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt) :=
  CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForgeTrackHalted
    P K ℓ Dh encPt encT decT idOf lam qep A

abbrev hiddenSaltGameTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) :
    ProbComp Bool :=
  CryptoGames.LibsignalSM.Proofs.Refinement.hiddenSaltGameTrackHalted
    P K ℓ Dh encPt encT decT idOf lam qep A

abbrev hiddenSaltTermTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) :
    ℝ≥0∞ :=
  CryptoGames.LibsignalSM.Proofs.Refinement.hiddenSaltTermTrackHalted
    P K ℓ Dh encPt encT decT idOf lam qep A

abbrev simDeliverForgeHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool)
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt) :=
  CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForgeHalted
    badLog P ℓ Dh encPt encT decT idOf lam qep A

abbrev hiddenSaltGameHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool)
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    ProbComp Bool :=
  CryptoGames.LibsignalSM.Proofs.Refinement.hiddenSaltGameHalted
    badLog P ℓ Dh encPt encT decT idOf lam qep A

abbrev hiddenSaltTermHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool)
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ℝ≥0∞ :=
  CryptoGames.LibsignalSM.Proofs.Refinement.hiddenSaltTermHalted
    badLog P ℓ Dh encPt encT decT idOf lam qep A

end

end Computational.Proofs.HeadlineV1.HiddenSaltHaltedDefs
