/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.SendShortC -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalSan
import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedCoupling

/-!
# Evaluation and Game Coupling for `simFig8RedProgHalted`

Combines the sanitized `.eval` and query/guard invariants for `simFig8RedProgHalted` with its
game-level coupling to `libsignalToModularSchemeSimHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval

noncomputable section

open OracleComp OracleSpec
open _root_.CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState Params)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFig8)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open CryptoVerification.E2E (idsOf paramsV1)
open CryptoGames.LibsignalSM.Proofs.SessionShort (SendMsgsOk GuardedSMShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (libsignalToModularSchemeSimHalted simCNoneWinEventHalted
   simFig8ClampSanHalted simFig8RedProgHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedCoupling
  (simFig8ClampSanHalted_sm_game_eq simFig8ClampSanHalted_simCNoneWinEvent_eq)

private theorem paramsV1_idsOf_eq (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (R : Party) :
    (if R == Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB) =
      idsOf idA idB R := by
  cases R <;> rfl

theorem libsignalToModularSchemeSimHalted_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    libsignalToModularSchemeSimHalted P K ℓ Dh encPt encT decT idOf lam qep A =
      CryptoGames.LibsignalSM.Proofs.Refinement.runLibsignalToModularSchemeSimTrackHalted
        P K (ℓ := ℓ) Dh encPt encT decT idOf lam qep A := rfl

section Theorems

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem simFig8RedProgHalted_eval_san (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) () =
      simFig8ClampSanHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
        lam qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A :=
  SimFig8HaltedEvalSan.simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_queries (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) q :=
  SimFig8HaltedEvalSan.simFig8RedProgHalted_queries hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_equalPub (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) :=
  SimFig8HaltedEvalSan.simFig8RedProgHalted_equalPub hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_sendShort (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) :=
  SimFig8HaltedEvalSan.simFig8RedProgHalted_sendShort hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_sendAtomicShort (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) :=
  SimFig8HaltedEvalSan.simFig8RedProgHalted_sendAtomicShort
    hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_guardedSMShort (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    GuardedSMShort
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) :=
  SimFig8HaltedEvalSan.simFig8RedProgHalted_guardedSMShort
    hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_sm_game_eq (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        3 (qep + 1) cfg
        (libsignalToModularSchemeSimHalted (paramsV1 C K idA idB) K ℓ
          Dh encPt encT decT (idsOf idA idB) lam qep A) =
      CryptoGames.SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        3 (qep + 1) cfg
        ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
          (fun _ => A) ()) := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact (simFig8ClampSanHalted_sm_game_eq (paramsV1 C K idA idB) K Dh encPt encT decT
    (idsOf idA idB) (paramsV1_idsOf_eq C K idA idB) lam qep
    (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) cfg hq
    (by omega) (by omega) le_rfl le_rfl le_rfl).symm

theorem simFig8RedProgHalted_simCNoneWinEvent_eq (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    simCNoneWinEventHalted (paramsV1 C K idA idB) K ℓ
        Dh encPt encT decT (idsOf idA idB) lam qep A =
      (do
        let b ← $ᵗ Bool
        let (_, s) ← CryptoGames.SM.run
          (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
          3 (qep + 1) CryptoGames.SM.Config.h1 b
          ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
            (fun _ => A) ())
        return s.win) := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact simFig8ClampSanHalted_simCNoneWinEvent_eq (paramsV1 C K idA idB) K Dh encPt encT decT
    (idsOf idA idB) (paramsV1_idsOf_eq C K idA idB) lam qep
    (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) hq
    (by omega) (by omega) le_rfl le_rfl le_rfl

end Theorems

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEval
