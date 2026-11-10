/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFs
public import Computational.Proofs.SessionCostedFig8
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsBase
public import Computational.Proofs.E2E.SpkCostedAndHeadlineSlice
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
public import Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg
public import Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg
public import Computational.Proofs.ReductionDsl.SM.DeliverForgeShifted
import Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.ReductionDsl.SpkHop2Red
public import Computational.Proofs.ReductionDsl.SpkLeakRedU
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Queries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedCoin
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.SignedThm1
import Computational.Proofs.E2E.SignedThm8
import Computational.Proofs.E2E.SpkCostedEval
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRed
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import VCVio.EvalDist.Monad.Basic

/-!
# Per-Session Costed `DeliverForge` Reductions and `SessionCostedReductions` Instance

Defines `v1SessionReds`, proves `v1SessionReds_bounded`, and establishes evaluation agreement
with the mixture bounds of `StatementComposed`.
-/

@[expose] public section

namespace CryptoVerification.E2E

set_option exponentiation.threshold 1024

open ReductionDsl OracleSpec OracleComp ENNReal MeasureTheory
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.GameHop.StateSim
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.ThmB
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-! ## `SessionCostedReductions` instance and bounds -/

abbrev spkCostedRedsInst {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst
    ℓ C K idA idB Dh encPt encT decT lam q qep

theorem hop2PrfRedK_queryBudget_le_old (q : ℕ) :
    q ≤ 2 * q :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.hop2PrfRedK_queryBudget_le_old q

theorem spkCostedBounds_imp_old {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q qep : ℕ) (R : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam)
    (h : spkCostedBounds q qep R) :
    GRedBounded R.spkLeakRed (fun _ => 1) (fun _ => 0)
      q (q + 1) (ratchetCostBudget q qep) ∧
    GRedBounded R.spkLeakRedU (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (ratchetCostBudget q qep) ∧
    (∀ k : ℕ, k < spkSwapHybridCount →
      GRedBounded (R.hop2PrgRedK k) Empty.elim (fun _ => 0)
        q 0 (ratchetCostBudget q qep)) ∧
    (∀ k : ℕ, k < spkSwapHybridCount →
      GRedBounded (R.hop2PrfRedK k) (fun _ => 1) (fun _ => 0)
        q (2 * q) (ratchetCostBudget q qep)) :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedBounds_imp_old q qep R h

theorem spkCostedRedsInst_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (hqep : qep ≤ q + 10) :
    spkCostedBounds q qep
      (spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep) :=
  Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst_bounds
    ℓ C K idA idB Dh encPt encT decT lam q qep hqep

/-- Canonical `SessionCostedReductions` instance combining SPK, Fig. 8, FS-AEAD, outer session, and atomic `DeliverForge` reductions. -/
noncomputable def v1SessionReds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam where
  spk :=
    Computational.Proofs.E2E.SpkCostedAndHeadlineSlice.spkCostedRedsInst
      ℓ C K idA idB Dh encPt encT decT lam q qep
  fig8 :=
    fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q
  fs :=
    fsCostedRedsInst C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2))
  simFig8 :=
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ C K idA idB Dh encPt encT decT lam qep q
  simDeliverForge :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg
      ℓ C K idA idB Dh encPt encT decT lam qep q
  epoch0Red :=
    Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red
      C K Dh encPt encT decT idA idB lam ℓ q qep
  uniformStartRed :=
    Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed
      C K Dh encPt encT decT idA idB lam ℓ q qep
  challSimDF :=
    challSimDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
  B_cka := fun tL t =>
    redCKAAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
  B_prng := fun tL t =>
    redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
  B_fs := fun j tL t =>
    redFSAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q j tL t

/-- `v1SessionReds` satisfies `sessionCostedReductionsBounded` under `qep ≤ q + 10`. -/
theorem v1SessionReds_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ q + 10) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  have hdf := Computational.Proofs.SessionCostedFig8.sessionCostedDFBaseBounds
    Dh encPt C ℓ encT (idsOf idA idB) lam qep q
  refine ⟨spkCostedRedsInst_bounds ℓ C K idA idB Dh encPt encT decT lam q qep hqep,
    fig8RedsInst_bounds Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q,
    fsCostedRedsInst_bounds C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) (qep + 1),
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_gRedBounded
      ℓ C K idA idB Dh encPt encT decT lam qep q,
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_gRedBounded
      ℓ C K idA idB Dh encPt encT decT lam qep q hqep,
    Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep,
    Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed_gRedBounded_succ
      C K Dh encPt encT decT idA idB lam ℓ q qep hqep,
    hdf.1, hdf.2.1, hdf.2.2.1, hdf.2.2.2, ?_, ?_⟩
  · intro t _ tL _ A hA
    dsimp only [v1SessionReds, redPRNGAuthDFAtomicProg]
    exact
      Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam ((q + 1) * (maxForwardJumps + 1))
        (min (2 + 2 * q) (q + 3)) _ A
        (Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNGPotOK.redPRNGAuthDFProg_makesAtMostQueries
          (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 (qep + 1) maxForwardJumps tL t q A
          (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr (by rintro (_ | _) <;> rfl) hA))
  · intro t _ tL _ j _ A hA
    dsimp only [v1SessionReds, redFSAuthDFAtomicProg]
    exact
      Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam ((q + 1) * (maxForwardJumps + 1))
        (min (2 * q) (q + 2)) _ A
        (Computational.Proofs.ReductionDsl.SM.DeliverForgePotOK.redFSAuthDFProg_makesAtMostQueries
          (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 (qep + 1) maxForwardJumps j tL t q A
          (CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr (by rintro (_ | _) <;> rfl) hA))

/-! ## Evaluation agreement for mixture bounds -/

section EvalBridges

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open CryptoGames.LibsignalSM.Proofs.Refinement (simCNoneWinEvent)

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

@[simp] theorem v1SessionReds_spk (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).spk =
      spkCostedRedsInst ℓ C K idA idB Dh encPt encT decT lam q qep := rfl

@[simp] theorem v1SessionReds_fig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 =
      fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q := rfl

@[simp] theorem v1SessionReds_fs (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      fsCostedRedsInst C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) := rfl

@[simp] theorem v1SessionReds_simFig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 =
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ C K idA idB Dh encPt encT decT lam qep q := rfl

@[simp] theorem v1SessionReds_simDeliverForge (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge =
      Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg
        ℓ C K idA idB Dh encPt encT decT lam qep q := rfl

@[simp] theorem v1SessionReds_epoch0Red (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
      Computational.Proofs.Game.PromotedCostedReds.Epoch0DistinguisherProg.epoch0Red
        C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem v1SessionReds_uniformStartRed (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
      Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg.uniformStartRed
        C K Dh encPt encT decT idA idB lam ℓ q qep := rfl

@[simp] theorem v1SessionReds_challSimDF (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).challSimDF =
      challSimDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q := rfl

@[simp] theorem v1SessionReds_B_cka (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_cka tL t =
      redCKAAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t := rfl

@[simp] theorem v1SessionReds_B_prng (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_prng tL t =
      redPRNGAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t := rfl

@[simp] theorem v1SessionReds_B_fs (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).B_fs j tL t =
      redFSAuthDFAtomicProg Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q j tL t := rfl

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeFSCompBoundWith_inst_eq (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    CryptoVerification.E2E.fsAeadSlotSumBound C qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A =
      Proofs.Refinement.deliverForgeFSCompBound C protoSignalCodec ℓ encT idOf qR A :=
  CryptoVerification.LibsignalSession.deliverForgeFSCompBoundWith_inst_eq
    C ℓ encT idOf qR hℓ hinj A hA hshort

omit [Zero Pt] [SampleableType Pt] in
theorem fsPrgMixWith_inst_eq {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR m : ℕ) (hℓ : ℓ < 10 ^ 6) (hm : m ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    fsChainPrgMixtureTerm C oa qR (fun o => fsCostedRedsInst C codec ℓ encT (idOf o) qR) A m =
      FSMix.fsPrgMix C protoSignalCodec ℓ encT oa idOf 25000 A m :=
  CryptoVerification.LibsignalSession.fsPrgMixWith_inst_eq
    C codec ℓ encT oa idOf qR m hℓ hm hinj A hA hshort

omit [Zero Pt] [SampleableType Pt] in
theorem fsSWMixWith_inst_eq {α : Type} (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR m : ℕ) (hℓ : ℓ < 10 ^ 6) (hm : m ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    fsSaltWireMixtureTerm C protoSignalCodec ℓ oa qR
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A m =
      FSMix.fsSWMix C protoSignalCodec ℓ encT oa idOf 25000 qR A m :=
  CryptoVerification.LibsignalSession.fsSWMixWith_inst_eq
    C ℓ encT oa idOf qR m hℓ hm hinj A hA hshort

omit [Zero Pt] [SampleableType Pt] in
theorem fsShortBoundMixWith_inst_eq {α : Type} (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR qd : ℕ) (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    fsAeadMixtureBound C protoSignalCodec ℓ oa (q := qR) (qd := qd)
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A =
      FSMix.fsShortBoundMix C protoSignalCodec ℓ encT oa idOf 25000 qR qd A :=
  CryptoVerification.LibsignalSession.fsShortBoundMixWith_inst_eq
    C ℓ encT oa idOf qR qd hℓ hinj A hA hshort

theorem prngAdvantage_advAvg_congr {KR Sig I K α : Type}
    [SampleableType KR] [SampleableType I] [SampleableType K] [DecidableEq I]
    (prng : PRFPRNG KR Sig I K) (oa : ProbComp α)
    (D₁ D₂ : α → PRFPRNG.Adversary Sig I K)
    (hBr : ∀ o b, PRFPRNG.branch prng b (D₁ o) = PRFPRNG.branch prng b (D₂ o)) :
    PRFPRNG.advantage prng (advAvg oa D₁) = PRFPRNG.advantage prng (advAvg oa D₂) := by
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
  have hT : (oa >>= fun o => PRFPRNG.branch prng true (D₁ o)) =
      (oa >>= fun o => PRFPRNG.branch prng true (D₂ o)) :=
    bind_congr fun o => hBr o true
  have hF : (oa >>= fun o => PRFPRNG.branch prng false (D₁ o)) =
      (oa >>= fun o => PRFPRNG.branch prng false (D₂ o)) :=
    bind_congr fun o => hBr o false
  rw [hT, hF]

theorem fig8MixAuth_simFig8_le_fig8MixShortAuthV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    letI : MeasurableSpace α := ⊤
    let simAdv : α → Fig8Adv Pt ℓ := fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
    2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
      (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
        + PRFPRNG.advantage (rootPRNG Z.F encPt)
          (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
        + ∫⁻ o, ∑ j ∈ Finset.range q,
            FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
              (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
                tL t (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))) ∂𝒟[oa]) ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hqSim : ∀ o, SM.MakesAtMostQueries (simAdv o) q := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hshSim : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (simAdv o) := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sendAtomicShort
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hgSim : ∀ o, SessionShort.GuardedSMShort (simAdv o) := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_guardedSMShort
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hChall : ∀ o,
      ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
        lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ()) =
      SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o) := fun o =>
    fig8RedsInst_challSim_eval Dh encPt Z protoSignalCodec ℓ hℓ encT (idsOf (ida o) (idb o))
      lam (qep + 1) q (simAdv o) (hqSim o)
  have hqChall : ∀ o,
      SM.MakesAtMostQueries (SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) q := fun o =>
    SM.Thm1.challSim_queries (2 + 1) (qep + 1) (simAdv o) q (hqSim o)
  have hshChall : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) := fun o =>
    SessionShort.challSim_sendOk (2 + 1) (qep + 1)
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (simAdv o) (hshSim o)
  have hAuthOk := fun o =>
    (fig8RedsInst_fsOk_and_encAtomicShort Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      (idsOf (ida o) (idb o)) lam (qep + 1) q (simAdv o) (hqSim o) (hshSim o) (hgSim o)).1
  unfold fig8MixShortAuthV1
  dsimp only [v1SessionReds_fig8, v1SessionReds_fs, v1SessionReds_simFig8]
  gcongr with t _ tL _
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAAuth tL t).eval
            (fun _ => ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAAuth tL t).eval
            (fun _ => SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hChall o])
    exact le_of_eq ((fig8RedsInst_redCKAAuth_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL t
      _ hqChall hshChall).symm.trans
      (congrArg (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)) hEq.symm))
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGAuth tL t).eval
            (fun _ => ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGAuth tL t).eval
            (fun _ => SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hChall o])
    exact le_of_eq ((fig8RedsInst_redPRNGAuth_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL t _ hqChall hshChall).symm.trans
      (congrArg (PRFPRNG.advantage (rootPRNG Z.F encPt)) hEq.symm))
  · rw [lintegral_finsetSum (Finset.range q) (fun _ _ => Measurable.of_discrete)]
    gcongr with j _
    have hbias := fig8RedsInst_redFSAuth_mix_boolBias Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q j tL t _ hqChall hshChall
    have hGame :
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSAuth j tL t).eval
            (fun _ => SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o)) ())) =
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSAuth j tL t).eval
            (fun _ => ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).challSim.eval (fun _ => simAdv o) ())) ())) :=
      bind_congr fun o => by rw [hChall o]; rfl
    change (∫⁻ o, FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
      (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps) lam 1 (qep + 1) j
        tL t (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))) ∂𝒟[oa]) ≤ _
    rw [hbias, hGame, fsShortBoundMixWith_inst_eq Z ℓ encT oa (fun o => idsOf (ida o) (idb o))
      (min (2 * q) (q + 2)) q hℓ hinj _ (fun o => (hAuthOk o j tL t).1.1) (fun o => (hAuthOk o j tL t).2)]
    exact lFS_bound_mix_of_fsOk_v1 Z hD ℓ (by omega) encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) _ (min (2 * q) (q + 2)) q (by omega) (fun o => (hAuthOk o j tL t).1)

theorem fig8MixPriv_simFig8_le_fig8MixShortPrivV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    letI : MeasurableSpace α := ⊤
    let simAdv : α → Fig8Adv Pt ℓ := fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
    2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (advAvg oa fun o => redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))
        + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
          (advAvg oa fun o => redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))
        + 𝒟[oa >>= fun o =>
            FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
              (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
                (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))].boolBias
        + 2 * ∫⁻ o,
            FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
              (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
                (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o))) ∂𝒟[oa]) ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hqSim : ∀ o, SM.MakesAtMostQueries (simAdv o) q := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hshSim : ∀ o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) (simAdv o) := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sendAtomicShort
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hgSim : ∀ o, SessionShort.GuardedSMShort (simAdv o) := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_guardedSMShort
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hPriv : ∀ o i,
      (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
        lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ()) =
      SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) := fun o i =>
    fig8RedsInst_privRedB_eval Dh encPt Z protoSignalCodec ℓ hℓ encT (idsOf (ida o) (idb o))
      lam (qep + 1) q i (simAdv o) (hqSim o)
  have hqPriv : ∀ i o,
      SM.MakesAtMostQueries (SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) q :=
    fun i o => PrivRedQueries.privRedB_queries (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) q (hqSim o)
  have hshPriv : ∀ i o, SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) := fun i o =>
    SessionShort.privRedB_sendOk (2 + 1) (qep + 1) i
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1)
      (lBlank ℓ) (fun _ => rfl) (simAdv o) (hshSim o)
  have hPrivOk := fun o =>
    (fig8RedsInst_fsOk_and_encAtomicShort Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      (idsOf (ida o) (idb o)) lam (qep + 1) q (simAdv o) (hqSim o) (hshSim o) (hgSim o)).2
  unfold fig8MixShortPrivV1
  dsimp only [v1SessionReds_fig8, v1SessionReds_fs, v1SessionReds_simFig8]
  gcongr with i _ tL _
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAPriv tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redCKAPriv tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hPriv o i])
    exact le_of_eq ((fig8RedsInst_redCKAPriv_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL i
      _ (hqPriv i) (hshPriv i)).symm.trans
      (congrArg (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)) hEq.symm))
  · have hEq :
        (prefixAdvAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGPriv tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ()) =
        (advAvg oa fun o =>
          ((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redPRNGPriv tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      unfold prefixAdvAvg advAvg
      exact congrArg _ (funext fun o => by rw [hPriv o i])
    exact le_of_eq ((fig8RedsInst_redPRNGPriv_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i
      _ (hqPriv i) (hshPriv i)).symm.trans
      (congrArg (PRFPRNG.advantage (rootPRNG Z.F encPt)) hEq.symm))
  · have heq := (fig8RedsInst_redFSPriv_mix_evalDistEq Dh encPt Z protoSignalCodec rfl ℓ hℓ encT
      oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i _ (hqPriv i) (hshPriv i)).evalDist_eq
    have hGame :
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPriv tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ())) =
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPriv tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ())) :=
      bind_congr fun o => by rw [hPriv o i]; rfl
    change 𝒟[oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
      (redFSPriv (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps) lam 1 (qep + 1) tL i
        (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)))].boolBias ≤ _
    rw [← heq, hGame, fsShortBoundMixWith_inst_eq Z ℓ encT oa (fun o => idsOf (ida o) (idb o))
      (min (2 * q) (q + 2)) q hℓ hinj _ (fun o => ((hPrivOk o i).1 tL).1.1) (fun o => ((hPrivOk o i).1 tL).2)]
    exact lFS_bound_mix_of_fsOk_v1 Z hD ℓ (by omega) encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) _ (min (2 * q) (q + 2)) q (by omega) (fun o => ((hPrivOk o i).1 tL).1)
  · have hbias := fig8RedsInst_redFSPrivCoin_mix_boolBias Dh encPt Z protoSignalCodec rfl ℓ hℓ
      encT oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i _ (hqPriv i) (hshPriv i)
    have hGame :
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPrivCoin tL i).eval
            (fun _ => SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ())) =
        (oa >>= fun o => FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
          (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
            lam (qep + 1) q).redFSPrivCoin tL i).eval
            (fun _ => (((fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
              lam (qep + 1) q).privRedB i).eval (fun _ => simAdv o) ())) ())) :=
      bind_congr fun o => by rw [hPriv o i]; rfl
    change (∫⁻ o, FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps)
      (redFSPrivCoin (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) maxForwardJumps) lam 1 (qep + 1) tL i
        (ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o))) ∂𝒟[oa]) ≤ _
    rw [hbias, hGame, fsShortBoundMixWith_inst_eq Z ℓ encT oa (fun o => idsOf (ida o) (idb o))
      (min (2 * q) (q + 2)) q hℓ hinj _ (fun o => ((hPrivOk o i).2 tL).1.1) (fun o => ((hPrivOk o i).2 tL).2)]
    exact lFS_bound_mix_of_fsOk_v1 Z hD ℓ (by omega) encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) _ (min (2 * q) (q + 2)) q (by omega) (fun o => ((hPrivOk o i).2 tL).1)

/-- Fig. 8 H1 bias of the `libsignalToModularSchemeSim` mixture is bounded by `fig8MixShortAuthV1 + fig8MixShortPrivV1` on `v1SessionReds`. -/
theorem boolBias_mixFig8_le_fig8MixShortV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
        (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o))].boolBias ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A +
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hGame :
      (oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1
        (Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o))) =
      (oa >>= fun o => SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) SM.Config.h1 (simAdv o)) :=
    bind_congr fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sm_game_eq
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q SM.Config.h1 (A o) (hq o)).symm
  rw [hGame]
  have h6 := theorem6_h1_blank_mix (dhScheme Dh) (rootPRNG Z.F encPt)
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
    (dhScheme_correct Dh hDh) (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1) (lBlank ℓ)
    (fun _ _ h => by simp [lBlank, h]) oa simAdv
    (fun o => Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_equalPub
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)) q
    (fun o => Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o))
  exact h6.trans (add_le_add
    (fig8MixAuth_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb A hq)
    (fig8MixPriv_simFig8_le_fig8MixShortPrivV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb A hq))

/-- Twice `simCNoneWinEvent` of the mixture is bounded by `fig8MixShortAuthV1` on `v1SessionReds`. -/
theorem evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1 {α : Type} (Z : Crypto) (K : MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, SM.MakesAtMostQueries (A o) q) :
    2 * 𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => v1SessionReds ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q) A := by
  let _ : MeasurableSpace α := ⊤
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hWin :
      𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
        ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          𝒟[oa >>= fun o => authGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} :=
    evalDist_bind_apply_le_sum_sum oa _ _ _ _ fun o => by
      rw [Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_simCNoneWinEvent_eq
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)]
      exact Proofs.Refinement.run_win_prob_le_auth
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) (by omega) (simAdv o)
  have h8 :
      2 * (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          𝒟[oa >>= fun o => authGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true}) ≤
        2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
              (advAvg oa fun o => redCKAAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
                (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
            + PRFPRNG.advantage (rootPRNG Z.F encPt)
              (advAvg oa fun o => redPRNGAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
                (Thm1.challSim (2 + 1) (qep + 1) (simAdv o)))
            + ∫⁻ o, ∑ j ∈ Finset.range q,
                FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
                  (redFSAuth (dhScheme Dh) (rootPRNG Z.F encPt)
                    (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) j
                    tL t (Thm1.challSim (2 + 1) (qep + 1) (simAdv o))) ∂𝒟[oa]) := by
    gcongr with t _ tL _
    exact theorem8_mix (dhScheme Dh) (rootPRNG Z.F encPt)
      (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
      (dhScheme_correct Dh hDh) tL t q oa _ fun o => Thm1.challSim_queries _ _ _ q
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
          hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o))
  exact (mul_le_mul_right hWin 2).trans (h8.trans
    (fig8MixAuth_simFig8_le_fig8MixShortAuthV1 Z K hD hℓ Dh encPt encT decT hinj hdum lam qep q
      hq32 oa ida idb A hq))

/-- Per-`o` costed hidden-salt bound matching the integrand of `hiddenSaltMixtureBound`. -/
noncomputable def hiddenSaltBoundV1 (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (R : SessionCostedReductions Pt ℓ Z K idA idB Dh encPt encT decT lam)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  let dfAdv := R.simDeliverForge.eval (fun _ => A) ()
  let challAdvDF := R.challSimDF.eval (fun _ => dfAdv) ()
  ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        ((R.B_cka tL t).eval (fun _ => challAdvDF) ()) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        ((R.B_prng tL t).eval (fun _ => challAdvDF) ()) +
      (∑ j ∈ Finset.range q,
        CryptoVerification.E2E.fsAeadSlotSumBound Z (min (2 * q) (q + 2)) R.fs
          ((R.B_fs j tL t).eval (fun _ => challAdvDF) ())) +
      4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q) +
    spuriousStepTerm Z.F encPt Dh q qep +
    (qep + 1) * (qep + 2) * δ

theorem lintegral_mono_of_support {α : Type} (oa : ProbComp α) (f g : α → ℝ≥0∞)
    (h : ∀ o ∈ support oa, f o ≤ g o) :
    letI : MeasurableSpace α := ⊤
    ∫⁻ o, f o ∂𝒟[oa] ≤ ∫⁻ o, g o ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have hae : ∀ᵐ x ∂𝒟[oa], x ∈ support oa :=
    evalDist.ae_of_forall_mem_support oa (· ∈ support oa) MeasurableSet.of_discrete fun _ ho => ho
  exact lintegral_mono_ae (hae.mono h)

theorem lintegral_congr_of_support {α : Type} (oa : ProbComp α) (f g : α → ℝ≥0∞)
    (h : ∀ o ∈ support oa, f o = g o) :
    letI : MeasurableSpace α := ⊤
    ∫⁻ o, f o ∂𝒟[oa] = ∫⁻ o, g o ∂𝒟[oa] :=
  le_antisymm
    (lintegral_mono_of_support oa f g fun o ho => le_of_eq (h o ho))
    (lintegral_mono_of_support oa g f fun o ho => le_of_eq (h o ho).symm)

theorem evalDist_mixHiddenSalt_le_v1_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hHid : ∀ o ∈ support oa,
      let P := paramsV1 Z K (ida o) (idb o)
      LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT (idsOf (ida o) (idb o)) lam qep (A o) ≤
        hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT (ida o) (idb o) lam qep q δ (R o) (A o)) :
    𝒟[oa >>= fun o => LibsignalSimC.hiddenSaltGame (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT
        decT (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      CryptoVerification.E2E.hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ
        oa ida idb R A := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral]
  refine (lintegral_mono_of_support oa _ _ hHid).trans_eq ?_
  unfold hiddenSaltBoundV1 CryptoVerification.E2E.hiddenSaltMixtureBound
  change (∫⁻ o, _ ∂𝒟[oa]) = _
  simp only [lintegral_add_left Measurable.of_discrete,
    lintegral_finsetSum _ fun _ _ => Measurable.of_discrete,
    lintegral_const, evalDist_apply_univ_eq_one, mul_one]

@[simp]
private lemma stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private def toRefuseState {C : Type} (r : RefuseB0.RefuseState C) :
    RefuseCorrB0.RefuseState C :=
  ⟨r.epoch, r.idx, r.trans⟩

@[simp]
private lemma toRefuseState_epoch {C : Type} (r : RefuseB0.RefuseState C) :
    (toRefuseState r).epoch = r.epoch := rfl

private lemma toRefuseState_onSend {C : Type} (r : RefuseB0.RefuseState C) (P : Party) (c : C) :
    toRefuseState (r.onSend P c) = (toRefuseState r).onSend P c := rfl

private lemma toRefuseState_onAccept {C : Type} (r : RefuseB0.RefuseState C) (P : Party)
    (pos : SM.Pos) :
    toRefuseState (r.onAccept P pos) = (toRefuseState r).onAccept P pos := rfl

private lemma toRefuseState_onDeliver {C : Type} [DecidableEq C] (r : RefuseB0.RefuseState C)
    (P : Party) (c : C) :
    toRefuseState (r.onDeliver P c) = (toRefuseState r).onDeliver P c := by
  unfold RefuseB0.RefuseState.onDeliver RefuseCorrB0.RefuseState.onDeliver toRefuseState
  dsimp only
  cases List.find? (fun pc => pc.1.sender == P.other && decide (pc.2 = c)) r.trans <;> rfl

private lemma refuseCorrB0Impl_run_toRefuseState {St Msg Coins C : Type} [DecidableEq C]
    (q : (unifSpec + SM.spec St Msg Coins C).Domain) (r : RefuseB0.RefuseState C) :
    (RefuseCorrB0.refuseCorrB0Impl (St := St) (Msg := Msg) (Coins := Coins) (C := C) q).run
        (toRefuseState r) =
      Prod.map id toRefuseState <$>
        (RefuseB0.refuseCorrB0Impl (St := St) (Msg := Msg) (Coins := Coins) (C := C) q).run r := by
  rcases q with n | ((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change (StateT.lift (query (spec := unifSpec + SM.spec St Msg Coins C) (.inl n)) :
        RefuseCorrB0.RefuseM St Msg Coins C _).run (toRefuseState r) =
      Prod.map id toRefuseState <$>
        (StateT.lift (query (spec := unifSpec + SM.spec St Msg Coins C) (.inl n)) :
          RefuseB0.RefuseM St Msg Coins C _).run r
    simp [map_eq_bind_pure_comp]
  · change (RefuseCorrB0.refuseTransmit (P, m, rc)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseTransmit (P, m, rc)).run r
    unfold RefuseCorrB0.refuseTransmit RefuseB0.refuseTransmit
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res <;> simp [toRefuseState_onSend]
  · change (RefuseCorrB0.refuseChall (P, m₀, m₁, rc)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseChall (P, m₀, m₁, rc)).run r
    unfold RefuseCorrB0.refuseChall RefuseB0.refuseChall
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res <;> simp [toRefuseState_onSend]
  · change (RefuseCorrB0.refuseDeliver (P, c)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseDeliver (P, c)).run r
    unfold RefuseCorrB0.refuseDeliver RefuseB0.refuseDeliver
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res with
    | none => simp
    | some rr => cases rr <;> simp [toRefuseState_onDeliver]
  · change (RefuseCorrB0.refuseInject (P, c)).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseInject (P, c)).run r
    unfold RefuseCorrB0.refuseInject RefuseB0.refuseInject
    simp only [StateT.run_bind, stateT_run_lift, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    cases res with
    | none => simp
    | some rr => cases rr <;> simp [toRefuseState_onAccept]
  · change (RefuseCorrB0.refuseCorr P).run (toRefuseState r) =
      Prod.map id toRefuseState <$> (RefuseB0.refuseCorr P).run r
    unfold RefuseCorrB0.refuseCorr RefuseB0.refuseCorr
    rw [StateT.run_bind, StateT.run_bind, StateT.run_get, StateT.run_get,
      pure_bind, pure_bind, toRefuseState_epoch]
    split_ifs <;> simp [map_eq_bind_pure_comp]

theorem refuseCorrB0_eq {St Msg Coins C : Type} [DecidableEq C]
    (A : SM.Adversary St Msg Coins C) :
    RefuseB0.refuseCorrB0 A = A.refuseCorrB0 := by
  unfold RefuseB0.refuseCorrB0 SM.Adversary.refuseCorrB0
  exact run'_simulateQ_eq_of_inv_dis RefuseB0.refuseCorrB0Impl RefuseCorrB0.refuseCorrB0Impl
    (fun _ => True) toRefuseState (fun _ => False)
    (fun _ _ _ _ _ _ => trivial)
    (fun t r _ _ => (refuseCorrB0Impl_run_toRefuseState t r).symm)
    A (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false A 0) {} trivial

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem prfAdvantage_prefixPrfAvg_congr_of_support {α Key Input Tag : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (oa : ProbComp α)
    (D₁ D₂ : α → MACScheme.PRFAdversary Input Tag)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    mac.prfAdvantage (prefixPrfAvg oa D₁) = mac.prfAdvantage (prefixPrfAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => mac.branch b (D₁ o)] =
      𝒟[oa >>= fun o => mac.branch b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change mac.prfAdvantage (prfAvg oa D₁) = mac.prfAdvantage (prfAvg oa D₂)
  rw [MACScheme.prfAdvantage_eq_boolDist, MACScheme.prfAdvantage_eq_boolDist,
    prfBranch_avg, prfBranch_avg, prfBranch_avg, prfBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem prgAdvantage_prefixPrgAvg_congr_of_support {α S R : Type}
    [SampleableType S] [SampleableType R]
    (prg : PRGScheme S R) (oa : ProbComp α)
    (D₁ D₂ : α → PRGScheme.PRGAdversary R)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    prg.prgAdvantage (prefixPrgAvg oa D₁) = prg.prgAdvantage (prefixPrgAvg oa D₂) := by
  have hr : 𝒟[oa >>= fun o => prg.prgRealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => prg.prgRealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  have hi : 𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change prg.prgAdvantage (prgAvg oa D₁) = prg.prgAdvantage (prgAvg oa D₂)
  unfold PRGScheme.prgAdvantage
  rw [prgReal_avg, prgReal_avg, prgIdeal_avg, prgIdeal_avg, hr, hi]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem ckaAdvantage_prefixAdvAvg_congr_of_support {α Key State Coins Msg CKey : Type}
    [SampleableType Key] [SampleableType Coins] [SampleableType CKey]
    (cka : CKAScheme Key State Coins Msg CKey) (Δ tStar : ℕ) (oa : ProbComp α)
    (D₁ D₂ : α → CKA.Adversary State Coins Msg CKey)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    CKA.advantage cka Δ tStar (prefixAdvAvg oa D₁) =
      CKA.advantage cka Δ tStar (prefixAdvAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => CKA.branch cka Δ tStar b (D₁ o)] =
      𝒟[oa >>= fun o => CKA.branch cka Δ tStar b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change CKA.advantage cka Δ tStar (advAvg oa D₁) = CKA.advantage cka Δ tStar (advAvg oa D₂)
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem prngAdvantage_prefixAdvAvg_congr_of_support {α Key State Input Output : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Input] [SampleableType Output]
    (P : PRFPRNG Key State Input Output) (oa : ProbComp α)
    (D₁ D₂ : α → PRFPRNG.Adversary State Input Output)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    PRFPRNG.advantage P (prefixAdvAvg oa D₁) = PRFPRNG.advantage P (prefixAdvAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => PRFPRNG.branch P b (D₁ o)] =
      𝒟[oa >>= fun o => PRFPRNG.branch P b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change PRFPRNG.advantage P (advAvg oa D₁) = PRFPRNG.advantage P (advAvg oa D₂)
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg, hb true, hb false]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem wireOtccaAdvantage_prefixWireAvg_congr_of_support {α K AD H M M' C T : Type}
    [SampleableType K] [SampleableType C] [SampleableType T] [DecidableEq AD] [DecidableEq T]
    (ae : WireAEAD K AD H M M' C T) (oa : ProbComp α)
    (D₁ D₂ : α → WireAEAD.WireAdversary AD H M M' T)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    ae.wireOtccaAdvantage (prefixWireAvg oa D₁) = ae.wireOtccaAdvantage (prefixWireAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => FSMix.wBranch ae b (D₁ o)] =
      𝒟[oa >>= fun o => FSMix.wBranch ae b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  change ae.wireOtccaAdvantage (FSMix.wireAvg oa D₁) = ae.wireOtccaAdvantage (FSMix.wireAvg oa D₂)
  rw [FSMix.wireOtccaAdvantage_eq_boolDist_wBranch, FSMix.wireOtccaAdvantage_eq_boolDist_wBranch,
    FSMix.wBranch_avg, FSMix.wBranch_avg, FSMix.wBranch_avg, FSMix.wBranch_avg, hb true, hb false]

omit [Zero Pt] [SampleableType Pt] in
theorem fsShortBoundMixWith_congr_of_support {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} (oa : ProbComp α) {idOf : α → Party → IdentityKey} (q qd : ℕ)
    (R : ∀ o, FsCostedReds C codec ℓ encT (idOf o))
    (A₁ A₂ : α → FsAdv Pt ℓ) (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    fsAeadMixtureBound C codec ℓ oa q qd R A₁ = fsAeadMixtureBound C codec ℓ oa q qd R A₂ := by
  unfold fsAeadMixtureBound fsChainPrgMixtureTerm fsSaltWireMixtureTerm
  refine congrArg (· + 4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) (congrArg (2 * ·) ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  have h1 := prgAdvantage_prefixPrgAvg_congr_of_support (lChainPRG C.F (Thm5.slotToHybridHopIndex q j / 2)) oa
    (fun o mt => evalTwoStage1 ((R o).prgRedZero (Thm5.slotToHybridHopIndex q j)) q false
      (fun _ => pubToADCosted (R o) (A₁ o)) mt)
    (fun o mt => evalTwoStage1 ((R o).prgRedZero (Thm5.slotToHybridHopIndex q j)) q false
      (fun _ => pubToADCosted (R o) (A₂ o)) mt)
    (fun o ho => by rw [hA o ho])
  have h2 := prfAdvantage_prefixPrfAvg_congr_of_support (lSaltPRF32 C.F) oa
    (fun o => (R o).lSaltRed.eval (fun _ => ((R o).slotSaltRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₁ o)) ()) ())
    (fun o => (R o).lSaltRed.eval (fun _ => ((R o).slotSaltRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₂ o)) ()) ())
    (fun o ho => by rw [hA o ho])
  have h3 := wireOtccaAdvantage_prefixWireAvg_congr_of_support (lWire C codec ℓ) oa
    (fun o => (R o).lWireRed.eval (fun _ => ((R o).slotWireRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₁ o)) ()) ())
    (fun o => (R o).lWireRed.eval (fun _ => ((R o).slotWireRed (Thm5.slotToHybridHopIndex q j)).eval
      (fun _ => multiSlotAdvCosted q (R o) (Thm5.isLookaheadHop (Thm5.slotToHybridHopIndex q j)) (A₂ o)) ()) ())
    (fun o ho => by rw [hA o ho])
  rw [h1, h2, h3]

theorem fig8MixShortAuthV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₁ =
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₂ := by
  unfold fig8MixShortAuthV1
  dsimp only
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun tL _ => ?_)
  have hc := ckaAdvantage_prefixAdvAvg_congr_of_support (dhScheme Dh) 1 (healEpoch tL) oa
    (fun o => ((R o).fig8.redCKAAuth tL t).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redCKAAuth tL t).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  have hp := prngAdvantage_prefixAdvAvg_congr_of_support (rootPRNG Z.F encPt) oa
    (fun o => ((R o).fig8.redPRNGAuth tL t).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redPRNGAuth tL t).eval (fun _ => (R o).fig8.challSim.eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  rw [hc, hp]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun j _ => ?_)
  exact fsShortBoundMixWith_congr_of_support Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q
    (fun o => (R o).fs) _ _ fun o ho => by rw [hA o ho]

theorem fig8MixShortPrivV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₁ =
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A₂ := by
  unfold fig8MixShortPrivV1
  dsimp only
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun tL _ => ?_)
  have hc := ckaAdvantage_prefixAdvAvg_congr_of_support (dhScheme Dh) 1 (healEpoch tL) oa
    (fun o => ((R o).fig8.redCKAPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redCKAPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  have hp := prngAdvantage_prefixAdvAvg_congr_of_support (rootPRNG Z.F encPt) oa
    (fun o => ((R o).fig8.redPRNGPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redPRNGPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  have hf1 := fsShortBoundMixWith_congr_of_support Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q
    (fun o => (R o).fs)
    (fun o => ((R o).fig8.redFSPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redFSPriv tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  have hf2 := fsShortBoundMixWith_congr_of_support Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q
    (fun o => (R o).fs)
    (fun o => ((R o).fig8.redFSPrivCoin tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₁ o) ()) ()) ())
    (fun o => ((R o).fig8.redFSPrivCoin tL i).eval (fun _ => ((R o).fig8.privRedB i).eval
      (fun _ => (R o).simFig8.eval (fun _ => A₂ o) ()) ()) ())
    (fun o ho => by rw [hA o ho])
  rw [hc, hp, hf1, hf2]

theorem hiddenSaltBoundMixV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    CryptoVerification.E2E.hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        A₁ =
      CryptoVerification.E2E.hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        A₂ := by
  let _ : MeasurableSpace α := ⊤
  unfold CryptoVerification.E2E.hiddenSaltMixtureBound
  dsimp only
  have hsum :
      (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
        ((∫⁻ o, CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (((R o).B_cka tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
              (R o).simDeliverForge.eval (fun _ => A₁ o) ()) ()) ())
            ∂𝒟[oa]) +
          (∫⁻ o, PRFPRNG.advantage (rootPRNG Z.F encPt)
            (((R o).B_prng tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
              (R o).simDeliverForge.eval (fun _ => A₁ o) ()) ()) ())
            ∂𝒟[oa]) +
          (∑ j ∈ Finset.range q,
            ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
              (((R o).B_fs j tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
                (R o).simDeliverForge.eval (fun _ => A₁ o) ()) ()) ())
              ∂𝒟[oa]) +
          4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) =
      (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
        ((∫⁻ o, CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
            (((R o).B_cka tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
              (R o).simDeliverForge.eval (fun _ => A₂ o) ()) ()) ())
            ∂𝒟[oa]) +
          (∫⁻ o, PRFPRNG.advantage (rootPRNG Z.F encPt)
            (((R o).B_prng tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
              (R o).simDeliverForge.eval (fun _ => A₂ o) ()) ()) ())
            ∂𝒟[oa]) +
          (∑ j ∈ Finset.range q,
            ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
              (((R o).B_fs j tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
                (R o).simDeliverForge.eval (fun _ => A₂ o) ()) ()) ())
              ∂𝒟[oa]) +
          4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) := by
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun tL _ => ?_
    have h1 := lintegral_congr_of_support oa
      (fun o => CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (((R o).B_cka tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
          (R o).simDeliverForge.eval (fun _ => A₁ o) ()) ()) ()))
      (fun o => CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (((R o).B_cka tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
          (R o).simDeliverForge.eval (fun _ => A₂ o) ()) ()) ()))
      (fun o ho => by rw [hA o ho])
    have h2 := lintegral_congr_of_support oa
      (fun o => PRFPRNG.advantage (rootPRNG Z.F encPt)
        (((R o).B_prng tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
          (R o).simDeliverForge.eval (fun _ => A₁ o) ()) ()) ()))
      (fun o => PRFPRNG.advantage (rootPRNG Z.F encPt)
        (((R o).B_prng tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
          (R o).simDeliverForge.eval (fun _ => A₂ o) ()) ()) ()))
      (fun o ho => by rw [hA o ho])
    have h3 :
        (∑ j ∈ Finset.range q,
          ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
            (((R o).B_fs j tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
              (R o).simDeliverForge.eval (fun _ => A₁ o) ()) ()) ())
            ∂𝒟[oa]) =
        (∑ j ∈ Finset.range q,
          ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
            (((R o).B_fs j tL t).eval (fun _ => (R o).challSimDF.eval (fun _ =>
              (R o).simDeliverForge.eval (fun _ => A₂ o) ()) ()) ())
            ∂𝒟[oa]) :=
      Finset.sum_congr rfl fun j _ =>
        lintegral_congr_of_support oa _ _ fun o ho => by rw [hA o ho]
    rw [h1, h2, h3]
  rw [hsum]

theorem uTermShortMixV1_congr_of_support {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A₁ A₂ : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    CryptoVerification.E2E.uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A₁ =
      CryptoVerification.E2E.uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        A₂ := by
  have ha := fig8MixShortAuthV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A₁ o)) (fun o => RefuseB0.refuseCorrB0 (A₂ o))
    (fun o ho => by rw [hA o ho])
  have hp := fig8MixShortPrivV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A₁ o)) (fun o => RefuseB0.refuseCorrB0 (A₂ o))
    (fun o ho => by rw [hA o ho])
  have he := prgAdvantage_prefixPrgAvg_congr_of_support (rootKdfAsPrg Z.F (encPt lam)) oa
    (fun o rc => (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A₁ o)) rc)
    (fun o rc => (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A₂ o)) rc)
    (fun o ho => by rw [hA o ho])
  have hh := hiddenSaltBoundMixV1_congr_of_support Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A₁ o)) (fun o => RefuseB0.refuseCorrB0 (A₂ o))
    (fun o ho => by rw [hA o ho])
  have hu := prgAdvantage_prefixPrgAvg_congr_of_support (rootKdfAsPrg Z.F (encPt lam)) oa
    (fun o rc => (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A₁ o)) rc)
    (fun o rc => (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A₂ o)) rc)
    (fun o ho => by rw [hA o ho])
  unfold CryptoVerification.E2E.uniformStartMixtureBound
  rw [ha, hp, he, hh, hu]

omit [Zero Pt] [SampleableType Pt] in
theorem fsShortBound_eq_deliverForgeFSCompBound_add (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd : ℕ) (R : FsAdv Pt ℓ) :
    fsShortBound C codec ℓ encT idOf qR qd R =
      Proofs.Refinement.deliverForgeFSCompBound C codec ℓ encT idOf qR R +
        4 * CryptoVerification.LibsignalSession.macForgeryTerm C qd := by
  unfold fsShortBound fsCompBound
    Proofs.Refinement.deliverForgeFSCompBound wireOtccaTerm
  simp only [add_assoc]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_runDFM {PQ : Type} [Inhabited PQ] {ℓ : ℕ}
    {Q : (HeadlineV1.DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {n : ℕ} (hx : HeadlineV1.df_QBC Q x n)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    IsQueryBoundP (LibsignalSim.runDFM x sC ex) Q n := by
  unfold LibsignalSim.runDFM
  rw [← Nat.add_zero n]
  exact isQueryBoundP_bind (hx sC ex) fun p _ => isQueryBoundP_pure Q (p.1.1, p.1.2, p.2) 0

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_deliverQueryDF_QShortDF {ℓ : ℕ} (Q : Party) (c : Fig8C Pt) :
    IsQueryBoundP
      (DeliverForge.deliverQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c)
      (HeadlineV1.QShortDF Pt ℓ) 0 :=
  (isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ)
    (.inr (.inl (.inl (.inl (.inr (Q, c)))))) 0).2 fun h => nomatch h

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_injectQueryDF_QShortDF {ℓ : ℕ} (Q : Party) (c : Fig8C Pt) :
    IsQueryBoundP
      (DeliverForge.injectQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c)
      (HeadlineV1.QShortDF Pt ℓ) 0 :=
  (isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ)
    (.inr (.inl (.inl (.inr (Q, c))))) 0).2 fun h => nomatch h

omit [Zero Pt] [SampleableType Pt] in
private lemma isQueryBoundP_deliverForgeSemHook_onProbe {PQC : Type} [SampleableType PQC] {ℓ : ℕ}
    (Q : Party) (c' : Fig8C Pt) (ex : List (Fig8C Pt)) :
    IsQueryBoundP
      ((LibsignalSim.deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex)
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => Proofs.Refinement.sameWireFig8 c c') with _ | c
  · simp
  · have hq : IsQueryBoundP
        (DeliverForge.deliverForgeQuery
          (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
          Q c c') (HeadlineV1.QShortDF Pt ℓ) 0 :=
      (isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ) (.inr (.inr (Q, c, c'))) 0).2
        fun h => nomatch h
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind hq fun _ _ => by simp

omit [SampleableType Pt] in
private lemma isQueryBoundP_semFwdAnswerHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (LibsignalSim.semFwdAnswerHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel ci? Tpk pq' c')
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semFwdAnswerHook LibsignalSim.deliverForgeSemHook
  dsimp only
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind ?_ fun ⟨res, ex'⟩ _ => by rcases res with _ | (_ | _) <;> simp
  split_ifs
  · rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_deliverQueryDF_QShortDF Q c') fun _ _ => by simp
  · rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_injectQueryDF_QShortDF Q c') fun _ _ => by simp

omit [SampleableType Pt] in
private lemma isQueryBoundP_semResyncHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × CBC.Plain ℓ))) :
    IsQueryBoundP
      (LibsignalSim.semResyncHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w ci? Tpk pq' c r)
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semResyncHook LibsignalSim.deliverForgeSemHook
  rcases r with _ | ⟨t, i, pub, m'⟩
  · simp
  · dsimp only
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind ?_ fun ⟨res, ex'⟩ _ => by rcases res with _ | (_ | _) <;> simp
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_deliverQueryDF_QShortDF Q c) fun _ _ => by simp

omit [SampleableType Pt] in
private lemma isQueryBoundP_semFwdEvictHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (LibsignalSim.semFwdEvictHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel Tpk pq' c')
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semFwdEvictHook
  split_ifs
  · rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind
      (isQueryBoundP_deliverForgeSemHook_onProbe (PQC := PQC) Q c' ex)
      fun _ _ => by simp
  · exact isQueryBoundP_semFwdAnswerHook_QShortDF P Dh encPt encT lam qep sC ex Q w isDel none
      Tpk pq' c'

omit [SampleableType Pt] in
private lemma isQueryBoundP_semFwdHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    IsQueryBoundP
      (LibsignalSim.semFwdHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel ci? Tpk pq' honestC c')
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semFwdHook
  rcases honestC with _ | c
  · exact isQueryBoundP_semFwdAnswerHook_QShortDF P Dh encPt encT lam qep sC ex Q w isDel ci?
      Tpk pq' c'
  · dsimp only
    split_ifs
    · rcases LibsignalSim.evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · rw [← Nat.zero_add 0]
        exact isQueryBoundP_bind
          (isQueryBoundP_deliverForgeSemHook_onProbe (PQC := PQC) Q c' ex)
          fun _ _ => by simp
      · exact isQueryBoundP_semResyncHook_QShortDF P Dh encPt encT lam qep sC ex Q w ci?
          Tpk pq' c r
    · exact isQueryBoundP_semFwdAnswerHook_QShortDF P Dh encPt encT lam qep sC ex Q w isDel ci?
        Tpk pq' c'

omit [SampleableType Pt] in
private lemma isQueryBoundP_semRecvHook_QShortDF {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP
      (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel)
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
  unfold LibsignalSim.semRecvHook
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases LibsignalSim.simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · simp
    · rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · simp
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact isQueryBoundP_semFwdHook_QShortDF P Dh encPt encT lam qep B _ ex
                    Q w isDel none pk pq' _ _
                · simp only [↓reduceIte]
                  exact isQueryBoundP_semFwdEvictHook_QShortDF P Dh encPt encT lam qep _ ex
                    Q w isDel pk pq' _
            · simp
          · simp
        · simp
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects
            i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact isQueryBoundP_semFwdHook_QShortDF P Dh encPt encT lam qep B sC ex
            Q w isDel (some ci) pk pq' _ _
        · simp
  · simp

omit [SampleableType Pt] in
theorem simDeliverForgeClamp_sendShort {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) {ℓ : ℕ} (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) PQC Bytes) :
    HeadlineV1.SendMsgsOkDF (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => m.1.shortB)
      (LibsignalSim.simDeliverForgeClamp P Dh encPt encT decT lam qep B A) := by
  unfold HeadlineV1.SendMsgsOkDF LibsignalSim.simDeliverForgeClamp
  have hpqr : IsQueryBoundP
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × CBC.Plain ℓ) (BitVec 256) (Fig8C Pt)
          (BitVec 256))
      (HeadlineV1.QShortDF Pt ℓ) 0 := by
    induction ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx ih =>
      change IsQueryBoundP (query (spec := HeadlineV1.DFSpec Pt ℓ) (.inl t) >>=
        fun u => liftM (mx u)) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind
        ((isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ) (.inl t) 0).2 fun h => nomatch h)
        fun u _ => ih u
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind hpqr fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  have hstep :
      ∀ (t : (unifSpec + SM.spec (GhostState PQ) (CBC.Plain ℓ) PQC Bytes).Domain)
        (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)),
        IsQueryBoundP
          ((LibsignalSim.simDeliverForgeOracle P Dh encPt encT decT lam qep B t).run (sC, ex))
          (HeadlineV1.QShortDF Pt ℓ) 0 := by
    rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) sC ex
    · show IsQueryBoundP (query (spec := HeadlineV1.DFSpec Pt ℓ) (.inl n) >>=
        fun a => pure (a, (sC, ex))) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind
        ((isQueryBoundP_query_iff (HeadlineV1.QShortDF Pt ℓ) (.inl n) 0).2 fun h => nomatch h)
        fun _ _ => by simp
    · change IsQueryBoundP
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m none r) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact isQueryBoundP_runDFM
        (HeadlineV1.df_qbc_guardC
          (HeadlineV1.df_qbc_simSendC_short P hL qep _ HeadlineV1.hQ_QShortDF Q m none r))
        sC ex
    · change IsQueryBoundP
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m₀ (some m₁) r) (HeadlineV1.QShortDF Pt ℓ) 0
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact isQueryBoundP_runDFM
        (HeadlineV1.df_qbc_guardC
          (HeadlineV1.df_qbc_simSendC_short P hL qep _ HeadlineV1.hQ_QShortDF Q m₀ (some m₁) r))
        sC ex
    · change IsQueryBoundP
        (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
          qep B sC ex Q w true >>= fun ⟨rr, sC₁, ex₁⟩ =>
            (LibsignalSim.deliverForgeSemHook (PQC := PQC)).onDeliverPost Q none rr ex₁ >>=
              fun ex₂ => pure (rr, (sC₁, ex₂)))
        (HeadlineV1.QShortDF Pt ℓ) 0
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind
        (isQueryBoundP_semRecvHook_QShortDF P Dh encPt encT decT lam qep B sC ex Q w true)
        fun ⟨rr, sC₁, ex₁⟩ _ => by simp [LibsignalSim.deliverForgeSemHook]
    · exact isQueryBoundP_semRecvHook_QShortDF P Dh encPt encT decT lam qep B sC ex Q w false
    · change IsQueryBoundP
        (LibsignalSim.semCorrHook P Dh encT LibsignalSim.deliverForgeSemHook sC ex Q)
        (HeadlineV1.QShortDF Pt ℓ) 0
      rw [LibsignalSim.semCorrHook_deliverForge_eq]
      exact isQueryBoundP_runDFM
        (HeadlineV1.df_qbc_guardC
          (HeadlineV1.df_qbc_simCorrC P Dh encT HeadlineV1.hQ_QShortDF 0
            (fun _ h => nomatch h) Q))
        sC ex
  exact isQueryBoundP_simulateQ_stateT_inv
    (LibsignalSim.simDeliverForgeOracle P Dh encPt encT decT lam qep B)
    (p := fun _ => False) (fun _ _ => True) 0
    (fun _ _ _ h => False.elim h)
    (fun t _ ⟨sC, ex⟩ _ _ => ⟨hstep t sC ex, fun _ _ => trivial⟩)
    A 0 (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false A 0) (_, []) trivial

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_commit_vR {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    (ctx : SM.Engine.Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : SM.Engine.VP (Option Γ) T RSt SS RS) (h : DeliverForge.CKAStateShifted Γ T I) :
    ∀ res ∈ support (((DeliverForge.hooksCKAShifted cka prng fs l tStar).commit
        ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR := by
  intro ⟨ans, h'⟩ hmem new' hEq
  dsimp only at hEq
  subst hEq
  dsimp only [DeliverForge.hooksCKAShifted] at hmem
  by_cases h1 : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [h1, ↓reduceIte, DeliverForge.liftCShifted, StateT.run_bind, StateT.run_lift,
      mem_support_bind_iff] at hmem
    obtain ⟨rcvRes, _, hmem⟩ := hmem
    rcases rcvRes with _ | ⟨⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h, _⟩; cases h
    · dsimp only at hmem
      by_cases h2 : l + 2 ≤ new.tcur
      · simp only [h2, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          mem_support_bind_iff] at hmem
        obtain ⟨γ?, _, hmem⟩ := hmem
        rcases γ? with _ | γ'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
      · simp only [h2, ↓reduceIte] at hmem
        by_cases h3 : new.tcur + 1 ≤ l
        · simp only [h3, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            mem_support_bind_iff] at hmem
          obtain ⟨γ?, _, hmem⟩ := hmem
          rcases γ? with _ | γ'
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨h, _⟩; cases h
          · simp only [DeliverForge.setγPreShifted, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq, Option.some.injEq] at hmem
            rcases hmem with ⟨rfl, rfl⟩; rfl
        · simp only [h3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_vrInv_fromAEADPRG {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip l tStar : ℕ) :
    SM.Engine.HooksVRInv (SM.Engine.RSReach maxSkip)
      (DeliverForge.hooksCKAShifted cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    SM.Construction.hooksCKAShifted_startRecv_rs cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar
      (SM.Engine.RSReach.init ae G maxSkip) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [DeliverForge.hooksCKAShifted] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (SM.Engine.RSReach.receive ae G maxSkip _ hVR hrec.symm).2
  commit_vR := hooksCKAShifted_commit_vR cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l tStar

end EvalBridges

end CryptoVerification.E2E
