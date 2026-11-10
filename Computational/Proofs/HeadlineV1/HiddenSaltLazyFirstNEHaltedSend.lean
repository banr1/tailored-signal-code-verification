/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple3
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple4
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple5
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple6
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple8
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafTransmit

/-!
# Online-Halted `corr`, `inject`, and `transmit` Coupling

**Checked by Lean.** Unfolds `firstNEHalted'` and `cellSimRunTrackHalted` on non-`deliver` queries
and proves the halted per-query coupling steps for `corr`, `inject`, and `transmit`.
-/

@[expose] public section

set_option autoImplicit false

open scoped MeasureTheory
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted (firstNEHalted' splitSimImplHalted_non_deliver_run)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux (cellSimRunTrackHalted cellSimRunTrackHalted_corr_query_bind cellSimRunTrackHalted_inr_query_bind cellTrackLift_eq_runCellStep simImplCTrackHalted_chall simImplCTrackHalted_transmit sum_cellSimRunTrackHalted_le_of_doomed_or_eq)
open CryptoGames (Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (DeliverForgeM KemFailTrackState deliverForgeHook kemFailSendStepHalted kemFailSendStepPostCoin kemFailSimImpl kemFailSimImplHalted simSendCTrackHalted stepKemFailSend)
open CryptoGames.LibsignalSession (GhostState IdentityKey Params PublicKey)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8Comp Fig8St SimState inReceiveOnlyEpoch)
open CryptoGames.Ratchet.LibsignalSimC (Hook LibsignalToModularSchemeSimState probeHook)
open CryptoGames.SM (noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.SM.Thm1 (Mirror)
open CryptoVerification.LibsignalSession.HeadlineV1 (FirstNECellFamilyInvT_body FirstNECoupledInvD FirstNEInTransOriginInv SyncInv cellShift cellWinPred corrStepGhost corrStepStateC deliverForgeHook_lift_liftM_run drawRc drawRq firstNECoupledOriginInvT_corr_step firstNESimImpl firstNESimImpl_corr_accepted firstNESimImpl_corr_refused fullImplBaseDFCellPaper runCellStep runCellStep_bind runCellStep_liftC_sC_eq runCellStep_pure runCellStep_set runCellStep_simCorrC_accepted_cell runCellStep_simCorrC_refused simSendQFig simulateQ_fullImplBaseDFCellPaper_liftM_probComp simulateQ_simImplDF'Paper_liftM_probComp syncInv_corr_step updSimStateCSend)

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedSend

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)

/-! ## Halted send unfolding -/

private theorem kemFailSimImplHalted_inl' {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep n : ℕ) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inl n) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inl n) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_transmit' {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) =
      kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_chall' {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) =
      kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_inject' {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : Party × List (BitVec 8)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inl (.inr q))) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inl (.inr q))) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_corr' {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : Party) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inr q)) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inr q)) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

theorem simulateQ_firstNEHalted'_inl_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (n : unifSpec.Domain)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inl n) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inl n) >>= u)).run
      (sC, (g, fl, dead), tr) =
    ((OracleSpec.query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u₁ =>
      (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
        (sC, (g, fl, dead), tr)) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, firstNEHalted']
  rw [splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inl n) (fun _ _ h => nomatch h) sC g fl dead tr,
    kemFailSimImplHalted_inl']
  dsimp only [kemFailSimImpl, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_lift, bind_assoc, pure_bind]
  rfl

private theorem simulateQ_firstNEHalted'_corr_eq_firstNESimImpl' {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inr Q)) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)).run
      (sC, (g, fl, dead), tr) =
    ((firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr (.inr Q))).run
        (sC, (g, fl), tr) >>=
      fun x =>
        (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
          (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2)) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, firstNEHalted']
  rw [splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inr Q)) (fun _ _ h => nomatch h) sC g fl dead tr,
    kemFailSimImplHalted_corr', bind_assoc]
  dsimp only [firstNESimImpl]
  refine bind_congr fun x => ?_
  simp only [pure_bind]
  rfl

theorem simulateQ_firstNEHalted'_inject_eq_firstNESimImpl' {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)).run
      (sC, (g, fl, dead), tr) =
    ((firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inr (Q, w))))).run (sC, (g, fl), tr) >>=
      fun x =>
        (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
          (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2)) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, firstNEHalted']
  rw [splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inr (Q, w)))) (fun _ _ h => nomatch h) sC g fl dead tr,
    kemFailSimImplHalted_inject', bind_assoc]
  dsimp only [firstNESimImpl]
  refine bind_congr fun x => ?_
  simp only [pure_bind]
  rfl

theorem simulateQ_firstNEHalted'_transmit_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)).run
      (sC, (g, fl, dead), tr) =
    ((kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r).run
      (sC, (g, fl), tr) >>=
      fun x =>
        (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
          (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2)) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, firstNEHalted']
  rw [splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) (fun _ _ h => nomatch h) sC g fl dead tr,
    kemFailSimImplHalted_transmit', bind_assoc]
  refine bind_congr fun x => ?_
  simp only [pure_bind]
  rfl

theorem simulateQ_firstNEHalted'_chall_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)).run
      (sC, (g, fl, dead), tr) =
    ((kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r).run
      (sC, (g, fl), tr) >>=
      fun x =>
        (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
          (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2)) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, firstNEHalted']
  rw [splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) (fun _ _ h => nomatch h) sC g fl dead tr,
    kemFailSimImplHalted_chall', bind_assoc]
  refine bind_congr fun x => ?_
  simp only [pure_bind]
  rfl

theorem kemFailSendStepHalted_run_of_guard_fail {PQ Pt : Type}
    [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ' : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ') (chal : Option (Plain ℓ')) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ')
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ') (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = true) :
    (kemFailSendStepHalted P K ℓ' Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, gh, tr) =
      pure (none, (sC, gh, tr)) := by
  unfold kemFailSendStepHalted
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  rcases hfail with hg1 | hep | ⟨s₁, hep, hg3⟩
  · simp [hg1, StateT.run_pure]
  · cases (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) <;>
      simp [hep, StateT.run_pure]
  · cases (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) <;>
      simp [hep, hg3, StateT.run_pure]

theorem kemFailSendStepHalted_run_of_guards_pass {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (tr : KemFailTrackState P.C.F)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    (kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, (g, fl), tr) =
      (drawRq r >>= fun rq =>
        let tr' := stepKemFailSend P.C.F K tr Q rq
        if tr'.cand.isSome then
          pure (none, (sC, (g, fl), { tr with cand := tr'.cand }))
        else
          drawRc r >>= fun rc =>
            match CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
            | none => pure (none, (sC, (g, fl), { tr with cand := tr'.cand }))
            | some (pq', pub) =>
              ((probeHook fig (qep + 1)).lift (simSendQFig Q pub m₀ chal rc)).run (g, fl) >>=
                fun p =>
                  match p.1 with
                  | none => pure (none, (sC, p.2, { tr with cand := tr'.cand }))
                  | some c =>
                    pure (some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                      (updSimStateCSend fig Q m₀ chal.isSome s₁ pq' pn c sC, p.2, tr'))) := by
  intro fig pn
  unfold kemFailSendStepHalted kemFailSendStepPostCoin
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3]
  cases r with
  | none =>
    simp only [drawRq, drawRc, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      pure_bind, bind_assoc]
    refine bind_congr fun rq => ?_
    cases (stepKemFailSend P.C.F K tr Q rq).cand.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [pn]
      cases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
      | none => simp [StateT.run_set]
      | some p_pub =>
        rcases p_pub with ⟨pq', pub⟩
        simp only [simSendQFig, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
          bind_assoc]
        refine bind_congr fun p => ?_
        rcases p with ⟨res, gh'⟩
        cases res
        · simp [StateT.run_set]
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            updSimStateCSend, fig]
          cases (sC.kept Q).full <;> rfl
    · simp [StateT.run_set]
  | some rq =>
    simp only [drawRq, drawRc,
      map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc]
    cases (stepKemFailSend P.C.F K tr Q rq).cand.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        MonadLiftT.monadLift, pure_bind, bind_assoc]
      refine bind_congr fun c_cka => ?_
      dsimp only [pn]
      cases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
      | none => simp [StateT.run_set]
      | some p_pub =>
        rcases p_pub with ⟨pq', pub⟩
        simp only [simSendQFig, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
          bind_assoc]
        refine bind_congr fun p => ?_
        rcases p with ⟨res, gh'⟩
        cases res
        · simp [StateT.run_set]
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            updSimStateCSend, fig]
          cases (sC.kept Q).full <;> rfl
    · simp [StateT.run_set]

private theorem simSendCTrackHalted_run_of_guard_fail {M : Type → Type} [Monad M] [LawfulMonad M]
    {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (H : Hook Pt ℓ M)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = true) :
    (simSendCTrackHalted P K qep fig H Q m₀ chal r).run (sC, tr) = pure (none, (sC, tr)) := by
  unfold simSendCTrackHalted
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  rcases hfail with hg1 | hep | ⟨s₁, hep, hg3⟩
  · simp [hg1, StateT.run_pure]
  · cases (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) <;>
      simp [hep, StateT.run_pure]
  · cases (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) <;>
      simp [hep, hg3, StateT.run_pure]

theorem cellSimRunTrackHalted_transmit_of_guard_fail {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        ((none : Option (Plain ℓ)).isSome && !s₁.safeCh 3 Q) = true) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
      sC tr sent m' s_cell =
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (u none) sC tr sent m' s_cell := by
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_transmit,
    simSendCTrackHalted_run_of_guard_fail P K qep _ _ Q m₀ none r sC tr hfail]
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]

theorem cellSimRunTrackHalted_chall_of_guard_fail {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        ((some m₁).isSome && !s₁.safeCh 3 Q) = true) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)
      sC tr sent m' s_cell =
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (u none) sC tr sent m' s_cell := by
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_chall,
    simSendCTrackHalted_run_of_guard_fail P K qep _ _ Q m₀ (some m₁) r sC tr hfail]
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]

private theorem cellEngine_deliverForgeHook_liftM_bind {Pt γ δ : Type} {ℓ : ℕ}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep t : ℕ) (tL : Option ℕ)
    (m : ProbComp γ) (k : γ → DeliverForgeM Pt ℓ δ)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Config.auth t))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((((deliverForgeHook Pt ℓ).lift (liftM m : Fig8Comp Pt ℓ γ)) >>= k).run sent)).run
        m')).run s_cell =
    (m >>= fun x =>
      (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
          (CryptoGames.SM.Config.auth t))
        ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
          ((k x).run sent)).run m')).run s_cell) := by
  rw [StateT.run_bind, deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFCellPaper_liftM_probComp]

private theorem cellEngine_deliverForgeHook_pure_bind {Pt γ δ : Type} {ℓ : ℕ}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep t : ℕ) (tL : Option ℕ)
    (a : γ) (k : γ → DeliverForgeM Pt ℓ δ)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Config.auth t))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((((deliverForgeHook Pt ℓ).lift (pure a : Fig8Comp Pt ℓ γ)) >>= k).run sent)).run
        m')).run s_cell =
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Config.auth t))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((k a).run sent)).run m')).run s_cell := by
  have hp : (pure a : Fig8Comp Pt ℓ γ) = liftM (pure a : ProbComp γ) := rfl
  rw [hp, cellEngine_deliverForgeHook_liftM_bind, pure_bind]

private theorem cellEngine_simSendCTrackHalted_of_guards_pass {PQ Pt : Type} {ℓ : ℕ}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false) :
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Config.auth t))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        (((simSendCTrackHalted P K qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r).run
          (sC, tr)).run sent)).run m')).run s_cell =
    (drawRq r >>= fun rq =>
      let tr' := stepKemFailSend P.C.F K tr Q rq
      if tr'.cand.isSome then
        pure ((((none, (sC, { tr with cand := tr'.cand })), sent), m'), s_cell)
      else
        drawRc r >>= fun rc =>
          match CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
          | none => pure ((((none, (sC, { tr with cand := tr'.cand })), sent), m'), s_cell)
          | some (pq', pub) =>
            runCellStep fig qep t tL
              (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ chal rc))
              sC sent m' s_cell >>= fun z =>
              match z.1.1.1.1 with
              | none =>
                pure ((((none, (sC, { tr with cand := tr'.cand })), z.1.1.2), z.1.2), z.2)
              | some c =>
                pure ((((some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                  (updSimStateCSend fig Q m₀ chal.isSome s₁ pq' pn c sC, tr')),
                  z.1.1.2), z.1.2), z.2)) := by
  intro pn
  have hlift : ∀ {β : Type} (m : DeliverForgeM Pt ℓ β)
      (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F),
      (StateT.lift m : StateT _ (DeliverForgeM Pt ℓ) β).run st =
        (m >>= fun a => pure (a, st)) := fun _ _ => rfl
  have hbind_st : ∀ {α' β' : Type}
      (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (DeliverForgeM Pt ℓ) α')
      (f : α' → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (DeliverForgeM Pt ℓ) β')
      (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F),
      (m >>= f).run st = (m.run st >>= fun p => (f p.1).run p.2) :=
    fun _ _ _ => StateT.run_bind _ _ _
  have hpost :
      ∀ (rq : BitVec 512) (rc : Option (BitVec 256)),
        let tr' := stepKemFailSend P.C.F K tr Q rq
        (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
            (CryptoGames.SM.Config.auth t))
          ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
            (((match CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
              | none =>
                set (sC, { tr with cand := tr'.cand }) >>= fun _ => pure none
              | some (pq', pub) =>
                StateT.lift ((deliverForgeHook Pt ℓ).lift (simSendQFig Q pub m₀ chal rc)) >>=
                  fun res =>
                    match res with
                    | none => set (sC, { tr with cand := tr'.cand }) >>= fun _ => pure none
                    | some c =>
                      let w := CryptoGames.Ratchet.LibsignalSim.toWire c
                      let rec' : CryptoGames.SM.Record (Plain ℓ) (List (BitVec 8)) :=
                        ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                      let base' : SimState PQ Pt ℓ :=
                        { sC.base with
                          mir := s₁.record 3 Q () rec' chal.isSome
                          pq := Function.update sC.base.pq Q pq'
                          pn := Function.update sC.base.pn Q pn
                          honest := (w, c) :: sC.base.honest }
                      let sent' := match (sC.kept Q).full, base'.honest.head? with
                        | some st, some (_, c₀) =>
                          if st.id.sendsIn (st.tcur + 1) then sC.sent
                          else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
                        | _, _ => sC.sent
                      set ({ sC with
                        base := base'
                        kept := Function.update sC.kept Q (CryptoGames.Ratchet.LibsignalSimC.Kept.send (fig := fig) (sC.kept Q))
                        sent := sent' }, tr') >>= fun _ => pure (some w)).run
              (sC, tr)).run sent)).run m')).run s_cell =
        match CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
        | none => pure ((((none, (sC, { tr with cand := tr'.cand })), sent), m'), s_cell)
        | some (pq', pub) =>
          runCellStep fig qep t tL
            (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ chal rc))
            sC sent m' s_cell >>= fun z =>
            match z.1.1.1.1 with
            | none =>
              pure ((((none, (sC, { tr with cand := tr'.cand })), z.1.1.2), z.1.2), z.2)
            | some c =>
              pure ((((some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                (updSimStateCSend fig Q m₀ chal.isSome s₁ pq' pn c sC, tr')),
                z.1.1.2), z.1.2), z.2) := by
    intro rq rc tr'
    cases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      dsimp only
      let mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ)
          (Option (List (BitVec 8))) :=
        CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ chal rc) >>= fun res =>
          match res with
          | none => pure none
          | some c =>
            set (updSimStateCSend fig Q m₀ chal.isSome s₁ pq' pn c sC) >>=
              fun _ => pure (some (CryptoGames.Ratchet.LibsignalSim.toWire c))
      have hmDF_eq :
          ((StateT.lift ((deliverForgeHook Pt ℓ).lift (simSendQFig Q pub m₀ chal rc)) >>=
            fun res =>
              match res with
              | none => set (sC, { tr with cand := tr'.cand }) >>= fun _ => pure none
              | some c =>
                let w := CryptoGames.Ratchet.LibsignalSim.toWire c
                let rec' : CryptoGames.SM.Record (Plain ℓ) (List (BitVec 8)) :=
                  ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                let base' : SimState PQ Pt ℓ :=
                  { sC.base with
                    mir := s₁.record 3 Q () rec' chal.isSome
                    pq := Function.update sC.base.pq Q pq'
                    pn := Function.update sC.base.pn Q pn
                    honest := (w, c) :: sC.base.honest }
                let sent' := match (sC.kept Q).full, base'.honest.head? with
                  | some st, some (_, c₀) =>
                    if st.id.sendsIn (st.tcur + 1) then sC.sent
                    else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
                  | _, _ => sC.sent
                set ({ sC with
                  base := base'
                  kept := Function.update sC.kept Q (CryptoGames.Ratchet.LibsignalSimC.Kept.send (fig := fig) (sC.kept Q))
                  sent := sent' }, tr') >>= fun _ => pure (some w)).run (sC, tr)) =
          (mDF.run sC >>= fun x =>
            pure (x.1, (x.2, if x.1.isSome then tr' else { tr with cand := tr'.cand }))) := by
        simp only [mDF, CryptoGames.Ratchet.LibsignalSimC.liftC, StateT.run_bind, hlift, StateT.run_lift,
          bind_assoc, pure_bind]
        refine bind_congr fun res => ?_
        cases res with
        | none =>
          simp [StateT.run_set, StateT.run_pure]
        | some c =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            Option.isSome, updSimStateCSend]
          cases (sC.kept Q).full <;> rfl
      rw [hmDF_eq,
        cellTrackLift_eq_runCellStep fig qep t tL mDF
          (fun o => if o.isSome then tr' else { tr with cand := tr'.cand }) sC sent m' s_cell]
      simp only [mDF, runCellStep_bind, runCellStep_liftC_sC_eq, bind_assoc]
      refine bind_congr fun z => ?_
      cases z.1.1.1.1 with
      | none =>
        simp [runCellStep_pure]
      | some c =>
        simp only [runCellStep_bind, runCellStep_set, runCellStep_pure, pure_bind,
          Option.isSome]
        rfl
  unfold simSendCTrackHalted
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3]
  cases r with
  | none =>
    simp only [drawRq, drawRc, hbind_st, hlift, bind_assoc, pure_bind]
    rw [cellEngine_deliverForgeHook_liftM_bind]
    refine bind_congr fun rq => ?_
    cases (stepKemFailSend P.C.F K tr Q rq).cand.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, hbind_st, hlift, bind_assoc, pure_bind]
      rw [cellEngine_deliverForgeHook_pure_bind]
      exact hpost rq none
    · simp [StateT.run_set, StateT.run_pure, simulateQ_pure]
  | some rq =>
    simp only [drawRq, drawRc, hbind_st, hlift, bind_assoc, pure_bind]
    rw [cellEngine_deliverForgeHook_pure_bind]
    cases (stepKemFailSend P.C.F K tr Q rq).cand.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, hbind_st, hlift, bind_assoc]
      have hmap :
          (some <$> (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))) =
            liftM (some <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))) := by
        simp only [map_eq_bind_pure_comp, Function.comp_def, liftM_bind, liftM_pure]
      rw [hmap, cellEngine_deliverForgeHook_liftM_bind]
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      refine bind_congr fun c_cka => ?_
      exact hpost rq (some c_cka)
    · simp [StateT.run_set, StateT.run_pure, simulateQ_pure]

theorem cellSimRunTrackHalted_transmit_of_guards_pass {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : ((none : Option (Plain ℓ)).isSome && !s₁.safeCh 3 Q) = false) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
      sC tr sent m' s_cell =
    (drawRq r >>= fun rq =>
      let tr' := stepKemFailSend P.C.F K tr Q rq
      if tr'.cand.isSome then
        cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (u none) sC { tr with cand := tr'.cand } sent m' s_cell
      else
        match CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
        | none =>
          drawRc r >>= fun _rc =>
            cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
              (u none) sC { tr with cand := tr'.cand } sent m' s_cell
        | some (pq', pub) =>
          (drawRc r >>= fun _rc =>
            runCellStep fig qep t tL
              (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ none _rc))
              sC sent m' s_cell >>= fun z =>
              match z.1.1.1.1 with
              | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
              | some c =>
                pure ((((some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                  updSimStateCSend fig Q m₀ false s₁ pq' pn c sC),
                  z.1.1.2), z.1.2), z.2)) >>=
          fun w =>
            cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
              (u w.1.1.1.1) w.1.1.1.2
              (if w.1.1.1.1.isSome then tr' else { tr with cand := tr'.cand })
              w.1.1.2 w.1.2 w.2) := by
  intro fig pn
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_transmit,
    cellEngine_simSendCTrackHalted_of_guards_pass P K qep t tL fig Q m₀ none r s₁ sC tr sent m'
      s_cell hg1 hep hg3, bind_assoc]
  refine bind_congr fun rq => ?_
  dsimp only
  cases (stepKemFailSend P.C.F K tr Q rq).cand.isSome
  · simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [pn]
    cases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none =>
      simp only [bind_assoc, pure_bind]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      simp only [bind_assoc]
      refine bind_congr fun rc => bind_congr fun z => ?_
      cases z.1.1.1.1 <;> simp [pure_bind, Option.isSome]
  · simp [pure_bind]

theorem cellSimRunTrackHalted_chall_of_guards_pass {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : ((some m₁).isSome && !s₁.safeCh 3 Q) = false) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)
      sC tr sent m' s_cell =
    (drawRq r >>= fun rq =>
      let tr' := stepKemFailSend P.C.F K tr Q rq
      if tr'.cand.isSome then
        cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (u none) sC { tr with cand := tr'.cand } sent m' s_cell
      else
        match CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
        | none =>
          drawRc r >>= fun _rc =>
            cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
              (u none) sC { tr with cand := tr'.cand } sent m' s_cell
        | some (pq', pub) =>
          (drawRc r >>= fun _rc =>
            runCellStep fig qep t tL
              (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ (some m₁) _rc))
              sC sent m' s_cell >>= fun z =>
              match z.1.1.1.1 with
              | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
              | some c =>
                pure ((((some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                  updSimStateCSend fig Q m₀ true s₁ pq' pn c sC),
                  z.1.1.2), z.1.2), z.2)) >>=
          fun w =>
            cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
              (u w.1.1.1.1) w.1.1.1.2
              (if w.1.1.1.1.isSome then tr' else { tr with cand := tr'.cand })
              w.1.1.2 w.1.2 w.2) := by
  intro fig pn
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_chall,
    cellEngine_simSendCTrackHalted_of_guards_pass P K qep t tL fig Q m₀ (some m₁) r s₁ sC tr sent
      m' s_cell hg1 hep hg3, bind_assoc]
  refine bind_congr fun rq => ?_
  dsimp only
  cases (stepKemFailSend P.C.F K tr Q rq).cand.isSome
  · simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [pn]
    cases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none =>
      simp only [bind_assoc, pure_bind]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      simp only [bind_assoc]
      refine bind_congr fun rc => bind_congr fun z => ?_
      cases z.1.1.1.1 <;> simp [pure_bind, Option.isSome]
  · simp [pure_bind]

/-! ## Per-oracle coupling steps -/

theorem firstNECoupledInvD_corr_halted_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inr Q)) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inr Q)))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ tr₁ sent₁
            m₁' (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hbody with ⟨hcol, hrel_all⟩
  rw [simulateQ_firstNEHalted'_corr_eq_firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep
    q Q u sC g false false tr]
  by_cases href : sC.base.stopped = true ∨
      (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
        !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · rw [firstNESimImpl_corr_refused P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q sC g false tr
      href, pure_bind]
    refine le_trans
      (hih none sC g false false tr sent m' s_cell
        (Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩))) ?_
    refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
      _ (u none) sC sC tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
    rw [cellSimRunTrackHalted_corr_query_bind,
      runCellStep_simCorrC_refused P encT Dh _ qep t tL Q sC sent m' (s_cell t tL) href,
      pure_bind]
  · rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at href
    rcases href with ⟨hstop, href'⟩
    rcases hsync.1 hstop with ⟨s_R, hmeta⟩
    have htrans_pos : sC.base.mir.trans.map CryptoGames.SM.Record.pos = g.trans.map CryptoGames.SM.Record.pos := by
      have h := congrArg (List.map Prod.fst) hmeta.htrans_fig8
      simpa [List.map_map, Function.comp_def] using h
    obtain ⟨hallow_g, hallow_m⟩ :=
      hsync.2.1.corr_sync hmeta.hchall_fig8.symm hmeta.hcomp_fig8.symm htrans_pos href'
    have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
    rw [firstNESimImpl_corr_accepted P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q sC g false tr
      hstop href' hwin_g hallow_g, pure_bind]
    let s_cell₁ :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL => if (s_cell t tL).win then s_cell t tL
        else CryptoGames.SM.Construction.DeliverForge.afterCorrShifted (cellShift tL t) (s_cell t tL) Q
    have hsnaps_sub : ∀ snap ∈ sC.snaps,
        snap ∈ (corrStepStateC P encT Dh sC Q (g.st Q)).snaps :=
      fun _ h => List.mem_cons_of_mem _ h
    have hcoupled₁ := firstNECoupledOriginInvT_corr_step qep Q
      (Or.inr ⟨rfl, hcol, hrel_all, horig⟩) hsnaps_sub hallow_g
    have hinvD₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
        (corrStepStateC P encT Dh sC Q (g.st Q)) sent (m'.afterCorr Q) (g.afterCorr Q) s_cell₁ := by
      rcases hcoupled₁ with hwin | ⟨_, hcol₁, hrel₁, horig₁⟩
      · exact Or.inl hwin
      · refine Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol₁, hrel₁⟩, horig₁, ?_⟩)
        have hsync₁ := syncInv_corr_step P Dh encPt encT idOf lam qep Q hsync
          (hrel_all 0 ht0).1.epoch_eq hstop hallow_g
        have hs0 : s_cell₁ 0 none =
            CryptoGames.SM.Construction.DeliverForge.afterCorrShifted (cellShift none 0) (s_cell 0 none) Q := by
          dsimp only [s_cell₁]
          simp [(hrel_all 0 ht0).1.win_df_false]
        rwa [hs0]
    refine le_trans
      (hih (some (corrStepGhost P encT Dh sC.base Q (g.st Q)))
        (corrStepStateC P encT Dh sC Q (g.st Q)) (g.afterCorr Q) false false tr sent
        (m'.afterCorr Q) s_cell₁ hinvD₁) ?_
    refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
      _ (u (some (corrStepGhost P encT Dh sC.base Q (g.st Q))))
      sC (corrStepStateC P encT Dh sC Q (g.st Q)) tr tr (g.afterCorr Q) sent sent
      m' (m'.afterCorr Q) s_cell s_cell₁ fun t ht tL htL => ?_
    rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
    · left
      dsimp only [s_cell₁]
      simp only [hdoomed.2.2.2, ↓reduceIte]
      exact hdoomed.of_corrs_sub (fun _ h => List.mem_cons_of_mem _ h)
    · right
      dsimp only [s_cell₁]
      simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
      rw [cellSimRunTrackHalted_corr_query_bind,
        runCellStep_simCorrC_accepted_cell P encT Dh _ qep t tL Q sC sent m' (s_cell t tL) g
          hstop href' hallow_m hrel_sh.win_df_false (hrel_sh.corrAllowedPaper_df Q)
          (congrFun hrel_sh.st_eq Q),
        pure_bind]

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedSend
