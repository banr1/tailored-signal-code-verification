/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple3
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple4
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple5
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple6
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple8
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliver
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliverProbe

/-!
# Online-Halted Cell Simulation and `deliver` Combinators

**Checked by Lean.** Unfolds `DeliverForge.forgeGuessedAdvantageCellPaper` on
`simDeliverForgeTrackHalted` into `cellSimRunTrackHalted` and proves the lockstep and winning-cell
`deliver` combinators for `firstNEHalted'`.
-/

@[expose] public section

set_option autoImplicit false

open scoped MeasureTheory
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted (firstNEHalted' splitSimImplHalted)
open CryptoGames (FSAEADScheme Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (DeliverForgeM KemFailTrackState deliverForgeHook initKemFailTrack simDeliverForgeTrackHalted simImplCTrackHalted simRecvStepC simRunCTrackHaltedWith simSendCTrackHalted stepKemFailDeliver)
open CryptoGames.LibsignalSession (GhostState IdentityKey Params PublicKey ShaCompress)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8Comp Fig8St)
open CryptoGames.Ratchet.LibsignalSimC (Hook LibsignalToModularSchemeSimState initSimC probeHook)
open CryptoGames.SM (RecvResult)
open CryptoGames.SM.Construction (Header)
open CryptoGames.SM.Thm1 (Mirror)
open CryptoVerification.LibsignalSession.HeadlineV1 (CellK4Doomed EvictedSpurHistSimInvLazy FirstNECoupledInvD cellWinPred cellWinPred_with_b deliverForgeHook_lift_liftM_run evalDist_simulateQ_fullImplBaseDFCellPaper_cellWinPred_eq_one forgeGuessedAdvantageCellPaper forgeGuessedAdvantageCellPaper_eq_runBaseDFCellPaper fullImplBaseDFCellPaper runBaseDFCellPaper runCellStep simRecvStepC_of_probeHook_run simulateQ_fullImplBaseDFCellPaper_liftM_probComp simulateQ_fullImplBaseDFCellPaper_simImplDF'Paper_with_b simulateQ_fullImplBaseDFCellPaper_state_eq_of_win_true simulateQ_simImplDF'Paper_liftM_probComp withB)

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)

/-! ## Cell simulation runner -/

abbrev cellSimRunTrackHalted {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp ((((α × (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)) ×
      List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme
      tL t (CryptoGames.SM.Config.auth t))
    ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      (((simulateQ (simImplCTrackHalted P K encT decT qep fig fs
          (deliverForgeHook Pt ℓ) Dh) oa).run (sC, tr)).run sent)).run m')).run s

theorem runBaseDFCellPaper_challSimDF'Paper_simDeliverForgeTrackHalted_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (tL : Option ℕ) (t : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (f : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp Bool)
    (A : CryptoGames.LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    𝒟[runBaseDFCellPaper fig (qep + 1) sameHdr tL t cfg false
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) >>=
      fun z => f z.2] =
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let tr₀ : KemFailTrackState P.C.F := initKemFailTrack P.C.F pqrKey
      let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
      let z ←
        (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) sameHdr tL t cfg)
          ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
            (((simulateQ (simImplCTrackHalted P K encT decT qep fig fs
                (deliverForgeHook Pt ℓ) Dh) A).run (sC₀, tr₀)).run [])).run m'₀)).run
          (CryptoGames.SM.initState fig k false)
      f z.2] := by
  intro fig fs
  unfold runBaseDFCellPaper CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper simDeliverForgeTrackHalted
    simRunCTrackHaltedWith
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap (γ := Bool)
    ($ᵗ Bool : ProbComp Bool) ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _)]
  refine congrArg evalDist (congrArg (($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= ·)
    (funext fun k => ?_))
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    simulateQ_bind, StateT.run_bind]
  rw [simulateQ_fullImplBaseDFCellPaper_liftM_probComp]
  simp only [bind_assoc, pure_bind]
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  rw [deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFCellPaper_liftM_probComp]
  refine congrArg (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= ·) (funext fun pqrKey => ?_)
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  rfl

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeTrackHalted_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeGuessedAdvantageCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
      (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) =
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let tr₀ : KemFailTrackState P.C.F := initKemFailTrack P.C.F pqrKey
      let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
      let z ←
        cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL A
          sC₀ tr₀ [] m'₀ (CryptoGames.SM.initState fig k b)
      return cellWinPred tL t z.2] {true} := by
  intro fig
  rw [forgeGuessedAdvantageCellPaper_eq_runBaseDFCellPaper]
  rw [runBaseDFCellPaper_challSimDF'Paper_simDeliverForgeTrackHalted_eq P K ℓ Dh encPt encT decT
    idOf lam qep CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t (CryptoGames.SM.Config.auth t)
    (fun s => pure (cellWinPred tL t s))]
  refine congrArg (fun m : ProbComp Bool => 𝒟[m] {true}) ?_
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  refine congrArg (($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= ·) (funext fun k => ?_)
  refine congrArg (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= ·) (funext fun pqrKey => ?_)
  dsimp only [cellSimRunTrackHalted]
  have hinit : CryptoGames.SM.initState fig k b = withB b (CryptoGames.SM.initState fig k false) := rfl
  rw [hinit, simulateQ_fullImplBaseDFCellPaper_simImplDF'Paper_with_b]
  simp only [bind_assoc, pure_bind, cellWinPred_with_b]
  rfl

/-! ## Query-bind lemmas -/

theorem evalDist_cellSimRunTrackHalted_cellWinPred_eq_zero_of_doomed {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {g s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hd : CellK4Doomed tL t g s) :
    𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa sC tr sent m' s >>=
      fun z => pure (cellWinPred tL t z.2)] {true} = 0 := by
  have hcongr :
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa sC tr sent m' s >>=
        fun z => pure (cellWinPred tL t z.2)] =
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa sC tr sent m' s >>=
        fun _ => (pure false : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    have hz_eq := simulateQ_fullImplBaseDFCellPaper_state_eq_of_win_true
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t _
      s z hz hd.2.2.2
    rw [hz_eq, hd.cellWinPred_eq_false]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

theorem sum_cellSimRunTrackHalted_le_of_doomed_or_eq {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa_pre oa_post : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (tr tr₁ : KemFailTrackState P.C.F)
    (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell s_cell₁ :
      ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hcells : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g₁ (s_cell₁ t tL) ∨
      cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC tr sent m'
        (s_cell t tL) =
      cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa_post sC₁ tr₁ sent₁ m₁'
        (s_cell₁ t tL)) :
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa_post sC₁ tr₁ sent₁ m₁'
          (s_cell₁ t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC tr sent m'
          (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
  rcases hcells t ht tL htL with hdoomed | heq
  · rw [evalDist_cellSimRunTrackHalted_cellWinPred_eq_zero_of_doomed P K ℓ Dh encPt encT decT idOf
      lam qep t tL oa_post sC₁ tr₁ sent₁ m₁' hdoomed]
    exact zero_le
  · rw [heq]

theorem evalDist_le_sum_cellSimRunTrackHalted_of_cell_step_win {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (lhs : ProbComp Bool)
    (oa_pre oa_post : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (tr tr₁ : KemFailTrackState P.C.F)
    (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (t₀ : ℕ) (ht₀ : t₀ ∈ Finset.range ((qep + 1) + 2))
    (tL₀ : Option ℕ) (htL₀ : tL₀ ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t₀)
    (s_win : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstep_eq :
      cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t₀ tL₀ oa_pre sC tr sent m'
        (s_cell t₀ tL₀) =
      cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t₀ tL₀ oa_post sC₁ tr₁ sent₁ m₁'
        s_win)
    (hwin : cellWinPred tL₀ t₀ s_win = true) :
    𝒟[lhs] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC tr sent m'
          (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  have hone :
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t₀ tL₀ oa_pre sC tr sent m'
          (s_cell t₀ tL₀) >>=
        fun z => pure (cellWinPred tL₀ t₀ z.2)] {true} = 1 := by
    rw [hstep_eq]
    exact evalDist_simulateQ_fullImplBaseDFCellPaper_cellWinPred_eq_one
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep CryptoGames.SM.Construction.DeliverForge.sameHdrScheme
      tL₀ t₀ _ s_win hwin
  refine le_trans MeasureTheory.prob_le_one ?_
  rw [← hone]
  exact le_trans
    (Finset.single_le_sum (f := fun tL =>
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t₀ tL oa_pre sC tr sent m'
          (s_cell t₀ tL) >>=
        fun z => pure (cellWinPred tL t₀ z.2)] {true})
      (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) htL₀)
    (Finset.single_le_sum (f := fun t => ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC tr sent m'
          (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true})
      (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) ht₀)

theorem cellSimRunTrackHalted_bind {α β : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (ob : α → OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL (oa >>= ob) sC tr sent m' s =
      (cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa sC tr sent m' s >>=
        fun z => cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (ob z.1.1.1.1) z.1.1.1.2.1 z.1.1.1.2.2 z.1.1.2 z.1.2 z.2) := by
  simp only [cellSimRunTrackHalted, simulateQ_bind, StateT.run_bind]

theorem simImplCTrackHalted_inl {M : Type → Type} [Monad M]
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt) (n : unifSpec.Domain) :
    simImplCTrackHalted P K encT decT qep fig fs H Dh (.inl n) =
      StateT.lift (H.lift (liftM (OracleSpec.query (spec := unifSpec) n : ProbComp _) :
        Fig8Comp Pt ℓ _)) :=
  rfl

theorem simImplCTrackHalted_transmit {M : Type → Type} [Monad M]
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512)) :
    simImplCTrackHalted P K encT decT qep fig fs H Dh (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) =
      simSendCTrackHalted P K qep fig H Q m₀ none r := by
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]

theorem simImplCTrackHalted_chall {M : Type → Type} [Monad M]
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512)) :
    simImplCTrackHalted P K encT decT qep fig fs H Dh
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) =
      simSendCTrackHalted P K qep fig H Q m₀ (some m₁) r := by
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]

/-- Deterministic `KemFailTrackState` update on `deliver (Q, w)` matching both `firstNEHalted'`
and `simImplCTrackHalted`. -/
def updDeliverTr {PQ Pt : Type} {ℓ : ℕ} {F : ShaCompress}
    (K : MlKem) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (tr : KemFailTrackState F) (Q : Party) (w : List (BitVec 8))
    (res : Option (RecvResult (Plain ℓ))) : KemFailTrackState F :=
  match res, sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other) with
  | some (.accepted _ _ _), some j => stepKemFailDeliver F K tr Q j
  | _, _ => tr

theorem simImplCTrackHalted_deliver_run {M : Type → Type} [Monad M] [LawfulMonad M]
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    (simImplCTrackHalted P K encT decT qep fig fs H Dh
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr) =
      ((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs H Q w true)).run sC >>=
        fun x => pure (x.1, (x.2, updDeliverTr K sC tr Q w x.1))) := by
  have hlift : ∀ {α : Type} (m : M α)
      (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F),
      (StateT.lift m : StateT _ M α).run st = (m >>= fun a => pure (a, st)) := fun _ _ => rfl
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, hlift,
    bind_assoc, pure_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨res, sC'⟩
  dsimp only [updDeliverTr]
  cases res with
  | none => simp only [StateT.run_pure]
  | some rr =>
    cases rr <;>
      cases sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other) <;>
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.run_bind, StateT.run_pure]
    unfold StateT.modifyGet StateT.run
    simp only [pure_bind]

theorem simImplCTrackHalted_inject_run {M : Type → Type} [Monad M] [LawfulMonad M]
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    (simImplCTrackHalted P K encT decT qep fig fs H Dh
      (.inr (.inl (.inr (Q, w))))).run (sC, tr) =
      ((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs H Q w false)).run sC >>=
        fun x => pure (x.1, (x.2, tr))) := by
  have hlift : ∀ {α : Type} (m : M α)
      (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F),
      (StateT.lift m : StateT _ M α).run st = (m >>= fun a => pure (a, st)) := fun _ _ => rfl
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, hlift,
    bind_assoc, pure_bind]

theorem simImplCTrackHalted_corr_run {M : Type → Type} [Monad M] [LawfulMonad M]
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    (simImplCTrackHalted P K encT decT qep fig fs H Dh (.inr (.inr Q))).run (sC, tr) =
      ((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simCorrC P encT H Dh Q)).run sC >>=
        fun x => pure (x.1, (x.2, tr))) := by
  have hlift : ∀ {α : Type} (m : M α)
      (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F),
      (StateT.lift m : StateT _ M α).run st = (m >>= fun a => pure (a, st)) := fun _ _ => rfl
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, hlift,
    bind_assoc, pure_bind]

theorem cellSimRunTrackHalted_inl_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (n : unifSpec.Domain)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inl n) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inl n) >>= u) sC tr sent m' s =
    ((OracleSpec.query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
      fun u₁ => cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL (u u₁)
        sC tr sent m' s) := by
  have hlift : ∀ {β : Type} (m : DeliverForgeM Pt ℓ β),
      (StateT.lift m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (DeliverForgeM Pt ℓ) β).run (sC, tr) = (m >>= fun a => pure (a, (sC, tr))) := fun _ => rfl
  unfold cellSimRunTrackHalted
  dsimp only
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift]
  rw [simImplCTrackHalted_inl, StateT.run_bind, hlift, StateT.run_bind]
  change (simulateQ (fullImplBaseDFCellPaper _ _ _ _ _ _)
    ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((((deliverForgeHook Pt ℓ).lift
          (liftM (OracleSpec.query (spec := unifSpec) n : ProbComp _) :
            Fig8Comp Pt ℓ _)).run sent >>=
        fun z => pure ((z.1, (sC, tr)), z.2)) >>=
      fun z => (((simulateQ (simImplCTrackHalted P K encT decT qep _ _
        (deliverForgeHook Pt ℓ) Dh) (u z.1.1)).run z.1.2).run z.2))).run m')).run s = _
  rw [deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFCellPaper_liftM_probComp]
  rfl

theorem cellSimRunTrackHalted_inr_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (q_game : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr q_game) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr q_game) >>= u)
      sC tr sent m' s =
    (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
     let fs := lFS P.C P.codec ℓ encT idOf 25000
     (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
         (CryptoGames.SM.Config.auth t))
       ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
         (((simImplCTrackHalted P K encT decT qep fig fs (deliverForgeHook Pt ℓ) Dh
           (.inr q_game)).run (sC, tr)).run sent)).run m')).run s >>=
     fun z =>
       cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2.1 z.1.1.1.2.2 z.1.1.2 z.1.2 z.2) := by
  rw [cellSimRunTrackHalted_bind]
  congr 1
  unfold cellSimRunTrackHalted
  simp only [simulateQ_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
    OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
    PFunctor.Obj.mk, id]
  simp only [id_map]

theorem cellTrackLift_eq_runCellStep
    {PQ Pt β : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {F : ShaCompress}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qep t : ℕ) (tL : Option ℕ)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) β)
    (trF : β → KemFailTrackState F)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Config.auth t))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        (((mDF.run sC >>= fun x => pure (x.1, (x.2, trF x.1))).run sent))).run m')).run s_cell =
    (runCellStep fig qep t tL mDF sC sent m' s_cell >>=
      fun z => pure ((((z.1.1.1.1, (z.1.1.1.2, trF z.1.1.1.1)), z.1.1.2), z.1.2), z.2)) := by
  simp only [runCellStep, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]

theorem cellSimRunTrackHalted_corr_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inr Q)) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inr Q)) >>= u)
      sC tr sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 tr z.1.1.2 z.1.2 z.2) := by
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_corr_run, cellTrackLift_eq_runCellStep (trF := fun _ => tr), bind_assoc]
  refine bind_congr fun z => ?_
  simp only [pure_bind]

theorem cellSimRunTrackHalted_inject_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inr (Q, w)))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)
      sC tr sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w false))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 tr z.1.1.2 z.1.2 z.2) := by
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_inject_run, cellTrackLift_eq_runCellStep (trF := fun _ => tr), bind_assoc]
  refine bind_congr fun z => ?_
  simp only [pure_bind]

theorem cellSimRunTrackHalted_deliver_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC tr sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w true))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 (updDeliverTr K sC tr Q w z.1.1.1.1) z.1.1.2 z.1.2 z.2) := by
  rw [cellSimRunTrackHalted_inr_query_bind]
  dsimp only
  rw [simImplCTrackHalted_deliver_run, cellTrackLift_eq_runCellStep, bind_assoc]
  refine bind_congr fun z => ?_
  simp only [pure_bind]

/-! ## Halted `deliver` combinators -/

open Classical in
theorem firstNEHalted'_deliver_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, fl, dead), tr) =
      (let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
       let hlazy := decide (∃ r_idx w_rem,
         EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
       pure (r.1, (r.2.1, (r.2.2.1, fl || (hlazy && r.2.2.2 && !dead), dead || !hlazy),
         updDeliverTr K sC tr Q w r.1))) := by
  simp only [firstNEHalted', splitSimImplHalted, updDeliverTr, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_pure, pure_bind]
  rfl

theorem simulateQ_firstNEHalted'_deliver_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, fl, dead), tr) =
      ((firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, fl, dead), tr) >>=
        fun z => (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
          (u z.1)).run z.2) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

open Classical in
theorem firstNEHalted'_deliver_of_noProbe
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ)))
    (tr : KemFailTrackState P.C.F)
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hstep : (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q w true)).run sC).run (g, false)) = pure ((ans, sC₁), (g₁, false))) :
    (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
      pure (ans, (sC₁, (g₁, false, false), updDeliverTr K sC tr Q w ans)) := by
  have hr := simRecvStepC_of_probeHook_run P ℓ Dh encPt encT decT idOf lam qep Q w true
    sC sC₁ g g₁ false false ans hstep
  have hlazy_true :
      decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) =
        true :=
    decide_eq_true hlazy
  rw [firstNEHalted'_deliver_run]
  dsimp only
  rw [hr, hlazy_true]
  simp only [Bool.and_false, Bool.or_false, Bool.false_and, Bool.not_true]

open Classical in
theorem firstNEHalted'_deliver_of_not_lazy
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hnot_lazy : ¬ ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) :
    ∃ (ans : Option (RecvResult (Plain ℓ)))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (tr' : KemFailTrackState P.C.F),
      (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
        pure (ans, (sC₁, (g₁, false, true), tr')) := by
  have hlazy_false :
      decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) =
        false :=
    decide_eq_false hnot_lazy
  rw [firstNEHalted'_deliver_run]
  dsimp only
  rw [hlazy_false]
  simp only [Bool.false_and, Bool.or_false, Bool.not_false]
  exact ⟨_, _, _, _, rfl⟩

theorem deliver_halted_pure_lockstep {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ)))
    (tr : KemFailTrackState P.C.F) (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell s_cell₁ :
      ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hprobe_run : (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q w true)).run sC).run (g, false)) = pure ((ans, sC₁), (g₁, false)))
    (hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent₁ m₁' g₁ s_cell₁)
    (hcells : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g₁ (s_cell₁ t tL) ∨
      runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
        (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w true))
        sC sent m' (s_cell t tL) =
        pure ((((ans, sC₁), sent₁), m₁'), s_cell₁ t tL))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g' : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl' dead' : Bool) (tr' : KemFailTrackState P.C.F) (sent' : List (Fig8C Pt))
      (m'' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell' :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl' dead' sC' sent' m'' g' s_cell' →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC', (g', fl', dead'), tr') >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL (u u₁)
            sC' tr' sent' m'' (s_cell' t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  have hrun := firstNEHalted'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
    sC sC₁ g g₁ ans tr hlazy hprobe_run
  rw [simulateQ_firstNEHalted'_deliver_query_bind, hrun, pure_bind]
  refine le_trans
    (hih ans sC₁ g₁ false false (updDeliverTr K sC tr Q w ans) sent₁ m₁' s_cell₁ hinv₁) ?_
  refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
    _ (u ans) sC sC₁ tr (updDeliverTr K sC tr Q w ans) g₁ sent sent₁ m' m₁' s_cell s_cell₁
    fun t ht tL htL => ?_
  rcases hcells t ht tL htL with hdoomed | hstep
  · exact Or.inl hdoomed
  · right
    rw [cellSimRunTrackHalted_deliver_query_bind, hstep, pure_bind]

theorem deliver_halted_cell_win {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ)))
    (tr : KemFailTrackState P.C.F) (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (t₀ : ℕ) (ht₀ : t₀ ∈ Finset.range ((qep + 1) + 2))
    (tL₀ : Option ℕ) (htL₀ : tL₀ ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t₀)
    (s_win : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstep_win :
      runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t₀ tL₀
        (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w true))
        sC sent m' (s_cell t₀ tL₀) =
        pure ((((ans, sC₁), sent₁), m₁'), s_win))
    (hwin : cellWinPred tL₀ t₀ s_win = true) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  refine evalDist_le_sum_cellSimRunTrackHalted_of_cell_step_win P K ℓ Dh encPt encT decT idOf lam
    qep _ _ (u ans) sC sC₁ tr (updDeliverTr K sC tr Q w ans) sent sent₁ m' m₁' s_cell
    t₀ ht₀ tL₀ htL₀ s_win ?_ hwin
  rw [cellSimRunTrackHalted_deliver_query_bind, hstep_win, pure_bind]

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux
