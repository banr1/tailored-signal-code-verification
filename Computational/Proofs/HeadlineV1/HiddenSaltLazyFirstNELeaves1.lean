/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import ProofLib.SepLogic.WP.StateNorm

/-!
# Non-Deliver Leaf Coupling Lemmas

Proves `KeptInv`, `CorrsKeptRecvInv`, and `SyncInv` preservation lemmas together with the
`FirstNECoupledInvD` step lemmas for the `corr` and `inject` oracles.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

/-! ## `corr` query step -/

theorem firstNESimImpl'_nondeliver_eq_firstNESimImpl
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_game : (SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (hnd : ∀ Q w, q_game ≠ .inl (.inl (.inr (Q, w))))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr q_game)).run
      (sC, (g, fl, dead), tr) =
    ((firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr q_game)).run
        (sC, (g, fl), tr) >>=
      fun x => pure (x.1, (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2))) := by
  have hlift : ∀ {α : Type} (m : ProbComp α),
      (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ α).run (sC, (g, fl, dead), tr) =
        (m >>= fun a => pure (a, (sC, (g, fl, dead), tr))) := fun _ => rfl
  rcases q_game with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · simp only [firstNESimImpl', firstNESimImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · simp only [firstNESimImpl', firstNESimImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · exact False.elim (hnd Q w rfl)
  · simp only [firstNESimImpl', firstNESimImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · simp only [firstNESimImpl', firstNESimImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]

theorem simulateQ_firstNESimImpl'_nondeliver_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_game : (SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (hnd : ∀ Q w, q_game ≠ .inl (.inl (.inr (Q, w))))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr q_game) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr q_game) >>= u)).run (sC, (g, fl, dead), tr) =
    ((firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr q_game)).run
        (sC, (g, fl), tr) >>=
      fun x =>
        (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u x.1)).run
          (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2)) := by
  rw [simulateQ_query_bind, StateT.run_bind]
  change ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr q_game)).run
      (sC, (g, fl, dead), tr) >>=
    fun p => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (u p.1)).run p.2) = _
  rw [firstNESimImpl'_nondeliver_eq_firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
    q_game hnd sC g fl dead tr]
  simp only [bind_assoc, pure_bind]

theorem syncInv_corr_step {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ} {sent : List (Fig8C Pt)}
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g s_unsh)
    (hep_unsh : s_unsh.epoch = g.epoch)
    (hstop : sC.base.stopped = false)
    (hallow_g : g.corrAllowed Q = true) :
    SyncInv P Dh encPt encT idOf lam qep (corrStepStateC P encT Dh sC Q (g.st Q)) sent
      (m'.afterCorr Q) (g.afterCorr Q)
      (DeliverForge.afterCorrShifted (cellShift none 0) s_unsh Q) := by
  rcases hsync with ⟨hmeta_imp, hmsync, hwf_g, hcorrs_le, hep_le, hsnap_idx, hcorrs_snaps,
    hfig8, hkept, hkept_inv, hid, hhon⟩
  rcases hmeta_imp hstop with ⟨s_R, hmeta⟩
  have hep_mir : sC.base.mir.epoch Q = g.epoch Q := congrFun hmeta.hepoch_fig8.symm Q
  have hsnaps_eq : (corrStepStateC P encT Dh sC Q (g.st Q)).snaps =
      (Q, g.epoch Q, corrStepGhost P encT Dh sC.base Q (g.st Q)) :: sC.snaps := by
    simp [corrStepStateC, hep_mir]
  have hfig8' := fig8SenderSync_afterCorr Q hfig8
  have hwf_g' : SM.Thm1L17.WFState 3 (g.afterCorr Q) := by
    rw [← afterCorrShifted_zero_eq_afterCorr g Q]
    exact wfState_afterCorrShifted (by omega) 0 hwf_g
      (corrAllowedPaper_of_corrAllowed (m' := m') hallow_g).1
  refine ⟨?_, ?_, hwf_g', corrsLeEpoch_afterCorr Q hcorrs_le, hep_le, ?_, ?_,
    hfig8', ?_, ?_, hid, hhon⟩
  · intro _
    exact ⟨s_R.afterCorr Q, hmeta.afterCorr_preserves Q _⟩
  · simpa [DeliverForge.afterCorrShifted, SM.GameState.afterCorr, cellShift] using
      hmsync.corr_step Q hep_unsh
  · rw [hsnaps_eq]
    refine corrsSnapIdxInv_afterCorr Q (corrStepGhost P encT Dh sC.base Q (g.st Q)) hsnap_idx
      fun hsend => ?_
    rcases hfig8.hvS Q hsend with ⟨x, v, hγ, hvS, hlast⟩
    refine ⟨⟨KeyPair.generate P.C x, ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩⟩, ?_, ?_⟩
    · simp [corrStepGhost, toGhost, hγ, hvS]
    · dsimp only
      rw [← hlast]
      exact Nat.mod_le v.lastIndex (2 ^ 32)
  · rw [hsnaps_eq]
    exact corrsSnapsInv_afterCorr Q (corrStepGhost P encT Dh sC.base Q (g.st Q)) hcorrs_snaps
  · refine corrsKeptRecvInv_afterCorr Q hkept ?_ ?_
    · simp [corrStepStateC, Kept.ofSt]
    · intro R hRQ
      simp [corrStepStateC, Function.update_of_ne hRQ]
  · refine ⟨fun R st hst => ?_, fun R t v hnone hrs_v => ?_, hfig8'.hvR⟩
    · rcases Decidable.eq_or_ne Q R with rfl | hQR
      · simp [corrStepStateC, Kept.ofSt] at hst
        exact hst.symm
      · simp [corrStepStateC, Function.update_of_ne (Ne.symm hQR)] at hst
        exact hkept_inv.hfull R st hst
    · rcases Decidable.eq_or_ne Q R with rfl | hQR
      · simp [corrStepStateC, Kept.ofSt] at hnone
      · simp [corrStepStateC, Function.update_of_ne (Ne.symm hQR)] at hnone hrs_v
        exact hkept_inv.hrs R t v hnone hrs_v

theorem firstNECoupledInvD_corr_query_step_aux {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inr Q)) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inr Q)))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hbody with ⟨hcol, hrel_all⟩
  rw [simulateQ_firstNESimImpl'_nondeliver_query_bind P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
    (.inr Q) (fun _ _ h => nomatch h) u sC g false false tr]
  by_cases href : sC.base.stopped = true ∨
      (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
        !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · rw [firstNESimImpl_corr_refused P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q sC g false tr
      href, pure_bind]
    refine le_trans
      (hih none sC g false false tr sent m' s_cell
        (Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩))) ?_
    refine sum_cellSimRun_le_of_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
      _ (u none) sC sC g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
    rw [cellSimRun_corr_query_bind,
      runCellStep_simCorrC_refused P encT Dh _ qep t tL Q sC sent m' (s_cell t tL) href,
      pure_bind]
  · rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at href
    rcases href with ⟨hstop, href'⟩
    rcases hsync.1 hstop with ⟨s_R, hmeta⟩
    have htrans_pos : sC.base.mir.trans.map SM.Record.pos = g.trans.map SM.Record.pos := by
      have h := congrArg (List.map Prod.fst) hmeta.htrans_fig8
      simpa [List.map_map, Function.comp_def] using h
    obtain ⟨hallow_g, hallow_m⟩ :=
      hsync.2.1.corr_sync hmeta.hchall_fig8.symm hmeta.hcomp_fig8.symm htrans_pos href'
    have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
    rw [firstNESimImpl_corr_accepted P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q sC g false tr
      hstop href' hwin_g hallow_g, pure_bind]
    let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL => if (s_cell t tL).win then s_cell t tL
        else DeliverForge.afterCorrShifted (cellShift tL t) (s_cell t tL) Q
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
            DeliverForge.afterCorrShifted (cellShift none 0) (s_cell 0 none) Q := by
          dsimp only [s_cell₁]
          simp [(hrel_all 0 ht0).1.win_df_false]
        rwa [hs0]
    refine le_trans
      (hih (some (corrStepGhost P encT Dh sC.base Q (g.st Q)))
        (corrStepStateC P encT Dh sC Q (g.st Q)) (g.afterCorr Q) false false tr sent
        (m'.afterCorr Q) s_cell₁ hinvD₁) ?_
    refine sum_cellSimRun_le_of_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
      _ (u (some (corrStepGhost P encT Dh sC.base Q (g.st Q))))
      sC (corrStepStateC P encT Dh sC Q (g.st Q)) (g.afterCorr Q) sent sent
      m' (m'.afterCorr Q) s_cell s_cell₁ fun t ht tL htL => ?_
    rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
    · left
      dsimp only [s_cell₁]
      simp only [hdoomed.2.2.2, ↓reduceIte]
      exact hdoomed.of_corrs_sub (fun _ h => List.mem_cons_of_mem _ h)
    · right
      dsimp only [s_cell₁]
      simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
      rw [cellSimRun_corr_query_bind,
        runCellStep_simCorrC_accepted_cell P encT Dh _ qep t tL Q sC sent m' (s_cell t tL) g
          hstop href' hallow_m hrel_sh.win_df_false (hrel_sh.corrAllowedPaper_df Q)
          (congrFun hrel_sh.st_eq Q),
        pure_bind]

/-! ## `Kept` state preservation -/

theorem lFig8_receive_le_tcur {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (st st' : Fig8St Pt) (c' : Fig8C Pt) (res_fig : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hc_le : c'.1.1 ≤ st.tcur)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' =
      some (st', res_fig)) :
    ∃ v₀ v',
      st.vR c'.1.1 = some v₀ ∧
      (lFS P.C P.codec ℓ encT idOf 25000).receive v₀ c'.1 c'.2 =
        some (v', res_fig.2.1, res_fig.2.2) ∧
      res_fig.1 = c'.1.1 ∧
      st' = { st with vR := Function.update st.vR c'.1.1 (some v') } := by
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at hfig
  by_cases h1 : (st.id.sendsIn c'.1.1 || decide (st.tcur + 1 < c'.1.1)) = true
  · simp [h1] at hfig
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hfig
    have hne : ¬(c'.1.1 = st.tcur + 1) := by omega
    simp only [hne, ↓reduceIte] at hfig
    cases hvR : st.vR c'.1.1 with
    | none => rw [hvR] at hfig; cases hfig
    | some v₀ =>
      rw [hvR] at hfig
      dsimp only at hfig
      cases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v₀ c'.1 c'.2 with
      | none => rw [hfs] at hfig; cases hfig
      | some p =>
        rcases p with ⟨v', i', m'⟩
        rw [hfs] at hfig
        simp only [Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, rfl⟩
        exact ⟨v₀, v', rfl, hfs, rfl, rfl⟩

theorem lFig8_receive_epoch_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (st st' : Fig8St Pt) (c' : Fig8C Pt) (res_fig : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' =
      some (st', res_fig)) :
    res_fig.1 = c'.1.1 := by
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at hfig
  by_cases h1 : (st.id.sendsIn c'.1.1 || decide (st.tcur + 1 < c'.1.1)) = true
  · simp [h1] at hfig
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hfig
    revert hfig
    cases (if c'.1.1 = st.tcur + 1 then (_ : Option (Fig8St Pt)) else some st) with
    | none => intro h; cases h
    | some s₁ =>
      dsimp only
      cases s₁.vR c'.1.1 with
      | none => intro h; cases h
      | some v₀ =>
        dsimp only
        cases (lFS P.C P.codec ℓ encT idOf 25000).receive v₀ c'.1 c'.2 with
        | none => intro h; cases h
        | some p =>
          intro h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ rfl

theorem fig8SenderSync_accept_le_tcur {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (Q : Party)
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {c' : Fig8C Pt} {st' : Fig8St Pt} {res_fig : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)}
    (hfig8 : Fig8SenderSync g)
    (ht'_le : res_fig.1 ≤ g.epoch Q)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', res_fig)) :
    Fig8SenderSync (g.accept Q st' ⟨Q.other, res_fig.1, res_fig.2.1⟩) := by
  have hc_eq := lFig8_receive_epoch_eq P Dh encPt encT idOf lam (g.st Q) st' c' res_fig hfig
  have hc_le : c'.1.1 ≤ (g.st Q).tcur := by
    rw [hfig8.htcur Q, ← hc_eq]; exact ht'_le
  rcases lFig8_receive_le_tcur P Dh encPt encT idOf lam (g.st Q) st' c' res_fig hc_le hfig with
    ⟨v₀, v', hvR₀, _, _, hst'⟩
  have hep_acc : (g.accept Q st' ⟨Q.other, res_fig.1, res_fig.2.1⟩).epoch = g.epoch := by
    ext R; rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simp [SM.GameState.accept, SM.GameState.delete, Nat.max_eq_left ht'_le]
    · simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne (Ne.symm hQR)]
  refine ⟨fun R => ?_, fun R hsend => ?_, fun R t => ?_⟩
  · rw [hep_acc]; rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simpa [SM.GameState.accept, SM.GameState.delete, hst'] using hfig8.htcur Q
    · simpa [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne (Ne.symm hQR)] using
        hfig8.htcur R
  · rw [hep_acc] at hsend
    rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simpa [SM.GameState.accept, SM.GameState.delete, hst'] using hfig8.hvS Q hsend
    · simpa [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne (Ne.symm hQR)] using
        hfig8.hvS R hsend
  · rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simp only [SM.GameState.accept, SM.GameState.delete, Function.update_self, hst']
      rcases Decidable.eq_or_ne c'.1.1 t with rfl | htc
      · have hsome : ((g.st Q).vR c'.1.1).isSome = true := by simp [hvR₀]
        simpa [Function.update_self, hsome] using (hfig8.hvR Q c'.1.1).mp hsome
      · simpa [Function.update_of_ne (Ne.symm htc)] using hfig8.hvR Q t
    · simpa [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne (Ne.symm hQR)] using
        hfig8.hvR R t

theorem corrsKeptRecvInv_updKeptOnRes_accept_le_tcur
    {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (Q : Party)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {b' : SimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {c' : Fig8C Pt} {st' : Fig8St Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    (hfull : ∀ R st, (sC.kept R).full = some st → st = g.st R)
    (hrs : ∀ R t v, (sC.kept R).full = none → (sC.kept R).rs t = some v → (g.st R).vR t = some v)
    (hkept : CorrsKeptRecvInv sC g)
    (ht'_le : t' ≤ (g.st Q).tcur)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let sC' := { updKeptOnRes fig fs Q c' (some (.accepted t' i' (some m_out))) sC with base := b' }
    let g' := g.accept Q st' ⟨Q.other, t', i'⟩
    (∀ R st, (sC'.kept R).full = some st → st = g'.st R) ∧
    (∀ R t v, (sC'.kept R).full = none → (sC'.kept R).rs t = some v → (g'.st R).vR t = some v) ∧
    CorrsKeptRecvInv sC' g' := by
  intro fig fs sC' g'
  have hc_eq := lFig8_receive_epoch_eq P Dh encPt encT idOf lam (g.st Q) st' c' (t', i', m_out) hfig
  have hc_le : c'.1.1 ≤ (g.st Q).tcur := hc_eq ▸ ht'_le
  rcases lFig8_receive_le_tcur P Dh encPt encT idOf lam (g.st Q) st' c' (t', i', m_out) hc_le hfig
    with ⟨v₀, v', hvR₀, hfs_rcv, _, hst'⟩
  refine ⟨fun R st hst => ?_, fun R t v hnone hrs_v => ?_, fun R e hmem t hle hrecv => ?_⟩
  · rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simp only [sC', g', updKeptOnRes, SM.GameState.accept, SM.GameState.delete,
        Function.update_self, LibsignalSimC.Kept.recv] at hst ⊢
      cases hfull_Q : (sC.kept Q).full with
      | none => rw [hfull_Q] at hst; cases hst
      | some st₀ =>
        rw [hfull_Q, hfull Q st₀ hfull_Q] at hst
        dsimp only [fig] at hst
        rw [hfig] at hst
        exact Option.some.inj hst.symm
    · simp only [sC', g', updKeptOnRes, SM.GameState.accept, SM.GameState.delete,
        Function.update_of_ne (Ne.symm hQR)] at hst ⊢
      exact hfull R st hst
  · rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simp only [sC', g', updKeptOnRes, SM.GameState.accept, SM.GameState.delete,
        Function.update_self, LibsignalSimC.Kept.recv] at hnone hrs_v ⊢
      cases hfull_Q : (sC.kept Q).full with
      | some st₀ =>
        rw [hfull_Q, hfull Q st₀ hfull_Q] at hnone
        dsimp only [fig] at hnone
        rw [hfig] at hnone
        cases hnone
      | none =>
        rw [hfull_Q] at hrs_v
        rw [hst']
        rcases Decidable.eq_or_ne c'.1.1 t with rfl | htc
        · simp only [Function.update_self, Option.bind_eq_some_iff, Option.map_eq_some_iff, fs]
            at hrs_v ⊢
          rcases hrs_v with ⟨v₁, hv₁, ⟨p, hp, rfl⟩⟩
          have hv₁_eq : v₁ = v₀ :=
            Option.some.inj ((hrs Q c'.1.1 v₁ hfull_Q hv₁).symm.trans hvR₀)
          subst hv₁_eq
          have hp_eq := Option.some.inj (hp.symm.trans hfs_rcv)
          subst hp_eq; rfl
        · simp only [Function.update_of_ne (Ne.symm htc)] at hrs_v ⊢
          exact hrs Q t v hfull_Q hrs_v
    · simp only [sC', g', updKeptOnRes, SM.GameState.accept, SM.GameState.delete,
        Function.update_of_ne (Ne.symm hQR)] at hnone hrs_v ⊢
      exact hrs R t v hnone hrs_v
  · rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simp only [sC', updKeptOnRes, Function.update_self, LibsignalSimC.Kept.recv]
      cases hfull_Q : (sC.kept Q).full with
      | some st₀ =>
        rw [hfull Q st₀ hfull_Q]
        dsimp only [fig]
        rw [hfig]; left; rfl
      | none =>
        right
        rcases hkept Q e hmem t hle hrecv with hsome | hrs_t
        · rw [hfull_Q] at hsome; cases hsome
        · rcases Option.isSome_iff_exists.mp hrs_t with ⟨v₁, hv₁⟩
          rcases Decidable.eq_or_ne c'.1.1 t with rfl | htc
          · have hv₁_eq : v₁ = v₀ :=
              Option.some.inj ((hrs Q c'.1.1 v₁ hfull_Q hv₁).symm.trans hvR₀)
            subst hv₁_eq
            dsimp only [fs]
            simp [Function.update_self, hv₁, hfs_rcv]
          · simp [Function.update_of_ne (Ne.symm htc), hv₁]
    · simp only [sC', updKeptOnRes, Function.update_of_ne (Ne.symm hQR)]
      exact hkept R e hmem t hle hrecv

theorem keptInv_and_corrsKeptRecvInv_updKeptOnRes_accept_le_tcur
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (P₀ : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (Q : Party)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {b' : SimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {c' : Fig8C Pt} {st' : Fig8St Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    (hfig8 : Fig8SenderSync g)
    (hkept_inv : KeptInv P₀ Dh encPt encT idOf lam sC g)
    (hkept : CorrsKeptRecvInv sC g)
    (ht'_le : t' ≤ g.epoch Q)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let sC' := { updKeptOnRes fig fs Q c' (some (.accepted t' i' (some m_out))) sC with base := b' }
    let g' := g.accept Q st' ⟨Q.other, t', i'⟩
    Fig8SenderSync g' ∧
    KeptInv P₀ Dh encPt encT idOf lam sC' g' ∧
    CorrsKeptRecvInv sC' g' := by
  intro fig fs sC' g'
  have hfig8' : Fig8SenderSync g' :=
    fig8SenderSync_accept_le_tcur P Dh encPt encT idOf lam Q hfig8 ht'_le hfig
  have ht'_le_tcur : t' ≤ (g.st Q).tcur := by rw [hfig8.htcur Q]; exact ht'_le
  rcases corrsKeptRecvInv_updKeptOnRes_accept_le_tcur P Dh encPt encT idOf lam Q (b' := b')
      hkept_inv.hfull hkept_inv.hrs hkept ht'_le_tcur hfig with
    ⟨hfull', hrs', hkept'⟩
  exact ⟨hfig8', ⟨hfull', hrs', hfig8'.hvR⟩, hkept'⟩

/-! ## `inject` query step -/

theorem pos_epoch_lt_min_of_trivial {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g : SM.GameState St Msg C} {pos : SM.Pos}
    (hwf_g : SM.Thm1L17.WFState (2 + 1) g)
    (hsafe_g : g.safeInj (2 + 1) = true)
    (htriv_g : g.trivial (2 + 1) pos = true) :
    pos.epoch < min (g.epoch .A) (g.epoch .B) := by
  have hunh : SM.healedBy g.tL (2 + 1) pos.epoch = false := by
    unfold SM.GameState.trivial at htriv_g
    rcases Bool.or_eq_true_iff.mp htriv_g with hcomp_g | hnot_in
    · exact hwf_g.comp_not_healed pos (List.contains_iff_mem.mp hcomp_g)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnot_in
      exact hnot_in.2
  unfold SM.GameState.safeInj at hsafe_g
  cases htl : g.tL with
  | none => rw [htl] at hunh; nomatch hunh
  | some m₀ =>
    rw [htl] at hunh hsafe_g
    simp only [SM.healedBy, decide_eq_false_iff_not, decide_eq_true_eq] at hunh hsafe_g
    omega

private theorem syncInv_updAmbSimStateC {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (b : Bool)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {sent : List (Fig8C Pt)}
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g s_unsh) :
    SyncInv P Dh encPt encT idOf lam qep (updAmbSimStateC Pt b sC) sent m' g s_unsh := by
  unfold updAmbSimStateC
  split_ifs with hb
  · rcases hsync with ⟨hmeta_imp, hmsync, hwf_g, hcorrs_le, hep_le, hsnap_idx, hcorrs_snaps,
      hfig8, hkept, ⟨hfull, hrs, hvR⟩, hid, hhon⟩
    refine ⟨fun hstop => ?_, hmsync, hwf_g, hcorrs_le, hep_le, hsnap_idx, hcorrs_snaps,
      hfig8, hkept, ⟨hfull, hrs, hvR⟩, hid, hhon⟩
    rcases hmeta_imp hstop with ⟨s_R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, h19, h20, h21⟩
    exact ⟨s_R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, h19, h20, h21⟩
  · exact hsync

theorem guardC_simRecvC_false_amb_cases {PQ PQC Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (∃ (ans : Option (RecvResult (Plain ℓ))) (b : Bool),
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w false)).run sC =
          pure (ans, updAmbSimStateC Pt b sC)) ∨
    (sC.base.stopped = false ∧
      (sC.base.mir.inTransit Q.other w).isSome = false ∧
      sC.base.mir.safeInj 3 = true ∧
      ∃ (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt),
        (LibsignalSim.toWire c' = w ∨ (w, c') ∈ sC.base.honest) ∧
        ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
          (LibsignalSimC.guardC
            (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w false)).run sC =
            (LibsignalSimC.fwdAnswerC qep fig fs H Q w false ci? T pq' c').run
              (updAmbSimStateC Pt b sC)) := by
  by_cases hstop : sC.base.stopped = true
  · left; refine ⟨none, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstop, ↓reduceIte]
    rfl
  have hstopF : sC.base.stopped = false := Bool.eq_false_iff.mpr hstop
  by_cases hwin : sC.base.mir.win = true
  · left; refine ⟨none, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwin,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  have hwinF : sC.base.mir.win = false := Bool.eq_false_iff.mpr hwin
  by_cases hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = true
  · left; refine ⟨none, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hguard,
      Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hguardF : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false := Bool.eq_false_iff.mpr hguard
  have hinT_false : (sC.base.mir.inTransit Q.other w).isSome = false := by
    revert hguardF; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
  have hsafe_true : sC.base.mir.safeInj 3 = true := by
    revert hguardF; cases sC.base.mir.safeInj 3 <;> simp
  by_cases hlen : w.length < 9
  · left; refine ⟨some .rejected, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hguardF,
      hlen, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none =>
    left; refine ⟨some .rejected, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hguardF,
      hlen, hparse, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  | some hp =>
    rcases hp with ⟨h, _⟩
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · left; refine ⟨some .rejected, false, fun H => ?_⟩
      unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
        hguardF, hlen, hparse, haddr, Bool.false_and, Bool.not_false, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    have haddrF : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = false :=
      Bool.eq_false_iff.mpr haddr
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · left; refine ⟨some .rejected, false, fun H => ?_⟩
      unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
        hguardF, hlen, hparse, haddrF, hpan, Bool.false_and, Bool.not_false, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    have hpanF : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false :=
      Bool.eq_false_iff.mpr hpan
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ =>
      left; refine ⟨some .rejected, false, fun H => ?_⟩
      unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
        hguardF, hlen, hparse, haddrF, hpanF, hspqr, Bool.false_and, Bool.not_false, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      let cRaw (ep : ℕ) (t : Option Pt) : Fig8C Pt :=
        ((ep, t), (h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
      let mkC (ep : ℕ) (t : Option Pt) : Fig8C Pt :=
        match honestC with
        | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else cRaw ep t
        | none => cRaw ep t
      have hcRaw (ep : ℕ) (t : Option Pt) : LibsignalSim.toWire (cRaw ep t) = w := by
        have hdrop : (w.drop (w.length - 8)).length = 8 := by rw [List.length_drop]; omega
        unfold LibsignalSim.toWire
        dsimp only [cRaw]
        rw [tagBytes_tag8 hdrop, List.take_append_drop]
      have hmkC (ep : ℕ) (t : Option Pt) :
          LibsignalSim.toWire (mkC ep t) = w ∨ (w, mkC ep t) ∈ sC.base.honest := by
        dsimp only [mkC, honestC]
        cases hfind : sC.base.honest.find?
            (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
        | none => exact Or.inl (hcRaw ep t)
        | some wc =>
          rcases wc with ⟨w₀, c₀⟩
          dsimp only [Option.map]
          split_ifs
          · have hmem := List.mem_of_find?_eq_some hfind
            have hpred := List.find?_some hfind
            simp only [Bool.and_eq_true, beq_iff_eq] at hpred
            rcases hpred with ⟨rfl, _⟩
            exact Or.inr hmem
          · exact Or.inl (hcRaw ep t)
      cases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
            (h.counter.toNat + 1) = true
        · left; refine ⟨some .rejected, false, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
            hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, hrej, Bool.false_and, Bool.not_false,
            Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          rfl
        · have hrejF : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
              (h.counter.toNat + 1) = false := Bool.eq_false_iff.mpr hrej
          right; refine ⟨hstopF, hinT_false, hsafe_true, false, some ci, h.senderRatchetKey, pq',
            mkC ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch (decT h.senderRatchetKey),
            hmkC _ _, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hstopF, hwinF,
            hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, hrejF, fwdC_false_eq,
            Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          rfl
      | none =>
        let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
        by_cases hev_salt :
            (evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true
        · left; refine ⟨some .rejected, false, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
            hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted, hev_salt,
            Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          rfl
        have hev_saltF :
            (evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) =
              false := Bool.eq_false_iff.mpr hev_salt
        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
        · left; refine ⟨some .rejected, false, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
            hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted, hev_saltF, hT0,
            Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          rfl
        have hT0F : (decT h.senderRatchetKey == some 0) = false := Bool.eq_false_iff.mpr hT0
        let spkAmb := Q == Party.A && (sC.base.chains Q).any (·.key.isNone)
        let b_amb : Bool := inReceiveOnlyEpoch sC.base.mir Q || spkAmb
        by_cases hwin_i :
            (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
        · left; refine ⟨some .rejected, b_amb, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
          dsimp only [b_amb]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, ite_modify_bind_run,
            pure_bind, hstopF, hwinF, hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC,
            evicted, hev_saltF, hT0F, spkAmb, hwin_i, Bool.false_and, Bool.not_false,
            Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        have hwin_iF :
            (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false := Bool.eq_false_iff.mpr hwin_i
        cases hT : decT h.senderRatchetKey with
        | none =>
          have hT0' : ((none : Option Pt) == some 0) = false := rfl
          left; refine ⟨some .rejected, b_amb, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
          dsimp only [b_amb]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, ite_modify_bind_run,
            pure_bind, hstopF, hwinF, hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC,
            evicted, hev_saltF, hT0', spkAmb, hwin_iF, hT, Bool.false_and, Bool.not_false,
            Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        | some T =>
          have hT0' : (some T == (some 0 : Option Pt)) = false := hT ▸ hT0F
          by_cases hev : evicted = true
          · right; refine ⟨hstopF, hinT_false, hsafe_true, b_amb, none, h.senderRatchetKey, pq',
              cRaw (sC.base.mir.epoch Q + 1) (some T), Or.inl (hcRaw _ _), fun H => ?_⟩
            unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
            dsimp only [b_amb]
            simp only [StateT.run_bind, StateT.run_get, ite_modify_bind_run, pure_bind, hstopF,
              hwinF, hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted,
              hev_saltF, hT0', hwin_iF, hT, fwdEvictC_false_eq, Bool.false_and,
              Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
            simp only [hev, evicted, honestC, ↓reduceIte]
            rfl
          · have hevF : evicted = false := Bool.eq_false_iff.mpr hev
            right; refine ⟨hstopF, hinT_false, hsafe_true, b_amb, none, h.senderRatchetKey, pq',
              mkC (sC.base.mir.epoch Q + 1) (some T), hmkC _ _, fun H => ?_⟩
            unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
            dsimp only [b_amb]
            simp only [StateT.run_bind, StateT.run_get, ite_modify_bind_run, pure_bind, hstopF,
              hwinF, hguardF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted,
              hev_saltF, hT0', hwin_iF, hT, fwdC_false_eq, Bool.false_and,
              Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
            simp only [hevF, evicted, honestC, Bool.false_eq_true, ↓reduceIte]
            rfl

private theorem onAnswer_rejected_run
    {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (b : SimState PQ Pt ℓ) :
    (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' (some .rejected)).run b = pure (some .rejected, b) :=
  rfl

theorem onAnswer_false_accepted_trivial_run
    {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ) (b : SimState PQ Pt ℓ)
    (ht'_le : t' ≤ qep + 1)
    (htriv_mir : b.mir.trivial 3 ⟨Q.other, t', i'⟩ = true) :
    ∃ (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ),
      (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
        Q w false ci? T pq' (some (.accepted t' i' (some m_out)))).run b = pure (ans, b') ∧
      b'.honest = b.honest ∧
      b'.stopped = b.stopped ∧
      b'.mir = b.mir.accept Q () ⟨Q.other, t', i'⟩ := by
  have hnot_lt : ¬(qep + 1 < t') := Nat.not_lt.mpr ht'_le
  unfold onAnswer onAccept putS
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
    Bool.false_eq_true, ↓reduceIte, hnot_lt, htriv_mir]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem syncInv_inject_accept_step
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    {sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ} {b' : SimState (List (BitVec 8)) Pt ℓ}
    {sent : List (Fig8C Pt)} {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {c' : Fig8C Pt} {st' : Fig8St Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g s_unsh)
    (hstop : sC₀.base.stopped = false)
    (hsafe_g : g.safeInj (2 + 1) = true)
    (htriv_g : g.trivial (2 + 1) ⟨Q.other, t', i'⟩ = true)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out))
    (hhon_b' : b'.honest = sC₀.base.honest)
    (hstop_b' : b'.stopped = sC₀.base.stopped)
    (hmir_b' : b'.mir = sC₀.base.mir.accept Q () ⟨Q.other, t', i'⟩) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let pos : SM.Pos := ⟨Q.other, t', i'⟩
    let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) := some (.accepted t' i' (some m_out))
    SyncInv P Dh encPt encT idOf lam qep
      { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' } sent
      (m'.accept Q () pos) (g.accept Q st' pos) (s_unsh.accept Q st' pos) := by
  intro fig fs pos res_acc
  rcases hsync with ⟨hmeta_imp, hmsync, hwf_g, hcorrs_le, hep_le, hsnap_idx, hcorrs_snaps,
    hfig8, hkept, hkept_inv, hid, hhon⟩
  rcases hmeta_imp hstop with ⟨s_R, hmeta⟩
  have hpos_lt : pos.epoch < min (g.epoch .A) (g.epoch .B) :=
    pos_epoch_lt_min_of_trivial hwf_g hsafe_g htriv_g
  have ht'_le_ep : t' ≤ g.epoch Q := by
    change pos.epoch ≤ g.epoch Q
    cases Q <;> omega
  have ht'_le_tcur : t' ≤ (g.st Q).tcur := by
    rw [hfig8.htcur Q]; exact ht'_le_ep
  have hc_eq := lFig8_receive_epoch_eq P Dh encPt encT idOf lam (g.st Q) st' c' (t', i', m_out) hrcv
  have hc_le : c'.1.1 ≤ (g.st Q).tcur := hc_eq ▸ ht'_le_tcur
  rcases lFig8_receive_le_tcur P Dh encPt encT idOf lam (g.st Q) st' c' (t', i', m_out) hc_le hrcv
    with ⟨_, _, _, _, _, hst'⟩
  rcases keptInv_and_corrsKeptRecvInv_updKeptOnRes_accept_le_tcur P P Dh encPt encT idOf lam Q
      (b' := b') hfig8 hkept_inv hkept ht'_le_ep hrcv with
    ⟨hfig8', hkept_inv', hkept'⟩
  refine ⟨?_, hmsync.inject_step Q st' pos,
    SM.Thm1L17.accept_wf hwf_g (SM.Thm1L17.pos_epoch_le_of_trivial hwf_g hsafe_g htriv_g),
    corrsLeEpoch_accept Q st' pos hcorrs_le,
    ?_, corrsSnapIdxInv_accept Q st' pos hsnap_idx hcorrs_le,
    corrsSnapsInv_accept Q st' pos hcorrs_snaps,
    hfig8', hkept', hkept_inv', ?_, ?_⟩
  · intro _
    have hb'_eq : b' =
        { mir := sC₀.base.mir.accept Q () pos,
          pq := b'.pq, pn := b'.pn, unackA := b'.unackA,
          honest := b'.honest, chains := b'.chains,
          amb := b'.amb, stopped := false } := by
      cases b'
      dsimp only at hmir_b' hstop_b'
      rw [hmir_b', hstop_b', hstop]
    rw [hb'_eq]
    exact ⟨s_R.accept Q (s_R.st Q) pos,
      hmeta.accept_preserves Q (s_R.st Q) st' pos b'.pq b'.pn b'.unackA b'.honest b'.chains b'.amb⟩
  · intro R
    rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simp [SM.GameState.accept, SM.GameState.delete, pos, Nat.max_eq_left ht'_le_ep, hep_le Q]
    · simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne (Ne.symm hQR), hep_le R]
  · intro R
    rcases Decidable.eq_or_ne Q R with rfl | hQR
    · simpa [SM.GameState.accept, SM.GameState.delete, hst'] using hid Q
    · simpa [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne (Ne.symm hQR)] using
        hid R
  · dsimp only
    rw [hhon_b']
    exact hhon

theorem firstNECoupledInvD_inject_query_step_aux {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hbody with ⟨hcol, hrel_all⟩
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  rw [simulateQ_firstNESimImpl'_nondeliver_query_bind P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
    (.inl (.inr (Q, w))) (fun _ _ h => nomatch h) u sC g false false tr]
  rcases guardC_simRecvC_false_amb_cases P encT decT qep fig fs Q w sC with
    ⟨ans, b, hpure⟩ | ⟨hstop, hinT, hsafe, b, ci?, T, pq', c', hcw, hfwd⟩
  · let sC₁ := updAmbSimStateC Pt b sC
    rw [firstNESimImpl_inject_pure_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w sC sC₁ ans
      g false tr (hpure (probeHook fig (qep + 1))), pure_bind]
    have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent m' g s_cell :=
      Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩,
        (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig,
        syncInv_updAmbSimStateC P Dh encPt encT idOf lam qep b hsync⟩)
    refine le_trans (hih ans sC₁ g false false tr sent m' s_cell hinv₁) ?_
    refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
      _ (u ans) sC sC₁ sent sent m' m' g s_cell s_cell fun t _ tL _ => Or.inr ?_
    rw [cellSimRun_inject_query_bind,
      runCellStep_inject_pure P encT decT qep fig fs t tL Q w sC sC₁ ans sent m' (s_cell t tL)
        (hpure (deliverForgeHook Pt ℓ)), pure_bind]
  · let sC₀ := updAmbSimStateC Pt b sC
    have hsync₀ : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g (s_cell 0 none) :=
      syncInv_updAmbSimStateC P Dh encPt encT idOf lam qep b hsync
    have horig₀ : FirstNEInTransOriginInv qep sC₀.snaps g s_cell :=
      (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig
    have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g s_cell :=
      Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig₀, hsync₀⟩)
    rcases hsync.1 hstop with ⟨s_R, hmeta⟩
    have hhon_wire : ∀ wc ∈ sC.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun _ hwc => (mem_honest_of_honestSentSync Pt hsync.2.2.2.2.2.2.2.2.2.2.2 hwc).1
    have htrans_mir : ∀ r ∈ g.trans,
        ∃ r_m ∈ sC.base.mir.trans, r_m.pos = r.pos ∧ r_m.ct = LibsignalSim.toWire r.ct := by
      intro r hr
      have hmem : (r.pos, LibsignalSim.toWire r.ct) ∈
          sC.base.mir.trans.map (fun r => (r.pos, r.ct)) := by
        rw [hmeta.htrans_fig8]
        exact List.mem_map_of_mem hr
      rcases List.mem_map.mp hmem with ⟨r_m, hrm_mem, heq⟩
      exact ⟨r_m, hrm_mem, (Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩
    obtain ⟨hInT_sC, hinT_g, hsafe_g⟩ := inject_sync_of_baseSync Q w c' sC g hhon_wire htrans_mir
      hmeta.hepoch_fig8.symm hmeta.htL_fig8.symm hcw hstop hinT hsafe
    have hInT_sC₀ : (sC₀.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false := by
      rw [(updAmbSimStateC_fields Pt b sC).2.2.2.1, (updAmbSimStateC_fields Pt b sC).2.2.2.2.1]
      exact hInT_sC
    have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
    cases hrcv : fig.receive (g.st Q) c' with
    | none =>
      have hrun := onAnswer_rejected_run qep Q w false ci? T pq' sC₀.base
      have hinj_g : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
          pure (some .rejected, g) := by
        rw [injectImpl_h1_run fig qep Q c' g hwin_g]
        simp [hinT_g, hsafe_g, hrcv]
      rw [firstNESimImpl_inject_fwd_of_eq P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
        ci? T pq' c' sC sC₀ g g false tr (some .rejected) (some .rejected) sC₀.base
        (hfwd (probeHook fig (qep + 1))) hInT_sC₀ hinj_g hrun, pure_bind]
      refine le_trans (hih (some .rejected) sC₀ g false false tr sent m' s_cell hinv₀) ?_
      refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u (some .rejected)) sC sC₀ sent sent m' m' g s_cell s_cell fun t ht tL htL => ?_
      rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        have hinj_c : (injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c')).run
            (s_cell t tL) = pure (some .rejected, s_cell t tL) := by
          rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
          have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
            rw [hrel_sh.inTransit_eq]; exact hinT_g
          have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
            hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
          have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = none := by
            rw [congrFun hrel_sh.st_eq Q]; exact hrcv
          simp [hinT_c, hsafe_c, hrcv_c]
        rw [cellSimRun_inject_query_bind,
          runCellStep_inject_fwd_of_eq P encT decT qep fig fs t tL Q w ci? T pq' c' sC sC₀ sent m'
            (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
            (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c hrun, pure_bind]
        rfl
    | some v =>
      rcases v with ⟨st', t', i', m_out⟩
      by_cases hq : (qep + 1) + 1 < t'
      · have hrun := onAnswer_rejected_run qep Q w false ci? T pq' sC₀.base
        have hinj_g : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
            pure (some .rejected, g) := by
          rw [injectImpl_h1_run fig qep Q c' g hwin_g]
          simp [hinT_g, hsafe_g, hrcv, hq]
        rw [firstNESimImpl_inject_fwd_of_eq P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
          ci? T pq' c' sC sC₀ g g false tr (some .rejected) (some .rejected) sC₀.base
          (hfwd (probeHook fig (qep + 1))) hInT_sC₀ hinj_g hrun, pure_bind]
        refine le_trans (hih (some .rejected) sC₀ g false false tr sent m' s_cell hinv₀) ?_
        refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
          _ (u (some .rejected)) sC sC₀ sent sent m' m' g s_cell s_cell fun t ht tL htL => ?_
        rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
        · exact Or.inl hdoomed
        · right
          have hinj_c : (injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c')).run
              (s_cell t tL) = pure (some .rejected, s_cell t tL) := by
            rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
            have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
              rw [hrel_sh.inTransit_eq]; exact hinT_g
            have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
              hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
            have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = some (st', t', i', m_out) := by
              rw [congrFun hrel_sh.st_eq Q]; exact hrcv
            simp [hinT_c, hsafe_c, hrcv_c, hq]
          rw [cellSimRun_inject_query_bind,
            runCellStep_inject_fwd_of_eq P encT decT qep fig fs t tL Q w ci? T pq' c' sC sC₀ sent m'
              (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
              (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c hrun, pure_bind]
          rfl
      · have ht'_le : t' ≤ (qep + 1) + 1 := Nat.le_of_not_lt hq
        let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
          some (.accepted t' i' (some m_out))
        let s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
          fun t tL =>
            if (s_cell t tL).win then s_cell t tL
            else if cellTrivialT tL t (s_cell t tL) ⟨Q.other, t', i'⟩ then
              (s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩
            else if t' == t then { s_cell t tL with win := true }
            else s_cell t tL
        rcases inject_step_branch_cases fig qep Q c' st' t' i' m_out
            (m₁' := updMirOnRes Q res_acc m') hcol hrel_all ht'_le hinT_g hsafe_g hrcv with
          ⟨t₀, ht₀, tL₀, htL₀, hrel_sh₀, htriv₀, ht_eq₀, hwin₀⟩ |
          ⟨htriv_g, hg'_eq, hinv', hcells'⟩
        · obtain ⟨ans, b', hrun, _, _⟩ :=
            onAnswer_run_pure qep Q w false ci? T pq' (some .rejected)
              (updKeptOnRes fig fs Q c' (some .rejected) sC₀).base
          have hinj_c₀ : (injectImplCell fig (qep + 1) tL₀ t₀ (SM.Config.auth t₀) (Q, c')).run
              (s_cell t₀ tL₀) = pure (some .rejected, { s_cell t₀ tL₀ with win := true }) := by
            rw [injectImplCell_run fig qep tL₀ t₀ Q c' (s_cell t₀ tL₀) hrel_sh₀.win_df_false]
            have hinT_c : ((s_cell t₀ tL₀).inTransit Q.other c').isSome = false := by
              rw [hrel_sh₀.inTransit_eq]; exact hinT_g
            have hsafe_c : (s_cell t₀ tL₀).safeInj (cellDelta tL₀ t₀) = true :=
              hrel_sh₀.safeInj_df_of_safeInj_mir (cellDelta_le_three tL₀ t₀) hsafe_g
            have hrcv_c : fig.receive ((s_cell t₀ tL₀).st Q) c' = some (st', t', i', m_out) := by
              rw [congrFun hrel_sh₀.st_eq Q]; exact hrcv
            simp [hinT_c, hsafe_c, hrcv_c, hq, htriv₀, ht_eq₀]
          refine evalDist_le_sum_cellSimRun_of_cell_step_win P ℓ Dh encPt encT decT idOf lam qep
            _ _ (u ans) sC { updKeptOnRes fig fs Q c' (some .rejected) sC₀ with base := b' }
            sent sent m' m' s_cell t₀ ht₀ tL₀ htL₀ { s_cell t₀ tL₀ with win := true } ?_ hwin₀
          rw [cellSimRun_inject_query_bind,
            runCellStep_inject_fwd_of_eq P encT decT qep fig fs t₀ tL₀ Q w ci? T pq' c' sC sC₀
              sent m' (s_cell t₀ tL₀) { s_cell t₀ tL₀ with win := true } (some .rejected) ans b'
              (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c₀ hrun, pure_bind]
          rfl
        · have hpos_lt : (⟨Q.other, t', i'⟩ : SM.Pos).epoch < min (g.epoch .A) (g.epoch .B) :=
            pos_epoch_lt_min_of_trivial hsync.2.2.1 hsafe_g htriv_g
          have ht'_le_qep : t' ≤ qep + 1 := by
            have ht'_le_ep : t' ≤ g.epoch Q := by
              change (⟨Q.other, t', i'⟩ : SM.Pos).epoch ≤ g.epoch Q
              cases Q <;> omega
            exact le_trans ht'_le_ep (hsync.2.2.2.2.1 Q)
          have htriv_mir : (updKeptOnRes fig fs Q c' res_acc sC₀).base.mir.trivial 3
              ⟨Q.other, t', i'⟩ = true := by
            dsimp only [updKeptOnRes]
            rw [(updAmbSimStateC_fields Pt b sC).2.2.2.2.1,
              ← hmeta.trivial_fig8 3 ⟨Q.other, t', i'⟩]
            exact htriv_g
          obtain ⟨ans, b', hrun, hhon_b', hstop_b', hmir_b'⟩ :=
            onAnswer_false_accepted_trivial_run qep Q w ci? T pq' t' i' m_out
              (updKeptOnRes fig fs Q c' res_acc sC₀).base ht'_le_qep htriv_mir
          have hinj_g : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
              pure (res_acc, g.accept Q st' ⟨Q.other, t', i'⟩) := by
            rw [injectImpl_h1_run fig qep Q c' g hwin_g]
            simp [hinT_g, hsafe_g, hrcv, hq, htriv_g, res_acc]
          rw [firstNESimImpl_inject_fwd_of_eq P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
            ci? T pq' c' sC sC₀ g (g.accept Q st' ⟨Q.other, t', i'⟩) false tr res_acc ans b'
            (hfwd (probeHook fig (qep + 1))) hInT_sC₀ hinj_g hrun, pure_bind]
          rw [hg'_eq] at hinv' hcells'
          have hinvD' : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
              { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' } sent
              (updMirOnRes Q res_acc m') (g.accept Q st' ⟨Q.other, t', i'⟩) s_cell' := by
            rcases hinv' with hwin' | ⟨_, hcol', hrel_all'⟩
            · exact Or.inl hwin'
            · refine Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol', hrel_all'⟩, ?_, ?_⟩)
              · exact hg'_eq ▸ firstNEInTransOriginInv_inject_step qep Q st' t' i' sC₀.snaps horig₀
              · have hsync' := syncInv_inject_accept_step P Dh encPt encT idOf lam qep Q hsync₀
                  ((updAmbSimStateC_fields Pt b sC).2.2.2.2.2.trans hstop)
                  hsafe_g htriv_g hrcv hhon_b' hstop_b' hmir_b'
                rcases hcells' 0 ht0 none (Finset.mem_insert_self none _) with
                  hdoomed0 | ⟨_, _, hs0_eq⟩
                · have hw0 := hdoomed0.2.2.2
                  rw [(hrel_all' 0 ht0).1.win_df_false] at hw0; nomatch hw0
                · dsimp only [updMirOnRes, res_acc, s_cell'] at hs0_eq ⊢
                  rwa [hs0_eq]
          refine le_trans (hih ans { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' }
            (g.accept Q st' ⟨Q.other, t', i'⟩) false false tr sent
            (updMirOnRes Q res_acc m') s_cell' hinvD') ?_
          refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
            _ (u ans) sC { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' }
            sent sent m' (updMirOnRes Q res_acc m')
            (g.accept Q st' ⟨Q.other, t', i'⟩) s_cell s_cell' fun t ht tL htL => ?_
          rcases hcells' t ht tL htL with hdoomed' | ⟨hrel_sh, htriv_sh, hs_eq⟩
          · exact Or.inl hdoomed'
          · right
            dsimp only [s_cell'] at hs_eq ⊢
            rw [hs_eq]
            have hinj_c : (injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c')).run
                (s_cell t tL) = pure (res_acc, (s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) := by
              rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
              have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
                rw [hrel_sh.inTransit_eq]; exact hinT_g
              have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
                hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
              have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = some (st', t', i', m_out) := by
                rw [congrFun hrel_sh.st_eq Q]; exact hrcv
              simp [hinT_c, hsafe_c, hrcv_c, hq, htriv_sh, res_acc]
            rw [cellSimRun_inject_query_bind,
              runCellStep_inject_fwd_of_eq P encT decT qep fig fs t tL Q w ci? T pq' c' sC sC₀
                sent m' (s_cell t tL) ((s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) res_acc ans b'
                (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c hrun, pure_bind]

end CryptoVerification.LibsignalSession.HeadlineV1
end
