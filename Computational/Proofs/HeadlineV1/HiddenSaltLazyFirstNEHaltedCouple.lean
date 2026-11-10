/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliver
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple3
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple4
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple5
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple6
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple8
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafTransmit
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNESkeleton
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4

/-!
# Online-Halted Cell-Sum Bound for `firstNEHalted'`

**Checked by Lean.** Proves the halted per-oracle step lemmas for `FirstNECoupledInvD` and bounds
the bad-event probability of `firstNEHalted'` by the sum of `forgeGuessedAdvantageCellPaper` on
`simDeliverForgeTrackHalted` across admissible cells.
-/

@[expose] public section

set_option autoImplicit false

open scoped MeasureTheory
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted (evalDist_firstNEHalted'_dead_eq_zero firstNEHalted')
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliver (firstNECoupledInvD_deliver_halted_query_step)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux (cellSimRunTrackHalted cellSimRunTrackHalted_inject_query_bind cellSimRunTrackHalted_inl_query_bind evalDist_cellSimRunTrackHalted_cellWinPred_eq_zero_of_doomed evalDist_le_sum_cellSimRunTrackHalted_of_cell_step_win forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeTrackHalted_eq sum_cellSimRunTrackHalted_le_of_doomed_or_eq)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedSend (cellSimRunTrackHalted_chall_of_guard_fail cellSimRunTrackHalted_chall_of_guards_pass cellSimRunTrackHalted_transmit_of_guard_fail cellSimRunTrackHalted_transmit_of_guards_pass firstNECoupledInvD_corr_halted_query_step kemFailSendStepHalted_run_of_guard_fail kemFailSendStepHalted_run_of_guards_pass simulateQ_firstNEHalted'_chall_query_bind simulateQ_firstNEHalted'_inject_eq_firstNESimImpl' simulateQ_firstNEHalted'_inl_query_bind simulateQ_firstNEHalted'_transmit_query_bind)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState KeptInv SameMeta deliverForgeHook initKemFailTrack keptInv_send simDeliverForgeTrackHalted simImplCTrackHalted stepKemFailSend transmitPure)
open CryptoGames.LibsignalSession (GhostState IdentityKey Params PublicKey)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart X25519RealizesDh lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC probeHook)
open CryptoGames.SM (RecvResult)
open CryptoGames.SM.Thm1 (Mirror)
open CryptoVerification.LibsignalSession.HeadlineV1 (CorrsKeptRecvInv FirstNECellFamilyInvT FirstNECellFamilyInvT_body FirstNECoupledInvD FirstNEInTransOriginInv MirrorSync SyncInv cellChallPost cellDelta cellDelta_le_three cellTransmitPost cellTrivialT cellWinPred challPure_eq_of_pprimePaperRelShifted corrsKeptRecvInv_updSimStateCSend corrsLeEpoch_record_of_epMgmt corrsSnapIdxInv_record_of_epMgmt corrsSnapsInv_of_corrs_eq deliverForge_forgeGuessedAdvantageCellPaper_eq drawRc epMgmt_corrs_st_and_epoch_le evalDist_bind_le_double_sum evalDist_cell_chall_mkPub_some evalDist_cell_transmit_mkPub_some evalDist_drawRc_bind_const fig8SenderSync_and_id_send_step firstNECellFamilyInvT_chall_step firstNECellFamilyInvT_transmit_step firstNECellFamilyInv_inl_one_le_sum_cell firstNECoupledInvD_init firstNECoupledInvD_unif_step firstNEInTransOriginInv_inject_step firstNEInTransOriginInv_send_step_of_cellFamily firstNESimImpl_inject_fwd_of_eq firstNESimImpl_inject_pure_run guardC_simRecvC_false_amb_cases honestSentSync_cons injectImplCell injectImplCell_run injectImpl_h1_run inject_step_branch_cases inject_sync_of_baseSync kemFailSendStep_chall_mkPub_some kemFailSendStep_transmit_mkPub_some mem_honest_of_honestSentSync onAnswer_false_accepted_trivial_run onAnswer_rejected_run onAnswer_run_pure pos_epoch_lt_min_of_trivial runCellStep runCellStep_inject_fwd_of_eq runCellStep_inject_pure simSendQFig syncInv_inject_accept_step syncInv_transmit_step syncInv_updAmbSimStateC transmitPure_eq_of_pprimePaperRelShifted updAmbSimStateC updAmbSimStateC_fields updKeptOnRes updMirOnRes updSimStateCSend)

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedCouple

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)

/-! ## Halted query steps -/

theorem firstNECoupledInvD_inject_halted_query_step {α : Type}
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
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hbody with ⟨hcol, hrel_all⟩
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  rw [simulateQ_firstNEHalted'_inject_eq_firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam
    qep q Q w u sC g false false tr]
  rcases guardC_simRecvC_false_amb_cases P encT decT qep fig fs Q w sC with
    ⟨ans, b, hpure⟩ | ⟨hstop, hinT, hsafe, b, ci?, T, pq', c', hcw, hfwd⟩
  · let sC₁ := updAmbSimStateC Pt b sC
    rw [firstNESimImpl_inject_pure_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w sC sC₁ ans
      g false tr (hpure (probeHook fig (qep + 1))), pure_bind]
    have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent m' g s_cell :=
      Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩,
        (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig,
        syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g (s_cell 0 none)
          hsync⟩)
    refine le_trans (hih ans sC₁ g false false tr sent m' s_cell hinv₁) ?_
    refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
      _ (u ans) sC sC₁ tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
    rw [cellSimRunTrackHalted_inject_query_bind,
      runCellStep_inject_pure P encT decT qep fig fs t tL Q w sC sC₁ ans sent m' (s_cell t tL)
        (hpure (deliverForgeHook Pt ℓ)), pure_bind]
  · let sC₀ := updAmbSimStateC Pt b sC
    have hsync₀ : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g (s_cell 0 none) :=
      syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g (s_cell 0 none) hsync
    have horig₀ : FirstNEInTransOriginInv qep sC₀.snaps g s_cell :=
      (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig
    have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g s_cell :=
      Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig₀, hsync₀⟩)
    rcases hsync.1 hstop with ⟨s_R, hmeta⟩
    have hhon_wire : ∀ wc ∈ sC.base.honest, wc.1 = CryptoGames.Ratchet.LibsignalSim.toWire wc.2 :=
      fun _ hwc => (mem_honest_of_honestSentSync Pt hsync.2.2.2.2.2.2.2.2.2.2.2 hwc).1
    have htrans_mir : ∀ r ∈ g.trans,
        ∃ r_m ∈ sC.base.mir.trans, r_m.pos = r.pos ∧ r_m.ct = CryptoGames.Ratchet.LibsignalSim.toWire r.ct := by
      intro r hr
      have hmem : (r.pos, CryptoGames.Ratchet.LibsignalSim.toWire r.ct) ∈
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
      have hinj_g : (CryptoGames.SM.injectImpl fig (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (Q, c')).run g =
          pure (some .rejected, g) := by
        rw [injectImpl_h1_run fig qep Q c' g hwin_g]
        simp [hinT_g, hsafe_g, hrcv]
      rw [firstNESimImpl_inject_fwd_of_eq P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
        ci? T pq' c' sC sC₀ g g false tr (some .rejected) (some .rejected) sC₀.base
        (hfwd (probeHook fig (qep + 1))) hInT_sC₀ hinj_g hrun, pure_bind]
      refine le_trans (hih (some .rejected) sC₀ g false false tr sent m' s_cell hinv₀) ?_
      refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
        _ (u (some .rejected)) sC sC₀ tr tr g sent sent m' m' s_cell s_cell fun t ht tL htL => ?_
      rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        have hinj_c : (injectImplCell fig (qep + 1) tL t (CryptoGames.SM.Config.auth t) (Q, c')).run
            (s_cell t tL) = pure (some .rejected, s_cell t tL) := by
          rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
          have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
            rw [hrel_sh.inTransit_eq]; exact hinT_g
          have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
            hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
          have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = none := by
            rw [congrFun hrel_sh.st_eq Q]; exact hrcv
          simp [hinT_c, hsafe_c, hrcv_c]
        rw [cellSimRunTrackHalted_inject_query_bind,
          runCellStep_inject_fwd_of_eq P encT decT qep fig fs t tL Q w ci? T pq' c' sC sC₀ sent m'
            (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
            (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c hrun, pure_bind]
        rfl
    | some v =>
      rcases v with ⟨st', t', i', m_out⟩
      by_cases hq : (qep + 1) + 1 < t'
      · have hrun := onAnswer_rejected_run qep Q w false ci? T pq' sC₀.base
        have hinj_g : (CryptoGames.SM.injectImpl fig (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (Q, c')).run g =
            pure (some .rejected, g) := by
          rw [injectImpl_h1_run fig qep Q c' g hwin_g]
          simp [hinT_g, hsafe_g, hrcv, hq]
        rw [firstNESimImpl_inject_fwd_of_eq P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
          ci? T pq' c' sC sC₀ g g false tr (some .rejected) (some .rejected) sC₀.base
          (hfwd (probeHook fig (qep + 1))) hInT_sC₀ hinj_g hrun, pure_bind]
        refine le_trans (hih (some .rejected) sC₀ g false false tr sent m' s_cell hinv₀) ?_
        refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
          _ (u (some .rejected)) sC sC₀ tr tr g sent sent m' m' s_cell s_cell fun t ht tL htL => ?_
        rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
        · exact Or.inl hdoomed
        · right
          have hinj_c : (injectImplCell fig (qep + 1) tL t (CryptoGames.SM.Config.auth t) (Q, c')).run
              (s_cell t tL) = pure (some .rejected, s_cell t tL) := by
            rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
            have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
              rw [hrel_sh.inTransit_eq]; exact hinT_g
            have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
              hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
            have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = some (st', t', i', m_out) := by
              rw [congrFun hrel_sh.st_eq Q]; exact hrcv
            simp [hinT_c, hsafe_c, hrcv_c, hq]
          rw [cellSimRunTrackHalted_inject_query_bind,
            runCellStep_inject_fwd_of_eq P encT decT qep fig fs t tL Q w ci? T pq' c' sC sC₀ sent m'
              (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
              (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c hrun, pure_bind]
          rfl
      · have ht'_le : t' ≤ (qep + 1) + 1 := Nat.le_of_not_lt hq
        let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
          some (.accepted t' i' (some m_out))
        let s_cell' :
            ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
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
          have hinj_c₀ : (injectImplCell fig (qep + 1) tL₀ t₀ (CryptoGames.SM.Config.auth t₀) (Q, c')).run
              (s_cell t₀ tL₀) = pure (some .rejected, { s_cell t₀ tL₀ with win := true }) := by
            rw [injectImplCell_run fig qep tL₀ t₀ Q c' (s_cell t₀ tL₀) hrel_sh₀.win_df_false]
            have hinT_c : ((s_cell t₀ tL₀).inTransit Q.other c').isSome = false := by
              rw [hrel_sh₀.inTransit_eq]; exact hinT_g
            have hsafe_c : (s_cell t₀ tL₀).safeInj (cellDelta tL₀ t₀) = true :=
              hrel_sh₀.safeInj_df_of_safeInj_mir (cellDelta_le_three tL₀ t₀) hsafe_g
            have hrcv_c : fig.receive ((s_cell t₀ tL₀).st Q) c' = some (st', t', i', m_out) := by
              rw [congrFun hrel_sh₀.st_eq Q]; exact hrcv
            simp [hinT_c, hsafe_c, hrcv_c, hq, htriv₀, ht_eq₀]
          refine evalDist_le_sum_cellSimRunTrackHalted_of_cell_step_win P K ℓ Dh encPt encT decT
            idOf lam qep _ _ (u ans) sC { updKeptOnRes fig fs Q c' (some .rejected) sC₀ with base := b' }
            tr tr sent sent m' m' s_cell t₀ ht₀ tL₀ htL₀ { s_cell t₀ tL₀ with win := true }
            ?_ hwin₀
          rw [cellSimRunTrackHalted_inject_query_bind,
            runCellStep_inject_fwd_of_eq P encT decT qep fig fs t₀ tL₀ Q w ci? T pq' c' sC sC₀
              sent m' (s_cell t₀ tL₀) { s_cell t₀ tL₀ with win := true } (some .rejected) ans b'
              (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c₀ hrun, pure_bind]
          rfl
        · have hpos_lt : (⟨Q.other, t', i'⟩ : CryptoGames.SM.Pos).epoch < min (g.epoch .A) (g.epoch .B) :=
            pos_epoch_lt_min_of_trivial hsync.2.2.1 hsafe_g htriv_g
          have ht'_le_qep : t' ≤ qep + 1 := by
            have ht'_le_ep : t' ≤ g.epoch Q := by
              change (⟨Q.other, t', i'⟩ : CryptoGames.SM.Pos).epoch ≤ g.epoch Q
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
          have hinj_g : (CryptoGames.SM.injectImpl fig (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (Q, c')).run g =
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
          refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
            _ (u ans) sC { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' }
            tr tr (g.accept Q st' ⟨Q.other, t', i'⟩) sent sent m' (updMirOnRes Q res_acc m')
            s_cell s_cell' fun t ht tL htL => ?_
          rcases hcells' t ht tL htL with hdoomed' | ⟨hrel_sh, htriv_sh, hs_eq⟩
          · exact Or.inl hdoomed'
          · right
            dsimp only [s_cell'] at hs_eq ⊢
            rw [hs_eq]
            have hinj_c : (injectImplCell fig (qep + 1) tL t (CryptoGames.SM.Config.auth t) (Q, c')).run
                (s_cell t tL) = pure (res_acc, (s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) := by
              rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
              have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
                rw [hrel_sh.inTransit_eq]; exact hinT_g
              have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
                hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
              have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = some (st', t', i', m_out) := by
                rw [congrFun hrel_sh.st_eq Q]; exact hrcv
              simp [hinT_c, hsafe_c, hrcv_c, hq, htriv_sh, res_acc]
            rw [cellSimRunTrackHalted_inject_query_bind,
              runCellStep_inject_fwd_of_eq P encT decT qep fig fs t tL Q w ci? T pq' c' sC sC₀
                sent m' (s_cell t tL) ((s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) res_acc ans b'
                (hfwd (deliverForgeHook Pt ℓ)) hInT_sC₀ hinj_c hrun, pure_bind]

theorem firstNECoupledInvD_transmit_halted_query_step {α : Type}
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
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hbody with ⟨hcol, hrel_all⟩
  have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩)
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [simulateQ_firstNEHalted'_transmit_query_bind,
      kemFailSendStepHalted_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
        sC (g, false) tr (Or.inl hg1), pure_bind]
    refine le_trans (hih none sC g false false tr sent m' s_cell hinv₀) ?_
    refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
      _ (u none) sC sC tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
    exact cellSimRunTrackHalted_transmit_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep t tL
      Q m₀ r u sC tr sent m' (s_cell t tL) (Or.inl hg1)
  · have hg1_f :
        (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    have hstop : sC.base.stopped = false := by
      cases h : sC.base.stopped
      · rfl
      · rw [h] at hg1_f; cases hg1_f
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [simulateQ_firstNEHalted'_transmit_query_bind,
        kemFailSendStepHalted_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
          sC (g, false) tr (Or.inr (Or.inl hep)), pure_bind]
      refine le_trans (hih none sC g false false tr sent m' s_cell hinv₀) ?_
      refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
        _ (u none) sC sC tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
      exact cellSimRunTrackHalted_transmit_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep t tL
        Q m₀ r u sC tr sent m' (s_cell t tL) (Or.inr (Or.inl hep))
    | some s₁ =>
      have hg3_f : ((none : Option (Plain ℓ)).isSome && !s₁.safeCh 3 Q) = false := rfl
      have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
      have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
      rcases hsync.1 hstop with ⟨s_R, hmeta⟩
      rcases hmeta.epMgmt_some Q qep r.isSome hep with ⟨_, g₁, _, hep_g, _, _, _⟩
      rw [simulateQ_firstNEHalted'_transmit_query_bind,
        kemFailSendStepHalted_run_of_guards_pass P K Dh encPt encT decT idOf lam qep Q m₀ none r s₁
          sC g false tr hg1_f hep hg3_f, bind_assoc, bind_assoc]
      have hrhs_eq :
          ∀ t tL,
            cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
              (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8)))
                (Plain ℓ) (BitVec 512) (List (BitVec 8)))
                (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
              sC tr sent m' (s_cell t tL) = _ :=
        fun t tL =>
          cellSimRunTrackHalted_transmit_of_guards_pass P K ℓ Dh encPt encT decT idOf lam qep t tL
            Q m₀ r s₁ u sC tr sent m' (s_cell t tL) hg1_f hep hg3_f
      simp_rw [hrhs_eq, bind_assoc]
      refine evalDist_bind_le_double_sum _ _ _ _ _ fun rq => ?_
      cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte]
        let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
          else sC.base.pn Q
        cases hmk : CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq
            (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
             else sC.base.pn Q) with
        | none =>
          simp only [bind_assoc, pure_bind, evalDist_drawRc_bind_const]
          exact hih none sC g false false
            { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
            sent m' s_cell hinv₀
        | some p_pub =>
          rcases p_pub with ⟨pq', pub⟩
          dsimp only [Option.isSome]
          erw [(bind_assoc _ _ _).trans
            (kemFailSendStep_transmit_mkPub_some P qep
              (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ r s₁ pq' pub
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q)
              sC g tr (stepKemFailSend P.C.F K tr Q rq) hwin_g
              (fun x =>
                (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
                  (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, false), x.2.2.2) >>=
                fun z => pure z.2.2.1.2.1))]
          have hcell_mk :
              ∀ t tL,
                𝒟[(drawRc r >>= fun _rc =>
                    runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
                      (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ)
                        (simSendQFig Q pub m₀ none _rc))
                      sC sent m' (s_cell t tL) >>= fun z =>
                      match z.1.1.1.1 with
                      | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
                      | some c =>
                        pure ((((some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                          updSimStateCSend (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀
                            false s₁ pq' pn c sC), z.1.1.2), z.1.2), z.2)) >>=
                  fun w =>
                    cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
                      (u w.1.1.1.1) w.1.1.1.2
                      (if w.1.1.1.1.isSome then stepKemFailSend P.C.F K tr Q rq
                       else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })
                      w.1.1.2 w.1.2 w.2 >>=
                    fun z => pure (cellWinPred tL t z.2)] =
                𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
                    cellTransmitPost (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep Q m₀ s₁
                      pq' pub pn sC sent m'
                      (fun w =>
                        cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
                          (u w.1.1.1.1) w.1.1.1.2
                          (if w.1.1.1.1.isSome then stepKemFailSend P.C.F K tr Q rq
                           else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })
                          w.1.1.2 w.1.2 w.2 >>=
                        fun z => pure (cellWinPred tL t z.2))
                      (if (s_cell t tL).win then (none, s_cell t tL)
                       else transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                         (cellDelta tL t) (qep + 1) Q (pub, m₀) coins false (s_cell t tL))] := by
            intro t tL
            rw [bind_assoc]
            exact evalDist_cell_transmit_mkPub_some P qep t tL
              (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ r s₁ pq' pub pn
              sC sent m' (s_cell t tL) _
          refine le_of_le_of_eq ?_
            (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun tL _ =>
              congrArg (fun μ => μ {true})
                ((hcell_mk t tL).symm.trans
                  (by dsimp only [Option.isSome, pn]; simp only [bind_assoc]; rfl)))
          refine evalDist_bind_le_double_sum _ _ _ _ _ fun coins => ?_
          let c := (fig.send (g₁.st Q) (pub, m₀) coins).2
          let st' := (fig.send (g₁.st Q) (pub, m₀) coins).1
          let rec_r : CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
            ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, (pub, m₀), c⟩
          let m₁' := match m'.epMgmt (2 + 1) (qep + 1) Q false with
            | some m₁ => m₁.record (2 + 1) Q () ⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, (pub, m₀), c⟩ false
            | none => m'
          let s_cell₁ :
              ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
            fun t tL =>
              if (s_cell t tL).win then s_cell t tL
              else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
                | some s₂ => s₂.record (cellDelta tL t) Q st' rec_r false
                | none => s_cell t tL
          have htr_g := (transmitPure_eq_of_pprimePaperRelShifted fig (2 + 1) qep Q (pub, m₀)
            coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g).1
          rw [htr_g]
          dsimp only
          have hcell_raw :=
            firstNECellFamilyInvT_transmit_step (m₁' := m₁') fig qep Q (pub, m₀) coins r.isSome
              (Or.inr ⟨rfl, hcol, hrel_all⟩) hep_g
          dsimp only at hcell_raw
          have hcell_next : FirstNECellFamilyInvT qep false (g₁.record (2 + 1) Q st' rec_r false)
              m₁' s_cell₁ := by
            convert hcell_raw using 1
            ext t tL
            dsimp only [s_cell₁, c, st', rec_r]
            split_ifs with hw
            · rfl
            · cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;> rfl
          have horig_next : FirstNEInTransOriginInv qep
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC).snaps
              (g₁.record (2 + 1) Q st' rec_r false) s_cell₁ :=
            firstNEInTransOriginInv_send_step_of_cellFamily qep sC.snaps Q r.isSome false
              st' (pub, m₀) c horig hrel_all hep_g hsync.2.2.2.1 hsync.2.2.2.2.2.1
          have hsync_next : SyncInv P Dh encPt encT idOf lam qep
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
              (g₁.record (2 + 1) Q st' rec_r false) (s_cell₁ 0 none) :=
            syncInv_transmit_step P ℓ Dh encPt encT idOf lam qep Q m₀ pub coins r.isSome s₁ pq' pn
              sC sent m' g g₁ s_cell hstop hep hep_g (hrel_all 0 ht0).1 hsync
          have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
              (g₁.record (2 + 1) Q st' rec_r false) s_cell₁ := by
            rcases hcell_next with hwin | ⟨_, hcol', hrel_all'⟩
            · exact Or.inl hwin
            · exact Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol', hrel_all'⟩, horig_next, hsync_next⟩)
          refine le_trans
            (hih (some (CryptoGames.Ratchet.LibsignalSim.toWire c))
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC)
              (g₁.record (2 + 1) Q st' rec_r false) false false
              (stepKemFailSend P.C.F K tr Q rq) (c :: sent) m₁' s_cell₁ hinv₁) ?_
          refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
          rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
          · simp only [s_cell₁, hdoomed.2.2.2, ↓reduceIte]
            have hcorrs_sub : ∀ x ∈ g.corrs, x ∈ (g₁.record (2 + 1) Q st' rec_r false).corrs := by
              unfold CryptoGames.SM.GameState.epMgmt CryptoGames.SM.GameState.leak at hep_g
              split_ifs at hep_g <;>
                { injection hep_g with h; subst h; intro x hx; exact hx }
            rw [evalDist_cellSimRunTrackHalted_cellWinPred_eq_zero_of_doomed P K ℓ Dh encPt encT
              decT idOf lam qep t tL (u (some (CryptoGames.Ratchet.LibsignalSim.toWire c)))
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (stepKemFailSend P.C.F K tr Q rq)
              (c :: sent) m₁' (hdoomed.of_corrs_sub hcorrs_sub)]
            exact zero_le
          · have htr_df := (transmitPure_eq_of_pprimePaperRelShifted fig (cellDelta tL t) qep Q
              (pub, m₀) coins r.isSome hrel_sh hep_g).2
            simp only [s_cell₁, hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
            rw [htr_df]
            simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
            dsimp only [cellTransmitPost, m₁', rec_r, c, st', pn, fig]
            cases m'.epMgmt (2 + 1) (qep + 1) Q false <;>
              cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;>
              { dsimp only [Option.isSome]; simp only [↓reduceIte]; exact le_rfl }
      · simp only [↓reduceIte, pure_bind]
        exact hih none sC g false false
          { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
          sent m' s_cell hinv₀

theorem firstNECoupledInvD_chall_halted_query_step {α : Type}
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
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))))
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
        𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL (u u₁)
            sC₁ tr₁ sent₁ m₁' (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>=
          u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>=
            u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  rcases hbody with ⟨hcol, hrel_all⟩
  have hcoupled₀ :
      FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩)
  rcases hsync with ⟨hmeta_opt, hmsync, hwf_g, hcorrs_le, hep_le_qep, hsnap_idx, hcorrs_snaps,
    hsender_sync, hkept_corr, hkept, hid_st, hhon_sent⟩
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [simulateQ_firstNEHalted'_chall_query_bind,
      kemFailSendStepHalted_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁)
        r sC (g, false) tr (Or.inl hg1), pure_bind]
    refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
    refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
      _ (u none) sC sC tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
    exact cellSimRunTrackHalted_chall_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep t tL
      Q m₀ m₁ r u sC tr sent m' (s_cell t tL) (Or.inl hg1)
  · have hg1_f :
        (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [simulateQ_firstNEHalted'_chall_query_bind,
        kemFailSendStepHalted_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀
          (some m₁) r sC (g, false) tr (Or.inr (Or.inl hep)), pure_bind]
      refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
      refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
        _ (u none) sC sC tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
      exact cellSimRunTrackHalted_chall_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep t tL
        Q m₀ m₁ r u sC tr sent m' (s_cell t tL) (Or.inr (Or.inl hep))
    | some s₁ =>
      by_cases hg3 : ((some m₁).isSome && !s₁.safeCh 3 Q) = true
      · rw [simulateQ_firstNEHalted'_chall_query_bind,
          kemFailSendStepHalted_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀
            (some m₁) r sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)), pure_bind]
        refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
        refine sum_cellSimRunTrackHalted_le_of_doomed_or_eq P K ℓ Dh encPt encT decT idOf lam qep
          _ (u none) sC sC tr tr g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
        exact cellSimRunTrackHalted_chall_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep t tL
          Q m₀ m₁ r u sC tr sent m' (s_cell t tL) (Or.inr (Or.inr ⟨s₁, hep, hg3⟩))
      · have hg3_f : ((some m₁).isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
        have hstop : sC.base.stopped = false := by
          cases h : sC.base.stopped
          · rfl
          · simp [h] at hg1_f
        have hsafe_s₁ : s₁.safeCh 3 Q = true := by
          simpa using hg3_f
        rcases hmeta_opt hstop with ⟨s_R, hmeta⟩
        have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
        rcases hmsync.chall_sync (hrel_all 0 ht0).1 hmeta.hepoch_fig8.symm hmeta.htL_fig8.symm
            hep hsafe_s₁ with
          ⟨g₁, m₁', hep_g, hsafe_g, hep_m, hsafe_m, hb_eq⟩
        have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
        rw [simulateQ_firstNEHalted'_chall_query_bind,
          kemFailSendStepHalted_run_of_guards_pass P K Dh encPt encT decT idOf lam qep Q m₀
            (some m₁) r s₁ sC g false tr hg1_f hep hg3_f, bind_assoc, bind_assoc]
        have hrhs_eq :
            ∀ t tL,
              cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
                (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8)))
                  (Plain ℓ) (BitVec 512) (List (BitVec 8)))
                  (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)
                sC tr sent m' (s_cell t tL) = _ :=
          fun t tL =>
            cellSimRunTrackHalted_chall_of_guards_pass P K ℓ Dh encPt encT decT idOf lam qep t tL
              Q m₀ m₁ r s₁ u sC tr sent m' (s_cell t tL) hg1_f hep hg3_f
        simp_rw [hrhs_eq, bind_assoc]
        refine evalDist_bind_le_double_sum _ _ _ _ _ fun rq => ?_
        cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
        · simp only [Bool.false_eq_true, ↓reduceIte]
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
            else sC.base.pn Q
          cases hmk : CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with
          | none =>
            simp only [bind_assoc, pure_bind, evalDist_drawRc_bind_const]
            exact hih none sC g false false
              { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
              sent m' s_cell hcoupled₀
          | some p_pub =>
            rcases p_pub with ⟨pq', pub⟩
            dsimp only [Option.isSome]
            erw [(bind_assoc _ _ _).trans
              (kemFailSendStep_chall_mkPub_some P qep
                (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ m₁ r s₁ pq' pub
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
                 else sC.base.pn Q)
                sC g tr (stepKemFailSend P.C.F K tr Q rq) hwin_g
                (fun x =>
                  (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
                    (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, false), x.2.2.2) >>=
                  fun z => pure z.2.2.1.2.1))]
            have hcell_mk :
                ∀ t tL,
                  𝒟[(drawRc r >>= fun _rc =>
                      runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
                        (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ)
                          (simSendQFig Q pub m₀ (some m₁) _rc))
                        sC sent m' (s_cell t tL) >>= fun z =>
                        match z.1.1.1.1 with
                        | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
                        | some c =>
                          pure ((((some (CryptoGames.Ratchet.LibsignalSim.toWire c),
                            updSimStateCSend (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q
                              m₀ true s₁ pq' pn c sC), z.1.1.2), z.1.2), z.2)) >>=
                    fun w =>
                      cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
                        (u w.1.1.1.1) w.1.1.1.2
                        (if w.1.1.1.1.isSome then stepKemFailSend P.C.F K tr Q rq
                         else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })
                        w.1.1.2 w.1.2 w.2 >>=
                      fun z => pure (cellWinPred tL t z.2)] =
                  𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
                      cellChallPost (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀
                        (if m'.b then (pub, m₁) else (pub, m₀)) s₁ pq' pn sC sent m' m₁'
                        (fun w =>
                          cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
                            (u w.1.1.1.1) w.1.1.1.2
                            (if w.1.1.1.1.isSome then stepKemFailSend P.C.F K tr Q rq
                             else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })
                            w.1.1.2 w.1.2 w.2 >>=
                          fun z => pure (cellWinPred tL t z.2))
                        (if (s_cell t tL).win then (none, s_cell t tL)
                         else transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                           (cellDelta tL t) (qep + 1) Q
                           (if m'.b then (pub, m₁) else (pub, m₀)) coins false (s_cell t tL))] := by
              intro t tL
              rw [bind_assoc]
              exact evalDist_cell_chall_mkPub_some qep t tL
                (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ m₁ r s₁ pq' pub pn
                sC sent m' m₁' (s_cell t tL) hep_m hsafe_m _
            refine le_of_le_of_eq ?_
              (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun tL _ =>
                congrArg (fun μ => μ {true})
                  ((hcell_mk t tL).symm.trans
                  (by dsimp only [Option.isSome, pn]; simp only [bind_assoc]; rfl)))
            refine evalDist_bind_le_double_sum _ _ _ _ _ fun coins => ?_
            let m_ch := if m'.b then (pub, m₁) else (pub, m₀)
            let c := (fig.send (g₁.st Q) m_ch coins).2
            let st' := (fig.send (g₁.st Q) m_ch coins).1
            let rec_r : CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
              ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, m_ch, c⟩
            let m₂' := m₁'.record (2 + 1) Q () ⟨⟨Q, m₁'.epoch Q, m₁'.idx Q + 1⟩, m_ch, c⟩ true
            let s_cell₁ :
                ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
              fun t tL =>
                if (s_cell t tL).win then s_cell t tL
                else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
                  | some s₂ => s₂.record (cellDelta tL t) Q st' rec_r false
                  | none => s_cell t tL
            have hch_g := (challPure_eq_of_pprimePaperRelShifted fig (2 + 1) qep Q (pub, m₀)
              (pub, m₁) coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g hsafe_g hb_eq).1
            rw [hch_g]
            dsimp only
            let sC' := updSimStateCSend fig Q m₀ true s₁ pq' pn c sC
            let g' := g₁.record (2 + 1) Q st' rec_r true
            have hinv₁ : FirstNECellFamilyInvT qep false g' m₂' s_cell₁ := by
              refine Eq.ndrec (motive := fun f => FirstNECellFamilyInvT qep false g' m₂' f)
                (firstNECellFamilyInvT_chall_step (m₁' := m₂') fig qep Q m_ch coins r.isSome
                  (Or.inr ⟨rfl, hcol, hrel_all⟩) hep_g hsafe_g) ?_
              funext t tL
              dsimp only [s_cell₁, st', rec_r, c]
              cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;> rfl
            have hcoupled₁ :
                FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC' (c :: sent) m₂' g'
                  s_cell₁ := by
              rcases hinv₁ with hwin | ⟨_, hcol₁, hrel_all₁⟩
              · exact Or.inl hwin
              · have horig₁ : FirstNEInTransOriginInv qep sC'.snaps g' s_cell₁ :=
                  firstNEInTransOriginInv_send_step_of_cellFamily qep sC.snaps Q r.isSome true st'
                    m_ch c horig hrel_all hep_g hcorrs_le hsnap_idx
                obtain ⟨hcorrs_g₁, hst_g₁, hep_le_qep'⟩ :=
                  epMgmt_corrs_st_and_epoch_le hep_g hep_le_qep
                obtain ⟨s_R₁, g₁', _, hep_g', _, _, hmeta₁⟩ := hmeta.epMgmt_some Q qep r.isSome hep
                have hg₁_eq : g₁' = g₁ := Option.some.inj (hep_g'.symm.trans hep_g)
                subst g₁'
                have hmeta' : SameMeta
                    (s_R₁.record 3 Q (s_R₁.st Q)
                      ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m₀, CryptoGames.Ratchet.LibsignalSim.toWire c⟩ true)
                    sC'.base g' := by
                  simpa [sC', g', updSimStateCSend, hstop] using
                    hmeta₁.record_preserves Q (s_R₁.st Q) st' m₀ m₀ m_ch c true
                      (Function.update sC.base.pq Q pq') (Function.update sC.base.pn Q pn)
                      sC.base.unackA ((CryptoGames.Ratchet.LibsignalSim.toWire c, c) :: sC.base.honest)
                      sC.base.chains sC.base.amb
                obtain ⟨s_unsh₁, hep_u, _⟩ :=
                  (hrel_all 0 ht0).1.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
                obtain ⟨m₁'', hep_m', hmsync₁⟩ :=
                  hmsync.epMgmt_step (hrel_all 0 ht0).1.epoch_eq hep_g hep_u
                have hm₁_eq : m₁'' = m₁' := Option.some.inj (hep_m'.symm.trans hep_m)
                subst m₁''
                have hs_cell₁_0 : s_cell₁ 0 none = s_unsh₁.record (2 + 1) Q st' rec_r false := by
                  have hdelta0 : cellDelta none 0 = 2 + 1 := by simp [cellDelta]
                  dsimp only [s_cell₁]
                  simp only [(hrel_all 0 ht0).1.win_df_false, Bool.false_eq_true, ↓reduceIte,
                    hdelta0, hep_u]
                have hm₂'_eq : m₂' = m₁'.record (2 + 1) Q () rec_r true := by
                  dsimp only [m₂', rec_r]
                  rw [hmsync₁.epoch_eq, hmsync₁.idx_eq]
                have hmsync' : MirrorSync m₂' g' (s_cell₁ 0 none) := by
                  rw [hm₂'_eq, hs_cell₁_0]
                  exact hmsync₁.record_step Q st' rec_r true
                obtain ⟨hwf₁, hsends₁⟩ := CryptoGames.SM.Thm1L17.epMgmt_wf hwf_g hep_g
                have hwf_g' : CryptoGames.SM.Thm1L17.WFState 3 g' :=
                  CryptoGames.SM.Thm1L17.record_wf (by omega) hwf₁ rfl rfl rfl hsends₁ (fun _ => hsafe_g)
                have hkept' : KeptInv P Dh encPt encT idOf lam sC' g' :=
                  keptInv_send hkept Q (hid_st Q) m_ch coins
                    (by simp [g', CryptoGames.SM.GameState.record, st', hst_g₁, fig]) rfl
                obtain ⟨hsender_sync', hid_st'⟩ :=
                  fig8SenderSync_and_id_send_step P Dh encPt encT idOf lam qep Q m_ch coins
                    r.isSome true hsender_sync hid_st hwf_g hep_g
                have hkept_corr' : CorrsKeptRecvInv sC' g' :=
                  corrsKeptRecvInv_updSimStateCSend P Dh encPt encT idOf lam Q m₀ true s₁ pq' pn c
                    sC hkept_corr hkept hcorrs_le hsender_sync hcorrs_g₁
                exact Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol₁, hrel_all₁⟩, horig₁,
                  fun _ => ⟨_, hmeta'⟩,
                  hmsync',
                  hwf_g',
                  corrsLeEpoch_record_of_epMgmt st' rec_r true hcorrs_le hep_g hcorrs_g₁,
                  hep_le_qep',
                  corrsSnapIdxInv_record_of_epMgmt st' rec_r true hsnap_idx hcorrs_le hep_g
                    hcorrs_g₁ (Nat.le_succ (g₁.idx Q)),
                  corrsSnapsInv_of_corrs_eq hcorrs_snaps hcorrs_g₁,
                  hsender_sync',
                  hkept_corr',
                  hkept',
                  hid_st',
                  honestSentSync_cons Pt hhon_sent c⟩)
            refine le_trans
              (hih (some (CryptoGames.Ratchet.LibsignalSim.toWire c)) sC' g' false false
                (stepKemFailSend P.C.F K tr Q rq) (c :: sent) m₂' s_cell₁ hcoupled₁) ?_
            refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
            rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
            · dsimp only [s_cell₁]
              simp only [hdoomed.2.2.2, ↓reduceIte]
              have hcorrs_sub : ∀ x ∈ g.corrs, x ∈ g'.corrs := by
                unfold CryptoGames.SM.GameState.epMgmt at hep_g
                split_ifs at hep_g <;>
                  { injection hep_g with h; subst h; intro x hx; exact hx }
              rw [evalDist_cellSimRunTrackHalted_cellWinPred_eq_zero_of_doomed P K ℓ Dh encPt encT
                decT idOf lam qep t tL (u (some (CryptoGames.Ratchet.LibsignalSim.toWire c))) sC'
                (stepKemFailSend P.C.F K tr Q rq) (c :: sent) m₂'
                (hdoomed.of_corrs_sub hcorrs_sub)]
              exact zero_le
            · have htr_df := (challPure_eq_of_pprimePaperRelShifted fig (cellDelta tL t) qep Q
                (pub, m₀) (pub, m₁) coins r.isSome hrel_sh hep_g hsafe_g hb_eq).2
              dsimp only [cellChallPost, s_cell₁, sC', m₂', rec_r, c, st', m_ch, pn, fig]
              simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
              rw [htr_df]
              simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
              cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;>
                { dsimp only [Option.isSome]; simp only [↓reduceIte]; exact le_rfl }
        · simp only [↓reduceIte, pure_bind]
          exact hih none sC g false false
            { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
            sent m' s_cell hcoupled₀

/-! ## Cell-sum bound -/

theorem firstNECoupledInvD_halted_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hinv : FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell)
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range q_sm)
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
        𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL (u u₁)
            sC₁ tr₁ sent₁ m₁' (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) q_sm >>= u)).run
        (sC, (g, fl, dead), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) q_sm >>= u)
          sC tr sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hinv with hwin | ⟨hdead_t, hfl_f⟩ | ⟨hfl, hdead, hbody, horig, hsync⟩
  · exact le_trans MeasureTheory.prob_le_one
      (firstNECellFamilyInv_inl_one_le_sum_cell
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep CryptoGames.SM.Construction.DeliverForge.sameHdrScheme
        (fun _ _ => (simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
          (((simulateQ (simImplCTrackHalted P K encT decT qep
              (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
              (lFS P.C P.codec ℓ encT idOf 25000)
              (deliverForgeHook Pt ℓ) Dh)
            (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
              (BitVec 512) (List (BitVec 8))) q_sm >>= u)).run (sC, tr)).run sent)).run m')
        s_cell hwin)
  · subst hdead_t; subst hfl_f
    rw [evalDist_firstNEHalted'_dead_eq_zero P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) q_sm >>= u)
      sC g tr]
    exact zero_le
  · subst hfl; subst hdead
    rcases q_sm with n | q_game
    · rw [simulateQ_firstNEHalted'_inl_query_bind, bind_assoc]
      simp only [cellSimRunTrackHalted_inl_query_bind, bind_assoc]
      refine evalDist_bind_le_double_sum _ _ _ _ _ fun u₁ => ?_
      exact hih u₁ sC g false false tr sent m' s_cell
        (firstNECoupledInvD_unif_step (Or.inr (Or.inr ⟨rfl, rfl, hbody, horig, hsync⟩)))
    · rcases q_game with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · exact firstNECoupledInvD_transmit_halted_query_step P K InvPQ ℓ Dh encPt encT decT idOf
          lam qep q Q m₀ r u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_chall_halted_query_step P K InvPQ ℓ Dh encPt encT decT idOf
          lam qep q Q m₀ m₁ r u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_deliver_halted_query_step P K hspqr_eq InvPQ hInv_top ℓ Dh hDh
          encPt encT decT idOf hid hX hinj hdec lam qep q Q w u sC g tr sent m' s_cell hbody horig
          hsync hih
      · exact firstNECoupledInvD_inject_halted_query_step P K InvPQ ℓ Dh encPt encT decT idOf
          lam qep q Q w u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_corr_halted_query_step P K InvPQ ℓ Dh encPt encT decT idOf
          lam qep q Q u sC g tr sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_simulateQ_halted_le_sum {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl dead : Bool) (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
      (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, fl, dead), tr) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep t tL oa sC tr sent m'
            (s_cell t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC g fl dead tr sent m' s_cell hinv
    rcases hinv with hwin | ⟨_, hfl⟩ | ⟨hfl, _, _, _, _⟩
    · exact le_trans MeasureTheory.prob_le_one
        (firstNECellFamilyInv_inl_one_le_sum_cell
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep CryptoGames.SM.Construction.DeliverForge.sameHdrScheme
          (fun _ _ => (simulateQ (CryptoGames.SM.Construction.DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
            (((simulateQ (simImplCTrackHalted P K encT decT qep
                (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                (lFS P.C P.codec ℓ encT idOf 25000)
                (deliverForgeHook Pt ℓ) Dh) (pure a)).run (sC, tr)).run sent)).run m')
          s_cell hwin)
    · subst hfl
      simp [simulateQ_pure, StateT.run_pure]
    · subst hfl
      simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    intro sC g fl dead tr sent m' s_cell hinv
    exact firstNECoupledInvD_halted_query_step P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT
      decT idOf hid hX hinj hdec lam qep q q_sm u sC g fl dead tr sent m' s_cell hinv ih

/-- Bounds the bad-event probability of `firstNEHalted'` from initial state by the sum of
`forgeGuessedAdvantageCellPaper` over `admissibleLastLeakGuesses 2`. -/
theorem evalDist_simulateQ_firstNEHalted'_le_sum_cells
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.LibsignalSM.LibAdv (List (BitVec 8)) (BitVec 512) ℓ) :
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let ghd₀ := (CryptoGames.SM.initState fig k b, false, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
          (sC₀, ghd₀, tr₀)
      return z.2.2.1.2.1] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 t,
      CryptoGames.SM.Construction.DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (qep + 1) CryptoGames.SM.Construction.DeliverForge.sameHdrScheme tL t
        (CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A)) := by
  simp_rw [deliverForge_forgeGuessedAdvantageCellPaper_eq,
    forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeTrackHalted_eq]
  refine evalDist_bind_le_double_sum _ _ _ _ _ fun b => ?_
  refine evalDist_bind_le_double_sum _ _ _ _ _ fun k => ?_
  refine evalDist_bind_le_double_sum _ _ _ _ _ fun pqrKey => ?_
  exact firstNECoupledInvD_simulateQ_halted_le_sum P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT
    decT idOf hid hX hinj hdec lam qep q A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) false false
    (initKemFailTrack P.C.F pqrKey) []
    { st := fun _ => (), b }
    (fun _ _ => CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
    (firstNECoupledInvD_init P ℓ Dh encPt encT idOf lam qep b k pqrKey)

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedCouple
