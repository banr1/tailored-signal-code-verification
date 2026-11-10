/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit2
import ProofLib.SepLogic.WP.StateNorm

/-!
# Coupled Origin Invariant and Send/Corruption Preservation

Defines `CorrsSnapIdxInv`, `CorrsKeptRecvInv`, `Fig8SenderSync`, and `FirstNECoupledOriginInvT`, and
proves send- and corruption-step preservation of the coupled origin invariant.
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

/-- Every sender corruption `(P, e) ∈ g.corrs` with `P.sendsIn e = true` has a snapshot
`(P, e, g₀) ∈ snaps` whose sender chain has `sc.chainKey.index.toNat ≤ g.idx P` when
`g.epoch P = e`. -/
def CorrsSnapIdxInv {PQ St Msg C : Type}
    (snaps : List (Party × ℕ × GhostState PQ))
    (g : SM.GameState St Msg C) : Prop :=
  ∀ P e, (P, e) ∈ g.corrs → P.sendsIn e = true →
    ∃ g₀ sc, (P, e, g₀) ∈ snaps ∧ g₀.session.senderChain = some sc ∧
      (g.epoch P = e → sc.chainKey.index.toNat ≤ g.idx P)

/-- Receiver-corruption kept-state invariant: whenever `(Q, e) ∈ g.corrs`,
every receiving epoch `t ≤ e` of `Q` (`Q.sendsIn t = false`) is covered by `sC.kept Q`
(either `(sC.kept Q).full` is `some _` or `(sC.kept Q).rs t` is `some _`). -/
def CorrsKeptRecvInv {Pt PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  ∀ Q e, (Q, e) ∈ g.corrs → ∀ t ≤ e, Q.sendsIn t = false →
    (sC.kept Q).full.isSome = true ∨ ((sC.kept Q).rs t).isSome = true

/-- Fig. 8 state-to-metadata synchronization invariant on `g`. -/
structure Fig8SenderSync {Pt : Type} {ℓ : ℕ}
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop where
  htcur : ∀ P, (g.st P).tcur = g.epoch P
  hvS : ∀ P, P.sendsIn (g.epoch P) = true →
    ∃ x v, (g.st P).γ = .exp x ∧ (g.st P).vS = some v ∧ v.lastIndex = g.idx P
  hvR : ∀ Q t, ((g.st Q).vR t).isSome ↔ (t ≤ (g.st Q).tcur ∧ Q.sendsIn t = false)

theorem firstNEInTransOriginInv_send_step_of_cellFamily
    {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} (qep : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ))
    (P : Party) (bad isChall : Bool)
    (st' : Fig8St Pt) (m_msg : LibsignalMsgPublicPart × Plain ℓ) (c : Fig8C Pt)
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : FirstNEInTransOriginInv qep snaps g s_cell)
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁)
    (hcorrs_le_ep : CorrsLeEpoch g)
    (hsnap_idx : CorrsSnapIdxInv snaps g) :
    let rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      ⟨⟨P, g₁.epoch P, g₁.idx P + 1⟩, m_msg, c⟩
    let g' := g₁.record (2 + 1) P st' rec_r isChall
    let s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL =>
        if (s_cell t tL).win then s_cell t tL
        else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) P false with
          | some s₁ => s₁.record (cellDelta tL t) P st' rec_r false
          | none => s_cell t tL
    FirstNEInTransOriginInv qep snaps g' s_cell' := by
  intro rec_r g' s_cell'
  have hcorrs_g₁ : g₁.corrs = g.corrs := by
    obtain ⟨s_u₁, hep_u, hrel_u₁⟩ := (hcell 0 (Finset.mem_range.mpr (by omega))).1.epMgmt_step
      (Δ := 2 + 1) (m₁' := m') hep_g
    have h1 : (s_cell 0 none).corrs = s_u₁.corrs := by
      unfold SM.GameState.epMgmt at hep_u
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hep_u
      split_ifs at hep_u <;> { injection hep_u with hu; subst hu; rfl }
    rw [← hrel_u₁.corrs_eq, ← h1, (hcell 0 (Finset.mem_range.mpr (by omega))).1.corrs_eq]
  have hcorrs_g' : g'.corrs = g.corrs := hcorrs_g₁
  refine firstNEInTransOriginInv_send_step qep snaps rec_r hinv
    (fun p hp => hcorrs_g'.symm ▸ hp) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t _ r hr
    dsimp only [s_cell'] at hr
    split_ifs at hr with hw
    · exact Or.inl hr
    · cases hep : (s_cell t none).epMgmt (cellDelta none t) (qep + 1) P false <;>
        rw [hep] at hr
      · exact Or.inl hr
      · rename_i s₁
        have htrans : s₁.trans = (s_cell t none).trans :=
          (epMgmt_false_tL_leaks_comp hep).2.2.2
        unfold SM.GameState.record at hr
        rcases List.mem_cons.mp hr with rfl | hr_old
        · exact Or.inr rfl
        · exact Or.inl (htrans ▸ hr_old)
  · intro t _
    dsimp only [s_cell']
    split_ifs with hw
    · rfl
    · cases hep : (s_cell t none).epMgmt (cellDelta none t) (qep + 1) P false
      · rfl
      · exact record_canon_eq_of_epMgmt_false hep t
  · intro t ht r hr_old hfalse
    rcases hcell t ht with ⟨hrel_none, hwf_none, _⟩
    obtain ⟨s_unsh₁, hep_unsh, hrel_unsh₁⟩ :=
      hrel_none.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
    have hrec_pos : rec_r.pos = ⟨P, s_unsh₁.epoch P, s_unsh₁.idx P + 1⟩ := by
      simp [rec_r, congrFun hrel_unsh₁.epoch_eq P, congrFun hrel_unsh₁.idx_eq P]
    have hne := pos_ne_of_mem_trans_epMgmt hep_unsh hwf_none hr_old hrec_pos
    dsimp only [s_cell']
    split_ifs with hw
    · exact hfalse
    · cases hep : (s_cell t none).epMgmt (cellDelta none t) (qep + 1) P false
      · exact hfalse
      · rw [record_comp_contains_of_pos_ne hep hne]
        exact hfalse
  · intro t ht r hr_old hfalse
    rcases hcell t ht with ⟨hrel_none, hwf_none, _⟩
    obtain ⟨s_unsh₁, hep_unsh, hrel_unsh₁⟩ :=
      hrel_none.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
    have hrec_pos : rec_r.pos = ⟨P, s_unsh₁.epoch P, s_unsh₁.idx P + 1⟩ := by
      simp [rec_r, congrFun hrel_unsh₁.epoch_eq P, congrFun hrel_unsh₁.idx_eq P]
    have hne := pos_ne_of_mem_trans_epMgmt hep_unsh hwf_none hr_old hrec_pos
    dsimp only [s_cell']
    split_ifs with hw
    · exact hfalse
    · cases hep : (s_cell t (some (t - 3))).epMgmt (cellDelta (some (t - 3)) t) (qep + 1) P false
      · exact hfalse
      · rw [record_comp_contains_of_pos_ne hep hne]
        exact hfalse
  · intro t ht r hr_old hfalse
    rcases hcell t ht with ⟨hrel_none, hwf_none, _⟩
    obtain ⟨s_unsh₁, hep_unsh, hrel_unsh₁⟩ :=
      hrel_none.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
    have hrec_pos : rec_r.pos = ⟨P, s_unsh₁.epoch P, s_unsh₁.idx P + 1⟩ := by
      simp [rec_r, congrFun hrel_unsh₁.epoch_eq P, congrFun hrel_unsh₁.idx_eq P]
    have hne := pos_ne_of_mem_trans_epMgmt hep_unsh hwf_none hr_old hrec_pos
    dsimp only [s_cell']
    split_ifs with hw
    · exact hfalse
    · cases hep : (s_cell t (some (t - 2))).epMgmt (cellDelta (some (t - 2)) t) (qep + 1) P false
      · exact hfalse
      · rw [record_comp_contains_of_pos_ne hep hne]
        exact hfalse
  · intro t ht hr_ep
    have ht_ep : g₁.epoch P = t := hr_ep
    rcases send_fresh_record_origin_or_pre_corr qep t P bad st' rec_r (hcell t ht) hep_g
        ht_ep hr_ep hcorrs_le_ep with
      hk4 | hw1 | hw2 | hcu | hb2 | ⟨ht2, hcorr_tm2, hcb1⟩
    · rcases hcell t ht with ⟨hrel_none, hwf_none, _⟩
      obtain ⟨s_unsh₁, hep_unsh, hrel_unsh₁⟩ :=
        hrel_none.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
      have ht_unsh : s_unsh₁.epoch P = t := (congrFun hrel_unsh₁.epoch_eq P).trans ht_ep
      have hsend_t : P.sendsIn t = true :=
        ht_unsh ▸ (SM.Thm1L17.epMgmt_wf hwf_none hep_unsh).2
      have hP_sender : P = Party.senderOf t := party_eq_senderOf_of_sendsIn hsend_t
      have ht_le_ep : t ≤ g.epoch P := hP_sender ▸ hcorrs_le_ep (Party.senderOf t) t hk4
      have hep_le_t : g.epoch P ≤ t := ht_ep ▸ epMgmt_epoch_le hep_g
      have hep_eq : g.epoch P = t := le_antisymm hep_le_t ht_le_ep
      have hidx_eq : g₁.idx P = g.idx P :=
        epMgmt_idx_eq_of_epoch_eq hep_g (ht_ep.trans hep_eq.symm)
      rcases hsnap_idx (Party.senderOf t) t hk4 (hP_sender ▸ hsend_t) with
        ⟨g₀, sc, hg₀, hsc, hsc_le⟩
      have hsc_lt : sc.chainKey.index.toNat < rec_r.pos.idx := by
        have hle : sc.chainKey.index.toNat ≤ g.idx P :=
          hP_sender ▸ hsc_le (hP_sender ▸ hep_eq)
        dsimp only [rec_r]
        omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hcorrs_g'.symm ▸ hk4, g₀, sc, hg₀, hsc, hsc_lt⟩))))
    · exact Or.inl (hcorrs_g'.symm ▸ hw1)
    · exact Or.inr (Or.inl (hcorrs_g'.symm ▸ hw2))
    · exact Or.inr (Or.inr (Or.inl hcu))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht2, hcorrs_g'.symm ▸ hcorr_tm2, hcb1⟩))))

/-- Disjunction of the post-divergence winning branch and the pre-divergence
`FirstNECellFamilyInvT` and `FirstNEInTransOriginInv` invariants. -/
def FirstNECoupledOriginInvT {PQ St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (snaps : List (Party × ℕ × GhostState PQ))
    (fl : Bool) (g : SM.GameState St Msg C) (m' : Mirror Msg C)
    (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  (∃ t ∈ Finset.range ((qep + 1) + 2), ∃ tL ∈ SM.admissibleLastLeakGuesses 2 t,
    cellWinPred tL t (s_cell t tL) = true) ∨
  (fl = false ∧
    (∀ t₁ ∈ Finset.range ((qep + 1) + 2), ∀ t₂ ∈ Finset.range ((qep + 1) + 2),
      s_cell t₁ none = s_cell t₂ none) ∧
    (∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL))) ∧
    FirstNEInTransOriginInv qep snaps g s_cell)

theorem FirstNECoupledOriginInvT.of_cellFamilyInvT_and_origin
    {PQ St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {qep : ℕ} {snaps : List (Party × ℕ × GhostState PQ)}
    {fl : Bool} {g : SM.GameState St Msg C} {m' : Mirror Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hcell : FirstNECellFamilyInvT qep fl g m' s_cell)
    (horigin : FirstNEInTransOriginInv qep snaps g s_cell) :
    FirstNECoupledOriginInvT qep snaps fl g m' s_cell := by
  rcases hcell with hwin | ⟨hfl, hcol, hrel_all⟩
  · exact Or.inl hwin
  · exact Or.inr ⟨hfl, hcol, hrel_all, horigin⟩

theorem firstNECoupledOriginInvT_corr_step
    {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} (qep : ℕ) (P : Party)
    {snaps snaps' : List (Party × ℕ × GhostState PQ)}
    {fl : Bool} {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : FirstNECoupledOriginInvT qep snaps fl g m' s_cell)
    (hsnaps : ∀ snap ∈ snaps, snap ∈ snaps')
    (hallow_g : g.corrAllowed P = true) :
    FirstNECoupledOriginInvT qep snaps' fl (g.afterCorr P) (m'.afterCorr P)
      (fun t tL => if (s_cell t tL).win then s_cell t tL
        else DeliverForge.afterCorrShifted (cellShift tL t) (s_cell t tL) P) := by
  rcases hinv with ⟨t, ht, tL, htL, hwin⟩ | ⟨hfl, hcol, hrel_all, horigin⟩
  · refine Or.inl ⟨t, ht, tL, htL, ?_⟩
    have hswin : (s_cell t tL).win = true := s_win_of_cellWinPred hwin
    dsimp only; simp only [hswin, ↓reduceIte]; exact hwin
  · exact FirstNECoupledOriginInvT.of_cellFamilyInvT_and_origin
      (firstNECellFamilyInvT_corr_step qep P (Or.inr ⟨hfl, hcol, hrel_all⟩) hallow_g)
      (firstNEInTransOriginInv_corr_step qep P horigin hsnaps hrel_all)

end CryptoVerification.LibsignalSession.HeadlineV1
end
