/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit
import ProofLib.SepLogic.WP.StateNorm
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- shake: keep
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep

/-!
# Corruption-Window Unpacking and Origin Invariant Preservation

Unpacks the `fwdCPure` probe flag into deliver-time corruption-window constraints and proves
per-oracle preservation of `FirstNEInTransOriginInv`.
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
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem fwdCPure_flag_true_imp_evalCK_none
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfl : (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c'
      (sC, (g, false))).2.2.2 = true) :
    ∃ c, honestC = some c ∧
      predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = none := by
  unfold fwdCPure at hfl; dsimp only at hfl
  cases honestC with
  | none => simp at hfl
  | some c =>
    dsimp only at hfl; split at hfl
    · cases hev : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' with
      | none => exact ⟨c, rfl, hev⟩
      | some r_ev =>
        rw [hev] at hfl
        rcases r_ev with _ | ⟨t, i, pm⟩
        · simp at hfl
        · dsimp only at hfl; split at hfl <;> simp at hfl
    · simp at hfl

theorem honest_mem_and_sender_of_find_map_some
    {Pt : Type} {honest : List (List (BitVec 8) × Fig8C Pt)}
    {Q : Party} {w : List (BitVec 8)} {c : Fig8C Pt}
    (hfind : (honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) =
      some c) :
    (w, c) ∈ honest ∧ Party.senderOf c.1.1 = Q.other := by
  rw [Option.map_eq_some_iff] at hfind
  rcases hfind with ⟨⟨w', c'⟩, hfind_eq, rfl⟩
  have hmem := List.mem_of_find?_eq_some hfind_eq
  have hpred := List.find?_some hfind_eq
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  rw [hpred.1] at hmem
  exact ⟨hmem, hpred.2⟩

theorem hw3_of_snaps_no_corr_window
    {PQ : Type} {snaps : List (Party × ℕ × GhostState PQ)}
    {Q : Party} {t' i' ctr : ℕ}
    (hsnd_eq : Party.senderOf t' = Q.other) (hi' : i' = ctr + 1)
    (hs3 : ∀ g₀ sc, (Q.other, t', g₀) ∈ snaps →
      g₀.session.senderChain = some sc → ctr < sc.chainKey.index.toNat) :
    ∀ g₀ sc, (Party.senderOf t', t', g₀) ∈ snaps →
      g₀.session.senderChain = some sc → i' ≤ sc.chainKey.index.toNat := by
  intro g₀ sc hmem hsc
  rw [hsnd_eq] at hmem
  have hlt := hs3 g₀ sc hmem hsc
  omega

@[simp]
theorem afterCorr_trans_eq {St Msg C : Type} (s : SM.GameState St Msg C) (P : Party) :
    (s.afterCorr P).trans = s.trans := rfl

@[simp]
theorem afterCorrShifted_trans_eq {St Msg C : Type} (sh : ℕ) (s : SM.GameState St Msg C)
    (P : Party) :
    (DeliverForge.afterCorrShifted sh s P).trans = s.trans := by
  unfold DeliverForge.afterCorrShifted SM.GameState.leak
  split <;> rfl

theorem afterCorrShifted_comp_contains_of_sender_ne {St Msg C : Type} (sh : ℕ)
    (s : SM.GameState St Msg C) (P : Party) (pos : SM.Pos) (hne : pos.sender ≠ P.other) :
    (DeliverForge.afterCorrShifted sh s P).comp.contains pos = s.comp.contains pos := by
  have hnot_new : pos ∉ List.map (fun r => r.pos)
      (List.filter (fun r => r.pos.sender == P.other) s.trans) := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨r₀, hr₀, rfl⟩
    have hflt := (List.mem_filter.mp hr₀).2
    simp only [beq_iff_eq] at hflt
    exact hne hflt
  unfold DeliverForge.afterCorrShifted SM.GameState.leak
  split <;>
  · dsimp only
    rw [List.contains_eq_mem, List.contains_eq_mem]
    simp only [List.mem_append, hnot_new, false_or]

theorem canon_afterCorr_eq_of_le_max {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (s : SM.GameState St Msg C) (P : Party)
    {t : ℕ} (ht : t ≤ max (s.epoch .A) (s.epoch .B)) :
    SM.canon t (s.afterCorr P) = SM.canon t s := by
  have h1 : SM.canon t (s.afterCorr P) =
      SM.canon t (s.leak (max (s.epoch .A) (s.epoch .B))) := rfl
  rw [h1, SM.Thm1L17.canon_leak_of_le ht]

theorem firstNEInTransOriginInv_corr_step
    {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} (qep : ℕ) (P : Party)
    {snaps snaps' : List (Party × ℕ × GhostState PQ)}
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : FirstNEInTransOriginInv qep snaps g s_cell)
    (hsnaps : ∀ snap ∈ snaps, snap ∈ snaps')
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL))) :
    FirstNEInTransOriginInv qep snaps' (g.afterCorr P)
      (fun t tL => if (s_cell t tL).win then s_cell t tL
        else DeliverForge.afterCorrShifted (cellShift tL t) (s_cell t tL) P) := by
  intro t ht r hr_mem hr_ep
  rcases hcell t ht with ⟨hrel_u, hwf_u, _⟩
  have hr_old : r ∈ (s_cell t none).trans := by
    dsimp only at hr_mem
    split_ifs at hr_mem with hwin
    · exact hr_mem
    · rwa [afterCorrShifted_trans_eq] at hr_mem
  have ht_le_sender : t ≤ (s_cell t none).epoch r.pos.sender :=
    hr_ep ▸ hwf_u.trans_epoch_le r hr_old
  have hsender_le_rcv :
      (s_cell t none).epoch r.pos.sender ≤ (s_cell t none).epoch (Party.receiverOf t) + 1 :=
    hwf_u.epoch_le_any_add_one r.pos.sender (Party.receiverOf t)
  by_cases hP : P = Party.receiverOf t
  · subst hP
    refine Or.inl ⟨g.epoch (Party.receiverOf t), ?_, ?_⟩
    · simp [SM.GameState.afterCorr]
    · have hep_eq : (s_cell t none).epoch (Party.receiverOf t) = g.epoch (Party.receiverOf t) :=
        congrFun hrel_u.epoch_eq (Party.receiverOf t)
      omega
  · have hrec_eq : Party.receiverOf t = r.pos.sender.other := by
      rw [← hr_ep]
      exact SM.Thm1L17.receiverOf_eq_other_of_sendsIn (hwf_u.trans_sender r hr_old)
    have hne_other : r.pos.sender ≠ P.other := by
      intro heq
      apply hP
      rw [hrec_eq, heq, Party.other_other]
    have hcorrs_sub : ∀ p ∈ g.corrs, p ∈ (g.afterCorr P).corrs :=
      fun p hp => List.mem_cons_of_mem _ hp
    have hcomp_pres : ∀ tL,
        (if (s_cell t tL).win then s_cell t tL
          else DeliverForge.afterCorrShifted (cellShift tL t) (s_cell t tL) P).comp.contains r.pos =
        (s_cell t tL).comp.contains r.pos := by
      intro tL
      split_ifs
      · rfl
      · exact afterCorrShifted_comp_contains_of_sender_ne _ _ P r.pos hne_other
    rcases hinv t ht r hr_old hr_ep with
      ⟨e, hce, hlt⟩ | ⟨e, hce, heq⟩ | hcu | ⟨ht3, hcan, hcb2⟩ |
      ⟨ht2, hcorr_tm2, hcb1⟩ | ⟨hcorr_t, g₀, sc, hg₀, hsc, hidx⟩
    · exact Or.inl ⟨e, hcorrs_sub _ hce, hlt⟩
    · exact Or.inr (Or.inl ⟨e, hcorrs_sub _ hce, heq⟩)
    · right; right; left
      dsimp only; rw [hcomp_pres none]; exact hcu
    · right; right; right; left
      have ht_le_max : t ≤ max ((s_cell t none).epoch .A) ((s_cell t none).epoch .B) :=
        ht_le_sender.trans (hwf_u.epoch_le_max r.pos.sender)
      have hcan' : SM.canon t (if (s_cell t none).win then s_cell t none
          else DeliverForge.afterCorrShifted (cellShift none t) (s_cell t none) P) =
          some (t - 2) := by
        have hsh0 : cellShift none t = 0 := by simp [cellShift]
        simp only [hrel_u.win_df_false, Bool.false_eq_true, ↓reduceIte, hsh0,
          afterCorrShifted_zero_eq_afterCorr]
        rw [canon_afterCorr_eq_of_le_max (s_cell t none) P ht_le_max]
        exact hcan
      refine ⟨ht3, hcan', ?_⟩
      dsimp only; rw [hcomp_pres (some (t - 3))]; exact hcb2
    · right; right; right; right; left
      refine ⟨ht2, hcorrs_sub _ hcorr_tm2, ?_⟩
      dsimp only; rw [hcomp_pres (some (t - 2))]; exact hcb1
    · right; right; right; right; right
      exact ⟨hcorrs_sub _ hcorr_t, g₀, sc, hsnaps _ hg₀, hsc, hidx⟩

theorem firstNEInTransOriginInv_send_step
    {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ))
    {g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (r₀ : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hinv : FirstNEInTransOriginInv qep snaps g s_cell)
    (hcorrs : ∀ p ∈ g.corrs, p ∈ g'.corrs)
    (htrans : ∀ t ∈ Finset.range ((qep + 1) + 2),
      ∀ r ∈ (s_cell' t none).trans, r ∈ (s_cell t none).trans ∨ r = r₀)
    (hcanon_eq : ∀ t ∈ Finset.range ((qep + 1) + 2),
      SM.canon t (s_cell' t none) = SM.canon t (s_cell t none))
    (hcomp_u : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ r ∈ (s_cell t none).trans,
      (s_cell t none).comp.contains r.pos = false →
      (s_cell' t none).comp.contains r.pos = false)
    (hcomp_b2 : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ r ∈ (s_cell t none).trans,
      (s_cell t (some (t - 3))).comp.contains r.pos = false →
      (s_cell' t (some (t - 3))).comp.contains r.pos = false)
    (hcomp_b1 : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ r ∈ (s_cell t none).trans,
      (s_cell t (some (t - 2))).comp.contains r.pos = false →
      (s_cell' t (some (t - 2))).comp.contains r.pos = false)
    (hr₀ : ∀ t ∈ Finset.range ((qep + 1) + 2), r₀.pos.epoch = t →
      (∃ e, (Party.receiverOf t, e) ∈ g'.corrs ∧ ¬(e + 3 ≤ t)) ∨
      (∃ e, (Party.senderOf t, e) ∈ g'.corrs ∧ t = e + 1) ∨
      (s_cell' t none).comp.contains r₀.pos = false ∨
      (3 ≤ t ∧ SM.canon t (s_cell' t none) = some (t - 2) ∧
        (s_cell' t (some (t - 3))).comp.contains r₀.pos = false) ∨
      (2 ≤ t ∧ (Party.senderOf t, t - 2) ∈ g'.corrs ∧
        (s_cell' t (some (t - 2))).comp.contains r₀.pos = false) ∨
      ((Party.senderOf t, t) ∈ g'.corrs ∧
        ∃ g₀ sc, (Party.senderOf t, t, g₀) ∈ snaps ∧
          g₀.session.senderChain = some sc ∧ sc.chainKey.index.toNat < r₀.pos.idx)) :
    FirstNEInTransOriginInv qep snaps g' s_cell' := by
  intro t ht r hr_mem hr_ep
  rcases htrans t ht r hr_mem with hr_old | rfl
  · rcases hinv t ht r hr_old hr_ep with
      ⟨e, hce, hlt⟩ | ⟨e, hce, heq⟩ | hcu | ⟨ht3, hcan, hcb2⟩ |
      ⟨ht2, hcorr_tm2, hcb1⟩ | ⟨hcorr_t, g₀, sc, hg₀, hsc, hidx⟩
    · exact Or.inl ⟨e, hcorrs _ hce, hlt⟩
    · exact Or.inr (Or.inl ⟨e, hcorrs _ hce, heq⟩)
    · exact Or.inr (Or.inr (Or.inl (hcomp_u t ht r hr_old hcu)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ht3, (hcanon_eq t ht).trans hcan, hcomp_b2 t ht r hr_old hcb2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ht2, hcorrs _ hcorr_tm2, hcomp_b1 t ht r hr_old hcb1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hcorrs _ hcorr_t, g₀, sc, hg₀, hsc, hidx⟩))))
  · exact hr₀ t ht hr_ep

theorem firstNEOriginAt_of_corrs_window_and_inTransOriginInv
    {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} (qep : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ))
    (Q : Party) (c : Fig8C Pt)
    (rec_f : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (t' i' : ℕ)
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hw1 : ∀ e, (Party.receiverOf t', e) ∈ g.corrs → e + 3 ≤ t')
    (hw2 : ∀ e, (Party.senderOf t', e) ∈ g.corrs → t' ≠ e + 1)
    (hw3 : ∀ g₀ sc, (Party.senderOf t', t', g₀) ∈ snaps →
      g₀.session.senderChain = some sc → rec_f.pos.idx ≤ sc.chainKey.index.toNat)
    (hw4 : 2 ≤ t' → ¬((Party.senderOf t', t' - 2) ∈ g.corrs ∧ (Party.senderOf t', t') ∈ g.corrs))
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (hreach : FirstNEInTransOriginInv qep snaps g s_cell)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some rec_f)
    (hr_pos : rec_f.pos = ⟨Q.other, t', i'⟩) :
    FirstNEOriginAt Q t' rec_f g s_cell := by
  have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := by
    rw [Finset.mem_range]; omega
  rcases hcell t' ht'_mem with ⟨hrel_unsh, _, _⟩
  rcases mem_trans_and_epoch_eq_of_inTransit hrel_unsh hin_g hr_pos with ⟨hr_mem, hr_ep⟩
  rcases hreach t' ht'_mem rec_f hr_mem hr_ep with
    ⟨e, hce, hlt⟩ | ⟨e, hce, heq⟩ | hcomp_u | h_b2 |
    ⟨ht2, hcorr_tm2, hcomp_b1⟩ | ⟨_, g₀, sc, hg₀, hsc, hlt⟩
  · exact False.elim (hlt (hw1 e hce))
  · exact False.elim (hw2 e hce heq)
  · exact Or.inr (Or.inr (Or.inl hcomp_u))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_b2)))
  · have hk4_b1 := (k4Free_at_deliver_and_not_cellK4Doomed_b1_of_w4
      (s_cell := s_cell) (hw4 ht2) hcorr_tm2).1
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht2, hk4_b1, hcomp_b1⟩)))
  · exact False.elim (Nat.not_lt.mpr (hw3 g₀ sc hg₀ hsc) hlt)

theorem accept_comp_contains_false {St Msg C : Type}
    (s : SM.GameState St Msg C) (Q : Party) (st' : St) (pos p : SM.Pos)
    (h : s.comp.contains p = false) :
    (s.accept Q st' pos).comp.contains p = false := by
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  rw [List.contains_eq_mem, decide_eq_false_iff_not] at h ⊢
  intro hp
  exact h (List.mem_of_mem_filter hp)

@[simp]
theorem accept_canon_eq {St Msg C : Type}
    (t : ℕ) (s : SM.GameState St Msg C) (Q : Party) (st' : St) (pos : SM.Pos) :
    SM.canon t (s.accept Q st' pos) = SM.canon t s := rfl

theorem firstNEInTransOriginInv_accept_step
    {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party) (st' : Fig8St Pt) (pos : SM.Pos)
    (snaps : List (Party × ℕ × GhostState PQ))
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : FirstNEInTransOriginInv qep snaps g s_cell) :
    let s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL =>
        if (s_cell t tL).win then s_cell t tL
        else (s_cell t tL).accept Q st' pos
    FirstNEInTransOriginInv qep snaps (g.accept Q st' pos) s_cell' := by
  intro s_cell' t ht r hr_mem hr_ep
  have hr_old : r ∈ (s_cell t none).trans := by
    dsimp only [s_cell'] at hr_mem
    split_ifs at hr_mem with hwin
    · exact hr_mem
    · exact List.mem_of_mem_filter hr_mem
  have hcomp_pres : ∀ tL, (s_cell t tL).comp.contains r.pos = false →
      (s_cell' t tL).comp.contains r.pos = false := by
    intro tL hfalse
    dsimp only [s_cell']
    split_ifs with hwin
    · exact hfalse
    · exact accept_comp_contains_false (s_cell t tL) Q st' pos r.pos hfalse
  have hcanon_pres : SM.canon t (s_cell' t none) = SM.canon t (s_cell t none) := by
    dsimp only [s_cell']
    split_ifs <;> rfl
  rcases hinv t ht r hr_old hr_ep with
    ⟨e, hce, hlt⟩ | ⟨e, hce, heq⟩ | hcu | ⟨ht3, hcan, hcb2⟩ |
    ⟨ht2, hcorr_tm2, hcb1⟩ | ⟨hcorr_t, g₀, sc, hg₀, hsc, hidx⟩
  · exact Or.inl ⟨e, hce, hlt⟩
  · exact Or.inr (Or.inl ⟨e, hce, heq⟩)
  · exact Or.inr (Or.inr (Or.inl (hcomp_pres none hcu)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht3, hcanon_pres.trans hcan,
      hcomp_pres (some (t - 3)) hcb2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨ht2, hcorr_tm2, hcomp_pres (some (t - 2)) hcb1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hcorr_t, g₀, sc, hg₀, hsc, hidx⟩))))

theorem firstNEInTransOriginInv_inject_step
    {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} (qep : ℕ) (Q : Party) (st' : Fig8St Pt) (t' i' : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ))
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : FirstNEInTransOriginInv qep snaps g s_cell) :
    let pos : SM.Pos := ⟨Q.other, t', i'⟩
    let g' := if g.trivial (2 + 1) pos then g.accept Q st' pos else { g with win := true }
    let s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL =>
        if (s_cell t tL).win then s_cell t tL
        else if cellTrivialT tL t (s_cell t tL) pos then
          (s_cell t tL).accept Q st' pos
        else if t' == t then { s_cell t tL with win := true }
        else s_cell t tL
    FirstNEInTransOriginInv qep snaps g' s_cell' := by
  intro pos g' s_cell' t ht r hr_mem hr_ep
  have hcorrs_eq : g'.corrs = g.corrs := by
    dsimp only [g']; split_ifs <;> rfl
  have hr_old : r ∈ (s_cell t none).trans := by
    dsimp only [s_cell'] at hr_mem
    split_ifs at hr_mem
    · exact hr_mem
    · exact List.mem_of_mem_filter hr_mem
    · exact hr_mem
    · exact hr_mem
  have hcomp_pres : ∀ tL, (s_cell t tL).comp.contains r.pos = false →
      (s_cell' t tL).comp.contains r.pos = false := by
    intro tL hfalse
    dsimp only [s_cell']
    split_ifs
    · exact hfalse
    · exact accept_comp_contains_false (s_cell t tL) Q st' pos r.pos hfalse
    · exact hfalse
    · exact hfalse
  have hcanon_pres : SM.canon t (s_cell' t none) = SM.canon t (s_cell t none) := by
    dsimp only [s_cell']
    split_ifs <;> rfl
  rcases hinv t ht r hr_old hr_ep with
    ⟨e, hce, hlt⟩ | ⟨e, hce, heq⟩ | hcu | ⟨ht3, hcan, hcb2⟩ |
    ⟨ht2, hcorr_tm2, hcb1⟩ | ⟨hcorr_t, g₀, sc, hg₀, hsc, hidx⟩
  · exact Or.inl ⟨e, hcorrs_eq ▸ hce, hlt⟩
  · exact Or.inr (Or.inl ⟨e, hcorrs_eq ▸ hce, heq⟩)
  · exact Or.inr (Or.inr (Or.inl (hcomp_pres none hcu)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht3, hcanon_pres.trans hcan,
      hcomp_pres (some (t - 3)) hcb2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht2, hcorrs_eq ▸ hcorr_tm2,
      hcomp_pres (some (t - 2)) hcb1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hcorrs_eq ▸ hcorr_t, g₀, sc, hg₀, hsc, hidx⟩))))

theorem epMgmt_false_tL_leaks_comp {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P₀ : Party}
    (h : s.epMgmt Δ qep P₀ false = some s₁) :
    s₁.tL = s.tL ∧ s₁.leaks = s.leaks ∧ s₁.comp = s.comp ∧ s₁.trans = s.trans := by
  unfold SM.GameState.epMgmt at h
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem record_canon_eq_of_epMgmt_false {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P₀ : Party} {st' : St} {rec_r : SM.Record Msg C} {win : Bool}
    (h : s.epMgmt Δ qep P₀ false = some s₁) (e : ℕ) :
    SM.canon e (s₁.record Δ P₀ st' rec_r win) = SM.canon e s := by
  have htl := (epMgmt_false_tL_leaks_comp h).2.1
  simp [SM.canon, SM.GameState.record, htl]

theorem record_comp_contains_of_pos_ne {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P₀ : Party} {st' : St} {rec_r : SM.Record Msg C} {win : Bool}
    {pos : SM.Pos}
    (h : s.epMgmt Δ qep P₀ false = some s₁)
    (hne : pos ≠ rec_r.pos) :
    (s₁.record Δ P₀ st' rec_r win).comp.contains pos = s.comp.contains pos := by
  have hcomp := (epMgmt_false_tL_leaks_comp h).2.2.1
  have hbeq : (pos == rec_r.pos) = false := beq_false_of_ne hne
  dsimp [SM.GameState.record]
  split
  · exact congrArg (·.contains pos) hcomp
  · simp only [List.contains_cons, hbeq, Bool.false_or, hcomp]

theorem pos_ne_of_mem_trans_epMgmt {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P₀ : Party} {r rec_r : SM.Record Msg C}
    (h : s.epMgmt Δ qep P₀ false = some s₁)
    (hwf : SM.Thm1L17.WFState Δ s)
    (hr : r ∈ s.trans)
    (hrec_pos : rec_r.pos = ⟨P₀, s₁.epoch P₀, s₁.idx P₀ + 1⟩) :
    r.pos ≠ rec_r.pos := by
  obtain ⟨hwf₁, _⟩ := SM.Thm1L17.epMgmt_wf hwf h
  have htrans₁ : s₁.trans = s.trans := (epMgmt_false_tL_leaks_comp h).2.2.2
  intro heq
  have hr₁ : r ∈ s₁.trans := htrans₁ ▸ hr
  have hpos_eq : r.pos = ⟨P₀, s₁.epoch P₀, s₁.idx P₀ + 1⟩ := heq.trans hrec_pos
  have h_ep := hwf₁.trans_epoch_idx r hr₁
  rw [hpos_eq] at h_ep
  dsimp only at h_ep
  omega

theorem record_comp_contains_false_of_healedBy {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    {Δ qep t : ℕ} {P : Party} {s s₁ : SM.GameState St Msg C}
    {st' : St} {rec_r : SM.Record Msg C}
    (hwf : SM.Thm1L17.WFState Δ s)
    (hep : s.epMgmt Δ qep P false = some s₁)
    (ht : s₁.epoch P = t)
    (hr_ep : rec_r.pos.epoch = t)
    (hheal : SM.healedBy s.tL Δ t = true) :
    (s₁.record Δ P st' rec_r false).comp.contains rec_r.pos = false := by
  have htL₁ : s₁.tL = s.tL := (epMgmt_false_tL_leaks_comp hep).1
  have hcomp₁ : s₁.comp = s.comp := (epMgmt_false_tL_leaks_comp hep).2.2.1
  have hsafe : s₁.safeCh Δ P = true := by
    simp only [SM.GameState.safeCh, htL₁, ht, hheal]
  have hrec_comp : (s₁.record Δ P st' rec_r false).comp = s.comp := by
    simp only [SM.GameState.record, hsafe, ↓reduceIte, hcomp₁]
  rw [hrec_comp]
  have hheal' : SM.healedBy s.tL Δ rec_r.pos.epoch = true := by
    rw [hr_ep]; exact hheal
  exact comp_contains_false_of_wfState_and_healedBy hwf hheal'

theorem healedBy_b2_of_corrs_bound {St Msg C : Type}
    {t : ℕ} {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (ht3 : 3 ≤ t)
    (hleak : ShiftedLeakRel (cellShift (some (t - 3)) t)
      (s_cell t none) (s_cell t (some (t - 3))))
    (hcorrs : ∀ P₀ e₀, (P₀, e₀) ∈ (s_cell t none).corrs → e₀ + 3 ≤ t) :
    SM.healedBy (s_cell t (some (t - 3))).tL (cellDelta (some (t - 3)) t) t = true := by
  have hdelta : cellDelta (some (t - 3)) t = 2 + 1 := by
    unfold cellDelta
    split_ifs with hB1
    · rcases hB1 with ⟨_, h⟩; injection h; omega
    · rfl
  have hshift : cellShift (some (t - 3)) t = t - 2 := by
    unfold cellShift
    split_ifs with hB1 hB2
    · rcases hB1 with ⟨_, h⟩; injection h; omega
    · rfl
    · exact False.elim (hB2 ⟨ht3, rfl⟩)
  rw [hshift] at hleak
  cases htl : (s_cell t (some (t - 3))).tL with
  | none => rfl
  | some k =>
    have hk_mem := (hleak.tL_sh_some k htl).1
    have hk_le : k ≤ t - 3 := by
      by_contra hgt
      rcases hleak.leaks_sh_ge_l (by omega) k hk_mem (by omega) with ⟨P₀, e₀, hmem₀, hle₀⟩
      have := hcorrs P₀ e₀ hmem₀
      omega
    rw [hdelta]
    simp only [SM.healedBy, decide_eq_true_eq]
    omega

theorem canon_unsh_eq_sub_two_of_not_healedBy_and_corrs_bound {St Msg C : Type}
    {t : ℕ} {s_unsh : SM.GameState St Msg C}
    (hunsh : SM.healedBy s_unsh.tL (2 + 1) t = false)
    (hleak_corr : DeliverForge.LeakCorrInv s_unsh)
    (hcorrs : ∀ P₀ e₀, (P₀, e₀) ∈ s_unsh.corrs → e₀ + 3 ≤ t) :
    3 ≤ t ∧ SM.canon t s_unsh = some (t - 2) := by
  cases htl : s_unsh.tL with
  | none => rw [htl] at hunsh; nomatch hunsh
  | some m₀ =>
    rcases hleak_corr.2.1 m₀ htl with ⟨hm₀_mem, hm₀_max⟩
    rcases hleak_corr.2.2 m₀ hm₀_mem with ⟨R₀, e₀, hRe₀, he₀_le, hm₀_le, _⟩
    have he₀_bound := hcorrs R₀ e₀ hRe₀
    rw [htl] at hunsh
    simp only [SM.healedBy, decide_eq_false_iff_not] at hunsh
    have ht3 : 3 ≤ t := by omega
    have hm₀_eq : m₀ = t - 2 := by omega
    refine ⟨ht3, canon_eq_some_of_mem_and_le (hm₀_eq ▸ hm₀_mem) (by omega) ?_⟩
    intro m hm _
    exact hm₀_eq ▸ hm₀_max m hm

theorem healedBy_b1_of_corrs_bound {St Msg C : Type}
    {t : ℕ} {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (ht2 : 2 ≤ t)
    (hleak : ShiftedLeakRel (cellShift (some (t - 2)) t)
      (s_cell t none) (s_cell t (some (t - 2))))
    (hcorrs : ∀ P₀ e₀, (P₀, e₀) ∈ (s_cell t none).corrs → e₀ + 2 ≤ t) :
    SM.healedBy (s_cell t (some (t - 2))).tL (cellDelta (some (t - 2)) t) t = true := by
  have hdelta : cellDelta (some (t - 2)) t = 2 := by
    unfold cellDelta; simp [ht2]
  have hshift : cellShift (some (t - 2)) t = t - 1 := by
    unfold cellShift; simp [ht2]
  rw [hshift] at hleak
  cases htl : (s_cell t (some (t - 2))).tL with
  | none => rfl
  | some k =>
    have hk_mem := (hleak.tL_sh_some k htl).1
    have hk_le : k ≤ t - 2 := by
      by_contra hgt
      rcases hleak.leaks_sh_ge_l (by omega) k hk_mem (by omega) with ⟨P₀, e₀, hmem₀, hle₀⟩
      have := hcorrs P₀ e₀ hmem₀
      omega
    rw [hdelta]
    simp only [SM.healedBy, decide_eq_true_eq]
    omega

theorem party_eq_senderOf_of_sendsIn {P : Party} {t : ℕ}
    (h : P.sendsIn t = true) : P = Party.senderOf t := by
  cases P <;> simp [Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

theorem party_eq_receiverOf_or_senderOf (P : Party) (t : ℕ) :
    P = Party.receiverOf t ∨ P = Party.senderOf t := by
  unfold Party.receiverOf Party.senderOf Party.other
  cases P <;> split_ifs <;> simp

/-- Every recorded corruption `(P, e) ∈ s.corrs` occurred at an epoch `e ≤ s.epoch P`. -/
def CorrsLeEpoch {St Msg C : Type} (s : SM.GameState St Msg C) : Prop :=
  ∀ P e, (P, e) ∈ s.corrs → e ≤ s.epoch P

theorem epMgmt_false_epoch_idx_of_epMgmt_some {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    ∃ s₂, s.epMgmt Δ qep P false = some s₂ ∧ s₁.epoch = s₂.epoch ∧ s₁.idx = s₂.idx := by
  unfold SM.GameState.epMgmt SM.GameState.leak at h ⊢
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split_ifs at h ⊢ <;> simp only [Option.some.injEq] at h ⊢ <;> subst h <;>
    exact ⟨_, rfl, rfl, rfl⟩

theorem epMgmt_false_epoch_le {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P Q : Party}
    (h : s.epMgmt Δ qep P false = some s₁) :
    s.epoch Q ≤ s₁.epoch Q := by
  unfold SM.GameState.epMgmt at h
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
  split_ifs at h
  · simp only [Option.some.injEq] at h
    subst h
    dsimp only
    by_cases hQP : Q = P
    · subst hQP; simp [Function.update_self]
    · simp [Function.update_of_ne hQP]
  · simp only [Option.some.injEq] at h
    subst h
    exact le_rfl

theorem epMgmt_epoch_le {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P Q : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s.epoch Q ≤ s₁.epoch Q := by
  rcases epMgmt_false_epoch_idx_of_epMgmt_some h with ⟨s₂, hs₂, hep_eq, _⟩
  rw [hep_eq]
  exact epMgmt_false_epoch_le hs₂

theorem epMgmt_idx_eq_of_epoch_eq {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P Q : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁)
    (hep_eq : s₁.epoch Q = s.epoch Q) :
    s₁.idx Q = s.idx Q := by
  rcases epMgmt_false_epoch_idx_of_epMgmt_some h with ⟨s₂, hf, hep₂, hidx₂⟩
  rw [hep₂] at hep_eq
  rw [hidx₂]
  unfold SM.GameState.epMgmt at hf
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf
  · simp only [Option.some.injEq] at hf
    subst hf
    dsimp only at hep_eq ⊢
    by_cases hQP : Q = P
    · subst hQP
      simp only [Function.update_self] at hep_eq
      omega
    · simp [Function.update_of_ne hQP]
  · simp only [Option.some.injEq] at hf
    subst hf
    rfl

theorem send_fresh_record_origin_or_pre_corr
    {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} (qep t : ℕ) (P : Party) (bad : Bool)
    (st' : Fig8St Pt) (rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hcell_t : PPrimePaperRel (s_cell t none) m' g ∧
      SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁)
    (ht_ep : g₁.epoch P = t)
    (hr_ep : rec_r.pos.epoch = t)
    (hcorrs_le_ep : CorrsLeEpoch g) :
    let s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t₀ tL =>
        if (s_cell t₀ tL).win then s_cell t₀ tL
        else match (s_cell t₀ tL).epMgmt (cellDelta tL t₀) (qep + 1) P false with
          | some s₁ => s₁.record (cellDelta tL t₀) P st' rec_r false
          | none => s_cell t₀ tL
    (Party.senderOf t, t) ∈ g.corrs ∨
    (∃ e, (Party.receiverOf t, e) ∈ g.corrs ∧ ¬(e + 3 ≤ t)) ∨
    (∃ e, (Party.senderOf t, e) ∈ g.corrs ∧ t = e + 1) ∨
    (s_cell' t none).comp.contains rec_r.pos = false ∨
    (3 ≤ t ∧ SM.canon t (s_cell' t none) = some (t - 2) ∧
      (s_cell' t (some (t - 3))).comp.contains rec_r.pos = false) ∨
    (2 ≤ t ∧ (Party.senderOf t, t - 2) ∈ g.corrs ∧
      (s_cell' t (some (t - 2))).comp.contains rec_r.pos = false) := by
  intro s_cell'
  rcases hcell_t with ⟨hrel_none, hwf_none, hsh_all⟩
  obtain ⟨s_unsh₁, hep_unsh, hrel_unsh₁⟩ :=
    hrel_none.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
  have ht_unsh : s_unsh₁.epoch P = t := (congrFun hrel_unsh₁.epoch_eq P).trans ht_ep
  have hdelta_none : cellDelta none t = 2 + 1 := by simp [cellDelta]
  have hs_none_eq : s_cell' t none = s_unsh₁.record (2 + 1) P st' rec_r false := by
    dsimp only [s_cell']
    simp only [hrel_none.win_df_false, Bool.false_eq_true, ↓reduceIte, hdelta_none, hep_unsh]
  cases hheal_u : SM.healedBy (s_cell t none).tL (2 + 1) t with
  | true =>
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [hs_none_eq]
    exact record_comp_contains_false_of_healedBy hwf_none hep_unsh ht_unsh hr_ep hheal_u
  | false =>
    by_cases hw1 : ∃ e, (Party.receiverOf t, e) ∈ g.corrs ∧ ¬(e + 3 ≤ t)
    · exact Or.inr (Or.inl hw1)
    by_cases hk4 : (Party.senderOf t, t) ∈ g.corrs
    · exact Or.inl hk4
    by_cases hw2 : ∃ e, (Party.senderOf t, e) ∈ g.corrs ∧ t = e + 1
    · exact Or.inr (Or.inr (Or.inl hw2))
    have hw1_all : ∀ e, (Party.receiverOf t, e) ∈ g.corrs → e + 3 ≤ t :=
      fun e hce => Decidable.byContradiction (fun hlt => hw1 ⟨e, hce, hlt⟩)
    have hw2_all : ∀ e, (Party.senderOf t, e) ∈ g.corrs → t ≠ e + 1 :=
      fun e hce heq => hw2 ⟨e, hce, heq⟩
    have htL_none : none ∈ SM.admissibleLastLeakGuesses 2 t := Finset.mem_insert_self none _
    have hnot_doomed_none : ¬CellK4Doomed none t g (s_cell t none) := by
      rintro ⟨_, h, _⟩; nomatch h
    rcases (hsh_all none htL_none).resolve_left hnot_doomed_none with ⟨_, _, hleak_none, _⟩
    have hleak_corr : DeliverForge.LeakCorrInv (s_cell t none) := hleak_none.leak_corr_unsh
    have hP_sender : P = Party.senderOf t :=
      party_eq_senderOf_of_sendsIn (ht_unsh ▸ (SM.Thm1L17.epMgmt_wf hwf_none hep_unsh).2)
    have hcorrs_2 : ∀ P₀ e₀, (P₀, e₀) ∈ (s_cell t none).corrs → e₀ + 2 ≤ t := by
      intro P₀ e₀ hce_df
      have hce : (P₀, e₀) ∈ g.corrs := hrel_none.corrs_eq ▸ hce_df
      rcases party_eq_receiverOf_or_senderOf P₀ t with rfl | rfl
      · have := hw1_all e₀ hce; omega
      · have he₀_le_ep : e₀ ≤ g.epoch P := hP_sender ▸ hcorrs_le_ep (Party.senderOf t) e₀ hce
        have hep_le_t : g.epoch P ≤ t := ht_ep ▸ epMgmt_epoch_le hep_g
        have he₀_ne_t : e₀ ≠ t := fun h => hk4 (h ▸ hce)
        have ht_ne_succ : t ≠ e₀ + 1 := hw2_all e₀ hce
        omega
    by_cases hcorrs_3 : ∀ P₀ e₀, (P₀, e₀) ∈ (s_cell t none).corrs → e₀ + 3 ≤ t
    · rcases canon_unsh_eq_sub_two_of_not_healedBy_and_corrs_bound
          hheal_u hleak_corr hcorrs_3 with ⟨ht3, hcan⟩
      have hcan' : SM.canon t (s_cell' t none) = some (t - 2) := by
        rw [hs_none_eq, record_canon_eq_of_epMgmt_false hep_unsh t]
        exact hcan
      have htL_b2 : some (t - 3) ∈ SM.admissibleLastLeakGuesses 2 t :=
        Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t - 3, Finset.mem_range.mpr (by omega), rfl⟩)
      have hnot_doomed_b2 : ¬CellK4Doomed (some (t - 3)) t g (s_cell t (some (t - 3))) :=
        not_cellK4Doomed_b2_of_three_le ht3
      rcases hsh_all (some (t - 3)) htL_b2 with hdoomed | ⟨hrel_b2, hwf_b2, hleak_b2, _⟩
      · exact False.elim (hnot_doomed_b2 hdoomed)
      · have hheal_b2 := healedBy_b2_of_corrs_bound ht3 hleak_b2 hcorrs_3
        obtain ⟨s_b2₁, hep_b2, _, _, hrel_b2₁⟩ :=
          hrel_b2.epMgmt_step (Δ := cellDelta (some (t - 3)) t) (m₁' := m') hep_g
        have ht_b2 : s_b2₁.epoch P = t := (congrFun hrel_b2₁.epoch_eq P).trans ht_ep
        have hs_b2_eq :
            s_cell' t (some (t - 3)) =
              s_b2₁.record (cellDelta (some (t - 3)) t) P st' rec_r false := by
          dsimp only [s_cell']
          simp only [hrel_b2.win_df_false, Bool.false_eq_true, ↓reduceIte, hep_b2]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht3, hcan', ?_⟩))))
        rw [hs_b2_eq]
        exact record_comp_contains_false_of_healedBy hwf_b2 hep_b2 ht_b2 hr_ep hheal_b2
    · have hex_not3 : ∃ P₀ e₀, (P₀, e₀) ∈ (s_cell t none).corrs ∧ ¬(e₀ + 3 ≤ t) := by
        by_contra hall
        exact hcorrs_3 (fun P₀ e₀ hmem =>
          Decidable.byContradiction (fun hlt => hall ⟨P₀, e₀, hmem, hlt⟩))
      rcases hex_not3 with ⟨P₀, e₀, hce_df, hlt3⟩
      have he₀_2 := hcorrs_2 P₀ e₀ hce_df
      have ht2 : 2 ≤ t := by omega
      have he₀_eq : e₀ = t - 2 := by omega
      have hce : (P₀, e₀) ∈ g.corrs := hrel_none.corrs_eq ▸ hce_df
      have hP₀_sender : P₀ = Party.senderOf t := by
        rcases party_eq_receiverOf_or_senderOf P₀ t with rfl | h
        · exact False.elim (hlt3 (hw1_all e₀ hce))
        · exact h
      have hcorr_tm2 : (Party.senderOf t, t - 2) ∈ g.corrs := by
        rw [← hP₀_sender, ← he₀_eq]; exact hce
      have htL_b1 : some (t - 2) ∈ SM.admissibleLastLeakGuesses 2 t :=
        Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t - 2, Finset.mem_range.mpr (by omega), rfl⟩)
      have hnot_doomed_b1 : ¬CellK4Doomed (some (t - 2)) t g (s_cell t (some (t - 2))) :=
        CellK4Doomed.not_of_k4Free hk4
      rcases hsh_all (some (t - 2)) htL_b1 with hdoomed | ⟨hrel_b1, hwf_b1, hleak_b1, _⟩
      · exact False.elim (hnot_doomed_b1 hdoomed)
      · have hheal_b1 := healedBy_b1_of_corrs_bound ht2 hleak_b1 hcorrs_2
        obtain ⟨s_b1₁, hep_b1, _, _, hrel_b1₁⟩ :=
          hrel_b1.epMgmt_step (Δ := cellDelta (some (t - 2)) t) (m₁' := m') hep_g
        have ht_b1 : s_b1₁.epoch P = t := (congrFun hrel_b1₁.epoch_eq P).trans ht_ep
        have hs_b1_eq :
            s_cell' t (some (t - 2)) =
              s_b1₁.record (cellDelta (some (t - 2)) t) P st' rec_r false := by
          dsimp only [s_cell']
          simp only [hrel_b1.win_df_false, Bool.false_eq_true, ↓reduceIte, hep_b1]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht2, hcorr_tm2, ?_⟩))))
        rw [hs_b1_eq]
        exact record_comp_contains_false_of_healedBy hwf_b1 hep_b1 ht_b1 hr_ep hheal_b1


end CryptoVerification.LibsignalSession.HeadlineV1
