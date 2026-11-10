/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple8
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliver
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import Computational.Specifications.Pqxdh.Game
import ProofLib.SepLogic.WP.StepsCore

/-!
# Lazy-Probe `deliver` Query Step

Proves `firstNECoupledInvD_deliver_probe_lazy_step` for `firstNECoupledInvD_deliver_query_step`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal

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

variable (Pt : Type) [Zero Pt] [DecidableEq Pt] [SampleableType Pt]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem lFS_receive_i_eq {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {v₀ v' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)}
    {c' : Fig8C Pt} {i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    (hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v₀ c'.1 c'.2 = some (v', i', m_out)) :
    i' = c'.2.1 := by
  dsimp only [lFS, FSAEAD.fromAEADPRG] at hfs
  cases hlk : v₀.skippedKeys.lookup c'.2.1 with
  | some key =>
    rw [hlk] at hfs
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hfs
    rcases hfs with ⟨_, _, _, rfl, _⟩
    rfl
  | none =>
    rw [hlk] at hfs
    dsimp only at hfs
    split_ifs at hfs
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hfs
    rcases hfs with ⟨_, _, _, rfl, _⟩
    rfl

omit [DecidableEq Pt] [SampleableType Pt] in
theorem lFig8_receive_t_i_eq {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    {s st' : Fig8St Pt} {c' : Fig8C Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive s c' =
      some (st', t', i', m_out)) :
    t' = c'.1.1 ∧ i' = c'.2.1 := by
  change SM.Construction.receive (dhScheme Dh) (rootPRNG P.C.F encPt)
    (lFS P.C P.codec ℓ encT idOf 25000) s c' = some (st', t', i', m_out) at hfig
  unfold SM.Construction.receive at hfig
  dsimp only at hfig
  split_ifs at hfig with hcond hnew
  · cases hT : c'.1.2 with
    | none => simp [hT] at hfig
    | some Tn =>
      simp only [hT, Function.update_self] at hfig
      rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive
          ((lFS P.C P.codec ℓ encT idOf 25000).initReceiver
            ((rootPRNG P.C.F encPt).up s.root ((dhScheme Dh).receive s.γ Tn).2).2)
          c'.1 c'.2 with _ | ⟨v', i₁, m₁⟩
      · simp [hfs] at hfig
      · simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, lFS_receive_i_eq Pt P encT idOf hfs⟩
  · cases hv : s.vR c'.1.1 with
    | none => simp [hv] at hfig
    | some v =>
      simp only [hv] at hfig
      rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 with _ | ⟨v', i₁, m₁⟩
      · simp [hfs] at hfig
      · simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, lFS_receive_i_eq Pt P encT idOf hfs⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem exists_winning_cell_of_deliverHcasesAtExt {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (Q : Party) (c : C) (r : SM.Record Msg C) (t' i' : ℕ)
    {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some r)
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩)
    (hcases : DeliverHcasesAtExt Q t' r g s_cell) :
    ∃ tLStar ∈ SM.admissibleLastLeakGuesses 2 t',
      PPrimePaperRelShifted (s_cell t' tLStar) m' g ∧
      (s_cell t' tLStar).comp.contains r.pos = false ∧
      (s_cell t' tLStar).trivial (cellDelta tLStar t') ⟨Q.other, t', i'⟩ = false ∧
      cellWinPred tLStar t' { s_cell t' tLStar with win := true } = true := by
  have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  rcases hbody.2 t' ht'_mem with ⟨hrel_unsh, hwf_unsh, hcell_t'⟩
  have hin_unsh : (s_cell t' none).inTransit Q.other c = some r := by
    rw [hrel_unsh.inTransit_eq]; exact hin_g
  have hcase_unsh : (s_cell t' none).comp.contains r.pos = false →
      ∃ tLStar ∈ SM.admissibleLastLeakGuesses 2 t',
        PPrimePaperRelShifted (s_cell t' tLStar) m' g ∧
        (s_cell t' tLStar).comp.contains r.pos = false ∧
        (s_cell t' tLStar).trivial (cellDelta tLStar t') ⟨Q.other, t', i'⟩ = false ∧
        cellWinPred tLStar t' { s_cell t' tLStar with win := true } = true := by
    intro hcomp_unsh
    have htriv_unsh : (s_cell t' none).trivial (2 + 1) ⟨Q.other, t', i'⟩ = false := by
      rw [← hr_pos]; exact trivial_false_of_inTransit_uncomp (2 + 1) hin_unsh hcomp_unsh
    obtain ⟨_, hmem3⟩ :=
      SM.Thm1L17.authOK_of_nontrivial_inject (by omega : 0 < 2 + 1) hwf_unsh htriv_unsh
    rcases targetsL_three_subset_targetsL_two hmem3 with ⟨htLStar, hnot_B1⟩
    set tLStar := SM.canon t' (s_cell t' none)
    rcases (hcell_t' tLStar htLStar).resolve_left (CellK4Doomed.not_of_not_B1 hnot_B1) with
      ⟨hrel_star, hwf_star, hleak_star, hcomp_rel⟩
    have hin_star : (s_cell t' tLStar).inTransit Q.other c = some r := by
      rw [hrel_star.inTransit_eq]; exact hin_g
    have hcomp_star : (s_cell t' tLStar).comp.contains r.pos = false := by
      rw [List.contains_eq_mem, decide_eq_false_iff_not] at hcomp_unsh ⊢
      exact fun hmem => hcomp_unsh (hcomp_rel.comp_sh_sub_unsh r.pos hmem)
    have htriv_star :
        (s_cell t' tLStar).trivial (cellDelta tLStar t') ⟨Q.other, t', i'⟩ = false := by
      rw [← hr_pos]
      exact trivial_false_of_inTransit_uncomp (cellDelta tLStar t') hin_star hcomp_star
    obtain ⟨hauth_canon, _⟩ :=
      SM.Thm1L17.authOK_of_nontrivial_inject (pos_cellDelta tLStar t') hwf_star htriv_star
    have hcanon_eq : SM.canon t' (s_cell t' tLStar) = tLStar :=
      canon_eq_of_shiftedLeakRel_of_mem_targetsL_three hleak_star rfl hmem3
    rw [hcanon_eq] at hauth_canon
    refine ⟨tLStar, htLStar, hrel_star, hcomp_star, htriv_star, ?_⟩
    unfold cellWinPred
    have hdelta : cellDelta tLStar t' = 2 + 1 := by unfold cellDelta; simp [hnot_B1]
    rw [hdelta] at hauth_canon
    simp only [hnot_B1, ↓reduceIte, Bool.true_and]
    exact hauth_canon
  rcases hcases with (⟨hnot_qo, hnot_q, hcorr_lt⟩ | ⟨hcomp_unsh, _⟩ | ⟨ht3, _, hcomp_b2⟩) |
      ⟨ht2, hk4_g, hcomp_b1⟩
  · have hcorrs_g : ∀ P e, (P, e) ∈ g.corrs → e + 2 ≤ t' := by
      intro P e hpe
      by_cases he : e = t'
      · subst he; cases P <;> cases Q <;> simp_all [Party.other]
      · exact hcorr_lt P e hpe he
    have hk4_g : (Party.senderOf t', t') ∉ g.corrs := fun hmem => by
      have := hcorrs_g (Party.senderOf t') t' hmem; omega
    have hcorrs_unsh : ∀ P e, (P, e) ∈ (s_cell t' none).corrs → e + 2 ≤ t' := by
      rw [hrel_unsh.corrs_eq]; exact hcorrs_g
    have hlive_t' : ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t',
        PPrimePaperRelShifted (s_cell t' tL) m' g ∧
        SM.Thm1L17.WFState (cellDelta tL t') (s_cell t' tL) ∧
        ShiftedLeakRel (cellShift tL t') (s_cell t' none) (s_cell t' tL) := by
      intro tL htL
      rcases (hcell_t' tL htL).resolve_left (CellK4Doomed.not_of_k4Free hk4_g) with
        ⟨h1, h2, h3, _⟩
      exact ⟨h1, h2, h3⟩
    have hleak_none := (hlive_t' none (Finset.mem_insert_self none _)).2.2
    rcases exists_cell_healed_of_corrs_bound hcorrs_unsh hleak_none.leak_corr_unsh
        (fun tL htL => (hlive_t' tL htL).2.2) with ⟨tLStar, htLStar, htL_eq, hheal_star⟩
    rcases hlive_t' tLStar htLStar with ⟨hrel_star, hwf_star, _⟩
    have hheal_df :
        SM.healedBy (s_cell t' tLStar).tL (cellDelta tLStar t') r.pos.epoch = true := by
      rw [hr_pos, htL_eq]; exact hheal_star
    have hcomp_star : (s_cell t' tLStar).comp.contains r.pos = false :=
      (CompUnhealed.of_wfState hwf_star).comp_contains_false_of_healedBy hheal_df
    have hin_star : (s_cell t' tLStar).inTransit Q.other c = some r := by
      rw [hrel_star.inTransit_eq]; exact hin_g
    have htriv_star :
        (s_cell t' tLStar).trivial (cellDelta tLStar t') ⟨Q.other, t', i'⟩ = false := by
      rw [← hr_pos]
      exact trivial_false_of_inTransit_uncomp (cellDelta tLStar t') hin_star hcomp_star
    obtain ⟨hauth_canon, _⟩ :=
      SM.Thm1L17.authOK_of_nontrivial_inject (pos_cellDelta tLStar t') hwf_star htriv_star
    have hcanon_eq : SM.canon t' (s_cell t' tLStar) = tLStar := by
      rw [SM.Thm1L17.canon_eq_tL_of_healedBy (pos_cellDelta tLStar t') hwf_star.tL_eq
        (by rw [htL_eq]; exact hheal_star), htL_eq]
    refine ⟨tLStar, htLStar, hrel_star, hcomp_star, htriv_star, ?_⟩
    exact cellWinPred_win_of_authOK_and_k4Free tLStar t' (s_cell t' tLStar)
      (by rw [hcanon_eq] at hauth_canon; exact hauth_canon)
      (by rw [hrel_star.corrs_eq]; exact hk4_g)
  · exact hcase_unsh hcomp_unsh
  · by_cases hcomp_u : (s_cell t' none).comp.contains r.pos = false
    · exact hcase_unsh hcomp_u
    · simp only [Bool.not_eq_false] at hcomp_u
      set tLStar : Option ℕ := some (t' - 3)
      have htLStar : tLStar ∈ SM.admissibleLastLeakGuesses 2 t' :=
        Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t' - 3, Finset.mem_range.mpr (by omega), rfl⟩)
      have hnot_B1 : ¬(2 ≤ t' ∧ tLStar = some (t' - 2)) := by
        rintro ⟨_, h⟩; injection h; omega
      rcases (hcell_t' tLStar htLStar).resolve_left (CellK4Doomed.not_of_not_B1 hnot_B1) with
        ⟨hrel_star, hwf_star, _, hcomp_rel⟩
      have hin_star : (s_cell t' tLStar).inTransit Q.other c = some r := by
        rw [hrel_star.inTransit_eq]; exact hin_g
      have htriv_star :
          (s_cell t' tLStar).trivial (cellDelta tLStar t') ⟨Q.other, t', i'⟩ = false := by
        rw [← hr_pos]
        exact trivial_false_of_inTransit_uncomp (cellDelta tLStar t') hin_star hcomp_b2
      obtain ⟨hauth_canon, _⟩ :=
        SM.Thm1L17.authOK_of_nontrivial_inject (pos_cellDelta tLStar t') hwf_star htriv_star
      have hr_in_trans : r ∈ (s_cell t' none).trans := List.mem_of_find?_eq_some hin_unsh
      have hcanon_eq : SM.canon t' (s_cell t' tLStar) = tLStar :=
        hcomp_rel.comp_diff_canon_eq r hr_in_trans (by rw [hr_pos])
          (List.contains_iff_mem.mp hcomp_u)
          (fun hm => by rw [List.contains_iff_mem.mpr hm] at hcomp_b2; nomatch hcomp_b2)
      rw [hcanon_eq] at hauth_canon
      refine ⟨tLStar, htLStar, hrel_star, hcomp_b2, htriv_star, ?_⟩
      unfold cellWinPred
      have hdelta : cellDelta tLStar t' = 2 + 1 := by unfold cellDelta; simp [hnot_B1]
      rw [hdelta] at hauth_canon
      simp only [hnot_B1, ↓reduceIte, Bool.true_and]
      exact hauth_canon
  · by_cases hcomp_u : (s_cell t' none).comp.contains r.pos = false
    · exact hcase_unsh hcomp_u
    · simp only [Bool.not_eq_false] at hcomp_u
      set tLStar : Option ℕ := some (t' - 2)
      have htLStar : tLStar ∈ SM.admissibleLastLeakGuesses 2 t' :=
        Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t' - 2, Finset.mem_range.mpr (by omega), rfl⟩)
      have hnot_doomed : ¬CellK4Doomed tLStar t' g (s_cell t' tLStar) :=
        CellK4Doomed.not_of_k4Free hk4_g
      rcases (hcell_t' tLStar htLStar).resolve_left hnot_doomed with
        ⟨hrel_star, hwf_star, _, hcomp_rel⟩
      have hin_star : (s_cell t' tLStar).inTransit Q.other c = some r := by
        rw [hrel_star.inTransit_eq]; exact hin_g
      have htriv_star :
          (s_cell t' tLStar).trivial (cellDelta tLStar t') ⟨Q.other, t', i'⟩ = false := by
        rw [← hr_pos]
        exact trivial_false_of_inTransit_uncomp (cellDelta tLStar t') hin_star hcomp_b1
      obtain ⟨hauth_canon, _⟩ :=
        SM.Thm1L17.authOK_of_nontrivial_inject (pos_cellDelta tLStar t') hwf_star htriv_star
      have hr_in_trans : r ∈ (s_cell t' none).trans := List.mem_of_find?_eq_some hin_unsh
      have hcanon_eq : SM.canon t' (s_cell t' tLStar) = tLStar :=
        hcomp_rel.comp_diff_canon_eq r hr_in_trans (by rw [hr_pos])
          (List.contains_iff_mem.mp hcomp_u)
          (fun hm => by rw [List.contains_iff_mem.mpr hm] at hcomp_b1; nomatch hcomp_b1)
      rw [hcanon_eq] at hauth_canon
      refine ⟨tLStar, htLStar, hrel_star, hcomp_b1, htriv_star, ?_⟩
      exact cellWinPred_win_of_authOK_and_k4Free tLStar t' (s_cell t' tLStar) hauth_canon
        (by rw [hrel_star.corrs_eq]; exact hk4_g)

theorem probe_c'_facts_of_sameWire_ne {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r_idx w_rem : ℕ)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (st' : Fig8St Pt) (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ)
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {sent : List (Fig8C Pt)}
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hsync_hon : HonestSentSync Pt sC.base.honest sent)
    (hhonC : (sC.base.honest.find? fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hc_mem : (w, c) ∈ sC.base.honest)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hin_g : g.inTransit Q.other c = some r)
    (hrcv_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out))
    (hsame : sameWireFig8 c c' = true)
    (hne : c ≠ c') :
    w = LibsignalSim.toWire c ∧
    sent.find? (fun c₀ => sameWireFig8 c₀ c') = some c ∧
    DeliverForge.sameHdrScheme c c' = true ∧
    (g.inTransit Q.other c').isSome = false ∧
    r.pos = ⟨Q.other, t', i'⟩ := by
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv_sim, _⟩ := hInv.2
  have hw : w = LibsignalSim.toWire c := (hinv_sim.hsim.hhon (w, c) hc_mem).1.1
  have hfind : sent.find? (fun c₀ => sameWireFig8 c₀ c') = some c := by
    rw [Option.map_eq_some_iff] at hhonC
    rcases hhonC with ⟨⟨w_c, c₀⟩, hfind_hon, rfl⟩
    exact find?_sameWire_eq_honestC_of_sync Pt hsync_hon hfind_hon hsame
  obtain ⟨hw_same, h1_eq, h21_eq⟩ := toWire_eq_of_sameWireFig8 Pt hsame
  have hhdr : DeliverForge.sameHdrScheme c c' = true := by
    simp [DeliverForge.sameHdrScheme, h1_eq]
  have hnone_g : (g.inTransit Q.other c').isSome = false := by
    rw [Bool.eq_false_iff]
    intro hsome
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hr'_mem, _, hr'_ct⟩ := inTransit_eq_some_mem hr'
    have hc'_hon := (hinv_sim.hsim.htrans_hon r' hr'_mem).1
    rw [hr'_ct, ← hw_same, ← hw] at hc'_hon
    have hc_eq := honestEntryInvC_unique P (InvB InvPQ q r_idx) Dh encT hinj epExp
      sC.base hinv_sim.huniq hc_mem hc'_hon (hinv_sim.hsim.hhon (w, c) hc_mem).1
      (hinv_sim.hsim.hhon (w, c') hc'_hon).1
      (hinv_sim.hsim.hcoll c.1.1 c'.1.1 (hinv_sim.hsim.hhon (w, c) hc_mem).2.1
        (hinv_sim.hsim.hhon (w, c') hc'_hon).2.1)
    exact hne hc_eq
  obtain ⟨ht'_eq, hi'_eq⟩ := lFig8_receive_t_i_eq Pt P Dh encPt encT idOf lam hrcv_eq
  have hr_mem : r ∈ g.trans := (inTransit_eq_some_mem hin_g).1
  have hr_ct : r.ct = c := (inTransit_eq_some_mem hin_g).2.2
  rcases hinv_sim.hsim.htrans_hon r hr_mem with ⟨_, hpos_s, hpos_e, hpos_i⟩
  rw [hr_ct] at hpos_s hpos_e hpos_i
  have hr_pos : r.pos = ⟨Q.other, t', i'⟩ := by
    cases hpos : r.pos
    simp only [hpos] at hpos_s hpos_e hpos_i ⊢
    rw [hpos_s, hc_sender, hpos_e, ht'_eq, ← congrArg Prod.fst h1_eq, hpos_i, hi'_eq, ← h21_eq]
  exact ⟨hw, hfind, hhdr, hnone_g, hr_pos⟩

theorem firstNECoupledInvD_deliver_probe_lazy_step {α : Type} {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8)) (b : Bool) (c' : Fig8C Pt)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
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
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hinT : (sC.base.mir.inTransit Q.other w).isSome = true)
    (hrcv : ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c').isSome = true)
    (hc'_probe :
      ∀ (c_hon : Fig8C Pt),
        (sC.base.honest.find? fun wc =>
          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c_hon →
        sameWireFig8 c_hon c' = true ∧ c_hon ≠ c')
    (hprobe : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        ((StateT.lift (H.probe Q c') >>= fun _ => pure (some RecvResult.rejected)) :
          StateT (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) M _).run (updAmbSimStateC Pt b sC)) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₀ := updAmbSimStateC Pt b sC
  obtain ⟨⟨st', t', i', m_out⟩, hrcv_eq⟩ := Option.isSome_iff_exists.mp hrcv
  have hprobe_run := probeStep_of_guardC_probe_rejected Pt P encT decT qep fig fs Q w c'
    sC sC₀ g (hprobe (probeHook fig (qep + 1)))
  rw [hrcv] at hprobe_run
  have hstep_probe :
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
        true := by
    rw [simRecvStepC_of_probeHook_run P ℓ Dh encPt encT decT idOf lam qep Q w true
      sC sC₀ g g false true (some RecvResult.rejected) hprobe_run]
  obtain ⟨r_m, hr_m⟩ := Option.isSome_iff_exists.mp hinT
  obtain ⟨c, r, hhonC, hc_mem, hc_sender, hin_g, _, _, _, hpos_qep, _⟩ :=
    inTransit_sync_of_evictedSpurHistSimInvLazy Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w
      hlazy hsync.2.2.2.2.2.2.2.1.htcur hsync.2.2.2.2.1 hr_m
  obtain ⟨hsame, hne⟩ := hc'_probe c hhonC
  rcases hlazy with ⟨r_idx, w_rem, hInv⟩
  obtain ⟨hw, hfind, hhdr, hnone_g, hr_pos⟩ :=
    probe_c'_facts_of_sameWire_ne Pt P K InvPQ Dh encPt encT hinj idOf lam qep q r_idx w_rem
      Q w c c' r st' t' i' m_out hInv hsync.2.2.2.2.2.2.2.2.2.2.2 hhonC hc_mem hc_sender
      hin_g hrcv_eq hsame hne
  have ht'_le : t' ≤ (qep + 1) + 1 := by
    have ht'_ep : t' = r.pos.epoch := by rw [hr_pos]
    omega
  have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv_sim, _⟩ := hInv.2
  have hno_ev := evictedOnlyNoForgeAt_of_evictedSpurHistSimInvLazy P K hspqr_eq hInv_top ℓ Dh
    encPt encT decT idOf hid hdec lam sC g Q hInv
  have hcases := firstNEProbeAt_imp_deliverHcasesAtExt_of_inv_lazy
    P InvPQ ℓ Dh hDh encPt encT decT idOf hX hinj lam qep q r_idx Q w c r t' i' x₀ s_R sC g
    ec winBefore epExp hinv_sim hsync.2.2.2.2.2.2.2.2.1 hsync.2.2.2.2.2.2.1 hno_ev
    hstep_probe hw hbody.2 horig ht'_le hin_g hr_pos
  obtain ⟨tLStar, htLStar, hrel_star, hcomp_star, htriv_star, hwin_star⟩ :=
    exists_winning_cell_of_deliverHcasesAtExt qep Q c r t' i' hbody ht'_le hin_g hr_pos hcases
  refine evalDist_le_sum_cellSimRun_of_cell_step_win P ℓ Dh encPt encT decT idOf lam qep
    _ _ (u (some RecvResult.rejected)) sC sC₀ sent sent m' m' s_cell
    t' ht'_mem tLStar htLStar { s_cell t' tLStar with win := true } ?_ hwin_star
  rw [cellSimRun_deliver_query_bind,
    runCellStep_congr_run fig qep t' tLStar _ _ sC sC₀ sent m' (s_cell t' tLStar)
      (hprobe (deliverForgeHook Pt ℓ)),
    runCellStep_probe_rejected_win Pt fig qep t' tLStar Q c c' r st' i' m_out sC₀ sent m'
      hrel_star hfind ht'_le hin_g hnone_g hcomp_star hhdr hrcv_eq hr_pos htriv_star,
    pure_bind]

theorem hc'_cases_of_sameWireFig8 {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8)) (b : Bool) (c c' : Fig8C Pt)
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hhonC : (sC.base.honest.find? fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hsame : sameWireFig8 c c' = true)
    (hfa_cond :
      ((sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).isNone = true ∨
      (updAmbSimStateC Pt b sC).base.mir.safeInj 3 = true ∨
      (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c') :
    (sC.base.honest.find? fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c' ∨
    (g.safeInj (2 + 1) = true ∧
      (∀ wc ∈ sC.base.honest, wc.2 ≠ c') ∧
      (g.inTransit Q.other c').isSome = false ∧
      (c'.1.1 = g.epoch Q + 1 ∨
        ∀ (c_hon : Fig8C Pt) (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
          (w, c_hon) ∈ sC.base.honest →
          g.inTransit Q.other c_hon = some r →
          r.pos = ⟨Q.other, c'.1.1, c'.2.1⟩)) := by
  by_cases hce : c = c'
  · subst hce; exact Or.inl hhonC
  · rcases hfa_cond with hnone | hsafe₀ | hsome'
    · rw [hhonC] at hnone; cases hnone
    · right
      rcases hlazy with ⟨r_idx, w_rem, _, x₀, s_R, ec, winBefore, epExp, hinv_sim, _⟩
      rcases honest_mem_and_sender_of_find_map_some hhonC with ⟨hc_mem, hc_sender⟩
      have hsafe_mir : sC.base.mir.safeInj 3 = true :=
        (updAmbSimStateC_fields Pt b sC).2.2.2.2.1 ▸ hsafe₀
      have hsafe_g : g.safeInj (2 + 1) = true :=
        (hinv_sim.hsim.hmeta.safeInj_fig8 (2 + 1)).trans hsafe_mir
      obtain ⟨hw_same, h1_eq, h21_eq⟩ := toWire_eq_of_sameWireFig8 Pt hsame
      have hw : w = LibsignalSim.toWire c := (hinv_sim.hsim.hhon (w, c) hc_mem).1.1
      have hc'_not_hon : ∀ wc ∈ sC.base.honest, wc.2 ≠ c' := by
        intro wc hwc heq
        have hwc1 : wc.1 = w := by
          rw [(hinv_sim.hsim.hhon wc hwc).1.1, heq, ← hw_same, ← hw]
        have hwc_mem : (w, c') ∈ sC.base.honest := by rwa [← hwc1, ← heq]
        have hc_eq := honestEntryInvC_unique P (InvB InvPQ q r_idx) Dh encT hinj epExp
          sC.base hinv_sim.huniq hc_mem hwc_mem (hinv_sim.hsim.hhon (w, c) hc_mem).1
          (hinv_sim.hsim.hhon (w, c') hwc_mem).1
          (hinv_sim.hsim.hcoll c.1.1 c'.1.1 (hinv_sim.hsim.hhon (w, c) hc_mem).2.1
            (hinv_sim.hsim.hhon (w, c') hwc_mem).2.1)
        exact hce hc_eq
      have hinT_g : (g.inTransit Q.other c').isSome = false := by
        rw [Bool.eq_false_iff]
        intro hsome
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨hr'_mem, _, hr'_ct⟩ := inTransit_eq_some_mem hr'
        exact hc'_not_hon _ (hinv_sim.hsim.htrans_hon r' hr'_mem).1 hr'_ct
      refine ⟨hsafe_g, hc'_not_hon, hinT_g, Or.inr fun c_hon r hmem_hon hr_g => ?_⟩
      have hc_hon_eq := honestEntryInvC_unique P (InvB InvPQ q r_idx) Dh encT hinj epExp
        sC.base hinv_sim.huniq hc_mem hmem_hon (hinv_sim.hsim.hhon (w, c) hc_mem).1
        (hinv_sim.hsim.hhon (w, c_hon) hmem_hon).1
        (hinv_sim.hsim.hcoll c.1.1 c_hon.1.1 (hinv_sim.hsim.hhon (w, c) hc_mem).2.1
          (hinv_sim.hsim.hhon (w, c_hon) hmem_hon).2.1)
      subst hc_hon_eq
      obtain ⟨hr_mem, _, hr_ct⟩ := inTransit_eq_some_mem hr_g
      rcases hinv_sim.hsim.htrans_hon r hr_mem with ⟨_, hpos_s, hpos_e, hpos_i⟩
      rw [hr_ct] at hpos_s hpos_e hpos_i
      cases hpos : r.pos
      simp only [hpos] at hpos_s hpos_e hpos_i ⊢
      rw [hpos_s, hc_sender, hpos_e, congrArg Prod.fst h1_eq, hpos_i, h21_eq]
    · exact Or.inl hsome'

theorem firstNECoupledInvD_deliver_fwdC_sameWire_step {α : Type} {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (c c' : Fig8C Pt)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
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
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hstop : sC.base.stopped = false)
    (hinT : (sC.base.mir.inTransit Q.other w).isSome = true)
    (hhonC : (sC.base.honest.find? fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hsame : sameWireFig8 c c' = true)
    (hfwd : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        (LibsignalSimC.fwdC P qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) H Q w true ci? T pq'
          ((sC.base.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)) c').run
          (updAmbSimStateC Pt b sC))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let honestC := (sC.base.honest.find? fun wc =>
    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
  rcases fwdC_true_cases Pt P qep fig fs Q w ci? T pq' honestC c' (updAmbSimStateC Pt b sC) with
    ⟨c₀, hhonC₀, hne₀, _, _, hprobe⟩ |
    ⟨c₀, v, hhonC₀, _, _, _, hres⟩ |
    ⟨hfa_cond, hfa⟩
  · cases hrcv : fig.receive (g.st Q) c' with
    | none =>
      exact firstNECoupledInvD_deliver_probe_none_step Pt P K InvPQ Dh encPt encT decT idOf lam
        qep q Q w b c' u sC g tr sent m' s_cell hbody horig hsync hlazy hrcv
        (fun H => (hfwd H).trans (hprobe H)) hih
    | some val =>
      have hrcv_some : (fig.receive (g.st Q) c').isSome = true := by rw [hrcv]; rfl
      have hc_eq : c = c₀ := Option.some.inj (hhonC.symm.trans hhonC₀)
      subst hc_eq
      exact firstNECoupledInvD_deliver_probe_lazy_step Pt P K hspqr_eq InvPQ hInv_top Dh hDh
        encPt encT decT idOf hid hX hinj hdec lam qep q Q w b c' u sC g tr sent m' s_cell
        hbody horig hsync hlazy hinT hrcv_some
        (fun c_hon hhon_eq => by
          have h := Option.some.inj (hhonC.symm.trans hhon_eq)
          subst h; exact ⟨hsame, hne₀⟩)
        (fun H => (hfwd H).trans (hprobe H))
  · exact firstNECoupledInvD_deliver_resync_step Pt P K InvPQ Dh encPt encT decT hinj idOf lam
      qep q Q w b ci? T pq' c₀ v u sC g tr sent m' s_cell hbody horig hsync hlazy hstop hinT
      hhonC₀ (fun H => (hfwd H).trans (hres H)) hih
  · exact firstNECoupledInvD_deliver_fwdAnswer_step Pt P K InvPQ Dh encPt encT decT hinj idOf lam
      qep q Q w b ci? T pq' c' u sC g tr sent m' s_cell hbody horig hsync hlazy hstop hinT
      (hc'_cases_of_sameWireFig8 Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w b c c'
        hlazy hhonC hsame hfa_cond)
      (fun H => (hfwd H).trans (hfa H)) hih

theorem guardC_simRecvC_true_lazy_cases {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let honestC := (sC.base.honest.find? fun wc =>
      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    (∃ (ans : Option (RecvResult (Plain ℓ))) (b : Bool),
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w true)).run sC =
          pure (ans, updAmbSimStateC Pt b sC)) ∨
    (∃ (b : Bool) (c' : Fig8C Pt),
      fig.receive (g.st Q) c' = none ∧
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w true)).run sC =
          ((StateT.lift (H.probe Q c') >>= fun _ => pure (some RecvResult.rejected)) :
            StateT (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) M _).run (updAmbSimStateC Pt b sC)) ∨
    (sC.base.stopped = false ∧
      (sC.base.mir.inTransit Q.other w).isSome = true ∧
      ∃ (b : Bool) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt),
        g.safeInj (2 + 1) = true ∧
        (∀ wc ∈ sC.base.honest, wc.2 ≠ c') ∧
        (g.inTransit Q.other c').isSome = false ∧
        c'.1.1 = g.epoch Q + 1 ∧
        ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
          (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w true)).run sC =
            (LibsignalSimC.fwdAnswerC qep fig fs H Q w true none T pq' c').run
              (updAmbSimStateC Pt b sC)) ∨
    (sC.base.stopped = false ∧
      (sC.base.mir.inTransit Q.other w).isSome = true ∧
      ∃ (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8)) (c c' : Fig8C Pt),
        honestC = some c ∧
        sameWireFig8 c c' = true ∧
        ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
          (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w true)).run sC =
            (LibsignalSimC.fwdC P qep fig fs H Q w true ci? T pq' honestC c').run
              (updAmbSimStateC Pt b sC)) := by
  intro fig fs honestC
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
  by_cases hinT : (sC.base.mir.inTransit Q.other w).isNone = true
  · left; refine ⟨none, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hinT,
      Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hinTF : (sC.base.mir.inTransit Q.other w).isNone = false := Bool.eq_false_iff.mpr hinT
  have hinT_true : (sC.base.mir.inTransit Q.other w).isSome = true := by
    revert hinTF; cases (sC.base.mir.inTransit Q.other w) <;> simp
  by_cases hlen : w.length < 9
  · left; refine ⟨some .rejected, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hinTF,
      hlen, Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none =>
    left; refine ⟨some .rejected, false, fun H => ?_⟩
    unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hinTF,
      hlen, hparse, Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  | some hp =>
    rcases hp with ⟨h, body⟩
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · left; refine ⟨some .rejected, false, fun H => ?_⟩
      unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hinTF,
        hlen, hparse, haddr, Bool.true_and, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    have haddrF : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = false :=
      Bool.eq_false_iff.mpr haddr
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · left; refine ⟨some .rejected, false, fun H => ?_⟩
      unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hinTF,
        hlen, hparse, haddrF, hpan, Bool.true_and, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    have hpanF : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false :=
      Bool.eq_false_iff.mpr hpan
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ =>
      left; refine ⟨some .rejected, false, fun H => ?_⟩
      unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
      simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF, hinTF,
        hlen, hparse, haddrF, hpanF, hspqr, Bool.true_and, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      let cRaw (ep : ℕ) (t : Option Pt) : Fig8C Pt :=
        ((ep, t), (h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
      let mkC (ep : ℕ) (t : Option Pt) : Fig8C Pt :=
        match honestC with
        | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else cRaw ep t
        | none => cRaw ep t
      obtain ⟨r_mir, htr_mir⟩ := Option.isSome_iff_exists.mp hinT_true
      rcases hlazy with ⟨r_idx, w_rem, hInv⟩
      obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv, _⟩ := hInv.2
      have hno_ev := evictedOnlyNoForgeAt_of_evictedSpurHistSimInvLazy P K hspqr_eq hInv_top ℓ Dh
        encPt encT decT idOf hid hdec lam sC g Q hInv
      rcases deliver_inTransit_syncC P (InvB InvPQ q r_idx) Dh encT hinj epExp
        (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) hinv.hsim.hmeta hinv.huniq
        (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
        (fun rec_f hrec =>
          ⟨(hinv.hsim.htrans_hon rec_f hrec).1, (hinv.hsim.htrans_hon rec_f hrec).2.1⟩)
        hinv.hsim.hcoll Q w htr_mir with
        ⟨_, c, _, hc_mem, hc_sender, _, _, hhonC, _⟩
      rcases honestEntryInvC_eq_raw P (InvB InvPQ q r_idx) Dh encT epExp
        (hinv.hsim.hhon (w, c) hc_mem).1 hparse with ⟨_, hsrk, hctr, hc_raw⟩
      have hc221 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
        congrArg (fun z : Fig8C Pt => z.2.2.1) hc_raw
      have hsame_mkC (ep : ℕ) (t : Option Pt) (hc1 : c.1 = (ep, t)) :
          sameWireFig8 c (mkC ep t) = true := by
        have hraw : sameWireFig8 c (cRaw ep t) = true := by
          unfold sameWireFig8
          exact decide_eq_true ⟨hc1, hctr.symm, hc221⟩
        dsimp only [mkC, honestC]
        rw [hhonC]
        dsimp only
        split_ifs
        · unfold sameWireFig8
          exact decide_eq_true ⟨rfl, rfl, rfl⟩
        · exact hraw
      cases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
            (h.counter.toNat + 1) = true
        · left; refine ⟨some .rejected, false, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
            hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, hrej, Bool.true_and, Bool.not_true,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rfl
        · have hrejF : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
              (h.counter.toNat + 1) = false := Bool.eq_false_iff.mpr hrej
          let ch := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
          rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hci with
            ⟨ch', hch_elem', hch_key'⟩
          have hch_eq : ch = ch' := by simp [ch, hch_elem']
          have hch_elem : (sC.base.chains Q)[ci]? = some ch := by rw [hch_eq, hch_elem']
          have hch_key : ch.key = some h.senderRatchetKey := by rw [hch_eq, hch_key']
          have hch_mem : ch ∈ sC.base.chains Q := List.mem_of_getElem? hch_elem
          rcases hinv.hsim.hchains_sync Q ch hch_mem with
            ⟨hch_ep_le, _, hch_key_sync, _, _, _⟩
          have hch_none : ch.key.isNone = false := by rw [hch_key]; rfl
          rw [hch_none] at hch_key_sync
          simp only [Bool.false_eq_true, ↓reduceIte, hch_key] at hch_key_sync
          have hdh : Dh.dh (epExp ch.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
            hinj ((Option.some.inj hch_key_sync).symm.trans hsrk)
          have hle_ch : ch.epoch ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) := by
            cases Q <;>
              [exact le_trans hch_ep_le (le_max_left _ _);
               exact le_trans hch_ep_le (le_max_right _ _)]
          have hch_ep : ch.epoch = c.1.1 :=
            hinv.hsim.hcoll ch.epoch c.1.1 hle_ch (hinv.hsim.hhon (w, c) hc_mem).2.1 hdh
          have hdec_srk : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
            rw [hsrk, hdec]
          have hc1 : c.1 = (ch.epoch, decT h.senderRatchetKey) := by
            rw [hch_ep, hdec_srk]; exact congrArg Prod.fst hc_raw
          right; right; right
          refine ⟨hstopF, hinT_true, false, some ci, h.senderRatchetKey, pq', c,
            mkC ch.epoch (decT h.senderRatchetKey), hhonC, hsame_mkC _ _ hc1, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hstopF, hwinF, hinTF,
            hlen, hparse, haddrF, hpanF, hspqr, hci, hrejF,
            Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rfl
      | none =>
        let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
        by_cases hev_salt :
            (evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true
        · left; refine ⟨some .rejected, false, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
            hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted, hev_salt,
            Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rfl
        have hev_saltF :
            (evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) =
              false := Bool.eq_false_iff.mpr hev_salt
        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
        · left; refine ⟨some .rejected, false, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hstopF, hwinF,
            hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted, hev_saltF, hT0,
            Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rfl
        have hT0F : (decT h.senderRatchetKey == some 0) = false := Bool.eq_false_iff.mpr hT0
        let spkAmb := Q == Party.A && (sC.base.chains Q).any (·.key.isNone)
        let b_amb := inReceiveOnlyEpoch sC.base.mir Q || spkAmb
        by_cases hwin_i :
            (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
        · left; refine ⟨some .rejected, b_amb, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
          dsimp only [b_amb, spkAmb]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, ite_modify_bind_run,
            pure_bind, hstopF, hwinF, hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC,
            evicted, hev_saltF, hT0F, hwin_i, Bool.true_and, Bool.not_true,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        have hwin_iF :
            (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false := Bool.eq_false_iff.mpr hwin_i
        have hskip := hwin_i
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hskip
        have hinw_Q : inReceiveOnlyEpoch sC.base.mir Q = false := Bool.eq_false_iff.mpr hskip.1.1
        have hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1) :=
          not_or.mpr ⟨hskip.1.2, hskip.2⟩
        cases hT : decT h.senderRatchetKey with
        | none =>
          have hT0' : ((none : Option Pt) == some 0) = false := rfl
          left; refine ⟨some .rejected, b_amb, fun H => ?_⟩
          unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
          dsimp only [b_amb, spkAmb]
          simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, ite_modify_bind_run,
            pure_bind, hstopF, hwinF, hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC,
            evicted, hev_saltF, hT0', hwin_iF, hT, Bool.true_and, Bool.not_true,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        | some T =>
          have hT0' : (some T == (some 0 : Option Pt)) = false := hT ▸ hT0F
          by_cases hev : evicted = true
          · have hev' := hev
            dsimp only [evicted, honestC] at hev'
            rw [hhonC] at hev'
            have hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1 := by simpa using hev'
            let c_ev := cRaw (sC.base.mir.epoch Q + 1) (some T)
            let sC₀ := updAmbSimStateC Pt b_amb sC
            have hevict_run : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
                (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs H Q w
                  true)).run sC =
                (LibsignalSimC.fwdEvictC qep fig fs H Q w true h.senderRatchetKey pq' c_ev).run
                  sC₀ := by
              intro M _ _ H
              dsimp only [sC₀, b_amb, spkAmb]
              unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
              simp only [StateT.run_bind, StateT.run_get, ite_modify_bind_run, pure_bind, hstopF,
                hwinF, hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted,
                hev_saltF, hT0', hwin_iF, hT, Bool.true_and, Bool.not_true, Bool.false_and,
                Bool.false_eq_true, ↓reduceIte]
              simp only [hev, evicted, honestC, ↓reduceIte]
              rfl
            rcases fwdEvictC_true_cases Pt qep fig fs Q w h.senderRatchetKey pq' c_ev sC₀ with
              ⟨hsafe₀, hprobe⟩ | ⟨hsafe₀, hfa⟩
            · have hsafe : sC.base.mir.safeInj 3 = false :=
                (updAmbSimStateC_fields Pt b_amb sC).2.2.2.2.1 ▸ hsafe₀
              have hrcv_none := hno_ev w c h body pq' salt hc_mem hc_sender hparse hspqr hci
                hepoch hinw_Q hbound hsafe T hT
              right; left
              exact ⟨b_amb, c_ev, hrcv_none, fun H => (hevict_run H).trans (hprobe H)⟩
            · have hsafe_mir : sC.base.mir.safeInj 3 = true :=
                (updAmbSimStateC_fields Pt b_amb sC).2.2.2.2.1 ▸ hsafe₀
              have hsafe_g : g.safeInj (2 + 1) = true :=
                (hinv.hsim.hmeta.safeInj_fig8 (2 + 1)).trans hsafe_mir
              have hc_ev_not_hon : ∀ wc ∈ sC.base.honest, wc.2 ≠ c_ev := by
                intro wc hwc heq
                have hwc1 : wc.1 = w := by
                  rw [(hinv.hsim.hhon wc hwc).1.1, heq]
                  exact toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T)
                    (h.counter.toNat + 1) (effectiveHkdfSalt32 salt)
                have hwc_mem : (w, c_ev) ∈ sC.base.honest := by rwa [← hwc1, ← heq]
                have hc_eq := honestEntryInvC_unique P (InvB InvPQ q r_idx) Dh encT hinj epExp
                  sC.base hinv.huniq hc_mem hwc_mem (hinv.hsim.hhon (w, c) hc_mem).1
                  (hinv.hsim.hhon (w, c_ev) hwc_mem).1
                  (hinv.hsim.hcoll c.1.1 c_ev.1.1 (hinv.hsim.hhon (w, c) hc_mem).2.1
                    (hinv.hsim.hhon (w, c_ev) hwc_mem).2.1)
                exact hepoch (congrArg (fun z : Fig8C Pt => z.1.1) hc_eq)
              have hinT_g : (g.inTransit Q.other c_ev).isSome = false := by
                rw [Bool.eq_false_iff]
                intro hsome
                obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
                obtain ⟨hr'_mem, _, hr'_ct⟩ := inTransit_eq_some_mem hr'
                exact hc_ev_not_hon _ (hinv.hsim.htrans_hon r' hr'_mem).1 hr'_ct
              have hc_ev_ep : c_ev.1.1 = g.epoch Q + 1 := by
                dsimp only [c_ev, cRaw]
                have hep : g.epoch Q = sC.base.mir.epoch Q :=
                  congrFun hinv.hsim.hmeta.hepoch_fig8 Q
                rw [hep]
              right; right; left
              exact ⟨hstopF, hinT_true, b_amb, h.senderRatchetKey, pq', c_ev, hsafe_g,
                hc_ev_not_hon, hinT_g, hc_ev_ep, fun H => (hevict_run H).trans (hfa H)⟩
          · have hevF : evicted = false := Bool.eq_false_iff.mpr hev
            have hev' := hev
            dsimp only [evicted, honestC] at hev'
            rw [hhonC] at hev'
            simp only [Option.map_some, beq_iff_eq, Option.some.injEq,
              decide_eq_true_eq, not_ne_iff] at hev'
            have hepoch : c.1.1 = sC.base.mir.epoch Q + 1 := hev'
            have hT_eq : T = Dh.dh (epExp (sC.base.mir.epoch Q + 1)) Dh.base := by
              rw [hsrk, hepoch, hdec] at hT
              exact Option.some.inj hT.symm
            have hc1 : c.1 = (sC.base.mir.epoch Q + 1, some T) := by
              rw [← hepoch, hT_eq, ← hepoch]; exact congrArg Prod.fst hc_raw
            right; right; right
            refine ⟨hstopF, hinT_true, b_amb, none, h.senderRatchetKey, pq', c,
              mkC (sC.base.mir.epoch Q + 1) (some T), hhonC, hsame_mkC _ _ hc1, fun H => ?_⟩
            unfold LibsignalSimC.guardC LibsignalSimC.simRecvC updAmbSimStateC
            dsimp only [b_amb, spkAmb]
            simp only [StateT.run_bind, StateT.run_get, ite_modify_bind_run, pure_bind, hstopF,
              hwinF, hinTF, hlen, hparse, haddrF, hpanF, hspqr, hci, honestC, evicted,
              hev_saltF, hT0', hwin_iF, hT, Bool.true_and, Bool.not_true, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte]
            simp only [hevF, evicted, honestC, Bool.false_eq_true, ↓reduceIte]
            rfl

theorem firstNECoupledInvD_deliver_query_step_aux {α : Type}
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
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
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
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  by_cases hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g
  · rcases guardC_simRecvC_true_lazy_cases Pt P K hspqr_eq InvPQ hInv_top Dh encPt encT decT idOf
        hid hinj hdec lam qep q Q w sC g hlazy with
      ⟨ans, b, hpure⟩ |
      ⟨b, c', hrcv_none, hprobe⟩ |
      ⟨hstop, hinT, b, T, pq', c', hsafe_g, hc'_not_hon, hinT_g, hc'_ep, hfa⟩ |
      ⟨hstop, hinT, b, ci?, T, pq', c, c', hhonC, hsame, hfwd⟩
    · exact firstNECoupledInvD_deliver_pure_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w
        u sC g tr sent m' s_cell hbody horig hsync hlazy ans b hpure hih
    · exact firstNECoupledInvD_deliver_probe_none_step Pt P K InvPQ Dh encPt encT decT idOf lam
        qep q Q w b c' u sC g tr sent m' s_cell hbody horig hsync hlazy hrcv_none hprobe hih
    · exact firstNECoupledInvD_deliver_fwdAnswer_step Pt P K InvPQ Dh encPt encT decT hinj idOf lam
        qep q Q w b none T pq' c' u sC g tr sent m' s_cell hbody horig hsync hlazy hstop hinT
        (Or.inr ⟨hsafe_g, hc'_not_hon, hinT_g, Or.inl hc'_ep⟩) hfa hih
    · exact firstNECoupledInvD_deliver_fwdC_sameWire_step Pt P K hspqr_eq InvPQ hInv_top Dh hDh
        encPt encT decT idOf hid hX hinj hdec lam qep q Q w b ci? T pq' c c' u sC g tr sent m'
        s_cell hbody horig hsync hlazy hstop hinT hhonC hsame hfwd hih
  · obtain ⟨ans, sC₁, g₁, tr', hrun⟩ :=
      firstNESimImpl'_deliver_of_not_lazy P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w sC g
        tr hlazy
    exact firstNECoupledInvD_deliver_probe_nonlazy_step Pt P K InvPQ Dh encPt encT decT idOf lam
      qep q Q w u sC sC₁ g g₁ ans tr tr' sent m' s_cell hrun

end CryptoVerification.LibsignalSession.HeadlineV1

end
