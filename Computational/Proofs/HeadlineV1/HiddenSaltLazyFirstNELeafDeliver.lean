/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple8
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import Computational.Specifications.Pqxdh.Game
import ProofLib.SepLogic.WP.StateNorm

/-!
# Non-Probe `deliver` Query Step Lemmas

Proves the `resyncC` and `fwdAnswerC` branch lemmas for `firstNECoupledInvD_deliver_query_step`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
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

theorem syncInv_deliver_accept_step {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    {sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ} {b' : SimState (List (BitVec 8)) Pt ℓ}
    {sent : List (Fig8C Pt)} {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {c : Fig8C Pt} {st' : Fig8St Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    {pos : SM.Pos} {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g s_unsh)
    (hstop : sC₀.base.stopped = false)
    (hpos_ep : pos.epoch = c.1.1)
    (hpos_le : pos.epoch ≤ max (g.epoch Q) (g.epoch Q.other))
    (hpos_qep : pos.epoch ≤ qep + 1)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c =
      some (st', t', i', m_out))
    (hres : ∃ pm, res = some (.accepted t' i' pm))
    (hhon_b' : b'.honest = sC₀.base.honest)
    (hstop_b' : b'.stopped = sC₀.base.stopped)
    (hmir_b' : b'.mir = sC₀.base.mir.accept Q () pos) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    SyncInv P Dh encPt encT idOf lam qep
      { updKeptOnRes fig fs Q c res sC₀ with base := b' } sent
      (m'.accept Q () pos) (g.accept Q st' pos) (s_unsh.accept Q st' pos) := by
  intro fig fs
  rcases hsync with ⟨hmeta_imp, hmsync, hwf_g, hcorrs_le, hep_le, hsnap_idx, hcorrs_snaps,
    hfig8, hkept, hkept_inv, hid, hhon⟩
  rcases hmeta_imp hstop with ⟨s_R, hmeta⟩
  rcases hres with ⟨pm, rfl⟩
  have heq_kept := updKeptOnRes_accepted_eq Pt fig fs Q c t' i' t' i' pm (some m_out) sC₀
  refine ⟨?_, hmsync.deliver_step Q st' pos,
    SM.Thm1L17.accept_wf hwf_g hpos_le,
    corrsLeEpoch_accept Q st' pos hcorrs_le,
    epoch_le_accept Q st' pos hep_le hpos_qep,
    corrsSnapIdxInv_updKeptOnRes_accept Pt fig fs Q c _ sC₀ b' g st' pos hsnap_idx hcorrs_le,
    corrsSnapsInv_updKeptOnRes_accept Pt fig fs Q c _ sC₀ b' g st' pos hcorrs_snaps,
    fig8SenderSync_accept Pt P Dh encPt encT idOf lam Q c st' t' i' m_out pos
      hkept_inv (hid Q) hfig8 hrcv hpos_ep,
    ?_, ?_,
    st_id_accept Pt P Dh encPt encT idOf lam Q c st' t' i' m_out pos hid hrcv,
    honestSentSync_with_base Pt _ b' sent hhon hhon_b'⟩
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
  · rw [heq_kept]
    exact corrsKeptRecvInv_with_base Pt _ b' _
      (corrsKeptRecvInv_updKeptOnRes_accept Pt P Dh encPt encT idOf lam Q c st' t' i' m_out pos
        hkept_inv hcorrs_le (hfig8.htcur Q) hkept hrcv)
  · rw [heq_kept]
    exact keptInv_with_base Pt P Dh encPt encT idOf lam _ b' _
      (keptInv_updKeptOnRes_accept Pt P Dh encPt encT idOf lam Q c st' t' i' m_out pos
        hkept_inv (hid Q) hrcv)

theorem deliver_accept_sync_and_family_step {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    {sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ} {b' : SimState (List (BitVec 8)) Pt ℓ}
    {sent : List (Fig8C Pt)} {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {c : Fig8C Pt} {st' : Fig8St Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    {pos : SM.Pos} {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g s_unsh)
    (hcol : ∀ t₁ ∈ Finset.range ((qep + 1) + 2), ∀ t₂ ∈ Finset.range ((qep + 1) + 2),
      s_cell t₁ none = s_cell t₂ none)
    (hrel_all : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (hstop : sC₀.base.stopped = false)
    (hpos_ep : pos.epoch = c.1.1)
    (hpos_le : pos.epoch ≤ max (g.epoch Q) (g.epoch Q.other))
    (hpos_qep : pos.epoch ≤ qep + 1)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c =
      some (st', t', i', m_out))
    (hres : ∃ pm, res = some (.accepted t' i' pm))
    (hhon_b' : b'.honest = sC₀.base.honest)
    (hstop_b' : b'.stopped = sC₀.base.stopped)
    (hmir_b' : b'.mir = sC₀.base.mir.accept Q () pos) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let g' := g.accept Q st' pos
    let m₁' := m'.accept Q () pos
    let s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL => if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' pos
    SyncInv P Dh encPt encT idOf lam qep
      { updKeptOnRes fig fs Q c res sC₀ with base := b' } sent
      m₁' g' (s_unsh.accept Q st' pos) ∧
    FirstNECellFamilyInvT qep false g' m₁' s_cell' ∧
    ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g' (s_cell' t tL) ∨
      (PPrimePaperRelShifted (s_cell t tL) m' g ∧
        s_cell' t tL = (s_cell t tL).accept Q st' pos) := by
  intro fig fs g' m₁' s_cell'
  exact ⟨syncInv_deliver_accept_step Pt P Dh encPt encT idOf lam qep Q
      hsync hstop hpos_ep hpos_le hpos_qep hrcv hres hhon_b' hstop_b' hmir_b',
    deliver_noProbe_step_of_inTransit qep Q st' pos hcol hrel_all hpos_le⟩

theorem inTransit_sync_of_evictedSpurHistSimInvLazy {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {r_m : SM.Record (Plain ℓ) (List (BitVec 8))}
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (htcur : ∀ P, (g.st P).tcur = g.epoch P)
    (hep_qep : ∀ P, g.epoch P ≤ qep + 1)
    (hr_m : sC.base.mir.inTransit Q.other w = some r_m) :
    ∃ (c : Fig8C Pt) (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c ∧
      (w, c) ∈ sC.base.honest ∧
      Party.senderOf c.1.1 = Q.other ∧
      g.inTransit Q.other c = some r ∧
      r.pos = r_m.pos ∧
      r.pos.epoch = c.1.1 ∧
      r.pos.epoch ≤ max (g.epoch Q) (g.epoch Q.other) ∧
      r.pos.epoch ≤ qep + 1 ∧
      (sC.base.honest.any fun wc =>
        decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = true := by
  rcases hlazy with ⟨r_idx, w_rem, _, x₀, s_R, ec, winBefore, epExp, hinv_sim, _⟩
  rcases deliver_inTransit_syncC P (InvB InvPQ q r_idx) Dh encT hinj epExp
    (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) hinv_sim.hsim.hmeta hinv_sim.huniq
    (fun wc hwc => ⟨(hinv_sim.hsim.hhon wc hwc).1, (hinv_sim.hsim.hhon wc hwc).2.1⟩)
    (fun rec_f hrec => ⟨(hinv_sim.hsim.htrans_hon rec_f hrec).1,
      (hinv_sim.hsim.htrans_hon rec_f hrec).2.1⟩)
    hinv_sim.hsim.hcoll Q w hr_m with
    ⟨_, c, r, hmem_hon, hsend_c, hr_g, hpos_eq, hhonC, _⟩
  have hr_g' : g.inTransit Q.other c = some r := hr_g
  have hr_mem : r ∈ g.trans := List.mem_of_find?_eq_some hr_g'
  have hpos_e := (hinv_sim.hsim.htrans_hon r hr_mem).2.2.1
  have hpred := List.find?_some hr_g'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  have hpos_ep : r.pos.epoch = c.1.1 := by rw [hpos_e, hpred.2]
  have hle_ep := (hinv_sim.hsim.hhon (w, c) hmem_hon).2.2.2
  rw [hsend_c] at hle_ep
  have hep_eq : g.epoch Q.other = sC.base.mir.epoch Q.other :=
    (htcur Q.other).symm.trans (hinv_sim.hsim.htcur Q.other)
  have hpos_le_other : r.pos.epoch ≤ g.epoch Q.other := by
    rw [hpos_ep, hep_eq]; exact hle_ep
  have hpos_le : r.pos.epoch ≤ max (g.epoch Q) (g.epoch Q.other) :=
    le_trans hpos_le_other (le_max_right _ _)
  have hpos_qep : r.pos.epoch ≤ qep + 1 :=
    le_trans hpos_le_other (hep_qep Q.other)
  have hInT : (sC.base.honest.any fun wc =>
      decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = true := by
    rw [List.any_eq_true]
    refine ⟨(w, c), hmem_hon, ?_⟩
    simp [hr_m]
  exact ⟨c, r, hhonC, hmem_hon, hsend_c, hr_g', hpos_eq, hpos_ep, hpos_le, hpos_qep, hInT⟩

theorem firstNECoupledInvD_deliver_resync_step {α : Type} {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (c : Fig8C Pt) (v : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
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
    (hres : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        (LibsignalSimC.resyncC qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) H Q w ci? T pq' c v).run
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
  let sC₀ := updAmbSimStateC Pt b sC
  have hsync₀ : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g (s_cell 0 none) :=
    syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g (s_cell 0 none) hsync
  have horig₀ : FirstNEInTransOriginInv qep sC₀.snaps g s_cell :=
    (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig
  have hstop₀ : sC₀.base.stopped = false :=
    (updAmbSimStateC_fields Pt b sC).2.2.2.2.2.trans hstop
  rcases v with _ | ⟨t_v, i_v, pm_v⟩
  · have hprobe_run :
        (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
            (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
          pure ((some RecvResult.rejected, sC₀), (g, false)) := by
      rw [hres (probeHook fig (qep + 1))]
      exact (resyncC_none_lockstep Pt qep 0 none fig fs Q w ci? T pq' c sC₀ sent m'
        g (s_cell 0 none) false).1
    obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf
      lam qep q Q w sC sC₀ g g (some RecvResult.rejected) tr hlazy hprobe_run
    rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
    have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g s_cell :=
      Or.inr (Or.inr ⟨rfl, rfl, hbody, horig₀, hsync₀⟩)
    refine le_trans (hih (some RecvResult.rejected) sC₀ g false false tr' sent m' s_cell hinv₁) ?_
    refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
      _ (u (some RecvResult.rejected)) sC sC₀ sent sent m' m' g s_cell s_cell fun t _ tL _ =>
      Or.inr ?_
    rw [cellSimRun_deliver_query_bind,
      runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
        (hres (deliverForgeHook Pt ℓ)),
      (resyncC_none_lockstep Pt qep t tL fig fs Q w ci? T pq' c sC₀ sent m' g
        (s_cell t tL) false).2,
      pure_bind]
  · obtain ⟨r_m, hr_m⟩ := Option.isSome_iff_exists.mp hinT
    obtain ⟨c_hon, r, hhonC_eq, _, _, hr_g, hpos_eq, hpos_ep, hpos_le, hpos_qep, _⟩ :=
      inTransit_sync_of_evictedSpurHistSimInvLazy Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w
        hlazy hsync.2.2.2.2.2.2.2.1.htcur hsync.2.2.2.2.1 hr_m
    have hc_eq : c_hon = c := Option.some.inj (hhonC_eq.symm.trans hhonC)
    subst c_hon
    have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hrel0 : PPrimePaperRelShifted (s_cell 0 none) m' g := (hbody.2 0 ht0).1.toShifted
    cases hrcv : fig.receive (g.st Q) c with
    | none =>
      have hprobe_run :
          (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((some RecvResult.rejected, sC₀), (g, false)) := by
        rw [hres (probeHook fig (qep + 1))]
        exact (resyncC_some_of_receive_none Pt fig fs qep 0 none Q w ci? T pq' c t_v i_v pm_v
          sC₀ sent false hrel0 hsync.2.1 hr_g hrcv).1
      obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf
        lam qep q Q w sC sC₀ g g (some RecvResult.rejected) tr hlazy hprobe_run
      rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g
          s_cell :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody, horig₀, hsync₀⟩)
      refine le_trans (hih (some RecvResult.rejected) sC₀ g false false tr' sent m' s_cell hinv₁) ?_
      refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u (some RecvResult.rejected)) sC sC₀ sent sent m' m' g s_cell s_cell
        fun t ht tL htL => ?_
      rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        rw [cellSimRun_deliver_query_bind,
          runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hres (deliverForgeHook Pt ℓ)),
          (resyncC_some_of_receive_none Pt fig fs qep t tL Q w ci? T pq' c t_v i_v pm_v
            sC₀ sent false hrel_sh hsync.2.1 hr_g hrcv).2,
          pure_bind]
    | some v_out =>
      rcases v_out with ⟨st', t', i', m_out⟩
      have hr_m₀ : sC₀.base.mir.inTransit Q.other w = some r_m :=
        (updAmbSimStateC_fields Pt b sC).2.2.2.2.1.symm ▸ hr_m
      obtain ⟨ans, b', hrun_acc, hhon_b', hstop_b', hmir_b'⟩ :=
        onAccept_true_of_inTransit_some Pt qep Q w t_v i_v pm_v.2 ci? T pq' sC₀.base hr_m₀
      rw [← hpos_eq] at hmir_b'
      let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) := some (.accepted t' i' (some m_out))
      let sC₁ := { updKeptOnRes fig fs Q c res_acc sC₀ with base := b' }
      let g₁ := g.accept Q st' r.pos
      let m₁' := m'.accept Q () r.pos
      let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
        fun t tL => if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' r.pos
      have hprobe_run :
          (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((ans, sC₁), (g₁, false)) := by
        rw [hres (probeHook fig (qep + 1))]
        exact (resyncC_some_of_accept Pt fig fs qep 0 none Q w ci? T pq' c t_v i_v pm_v
          sC₀ sent false hrel0 hsync.2.1 hr_g hrcv ans b' hrun_acc).1
      obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf
        lam qep q Q w sC sC₁ g g₁ ans tr hlazy hprobe_run
      rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
      obtain ⟨hsync₁, hfam₁, hcells₁⟩ :=
        deliver_accept_sync_and_family_step Pt P Dh encPt encT idOf lam qep Q
          (s_cell := s_cell) (res := res_acc) hsync₀ hbody.1 hbody.2 hstop₀
          hpos_ep hpos_le hpos_qep hrcv ⟨some m_out, rfl⟩ hhon_b' hstop_b' hmir_b'
      have hbody₁ : FirstNECellFamilyInvT_body qep g₁ m₁' s_cell₁ := by
        rcases hfam₁ with ⟨t, ht, tL, htL, hwin_cell⟩ | ⟨_, hcol₁, hrel₁⟩
        · exfalso
          rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
          · rw [hdoomed.cellWinPred_eq_false] at hwin_cell; cases hwin_cell
          · have hw := s_win_of_cellWinPred hwin_cell
            rw [hacc] at hw
            exact Bool.false_ne_true (hrel_sh.win_df_false.symm.trans hw)
        · exact ⟨hcol₁, hrel₁⟩
      have horig₁ : FirstNEInTransOriginInv qep sC₁.snaps g₁ s_cell₁ := by
        have hsnaps₁ : sC₁.snaps = sC₀.snaps :=
          (updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c res_acc sC₀).2.2
        rw [hsnaps₁]
        exact firstNEInTransOriginInv_accept_step qep Q st' r.pos sC₀.snaps horig₀
      have h0_eq : s_cell₁ 0 none = (s_cell 0 none).accept Q st' r.pos := by
        dsimp only [s_cell₁]
        rw [(hbody.2 0 ht0).1.win_df_false]
        rfl
      have hsync₁' : SyncInv P Dh encPt encT idOf lam qep sC₁ sent m₁' g₁ (s_cell₁ 0 none) := by
        rw [h0_eq]
        exact hsync₁
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
          sC₁ sent m₁' g₁ s_cell₁ :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody₁, horig₁, hsync₁'⟩)
      refine le_trans (hih ans sC₁ g₁ false false tr' sent m₁' s_cell₁ hinv₁) ?_
      refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u ans) sC sC₁ sent sent m' m₁' g₁ s_cell s_cell₁ fun t ht tL htL => ?_
      rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
      · exact Or.inl hdoomed
      · right
        rw [cellSimRun_deliver_query_bind,
          runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hres (deliverForgeHook Pt ℓ)),
          (resyncC_some_of_accept Pt fig fs qep t tL Q w ci? T pq' c t_v i_v pm_v
            sC₀ sent false hrel_sh hsync.2.1 hr_g hrcv ans b' hrun_acc).2,
          pure_bind, ← hacc]

theorem firstNECoupledInvD_deliver_fwdAnswer_step {α : Type} {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
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
    (hc'_cases :
      (sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c' ∨
      (g.safeInj (2 + 1) = true ∧
        (∀ wc ∈ sC.base.honest, wc.2 ≠ c') ∧
        (g.inTransit Q.other c').isSome = false ∧
        (c'.1.1 = g.epoch Q + 1 ∨
          ∀ (c_hon : Fig8C Pt) (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
            (w, c_hon) ∈ sC.base.honest →
            g.inTransit Q.other c_hon = some r →
            r.pos = ⟨Q.other, c'.1.1, c'.2.1⟩)))
    (hfa : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        (LibsignalSimC.fwdAnswerC qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) H Q w true ci? T pq' c').run
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
  let sC₀ := updAmbSimStateC Pt b sC
  have hsync₀ : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g (s_cell 0 none) :=
    syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g (s_cell 0 none) hsync
  have horig₀ : FirstNEInTransOriginInv qep sC₀.snaps g s_cell :=
    (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig
  have hstop₀ : sC₀.base.stopped = false :=
    (updAmbSimStateC_fields Pt b sC).2.2.2.2.2.trans hstop
  obtain ⟨r_m, hr_m⟩ := Option.isSome_iff_exists.mp hinT
  obtain ⟨c_hon, r, hhonC, hmem_hon, _, hr_g, hpos_eq, hpos_ep, hpos_le, hpos_qep, hInT⟩ :=
    inTransit_sync_of_evictedSpurHistSimInvLazy Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w
      hlazy hsync.2.2.2.2.2.2.2.1.htcur hsync.2.2.2.2.1 hr_m
  have hr_m₀ : sC₀.base.mir.inTransit Q.other w = some r_m := by
    rw [(updAmbSimStateC_fields Pt b sC).2.2.2.2.1]; exact hr_m
  have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  have hnone0 : none ∈ SM.admissibleLastLeakGuesses 2 0 := by simp [SM.admissibleLastLeakGuesses]
  have hrel0 : PPrimePaperRelShifted (s_cell 0 none) m' g := by
    rcases (hbody.2 0 ht0).2.2 none hnone0 with hdoomed | ⟨hrel_sh, _, _, _⟩
    · exact False.elim (nomatch hdoomed.1)
    · exact hrel_sh
  rcases hc'_cases with hhonC' | ⟨hsafe_g, hc'_not_hon, hinT_g, hc'_ep⟩
  · have hc_eq : c_hon = c' := Option.some.inj (hhonC.symm.trans hhonC')
    subst hc_eq
    have hInT₀ : (sC₀.base.honest.any fun wc =>
        decide (wc.2 = c_hon) && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = true := by
      rw [(updAmbSimStateC_fields Pt b sC).2.2.2.1, (updAmbSimStateC_fields Pt b sC).2.2.2.2.1]
      exact hInT
    cases hrcv : fig.receive (g.st Q) c_hon with
    | none =>
      have hrej_ans := onAnswer_rejected_run qep Q w true ci? T pq' sC₀.base
      have hrej_kept := updKeptOnRes_rejected Pt fig fs Q c_hon sC₀
      have hlock := fwdAnswerC_deliver_lockstep Pt fig fs qep 0 none Q w true ci? T pq' c_hon
        sC₀ sent false hrel0 hsync.2.1 hInT₀ (some RecvResult.rejected) sC₀.base
        (by simpa [hr_g, hrcv] using hrej_ans)
      simp only [hr_g, hrcv, hrej_kept] at hlock
      have hprobe_run :
          (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((some RecvResult.rejected, sC₀), (g, false)) := by
        rw [hfa (probeHook fig (qep + 1))]; exact hlock.1
      obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf
        lam qep q Q w sC sC₀ g g (some RecvResult.rejected) tr hlazy hprobe_run
      rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
          sC₀ sent m' g s_cell :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody, horig₀, hsync₀⟩)
      refine le_trans (hih (some RecvResult.rejected) sC₀ g false false tr' sent m' s_cell hinv₁) ?_
      refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u (some RecvResult.rejected)) sC sC₀ sent sent m' m' g s_cell s_cell
        fun t ht tL htL => ?_
      rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        have hlock_t := fwdAnswerC_deliver_lockstep Pt fig fs qep t tL Q w true ci? T pq' c_hon
          sC₀ sent false hrel_sh hsync.2.1 hInT₀ (some RecvResult.rejected) sC₀.base
          (by simpa [hr_g, hrcv] using hrej_ans)
        simp only [hr_g, hrcv, hrej_kept] at hlock_t
        rw [cellSimRun_deliver_query_bind,
          runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hfa (deliverForgeHook Pt ℓ)),
          hlock_t.2, pure_bind]
    | some val =>
      rcases val with ⟨st', t', i', m_out⟩
      let pm : Option (LibsignalMsgPublicPart × Plain ℓ) := if r.pos ∈ g.chall then none else some m_out
      let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) := some (.accepted t' i' pm)
      obtain ⟨ans, b', hrun_ans, hhon_b', hstop_b', hmir_b'⟩ :=
        onAnswer_true_accepted_of_inTransit_some Pt qep Q w ci? T pq' t' i' pm sC₀.base hr_m₀
      rw [← hpos_eq] at hmir_b'
      let sC₁ := { updKeptOnRes fig fs Q c_hon res_acc sC₀ with base := b' }
      let g₁ := g.accept Q st' r.pos
      let m₁' := m'.accept Q () r.pos
      let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
        fun t tL => if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' r.pos
      have hlock := fwdAnswerC_deliver_lockstep Pt fig fs qep 0 none Q w true ci? T pq' c_hon
        sC₀ sent false hrel0 hsync.2.1 hInT₀ ans b'
        (by simpa [hr_g, hrcv, res_acc, pm] using hrun_ans)
      simp only [hr_g, hrcv] at hlock
      have hprobe_run :
          (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((ans, sC₁), (g₁, false)) := by
        rw [hfa (probeHook fig (qep + 1))]; exact hlock.1
      obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf
        lam qep q Q w sC sC₁ g g₁ ans tr hlazy hprobe_run
      rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
      obtain ⟨hsync₁, hfam₁, hcells₁⟩ :=
        deliver_accept_sync_and_family_step Pt P Dh encPt encT idOf lam qep Q
          (s_cell := s_cell) (res := res_acc) hsync₀ hbody.1 hbody.2 hstop₀
          hpos_ep hpos_le hpos_qep hrcv ⟨pm, rfl⟩ hhon_b' hstop_b' hmir_b'
      have hbody₁ : FirstNECellFamilyInvT_body qep g₁ m₁' s_cell₁ := by
        rcases hfam₁ with ⟨t, ht, tL, htL, hwin_cell⟩ | ⟨_, hcol₁, hrel₁⟩
        · exfalso
          rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
          · rw [hdoomed.cellWinPred_eq_false] at hwin_cell; cases hwin_cell
          · have hw := s_win_of_cellWinPred hwin_cell
            rw [hacc] at hw
            exact Bool.false_ne_true (hrel_sh.win_df_false.symm.trans hw)
        · exact ⟨hcol₁, hrel₁⟩
      have horig₁ : FirstNEInTransOriginInv qep sC₁.snaps g₁ s_cell₁ := by
        have hsnaps₁ : sC₁.snaps = sC₀.snaps :=
          (updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c_hon res_acc sC₀).2.2
        rw [hsnaps₁]
        exact firstNEInTransOriginInv_accept_step qep Q st' r.pos sC₀.snaps horig₀
      have h0_eq : s_cell₁ 0 none = (s_cell 0 none).accept Q st' r.pos := by
        dsimp only [s_cell₁]
        rw [(hbody.2 0 ht0).1.win_df_false]
        rfl
      have hsync₁' : SyncInv P Dh encPt encT idOf lam qep sC₁ sent m₁' g₁ (s_cell₁ 0 none) := by
        rw [h0_eq]; exact hsync₁
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
          sC₁ sent m₁' g₁ s_cell₁ :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody₁, horig₁, hsync₁'⟩)
      refine le_trans (hih ans sC₁ g₁ false false tr' sent m₁' s_cell₁ hinv₁) ?_
      refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u ans) sC sC₁ sent sent m' m₁' g₁ s_cell s_cell₁ fun t ht tL htL => ?_
      rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
      · exact Or.inl hdoomed
      · right
        have hlock_t := fwdAnswerC_deliver_lockstep Pt fig fs qep t tL Q w true ci? T pq' c_hon
          sC₀ sent false hrel_sh hsync.2.1 hInT₀ ans b'
          (by simpa [hr_g, hrcv, res_acc, pm] using hrun_ans)
        simp only [hr_g, hrcv] at hlock_t
        rw [cellSimRun_deliver_query_bind,
          runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hfa (deliverForgeHook Pt ℓ)),
          hlock_t.2, pure_bind, ← hacc]
  · have hInT_sC₀ : (sC₀.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false := by
      rw [List.any_eq_false]
      intro wc hwc
      rw [(updAmbSimStateC_fields Pt b sC).2.2.2.1] at hwc
      simp [hc'_not_hon wc hwc]
    have hwin_g : g.win = false := (hbody.2 0 ht0).1.win_mir_false
    have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g s_cell :=
      Or.inr (Or.inr ⟨rfl, rfl, hbody, horig₀, hsync₀⟩)
    cases hrcv : fig.receive (g.st Q) c' with
    | none =>
      have hrun_ans := onAnswer_rejected_run qep Q w true ci? T pq' sC₀.base
      have hrej_kept := updKeptOnRes_rejected Pt fig fs Q c' sC₀
      have hinj_g : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
          pure (some .rejected, g) := by
        rw [injectImpl_h1_run fig qep Q c' g hwin_g]
        simp [hinT_g, hsafe_g, hrcv]
      have hprobe_run :
          (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((some RecvResult.rejected, sC₀), (g, false)) := by
        rw [hfa (probeHook fig (qep + 1))]
        simpa [hrej_kept] using
          probeHook_fwdAnswerC_inject_run_of_eq fig fs qep Q w true ci? T pq' c' sC₀ g g false
            (some .rejected) (some .rejected) sC₀.base hInT_sC₀ hinj_g
            (by simpa [hrej_kept] using hrun_ans)
      obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf
        lam qep q Q w sC sC₀ g g (some RecvResult.rejected) tr hlazy hprobe_run
      rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
      refine le_trans (hih (some .rejected) sC₀ g false false tr' sent m' s_cell hinv₀) ?_
      refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u (some .rejected)) sC sC₀ sent sent m' m' g s_cell s_cell fun t ht tL htL => ?_
      rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
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
        have hcell_step :
            runCellStep fig qep t tL
              (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w true ci? T pq' c')
              sC₀ sent m' (s_cell t tL) =
            pure ((((some .rejected, sC₀), sent), m'), s_cell t tL) := by
          simpa [hrej_kept, updMirOnRes] using
            runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w true ci? T pq' c' sC₀ sent m'
              (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
              hInT_sC₀ hinj_c (by simpa [hrej_kept] using hrun_ans)
        rw [cellSimRun_deliver_query_bind,
          runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hfa (deliverForgeHook Pt ℓ)),
          hcell_step, pure_bind]
    | some v =>
      rcases v with ⟨st', t', i', m_out⟩
      by_cases hq : (qep + 1) + 1 < t'
      · have hrun_ans := onAnswer_rejected_run qep Q w true ci? T pq' sC₀.base
        have hrej_kept := updKeptOnRes_rejected Pt fig fs Q c' sC₀
        have hinj_g : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
            pure (some .rejected, g) := by
          rw [injectImpl_h1_run fig qep Q c' g hwin_g]
          simp [hinT_g, hsafe_g, hrcv, hq]
        have hprobe_run :
            (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
                (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
              pure ((some RecvResult.rejected, sC₀), (g, false)) := by
          rw [hfa (probeHook fig (qep + 1))]
          simpa [hrej_kept] using
            probeHook_fwdAnswerC_inject_run_of_eq fig fs qep Q w true ci? T pq' c' sC₀ g g false
              (some .rejected) (some .rejected) sC₀.base hInT_sC₀ hinj_g
              (by simpa [hrej_kept] using hrun_ans)
        obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT
          idOf lam qep q Q w sC sC₀ g g (some RecvResult.rejected) tr hlazy hprobe_run
        rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
        refine le_trans (hih (some .rejected) sC₀ g false false tr' sent m' s_cell hinv₀) ?_
        refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
          _ (u (some .rejected)) sC sC₀ sent sent m' m' g s_cell s_cell fun t ht tL htL => ?_
        rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
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
          have hcell_step :
              runCellStep fig qep t tL
                (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w true ci? T pq' c')
                sC₀ sent m' (s_cell t tL) =
              pure ((((some .rejected, sC₀), sent), m'), s_cell t tL) := by
            simpa [hrej_kept, updMirOnRes] using
              runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w true ci? T pq' c' sC₀ sent m'
                (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
                hInT_sC₀ hinj_c (by simpa [hrej_kept] using hrun_ans)
          rw [cellSimRun_deliver_query_bind,
            runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
              (hfa (deliverForgeHook Pt ℓ)),
            hcell_step, pure_bind]
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
            (m₁' := updMirOnRes Q res_acc m') hbody.1 hbody.2 ht'_le hinT_g hsafe_g hrcv with
          ⟨t₀, ht₀, tL₀, htL₀, hrel_sh₀, htriv₀, ht_eq₀, hwin₀⟩ |
          ⟨htriv_g, hg'_eq, hinv', hcells'⟩
        · obtain ⟨ans, b', hrun_ans, _, _⟩ :=
            onAnswer_run_pure qep Q w true ci? T pq' (some .rejected)
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
          rw [cellSimRun_deliver_query_bind,
            runCellStep_congr_run fig qep t₀ tL₀ _ _ sC sC₀ sent m' (s_cell t₀ tL₀)
              (hfa (deliverForgeHook Pt ℓ)),
            runCellStep_fwdAnswerC_inject_of_eq fig fs qep t₀ tL₀ Q w true ci? T pq' c' sC₀
              sent m' (s_cell t₀ tL₀) { s_cell t₀ tL₀ with win := true } (some .rejected) ans b'
              hInT_sC₀ hinj_c₀ hrun_ans,
            pure_bind]
          rfl
        · have hpos_lt : (⟨Q.other, t', i'⟩ : SM.Pos).epoch < min (g.epoch .A) (g.epoch .B) :=
            pos_epoch_lt_min_of_trivial hsync.2.2.1 hsafe_g htriv_g
          have hlt_Q : t' < g.epoch Q := by
            change (⟨Q.other, t', i'⟩ : SM.Pos).epoch < g.epoch Q
            cases Q <;> omega
          have hrcv_spec :=
            lFig8_receive_spec Pt P Dh encPt encT idOf lam hrcv
          have ht'_eq_c' : t' = c'.1.1 := hrcv_spec.2.1
          have hi'_eq_c' : i' = c'.2.1 := by
            have htcur_Q := hsync.2.2.2.2.2.2.2.1.htcur Q
            rcases hrcv_spec.2.2.2 with ⟨hnew, _⟩ | ⟨_, _, _, _, v₀, v', _, hfs⟩
            · omega
            · dsimp only [lFS, FSAEAD.fromAEADPRG] at hfs
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
          have hpos_c' : (⟨Q.other, t', i'⟩ : SM.Pos) = r.pos := by
            rcases hc'_ep with hep_succ | hfn
            · omega
            · rw [ht'_eq_c', hi'_eq_c', (hfn c_hon r hmem_hon hr_g).symm]
          have hr_m_kept :
              (updKeptOnRes fig fs Q c' res_acc sC₀).base.mir.inTransit Q.other w = some r_m :=
            hr_m₀
          obtain ⟨ans, b', hrun_ans, hhon_b', hstop_b', hmir_b'⟩ :=
            onAnswer_true_accepted_of_inTransit_some Pt qep Q w ci? T pq' t' i' (some m_out)
              (updKeptOnRes fig fs Q c' res_acc sC₀).base hr_m_kept
          dsimp only [updKeptOnRes] at hhon_b' hstop_b' hmir_b'
          rw [← hpos_eq, ← hpos_c'] at hmir_b'
          have hinj_g : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
              pure (res_acc, g.accept Q st' ⟨Q.other, t', i'⟩) := by
            rw [injectImpl_h1_run fig qep Q c' g hwin_g]
            simp [hinT_g, hsafe_g, hrcv, hq, htriv_g, res_acc]
          let sC₁ := { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' }
          have hprobe_run :
              (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
                  (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
                pure ((ans, sC₁), (g.accept Q st' ⟨Q.other, t', i'⟩, false)) := by
            rw [hfa (probeHook fig (qep + 1))]
            exact probeHook_fwdAnswerC_inject_run_of_eq fig fs qep Q w true ci? T pq' c' sC₀ g
              (g.accept Q st' ⟨Q.other, t', i'⟩) false res_acc ans b' hInT_sC₀ hinj_g hrun_ans
          obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT
            idOf lam qep q Q w sC sC₁ g (g.accept Q st' ⟨Q.other, t', i'⟩) ans tr hlazy hprobe_run
          rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
          rw [hg'_eq] at hinv' hcells'
          have hinvD' : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
              sC₁ sent (updMirOnRes Q res_acc m') (g.accept Q st' ⟨Q.other, t', i'⟩) s_cell' := by
            rcases hinv' with hwin' | ⟨_, hcol', hrel_all'⟩
            · exact Or.inl hwin'
            · refine Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol', hrel_all'⟩, ?_, ?_⟩)
              · have hsnaps₁ : sC₁.snaps = sC₀.snaps :=
                  (updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c' res_acc sC₀).2.2
                rw [hsnaps₁]
                exact hg'_eq ▸ firstNEInTransOriginInv_inject_step qep Q st' t' i' sC₀.snaps horig₀
              · have hsync' := syncInv_inject_accept_step P Dh encPt encT idOf lam qep Q hsync₀
                  hstop₀ hsafe_g htriv_g hrcv hhon_b' hstop_b' hmir_b'
                rcases hcells' 0 ht0 none (Finset.mem_insert_self none _) with
                  hdoomed0 | ⟨_, _, hs0_eq⟩
                · have hw0 := hdoomed0.2.2.2
                  rw [(hrel_all' 0 ht0).1.win_df_false] at hw0; nomatch hw0
                · dsimp only [updMirOnRes, res_acc, s_cell'] at hs0_eq ⊢
                  rwa [hs0_eq]
          refine le_trans (hih ans sC₁ (g.accept Q st' ⟨Q.other, t', i'⟩) false false tr' sent
            (updMirOnRes Q res_acc m') s_cell' hinvD') ?_
          refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
            _ (u ans) sC sC₁ sent sent m' (updMirOnRes Q res_acc m')
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
            rw [cellSimRun_deliver_query_bind,
              runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
                (hfa (deliverForgeHook Pt ℓ)),
              runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w true ci? T pq' c' sC₀
                sent m' (s_cell t tL) ((s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) res_acc ans b'
                hInT_sC₀ hinj_c hrun_ans,
              pure_bind]

end CryptoVerification.LibsignalSession.HeadlineV1

end
