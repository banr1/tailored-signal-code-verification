/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject

/-!
# Deliver step of the C coupling: known chain, honest salt

Closes the `deliver` step on a known chain when the SPQR salt matches the honest record (`c' = c`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

private theorem dksm_fwdCPure_self (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c : Fig8C Pt) (x : JointC PQ Pt ℓ) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel ci? T pq' (some c) c x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c x := by
  unfold fwdCPure
  simp

/-- Closes the known-chain `deliver` step when `c' = c`. -/
theorem closeByStateC_deliver_known_saltMatch {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) =
      some c)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
    (hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false)
    (hsalt : c.2.2.2 = effectiveHkdfSalt32 salt)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hinv.hsim.hpqInv Q) hspqr
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.huniq
    (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
    (fun r hr => ⟨(hinv.hsim.htrans_hon r hr).1, (hinv.hsim.htrans_hon r hr).2.1⟩)
    hinv.hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC₀, hfwd_eq⟩
  have hc₀_eq : c₀ = c := Option.some.inj (hhonC₀.symm.trans hhonC)
  subst c₀
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hsim.hhon (w, c) hc_mem).1 hparse with
    ⟨_, hsrk, hctr, hc_raw⟩
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, v, hvR, hsync⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hsrk_eq : h.senderRatchetKey = encT (Dh.dh (epExp g.epoch) Dh.base) :=
    Option.some.inj hg_key_sync
  have hdh : Dh.dh (epExp g.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
    hinj (hsrk_eq.symm.trans hsrk)
  have hle_g : g.epoch ≤ M := by
    have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
      refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
    cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
  have hg_ep_eq : g.epoch = c.1.1 :=
    hinv.hsim.hcoll g.epoch c.1.1 hle_g (hinv.hsim.hhon (w, c) hc_mem).2.1 hdh
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
  let i := h.counter.toNat + 1
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  have hc_eq_g : ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
    rw [hg_ep_eq, hT_dec, ← hsalt]
    exact hc_raw.symm
  have hpos_mir_ep : r_mir.pos.epoch = g.epoch := by
    rw [← hpos_fig8, hg_ep_eq]
    exact inTransit_fig8_pos_epoch_eq hinv.hsim.htrans_hon hr_fig8
  have hpos_le_epQ : r_mir.pos.epoch ≤ sC.base.mir.epoch Q := by
    rw [hpos_mir_ep]; exact hg_ep_le
  let mir' := sC.base.mir.accept Q () r_mir.pos
  have hmir_ep : mir'.epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () r_mir.pos hpos_le_epQ
  have hmir_idx : mir'.idx = sC.base.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
    hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hsim Q w hlen h body
    hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT mir' hmir_ep hmir_idx rc
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hstep_inTransit : ∀ k,
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
        (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c s_fig8
         let a := onAnswerPure qep Q w true (some ci) h.senderRatchetKey pq' z.1 sC.base
         (a.1, (a.2, z.2))) := by
    intro k
    rw [simRecvStep_deliver_inTransit_eq P ℓ Dh encPt encT decT idOf lam qep k Q w sC.base s_fig8
      hmeta.hstop hmeta.hwin_mir r_mir htr_mir hlen h body hparse haddrs c pq' salt hspqr
      hsalt.symm hhonC]
    simp only [hfind, hrej, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hgenC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true (some ci) h.senderRatchetKey pq'
        none c (sC, s_fig8, false) := by
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
      Bool.not_true, Bool.false_and, hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs,
      hspqr, hpan, hhonC, hsalt, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej]
    exact dksm_fwdCPure_self P ℓ Dh encPt encT idOf lam qep Q w true (some ci) h.senderRatchetKey
      pq' c (sC, s_fig8, false)
  cases hfig : sm.receive (s_fig8.st Q) c with
  | none =>
    have hdel_fig8 : deliverPure sm SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
      unfold deliverPure
      simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig, SM.Config.h1,
        Bool.false_and]
    refine closeByStateC_deliver_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
      cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir
      (fun rc => by
        have h2 := (hstep_all rc).2 hrej
        dsimp only at h2
        rw [hc_eq_g, hfig] at h2
        exact h2)
      huse
      (fun k => by
        rw [hstep_inTransit k, hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
        rfl)
      (by
        rw [hgenC]
        unfold fwdCPure
        dsimp only
        rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
        rfl)
      ih
  | some res_fig =>
    rcases res_fig with ⟨st', t', i', pub, m⟩
    have hfig' : sm.receive (s_fig8.st Q) c = some (st', t', i', pub, m) := hfig
    have h2_0 := (hstep_all 0).2 hrej
    dsimp only at h2_0
    rw [hc_eq_g, hfig'] at h2_0
    rcases h2_0 with ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw₀, hm_raw₀, _⟩
    subst ht' hi'
    let ans : Option (RecvResult (Plain ℓ)) :=
      some (.accepted g.epoch i (if sC.base.mir.chall.contains r_mir.pos then none else some m))
    let s' : SimState PQ Pt ℓ :=
      { sC.base with
        mir := mir',
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
    let kept' := Function.update sC.kept Q
      (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
    let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s', kept := kept' }
    let s_fig8' := s_fig8.accept Q st' r_mir.pos
    let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
    let s_R' := s_R.accept Q st_R' r_mir.pos
    have hdel_fig8 : deliverPure sm SM.Config.h1 Q c s_fig8 =
        (some (.accepted g.epoch i (if sC.base.mir.chall.contains r_mir.pos then none else some (pub, m))),
         s_fig8') := by
      unfold deliverPure
      simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig', SM.Config.h1,
        Bool.false_and, hpos_fig8, hmeta.hchall_fig8]
      rfl
    have hstep_sim : ∀ k,
        simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
          (ans, (s', s_fig8')) := by
      intro k
      rw [hstep_inTransit k, hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
      unfold onAnswerPure onAcceptPure
      simp only [htr_mir, ↓reduceIte]
      cases hch : sC.base.mir.chall.contains r_mir.pos <;>
        simp only [ans, s', mir', hch, ↓reduceIte, Bool.false_eq_true,
          Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
    have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (ans, (sC', s_fig8', false)) := by
      rw [hgenC]
      unfold fwdCPure
      dsimp only
      rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
      unfold onAnswerPure onAcceptPure
      simp only [htr_mir, ↓reduceIte]
      cases hch : sC.base.mir.chall.contains r_mir.pos <;>
        simp only [ans, sC', s', mir', kept', sm, hch, ↓reduceIte, Bool.false_eq_true,
          Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
    have hstepC : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
        pure (ans, ((sC', s_fig8', false), ec)) := fun k =>
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) ec hinv.hsim.hec (huse k)
        (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true
          (sC.base, s_fig8) (by rw [hstep_sim k]; exact hmeta.hstop))
        _ hresC hmir_ep
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      have h2_rc := (hstep_all rc).2 hrej
      dsimp only at h2_rc
      rw [hc_eq_g, hfig'] at h2_rc
      rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
      rw [hrec_rc]
      dsimp only
      rw [← hm_raw, hpos_R, hmeta.hchall_R]
    have hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir := by
      unfold remWin
      rw [winCount_accept_of_le sC.base.mir Q () r_mir.pos hpos_le_epQ]
    have hold : c.1.1 ≤ (s_fig8.st Q).tcur := by
      rw [← hg_ep_eq]
      exact ((hinv.hkept.hvR Q g.epoch).mp (by simp [hvR])).1
    have hkept' : KeptInv P Dh encPt encT idOf lam sC' s_fig8' :=
      keptInv_recv_accept hinv.hkept Q (hinv.hsim.hst_id Q) c st' _ hfig' rfl rfl
    have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp :=
      epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _ hinv.hsync Q c st' _ hfig' hold rfl
        (fun hw => hw) (fun _ hwc => hwc)
    have hinv' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec
        winBefore epExp := by
      subst hst'
      exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8
        ec winBefore epExp hinv Q ci g i pq' hg_elem v' hsync' r_mir.pos hpos_mir_ep hpq' s' rfl
        s_fig8' rfl s_R' rfl kept' hkept' hsync8'
    exact closeByStateC_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R s_R' sC sC' s_fig8 s_fig8' false false ec ec winBefore
      ans (stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R) hstepR (hstepC none)
      (fun idx _ => hstepC (some idx)) rfl hrem
      (ih ans s_R' sC' s_fig8' false ec winBefore epExp hinv')

end CryptoGames.LibsignalSM.Proofs.Refinement
