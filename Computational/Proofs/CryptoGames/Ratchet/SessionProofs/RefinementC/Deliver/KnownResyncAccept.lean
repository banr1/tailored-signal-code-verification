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
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep

/-!
# Deliver step: known chain, case 3a resync accept

Closes the accepting half of `closeByStateC_deliver_known_resync`, where `resyncC` delivers the
honest record to Fig. 8 and both sides accept with matching plaintext.
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

/-- Closes `deliver` on a known chain in case 3a when `predictReceive` and Fig. 8 both accept. -/
theorem closeByStateC_deliver_known_resync_accept {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hsafe : sC.base.mir.safeInj 3 = false)
    {x : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) =
      some (some x))
    {st' : Fig8St Pt} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some (st', x))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
      some (st', (x.1, x.2.1, pm)))
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
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  set c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hinv.hsim.hpqInv Q) hspqr
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.huniq
    (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
    (fun r' hr' => ⟨(hinv.hsim.htrans_hon r' hr').1, (hinv.hsim.htrans_hon r' hr').2.1⟩)
    hinv.hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, hc₀_mem, hc₀_sender, hr_fig8, hpos_fig8, hhonC₀, _⟩
  have hc₀_eq : c₀ = c := Option.some.inj (hhonC₀.symm.trans hhonC)
  subst c₀
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]
    exact inTransit_fig8_pos_epoch_eq hinv.hsim.htrans_hon hr_fig8
  rcases hinv.hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨hver, hsrk, hctr, hc_raw⟩
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT_map : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, hg_recv, hg_key_ep, v, hvR, hsync⟩
  have hg_ep_eq : g.epoch = c.1.1 := by
    have hnot_none : g.key.isNone = false := by rw [hg_key]; rfl
    rw [hnot_none] at hg_key_ep
    simp only [Bool.false_eq_true, ↓reduceIte, hg_key, hsrk, Option.some.injEq] at hg_key_ep
    have hle1 : g.epoch ≤ M := by
      have : g.epoch ≤ maxActiveEp sC.base.mir Q := by
        unfold maxActiveEp; omega
      cases Q <;> [exact le_trans this (le_max_left _ _); exact le_trans this (le_max_right _ _)]
    exact hinv.hsim.hcoll g.epoch c.1.1 hle1 hc_le_M (hinj hg_key_ep.symm)
  have hpos_ep : r_mir.pos.epoch = g.epoch := hpos_mir_ep.trans hg_ep_eq.symm
  have hpos_le_epQ : r_mir.pos.epoch ≤ sC.base.mir.epoch Q := by
    rw [hpos_ep]; exact hg_ep_le
  have hg_ep_tcur : g.epoch ≤ (s_fig8.st Q).tcur := by
    rw [hinv.hsim.htcur Q]; exact hg_ep_le
  have hc1 : c.1 = (g.epoch, decT h.senderRatchetKey) := by
    rw [hg_ep_eq, hT_dec]; exact congrArg Prod.fst hc_raw
  have hc21 : c.2.1 = i := congrArg (fun z => z.2.1) hc_raw
  have hc221 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
    congrArg (fun z => z.2.2.1) hc_raw
  have hc'_eq_g : ((g.epoch, decT h.senderRatchetKey), i,
      (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c' := by
    dsimp only [c']
    rw [hc1, hc21, hc221]
  set pos := r_mir.pos
  have hmir_ep : (sC.base.mir.accept Q () pos).epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hpos_le_epQ
  have hmir_idx : (sC.base.mir.accept Q () pos).idx = sC.base.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
    hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hsim Q w hlen h body
    hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT_map
    (sC.base.mir.accept Q () pos) hmir_ep hmir_idx rc
  rcases x with ⟨t', i', pub, m⟩
  have hfig'_raw : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
        h.counter.toNat + 1, (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
      some (st', t', i', pub, m) := by
    rw [show ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
        h.counter.toNat + 1, (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c'
        from hc'_eq_g]
    exact hfig'
  have hstep0 := (hstep_all 0).2 hrej
  dsimp only at hstep0
  rw [hfig'_raw] at hstep0
  rcases hstep0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
  subst ht' hi'
  dsimp only at hfig
  set s' : SimState PQ Pt ℓ :=
    { sC.base with
      mir := sC.base.mir.accept Q () pos
      pq := Function.update sC.base.pq Q pq'
      unackA := sC.base.unackA && Q != Party.A
      chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
  set kept' := Function.update sC.kept Q
    (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
  set sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s', kept := kept' }
  set s_fig8' := s_fig8.accept Q st' pos
  set s_R' := s_R.accept Q (expectedGhost P Dh encPt spkKey s' Q st' (ec Q)) pos
  set ans : Option (RecvResult (Plain ℓ)) :=
    some (.accepted g.epoch i (if sC.base.mir.chall.contains pos then none else some m))
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')) := by
    rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
    congr 1; funext rc
    have hstep_rc := (hstep_all rc).2 hrej
    dsimp only at hstep_rc
    rw [hfig'_raw] at hstep_rc
    rcases hstep_rc with ⟨_, _, _, _, m_raw, hm_eq, hrec_rc⟩
    rw [hrec_rc]
    dsimp only
    rw [← hm_eq, hpos_R, hmeta.hchall_R]
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hstops : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvStops simRecvStep
    dsimp only
    rw [recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan, hmeta.hstop, hmeta.hwin_mir, htr_mir]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and, Option.isNone_some, hlen,
      Bool.not_true, Bool.not_false, Bool.false_and, hparse, haddrs, hspqr, hpan, hfind]
    split
    · exact hmeta.hstop
    · unfold onAnswerPure
      cases (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 sC.base Q _ s_fig8).1 with
      | none => exact hmeta.hstop
      | some res =>
        cases res with
        | rejected => exact hmeta.hstop
        | accepted t_a i_a pm_a =>
          unfold onAcceptPure
          simp [htr_mir, hmeta.hstop]
  have hstepC_res : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (ans, (sC', s_fig8', false)) := by
    unfold simRecvStepC simRecvStepCGen
    dsimp only
    have hsalt_if : (if c.2.2.2 = effectiveHkdfSalt32 salt then c else
        ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
          h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) = c' := by
      simp only [hsalt, ↓reduceIte]
      exact hc'_eq_g
    have hc_ne_c' : decide (c ≠ c') = true := by
      refine decide_eq_true (fun h_eq => hsalt ?_)
      exact congrArg (fun z : Fig8C Pt => z.2.2.2) h_eq
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Bool.true_and, Option.isNone_some, hlen, Bool.not_true, Bool.false_and,
      hparse, haddrs, Bool.not_eq_true', hspqr, hpan, hhonC, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej,
      hsalt_if]
    unfold fwdCPure deliverPure onAcceptPure
    simp only [hc_ne_c', hsafe, Bool.not_false, Bool.and_self, ↓reduceIte, heval,
      hmeta.hwin_fig8, Bool.false_eq_true, hr_fig8, hfig, SM.Config.h1, Bool.false_and,
      hpos_fig8, hmeta.hchall_fig8, htr_mir]
    rfl
  have hstepC : ∀ k,
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
      pure (ans, ((sC', s_fig8', false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep
      k Q w (sC, s_fig8, false) ec hinv.hsim.hec (huse k) (hstops k) _ hstepC_res hmir_ep
  have hrem_le : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir := by
    unfold remWin
    rw [winCount_accept_of_le sC.base.mir Q () pos hpos_le_epQ]
  have hkept' : KeptInv P Dh encPt encT idOf lam sC' s_fig8' :=
    keptInv_recv_accept hinv.hkept Q (hinv.hsim.hst_id Q) c st' (g.epoch, i, pm) hfig rfl rfl
  have hold : c.1.1 ≤ (s_fig8.st Q).tcur := by
    rw [← hg_ep_eq]; exact hg_ep_tcur
  have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp :=
    epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _
      hinv.hsync Q c st' (g.epoch, i, pm) hfig hold rfl (fun hw => hw) (fun _ hwc => hwc)
  have hinv' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
      s_R' sC' s_fig8' ec winBefore epExp := by
    subst hst'_eq
    exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8
      ec winBefore epExp hinv Q ci g i pq' hg_elem v' hsync' pos hpos_ep hpq' s' rfl s_fig8' rfl
      s_R' rfl kept' hkept' hsync8'
  exact closeByStateC_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R s_R' sC sC' s_fig8 s_fig8' false false ec ec winBefore
    ans (stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R)
    hstepR (hstepC none) (fun idx _ => hstepC (some idx)) rfl hrem_le
    (ih ans s_R' sC' s_fig8' false ec winBefore epExp hinv')

end CryptoGames.LibsignalSM.Proofs.Refinement
