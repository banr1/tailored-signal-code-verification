/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Combinators
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC

/-!
# Deliver step of the C coupling: new epoch, counter jump out of range

Closes the new-epoch `deliver` step when the message counter exceeds the skip bound (`25000 < i - 1`).
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

/-- Closes the new-epoch `deliver` step when `25000 < h.counter.toNat`, where both sides reject. -/
theorem closeByStateC_deliver_newChain_jump {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1)
    (hjump : 25000 < h.counter.toNat + 1 - 1)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  set spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  have hsim := hinv.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  have hsync := deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.huniq
    (fun wc hwc => ⟨(hsim.hhon wc hwc).1, (hsim.hhon wc hwc).2.1⟩)
    (fun r hr => ⟨(hsim.htrans_hon r hr).1, (hsim.htrans_hon r hr).2.1⟩) hsim.hcoll Q w htr_mir
  rcases hsync with ⟨⟨r_R, htr_R, hpos_R⟩, c_sync, r_fig8, hc_mem_sync, hc_sender_sync,
    hr_fig8, hpos_fig8, hhonC_sync, hfwd_eq⟩
  have hc_eq : c_sync = c := Option.some.inj (hhonC_sync.symm.trans hhonC)
  rw [hc_eq] at hr_fig8
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]
    exact inTransit_fig8_pos_epoch_eq hsim.htrans_hon hr_fig8
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨hver, hsrk, hctr, hc_eq_raw⟩
  rcases hhon_c with ⟨hw_c, hw_len_c, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  dsimp only at ht1 hi1 hi32
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
      rw [hsim.hepExp0]
      exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  have ⟨hinw_Q, hQ_recv⟩ := inWin_eq_false_of_senderOf_succ sC.base.mir Q (hepoch ▸ hc_sender)
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  have hT_dec' : decT h.senderRatchetKey = some T := by
    dsimp only [T, t]; rw [← hepoch, hsrk, hdec]
  have hT_ne0' : T ≠ 0 := by
    dsimp only [T, t]; rw [← hepoch]; exact hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
  have hevict_f : (Option.map (fun c : Fig8C Pt => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) (some c) == some true) = false := by
    simp [hepoch]
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]; exact hQ_recv
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]
      exact List.mem_map_of_mem hg'
    rw [List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]
    omega
  have hpos_mir_t : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by
    rw [hpos_mir_ep, hepoch]
  have hmir'_ep_tcur : (sC.base.mir.accept Q () r_mir.pos).epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  letI : DecidableEq PQ := Classical.decEq PQ
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
    (sC.base.mir.accept Q () r_mir.pos) hmir'_ep_tcur
  dsimp only at hnew
  set g_init : GhostChain := ⟨some h.senderRatchetKey, (s_fig8.st Q).tcur + 1, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) ((s_fig8.st Q).tcur + 1) i
      (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := by
    intro rc
    rw [hst_R_Q]
    refine (hnew rc).1 ?_
    rw [hg_rej_eq]
    exact decide_eq_true hjump
  have hjump0 : 25000 < h.counter.toNat := by omega
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  cases hspk : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) with
  | false =>
    refine closeByStateC_deliver_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
      Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hrcv huse_all ?_ ?_ ih
    · intro k
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
    · unfold simRecvStepC simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
  | true =>
    have hstop_amb :
        (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
          (sC.base, s_fig8) ec).2.1.stopped = true := by
      unfold simRecvStepEager simRecvStep
      simp [huse_all (some sC.base.amb), hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen,
        hparse, haddrs, hspqr, hpan, hfind, hepoch, hzero_f, hinw_Q, hspk]
    have hres_amb_none :
        simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8) =
          (some .rejected, ({ sC.base with amb := sC.base.amb + 1 }, s_fig8)) := by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
    have hresC_amb :
        simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) := by
      unfold simRecvStepC simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
    have hstep_none :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
          (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep
        none Q w (sC, s_fig8, false) ec hsim.hec (huse_all none)
        (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true
          (sC.base, s_fig8) (by rw [hres_amb_none]; exact hmeta.hstop))
        (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false))
        hresC_amb rfl
    exact closeByStateC_deliver_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ
      post x₀ Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hrcv hstop_amb hstep_none
      (fun s_R' sC' s_fig8' fl' ec' winBefore' epExp' hinv' =>
        ih (some .rejected) s_R' sC' s_fig8' fl' ec' winBefore' epExp' hinv')

end CryptoGames.LibsignalSM.Proofs.Refinement
