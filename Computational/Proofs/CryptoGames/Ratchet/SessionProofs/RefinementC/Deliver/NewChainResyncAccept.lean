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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep

/-!
# Deliver step of the C coupling: new epoch, resync accept

Proves `closeByStateC_deliver_newChain_resync_accept`, the accepting case of a new-epoch case-3a
resync delivery where `predictReceiveWithSnapshots` and Fig. 8 both accept.
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

private theorem d4nb_onAnswerPure_stopped (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s₁ : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s₁).2.stopped = s₁.stopped := by
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      unfold onAnswerPure onAcceptPure
      dsimp only
      cases isDel
      · by_cases h1 : qep + 1 < t
        · simp [h1]
        · by_cases h2 : s₁.mir.trivial 3 { sender := Q.other, epoch := t, idx := i } = true <;>
            simp [h1, h2]
      · cases s₁.mir.inTransit Q.other w <;> rfl

private theorem d4nb_evalC_congr_base (P : Params PQ PQC)
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8))
    (c c' : Fig8C Pt) :
    predictReceiveWithSnapshots (fig := fig) (fs := fs) P { sC with base := s' } Q w c c' =
      predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' := rfl

/-- Closes the `deliver` step for a new epoch under case-3a resync when both
`predictReceiveWithSnapshots` and Fig. 8 accept. -/
theorem closeByStateC_deliver_newChain_resync_accept {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hjump : ¬ 25000 < h.counter.toNat + 1 - 1)
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
  letI : DecidableEq PQ := Classical.decEq PQ
  have hmeta := hinv.hsim.hmeta
  have hD0 := stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hinv.hsim.hpqInv Q) hspqr
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  have hQQ : Q.other.other = Q := by cases Q <;> rfl
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.huniq
    (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
    (fun rec_f hrec_f => ⟨(hinv.hsim.htrans_hon rec_f hrec_f).1, (hinv.hsim.htrans_hon rec_f hrec_f).2.1⟩)
    hinv.hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC₀, _⟩
  have hc₀_eq : c = c₀ := Option.some.inj (hhonC.symm.trans hhonC₀)
  subst hc₀_eq
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]
    exact inTransit_fig8_pos_epoch_eq hinv.hsim.htrans_hon hr_fig8
  rcases hinv.hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨hver, hsrk, hctr, hc_raw⟩
  rcases hhon_c with ⟨hw_eq, _, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set fs := lFS P.C P.codec ℓ encT idOf 25000
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    dsimp only [spkKey]
    rw [hsrk, ← hinv.hsim.hepExp0]
    intro heq
    have ht0 := hinv.hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) (hinj heq)
    omega
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false := decide_eq_false (not_not.mpr hepoch)
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by
    rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  have hep_other : sC.base.mir.epoch Q.other = sC.base.mir.epoch Q + 1 := by
    have h1 : sC.base.mir.epoch Q + 1 ≤ sC.base.mir.epoch Q.other := by
      rw [← hepoch, ← hc_sender]; exact hc_le_sender
    have h2 : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
      have := (hinv.hsim.hep_adj Q.other).2
      rwa [hQQ] at this
    omega
  have hinw_other : inReceiveOnlyEpoch sC.base.mir Q.other = false := by
    rw [Bool.eq_false_iff]
    intro hinw_O
    have := (hinv.hsim.hep_adj Q.other).1 hinw_O
    rw [hQQ] at this
    omega
  have hpos_AB : 0 < sC.base.mir.epoch .A ∨ 0 < sC.base.mir.epoch .B := by
    cases Q with
    | A => exact Or.inr (by change 0 < sC.base.mir.epoch Party.A.other; omega)
    | B => exact Or.inl (by change 0 < sC.base.mir.epoch Party.B.other; omega)
  have hamb_strict : sC.base.amb + r < q := hinv.hsim.hamb_strict hpos_AB
  have hamb_lt : sC.base.amb < q := by omega
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  have hT_dec' : decT h.senderRatchetKey = some T := by
    dsimp only [T, t]; rw [← hepoch]; exact hT_dec
  have hT_ne0' : T ≠ 0 := by
    dsimp only [T, t]; rw [← hepoch]; exact hT_ne0
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
  have hzero_T : (some T == some (0 : Pt)) = false := by
    simp [beq_eq_false_iff_ne, hT_ne0']
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hinv.hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hinv.hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hinv.hsim.htcur Q]; exact hQ_recv
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
    have hg₀_le := (hinv.hsim.hchains_sync Q g₀ hg₀).1
    rw [hinv.hsim.htcur Q, ← hgep]
    omega
  have hpos_mir_t : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by
    rw [hpos_mir_ep, hepoch]
  have hmir'_ep_tcur : (sC.base.mir.accept Q () r_mir.pos).epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, hinv.hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  set c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  have hc'_eq_new : (((s_fig8.st Q).tcur + 1, some T), i,
      (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c' := by
    dsimp only [c', T, t]
    rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
    dsimp only at hepoch hT_c hctr hraw_c ⊢
    rw [hinv.hsim.htcur Q, ← hepoch, ← hT_c, hctr, ← hraw_c]
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hinv.hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
    (sC.base.mir.accept Q () r_mir.pos) hmir'_ep_tcur
  dsimp only at hnew
  rw [hc'_eq_new, hinv.hsim.htcur Q] at hnew
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hi32_f : decide (2 ^ 32 ≤ i) = false :=
    decide_eq_false (by dsimp only [i]; omega)
  have hjump_f : decide (25000 < i - 1) = false := decide_eq_false hjump
  have hrej_false : g_init.rejects i = false := by
    rw [hg_rej_eq]; exact hjump_f
  rcases x with ⟨t', i', pub, m⟩
  have hfig'_raw : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      some (st', t', i', pub, m) := hfig'
  have hnew0 := (hnew 0).2 hrej_false
  rw [hfig'_raw] at hnew0
  rcases hnew0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
  subst ht' hi'
  dsimp only at hfig heval
  change sm.receive (s_fig8.st Q) c = some (st', t, i, pm) at hfig
  set p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (epExp (sC.base.mir.epoch Q)) T)
  set pn_new := BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
  have hidx_lt32 : sC.base.mir.idx Q < 2 ^ 32 := by
    have := hinv.hsim.hidx_le Q; omega
  have hpn_eq : (if BitVec.ofNat 32 v_prev.lastIndex = 0 then (0 : BitVec 32)
      else BitVec.ofNat 32 v_prev.lastIndex - 1) = pn_new := by
    rw [hv_last]
    exact bitVec_pred_eq_of_lt (sC.base.mir.idx Q) hidx_lt32
  set ans : Option (RecvResult (Plain ℓ)) :=
    some (.accepted t i (if sC.base.mir.chall.contains r_mir.pos then none else some m))
  set s_fig8' := s_fig8.accept Q st' r_mir.pos
  let mir' := sC.base.mir.accept Q () r_mir.pos
  have hinw'_Q : inReceiveOnlyEpoch mir' Q = true := by
    unfold inReceiveOnlyEpoch
    dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _), hQ_recv]
  have hinw'_O : inReceiveOnlyEpoch mir' Q.other = inReceiveOnlyEpoch sC.base.mir Q.other := by
    unfold inReceiveOnlyEpoch
    dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
    have hne : Q.other ≠ Q := by cases Q <;> decide
    simp [Function.update_of_ne hne]
  have hupd_ec := (updateAllEagerCoins_enter_inWin Q sC.base.mir mir' ec hinw_Q hinw'_Q hinw'_O hinv.hsim.hec).1
  have hwin_succ : winCount mir' = winCount sC.base.mir + 1 :=
    winCount_accept_succ sC.base.mir Q () r_mir.pos hinw_Q hpos_mir_t
  have hwin'_le_qep : winCount mir' ≤ qep := by
    refine winCount_le_of_epoch_le ?_ ?_
    · dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
      by_cases hQA : Q = .A
      · subst hQA
        have hB : sC.base.mir.epoch .B ≤ qep := hinv.hsim.hep_le .B
        have hAB : sC.base.mir.epoch .B = sC.base.mir.epoch .A + 1 := hep_other
        simp [Function.update_self, hpos_mir_t]; omega
      · simp [Function.update_of_ne (Ne.symm hQA), hinv.hsim.hep_le .A]
    · dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
      by_cases hQB : Q = .B
      · subst hQB
        have hA : sC.base.mir.epoch .A ≤ qep := hinv.hsim.hep_le .A
        have hBA : sC.base.mir.epoch .A = sC.base.mir.epoch .B + 1 := hep_other
        simp [Function.update_self, hpos_mir_t]; omega
      · simp [Function.update_of_ne (Ne.symm hQB), hinv.hsim.hep_le .B]
  have hrem_eq : remWin qep sC.base.mir = remWin qep mir' + 1 := by
    unfold remWin; omega
  set d₁ : ℝ≥0∞ := (sC.base.honest.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh +
    ((sC.base.mir.epoch Q + 2 : ℕ) : ℝ≥0∞) * δ
  have hbad_le : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {rc | deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T rc = true} ≤ d₁ :=
    deliverBadCoin_prob_le P encPt Dh δ hδ sC.base epExp Q p₁.1 T
  have hslack_le : d₁ + stepSlack P encPt Dh q qep δ (remWin qep mir') ≤
      stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir) := by
    rw [hrem_eq]
    have hlen_le : sC.base.honest.length ≤ q := by have := hinv.hsim.hhon_len; omega
    have hpts_le : sC.base.mir.epoch Q + 2 ≤ q + qep + 2 := by have := hinv.hsim.hep_le Q; omega
    exact stepSlack_step_le P encPt Dh q qep δ hlen_le hpts_le
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  have hspk_def : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb := rfl
  have hi_def : h.counter.toNat + 1 = i := rfl
  have hsm_def : lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam = sm := rfl
  have hfs_def : lFS P.C P.codec ℓ encT idOf 25000 = fs := rfl
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hc_ne_c' : decide (c ≠ c') = true :=
    decide_eq_true (fun hcc' => hsalt (congrArg (fun z : Fig8C Pt => z.2.2.2) hcc'))
  have hmkC_eq : (if c.2.2.2 = effectiveHkdfSalt32 salt then c
      else ((sC.base.mir.epoch Q + 1, some T), (i, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))) = c' := by
    rw [ite_eq_right hsalt, ← hinv.hsim.htcur Q]
    exact hc'_eq_new
  have hstops_of_not_amb : ∀ k, ((inReceiveOnlyEpoch sC.base.mir Q || spkAmb) && k == some sC.base.amb) = false →
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
    intro k hk
    rw [hinw_Q, Bool.false_or] at hk
    refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
    unfold simRecvStep
    dsimp only
    have hstop' : ¬ (sC.base.stopped = true) := by rw [hmeta.hstop]; decide
    have hwin' : ¬ (sC.base.mir.win = true) := by rw [hmeta.hwin_mir]; decide
    rw [ite_eq_right hstop', ite_eq_right hwin']
    simp only [htr_mir, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
      hbeq_true, hfind, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hspk_def, hk,
      hi_def, hjump_f, hi32_f, Bool.or_self, hT_dec', hzero_T, d4nb_onAnswerPure_stopped]
    cases spkAmb <;> exact hmeta.hstop
  have hstop_amb : spkAmb = true →
      (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true (sC.base, s_fig8) ec).2.1.stopped = true := by
    intro hspk
    unfold simRecvStepEager
    simp only [huse_all (some sC.base.amb), Bool.false_eq_true, ↓reduceIte]
    unfold simRecvStep
    dsimp only
    have hstop' : ¬ (sC.base.stopped = true) := by rw [hmeta.hstop]; decide
    have hwin' : ¬ (sC.base.mir.win = true) := by rw [hmeta.hwin_mir]; decide
    rw [ite_eq_right hstop', ite_eq_right hwin']
    simp only [htr_mir, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
      hbeq_true, hfind, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hspk_def, hspk,
      beq_self_eq_true, Bool.and_self, hT_dec', hzero_T]
  set kept' := Function.update sC.kept Q (Kept.recv (fig := sm) (fs := fs) c (sC.kept Q))
  have hstepC_eq : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      let s₁ : SimState PQ Pt ℓ := if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
      let s'_new : SimState PQ Pt ℓ :=
        { s₁ with
          mir := mir',
          pq := Function.update sC.base.pq Q pq',
          unackA := sC.base.unackA && Q != Party.A,
          chains := Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)) }
      (ans, ({ sC with base := s'_new, kept := kept' }, s_fig8', false)) := by
    unfold simRecvStepC simRecvStepCGen
    dsimp only
    have hstop' : ¬ (sC.base.stopped = true) := by rw [hmeta.hstop]; decide
    have hwin' : ¬ (sC.base.mir.win = true) := by rw [hmeta.hwin_mir]; decide
    rw [ite_eq_right hstop', ite_eq_right hwin']
    simp only [htr_mir, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
      hbeq_true, hfind, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hspk_def,
      hi_def, hjump_f, hi32_f, Bool.or_self, hT_dec', hzero_T, hmkC_eq]
    unfold fwdCPure deliverPure onAcceptPure
    cases hspk : spkAmb <;> {
      simp only [↓reduceIte, Bool.false_eq_true, d4nb_evalC_congr_base,
        hsm_def, hfs_def, hc_ne_c', hsafe, Bool.not_false, Bool.and_self, heval, hi_def,
        hmeta.hwin_fig8, hr_fig8, hfig, SM.Config.h1, Bool.false_and,
        hpos_fig8, hmeta.hchall_fig8, htr_mir]
      cases hch : sC.base.mir.chall.contains r_mir.pos <;>
        simp only [ans, kept', s_fig8', mir', g_init, t, i, hch, ↓reduceIte, Bool.false_eq_true,
          Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] }
  have hinvCX_of : ∀ (amb' : ℕ) (winBefore' : ℕ → Bool) (rc : BitVec 256),
      amb' + (r - 1) ≤ q → amb' + (r - 1) < q →
      (∀ j < amb', winBefore' j = false) →
      deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T rc = false →
      let s'_new : SimState PQ Pt ℓ :=
        { sC.base with
          mir := mir',
          pq := Function.update sC.base.pq Q pq',
          unackA := sC.base.unackA && Q != Party.A,
          chains := Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)),
          amb := amb' }
      let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
      let s_R' := s_R.accept Q
        (withEager (toGhost P (resolveSim spkKey s'_new) Q st') p₂.1
          (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) r_mir.pos
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
        s_R' { sC with base := s'_new, kept := kept' } s_fig8'
        (Function.update ec Q rc) winBefore' (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
    intro amb' winBefore' rc hamb'_le hamb'_strict hwb' hbad_f s'_new p₂ s_R'
    rcases deliverBadCoin_eq_false P encPt Dh sC.base epExp Q p₁.1 T rc hbad_f with ⟨hspur_f, hcoll_f⟩
    have hsimr : SimInvC P (InvB Inv q r) ℓ Dh encPt encT qep q (r - 1) x₀
        s_R' s'_new s_fig8' (Function.update ec Q rc) winBefore'
        (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
      dsimp only [s_R', s'_new, s_fig8', g_init]
      rw [hst'_eq, hsrk']
      exact simInvC_deliver_newChain P (InvB Inv q r) Dh encPt encT qep q r x₀ hinv.hsim Q
        hinw_Q hQ_recv hinw_other hep_other i pq' rc amb' hamb'_le hamb'_strict hwb'
        r_mir.pos hpos_mir_t v' (hsrk' ▸ hsync') hT_ne0' hspur_f hcoll_f hpq'
    refine
      { hsim := SimInvC.mono hsimr (fun R => InvB.mono (Nat.sub_le r 1) (hsimr.hpqInv R))
        huniq := hinv.huniq
        hkept := keptInv_recv_accept hinv.hkept Q (hinv.hsim.hst_id Q) c st' (t, i, pm) hfig rfl rfl
        hidx := ?_
        hsync := epochSync_recv_new P Inv Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec
          winBefore epExp hinv Q w c c hc_mem hc_sender rfl
          (by rw [hinv.hsim.htcur Q]; exact hepoch) st' (t, i, pm) hfig sC.base.honest s_fig8' rfl
          (fun hw' => by dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete] at hw'; exact hw')
          (fun _ h => h) }
    intro wc hwc hep_wc
    dsimp only [s'_new] at hwc hep_wc ⊢
    by_cases hSQ : Party.senderOf wc.2.1.1 = Q
    · exfalso
      have hsends_wc := (hinv.hsim.hhon wc hwc).2.2.1
      have hep'_Q : mir'.epoch Q = sC.base.mir.epoch Q + 1 := by
        dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
        simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _)]
      rw [hSQ, hep'_Q] at hep_wc
      rw [hSQ, hep_wc, hQ_recv] at hsends_wc
      cases hsends_wc
    · have hep'_ne : mir'.epoch (Party.senderOf wc.2.1.1) = sC.base.mir.epoch (Party.senderOf wc.2.1.1) := by
        dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
        simp [Function.update_of_ne hSQ]
      rw [hep'_ne] at hep_wc
      exact hinv.hidx wc hwc hep_wc
  cases hspk : spkAmb with
  | false =>
    set s'_new : SimState PQ Pt ℓ :=
      { sC.base with
        mir := mir',
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)) }
    set sC'_new : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s'_new, kept := kept' }
    set fR := fun rc : BitVec 256 =>
      let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
      (ans, s_R.accept Q
        (withEager (toGhost P (resolveSim spkKey s'_new) Q st') p₂.1
          (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) r_mir.pos)
    set fS := fun rc : BitVec 256 =>
      (ans, ((sC'_new, s_fig8', false), Function.update ec Q rc))
    have hstepR_eq :
        stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fR rc)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      have hnew_rc := (hnew rc).2 hrej_false
      rw [hfig'_raw] at hnew_rc
      rcases hnew_rc with ⟨_, _, _, _, m_raw', hm_eq', hrec_rc, _⟩
      rw [hpn_eq] at hrec_rc
      rw [hst_R_Q]
      have hres_push :
          { mir := sC.base.mir.accept Q () r_mir.pos,
            pq := Function.update (resolveSim spkKey sC.base).pq Q pq',
            pn := (resolveSim spkKey sC.base).pn,
            unackA := (resolveSim spkKey sC.base).unackA && Q != Party.A,
            honest := (resolveSim spkKey sC.base).honest,
            chains := Function.update (resolveSim spkKey sC.base).chains Q
              (pushChain ((resolveSim spkKey sC.base).chains Q) (g_init.accept (h.counter.toNat + 1))),
            amb := (resolveSim spkKey sC.base).amb,
            stopped := (resolveSim spkKey sC.base).stopped } =
          resolveSim spkKey s'_new := by
        symm
        exact resolveSim_pushChain_of_key_some spkKey sC.base Q (g_init.accept i) h.senderRatchetKey
          (accept_key g_init i) mir' (Function.update sC.base.pq Q pq') (sC.base.unackA && Q != Party.A) sC.base.amb
      rw [hres_push] at hrec_rc
      rw [hrec_rc]
      dsimp only [fR, ans]
      rw [← hm_eq', hpos_R, hmeta.hchall_R]
    have hstepSim_all : ∀ k,
        ((inReceiveOnlyEpoch sC.base.mir Q || spkAmb) && k == some sC.base.amb) = false →
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
      intro k hk
      rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) ec (huse_all k) (hstops_of_not_amb k hk)]
      dsimp only
      rw [hstepC_eq]
      simp only [hspk, Bool.false_eq_true, ↓reduceIte, hupd_ec, bind_assoc, pure_bind]
      rfl
    exact closeByStateC_inr_same_amb_badCoin P ℓ Dh encPt encT decT idOf lam qep q δ d₁
      (remWin qep mir') post (.inl (.inl (.inr (Q, w)))) cont s_R sC s_fig8 false ec winBefore
      (deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T) hbad_le hslack_le fR fS
      (fun _ => rfl) hD0 hstepR_eq
      (hstepSim_all none (by simp [hinw_Q, hspk]))
      (fun idx _ => hstepSim_all (some idx) (by simp [hinw_Q, hspk]))
      (fun _ => rfl)
      (fun _ _ => le_rfl)
      (fun rc hbad_f => ih ans (fR rc).2 sC'_new s_fig8' false (Function.update ec Q rc) winBefore
        (Function.update epExp (sC.base.mir.epoch Q + 2) rc)
        (hinvCX_of sC.base.amb winBefore rc (by have := hinv.hsim.hamb; omega) (by omega)
          hinv.hsim.hwinBefore hbad_f))
  | true =>
    have hstop0 := hstop_amb hspk
    set s'_new : SimState PQ Pt ℓ :=
      { sC.base with
        mir := mir',
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)),
        amb := sC.base.amb + 1 }
    set sC'_new : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s'_new, kept := kept' }
    set fR := fun rc : BitVec 256 =>
      let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
      (ans, s_R.accept Q
        (withEager (toGhost P (resolveSim spkKey s'_new) Q st') p₂.1
          (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) r_mir.pos)
    set fS := fun rc : BitVec 256 =>
      (ans, ((sC'_new, s_fig8', false), Function.update ec Q rc))
    have hstepR_eq :
        stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fR rc)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      have hnew_rc := (hnew rc).2 hrej_false
      rw [hfig'_raw] at hnew_rc
      rcases hnew_rc with ⟨_, _, _, _, m_raw', hm_eq', hrec_rc, _⟩
      rw [hpn_eq] at hrec_rc
      rw [hst_R_Q]
      have hres_push :
          toGhost P
            { mir := sC.base.mir.accept Q () r_mir.pos,
              pq := Function.update (resolveSim spkKey sC.base).pq Q pq',
              pn := (resolveSim spkKey sC.base).pn,
              unackA := (resolveSim spkKey sC.base).unackA && Q != Party.A,
              honest := (resolveSim spkKey sC.base).honest,
              chains := Function.update (resolveSim spkKey sC.base).chains Q
                (pushChain ((resolveSim spkKey sC.base).chains Q) (g_init.accept (h.counter.toNat + 1))),
              amb := (resolveSim spkKey sC.base).amb,
              stopped := (resolveSim spkKey sC.base).stopped } Q st' =
          toGhost P (resolveSim spkKey s'_new) Q st' := by
        have h1 :
            { mir := sC.base.mir.accept Q () r_mir.pos,
              pq := Function.update (resolveSim spkKey sC.base).pq Q pq',
              pn := (resolveSim spkKey sC.base).pn,
              unackA := (resolveSim spkKey sC.base).unackA && Q != Party.A,
              honest := (resolveSim spkKey sC.base).honest,
              chains := Function.update (resolveSim spkKey sC.base).chains Q
                (pushChain ((resolveSim spkKey sC.base).chains Q) (g_init.accept (h.counter.toNat + 1))),
              amb := (resolveSim spkKey sC.base).amb + 1,
              stopped := (resolveSim spkKey sC.base).stopped } =
            resolveSim spkKey s'_new := by
          symm
          exact resolveSim_pushChain_of_key_some spkKey sC.base Q (g_init.accept i) h.senderRatchetKey
            (accept_key g_init i) mir' (Function.update sC.base.pq Q pq') (sC.base.unackA && Q != Party.A) (sC.base.amb + 1)
        rw [← h1]
        rfl
      rw [hres_push] at hrec_rc
      rw [hrec_rc]
      dsimp only [fR, ans]
      rw [← hm_eq', hpos_R, hmeta.hchall_R]
    have hstepSim_none :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
          (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
      have hk_none : ((inReceiveOnlyEpoch sC.base.mir Q || spkAmb) && (none : Option ℕ) == some sC.base.amb) = false := by
        simp
      rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec (huse_all none) (hstops_of_not_amb none hk_none)]
      dsimp only
      rw [hstepC_eq]
      simp only [hspk, ↓reduceIte, hupd_ec, bind_assoc, pure_bind]
      rfl
    exact closeByStateC_inr_deliver_amb_badCoin (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) P ℓ Dh encPt encT decT idOf lam qep q δ d₁
      (remWin qep mir') post Q w cont s_R sC s_fig8 ec winBefore hamb_lt hinv.hsim.hwinBefore
      (deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T) hbad_le hslack_le fR fS
      (fun _ => rfl) hD0 hstepR_eq hstop0 hstepSim_none
      (fun _ => rfl)
      (fun _ _ => le_rfl)
      (fun winBefore' hwb' rc hbad_f => ih ans (fR rc).2 sC'_new s_fig8' false
        (Function.update ec Q rc) winBefore' (Function.update epExp (sC.base.mir.epoch Q + 2) rc)
        (hinvCX_of (sC.base.amb + 1) winBefore' rc (by omega) (by omega) hwb' hbad_f))

end CryptoGames.LibsignalSM.Proofs.Refinement

