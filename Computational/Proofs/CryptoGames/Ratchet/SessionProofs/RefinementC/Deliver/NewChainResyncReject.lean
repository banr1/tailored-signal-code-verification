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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep

/-!
# Deliver step of the C coupling: new epoch, resync reject

Proves `closeByStateC_deliver_newChain_resync_reject`, the rejecting case of a new-epoch case-3a
resync delivery where Fig. 8 rejects the salt-steered record.
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

private theorem dncrr_deliverPure_of_receive_none {Key : Type}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (Q : Party)
    (c : Fig8C Pt) (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hrcv : sm.receive (s.st Q) c = none) :
    ∃ a, (a = none ∨ a = some .rejected) ∧ deliverPure sm SM.Config.h1 Q c s = (a, s) := by
  unfold deliverPure
  by_cases hw : s.win = true
  · exact ⟨none, Or.inl rfl, by simp [hw]⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit Q.other c with
    | none => exact ⟨none, Or.inl rfl, rfl⟩
    | some r =>
      refine ⟨some .rejected, Or.inr rfl, ?_⟩
      simp [hrcv, SM.Config.h1]

private theorem dncrr_onAnswerPure_stopped {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped := by
  unfold onAnswerPure onAcceptPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      dsimp only
      split
      · cases s.mir.inTransit Q.other w <;> rfl
      · split <;> [rfl; (split <;> rfl)]

/-- Closes the `deliver` step for a new epoch under case-3a resync when Fig. 8 rejects `c'`, leaving
Fig. 8's state unchanged (`DEV-SM4`) and coupling rejection on both sides. -/
theorem closeByStateC_deliver_newChain_resync_reject {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    {ev : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) =
      some ev)
    (hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = none)
    (hfig : ∀ x, ev = some x →
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c = none)
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
  have hsim := hinv.hsim
  have hmeta := hsim.hmeta
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨_, hsrk, hctr, _⟩
  rcases hhon_c with ⟨_, _, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by
    rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let i := h.counter.toNat + 1
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hM := libX25519Rel_model hX
  have hT_ne0 : T ≠ 0 := hM.dh_ne_zero (epExp t) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hT_dec : decT h.senderRatchetKey = some T := by
    rw [hsrk', hdec]
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec]; simp [beq_eq_false_iff_ne, hT_ne0]
  have hzero_T : (some T == some (0 : Pt)) = false := by
    simp [beq_eq_false_iff_ne, hT_ne0]
  have hc'_eq :
      (((sC.base.mir.epoch Q + 1, some T),
        (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) : Fig8C Pt) = c' := by
    rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
    dsimp only [c', T, t] at hepoch hT_c hctr hraw_c ⊢
    rw [← hepoch, ← hT_c, hctr, ← hraw_c]
  have hc_ne_c' : decide (c ≠ c') = true :=
    decide_eq_true (fun heq => hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) heq))
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false :=
    decide_eq_false (not_not.mpr hepoch)
  have hjump_f : decide (25000 < h.counter.toNat + 1 - 1) = false := decide_eq_false hjump
  have hi32_f : decide (2 ^ 32 ≤ h.counter.toNat + 1) = false :=
    decide_eq_false (by dsimp only at hi32; omega)
  let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
  have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
    dsimp only [s₁]
    generalize hs : sC.base = sb
    have hst : sb.stopped = false := hs ▸ hmeta.hstop
    cases sb; dsimp only at hst; subst hst; rfl
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
    if spkAmb then { sC with base := s₁ } else sC
  have heval₀ :
      predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000)
        P sC Q w c c' = some ev := heval
  have heval₁ :
      predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000)
        P { base := s₁, kept := sC.kept, sent := sC.sent, snaps := sC.snaps } Q w c c' =
        some ev := heval
  have hstepC_eq :
      simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (some .rejected, (sC₁, s_fig8, false)) := by
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
      hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
      show (some false == some true) = false from rfl,
      hzero_f, hinw_Q, Bool.false_or, hjump_f, hi32_f, hT_dec, hzero_T,
      show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl]
    cases hspk : spkAmb <;>
      simp only [↓reduceIte, Bool.false_eq_true, sC₁, hspk, hs₁_stop] <;>
      { unfold fwdCPure
        simp only [hsalt, ↓reduceIte, hc'_eq, hc_ne_c',
          show s₁.mir = sC.base.mir from rfl, hsafe, Bool.not_false, Bool.and_self,
          Bool.true_and, Bool.false_or, heval₀, heval₁]
        rcases ev with _ | x
        · rfl
        · rcases dncrr_deliverPure_of_receive_none sm Q c s_fig8 (hfig x rfl) with ⟨a, ha, hz⟩
          rw [hz]
          rcases ha with rfl | rfl <;> rfl }
  have hstops_none :
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8) = false := by
    refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8) ?_
    unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
      hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
      show (some false == some true) = false from rfl,
      hzero_f, hinw_Q, Bool.false_or,
      show ((none : Option ℕ) == some sC.base.amb) = false from rfl,
      Bool.and_false, hjump_f, hi32_f, hT_dec, hzero_T,
      show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
      dncrr_onAnswerPure_stopped]
    cases spkAmb <;> simp only [↓reduceIte, Bool.false_eq_true, hmeta.hstop]
  have hstep_none :
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
        pure (some .rejected, ((sC₁, s_fig8, false), ec)) :=
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) ec hsim.hec (huse_all none) hstops_none _ hstepC_eq
      (by dsimp only [sC₁, s₁]; cases spkAmb <;> rfl)
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, _⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]; exact hQ_recv
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
      rw [hsim.hepExp0]
      exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  have hfind_res :
      ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hdummy_res :
      ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res :
      ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]
      exact List.mem_map_of_mem hg'
    rw [List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]
    omega
  let pos : SM.Pos := ⟨Q.other, (s_fig8.st Q).tcur + 1, i⟩
  let mir' := sC.base.mir.accept Q () pos
  have hmir'_ep_tcur : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [mir', pos, SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  have hc'_tcur : (((s_fig8.st Q).tcur + 1, some T), i, (ser, tag), effectiveHkdfSalt32 salt) = c' := by
    rw [hsim.htcur Q]; exact hc'_eq
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0 hsrk'.symm
    mir' hmir'_ep_tcur
  dsimp only at hnew
  rw [hc'_tcur, hsim.htcur Q] at hnew
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hrej_false : g_init.rejects i = false := by
    rw [g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i, hctr]; dsimp only at hi32; omega)]
    exact hjump_f
  have hfig'_c' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none :=
    hfig'
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := by
    intro rc
    rw [hst_R_Q]
    have h2 := (hnew rc).2 hrej_false
    rw [hfig'_c'] at h2
    exact h2
  cases hspk : spkAmb with
  | false =>
    have hR_map := hmeta.inTransit_R_map Q.other w
    rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      rw [hrcv rc]
    have hstops_all : ∀ k,
        simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
      intro k
      refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
      unfold simRecvStep
      simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
        hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
        show (some false == some true) = false from rfl,
        hzero_f, hinw_Q,
        show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
        hspk, Bool.or_self, hjump_f, hi32_f, hT_dec, hzero_T, dncrr_onAnswerPure_stopped]
    have hresC_f :
        simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (some .rejected, (sC, s_fig8, false)) := by
      rw [hstepC_eq]
      simp [sC₁, hspk]
    have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) ec hsim.hec (huse_all k) (hstops_all k) _ hresC_f rfl
    exact closeByStateC_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore
      (some .rejected)
      (stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R)
      hstepR (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
      (ih (some .rejected) s_R sC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
  | true =>
    have hdiv : ((some sC.base.amb : Option ℕ) == some sC.base.amb) = true := beq_self_eq_true _
    have hstop0 :
        (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
          (sC.base, s_fig8) ec).2.1.stopped = true := by
      unfold simRecvStepEager
      rw [huse_all (some sC.base.amb)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold simRecvStep
      simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
        hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
        show (some false == some true) = false from rfl,
        hzero_f, hinw_Q, Bool.false_or,
        show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
        hspk, hdiv, Bool.and_self, huse_all (some sC.base.amb)]
    have hnone_t :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
          pure (some .rejected,
            (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) := by
      rw [hstep_none]
      simp [sC₁, s₁, hspk]
    exact closeByStateC_deliver_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post
      x₀ Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hrcv hstop0 hnone_t
      (ih (some .rejected))

end CryptoGames.LibsignalSM.Proofs.Refinement
