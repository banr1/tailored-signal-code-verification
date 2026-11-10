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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Reject

/-!
# Evicted salt mismatch on inject: counter out of range

Proves `closeByStateC_inject_evictedMismatch_reject`, handling an injected wire with an evicted salt mismatch outside the receive-only window when the counter exceeds `MAX_FORWARD_JUMPS`.
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

/-- On an injected wire with an evicted salt mismatch outside `inReceiveOnlyEpoch` and counter out of range, both `libsignalToModularSchemeSim` and libsignal reject. -/
theorem closeByStateC_inject_evictedMismatch_reject {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true)
    (c : Fig8C Pt)
    (hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) =
      some (w, c))
    (hmis : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1))
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  set spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  have hsim := hinv.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  have hmem_hon : (w, c) ∈ sC.base.honest := List.mem_of_find?_eq_some hfind_hon
  rcases hsim.hhon (w, c) hmem_hon with ⟨hhon_c, hc_le_M, _, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨_, hsrk, _, _⟩
  have ht1 : 1 ≤ c.1.1 := hhon_c.2.2.1
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
      rw [hsim.hepExp0]
      exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  let T := Dh.dh (epExp c.1.1) Dh.base
  have hT_dec : decT h.senderRatchetKey = some T := by
    dsimp only [T]; rw [hsrk, hdec]
  have hT_ne0 : T ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec]; simp [beq_eq_false_iff_ne, hT_ne0]
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q, expectedGhost_of_inWin_false P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q) hinw]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw with ⟨hγ_Q, _, v_prev, hvS_Q, _⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]
    exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
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
  set t := (s_fig8.st Q).tcur + 1
  set pos : SM.Pos := ⟨Q.other, t, i⟩
  set mir' := sC.base.mir.accept Q () pos
  have hmir'_ep_tcur : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hsim.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hnew := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
      (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
      pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0 hsrk.symm
      mir' hmir'_ep_tcur rc
  have hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1 := by
    simp only [hfind_hon, Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hevict
    exact hevict
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hjump : (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact hbound
  have hrej_init : g_init.rejects i = true := by
    unfold GhostChain.rejects
    dsimp only [g_init]
    have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
    simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
    exact hjump
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := by
    intro rc
    rw [hst_R_Q]
    exact (hnew rc).1 hrej_init
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hepoch]
  have hres_sim : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)) := by
    intro k
    unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hepoch]
  have hstops_all : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8) = false :=
    fun k => simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8)
      (by rw [hres_sim k]; exact hmeta.hstop)
  cases hspk : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) with
  | false =>
    refine closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
      Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv huse_all hres_sim ?_ ih
    unfold simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan,
      hfind, hfind_hon, Option.map_some, decide_eq_true hepoch, decide_eq_false hmis, Option.some_beq_some,
      beq_false, Bool.and_false, hzero_f, hinw, hspk, Bool.false_or, hjump]
    rfl
  | true =>
    let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
    have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
      dsimp only [s₁]
      generalize hs : sC.base = sb
      have hst : sb.stopped = false := hs ▸ hmeta.hstop
      cases sb
      dsimp only at hst
      subst hst
      rfl
    have hresC_amb : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := s₁ }, s_fig8, false)) := by
      unfold simRecvStepCGen
      simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan,
        hfind, hfind_hon, Option.map_some, decide_eq_true hepoch, decide_eq_false hmis, Option.some_beq_some,
        beq_false, Bool.and_false, hzero_f, hinw, hspk, Bool.false_or, hjump, hs₁_stop]
      rfl
    have hstep_k : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
        (sC, s_fig8, false) ec =
        pure (some .rejected, (({ sC with base := s₁ }, s_fig8, false), ec)) := fun k =>
      stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) ec hsim.hec (huse_all k) (hstops_all k) _ hresC_amb rfl
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inr (Q, w))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_inject_eq]
      simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext rc
      have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
        unfold libsignalSessionScheme; dsimp only; rw [hrcv rc]; rfl
      unfold injectRPure
      simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R]
    have hD0 := stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam
      (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
      (Or.inr fun rc _ _ _ _ h => by unfold libsignalSessionScheme at h; dsimp only at h; rw [hrcv rc] at h; cases h)
    have hinv' := simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀
      s_R sC s_fig8 ec winBefore epExp hinv rfl
    exact closeByStateC_inr_amb_noStop P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inr (Q, w))) cont s_R sC { sC with base := s₁ } s_fig8 s_fig8 false false ec ec winBefore
      (some .rejected) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun _ => s_R)
      hD0 hstepR (hstep_k none) (hstep_k (some sC.base.amb)) rfl hmeta.hstop le_rfl
      (fun _ => ih (some .rejected) s_R { sC with base := s₁ } s_fig8 false ec _ epExp hinv')

end CryptoGames.LibsignalSM.Proofs.Refinement
