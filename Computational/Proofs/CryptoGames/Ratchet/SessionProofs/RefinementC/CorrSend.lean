/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepCorrSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager

/-!
# Refinement under decision C: transmit, challenge, and corruption steps

Proves `CloseByStateC` step preservation for `transmit`, `chall`, and `corr` queries under the
decision-C invariant `SimInvCX` (`closeByStateC_transmit_step`, `closeByStateC_chall_step`,
`closeByStateC_corr_step`).
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

abbrev c7_expectedGhost_congr := @expectedGhost_congr
abbrev c8_expectedGhost_congr := @expectedGhost_congr
abbrev c7_sendsIn_of_inWin_false := @sendsIn_of_inWin_false
abbrev c7_sendsIn_succ_of_inWin_true := @sendsIn_succ_of_inWin_true
abbrev c7_sendsIn_other_false_of_sendsIn := @sendsIn_other_false_of_sendsIn
abbrev c8_map_epoch_resolve_list := @map_epoch_resolve_list
abbrev c7_epMgmt_of_sendsIn_succ_false := @epMgmt_of_sendsIn_succ_false
abbrev c7_epMgmt_of_sendsIn_succ_true := @epMgmt_of_sendsIn_succ_true
abbrev c7_lFig8_send_step_not_inWinC := @lFig8_send_step_not_inWinC
abbrev c7_lFig8_send_step_inWinC := @lFig8_send_step_inWinC

private theorem c7_simInvCX_mono_r {P : Params PQ PQC} {Inv : ℕ → PQ → Prop}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hr : r' ≤ r) :
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R sC s_fig8 ec winBefore epExp := by
  refine ⟨?_, h.huniq, h.hkept, h.hidx, h.hsync⟩
  have hsim := h.hsim
  exact
    { hsim with
      hamb := by have := hsim.hamb; omega
      hamb_strict := fun hpos => by have := hsim.hamb_strict hpos; omega
      hidx_le := fun Q => by have := hsim.hidx_le Q; omega
      hhon_len := by have := hsim.hhon_len; omega
      hhon := hsim.hhon
      hpqInv := fun Q => InvB.mono hr (hsim.hpqInv Q) }

private theorem c7_closeByStateC_inr_same_amb_bind_const_R {α γ : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun _ => pure (ans, s_R'))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (sC, s_fig8, fl) ec =
        pure (ans, ((sC', s_fig8', fl'), ec')))
    (hamb : sC'.base.amb = sC.base.amb)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont ans) s_R' sC' s_fig8' fl' ec' winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) hcont)
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runSimCEager_inr_bind, hstepSim, pure_bind]
  · intro idx _
    have h := evalDist_runWinAtC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) ec (pure ()) (fun _ => (ans, ((sC', s_fig8', fl'), ec')))
      (fun _ => hamb) (fun j hj => by rw [hstepWin j hj, pure_bind]) winBefore idx
    simpa only [pure_bind] using h
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runHidC, runSimCEager_inr_bind, hstepSim, pure_bind]

private theorem c7_closeByStateC_inr_same_amb_bind_const_sim {α γ β : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ) (M : ProbComp β)
    (fR : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun x => pure (fR x))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      N >>= fun x => M >>= fun _ => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (sC, s_fig8, fl) ec =
        N >>= fun x => M >>= fun _ => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.base.amb = sC.base.amb)
    (hrem : ∀ x, remWin qep (fS x).2.1.1.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ x, CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2.1 (fS x).2.1.2.2 (fS x).2.2 winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun x => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x)) (hcont x)))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const _ _
  · intro idx _
    unfold runWinAtC
    cases idx with
    | zero =>
      rw [runSimCEager_inr_bind, hstepSim]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr N _ _ fun x => ?_
      exact OracleComp.evalDist_bind_const _ _
    | succ j =>
      dsimp only
      simp only [hamb]
      split
      · exact (OracleComp.evalDist_bind_const _ _).symm
      · rename_i hnot
        rw [runSimCEager_inr_bind, hstepWin j hnot]
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_congr N _ _ fun x => ?_
        exact OracleComp.evalDist_bind_const _ _
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runHidC, runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const _ _


set_option maxHeartbeats 800000 in
theorem c7_simSendStep_preserves_simInvC
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : PQC)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true)
    (hep_mir : s.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true) :
    let fR := chal.elim
      (transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m₀ rq bad s_R)
      (fun m₁ => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep SM.Config.h1 Q m₀ m₁ rq bad s_R)
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq (ec Q) (s, s_fig8)
    let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
    fR.1 = res.1 ∧
    res.2.1.amb = s.amb ∧
    remWin qep res.2.1.mir ≤ remWin qep s.mir ∧
    (inReceiveOnlyEpoch s.mir Q = true → updateAllEagerCoins s.mir res.2.1.mir (· == Q) ec = pure ec') ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      updateAllEagerCoins s.mir res.2.1.mir (fun _ => false) ec = pure ec' ∧
      ∀ (c_cka : BitVec 256), simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, s_fig8) = res) ∧
    SimInvC P (InvB Inv q (r - 1)) ℓ Dh encPt encT qep q (r - 1) x₀ fR.2 res.2.1 res.2.2 ec' winBefore epExp ∧
    (PosUniq s → HonestIdxLe s → PosUniq res.2.1 ∧ HonestIdxLe res.2.1) ∧
    (∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ), sC.base = s →
      KeptInv P Dh encPt encT idOf lam sC s_fig8 →
      EpochSync P Dh encPt encT idOf sC.base.honest sC.sent sC.snaps s_fig8 epExp →
      let sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
      KeptInv P Dh encPt encT idOf lam sC' res.2.2 ∧
      EpochSync P Dh encPt encT idOf sC'.base.honest sC'.sent sC'.snaps res.2.2 epExp) := by
  intro fR res ec'
  rcases simSendStep_preserves_simInvC_core P (InvB Inv q r) (InvB Inv q (r - 1)) ℓ Dh encPt encT decT idOf
      hX hrt hid lam qep q r hq32 hr Q m₀ chal bad s₁ rq x₀ s_R s s_fig8 ec winBefore epExp hinv
      (spqrCLocal_total hS hr (s.pq Q) rq (hinv.hpqInv Q))
      (spqrCLocal_noSendPanic hS hr (s.pq Q) rq (hinv.hpqInv Q))
      (fun pq' _ _ hspqr R => by
        by_cases hRQ : R = Q
        · subst hRQ; rw [Function.update_self]; exact InvB.send hS hr (hinv.hpqInv R) hspqr
        · rw [Function.update_of_ne hRQ]; exact InvB.mono (Nat.sub_le r 1) (hinv.hpqInv R))
      hnoBob_mir hep_mir hsafeCh with
    ⟨h1, h2, h3, h4, h5, hsimC, huniq, _, pub, m_enc, w, hres1, hhon_eq, hst_f', hpub_pq, hpub_addr⟩
  refine ⟨h1, h2, h3, h4, h5, hsimC, huniq, ?_⟩
  intro sC hsC hkept hsync
  rw [hres1]
  set sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 (some w)
  have hhonEp : ∀ wc ∈ s.honest, wc.2.1.1 ≤ (s_fig8.st (Party.senderOf wc.2.1.1)).tcur := by
    intro wc hwc
    rw [hinv.htcur]
    exact (hinv.hhon wc hwc).2.2.2
  refine ⟨keptInv_send hkept Q (hinv.hst_id Q) (pub, m_enc) (ec Q) hst_f' rfl, ?_⟩
  have hrc : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true →
      epExp ((s_fig8.st Q).tcur + 1) = ec Q := by
    intro hsends_next
    rw [hinv.hst_id Q, hinv.htcur Q] at hsends_next
    rw [hinv.htcur Q]
    have hinw : inReceiveOnlyEpoch s.mir Q = true := by
      unfold inReceiveOnlyEpoch
      cases hs : Q.sendsIn (s.mir.epoch Q)
      · rfl
      · rw [sendsIn_succ_of_sendsIn Q (s.mir.epoch Q) hs] at hsends_next
        cases hsends_next
    rcases hinv.hspur Q with ⟨_, _, hinw_t, _, _⟩
    exact (hinw_t hinw).2.2.2
  rw [hsC] at hsync
  refine epochSync_send P Dh hDh encPt encT idOf lam hD hrt s.honest res.2.1.honest
    sC.sent sC'.sent s_fig8 res.2.2 hsync hkept.hvR hinv.hst_id hhonEp Q (pub, m_enc) (ec Q)
    hrc hst_f' (fun _ => hinv.hmeta.hwin_fig8) ?_ ?_ hpub_pq hpub_addr
  · intro wc hwc
    rw [hhon_eq] at hwc
    rcases List.mem_cons.mp hwc with rfl | hwc
    · exact Or.inr rfl
    · exact Or.inl hwc
  · intro e he
    dsimp only [sC', cxSend] at he
    rw [hhon_eq, List.head?_cons] at he
    cases hkf : (sC.kept Q).full with
    | none =>
      rw [hkf] at he
      exact Or.inl he
    | some st₀ =>
      rw [hkf] at he
      dsimp only at he
      have hst₀ : st₀ = s_fig8.st Q := hkept.hfull Q st₀ hkf
      subst hst₀
      by_cases hsends_next : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true
      · rw [hsends_next, ite_eq_left rfl] at he
        exact Or.inl he
      · have hsends_next_f : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false :=
          Bool.eq_false_iff.mpr hsends_next
        rw [hsends_next_f, ite_eq_right Bool.false_ne_true] at he
        cases hvS : (s_fig8.st Q).vS with
        | none =>
          rw [hvS] at he
          exact Or.inl he
        | some v =>
          rw [hvS] at he
          rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr ⟨hsends_next_f, rfl, rfl⟩
          · exact Or.inl he

theorem c7_cxSend_base (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

/-- One-step `CloseByStateC` reduction for `transmit` queries. -/
theorem closeByStateC_transmit_step {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (Q : Party) (m : Plain ℓ) (rc : Option PQC)
    (cont : Option (List (BitVec 8)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inl (Q, m, rc))))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  set s := sC.base
  set q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain :=
    .inl (.inl (.inl (.inl (Q, m, rc))))
  have hD0 := stepR_D0_eq_of_simInvC P (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀ q_sm
    s_R s s_fig8 ec winBefore epExp hinv.hsim (by intro _ h; dsimp [q_sm] at h; nomatch h)
  have hwin_R := hinv.hsim.hmeta.hwin_R
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  have hwin_fig8 := hinv.hsim.hmeta.hwin_fig8
  have hstop := hinv.hsim.hmeta.hstop
  have hnoBob_R := hinv.hsim.hmeta.noBobEpoch0_R Q
  have hW0 := spqrCLocal_total hS hr
  by_cases hguard : (!(SM.noBobSendInEpoch0 s.mir Q)) = true
  · have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        q_sm s_R = pure (none, s_R) := by
      rw [stepR_transmit_eq]
      change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = pure (none, s_R)
      rw [hnoBob_R, hwin_R, hguard, Bool.true_or, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
        pure (none, ((sC, s_fig8, false), ec)) := by
      intro k
      change stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (sC, s_fig8, false) ec = _
      unfold stepSimCEagerTransmit
      have hsimE : stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec =
          pure (none, ((s, s_fig8), ec)) := by
        unfold stepSimEagerTransmit
        dsimp only
        rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, Bool.not_true, Bool.and_false,
            ite_eq_right Bool.false_ne_true,
            stepSim_transmit_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8)
              hwin_fig8 hinv.hsim.hpqInv hW0]
        dsimp only
        rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, ite_eq_left rfl,
            pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
      change (stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec >>= _) = _
      rw [hsimE, pure_bind]
      rfl
    exact closeByStateC_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      q_sm cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R sC s_fig8 false ec winBefore epExp (c7_simInvCX_mono_r hinv (Nat.sub_le r 1)))
  · have hguard_f : (!(SM.noBobSendInEpoch0 s.mir Q)) = false := Bool.eq_false_iff.mpr hguard
    have hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true := by
      revert hguard_f; cases SM.noBobSendInEpoch0 s.mir Q <;> simp
    cases hep_mir : s.mir.epMgmt 3 qep Q rc.isSome with
    | none =>
      have hep_R : s_R.epMgmt 3 qep Q rc.isSome = none :=
        hinv.hsim.hmeta.epMgmt_none Q qep rc.isSome hep_mir
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          q_sm s_R = samCoin rc >>= fun _ => pure (none, s_R) := by
        rw [stepR_transmit_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
            samIfNec_bind_eq]
        congr 1; funext rq
        unfold transmitPure
        rw [hep_R]
      have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
          pure (none, ((sC, s_fig8, false), ec)) := by
        intro k
        change stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (sC, s_fig8, false) ec = _
        unfold stepSimCEagerTransmit
        have hsimE : stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec =
            pure (none, ((s, s_fig8), ec)) := by
          unfold stepSimEagerTransmit
          dsimp only
          have hsim : stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) = pure (none, (s, s_fig8)) := by
            rw [stepSim_transmit_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8)
              hwin_fig8 hinv.hsim.hpqInv hW0]
            dsimp only
            rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
          split
          · rw [hep_mir]
            change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
            rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
          · change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
            rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
        change (stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec >>= _) = _
        rw [hsimE, pure_bind]
        rfl
      exact c7_closeByStateC_inr_same_amb_bind_const_R P ℓ Dh encPt encT decT idOf lam qep q δ post
        q_sm cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore (samCoin rc) none
        hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
        (ih none s_R sC s_fig8 false ec winBefore epExp (c7_simInvCX_mono_r hinv (Nat.sub_le r 1)))
    | some s₁ =>
      let fR := fun rq => transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m rq rc.isSome s_R
      let res := fun rq => simSendStep P ℓ Dh encPt encT idOf lam qep Q m none rc.isSome s₁ rq (ec Q) (s, s_fig8)
      let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
      let sC' := fun rq => cxSend P Dh encPt encT idOf lam Q sC (res rq).2.1 (res rq).1
      let fS := fun rq => ((res rq).1, ((sC' rq, (res rq).2.2, false), ec'))
      have hpres := fun rq => c7_simSendStep_preserves_simInvC P Inv ℓ Dh hDh encPt encT decT idOf
        hX hD hrt hid lam qep q r hS hq32 hr Q m none rc.isSome s₁ rq x₀ s_R s s_fig8 ec winBefore epExp
        hinv.hsim hnoBob_mir hep_mir (fun h => by cases h)
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          q_sm s_R = samCoin rc >>= fun rq => pure (fR rq) := by
        rw [stepR_transmit_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
            samIfNec_bind_eq]
      have hinvCX' : ∀ rq, SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
          (fR rq).2 (sC' rq) (res rq).2.2 ec' winBefore epExp := by
        intro rq
        have hbase : (sC' rq).base = (res rq).2.1 :=
          c7_cxSend_base P Dh encPt encT idOf lam Q sC (res rq).2.1 (res rq).1
        rcases (hpres rq).2.2.2.2.2.2.1 hinv.huniq hinv.hidx with ⟨huniq', hidx'⟩
        rcases (hpres rq).2.2.2.2.2.2.2 sC rfl hinv.hkept hinv.hsync with ⟨hkept', hsync'⟩
        exact ⟨hbase ▸ (hpres rq).2.2.2.2.2.1, hbase ▸ huniq', hkept', hbase ▸ hidx', hsync'⟩
      cases hinw : inReceiveOnlyEpoch s.mir Q with
      | true =>
        have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
            samCoin rc >>= fun rq => pure (fS rq) := by
          intro k
          change stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (sC, s_fig8, false) ec = _
          unfold stepSimCEagerTransmit
          have hsimE : stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec =
              samCoin rc >>= fun rq => pure ((res rq).1, ((res rq).2, ec')) := by
            unfold stepSimEagerTransmit
            dsimp only
            rw [hwin_fig8, hinw, hstop, hwin_mir, hguard_f, Bool.not_false, Bool.true_and,
                Bool.false_or, Bool.false_or, Bool.not_false, Bool.and_true, ite_eq_left rfl, hep_mir]
            dsimp only
            change (samCoin rc >>= _) = _
            congr 1; funext rq
            rw [(hpres rq).2.2.2.1 hinw, pure_bind]
          change (stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec >>= _) = _
          rw [hsimE, bind_assoc]
          rfl
        exact closeByStateC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R sC s_fig8 false ec winBefore (samCoin rc) fR fS
          (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
          (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.1)
          (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.2.1)
          (fun rq => ih (fS rq).1 (fR rq).2 (sC' rq) (res rq).2.2 false ec' winBefore epExp (hinvCX' rq))
      | false =>
        have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
            samCoin rc >>= fun rq => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (fS rq) := by
          intro k
          change stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (sC, s_fig8, false) ec = _
          unfold stepSimCEagerTransmit
          have hsimE : stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec =
              samCoin rc >>= fun rq => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
                pure ((res rq).1, ((res rq).2, ec')) := by
            unfold stepSimEagerTransmit
            dsimp only
            rw [hinw, Bool.and_false, Bool.false_and, ite_eq_right Bool.false_ne_true,
                stepSim_transmit_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8)
                  hwin_fig8 hinv.hsim.hpqInv hW0]
            dsimp only
            rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
            dsimp only
            change ((samCoin rc >>= _) >>= _) = _
            simp only [bind_assoc, pure_bind]
            congr 1; funext rq
            congr 1; funext c_cka
            rcases (hpres rq).2.2.2.2.1 hinw with ⟨hupd, hcoins⟩
            rw [hcoins c_cka, hupd, pure_bind]
          change (stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec >>= _) = _
          rw [hsimE]
          simp only [bind_assoc, pure_bind]
          rfl
        exact c7_closeByStateC_inr_same_amb_bind_const_sim P ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R sC s_fig8 false ec winBefore (samCoin rc) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fR fS
          (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
          (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.1)
          (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.2.1)
          (fun rq => ih (fS rq).1 (fR rq).2 (sC' rq) (res rq).2.2 false ec' winBefore epExp (hinvCX' rq))

/-- One-step `CloseByStateC` reduction for `chall` queries. -/
theorem closeByStateC_chall_step {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (Q : Party) (m₀ m₁ : Plain ℓ) (rc : Option PQC)
    (cont : Option (List (BitVec 8)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  set s := sC.base
  set q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))
  have hD0 := stepR_D0_eq_of_simInvC P (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀ q_sm
    s_R s s_fig8 ec winBefore epExp hinv.hsim (by intro _ h; dsimp [q_sm] at h; nomatch h)
  have hwin_R := hinv.hsim.hmeta.hwin_R
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  have hwin_fig8 := hinv.hsim.hmeta.hwin_fig8
  have hstop := hinv.hsim.hmeta.hstop
  have hnoBob_R := hinv.hsim.hmeta.noBobEpoch0_R Q
  have hW0 := spqrCLocal_total hS hr
  by_cases hguard : (!(SM.noBobSendInEpoch0 s.mir Q)) = true
  · have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        q_sm s_R = pure (none, s_R) := by
      rw [stepR_chall_eq]
      change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = pure (none, s_R)
      rw [hnoBob_R, hwin_R, hguard, Bool.true_or, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
        pure (none, ((sC, s_fig8, false), ec)) := by
      intro k
      change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (sC, s_fig8, false) ec = _
      unfold stepSimCEagerChall
      have hsimE : stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec =
          pure (none, ((s, s_fig8), ec)) := by
        unfold stepSimEagerChall
        dsimp only
        rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, Bool.not_true, Bool.and_false,
            ite_eq_right Bool.false_ne_true,
            stepSim_chall_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8)
              hwin_fig8 hinv.hsim.hpqInv hW0]
        dsimp only
        rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, ite_eq_left rfl,
            pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
      change (stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec >>= _) = _
      rw [hsimE, pure_bind]
      rfl
    exact closeByStateC_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      q_sm cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R sC s_fig8 false ec winBefore epExp (c7_simInvCX_mono_r hinv (Nat.sub_le r 1)))
  · have hguard_f : (!(SM.noBobSendInEpoch0 s.mir Q)) = false := Bool.eq_false_iff.mpr hguard
    have hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true := by
      revert hguard_f; cases SM.noBobSendInEpoch0 s.mir Q <;> simp
    cases hep_mir : s.mir.epMgmt 3 qep Q rc.isSome with
    | none =>
      have hep_R : s_R.epMgmt 3 qep Q rc.isSome = none :=
        hinv.hsim.hmeta.epMgmt_none Q qep rc.isSome hep_mir
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          q_sm s_R = samCoin rc >>= fun _ => pure (none, s_R) := by
        rw [stepR_chall_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
            samIfNec_bind_eq]
        congr 1; funext rq
        unfold challPure
        rw [hep_R]
      have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
          pure (none, ((sC, s_fig8, false), ec)) := by
        intro k
        change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (sC, s_fig8, false) ec = _
        unfold stepSimCEagerChall
        have hsimE : stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec =
            pure (none, ((s, s_fig8), ec)) := by
          unfold stepSimEagerChall
          dsimp only
          have hsim : stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) = pure (none, (s, s_fig8)) := by
            rw [stepSim_chall_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8)
              hwin_fig8 hinv.hsim.hpqInv hW0]
            dsimp only
            rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
          split
          · rw [hep_mir]
            change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
            rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
          · change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
            rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
        change (stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec >>= _) = _
        rw [hsimE, pure_bind]
        rfl
      exact c7_closeByStateC_inr_same_amb_bind_const_R P ℓ Dh encPt encT decT idOf lam qep q δ post
        q_sm cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore (samCoin rc) none
        hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
        (ih none s_R sC s_fig8 false ec winBefore epExp (c7_simInvCX_mono_r hinv (Nat.sub_le r 1)))
    | some s₁ =>
      rcases hinv.hsim.hmeta.epMgmt_some Q qep rc.isSome hep_mir with
        ⟨s_R₁, s_fig8₁, hep_R, hep_fig8, hst_R₁, hst_fig8₁, hmeta₁⟩
      by_cases hsafe_neg : (!(s₁.safeCh 3 Q)) = true
      · have hsafe_R : s_R₁.safeCh 3 Q = s₁.safeCh 3 Q := hmeta₁.safeCh_R 3 Q
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            q_sm s_R = samCoin rc >>= fun _ => pure (none, s_R) := by
          rw [stepR_chall_eq]
          change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
          rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
              samIfNec_bind_eq]
          congr 1; funext rq
          unfold challPure
          rw [hep_R]
          dsimp only
          rw [hsafe_R, hsafe_neg, Bool.true_or, ite_eq_left rfl]
        have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
            pure (none, ((sC, s_fig8, false), ec)) := by
          intro k
          change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (sC, s_fig8, false) ec = _
          unfold stepSimCEagerChall
          have hsimE : stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec =
              pure (none, ((s, s_fig8), ec)) := by
            unfold stepSimEagerChall
            dsimp only
            have hsim : stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) = pure (none, (s, s_fig8)) := by
              rw [stepSim_chall_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8)
                hwin_fig8 hinv.hsim.hpqInv hW0]
              dsimp only
              rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true,
                  hep_mir]
              dsimp only
              rw [hsafe_neg, ite_eq_left rfl]
            split
            · rw [hep_mir]
              dsimp only
              rw [hsafe_neg, ite_eq_left rfl]
              change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
              rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
            · change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
              rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hsim.hec, pure_bind]
          change (stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec >>= _) = _
          rw [hsimE, pure_bind]
          rfl
        exact c7_closeByStateC_inr_same_amb_bind_const_R P ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore (samCoin rc) none
          hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
          (ih none s_R sC s_fig8 false ec winBefore epExp (c7_simInvCX_mono_r hinv (Nat.sub_le r 1)))
      · have hsafe_f : (!(s₁.safeCh 3 Q)) = false := Bool.eq_false_iff.mpr hsafe_neg
        have hsafeCh : s₁.safeCh 3 Q = true := by
          revert hsafe_f; cases s₁.safeCh 3 Q <;> simp
        let fR := fun rq => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep
          SM.Config.h1 Q m₀ m₁ rq rc.isSome s_R
        let res := fun rq => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) rc.isSome s₁ rq (ec Q) (s, s_fig8)
        let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
        let sC' := fun rq => cxSend P Dh encPt encT idOf lam Q sC (res rq).2.1 (res rq).1
        let fS := fun rq => ((res rq).1, ((sC' rq, (res rq).2.2, false), ec'))
        have hpres := fun rq => c7_simSendStep_preserves_simInvC P Inv ℓ Dh hDh encPt encT decT idOf
          hX hD hrt hid lam qep q r hS hq32 hr Q m₀ (some m₁) rc.isSome s₁ rq x₀ s_R s s_fig8 ec winBefore epExp
          hinv.hsim hnoBob_mir hep_mir (fun _ => hsafeCh)
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            q_sm s_R = samCoin rc >>= fun rq => pure (fR rq) := by
          rw [stepR_chall_eq]
          change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
          rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
              samIfNec_bind_eq]
          rfl
        have hinvCX' : ∀ rq, SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
            (fR rq).2 (sC' rq) (res rq).2.2 ec' winBefore epExp := by
          intro rq
          have hbase : (sC' rq).base = (res rq).2.1 :=
            c7_cxSend_base P Dh encPt encT idOf lam Q sC (res rq).2.1 (res rq).1
          rcases (hpres rq).2.2.2.2.2.2.1 hinv.huniq hinv.hidx with ⟨huniq', hidx'⟩
          rcases (hpres rq).2.2.2.2.2.2.2 sC rfl hinv.hkept hinv.hsync with ⟨hkept', hsync'⟩
          exact ⟨hbase ▸ (hpres rq).2.2.2.2.2.1, hbase ▸ huniq', hkept', hbase ▸ hidx', hsync'⟩
        cases hinw : inReceiveOnlyEpoch s.mir Q with
        | true =>
          have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
              samCoin rc >>= fun rq => pure (fS rq) := by
            intro k
            change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (sC, s_fig8, false) ec = _
            unfold stepSimCEagerChall
            have hsimE : stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec =
                samCoin rc >>= fun rq => pure ((res rq).1, ((res rq).2, ec')) := by
              unfold stepSimEagerChall
              dsimp only
              rw [hwin_fig8, hinw, hstop, hwin_mir, hguard_f, Bool.not_false, Bool.true_and,
                  Bool.false_or, Bool.false_or, Bool.not_false, Bool.and_true, ite_eq_left rfl, hep_mir]
              dsimp only
              rw [hsafe_f, ite_eq_right Bool.false_ne_true]
              change (samCoin rc >>= _) = _
              congr 1; funext rq
              rw [(hpres rq).2.2.2.1 hinw, pure_bind]
            change (stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec >>= _) = _
            rw [hsimE, bind_assoc]
            rfl
          exact closeByStateC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q δ post
            q_sm cont s_R sC s_fig8 false ec winBefore (samCoin rc) fR fS
            (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
            (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.1)
            (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.2.1)
            (fun rq => ih (fS rq).1 (fR rq).2 (sC' rq) (res rq).2.2 false ec' winBefore epExp (hinvCX' rq))
        | false =>
          have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (sC, s_fig8, false) ec =
              samCoin rc >>= fun rq => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (fS rq) := by
            intro k
            change stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (sC, s_fig8, false) ec = _
            unfold stepSimCEagerChall
            have hsimE : stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec =
                samCoin rc >>= fun rq => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
                  pure ((res rq).1, ((res rq).2, ec')) := by
              unfold stepSimEagerChall
              dsimp only
              rw [hinw, Bool.and_false, Bool.false_and, ite_eq_right Bool.false_ne_true,
                  stepSim_chall_eqW P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8)
                    hwin_fig8 hinv.hsim.hpqInv hW0]
              dsimp only
              rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
              dsimp only
              rw [hsafe_f, ite_eq_right Bool.false_ne_true]
              change ((samCoin rc >>= _) >>= _) = _
              simp only [bind_assoc, pure_bind]
              congr 1; funext rq
              congr 1; funext c_cka
              rcases (hpres rq).2.2.2.2.1 hinw with ⟨hupd, hcoins⟩
              rw [hcoins c_cka, hupd, pure_bind]
            change (stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec >>= _) = _
            rw [hsimE]
            simp only [bind_assoc, pure_bind]
            rfl
          exact c7_closeByStateC_inr_same_amb_bind_const_sim P ℓ Dh encPt encT decT idOf lam qep q δ post
            q_sm cont s_R sC s_fig8 false ec winBefore (samCoin rc) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fR fS
            (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
            (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.1)
            (fun rq => by rw [c7_cxSend_base]; exact (hpres rq).2.2.1)
            (fun rq => ih (fS rq).1 (fR rq).2 (sC' rq) (res rq).2.2 false ec' winBefore epExp (hinvCX' rq))

def c8_simCorrPureC (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Q : Party)
    (x : JointC PQ Pt ℓ) :
    Option (GhostState PQ) × JointC PQ Pt ℓ :=
  let sC := x.1
  let s := sC.base
  let s_fig8 := x.2.1
  let fl := x.2.2
  if s.stopped then (none, x)
  else if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then
    (none, x)
  else
    let z := corrPure Q s_fig8
    match z.1 with
    | none => (none, (sC, z.2, fl))
    | some figSt =>
      let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
          match figSt.γ with
          | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => s.chains
        else s.chains
      let g := LibsignalSim.toGhost (P := P) { s with chains } Q figSt
      (some g,
       ({ sC with base := { s with mir := s.mir.afterCorr Q, chains },
                  kept := Function.update sC.kept Q (Kept.ofSt figSt),
                  snaps := (Q, s.mir.epoch Q, g) :: sC.snaps }, z.2, fl))

private theorem c8_probeHook_lift_corrQuery_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift
      (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gh =
      pure ((corrPure Q gh.1).1, ((corrPure Q gh.1).2, gh.2)) := by
  change ((simulateQ (fig8ImplH1 fig qepF)
    (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gh.1 >>=
    fun p => pure (p.1, (p.2, gh.2))) = _
  have hq := simulateQ_corrQuery_run fig 3 qepF SM.Config.h1 Q pure gh.1
  rw [bind_pure] at hq
  change (simulateQ (fig8ImplH1 fig qepF) (SM.corrQuery Q)).run gh.1 =
    pure ((corrPure Q gh.1).1, (corrPure Q gh.1).2) at hq
  rw [hq, pure_bind]

theorem c8_stepSimCNone_corr_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x =
      pure (c8_simCorrPureC P Dh encT Q x) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  change (((guardC (simCorrC (P := P) (encT := encT) (H := probeHook fig (qep + 1)) Dh Q)).run
    x.1).run x.2) >>= (fun r => pure (r.1.1, (r.1.2, r.2))) =
    pure (c8_simCorrPureC P Dh encT Q x)
  unfold guardC simCorrC c8_simCorrPureC
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  by_cases hstop : x.1.base.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind]
    by_cases hcond : x.1.base.mir.win || !(x.1.base.mir.corrAllowed Q) || inReceiveOnlyEpoch x.1.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 x.1.base.mir Q)
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ite_false, LibsignalSimC.liftC,
        StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind]
      rw [c8_probeHook_lift_corrQuery_run]
      simp only [pure_bind]
      cases h : (corrPure Q x.2.1).1 with
      | none => simp [h]
      | some figSt =>
        cases hγ : figSt.γ <;>
          simp [h, hγ, hstop, StateT.run_bind, StateT.run_set, StateT.run_pure]

theorem c8_keptInv_corr (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ)
    (snaps' : List (Party × ℕ × GhostState PQ))
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hkept : KeptInv P Dh encPt encT idOf lam sC s_fig8)
    (hhon : s'.honest = sC.base.honest)
    (htrans : ∀ R w, s'.mir.inTransit R w = sC.base.mir.inTransit R w) :
    let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
      { sC with base := s',
                kept := Function.update sC.kept Q (Kept.ofSt (s_fig8.st Q)),
                snaps := snaps' }
    KeptInv P Dh encPt encT idOf lam sC' (s_fig8.afterCorr Q) := by
  intro sC'
  have hst_after : ∀ R, (s_fig8.afterCorr Q).st R = s_fig8.st R := fun _ => rfl
  refine ⟨fun R st hfull => ?_, fun R t v hfull hrs => ?_, fun R t => ?_⟩
  · rw [hst_after]
    by_cases hRQ : R = Q
    · subst hRQ
      simp only [sC', Function.update_self, Kept.ofSt, Option.some.injEq] at hfull
      exact hfull.symm
    · simp only [sC', Function.update_of_ne hRQ] at hfull
      exact hkept.hfull R st hfull
  · rw [hst_after]
    by_cases hRQ : R = Q
    · subst hRQ
      simp only [sC', Function.update_self, Kept.ofSt, reduceCtorEq] at hfull
    · simp only [sC', Function.update_of_ne hRQ] at hfull hrs
      exact hkept.hrs R t v hfull hrs
  · rw [hst_after]
    exact hkept.hvR R t

theorem c8_mem_of_lookup {α β : Type*} [BEq α] [LawfulBEq α] {k : α} {v : β} :
    ∀ {xs : List (α × β)}, xs.lookup k = some v → (k, v) ∈ xs
  | [], h => nomatch h
  | (k', v') :: xs, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i heq
      rw [beq_iff_eq] at heq
      rw [Option.some.injEq] at h
      subst heq h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (c8_mem_of_lookup h)

theorem c8_epListA_getLast (n : ℕ) : (epListA n).getLast? = some (2 * n) := by
  unfold epListA
  have hraw : rawEpListA n = (List.range n).map (2 * ·) ++ [2 * n] := by
    unfold rawEpListA
    rw [List.range_succ, List.map_append, List.map_singleton]
  rw [hraw, List.drop_append_of_le_length (by simp)]
  simp

theorem c8_epListB_getLast {n : ℕ} (hn : 1 ≤ n) :
    (epListB n).getLast? = some (2 * (n - 1) + 1) := by
  unfold epListB
  have hlen : n = (n - 1) + 1 := by omega
  have hraw : rawEpListB n = (List.range (n - 1)).map (2 * · + 1) ++ [2 * (n - 1) + 1] := by
    unfold rawEpListB
    conv_lhs => rw [hlen, List.range_succ, List.map_append, List.map_singleton]
  rw [hraw, List.drop_append_of_le_length (by simp; omega)]
  simp

/-- One-step `CloseByStateC` reduction for `corr` queries. -/
theorem closeByStateC_corr_step {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (Q : Party)
    (cont : Option (GhostState PQ) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inr Q))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  set s := sC.base
  have hD0 := stepR_D0_eq_of_simInvC P (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    (.inr Q) s_R s s_fig8 ec winBefore epExp hinv.hsim (by rintro ⟨_, _⟩ ⟨⟩)
  have hwin_R := hinv.hsim.hmeta.hwin_R
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  have hwin_fig8 := hinv.hsim.hmeta.hwin_fig8
  have hstop := hinv.hsim.hmeta.hstop
  have hcorr_R := hinv.hsim.hmeta.corrAllowed_R Q
  have hcorr_fig8 := hinv.hsim.hmeta.corrAllowed_fig8 Q
  have hinw_R := hinv.hsim.hmeta.inWindow_R Q
  have hnospk_R := hinv.hsim.hmeta.noSpkCorr_R Q
  by_cases hguard : (!(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = true
  · have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inr Q) s_R = pure (none, s_R) := by
      rw [stepR_corr_eq]
      change pure (if (s_R.win || !s_R.corrAllowed Q || (true && inWindow s_R Q) || !noAliceCorrWhileAliceBelowEpoch10 s_R Q) = true
        then (none, s_R) else (some (s_R.st Q), s_R.afterCorr Q)) = pure (none, s_R)
      rw [hwin_R, hcorr_R, hinw_R, hnospk_R, Bool.false_or, Bool.true_and, hguard, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (sC, s_fig8, false) ec =
        pure (none, ((sC, s_fig8, false), ec)) := by
      intro k
      change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q (sC, s_fig8, false) ec = _
      unfold stepSimCEagerCorr
      have hstepC : stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (sC, s_fig8, false) =
          stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, s_fig8, false) := rfl
      rw [hstepC, c8_stepSimCNone_corr_eq]
      unfold c8_simCorrPureC
      dsimp only [s] at *
      rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard, ite_eq_left rfl,
          pure_bind, updateAllEagerCoins_self_unused sC.base.mir ec hinv.hsim.hec, pure_bind]
    exact closeByStateC_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post (.inr Q) cont
      s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore none hD0 hstepR (hstepSim none)
      (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R sC s_fig8 false ec winBefore epExp (c7_simInvCX_mono_r hinv (Nat.sub_le r 1)))
  · have hguard_f : (!(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = false :=
      Bool.eq_false_iff.mpr hguard
    have hcorr_mir : s.mir.corrAllowed Q = true := by
      revert hguard_f; cases s.mir.corrAllowed Q <;> simp
    have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
      revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
    have hnospk_mir : SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q = true := by
      revert hguard_f; cases SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q <;> simp
    set figSt := s_fig8.st Q
    set chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    set g_snap := toGhost (P := P) { s with chains := chains } Q figSt
    set s' : SimState PQ Pt ℓ := { s with mir := s.mir.afterCorr Q, chains := chains }
    set sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
      { sC with base := s',
                kept := Function.update sC.kept Q (Kept.ofSt figSt),
                snaps := (Q, s.mir.epoch Q, g_snap) :: sC.snaps }
    set s_R' := s_R.afterCorr Q
    set s_fig8' := s_fig8.afterCorr Q
    rcases simCorr_preserves_simInvC P (InvB Inv q r) ℓ Dh encPt encT qep q r Q x₀ s_R s s_fig8 ec winBefore epExp
      hinv.hsim hcorr_mir hinw_mir hnospk_mir with ⟨hans_eq, hsimC⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inr Q) s_R = pure (some (s_R.st Q), s_R') := by
      rw [stepR_corr_eq]
      change pure (if (s_R.win || !s_R.corrAllowed Q || (true && inWindow s_R Q) || !noAliceCorrWhileAliceBelowEpoch10 s_R Q) = true
        then (none, s_R) else (some (s_R.st Q), s_R.afterCorr Q)) = pure (some (s_R.st Q), s_R')
      rw [hwin_R, hcorr_R, hinw_R, hnospk_R, Bool.false_or, Bool.true_and, hguard_f,
          ite_eq_right Bool.false_ne_true]
    have hcorrPure_fig8 : corrPure Q s_fig8 = (some figSt, s_fig8') := by
      unfold corrPure
      rw [hwin_fig8, hcorr_fig8, hcorr_mir]
      rfl
    have hupd_ec : updateAllEagerCoins s.mir s'.mir (fun _ => false) ec = pure ec :=
      updateAllEagerCoins_same_inWin s.mir (s.mir.afterCorr Q) ec rfl rfl hinv.hsim.hec
    have hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (sC, s_fig8, false) ec =
        pure (some (s_R.st Q), ((sC', s_fig8', false), ec)) := by
      intro k
      change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q (sC, s_fig8, false) ec = _
      unfold stepSimCEagerCorr
      have hstepC : stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (sC, s_fig8, false) =
          stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, s_fig8, false) := rfl
      rw [hstepC, c8_stepSimCNone_corr_eq]
      have hsimCorr : c8_simCorrPureC P Dh encT Q (sC, s_fig8, false) =
          (some (s_R.st Q), (sC', s_fig8', false)) := by
        unfold c8_simCorrPureC
        dsimp only
        rw [show (sC, s_fig8, false).1.base = s from rfl,
            ite_eq_right (by rw [hstop]; decide), hwin_mir, Bool.false_or, hguard_f,
            ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
        dsimp only
        rw [hans_eq]
        rfl
      rw [hsimCorr, pure_bind, hupd_ec, pure_bind]
    have hrem : remWin qep s'.mir ≤ remWin qep s.mir := by
      simp [remWin, s', winCount_afterCorr_eq]
    refine closeByStateC_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inr Q) cont s_R s_R' sC sC' s_fig8 s_fig8' false false ec ec winBefore (some (s_R.st Q))
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl hrem ?_
    refine ih (some (s_R.st Q)) s_R' sC' s_fig8' false ec winBefore epExp ?_
    refine ⟨
      hsimC.mono (fun R => InvB.mono (Nat.sub_le r 1) (hinv.hsim.hpqInv R)),
      hinv.huniq,
      c8_keptInv_corr P Dh encPt encT idOf lam Q sC s' ((Q, s.mir.epoch Q, g_snap) :: sC.snaps)
        s_fig8 hinv.hkept rfl (fun _ _ => rfl),
      hinv.hidx, ?_⟩
    intro hwin'
    rcases hinv.hsync hwin' with ⟨K, rk, hK⟩
    refine ⟨K, rk, { hK with hsnaps := ?_ }⟩
    intro snap hsnap
    rcases List.mem_cons.mp hsnap with rfl | hsnap
    · have hsends_Q : Q.sendsIn (s.mir.epoch Q) = true := by
        unfold inReceiveOnlyEpoch at hinw_mir
        simpa using hinw_mir
      have hchains_Q : chains Q = s.chains Q := by
        cases Q with
        | A => dsimp [chains]
        | B =>
          dsimp [chains]
          split
          · cases figSt.γ <;> simp [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
          · rfl
      have hno_none_Q : ∀ g ∈ s.chains Q, g.key.isNone = false := by
        cases Q with
        | B => exact hinv.hsim.hchainsB_none
        | A =>
          have h10 : 10 ≤ s.mir.epoch .A := by
            unfold SM.noAliceCorrWhileAliceBelowEpoch10 at hnospk_mir
            simpa using hnospk_mir
          exact chainsEpochInvA_no_none hinv.hsim.hchainsA h10
      rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, _, hnot_inw, _⟩
      rcases hnot_inw hinw_mir with ⟨hγ_Q, _, vS, hvS, hvS_last⟩
      have hidx_Q_lt : vS.lastIndex < 2 ^ 32 := by
        have := hinv.hsim.hidx_le Q
        omega
      have hsend_Q : vS.chainKey = lChainAt P.C.F (K (s.mir.epoch Q)) vS.lastIndex := by
        have h := hK.hsend Q vS hvS (by rw [hinv.hsim.htcur Q]; exact hsends_Q)
        rwa [hinv.hsim.htcur Q] at h
      refine ⟨hsends_Q, ?_, ?_, ?_, ?_, ?_⟩
      · change s.mir.epoch Q ≤ max (s_fig8.st .A).tcur (s_fig8.st .B).tcur
        rw [hinv.hsim.htcur .A, hinv.hsim.htcur .B]
        cases Q with
        | A => exact Nat.le_max_left _ _
        | B => exact Nat.le_max_right _ _
      · change figSt.root = rk (s.mir.epoch Q)
        rw [← hinv.hsim.htcur Q]
        exact hK.hroot Q
      · refine ⟨vS.lastIndex, hidx_Q_lt, ?_⟩
        dsimp only [g_snap, toGhost, figSt, s]
        rw [hγ_Q, hvS]
        dsimp only
        rw [hsend_Q]
      · intro rc_ch hrc_ch
        dsimp only [g_snap, toGhost] at hrc_ch
        rw [hchains_Q, List.mem_map] at hrc_ch
        rcases hrc_ch with ⟨g, hg, rfl⟩
        rcases hinv.hsim.hchains_sync Q g hg with ⟨hgep, _, hgkey, v, hvR, hsync_g⟩
        have hnone_g : g.key.isNone = false := hno_none_Q g hg
        rw [hnone_g, ite_eq_right Bool.false_ne_true] at hgkey
        rcases hK.hrecv Q g.epoch v hvR with ⟨hv_ck, hv_sk⟩
        change ∃ ep ≤ s.mir.epoch Q, _
        refine ⟨g.epoch, hgep, ?_, ?_, ?_⟩
        · dsimp only [figSt]
          rw [hvR, hgkey]
          rfl
        · refine ⟨v.lastIndex, hsync_g.last_lt, ?_⟩
          dsimp only [figSt]
          rw [hvR]
          dsimp only
          rw [hv_ck]
        · intro mk hmk
          dsimp only [figSt] at hmk
          rw [hvR] at hmk
          dsimp only at hmk
          rw [List.mem_filterMap] at hmk
          rcases hmk with ⟨j, hj, hmap_j⟩
          cases hlk : v.skippedKeys.lookup j with
          | none => rw [hlk] at hmap_j; cases hmap_j
          | some seed =>
            rw [hlk, Option.map_some, Option.some.injEq] at hmap_j
            subst hmap_j
            dsimp only
            rcases hsync_g.mem_skipped j hj with ⟨hj1, hj_le, _⟩
            have hj_lt : j - 1 < 2 ^ 32 := by have := hsync_g.last_lt; omega
            have hctr : (BitVec.ofNat 32 (j - 1)).toNat + 1 = j := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj_lt]
              omega
            have hseed : seed = lSeedAt P.C.F (K g.epoch) j :=
              hv_sk (j, seed) (c8_mem_of_lookup hlk)
            rw [hctr, hseed]
      · intro h2
        have h2' : 2 ≤ sC.base.mir.epoch Q := h2
        have hlast_ep : ((s.chains Q).map (·.epoch)).getLast? = some (s.mir.epoch Q - 1) := by
          dsimp only [s]
          cases Q with
          | A =>
            rw [hinv.hsim.hchainsA_ep, c8_epListA_getLast]
            congr 1
            have hmod : sC.base.mir.epoch .A % 2 = 1 := by
              simpa [Party.sendsIn, s] using hsends_Q
            omega
          | B =>
            have hmod : sC.base.mir.epoch .B % 2 = 0 := by
              simpa [Party.sendsIn, s] using hsends_Q
            rw [hinv.hsim.hchainsB_ep, c8_epListB_getLast (by omega)]
            congr 1
            omega
        rw [List.getLast?_map, Option.map_eq_some_iff] at hlast_ep
        rcases hlast_ep with ⟨g_last, hglast, hg_ep⟩
        have hmem_last : g_last ∈ s.chains Q := List.mem_of_getLast? hglast
        rcases hinv.hsim.hchains_sync Q g_last hmem_last with
          ⟨_, _, hgkey_last, v_last, hvR_last, _⟩
        have hnone_last : g_last.key.isNone = false := hno_none_Q g_last hmem_last
        rw [hnone_last, ite_eq_right Bool.false_ne_true, hg_ep] at hgkey_last
        dsimp only [g_snap, toGhost, figSt]
        rw [hchains_Q, List.getLast?_map, hglast, Option.map_some]
        refine ⟨_, rfl, ?_⟩
        rw [hvR_last]
        dsimp only
        rw [hgkey_last]
        rfl
    · exact hK.hsnaps snap hsnap

end CryptoGames.LibsignalSM.Proofs.Refinement

