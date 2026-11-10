/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base

/-!
# Ambiguous new-chain inject inside the receive-only window

Proves `closeByStateC_inject_newChain_amb_inWin_true_find_none`, closing the inject step when an
ambiguous new ratchet key arrives inside the receive-only window and no resolved chain is found.
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

/-- Closes `CloseByStateC` for an ambiguous new-chain injection with `inReceiveOnlyEpoch = true` and
no matching resolved chain. -/
theorem closeByStateC_inject_newChain_amb_inWin_true_find_none {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = true)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = true)
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none)
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
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey sC.base
  rcases simRecvStepEager_inject_ambC P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q r x₀
    Q w s_R sC.base s_fig8 ec winBefore epExp hinv.hsim hguard hlen hparse haddrs hspqr hpan hfind
    hevict hzero hamb_b with ⟨hstop0, hw0_if⟩
  simp only [hinw, ↓reduceIte] at hw0_if
  cases hspur_pt : spurPtStep P Dh encPt decT Q w false (ec Q) (sC.base, s_fig8) with
  | true =>
    rw [hspur_pt] at hw0_if
    unfold CloseByStateC
    refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1)
      (Finset.mem_range.mpr (by have := hinv.hsim.hamb; omega)) ?_
    unfold runWinAtC
    have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
    simp only [hnlt, ↓reduceIte, runSimCEager_inr_bind, bind_assoc]
    rw [evalDist_stepSimCEager_inject_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some sC.base.amb) Q w cont (sC, s_fig8, false) ec hstop0 (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan)]
    change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false
      (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
    rw [hw0_if]
    simp
  | false =>
    have hno_none_res : ∀ g ∈ s_res.chains Q, g.key.isNone = false :=
      resolveSim_chains_no_none' spkKey sC.base Q hinv.hsim.hchainsB_none
    have hdummy_res : ∀ g ∈ s_res.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
      intro g hg hgn
      have hgn' := hno_none_res g hg
      simp [hgn] at hgn'
    have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
        cases ratchetKeyAdmissible P.codec decT encT w <;> simp
    rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
    have hT_ne0 : T ≠ 0 := by
      intro h0
      subst h0
      have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
      rw [h0'] at hzero
      exact Bool.noConfusion hzero
    rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, hinw_sp, _, _⟩
    rcases hinw_sp hinw with ⟨hroot, hγ, hT_base_ne0, _⟩
    have hspur_single : spurBadSinglePt P encPt Dh Q (s_fig8.st Q).root T_base w salt T (ec Q) = false := by
      unfold spurPtStep at hspur_pt
      simp only [hinv.hsim.hmeta.hwin_fig8, hinw, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hγ, hT_base_ne0, hlen, hparse, hspqr, hpan, hdecT, hT_ne0] at hspur_pt
      exact hspur_pt
    have hf_R := expectedGhost_session_fields P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q)
    rw [← hinv.hsim.hst_R Q] at hf_R
    rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, hrc_R⟩
    have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
      rw [hpq_R]; exact hspqr
    have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
        (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
      rw [hrc_R, findIdx_toRecvChain_gen (s_fig8.st Q) (s_res.chains Q) h.senderRatchetKey hdummy_res]
      exact hfind_res
    have hrk_R : (s_R.st Q).session.rootKey =
        (rootKdf P.C.F (s_fig8.st Q).root (encPt (Dh.dh (ec Q) T_base))).1 := by
      rw [hinv.hsim.hst_R Q, expectedGhost_of_inWin_true P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q) T_base hinw hγ]
      rfl
    have hsc_R : (s_R.st Q).session.senderChain =
        some ⟨KeyPair.generate P.C (ec Q),
          ⟨((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).2, 0⟩⟩ := by
      rw [hinv.hsim.hst_R Q, expectedGhost_of_inWin_true P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q) T_base hinw hγ]
      rfl
    have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      intro rc
      have hnone := receive_newChain_eq_none_of_spurBadSinglePt_false P Dh encPt encT hX Q (s_R.st Q)
        hparty_R hver_R hloc_R hrem_R (s_fig8.st Q).root T_base (ec Q) _ 0 hrk_R hsc_R
        w hlen (ratchetKeyAdmissible_length_lt P.codec decT encT w h body hon_img hlen hparse)
        h body hparse haddrs pq' salt hspqr_R hfind_R T hT_ne0 hencT hspur_single rc
      unfold libsignalSessionScheme
      dsimp only
      rw [hnone]
      rfl
    have huse_none : simRecvUsesCoin P encT decT none Q w false (sC.base, s_fig8) = false :=
      simRecvUsesCoin_none P encT decT Q w false (sC.base, s_fig8)
    have hnone_div : ((none : Option ℕ) == some sC.base.amb) = false := rfl
    have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
        (some .rejected, ({ sC.base with amb := sC.base.amb + 1 }, s_fig8)) := by
      unfold simRecvStep
      simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hamb_b, hnone_div, hinw, Bool.true_or]
    have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) := by
      unfold simRecvStepCGen
      simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hamb_b, hinw, Bool.true_or]
    have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
      simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
        (by rw [hstep_none]; exact hinv.hsim.hmeta.hstop)
    have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, false) ec =
        pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
      stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
    exact closeByStateC_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
      Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
      (ih (some .rejected))

end CryptoGames.LibsignalSM.Proofs.Refinement
