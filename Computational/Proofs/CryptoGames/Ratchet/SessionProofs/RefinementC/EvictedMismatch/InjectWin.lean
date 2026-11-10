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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.WinBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC

/-!
# Evicted salt mismatch on inject: inside the window

Proves `closeByStateC_inject_evictedMismatch_inWin`, handling an injected wire with an evicted salt mismatch inside the receive-only window via the `evictStopsC` stopping run.
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

/-- On an injected wire with an evicted salt mismatch inside `inReceiveOnlyEpoch`, `libsignalToModularSchemeSim` rejects with `amb + 1` while the `k = some amb` run stops at `evictStopsC` with win bit `spurPtStep`. -/
theorem closeByStateC_inject_evictedMismatch_inWin {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = true)
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
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none →
      h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1 := by
    simp only [hfind_hon, Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hevict
    exact hevict
  have hcase : evictCaseC P encT decT Q w false sC.base = true := by
    unfold evictCaseC
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon,
      hepoch, hmis, hzero_f, hinw]
  have hev : evictStopsC P encT decT (some sC.base.amb) Q w false (sC, s_fig8, false) = true := by
    simp [evictStopsC, hcase]
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_eq_false_of_evictCaseC P encT decT k Q w false (sC.base, s_fig8) hcase
  have hres_sim : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)) :=
    fun k => simRecvStep_of_evictCaseC P ℓ Dh encPt encT decT idOf lam qep k Q w false 0
      (sC.base, s_fig8) hcase
  have hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) :=
    simRecvStepCGen_of_evictCaseC P ℓ Dh encPt encT decT idOf lam qep false Q w false
      (sC, s_fig8, false) hcase
  have hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec =
      pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
    stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) ec hsim.hec (huse_all none)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false
        (sC.base, s_fig8) (by rw [hres_sim none]; exact hmeta.hstop))
      _ hresC rfl
  have hw0 := evalDist_stepSimCEager_inject_evictStop P ℓ Dh encPt encT decT idOf lam qep
    (some sC.base.amb) Q w cont (sC, s_fig8, false) ec hev
  dsimp only [JointC.sim] at hw0
  cases hspur : spurPtStep P Dh encPt decT Q w false (ec Q) (sC.base, s_fig8) with
  | true =>
    rw [hspur] at hw0
    exact closeByStateC_inr_amb_stopEq_win P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inr (Q, w))) cont s_R sC s_fig8 false ec winBefore
      (by have := hsim.hamb; omega) hw0
  | false =>
    rw [hspur] at hw0
    have hrcv := receive_none_of_spurPtStep_false_inWin P (InvB Inv q r) ℓ Dh encPt encT decT idOf hX
      lam qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hsim Q w hlen (honestEntryInvC_len_lt hhon_c) hparse haddrs hspqr hpan hinw
      T hT_dec hT_ne0 hsrk.symm hfind_res hdummy_res hspur
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
    exact closeByStateC_inr_amb_stopEq_false P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inr (Q, w))) cont s_R sC
      { sC with base := { sC.base with amb := sC.base.amb + 1 } } s_fig8 s_fig8 false false ec ec
      winBefore (some .rejected) ($ᵗ BitVec 256) (fun _ => s_R)
      hD0 hstepR hnone hw0 rfl le_rfl
      (fun _ => ih (some .rejected) s_R
        { sC with base := { sC.base with amb := sC.base.amb + 1 } } s_fig8 false ec
        (fun j => if j = sC.base.amb then false else winBefore j) epExp
        (simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀ s_R sC s_fig8 ec
          winBefore epExp hinv rfl))

end CryptoGames.LibsignalSM.Proofs.Refinement
