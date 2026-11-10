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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.DeliverProbe
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.DeliverReject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.DeliverSafe
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.DeliverWin
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC

/-!
# Deliver step: honest record of an evicted epoch

Closes `deliver` of an honest wire from an evicted epoch, either rejecting on a matching salt or
dispatching salt mismatches (DEV-LS36) to the `EvictedMismatch` hops.
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

/-- Closes `deliver` of an evicted-epoch honest wire with matching salt, where both sides reject. -/
theorem closeByStateC_deliver_evicted_saltMatch {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1)
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
  have hM := libX25519Rel_model hX
  have hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) =
      some (w, c) := by
    cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
    | none => rw [hf] at hhonC; cases hhonC
    | some wc =>
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rw [hf, Option.map_some] at hhonC
      have hc2 : wc.2 = c := Option.some.inj hhonC
      rcases wc with ⟨w', c'⟩
      dsimp only at hp hc2
      rw [hp.1, hc2]
  rcases hinv.hsim.hhon (w, c) hc_mem with ⟨hc_inv, hc_max, _, hc_le_other⟩
  dsimp only at hc_max hc_le_other
  rw [hc_sender] at hc_le_other
  have hother_adj : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
    have h1 := (hinv.hsim.hep_adj Q.other).2
    have h2 : Q.other.other = Q := by cases Q <;> rfl
    rwa [h2] at h1
  have hc_le_Q : c.1.1 ≤ sC.base.mir.epoch Q := by omega
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hc_inv hparse with
    ⟨_, hsrk, _, _⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
    intro heq
    rw [hsrk, ← hinv.hsim.hepExp0] at heq
    have hdh := hinj heq
    have ht0 := hinv.hsim.hcoll c.1.1 0 hc_max (Nat.zero_le _) hdh
    omega
  have hc_not_mem : c.1.1 ∉ (sC.base.chains Q).map (·.epoch) := by
    intro hmem_ep
    rw [List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g, hg_mem, hg_ep⟩
    rcases hinv.hsim.hchains_sync Q g hg_mem with ⟨_, _, hg_key, _⟩
    have hgn : g.key.isNone = false := by
      cases Q with
      | B => exact hinv.hsim.hchainsB_none g hg_mem
      | A =>
        rw [Bool.eq_false_iff]
        intro hnone
        have hep0 := hinv.hsim.hchainsA.1 g hg_mem hnone
        omega
    simp only [hgn, Bool.false_eq_true, ↓reduceIte, hg_ep, ← hsrk] at hg_key
    have hnone := List.findIdx?_eq_none_iff.mp hfind g hg_mem
    simp [hg_key] at hnone
  rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, hinw, hninw, hevict_spur⟩
  rcases hevict_spur (w, c) hc_mem hc_sender hc_le_Q hc_not_mem with ⟨hpos_Q, hspur_false⟩
  rcases expectedGhost_root_senderChain_of_posC P (InvB Inv q r) Dh encPt encT qep q r x₀ hinv.hsim Q
    rk_base T_base hinw hninw hpos_Q with ⟨ck_prev, idx_prev, hrk_R, hsc_R⟩
  have hf_R := expectedGhost_session_fields P Dh encPt (encT (Dh.dh x₀ Dh.base))
    sC.base Q (s_fig8.st Q) (ec Q)
  rw [← hinv.hsim.hst_R Q] at hf_R
  rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, _⟩
  have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
    rw [hpq_R]; exact hspqr
  have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
      (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_findIdx_none_of_ne P Dh encPt (encT (Dh.dh x₀ Dh.base))
      sC.base Q (s_fig8.st Q) (ec Q) hinv.hsim.hchainsB_none h.senderRatchetKey hsrk_ne_spk hfind
  have hy_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hspur_salt : spurBadSingle P encPt Dh Q rk_base T_base w salt
      (epExp c.1.1) (epExp (maxActiveEp sC.base.mir Q)) = false := by
    rw [← spurBadSingle_effSalt, ← hsalt]; exact hspur_false
  refine closeByStateC_deliver_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir ?_ ?_ ?_ ?_ ih
  · intro rc
    exact receive_evicted_honest_eq_none P Dh encPt encT hX Q (s_R.st Q)
      hparty_R hver_R hloc_R hrem_R rk_base T_base (epExp (maxActiveEp sC.base.mir Q))
      ck_prev idx_prev hrk_R hsc_R w hlen (honestEntryInvC_len_lt hc_inv) h body hparse haddrs pq' salt hspqr_R
      hfind_R (epExp c.1.1) hy_ne0 hsrk.symm hspur_salt rc
  · intro k
    exact simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  · intro k
    unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon,
      hepoch]
  · unfold simRecvStepC simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon,
      hepoch, hsalt]

/-- Dispatches `deliver` of an evicted-epoch honest wire with a mismatched salt (DEV-LS36) across the window, counter-bound, and `safeInj 3` cases. -/
theorem closeByStateC_deliver_evicted_saltMismatch {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  cases hinw : inReceiveOnlyEpoch sC.base.mir Q
  · by_cases hbound : (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)
    · exact closeByStateC_deliver_evictedMismatch_reject
        P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32
        δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem
        hc_sender hhonC hlen hparse haddrs hspqr hpan hfind hepoch hsalt hinw hbound ih
    · cases hsafe : sC.base.mir.safeInj 3
      · exact closeByStateC_deliver_evictedMismatch_probe
          P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS
          hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem
          hc_sender hhonC hlen hparse haddrs hspqr hpan hfind hepoch hsalt hinw hbound hsafe ih
      · exact closeByStateC_deliver_evictedMismatch_safe
          P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS
          hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem
          hc_sender hhonC hlen hparse haddrs hspqr hpan hfind hepoch hsalt hinw hbound hsafe ih
  · exact closeByStateC_deliver_evictedMismatch_inWin
      P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ
      hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender
      hhonC hlen hparse haddrs hspqr hpan hfind hepoch hsalt hinw ih

end CryptoGames.LibsignalSM.Proofs.Refinement
