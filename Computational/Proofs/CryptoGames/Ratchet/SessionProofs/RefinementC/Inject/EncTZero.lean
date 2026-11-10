/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Reject

/-!
# New-key inject with zero X25519 agreement

Proves `closeByStateC_inject_encT_zero`, closing the inject step when a new ratchet key has zero
X25519 agreement so both sides reject.
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

private theorem ie0_expectedGhost_senderChain_someC (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) :
    ∃ x ck_prev idx_prev,
      (s_R.st Q).session.senderChain =
        some ⟨KeyPair.generate P.C x, ⟨ck_prev, idx_prev⟩⟩ := by
  rw [hinv.hst_R Q]
  rcases hinv.hspur Q with ⟨rk_base, T_base, hinw, hninw, _⟩
  by_cases hw : inReceiveOnlyEpoch s.mir Q = true
  · rcases hinw hw with ⟨_, hγ, _, _⟩
    rw [expectedGhost_of_inWin_true P Dh encPt _ s Q (s_fig8.st Q) (ec Q) T_base hw hγ]
    exact ⟨ec Q, _, 0, rfl⟩
  · have hwf : inReceiveOnlyEpoch s.mir Q = false := Bool.eq_false_iff.mpr hw
    rcases hninw hwf with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
    rw [expectedGhost_of_inWin_false P Dh encPt _ s Q (s_fig8.st Q) (ec Q) hwf]
    unfold toGhost
    dsimp only
    rw [hγ, hvS]
    exact ⟨epExp (s.mir.epoch Q), vS.chainKey, BitVec.ofNat 32 vS.lastIndex, rfl⟩

/-- Closes `CloseByStateC` when an injected new ratchet key yields zero X25519 agreement. -/
theorem closeByStateC_inject_encT_zero {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hzero : (decT h.senderRatchetKey == some 0) = true)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hM := libX25519Rel_model hX
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT0 : decT h.senderRatchetKey = some 0 := beq_iff_eq.mp hzero
  have hT_eq : T = 0 := Option.some.inj (hdecT.symm.trans hT0)
  subst hT_eq
  have hT0_ne : Dh.dh x₀ Dh.base ≠ 0 := hM.dh_ne_zero x₀ Dh.base hM.base_ne_zero
  have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
    intro heq
    exact hT0_ne (hinj (heq.symm.trans hencT.symm))
  rcases ie0_expectedGhost_senderChain_someC P (InvB Inv q r) Dh encPt encT qep q r x₀ hinv.hsim Q with
    ⟨x_sc, ck_prev, idx_prev, hsc_R⟩
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
  refine closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard ?_ ?_ ?_ ?_ ih
  · intro rc
    exact receive_eq_none_of_encT_zero P Dh encPt encT hX hz Q (s_R.st Q)
      hparty_R hver_R hloc_R hrem_R x_sc ck_prev idx_prev hsc_R
      w hlen h body hparse haddrs pq' salt hspqr_R hfind_R hencT rc
  · intro k
    unfold simRecvUsesCoin
    simp [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero]
  · intro k
    unfold simRecvStep
    simp [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero]
  · unfold simRecvStepCGen
    simp [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero]

end CryptoGames.LibsignalSM.Proofs.Refinement
