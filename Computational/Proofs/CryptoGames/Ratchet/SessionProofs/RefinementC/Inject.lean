/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.KnownChain
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Evicted
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.EncTZero
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.NewChainUnamb
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.AmbInWinFalse
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.AmbInWinTrue
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.AmbFindSome
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Reject

/-!
# Inject step of the C refinement

Dispatches `closeByStateC_inject_step` across the early-reject, known-chain, evicted-epoch
(including `DEV-LS36` salt mismatch), zero-agreement, and new-chain sub-hops in
`RefinementC/Inject/`.
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

/-- Closes `CloseByStateC` across an `inject` query under `SimInvCX`. -/
theorem closeByStateC_inject_step {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  set s := sC.base with hs_def
  by_cases hguard_b : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = true
  · exact closeByStateC_inject_guard_fail P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post Q w cont
      x₀ s_R sC s_fig8 ec winBefore epExp hinv hguard_b ih
  have hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false := Bool.eq_false_iff.mpr hguard_b
  by_cases hlen : w.length < 9
  · exact closeByStateC_inject_lt_nine P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont s_R sC s_fig8 ec winBefore
          epExp hinv hguard hlen ih
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none =>
    exact closeByStateC_inject_parse_none P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont s_R sC s_fig8 ec winBefore
          epExp hinv hguard hlen hparse ih
  | some hb =>
    rcases hb with ⟨h, body⟩
    by_cases haddrs_b : addressCheckPasses h.addresses (P.expectedAddrs Q) = true
    swap
    · exact closeByStateC_inject_addrs_false P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont s_R sC s_fig8 ec winBefore
          epExp hinv hguard hlen hparse
        (Bool.eq_false_iff.mpr haddrs_b) ih
    have haddrs := haddrs_b
    cases hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet with
    | true =>
      exact closeByStateC_inject_spqr_panic P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
        cont s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hpan ih
    | false =>
    cases hspqr : P.spqr.recv (s.pq Q) h.pqRatchet with
    | error e =>
      exact closeByStateC_inject_spqr_error P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont s_R sC s_fig8 ec winBefore
          epExp hinv hguard hlen hparse haddrs
        hspqr hpan ih
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      cases hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        exact closeByStateC_inject_knownChain P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind ih
      | none =>
        by_cases hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
            fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = true
        · exact closeByStateC_inject_evicted_honest P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind hevict ih
        replace hevict := Bool.eq_false_iff.mpr hevict
        by_cases hzero : (decT h.senderRatchetKey == some 0) = true
        · exact closeByStateC_inject_encT_zero P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind hevict hzero ih
        replace hzero := Bool.eq_false_iff.mpr hzero
        by_cases hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true
        swap
        · exact closeByStateC_inject_newChain_unamb P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind hevict hzero
            (Bool.eq_false_iff.mpr hamb_b) ih
        cases hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q).findIdx?
            (fun g => g.key == some h.senderRatchetKey) with
        | some ci =>
          exact closeByStateC_inject_newChain_amb_find_some P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind hevict hzero hamb_b
            hfind_res ih
        | none =>
          cases hinw : inReceiveOnlyEpoch s.mir Q with
          | false =>
            exact closeByStateC_inject_newChain_amb_inWin_false_find_none P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind hevict hzero
              hamb_b hinw hfind_res ih
          | true =>
            exact closeByStateC_inject_newChain_amb_inWin_true_find_none P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                s_R sC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hpan hfind hevict hzero
              hamb_b hinw hfind_res ih

end CryptoGames.LibsignalSM.Proofs.Refinement
