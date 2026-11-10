/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.KnownReject
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.KnownSaltMatch
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.KnownSaltMismatchSafe
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.KnownResync
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.KnownProbe
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Evicted
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainJump
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainSaltMatch
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainSaltMismatchSafe
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainResync
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainProbe
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Honest

/-!
# Refinement without salt binding: the deliver step

Proves `closeByStateC_deliver_step`, closing one `deliver` step of the C coupling across
not-in-transit, SPQR error/panic, known-chain, new-epoch, and evicted-epoch cases, including
salt-steered honest wires under case 3 and evicted salt mismatches (`DEV-LS36`).
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

/-- Closes one `deliver` step of the C coupling by dispatching across `simRecvStepCGen` cases. -/
theorem closeByStateC_deliver_step {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  cases htr_mir : sC.base.mir.inTransit Q.other w with
  | none =>
    exact closeByStateC_deliver_not_inTransit P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
      Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir ih
  | some r_mir =>
    rcases deliver_inTransit_mem hinv.hsim.hmeta
      (fun r hr => ⟨(hinv.hsim.htrans_hon r hr).1, (hinv.hsim.htrans_hon r hr).2.1⟩)
      Q w htr_mir with ⟨c, hc_mem, hc_sender⟩
    rcases (hinv.hsim.hhon (w, c) hc_mem).1 with ⟨_, hlen, _, _, _, _, _,
      h, body, hparse, _, _, _, haddrs_other, _⟩
    have hQQ : Q.other.other = Q := by cases Q <;> rfl
    have haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := by
      rw [hc_sender, hQQ] at haddrs_other
      exact haddrs_other
    have hhonC := honestC_eq_some_of_memC P (InvB Inv q r) Dh encT hinj epExp
      (max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)) sC.base hinv.huniq Q w c
      hc_mem hc_sender (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
      hinv.hsim.hcoll
    cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet with
    | true =>
      exact closeByStateC_deliver_spqr_panic P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hlen hparse haddrs hpan ih
    | false =>
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error e_pq =>
      exact closeByStateC_deliver_spqr_error P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hlen hparse haddrs hspqr hpan ih
    | ok val_pq =>
      rcases val_pq with ⟨pq', salt⟩
      cases hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) with
        | true =>
          exact closeByStateC_deliver_known_rejects P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
            hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
            winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind
            hrej ih
        | false =>
          by_cases hsalt : c.2.2.2 = effectiveHkdfSalt32 salt
          · exact closeByStateC_deliver_known_saltMatch P Inv ℓ Dh hDh encPt encT decT idOf hX hdec
              hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
              winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind
              hrej hsalt ih
          · cases hsafe : sC.base.mir.safeInj 3 with
            | true =>
              exact closeByStateC_deliver_known_saltMismatch_safe P Inv ℓ Dh hDh encPt encT decT idOf
                hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC
                s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs
                hspqr hpan hfind hrej hsalt hsafe ih
            | false =>
              cases heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                  (fs := lFS P.C P.codec ℓ encT idOf 25000)
                  P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) with
              | some ev =>
                exact closeByStateC_deliver_known_resync P Inv ℓ Dh hDh encPt encT decT idOf hX hdec
                  hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8
                  ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan
                  hfind hrej hsalt hsafe heval ih
              | none =>
                exact closeByStateC_deliver_known_probe P Inv ℓ Dh hDh encPt encT decT idOf hX hdec
                  hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8
                  ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan
                  hfind hrej hsalt hsafe heval ih
      | none =>
        by_cases hepoch : c.1.1 = sC.base.mir.epoch Q + 1
        ·
          by_cases hjump : 25000 < h.counter.toNat + 1 - 1
          · exact closeByStateC_deliver_newChain_jump P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
              hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
              winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind
              hepoch hjump ih
          · by_cases hsalt : c.2.2.2 = effectiveHkdfSalt32 salt
            · exact closeByStateC_deliver_newChain_saltMatch P Inv ℓ Dh hDh encPt encT decT idOf hX
                hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC
                s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs
                hspqr hpan hfind hepoch hjump hsalt ih
            · cases hsafe : sC.base.mir.safeInj 3 with
              | true =>
                exact closeByStateC_deliver_newChain_saltMismatch_safe P Inv ℓ Dh hDh encPt encT decT
                  idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀
                  s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse
                  haddrs hspqr hpan hfind hepoch hjump hsalt hsafe ih
              | false =>
                cases heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                    (fs := lFS P.C P.codec ℓ encT idOf 25000)
                    P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) with
                | some ev =>
                  exact closeByStateC_deliver_newChain_resync P Inv ℓ Dh hDh encPt encT decT idOf hX
                    hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC
                    s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse
                    haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval ih
                | none =>
                  exact closeByStateC_deliver_newChain_probe P Inv ℓ Dh hDh encPt encT decT idOf hX
                    hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC
                    s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse
                    haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval ih
        ·
          by_cases hsalt : c.2.2.2 = effectiveHkdfSalt32 salt
          · exact closeByStateC_deliver_evicted_saltMatch P Inv ℓ Dh hDh encPt encT decT idOf hX hdec
              hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
              winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind
              hepoch hsalt ih
          · exact closeByStateC_deliver_evicted_saltMismatch P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
              hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
              winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind
              hepoch hsalt ih

end CryptoGames.LibsignalSM.Proofs.Refinement
