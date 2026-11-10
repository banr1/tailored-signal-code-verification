/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainResyncAccept
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainResyncReject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.KnownSeedEval

/-!
# Deliver step of the C coupling: new epoch, case-3a resync

Dispatches the new-epoch case-3a `deliver` step with a known `predictReceiveWithSnapshots` outcome into
its rejecting and accepting branches.
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

/-- Closes the new-epoch case-3a `deliver` step when `predictReceiveWithSnapshots` returns `some ev`. -/
theorem closeByStateC_deliver_newChain_resync {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hspec := KeptInv.evalCK_spec P Inv Dh encPt encT idOf lam qep q r hX hDh hid x₀ s_R sC s_fig8
    ec winBefore epExp hinv hinv.hsim.hmeta.hwin_fig8 Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
    hc_mem hc_sender (by rw [htr_mir]; rfl) rfl rfl rfl
  rcases ev with _ | x
  · exact closeByStateC_deliver_newChain_resync_reject
      P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ
      hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender
      hhonC hlen hparse haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval
      (hspec.1 heval) (fun x hx => by cases hx) ih
  · rcases hspec.2 x heval with ⟨st', hfig', pm, hfig⟩ | ⟨hfig', hfig⟩
    · exact closeByStateC_deliver_newChain_resync_accept
        P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ
        hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender
        hhonC hlen hparse haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval
        hfig' hfig ih
    · exact closeByStateC_deliver_newChain_resync_reject
        P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ
        hδ hr post Q w cont x₀ s_R sC s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender
        hhonC hlen hparse haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval
        hfig' (fun _ _ => hfig) ih

end CryptoGames.LibsignalSM.Proofs.Refinement
