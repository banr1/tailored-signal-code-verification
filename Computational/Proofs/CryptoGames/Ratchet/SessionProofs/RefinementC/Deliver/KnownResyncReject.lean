/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep

/-!
# Deliver step of the C coupling: known chain, case-3a resync reject

Closes the known-chain case-3a resync `deliver` step when Fig. 8 rejects `c'`.
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

private theorem dkrr_deliverPure_of_receive_none {Key : Type}
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

private theorem dkrr_fwdPure_of_receive_none {Key : Type}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (Δ qep : ℕ)
    (simSt : SimState PQ Pt ℓ) (Q : Party)
    (c : Fig8C Pt) (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hrcv : sm.receive (s.st Q) c = none) :
    ∃ a, (a = none ∨ a = some .rejected) ∧ fwdPure sm Δ qep SM.Config.h1 simSt Q c s = (a, s) := by
  unfold fwdPure
  split
  · exact dkrr_deliverPure_of_receive_none sm Q c s hrcv
  · unfold injectPure
    split
    · exact ⟨none, Or.inl rfl, rfl⟩
    · exact ⟨some .rejected, Or.inr rfl, by simp [hrcv]⟩

/-- Closes the known-chain case-3a resync `deliver` step when Fig. 8 rejects `c'` (`deliverWin = false` under `Config.h1`, DEV-SM4). -/
theorem closeByStateC_deliver_known_resync_reject {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
    (hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false)
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
  have hmeta := hinv.hsim.hmeta
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hsim.hhon (w, c) hc_mem).1
    hparse with ⟨_, hsrk, hctr, hc_raw⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g, hg_elem, hg_key⟩
  have hg_getD : (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩ = g := by
    simp [List.getD, hg_elem]
  have hrej_g : g.rejects (h.counter.toNat + 1) = false := by rw [← hg_getD]; exact hrej
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, _⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hdh : Dh.dh (epExp g.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
    hinj ((Option.some.inj hg_key_sync).symm.trans hsrk)
  have hle_g : g.epoch ≤ max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B) := by
    have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
      refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
    cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
  have hg_ep : g.epoch = c.1.1 :=
    hinv.hsim.hcoll g.epoch c.1.1 hle_g (hinv.hsim.hhon (w, c) hc_mem).2.1 hdh
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
  have hc'_eq : ((g.epoch, decT h.senderRatchetKey), (h.counter.toNat + 1,
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) =
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) := by
    have h1 : c.1 = (c.1.1, some (Dh.dh (epExp c.1.1) Dh.base)) := congrArg (·.1) hc_raw
    have h3 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
      congrArg (·.2.2.1) hc_raw
    rw [hg_ep, hT_dec, hctr, h3, ← h1]
  have hfig'_g : fig.receive (s_fig8.st Q) ((g.epoch, decT h.senderRatchetKey),
      (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
      = none := by
    rw [hc'_eq]; exact hfig'
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
    have h2 := (receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT hinj idOf lam
      hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hsim Q w hlen h body hparse haddrs
      pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT sC.base.mir rfl rfl rc).2 hrej
    dsimp only at h2
    rw [hg_getD, hfig'_g] at h2
    exact h2
  have hne : c ≠ (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) := fun heq => hsalt (congrArg (·.2.2.2) heq)
  refine closeByStateC_deliver_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
    cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hrcv
    (fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC
      hc_sender)
    (fun k => ?_) ?_ ih
  ·
    rcases dkrr_fwdPure_of_receive_none fig 3 (qep + 1) sC.base Q _ s_fig8 hfig'_g with
      ⟨a, ha, hz⟩
    unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hlen, hparse, haddrs,
      hspqr, hpan, hhonC, hsalt, hfind, hg_getD, hrej_g]
    rw [hz]
    rcases ha with rfl | rfl <;> rfl
  ·
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hlen, hparse, haddrs,
      hspqr, hpan, hhonC, hsalt, hfind, hg_getD, hrej_g, hc'_eq]
    unfold fwdCPure
    simp only [hne, hsafe, heval, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
      Bool.not_false, ↓reduceIte]
    rcases ev with _ | x
    · rfl
    · rcases dkrr_deliverPure_of_receive_none fig Q c s_fig8 (hfig x rfl) with ⟨a, ha, hz⟩
      rw [hz]
      rcases ha with rfl | rfl <;> rfl

end CryptoGames.LibsignalSM.Proofs.Refinement
