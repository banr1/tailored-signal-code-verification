/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep

/-!
# Deliver step: known chain, case 3a probe

Closes `deliver` on a known receiver chain under `!safeInj 3` when `predictReceive` returns `none`,
answering `rejected` and setting the probe flag iff Fig. 8 accepts the salt-replaced record.
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

private theorem dkp_onAnswerPure_stopped {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped := by
  unfold onAnswerPure onAcceptPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      dsimp only
      split
      · cases s.mir.inTransit Q.other w <;> rfl
      · split <;> [rfl; (split <;> rfl)]

/-- Closes `deliver` on a known chain in case 3a when `predictReceive` is `none`, coupling libsignal acceptance with the Fig. 8 probe flag. -/
theorem closeByStateC_deliver_known_probe {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = none)
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
  have htr_none : (sC.base.mir.inTransit Q.other w).isNone = false := by
    rw [htr_mir]; rfl
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hsim.hhon (w, c) hc_mem).1 hparse with
    ⟨_, hsrk, hctr, hc_eq⟩
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, _⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hsrk_g : h.senderRatchetKey = encT (Dh.dh (epExp g.epoch) Dh.base) :=
    Option.some.inj hg_key_sync
  have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp g.epoch) Dh.base :=
    hinj (hsrk.symm.trans hsrk_g)
  have hle_g : g.epoch ≤ max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B) := by
    have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
      refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
    cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
  have hep_eq : c.1.1 = g.epoch :=
    hinv.hsim.hcoll c.1.1 g.epoch (hinv.hsim.hhon (w, c) hc_mem).2.1 hle_g hdh
  have hdec_srk : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hdec_srk, Option.map_some, Option.getD_some, hsrk]
  let c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  have hc1 : c.1 = (g.epoch, decT h.senderRatchetKey) := by
    rw [← hep_eq, hdec_srk]
    exact congrArg Prod.fst hc_eq
  have hc21 : c.2.1 = h.counter.toNat + 1 := hctr.symm
  have hc221 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
    congrArg (fun x : Fig8C Pt => x.2.2.1) hc_eq
  have hc'_eq : ((g.epoch, decT h.senderRatchetKey),
      (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) = c' := by
    dsimp only [c']
    rw [hc1, hc21, hc221]
  have hc_ne : c ≠ c' := fun h => hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) h)
  have hc_ne_dec : decide (c ≠ c') = true := decide_eq_true hc_ne
  have heval' : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = none := heval
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, htr_none, hlen, hparse, haddrs, hspqr, hpan, hfind]
  have hstops : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
    intro k
    refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
    unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_none, Bool.false_eq_true, ↓reduceIte,
      Bool.true_and, Bool.not_true, Bool.false_and, hlen, hparse, haddrs, hspqr, hpan, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false from hrej]
    rw [dkp_onAnswerPure_stopped]
    exact hmeta.hstop
  have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8,
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c').isSome)) := by
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_none, Bool.false_eq_true, ↓reduceIte,
      Bool.true_and, Bool.not_true, Bool.false_and, Bool.not_false, hlen, hparse, haddrs, hspqr, hpan,
      hfind, hhonC, hsalt,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false from hrej]
    change fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true (some ci) h.senderRatchetKey pq'
      (some c) ((g.epoch, decT h.senderRatchetKey),
        (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
      (sC, s_fig8, false) = _
    rw [hc'_eq]
    unfold fwdCPure
    simp only [hc_ne_dec, hsafe, Bool.not_false, Bool.and_self, ↓reduceIte, heval', Bool.false_or]
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec =
      pure (some .rejected, ((sC, s_fig8,
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c').isSome), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hsim.hec (huse k) (hstops k) _ hresC rfl
  cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' with
  | some v =>
    refine closeByStateC_inr_of_fl_step P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R sC s_fig8 false ec winBefore ?_
    intro z hz
    rw [hstep none, hfig, Option.isSome_some, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | none =>
    have hstep' : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := by
      intro k
      simpa [hfig] using hstep k
    have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := by
      intro rc
      have h2 := (receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
        hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hsim Q w hlen h body
        hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT sC.base.mir rfl rfl rc).2 hrej
      dsimp only at h2
      rw [show (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩ = g from rfl, hc'_eq, hfig] at h2
      exact h2
    have hR_map := hmeta.inTransit_R_map Q.other w
    rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      rw [hrcv rc]
    exact closeByStateC_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore
      (some .rejected)
      (stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R)
      hstepR (hstep' none) (fun idx _ => hstep' (some idx)) rfl le_rfl
      (ih (some .rejected) s_R sC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))

end CryptoGames.LibsignalSM.Proofs.Refinement
