/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedRecvBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.KnownSeedEval
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted `deliver` step: known-chain salt mismatch

Proves the known-chain salt-mismatch `deliver` cases (`probe`, `resync`, and `saltMismatch_safe`)
for `CloseByStateCTrack`.
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory
open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Proofs
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section DeliverKnown

variable {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]

private theorem dkp_onAnswerPure_stopped_track {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
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

theorem closeByStateCTrack_deliver_known_probe {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
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
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hcx := hinv.hcx
  have hmeta := hcx.hsim.hmeta
  have htr_none : (sC.base.mir.inTransit Q.other w).isNone = false := by rw [htr_mir]; rfl
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hcx.hsim.hhon (w, c) hc_mem).1
    hparse with ⟨_, hsrk, hctr, hc_eq⟩
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hcx.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, _⟩
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
    hcx.hsim.hcoll c.1.1 g.epoch (hcx.hsim.hhon (w, c) hc_mem).2.1 hle_g hdh
  have hdec_srk : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hdec_srk, Option.map_some, Option.getD_some, hsrk]
  let c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  have hc1 : c.1 = (g.epoch, decT h.senderRatchetKey) := by
    rw [← hep_eq, hdec_srk]; exact congrArg Prod.fst hc_eq
  have hc21 : c.2.1 = h.counter.toNat + 1 := hctr.symm
  have hc221 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
    congrArg (fun x : Fig8C Pt => x.2.2.1) hc_eq
  have hc'_eq : ((g.epoch, decT h.senderRatchetKey),
      (h.counter.toNat + 1,
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
          effectiveHkdfSalt32 salt))) = c' := by
    dsimp only [c']; rw [hc1, hc21, hc221]
  have hc_ne : c ≠ c' := fun h => hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) h)
  have hc_ne_dec : decide (c ≠ c') = true := decide_eq_true hc_ne
  have heval' : predictReceiveWithSnapshots
      (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = none := heval
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false := by
    intro k; unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, htr_none, hlen, hparse, haddrs, hspqr, hpan, hfind]
  have hstops : ∀ k,
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
    intro k
    refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true
      (sC.base, s_fig8) ?_
    unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_none, Bool.false_eq_true, ↓reduceIte,
      Bool.true_and, Bool.not_true, Bool.false_and, hlen, hparse, haddrs, hspqr, hpan, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej]
    rw [dkp_onAnswerPure_stopped_track]
    exact hmeta.hstop
  have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8,
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c').isSome)) := by
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_none, Bool.false_eq_true, ↓reduceIte,
      Bool.true_and, Bool.not_true, Bool.false_and, Bool.not_false, hlen, hparse, haddrs, hspqr,
      hpan, hhonC, hsalt, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej]
    change fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true (some ci) h.senderRatchetKey pq'
      (some c) ((g.epoch, decT h.senderRatchetKey),
        (h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
            effectiveHkdfSalt32 salt)))
      (sC, s_fig8, false) = _
    rw [hc'_eq]
    unfold fwdCPure
    simp only [hc_ne_dec, hsafe, Bool.not_false, Bool.and_self, ↓reduceIte, heval', Bool.false_or]
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
      pure (some .rejected, ((sC, s_fig8,
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c').isSome),
        ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hcx.hsim.hec (huse k) (hstops k) _ hresC rfl
  cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' with
  | some v =>
    refine closeByStateCTrack_deliver_of_fl_step P K ℓ Dh encPt encT decT idOf lam qep q δ post
      Q w cont s_R stTrR sC trC s_fig8 false ec winBefore ?_
    intro z hz
    rw [hstep none, hfig, Option.isSome_some, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | none =>
    have hstep' : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k
        (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
        pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k => by
      simpa [hfig] using hstep k
    have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
      have h2 := (receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
        hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hcx.hsim Q w hlen h body
        hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT sC.base.mir rfl rfl
        rc).2 hrej
      dsimp only at h2
      rw [show (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩ = g from rfl, hc'_eq, hfig] at h2
      exact h2
    have hR_map := hmeta.inTransit_R_map Q.other w
    rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc; rw [hrcv rc]
    exact closeByStateCTrack_deliver_const_rc_same_amb P K ℓ Dh encPt encT decT idOf lam qep q δ
      post Q w cont s_R s_R stTrR sC sC trC s_fig8 s_fig8 false false ec ec winBefore
      (some .rejected) hstepR (hstep' none) (fun idx _ => hstep' (some idx)) rfl le_rfl
      (ih (some .rejected) s_R stTrR sC trC s_fig8 false ec winBefore epExp
        (hinv.mono_r (Nat.sub_le r 1)))

private theorem dkrr_deliverPure_of_receive_none_track {Key : Type} {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (c : Fig8C Pt)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hrcv : sm.receive (s.st Q) c = none) :
    ∃ a, (a = none ∨ a = some .rejected) ∧ deliverPure sm SM.Config.h1 Q c s = (a, s) := by
  unfold deliverPure
  by_cases hw : s.win = true
  · exact ⟨none, Or.inl rfl, by simp [hw]⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit Q.other c with
    | none => exact ⟨none, Or.inl rfl, rfl⟩
    | some r => refine ⟨some .rejected, Or.inr rfl, ?_⟩; simp [hrcv, SM.Config.h1]

private theorem dkrr_fwdPure_of_receive_none_track {Key : Type} {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Δ qep : ℕ) (simSt : SimState PQ Pt ℓ) (Q : Party) (c : Fig8C Pt)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hrcv : sm.receive (s.st Q) c = none) :
    ∃ a, (a = none ∨ a = some .rejected) ∧ fwdPure sm Δ qep SM.Config.h1 simSt Q c s = (a, s) := by
  unfold fwdPure
  split
  · exact dkrr_deliverPure_of_receive_none_track sm Q c s hrcv
  · unfold injectPure
    split
    · exact ⟨none, Or.inl rfl, rfl⟩
    · exact ⟨some .rejected, Or.inr rfl, by simp [hrcv]⟩

theorem closeByStateCTrack_deliver_known_resync_reject {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
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
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some ev)
    (hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = none)
    (hfig : ∀ x, ev = some x →
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c = none)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hcx := hinv.hcx
  have hmeta := hcx.hsim.hmeta
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hcx.hsim.hhon (w, c) hc_mem).1
    hparse with ⟨_, hsrk, hctr, hc_raw⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g, hg_elem, hg_key⟩
  have hg_getD : (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩ = g := by simp [List.getD, hg_elem]
  have hrej_g : g.rejects (h.counter.toNat + 1) = false := by rw [← hg_getD]; exact hrej
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hcx.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, _⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hdh : Dh.dh (epExp g.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
    hinj ((Option.some.inj hg_key_sync).symm.trans hsrk)
  have hle_g : g.epoch ≤ max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B) := by
    have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
      refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
    cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
  have hg_ep : g.epoch = c.1.1 :=
    hcx.hsim.hcoll g.epoch c.1.1 hle_g (hcx.hsim.hhon (w, c) hc_mem).2.1 hdh
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
  have hc'_eq : ((g.epoch, decT h.senderRatchetKey), (h.counter.toNat + 1,
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
        effectiveHkdfSalt32 salt))) =
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) := by
    have h1 : c.1 = (c.1.1, some (Dh.dh (epExp c.1.1) Dh.base)) := congrArg (·.1) hc_raw
    have h3 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
      congrArg (·.2.2.1) hc_raw
    rw [hg_ep, hT_dec, hctr, h3, ← h1]
  have hfig'_g : fig.receive (s_fig8.st Q) ((g.epoch, decT h.senderRatchetKey),
      (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
        effectiveHkdfSalt32 salt))) = none := by
    rw [hc'_eq]; exact hfig'
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
    have h2 := (receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT hinj idOf lam
      hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hcx.hsim Q w hlen h body hparse haddrs
      pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT sC.base.mir rfl rfl rc).2 hrej
    dsimp only at h2
    rw [hg_getD, hfig'_g] at h2
    exact h2
  have hne : c ≠ (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) :=
    fun heq => hsalt (congrArg (·.2.2.2) heq)
  refine closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
    post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hrcv
    (fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC
      hc_sender)
    (fun k => ?_) ?_ ih
  · rcases dkrr_fwdPure_of_receive_none_track fig 3 (qep + 1) sC.base Q _ s_fig8 hfig'_g with
      ⟨a, ha, hz⟩
    unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hlen, hparse, haddrs,
      hspqr, hpan, hhonC, hsalt, hfind, hg_getD, hrej_g]
    rw [hz]
    rcases ha with rfl | rfl <;> rfl
  · unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hlen, hparse, haddrs,
      hspqr, hpan, hhonC, hsalt, hfind, hg_getD, hrej_g, hc'_eq]
    unfold fwdCPure
    simp only [hne, hsafe, heval, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
      Bool.not_false, ↓reduceIte]
    rcases ev with _ | x
    · rfl
    · rcases dkrr_deliverPure_of_receive_none_track fig Q c s_fig8 (hfig x rfl) with ⟨a, ha, hz⟩
      rw [hz]
      rcases ha with rfl | rfl <;> rfl

theorem closeByStateCTrack_deliver_known_resync_accept {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
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
    {x : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some (some x))
    {st' : Fig8St Pt} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some (st', x))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
      some (st', (x.1, x.2.1, pm)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hcx := hinv.hcx
  have hmeta := hcx.hsim.hmeta
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  set c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hcx.hsim.hpqInv Q) hspqr
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hcx.huniq
    (fun wc hwc => ⟨(hcx.hsim.hhon wc hwc).1, (hcx.hsim.hhon wc hwc).2.1⟩)
    (fun r' hr' => ⟨(hcx.hsim.htrans_hon r' hr').1, (hcx.hsim.htrans_hon r' hr').2.1⟩)
    hcx.hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC₀, _⟩
  have hc₀_eq : c₀ = c := Option.some.inj (hhonC₀.symm.trans hhonC)
  subst c₀
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]; exact inTransit_fig8_pos_epoch_eq hcx.hsim.htrans_hon hr_fig8
  rcases hcx.hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨_, hsrk, _, hc_raw⟩
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by rw [hsrk, hdec]
  have hT_map : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hcx.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_ep, v, hvR, _⟩
  have hg_ep_eq : g.epoch = c.1.1 := by
    have hnot_none : g.key.isNone = false := by rw [hg_key]; rfl
    rw [hnot_none] at hg_key_ep
    simp only [Bool.false_eq_true, ↓reduceIte, hg_key, hsrk, Option.some.injEq] at hg_key_ep
    have hle1 : g.epoch ≤ M := by
      have : g.epoch ≤ maxActiveEp sC.base.mir Q := by unfold maxActiveEp; omega
      cases Q <;> [exact le_trans this (le_max_left _ _); exact le_trans this (le_max_right _ _)]
    exact hcx.hsim.hcoll g.epoch c.1.1 hle1 hc_le_M (hinj hg_key_ep.symm)
  have hpos_ep : r_mir.pos.epoch = g.epoch := hpos_mir_ep.trans hg_ep_eq.symm
  have hpos_le_epQ : r_mir.pos.epoch ≤ sC.base.mir.epoch Q := by rw [hpos_ep]; exact hg_ep_le
  have hg_ep_tcur : g.epoch ≤ (s_fig8.st Q).tcur := by rw [hcx.hsim.htcur Q]; exact hg_ep_le
  have hc1 : c.1 = (g.epoch, decT h.senderRatchetKey) := by
    rw [hg_ep_eq, hT_dec]; exact congrArg Prod.fst hc_raw
  have hc21 : c.2.1 = i := congrArg (fun z => z.2.1) hc_raw
  have hc221 : c.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))) :=
    congrArg (fun z => z.2.2.1) hc_raw
  have hc'_eq_g : ((g.epoch, decT h.senderRatchetKey), i,
      (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
      effectiveHkdfSalt32 salt) = c' := by
    dsimp only [c']; rw [hc1, hc21, hc221]
  set pos := r_mir.pos
  have hmir_ep : (sC.base.mir.accept Q () pos).epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hpos_le_epQ
  have hmir_idx : (sC.base.mir.accept Q () pos).idx = sC.base.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
    hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hcx.hsim Q w hlen h body
    hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT_map
    (sC.base.mir.accept Q () pos) hmir_ep hmir_idx rc
  rcases x with ⟨t', i', pub, m⟩
  have hfig'_raw : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
        h.counter.toNat + 1, (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
        effectiveHkdfSalt32 salt) = some (st', t', i', pub, m) := by
    rw [show ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
        h.counter.toNat + 1, (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
        effectiveHkdfSalt32 salt) = c' from hc'_eq_g]
    exact hfig'
  have hstep0 := (hstep_all 0).2 hrej
  dsimp only at hstep0
  rw [hfig'_raw] at hstep0
  rcases hstep0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
  subst ht' hi'
  dsimp only at hfig
  set s' : SimState PQ Pt ℓ :=
    { sC.base with
      mir := sC.base.mir.accept Q () pos
      pq := Function.update sC.base.pq Q pq'
      unackA := sC.base.unackA && Q != Party.A
      chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
  set kept' := Function.update sC.kept Q
    (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
  set sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s', kept := kept' }
  set s_fig8' := s_fig8.accept Q st' pos
  set s_R' := s_R.accept Q (expectedGhost P Dh encPt spkKey s' Q st' (ec Q)) pos
  set ans : Option (RecvResult (Plain ℓ)) :=
    some (.accepted g.epoch i (if sC.base.mir.chall.contains pos then none else some m))
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')) := by
    rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
    congr 1; funext rc
    have hstep_rc := (hstep_all rc).2 hrej
    dsimp only at hstep_rc
    rw [hfig'_raw] at hstep_rc
    rcases hstep_rc with ⟨_, _, _, _, m_raw, hm_eq, hrec_rc⟩
    rw [hrec_rc]; dsimp only
    rw [← hm_eq, hpos_R, hmeta.hchall_R]
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC
      hc_sender
  have hstops : ∀ k,
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvStops simRecvStep; dsimp only
    rw [recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan, hmeta.hstop, hmeta.hwin_mir,
      htr_mir]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and, Option.isNone_some, hlen,
      Bool.not_true, Bool.not_false, Bool.false_and, hparse, haddrs, hspqr, hpan, hfind]
    split
    · exact hmeta.hstop
    · unfold onAnswerPure
      cases (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          sC.base Q _ s_fig8).1 with
      | none => exact hmeta.hstop
      | some res =>
        cases res with
        | rejected => exact hmeta.hstop
        | accepted t_a i_a pm_a => unfold onAcceptPure; simp [htr_mir, hmeta.hstop]
  have hstepC_res : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (ans, (sC', s_fig8', false)) := by
    unfold simRecvStepC simRecvStepCGen; dsimp only
    have hsalt_if : (if c.2.2.2 = effectiveHkdfSalt32 salt then c else
        ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
          h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
            effectiveHkdfSalt32 salt))) = c' := by
      simp only [hsalt, ↓reduceIte]; exact hc'_eq_g
    have hc_ne_c' : decide (c ≠ c') = true :=
      decide_eq_true (fun h_eq => hsalt (congrArg (fun z : Fig8C Pt => z.2.2.2) h_eq))
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Bool.true_and, Option.isNone_some, hlen, Bool.not_true, Bool.false_and,
      hparse, haddrs, Bool.not_eq_true', hspqr, hpan, hhonC, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej, hsalt_if]
    unfold fwdCPure deliverPure onAcceptPure
    simp only [hc_ne_c', hsafe, Bool.not_false, Bool.and_self, ↓reduceIte, heval,
      hmeta.hwin_fig8, Bool.false_eq_true, hr_fig8, hfig, SM.Config.h1, Bool.false_and,
      hpos_fig8, hmeta.hchall_fig8, htr_mir]
    rfl
  have hstepC : ∀ k,
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
      pure (ans, ((sC', s_fig8', false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep
      k Q w (sC, s_fig8, false) ec hcx.hsim.hec (huse k) (hstops k) _ hstepC_res hmir_ep
  have hrem_le : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir := by
    unfold remWin; rw [winCount_accept_of_le sC.base.mir Q () pos hpos_le_epQ]
  have hkept' : KeptInv P Dh encPt encT idOf lam sC' s_fig8' :=
    keptInv_recv_accept hcx.hkept Q (hcx.hsim.hst_id Q) c st' (g.epoch, i, pm) hfig rfl rfl
  have hold : c.1.1 ≤ (s_fig8.st Q).tcur := by rw [← hg_ep_eq]; exact hg_ep_tcur
  have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp :=
    epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _
      hcx.hsync Q c st' (g.epoch, i, pm) hfig hold rfl (fun hw => hw) (fun _ hwc => hwc)
  have hcx' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
      s_R' sC' s_fig8' ec winBefore epExp := by
    subst hst'_eq
    exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8
      ec winBefore epExp hcx Q ci g i pq' hg_elem v' hsync' pos hpos_ep hpq' s' rfl s_fig8' rfl
      s_R' rfl kept' hkept' hsync8'
  have hinv' : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R'
      (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
      (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' ec winBefore epExp :=
    simInvCXTrack_of_deliver_step P K Inv ℓ Dh encPt encT idOf lam qep q r (r - 1) x₀ Q w ans
      s_R s_R' stTrR sC sC' trC s_fig8 s_fig8' ec ec winBefore winBefore epExp epExp hinv hcx' rfl
  exact closeByStateCTrack_deliver_const_rc_same_amb P K ℓ Dh encPt encT decT idOf lam qep q δ
    post Q w cont s_R s_R' stTrR sC sC' trC s_fig8 s_fig8' false false ec ec winBefore ans hstepR
    (hstepC none) (fun idx _ => hstepC (some idx)) rfl hrem_le
    (ih ans s_R' (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
      (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' false ec winBefore epExp hinv')

theorem closeByStateCTrack_deliver_known_resync {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
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
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some ev)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hspec := KeptInv.evalCK_spec P Inv Dh encPt encT idOf lam qep q r hX hDh hid x₀ s_R sC
    s_fig8 ec winBefore epExp hinv.hcx hinv.hcx.hsim.hmeta.hwin_fig8 Q w c
    (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) hc_mem hc_sender (by rw [htr_mir]; rfl) rfl
    rfl rfl
  rcases ev with _ | x
  · exact closeByStateCTrack_deliver_known_resync_reject P K Inv ℓ Dh hDh encPt encT decT idOf hX
      hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R stTrR sC trC
      s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan
      hfind hrej hsalt hsafe heval (hspec.1 heval) (fun x hx => by cases hx) ih
  · rcases hspec.2 x heval with ⟨st', hfig', pm, hfig⟩ | ⟨hfig', hfig⟩
    · exact closeByStateCTrack_deliver_known_resync_accept P K Inv ℓ Dh hDh encPt encT decT idOf hX
        hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R stTrR sC trC
        s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr
        hpan hfind hrej hsalt hsafe heval hfig' hfig ih
    · exact closeByStateCTrack_deliver_known_resync_reject P K Inv ℓ Dh hDh encPt encT decT idOf hX
        hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R stTrR sC trC
        s_fig8 ec winBefore epExp hinv htr_mir c hc_mem hc_sender hhonC hlen hparse haddrs hspqr
        hpan hfind hrej hsalt hsafe heval hfig' (fun _ _ => hfig) ih

private theorem dksms_fwdCPure_false_honest_irrel_track (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt))
    (c' : Fig8C Pt) (x : JointC PQ Pt ℓ) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' x := by
  unfold fwdCPure
  cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem closeByStateCTrack_deliver_known_saltMismatch_safe {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
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
    (hsafe : sC.base.mir.safeInj 3 = true)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hcx := hinv.hcx
  have hmeta := hcx.hsim.hmeta
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hcx.hsim.hpqInv Q) hspqr
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hcx.huniq
    (fun wc hwc => ⟨(hcx.hsim.hhon wc hwc).1, (hcx.hsim.hhon wc hwc).2.1⟩)
    (fun rec_f hrec_f => ⟨(hcx.hsim.htrans_hon rec_f hrec_f).1,
      (hcx.hsim.htrans_hon rec_f hrec_f).2.1⟩)
    hcx.hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC₀, _⟩
  have hc₀_eq : c₀ = c := Option.some.inj (hhonC₀.symm.trans hhonC)
  rw [hc₀_eq] at hr_fig8
  rcases hcx.hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨_, hsrk, hctr, _⟩
  have hdecT : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hdecT, Option.map_some, Option.getD_some, hsrk]
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hcx.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, v, hvR, _⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hsrk_g : h.senderRatchetKey = encT (Dh.dh (epExp g.epoch) Dh.base) :=
    Option.some.inj hg_key_sync
  have hg_le_M : g.epoch ≤ M := by
    have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
      refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
    cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
  have hg_ep_eq : g.epoch = c.1.1 :=
    hcx.hsim.hcoll g.epoch c.1.1 hg_le_M hc_le_M (hinj (hsrk_g.symm.trans hsrk))
  let i := h.counter.toNat + 1
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt :=
    ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  let pos : SM.Pos := ⟨Q.other, g.epoch, i⟩
  have hpos_mir : r_mir.pos = pos := by
    have hr_mem : r_fig8 ∈ s_fig8.trans := List.mem_of_find?_eq_some hr_fig8
    have hr_pred := List.find?_some hr_fig8
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
    rcases hcx.hsim.htrans_hon r_fig8 hr_mem with ⟨_, hs_f, hep_f, hidx_f⟩
    rw [hr_pred.2] at hs_f hep_f hidx_f
    rw [← hpos_fig8]
    cases hp : r_fig8.pos
    rw [hp] at hs_f hep_f hidx_f
    dsimp only at hs_f hep_f hidx_f
    dsimp only [pos, i]
    rw [hs_f, hc_sender, hep_f, ← hg_ep_eq, hidx_f, ← hctr]
  have hc'_not_honest : ∀ wc ∈ sC.base.honest, wc.2 ≠ c' := by
    intro wc hwc hwc_eq
    have ht : wc.2.1.1 = c.1.1 := by rw [hwc_eq]; exact hg_ep_eq
    have hi : wc.2.2.1 = c.2.1 := by rw [hwc_eq]; exact hctr
    have hwc_c : wc = (w, c) := hcx.huniq wc hwc (w, c) hc_mem ht hi
    have hc_eq_c' : c = c' := (congrArg Prod.snd hwc_c).symm.trans hwc_eq
    exact hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) hc_eq_c')
  have hany_f : sC.base.honest.any
      (fun wc => decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome) = false := by
    rw [List.any_eq_false]; intro wc hwc; simp [hc'_not_honest wc hwc]
  have hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
      sC.base Q c' s_fig8 =
      injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 Q c'
        s_fig8 := by
    unfold fwdPure; rw [hany_f]; rfl
  have htr_fig8_c' : (s_fig8.inTransit Q.other c').isSome = false := by
    cases htr : s_fig8.inTransit Q.other c' with
    | none => rfl
    | some r_f =>
      exfalso
      have hr_mem : r_f ∈ s_fig8.trans := List.mem_of_find?_eq_some htr
      have hr_pred := List.find?_some htr
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
      exact hc'_not_honest (LibsignalSim.toWire r_f.ct, r_f.ct)
        (hcx.hsim.htrans_hon r_f hr_mem).1 hr_pred.2
  have hguard_fig8 :
      (s_fig8.win || (s_fig8.inTransit Q.other c').isSome || !(s_fig8.safeInj 3)) = false := by
    rw [hmeta.hwin_fig8, htr_fig8_c', hmeta.safeInj_fig8, hsafe]; rfl
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false := by
    intro k; unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind]
  let mir' := sC.base.mir.accept Q () pos
  have hmir_ep : mir'.epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hg_ep_le
  have hmir_idx : mir'.idx = sC.base.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
    hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hcx.hsim Q w hlen h body
    hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT mir' hmir_ep hmir_idx rc
  let c_mk : Fig8C Pt :=
    match (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
        (·.2) with
    | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else
        ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    | none => ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  have hmkC : c_mk = c' := by simp only [c_mk, c', hhonC, hsalt, ↓reduceIte]
  have htr_isNone_f : (sC.base.mir.inTransit Q.other w).isNone = false := by rw [htr_mir]; rfl
  have hstepC_eq : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true (some ci) h.senderRatchetKey pq'
        none c' (sC, s_fig8, false) := by
    rw [simRecvStepC_eq_gen_false P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false)
      (Or.inr hsafe)]
    unfold simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_isNone_f, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.not_true, Bool.true_and, hlen, hparse, haddrs, hspqr, hpan, hfind, hrej]
    rw [dksms_fwdCPure_false_honest_irrel_track]
    change fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true (some ci) h.senderRatchetKey pq'
      none c_mk (sC, s_fig8, false) = _
    rw [hmkC]
  have hstep_sim_eq : ∀ k,
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
        (let z := fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
                    SM.Config.h1 sC.base Q c' s_fig8
         let a := onAnswerPure qep Q w true (some ci) h.senderRatchetKey pq' z.1 sC.base
         (a.1, (a.2, z.2))) := by
    intro k; unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_isNone_f, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.not_true, Bool.true_and, hlen, hparse, haddrs, hspqr, hpan, hfind, hrej]
    change (let z := fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
                      SM.Config.h1 sC.base Q c_mk s_fig8
            let a := onAnswerPure qep Q w true (some ci) h.senderRatchetKey pq' z.1 sC.base
            (a.1, (a.2, z.2))) = _
    rw [hmkC]
  cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' with
  | none =>
    have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 Q c' s_fig8 = (some .rejected, s_fig8) := by
      unfold injectPure; simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig]
    refine closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
      post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir
      (fun rc => by
        have h2 := (hstep_all rc).2 hrej; dsimp only at h2
        change (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none
          at hfig
        rw [hfig] at h2; exact h2)
      huse
      (fun k => by rw [hstep_sim_eq k, hfwd, hinj_fig8]; rfl)
      (by rw [hstepC_eq]; unfold fwdCPure; dsimp only; rw [hfwd, hinj_fig8]; rfl)
      ih
  | some res_fig =>
    rcases res_fig with ⟨st', t', i', pub, m⟩
    have hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
        some (st', t', i', pub, m) := hfig
    have h2_0 := (hstep_all 0).2 hrej; dsimp only at h2_0; rw [hfig'] at h2_0
    rcases h2_0 with ⟨ht', hi', _, ⟨v', hst', hsync'⟩, _, _, _⟩
    subst ht' hi'
    have hnot_gt : ¬ (qep + 1 < g.epoch) := by have := hcx.hsim.hep_le Q; omega
    have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < g.epoch) := by omega
    by_cases htriv : sC.base.mir.trivial 3 pos = true
    · let s' : SimState PQ Pt ℓ :=
        { sC.base with
          mir := mir',
          pq := Function.update sC.base.pq Q pq',
          unackA := sC.base.unackA && Q != Party.A,
          chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
      let kept' := Function.update sC.kept Q
        (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s', kept := kept' }
      let s_fig8' := s_fig8.accept Q st' pos
      let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
      let s_R' := s_R.accept Q st_R' pos
      let ans : Option (RecvResult (Plain ℓ)) :=
        some (.accepted g.epoch i (if sC.base.mir.chall.contains pos then none else some m))
      have htriv_fig8 : s_fig8.trivial 3 pos = true := by rw [hmeta.trivial_fig8, htriv]
      have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c' s_fig8 =
          (some (.accepted g.epoch i (some (pub, m))), s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig',
          show ¬ (qep + 1 + 1 < ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch)
            from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch,
            h.counter.toNat + 1⟩ = true from htriv_fig8]
        rfl
      have hstep_sim : ∀ k,
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
            (ans, (s', s_fig8')) := by
        intro k; rw [hstep_sim_eq k, hfwd, hinj_fig8]
        unfold onAnswerPure onAcceptPure
        simp only [↓reduceIte, htr_mir, hpos_mir, Option.map_some, Option.getD_some]; rfl
      have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (ans, (sC', s_fig8', false)) := by
        rw [hstepC_eq]; unfold fwdCPure; dsimp only; rw [hfwd, hinj_fig8]
        unfold onAnswerPure onAcceptPure
        simp only [↓reduceIte, htr_mir, hpos_mir, Option.map_some, Option.getD_some]; rfl
      have hstepC : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k
          (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
          pure (ans, ((sC', s_fig8', false), ec)) := fun k =>
        stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
          (sC, s_fig8, false) ec hcx.hsim.hec (huse k)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true
            (sC.base, s_fig8) (by rw [hstep_sim k]; exact hmeta.hstop))
          _ hresC hmir_ep
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')) := by
        rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
        congr 1; funext rc
        have h2_rc := (hstep_all rc).2 hrej; dsimp only at h2_rc; rw [hfig'] at h2_rc
        rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
        rw [hrec_rc]; dsimp only; rw [← hm_raw, hpos_R, hmeta.hchall_R, hpos_mir]
      have hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir := by
        unfold remWin; rw [winCount_accept_of_le sC.base.mir Q () pos hg_ep_le]
      have hold : g.epoch ≤ (s_fig8.st Q).tcur := ((hcx.hkept.hvR Q g.epoch).mp (by simp [hvR])).1
      have hkept' : KeptInv P Dh encPt encT idOf lam sC' s_fig8' :=
        keptInv_recv_accept hcx.hkept Q (hcx.hsim.hst_id Q) c' st' _ hfig' rfl rfl
      have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp :=
        epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _ hcx.hsync Q c' st' _ hfig' hold rfl
          (fun hw => hw) (fun _ hwc => hwc)
      have hcx' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec
          winBefore epExp := by
        subst hst'
        exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8
          ec winBefore epExp hcx Q ci g i pq' hg_elem v' hsync' pos rfl hpq' s' rfl s_fig8' rfl
          s_R' rfl kept' hkept' hsync8'
      have hinv' : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R'
          (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
          (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' ec winBefore epExp :=
        simInvCXTrack_of_deliver_step P K Inv ℓ Dh encPt encT idOf lam qep q r (r - 1) x₀ Q w ans
          s_R s_R' stTrR sC sC' trC s_fig8 s_fig8' ec ec winBefore winBefore epExp epExp hinv hcx'
          rfl
      exact closeByStateCTrack_deliver_const_rc_same_amb P K ℓ Dh encPt encT decT idOf lam qep q
        δ post Q w cont s_R s_R' stTrR sC sC' trC s_fig8 s_fig8' false false ec ec winBefore ans
        hstepR (hstepC none) (fun idx _ => hstepC (some idx)) rfl hrem
        (ih _ s_R' (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
          (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' false ec winBefore epExp
          hinv')
    · have htriv_f : sC.base.mir.trivial 3 pos = false := Bool.eq_false_iff.mpr htriv
      have htriv_fig8 : s_fig8.trivial 3 pos = false := by rw [hmeta.trivial_fig8, htriv_f]
      let s_fig8' := { s_fig8 with win := true }
      have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c' s_fig8 = (some .rejected, s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig',
          show ¬ (qep + 1 + 1 < ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch)
            from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch,
            h.counter.toNat + 1⟩ = false from htriv_fig8]
        rfl
      have hstep_sim_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8) =
            (some .rejected, (sC.base, s_fig8')) := by
        rw [hstep_sim_eq none, hfwd, hinj_fig8]; rfl
      have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true
          (sC, s_fig8, false) = (some .rejected, (sC, s_fig8', false)) := by
        rw [hstepC_eq]; unfold fwdCPure; dsimp only; rw [hfwd, hinj_fig8]; rfl
      have hSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
          (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
          pure (some .rejected, ((sC, s_fig8', false), ec)) :=
        stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hcx.hsim.hec (huse none)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true
            (sC.base, s_fig8) (by rw [hstep_sim_none]; exact hmeta.hstop))
          _ hresC rfl
      exact closeByStateCTrack_deliver_fig8_win P K ℓ Dh encPt encT decT idOf lam qep q δ post Q
        w cont s_R stTrR sC sC trC s_fig8 s_fig8' false false ec ec winBefore (some .rejected) hSim
        rfl

end DeliverKnown

end CryptoGames.LibsignalSM.Proofs.Refinement
