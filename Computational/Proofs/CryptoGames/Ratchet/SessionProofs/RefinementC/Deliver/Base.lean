/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv

/-!
# Deliver step of the C coupling: base lemmas and early cases

Reduction of `stepSimCEager` on non-stopping `deliver` calls to `simRecvStepC`, along with
state-preserving rejection combinators and the out-of-transit, SPQR-panic, and SPQR-error cases.
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

theorem stepSimCEager_deliver_of_not_stops_core (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (huse' : (simRecvUsesCoin P encT decT k Q w true x.sim && !recvPanicsW P Q w x.1.base) =
      false)
    (hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim = false)
    (hev : evictStopsC P encT decT k Q w true x = false) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      (let res := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true x
       updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
         pure (res.1, (res.2, ec'))) := by
  change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
  unfold stepSimCEagerDeliver
  simp only [huse', hev, Bool.false_eq_true, ↓reduceIte]
  change (if simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim then _
    else stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x) >>= _ = _
  simp only [hstops, Bool.false_eq_true, ↓reduceIte]
  rw [stepSimCNone_deliver_eq, pure_bind]

theorem stepSimCEager_deliver_of_not_stops (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (huse : simRecvUsesCoin P encT decT k Q w true x.sim = false)
    (hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim = false)
    (hev : evictStopsC P encT decT k Q w true x = false := by evict_stops_tac) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      (let res := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true x
       updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
         pure (res.1, (res.2, ec'))) :=
  stepSimCEager_deliver_of_not_stops_core P ℓ Dh encPt encT decT idOf lam qep k Q w x ec
    (by rw [huse, Bool.false_and]) hstops hev

theorem stepSimCEager_deliver_of_not_stops_same_epoch (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hec : ValidEagerCoins x.1.base.mir ec)
    (huse : simRecvUsesCoin P encT decT k Q w true x.sim = false)
    (hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim = false)
    (res : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ)
    (hres : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true x = res)
    (hep : res.2.1.base.mir.epoch = x.1.base.mir.epoch)
    (hev : evictStopsC P encT decT k Q w true x = false := by evict_stops_tac) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      pure (res.1, (res.2, ec)) := by
  rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w x ec huse
    hstops hev]
  dsimp only
  rw [hres]
  have hA : inReceiveOnlyEpoch res.2.1.base.mir .A = inReceiveOnlyEpoch x.1.base.mir .A := by simp [inReceiveOnlyEpoch, hep]
  have hB : inReceiveOnlyEpoch res.2.1.base.mir .B = inReceiveOnlyEpoch x.1.base.mir .B := by simp [inReceiveOnlyEpoch, hep]
  rw [updateAllEagerCoins_same_inWin x.1.base.mir res.2.1.base.mir ec hA hB hec, pure_bind]

theorem stepSimCEager_deliver_of_recvPanics (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hec : ValidEagerCoins x.1.base.mir ec)
    (hpanW : recvPanicsW P Q w x.1.base = true)
    (hres : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true x = (some .rejected, x)) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      pure (some .rejected, (x, ec)) := by
  rw [stepSimCEager_deliver_of_not_stops_core P ℓ Dh encPt encT decT idOf lam qep k Q w x ec
    (by rw [hpanW, Bool.not_true, Bool.and_false])
    (simRecvStops_of_recvPanicsW P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim hpanW)
    (evictStopsC_of_recvPanicsW P encT decT k Q w true x hpanW)]
  dsimp only
  rw [hres]
  rw [updateAllEagerCoins_same_inWin x.1.base.mir x.1.base.mir ec rfl rfl hec, pure_bind]

theorem closeByStateC_deliver_reject_of_step {α : Type} (P : Params PQ PQC)
    (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)))
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
    hstepR (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
    (ih (some .rejected) s_R sC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))

/-- Closes a `deliver` step when both R and the C side reject without modifying state. -/
theorem closeByStateC_deliver_reject_same {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)))
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
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep true k Q w true _ _ hresC rfl)
  exact closeByStateC_deliver_reject_of_step P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hrcv hstep ih

theorem closeByStateC_deliver_spqr_panic {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true)
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
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpanW : recvPanicsW P Q w sC.base = true :=
    recvPanicsW_eq_true_of P Q w sC.base hlen hparse haddrs hpan
  have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)) := by
    unfold simRecvStepC simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hpan]
  exact closeByStateC_deliver_reject_of_step P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir
    (fun rc => receive_eq_none_of_spqr_panic P Q (s_R.st Q) hparty w hlen h body hparse
      (by rw [hpq]; exact hpan) rc)
    (fun k => stepSimCEager_deliver_of_recvPanics P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hsim.hec hpanW hresC)
    ih

theorem closeByStateC_deliver_not_inTransit {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (htr_mir : sC.base.mir.inTransit Q.other w = none)
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
  have htr_R : s_R.inTransit Q.other w = none :=
    Option.isNone_iff_eq_none.mp (by rw [hmeta.inTransit_R_isNone Q.other w, htr_mir]; rfl)
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
  have hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
      (none, (sC.base, s_fig8)) := by
    intro k
    unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
  have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (none, (sC, s_fig8, false)) := by
    unfold simRecvStepC simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (none, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep true k Q w true _ _ hresC rfl)
  exact closeByStateC_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore none
    (stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R)
    (stepR_deliver_R1Inj_none P ℓ encPt decT encT lam qep Q w s_R hmeta.hwin_R htr_R)
    (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
    (ih none s_R sC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))

theorem closeByStateC_deliver_spqr_error {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {e_pq : Bool}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .error e_pq)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
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
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  refine closeByStateC_deliver_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
    cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir
    (fun rc => receive_eq_none_of_spqr_error P Q (s_R.st Q) hparty w hlen h body hparse e_pq
      (by rw [hpq]; exact hspqr) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan])
    (fun k => by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan])
    (by
      unfold simRecvStepC simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan])
    ih

end CryptoGames.LibsignalSM.Proofs.Refinement
