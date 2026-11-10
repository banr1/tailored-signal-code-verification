/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted base and known-chain `deliver` lemmas

Shared `CloseByStateCTrack` combinators for `deliver` queries, `SimInvCXTrack` and `win`
preservation lemmas, and the base and early known-chain `deliver` cases.
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

section DeliverBase

variable {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]

/-- Updates the real-game `KemFailSessionTrack` on a `deliver (Q, w)` answer. -/
def stepDeliverTrR {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (stTrR : KemFailTrackBridge.KemFailSessionTrack F (List (BitVec 8)))
    (Q : Party) (w : List (BitVec 8)) (ans : Option (RecvResult (Plain ℓ))) :
    KemFailTrackBridge.KemFailSessionTrack F (List (BitVec 8)) :=
  let j? := stTrR.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
  let tr' := match ans, j? with
    | some (.accepted _ _ _), some j => KemFailTrackBridge.stepKemFailDeliver F K stTrR.1 Q j
    | _, _ => stTrR.1
  (tr', stTrR.2)

/-- Updates the simulator `KemFailTrackState` on a `deliver (Q, w)` answer. -/
def stepDeliverTrC {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (honest : List (List (BitVec 8) × Fig8C Pt))
    (trC : KemFailTrackState F) (Q : Party) (w : List (BitVec 8))
    (ans : Option (RecvResult (Plain ℓ))) : KemFailTrackState F :=
  let j? := honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
  match ans, j? with
  | some (.accepted _ _ _), some j => stepKemFailDeliver F K trC Q j
  | _, _ => trC

theorem SimInvCXTrack.mono_r {P : Params PQ (BitVec 512)} {Inv : ℕ → PQ → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {trC : KemFailTrackState P.C.F}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hr' : r' ≤ r) :
    SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp :=
  ⟨hinv.hcx.mono_r hr', hinv.htr, hinv.hhw⟩

theorem simInvCXTrack_of_deliver_step (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q r r' : ℕ) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (ans : Option (RecvResult (Plain ℓ)))
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec ec' : Party → BitVec 256) (winBefore winBefore' : ℕ → Bool)
    (epExp epExp' : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hcx' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R' sC' s_fig8' ec' winBefore'
      epExp')
    (hhon : sC'.base.honest = sC.base.honest) :
    SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
      (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
      (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' ec' winBefore' epExp' := by
  refine ⟨hcx', ?_, ?_⟩
  · dsimp only [stepDeliverTrR, stepDeliverTrC]
    rw [hinv.hhw, honestWiresOf_reverse_findIdx_eq, hinv.htr]
    cases ans with
    | none => rfl
    | some rr =>
      cases rr with
      | rejected => rfl
      | accepted t i m =>
        cases sC.base.honest.reverse.findIdx? _ with
        | none => rfl
        | some j => exact (ofRefTrack_stepDeliver P.C.F K trC Q j).symm
  · dsimp only [stepDeliverTrR]
    rw [hinv.hhw, hhon]

private lemma list_beq_eq_dec_beq (a b : List (BitVec 8)) :
    (instBEqOfDecidableEq.beq a b) = (a == b) := by
  by_cases h : a = b <;> simp [instBEqOfDecidableEq, h]

theorem stepRTrack_deliver_eq_stepDeliverTrR (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (qep : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (w : List (BitVec 8))
    (s : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8))) :
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg
      (.inl (.inl (.inr (Q, w)))) s stTrR =
      (do
        let res_s ← stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg
          (.inl (.inl (.inr (Q, w)))) s
        pure (res_s, stepDeliverTrR P.C.F K stTrR Q w res_s.1)) := by
  rw [stepRTrack_deliver_eq]
  congr 1; funext res_s
  dsimp only [stepDeliverTrR]
  have hj : List.findIdx?
      (fun wp => (instBEqOfDecidableEq.beq wp.1 w) && (instBEqOfDecidableEq.beq wp.2 Q.other))
      stTrR.2.reverse =
      List.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) stTrR.2.reverse := by
    congr 1; funext wp
    rw [list_beq_eq_dec_beq]
  rw [hj]
  rcases res_s with ⟨ans, s'⟩
  cases ans with
  | none => rfl
  | some rr =>
    cases rr <;> cases List.findIdx? _ _ <;> rfl

theorem stepSimCEagerTrack_deliver_of_pure (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x x' : JointC PQ Pt ℓ) (trC : KemFailTrackState P.C.F) (ec ec' : Party → BitVec 256)
    (ans : Option (RecvResult (Plain ℓ)))
    (hstep : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      pure (ans, (x', ec'))) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x trC ec =
      pure (ans, ((x', stepDeliverTrC P.C.F K x.1.base.honest trC Q w ans), ec')) := by
  change stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x trC ec = _
  rw [stepSimCEagerDeliverTrack]
  change (do
    let res ← stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec
    _) = _
  rw [hstep, pure_bind]
  dsimp only [stepDeliverTrC]
  cases ans with
  | none => rfl
  | some rr =>
    cases rr <;> cases List.findIdx? _ _ <;> rfl

theorem stepSimCEagerSendTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep none Q m₀ chal r
        x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz
  unfold stepSimCEagerSendTrack at hz
  have hcond : ((!x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q) &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q))) =
      false := by simp [hwin]
  rw [hcond] at hz
  simp only [Bool.false_eq_true, ↓reduceIte] at hz
  simp only [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨z₀, hz₀, hz⟩
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hw₀ : z₀.2.win = true :=
    simulateQ_run_preserve (SM.oracleImpl fig (2 + 1) (qep + 1) SM.Config.h1)
      (fun s => s.win = true)
      (fun q' s hs => oracleImpl_run_of_win_true fig (2 + 1) (qep + 1) SM.Config.h1 q' s hs)
      _ x.2.1 hwin z₀ hz₀
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hw₀
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hw₀

theorem stepSimCEagerTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q x tr ec),
      z.2.1.1.2.1.win = true := by
  rcases q with (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · exact stepSimCEagerSendTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep Q m none
      rc x tr ec hwin
  · exact stepSimCEagerSendTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep Q m₀
      (some m₁) rc x tr ec hwin
  · intro z hz
    simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inl (.inr (Q, w)))) x ec hwin res hres
  · intro z hz
    simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inr (Q, w))) x ec hwin res hres
  · intro z hz
    simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep
      (.inr Q) x ec hwin res hres

theorem evalDist_runWinAtCTrack_zero_of_win_true {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) (hwin : x.2.1.win = true) :
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep oa x tr ec winBefore 0] {true} = 1 := by
  unfold runWinAtCTrack runSimCEagerTrack
  refine Construction.AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := simulateQ_run_preserve (simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.1.2.1.win = true)
    (fun q s hs z hz => stepSimCEagerTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep
      q s.1.1 s.1.2 s.2 hs z hz) oa ((x, tr), ec) hwin z hz
  simp [h]

theorem closeByStateCTrack_deliver_fig8_win {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : Option (RecvResult (Plain ℓ)))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, fl) ec = pure (ans, ((sC', s_fig8', fl'), ec')))
    (hwin : s_fig8'.win = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  have htrack := stepSimCEagerTrack_deliver_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w
    (sC, s_fig8, fl) (sC', s_fig8', fl') trC ec ec' ans hstepSim
  refine closeByRefinesH_of_win_eq_one (Finset.mem_range.mpr (Nat.zero_lt_succ q)) ?_
  have hw0 : runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      (sC, s_fig8, fl) trC ec winBefore 0 =
      runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont ans)
        (sC', s_fig8', fl') (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) ec' winBefore 0 := by
    simp only [runWinAtCTrack, runSimCEagerTrack_inr_bind, htrack, pure_bind]
  rw [hw0]
  exact evalDist_runWinAtCTrack_zero_of_win_true P K ℓ Dh encPt encT decT idOf lam qep (cont ans)
    (sC', s_fig8', fl') (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) ec' winBefore hwin

theorem closeByStateCTrack_deliver_const_rc_same_amb {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : Option (RecvResult (Plain ℓ)))
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx)
        (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, fl) ec =
        pure (ans, ((sC', s_fig8', fl'), ec')))
    (hamb : sC'.base.amb = sC.base.amb)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
      s_R' (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
      (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' fl' ec' winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  have hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R stTrR := by
    rw [stepRTrack_deliver_eq, stepRTrack_deliver_eq,
      stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R]
  have hR' : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
        pure ((ans, s_R'), stepDeliverTrR P.C.F K stTrR Q w ans)) := by
    rw [stepRTrack_deliver_eq_stepDeliverTrR, hstepR, bind_assoc]
    rfl
  exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R s_R' stTrR (stepDeliverTrR P.C.F K stTrR Q w ans) sC sC'
    trC (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8 s_fig8' fl fl' ec ec' winBefore
    ($ᵗ BitVec 256 : ProbComp (BitVec 256)) ans hD0 hR'
    (stepSimCEagerTrack_deliver_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, fl) (sC', s_fig8', fl') trC ec ec' ans hstepSim)
    (fun idx hni => stepSimCEagerTrack_deliver_of_pure P K ℓ Dh encPt encT decT idOf lam qep
      (some idx) Q w (sC, s_fig8, fl) (sC', s_fig8', fl') trC ec ec' ans (hstepWin idx hni))
    hamb hrem hcont

theorem closeByStateCTrack_deliver_of_fl_step {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hset : ∀ z ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, fl) ec),
      z.2.1.2.2 = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  refine closeByStateCTrack_inr_of_fl_step P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R stTrR sC trC s_fig8 fl ec winBefore ?_
  intro z hz
  simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
  rcases hz with ⟨res, hres, rfl⟩
  exact hset res hres

theorem closeByStateCTrack_deliver_reject_of_step {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)))
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
  have hmeta := hinv.hcx.hsim.hmeta
  have hR_map := hmeta.inTransit_R_map Q.other w
  rw [htr_mir, Option.map_some] at hR_map
  rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, htr_R, _⟩
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
    rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R htr_R]
    congr 1; funext rc
    rw [hrcv rc]
  exact closeByStateCTrack_deliver_const_rc_same_amb P K ℓ Dh encPt encT decT idOf lam qep q δ post
    Q w cont s_R s_R stTrR sC sC trC s_fig8 s_fig8 false false ec ec winBefore (some .rejected)
    hstepR (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
    (ih (some .rejected) s_R stTrR sC trC s_fig8 false ec winBefore epExp
      (hinv.mono_r (Nat.sub_le r 1)))

theorem closeByStateCTrack_deliver_reject_same {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)))
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
  have hmeta := hinv.hcx.hsim.hmeta
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep true k Q w true _ _ hresC rfl)
  exact closeByStateCTrack_deliver_reject_of_step P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
    post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hrcv hstep ih

theorem closeByStateCTrack_deliver_spqr_panic {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true)
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
  have hmeta := hinv.hcx.hsim.hmeta
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q)
      (ec Q)
  have hpanW : recvPanicsW P Q w sC.base = true :=
    recvPanicsW_eq_true_of P Q w sC.base hlen hparse haddrs hpan
  have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)) := by
    unfold simRecvStepC simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hpan]
  exact closeByStateCTrack_deliver_reject_of_step P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
    post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir
    (fun rc => receive_eq_none_of_spqr_panic P Q (s_R.st Q) hparty w hlen h body hparse
      (by rw [hpq]; exact hpan) rc)
    (fun k => stepSimCEager_deliver_of_recvPanics P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hcx.hsim.hec hpanW hresC)
    ih

theorem closeByStateCTrack_deliver_not_inTransit {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (htr_mir : sC.base.mir.inTransit Q.other w = none)
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
  have hmeta := hinv.hcx.hsim.hmeta
  have htr_R : s_R.inTransit Q.other w = none :=
    Option.isNone_iff_eq_none.mp (by rw [hmeta.inTransit_R_isNone Q.other w, htr_mir]; rfl)
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false := by
    intro k; unfold simRecvUsesCoin; simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
  have hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
      (none, (sC.base, s_fig8)) := by
    intro k; unfold simRecvStep; simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
  have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (none, (sC, s_fig8, false)) := by
    unfold simRecvStepC simRecvStepCGen; simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (none, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep true k Q w true _ _ hresC rfl)
  have hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R stTrR := by
    rw [stepRTrack_deliver_eq, stepRTrack_deliver_eq,
      stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R]
  have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      pure ((none, s_R), stTrR) := by
    rw [stepRTrack_deliver_eq_stepDeliverTrR,
      stepR_deliver_R1Inj_none P ℓ encPt decT encT lam qep Q w s_R hmeta.hwin_R htr_R, pure_bind]
    rfl
  exact closeByStateCTrack_inr_same_amb_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec
    ec winBefore none hD0 hstepR
    (stepSimCEagerTrack_deliver_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) (sC, s_fig8, false) trC ec ec none (hstep none))
    (fun idx hni => stepSimCEagerTrack_deliver_of_pure P K ℓ Dh encPt encT decT idOf lam qep
      (some idx) Q w (sC, s_fig8, false) (sC, s_fig8, false) trC ec ec none (hstep (some idx)))
    rfl le_rfl
    (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))

theorem closeByStateCTrack_deliver_spqr_error {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {e_pq : Bool}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .error e_pq)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
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
  have hmeta := hinv.hcx.hsim.hmeta
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q)
      (ec Q)
  refine closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir
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

theorem closeByStateCTrack_deliver_known_rejects {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
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
    (hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true)
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
  have hmeta := hinv.hcx.hsim.hmeta
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp
    (hinv.hcx.hsim.hhon (w, c) hc_mem).1 hparse with ⟨_, hsrk, _, _⟩
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hsrk, hdec, Option.map_some, Option.getD_some]
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc =>
    (receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT hinj idOf lam hid qep q r
      x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim Q w hlen h body hparse haddrs pq' salt
      hspqr hpan ci hfind (decT h.senderRatchetKey) hT sC.base.mir rfl rfl rc).1 hrej
  refine closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hrcv
    (fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC
      hc_sender)
    (fun k => ?_) ?_ ih
  · unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hlen, hparse, haddrs,
      Bool.not_true, hspqr, hpan, hfind, hrej]
  · unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Bool.false_eq_true, ↓reduceIte,
      Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hlen, hparse, haddrs,
      Bool.not_true, hspqr, hpan, hfind, hrej]

private theorem dksm_fwdCPure_self_track (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (x : JointC PQ Pt ℓ) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel ci? T pq' (some c) c x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c x := by
  unfold fwdCPure
  simp

theorem closeByStateCTrack_deliver_known_saltMatch {α : Type} (P : Params PQ (BitVec 512))
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
    (hsalt : c.2.2.2 = effectiveHkdfSalt32 salt)
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
    (fun r hr => ⟨(hcx.hsim.htrans_hon r hr).1, (hcx.hsim.htrans_hon r hr).2.1⟩)
    hcx.hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC₀, hfwd_eq⟩
  have hc₀_eq : c₀ = c := Option.some.inj (hhonC₀.symm.trans hhonC)
  subst c₀
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hcx.hsim.hhon (w, c) hc_mem).1
    hparse with ⟨_, hsrk, hctr, hc_raw⟩
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hcx.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, v, hvR, hsync⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hsrk_eq : h.senderRatchetKey = encT (Dh.dh (epExp g.epoch) Dh.base) :=
    Option.some.inj hg_key_sync
  have hdh : Dh.dh (epExp g.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
    hinj (hsrk_eq.symm.trans hsrk)
  have hle_g : g.epoch ≤ M := by
    have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
      refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
    cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
  have hg_ep_eq : g.epoch = c.1.1 :=
    hcx.hsim.hcoll g.epoch c.1.1 hle_g (hcx.hsim.hhon (w, c) hc_mem).2.1 hdh
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
  let i := h.counter.toNat + 1
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  have hc_eq_g : ((g.epoch, decT h.senderRatchetKey),
      (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
    rw [hg_ep_eq, hT_dec, ← hsalt]
    exact hc_raw.symm
  have hpos_mir_ep : r_mir.pos.epoch = g.epoch := by
    rw [← hpos_fig8, hg_ep_eq]
    exact inTransit_fig8_pos_epoch_eq hcx.hsim.htrans_hon hr_fig8
  have hpos_le_epQ : r_mir.pos.epoch ≤ sC.base.mir.epoch Q := by
    rw [hpos_mir_ep]; exact hg_ep_le
  let mir' := sC.base.mir.accept Q () r_mir.pos
  have hmir_ep : mir'.epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () r_mir.pos hpos_le_epQ
  have hmir_idx : mir'.idx = sC.base.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
    hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hcx.hsim Q w hlen h body
    hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT mir' hmir_ep hmir_idx rc
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC
      hc_sender
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hstep_inTransit : ∀ k,
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
        (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c s_fig8
         let a := onAnswerPure qep Q w true (some ci) h.senderRatchetKey pq' z.1 sC.base
         (a.1, (a.2, z.2))) := by
    intro k
    rw [simRecvStep_deliver_inTransit_eq P ℓ Dh encPt encT decT idOf lam qep k Q w sC.base s_fig8
      hmeta.hstop hmeta.hwin_mir r_mir htr_mir hlen h body hparse haddrs c pq' salt hspqr
      hsalt.symm hhonC]
    simp only [hfind, hrej, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hgenC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true (some ci) h.senderRatchetKey pq'
        none c (sC, s_fig8, false) := by
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
      Bool.not_true, Bool.false_and, hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs,
      hspqr, hpan, hhonC, hsalt, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej]
    exact dksm_fwdCPure_self_track P ℓ Dh encPt encT idOf lam qep Q w true (some ci)
      h.senderRatchetKey pq' c (sC, s_fig8, false)
  cases hfig : sm.receive (s_fig8.st Q) c with
  | none =>
    have hdel_fig8 : deliverPure sm SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
      unfold deliverPure
      simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig, SM.Config.h1,
        Bool.false_and]
    refine closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
      post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir
      (fun rc => by
        have h2 := (hstep_all rc).2 hrej
        dsimp only at h2
        rw [hc_eq_g, hfig] at h2
        exact h2)
      huse
      (fun k => by
        rw [hstep_inTransit k, hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
        rfl)
      (by
        rw [hgenC]
        unfold fwdCPure
        dsimp only
        rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
        rfl)
      ih
  | some res_fig =>
    rcases res_fig with ⟨st', t', i', pub, m⟩
    have hfig' : sm.receive (s_fig8.st Q) c = some (st', t', i', pub, m) := hfig
    have h2_0 := (hstep_all 0).2 hrej
    dsimp only at h2_0
    rw [hc_eq_g, hfig'] at h2_0
    rcases h2_0 with ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw₀, hm_raw₀, _⟩
    subst ht' hi'
    let ans : Option (RecvResult (Plain ℓ)) :=
      some (.accepted g.epoch i (if sC.base.mir.chall.contains r_mir.pos then none else some m))
    let s' : SimState PQ Pt ℓ :=
      { sC.base with
        mir := mir',
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
    let kept' := Function.update sC.kept Q
      (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
    let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s', kept := kept' }
    let s_fig8' := s_fig8.accept Q st' r_mir.pos
    let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
    let s_R' := s_R.accept Q st_R' r_mir.pos
    have hdel_fig8 : deliverPure sm SM.Config.h1 Q c s_fig8 =
        (some (.accepted g.epoch i
          (if sC.base.mir.chall.contains r_mir.pos then none else some (pub, m))),
         s_fig8') := by
      unfold deliverPure
      simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig', SM.Config.h1,
        Bool.false_and, hpos_fig8, hmeta.hchall_fig8]
      rfl
    have hstep_sim : ∀ k,
        simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
          (ans, (s', s_fig8')) := by
      intro k
      rw [hstep_inTransit k, hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
      unfold onAnswerPure onAcceptPure
      simp only [htr_mir, ↓reduceIte]
      cases hch : sC.base.mir.chall.contains r_mir.pos <;>
        simp only [ans, s', mir', hch, ↓reduceIte, Bool.false_eq_true,
          Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
    have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (ans, (sC', s_fig8', false)) := by
      rw [hgenC]
      unfold fwdCPure
      dsimp only
      rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1, hdel_fig8]
      unfold onAnswerPure onAcceptPure
      simp only [htr_mir, ↓reduceIte]
      cases hch : sC.base.mir.chall.contains r_mir.pos <;>
        simp only [ans, sC', s', mir', kept', sm, hch, ↓reduceIte, Bool.false_eq_true,
          Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
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
      have h2_rc := (hstep_all rc).2 hrej
      dsimp only at h2_rc
      rw [hc_eq_g, hfig'] at h2_rc
      rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
      rw [hrec_rc]
      dsimp only
      rw [← hm_raw, hpos_R, hmeta.hchall_R]
    have hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir := by
      unfold remWin
      rw [winCount_accept_of_le sC.base.mir Q () r_mir.pos hpos_le_epQ]
    have hold : c.1.1 ≤ (s_fig8.st Q).tcur := by
      rw [← hg_ep_eq]
      exact ((hcx.hkept.hvR Q g.epoch).mp (by simp [hvR])).1
    have hkept' : KeptInv P Dh encPt encT idOf lam sC' s_fig8' :=
      keptInv_recv_accept hcx.hkept Q (hcx.hsim.hst_id Q) c st' _ hfig' rfl rfl
    have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp :=
      epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _ hcx.hsync Q c st' _ hfig' hold rfl
        (fun hw => hw) (fun _ hwc => hwc)
    have hcx' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec
        winBefore epExp := by
      subst hst'
      exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8
        ec winBefore epExp hcx Q ci g i pq' hg_elem v' hsync' r_mir.pos hpos_mir_ep hpq' s' rfl
        s_fig8' rfl s_R' rfl kept' hkept' hsync8'
    have hinv' : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R'
        (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
        (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' ec winBefore epExp :=
      simInvCXTrack_of_deliver_step P K Inv ℓ Dh encPt encT idOf lam qep q r (r - 1) x₀ Q w ans
        s_R s_R' stTrR sC sC' trC s_fig8 s_fig8' ec ec winBefore winBefore epExp epExp hinv hcx'
        rfl
    exact closeByStateCTrack_deliver_const_rc_same_amb P K ℓ Dh encPt encT decT idOf lam qep q δ
      post Q w cont s_R s_R' stTrR sC sC' trC s_fig8 s_fig8' false false ec ec winBefore ans hstepR
      (hstepC none) (fun idx _ => hstepC (some idx)) rfl hrem
      (ih ans s_R' (stepDeliverTrR P.C.F K stTrR Q w ans) sC'
        (stepDeliverTrC P.C.F K sC.base.honest trC Q w ans) s_fig8' false ec winBefore epExp hinv')

end DeliverBase

end CryptoGames.LibsignalSM.Proofs.Refinement
