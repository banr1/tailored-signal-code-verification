/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltV1
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNESplit
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNESkeleton
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Online-Halted Hidden-Salt Game Split

Reassociates `hiddenSaltGameTrackHalted` with `kemFailSimImplHalted` and splits its bad-event
probability into the sticky-dead-ghost simulations `firstNEHalted'` and `evictOnlyHalted'`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState KemFailSimM initKemFailTrack stepKemFailSend stepKemFailDeliver
   runProbeStep kemFailSendStep kemFailSimImpl deliverForgeHook SpqrCLocal badCoin_prob_le
   simRecvStepC kemFailSendStepPostCoin kemFailSendStepHalted kemFailSimImplHalted
   simSendCTrackHalted simImplCTrackHalted simRunCTrackHaltedWith
   runLibsignalToModularSchemeSimTrackHalted hiddenSaltGameTrackHalted hiddenSaltTermTrackHalted
   simDeliverForgeTrackHalted stepKemFailSend_cand_sticky)
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.HeadlineV1
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

def cleanCand {F : ShaCompress} (tr : KemFailTrackState F) : KemFailTrackState F :=
  { tr with cand := none }

@[simp]
theorem cleanCand_cand {F : ShaCompress} (tr : KemFailTrackState F) :
    (cleanCand tr).cand = none := rfl

@[simp]
theorem cleanCand_idem {F : ShaCompress} (tr : KemFailTrackState F) :
    cleanCand (cleanCand tr) = cleanCand tr := rfl

theorem cleanCand_eq_self_of_cand_eq_none {F : ShaCompress} {tr : KemFailTrackState F}
    (hc : tr.cand = none) : cleanCand tr = tr := by
  cases tr; simp [cleanCand] at hc ⊢; exact hc.symm

@[simp]
theorem initKemFailTrack_cand (F : ShaCompress) (pqrKey : BitVec 256) :
    (initKemFailTrack F pqrKey).cand = none := rfl

@[simp]
theorem cleanCand_initKemFailTrack (F : ShaCompress) (pqrKey : BitVec 256) :
    cleanCand (initKemFailTrack F pqrKey) = initKemFailTrack F pqrKey := rfl

theorem stepKemFailSend_cand_sticky_local {F : ShaCompress} (K : MlKem) (tr : KemFailTrackState F)
    (Q : Party) (rq : BitVec 512) {p : CryptoVerification.SpqrV1Sync.InSync.Seed ×
      CryptoVerification.SpqrV1Sync.Braid.EncRand} (hc : tr.cand = some p) :
    (stepKemFailSend F K tr Q rq).cand = some p := by
  unfold stepKemFailSend; cases (tr.st Q).send K (coinBytes rq) <;> simp [hc]

theorem stepKemFailDeliver_cand_eq {F : ShaCompress} (K : MlKem) (tr : KemFailTrackState F)
    (Q : Party) (j : ℕ) : (stepKemFailDeliver F K tr Q j).cand = tr.cand := by
  unfold stepKemFailDeliver
  cases h : tr.sentB[j]? with
  | none => rfl
  | some p =>
    rcases p with ⟨m, _⟩
    dsimp only
    cases hr : CryptoVerification.LibsignalSpqrV1.States.recv K (tr.st Q) m with
    | error _ => rfl
    | ok out => dsimp only; split_ifs <;> (try cases tr.c) <;> rfl

theorem cleanCand_stepKemFailDeliver {F : ShaCompress} (K : MlKem) (tr : KemFailTrackState F)
    (Q : Party) (j : ℕ) :
    cleanCand (stepKemFailDeliver F K tr Q j) = stepKemFailDeliver F K (cleanCand tr) Q j := by
  unfold cleanCand stepKemFailDeliver
  dsimp only
  cases h : tr.sentB[j]? with
  | none => rfl
  | some p =>
    rcases p with ⟨m, _⟩
    dsimp only
    cases hr : CryptoVerification.LibsignalSpqrV1.States.recv K (tr.st Q) m with
    | error _ => rfl
    | ok out => dsimp only; split_ifs <;> (try cases tr.c) <;> rfl

/-! ## Simulator state reassociation -/

set_option exponentiation.threshold 1024 in
theorem kemFailSendStepHalted_proj_eq_simSendCTrackHalted {PQ Pt : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    ((kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, gh, tr) >>=
      fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) =
    (((simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q m₀ chal r).run
      (sC, tr)).run gh) := by
  unfold kemFailSendStepHalted simSendCTrackHalted kemFailSendStepPostCoin
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  cases hstop : sC.base.stopped
  · simp only [Bool.false_or]
    cases hwin : (sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
      | none =>
        simp only [StateT.run_pure, pure_bind]
      | some s₁ =>
        dsimp only
        clear hep
        cases hchal : (chal.isSome && !s₁.safeCh 3 Q)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          clear hchal
          cases r with
          | none =>
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_lift,
              MonadLiftT.monadLift, probeHook_lift_liftM_run, bind_assoc, pure_bind]
            apply probComp_bind_congr
            intro rq
            cases hc : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
                probeHook_lift_pure_run, bind_assoc, pure_bind]
              generalize mkPub P sC.base Q rq _ = mkRes
              rcases mkRes with _ | ⟨pq', pub⟩
              · simp [StateT.run_set, StateT.run_pure]
              · cases chal <;>
                · dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_lift,
                    MonadLiftT.monadLift, bind_assoc, pure_bind]
                  apply probComp_bind_congr
                  intro ⟨res, gh'⟩
                  cases res <;>
                    simp [StateT.run_set, StateT.run_pure]
            · simp [StateT.run_set, StateT.run_pure]
          | some rq =>
            dsimp only
            simp only [StateT.run_bind, StateT.run_lift,
              probeHook_lift_pure_run, bind_assoc, pure_bind]
            cases hc : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
                StateT.run_lift, MonadLiftT.monadLift, map_eq_bind_pure_comp, Function.comp_apply,
                probeHook_lift_bind_run, probeHook_lift_liftM_run,
                probeHook_lift_pure_run, bind_assoc, pure_bind]
              generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = m256
              apply probComp_bind_congr
              intro rc_val
              generalize mkPub P sC.base Q rq _ = mkRes
              rcases mkRes with _ | ⟨pq', pub⟩
              · simp [StateT.run_set, StateT.run_pure]
              · cases chal <;>
                · dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_lift,
                    MonadLiftT.monadLift, bind_assoc, pure_bind]
                  apply probComp_bind_congr
                  intro ⟨res, gh'⟩
                  cases res <;>
                    simp [StateT.run_set, StateT.run_pure]
            · simp [StateT.run_set, StateT.run_pure]
        · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
  · simp only [Bool.true_or, ↓reduceIte, StateT.run_pure, pure_bind]

theorem kemFailSimImplHalted_proj_eq_simImplCTrackHalted {PQ Pt : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    ((kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, gh, tr) >>=
      fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) =
    (((simImplCTrackHalted P K encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Dh q_sm).run (sC, tr)).run gh) := by
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change (((StateT.lift (OracleSpec.query (spec := unifSpec) n : ProbComp _) :
        KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) >>=
      fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) = _
    rw [StateT.run_lift, bind_assoc]
    change _ = (((StateT.lift ((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (qep + 1)).lift (liftM (OracleSpec.query (spec := unifSpec) n : ProbComp _))) :
      StateT _ (ProbeM Pt ℓ) _).run (sC, tr)).run gh)
    rw [StateT.run_lift, StateT.run_bind, probeHook_lift_liftM_run, bind_assoc]
    simp only [pure_bind, StateT.run_pure]
  · exact kemFailSendStepHalted_proj_eq_simSendCTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      Q m₀ none r sC gh tr
  · exact kemFailSendStepHalted_proj_eq_simSendCTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      Q m₀ (some m₁) r sC gh tr
  · change (((do
        let ⟨sC, _, _⟩ ← get
        let revHonest := sC.base.honest.reverse
        let j? := revHonest.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
        let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
          (guardC (simRecvC P encT decT qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (lFS P.C P.codec ℓ encT idOf 25000)
            (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w true))
        match res, j? with
        | some (.accepted _ _ _), some j =>
          modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
        | _, _ => pure ()
        return res : KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) >>=
      fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) = _
    rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, runProbeStep_run,
      bind_assoc, bind_assoc]
    dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
      pure_bind, bind_assoc]
    apply probComp_bind_congr
    intro ⟨⟨res, sC'⟩, gh'⟩
    rcases res with _ | r_acc
    · simp
    · cases r_acc with
      | rejected => simp
      | accepted t i pm =>
        cases List.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
            sC.base.honest.reverse <;>
          simp [StateT.run_modify]
  · change ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr) >>=
      fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) = _
    rw [runProbeStep_run, bind_assoc]
    change _ = (((do
        let (sC, tr) ← get
        let (a, sC') ← StateT.lift ((guardC (simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false)).run sC)
        set (sC', tr); return a : StateT _ (ProbeM Pt ℓ) _).run (sC, tr)).run gh)
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, bind_assoc]
    rfl
  · change ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr) >>=
      fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) = _
    rw [runProbeStep_run, bind_assoc]
    change _ = (((do
        let (sC, tr) ← get
        let (a, sC') ← StateT.lift ((guardC (simCorrC P encT
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run sC)
        set (sC', tr); return a : StateT _ (ProbeM Pt ℓ) _).run (sC, tr)).run gh)
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, bind_assoc]
    rfl

theorem simulateQ_kemFailSimImplHalted_proj_eq_simulateQ_simImplCTrackHalted {PQ Pt α : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      α) :
    ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
      (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
      (tr : KemFailTrackState P.C.F),
      ((simulateQ (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep) oa).run
          (sC, gh, tr) >>=
        fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) =
      (((simulateQ (simImplCTrackHalted P K encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
          Dh) oa).run (sC, tr)).run gh) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC gh tr
    rfl
  | query_bind q_sm u ih =>
    intro sC gh tr
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    have hstep :
        (StateT.run (liftM (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
            (OracleSpec.query q_sm).input)) (sC, gh, tr) >>=
          fun z => pure ((z.1, (z.2.1, z.2.2.2)), z.2.2.1)) =
        StateT.run (StateT.run (liftM (simImplCTrackHalted P K encT decT qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (lFS P.C P.codec ℓ encT idOf 25000)
            (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
            Dh (OracleSpec.query q_sm).input)) (sC, tr)) gh :=
      kemFailSimImplHalted_proj_eq_simImplCTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
        q_sm sC gh tr
    rw [← hstep, bind_assoc]
    apply probComp_bind_congr
    intro ⟨u₁, sC₁, gh₁, tr₁⟩
    rw [pure_bind]
    exact ih u₁ sC₁ gh₁ tr₁

theorem hiddenSaltGameTrackHalted_eq_kemFailSimImplHalted_proj {PQ Pt : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    hiddenSaltGameTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A = (do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep) A).run
          (sC₀, gh₀, tr₀)
      return z.2.2.1.2) := by
  unfold hiddenSaltGameTrackHalted simRunCTrackHaltedWith
  apply probComp_bind_congr; intro b
  apply probComp_bind_congr; intro k
  dsimp only
  rw [StateT.run_bind, bind_assoc, probeHook_lift_liftM_run, bind_assoc]
  apply probComp_bind_congr; intro pqrKey
  rw [pure_bind]
  dsimp only
  rw [StateT.run'_eq, StateT.run_map, map_eq_bind_pure_comp,
    ← simulateQ_kemFailSimImplHalted_proj_eq_simulateQ_simImplCTrackHalted P K ℓ Dh encPt encT decT
      idOf lam qep A
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b, false)
      (initKemFailTrack P.C.F pqrKey)]
  simp only [Function.comp_apply, bind_assoc, pure_bind]

/-! ## Sticky-dead-ghost split -/

set_option exponentiation.threshold 1024 in
set_option linter.constructorNameAsVariable false in
theorem mem_support_kemFailSendStep_of_postCoin {PQ Pt : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (rq : BitVec 512)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hrq : r = some rq ∨ (r = none ∧ rq ∈ support ($ᵗ BitVec 512 : ProbComp (BitVec 512))))
    {z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F)}
    (hz : z ∈ support ((kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC gh tr s₁ Q m₀
      chal r rq).run (sC, gh, tr))) :
    z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, gh, tr)) := by
  rcases hrq with rfl | ⟨rfl, hrq512⟩
  · unfold kemFailSendStep
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3]
    change z ∈ support ((pure rq >>= fun rq =>
      kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC gh tr s₁ Q m₀ chal (some rq)
        rq).run (sC, gh, tr))
    rw [pure_bind]
    exact hz
  · unfold kemFailSendStep
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3]
    change z ∈ support ((liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512)) >>= fun rq =>
      kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC gh tr s₁ Q m₀ chal none rq).run
        (sC, gh, tr))
    rw [StateT.run_bind, StateT.run_monadLift]
    dsimp only [MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
    rw [bind_assoc, MonadAttach.mem_support_bind]
    refine ⟨rq, hrq512, ?_⟩
    rw [pure_bind]
    exact hz

set_option exponentiation.threshold 1024 in
set_option linter.constructorNameAsVariable false in
theorem kemFailSendStepHalted_mem_support_cases {PQ Pt : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    {z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F)}
    (hz : z ∈ support ((kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, gh, tr))) :
    (∃ tr', z = (none, (sC, gh, tr'))) ∨
    z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, gh, tr)) := by
  unfold kemFailSendStepHalted at hz
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hg1 : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q)
  · simp only [hg1, Bool.false_eq_true, ↓reduceIte] at hz
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl ⟨tr, hz⟩
    | some s₁ =>
      simp only [hep] at hz
      cases hg3 : (chal.isSome && !s₁.safeCh 3 Q)
      · simp only [hg3, Bool.false_eq_true, ↓reduceIte] at hz
        cases r with
        | some rq =>
          simp only [pure_bind] at hz
          split_ifs at hz with hcand
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff] at hz
            exact Or.inl ⟨{ tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }, hz⟩
          · exact Or.inr (mem_support_kemFailSendStep_of_postCoin P K ℓ Dh encPt encT decT idOf lam
              qep sC gh tr s₁ Q m₀ chal (some rq) rq hg1 hep hg3 (Or.inl rfl) hz)
        | none =>
          rw [StateT.run_bind, StateT.run_monadLift] at hz
          dsimp only [MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift] at hz
          rw [bind_assoc, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨rq, hrq512, hz⟩
          rw [pure_bind] at hz
          dsimp only at hz
          split_ifs at hz with hcand
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff] at hz
            exact Or.inl ⟨{ tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }, hz⟩
          · exact Or.inr (mem_support_kemFailSendStep_of_postCoin P K ℓ Dh encPt encT decT idOf lam
              qep sC gh tr s₁ Q m₀ chal none rq hg1 hep hg3 (Or.inr ⟨rfl, hrq512⟩) hz)
      · simp only [hg3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        exact Or.inl ⟨tr, hz⟩
  · simp only [hg1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact Or.inl ⟨tr, hz⟩

private theorem kemFailSimImplHalted_inl {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep n : ℕ) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inl n) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inl n) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_transmit {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) =
      kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_chall {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) =
      kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_deliver {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : Party × List (BitVec 8)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inl (.inl (.inr q)))) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inl (.inl (.inr q)))) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_inject {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : Party × List (BitVec 8)) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inl (.inr q))) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inl (.inr q))) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_corr {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : Party) :
    kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inr q)) =
      kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inr (.inr q)) := by
  dsimp only [kemFailSimImplHalted, HAdd.hAdd, Add.add, QueryImpl.add]

private theorem kemFailSimImplHalted_non_deliver_flag_false
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
      (sC, (g, false), tr))) :
    z.2.2.1.2 = false := by
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rw [kemFailSimImplHalted_inl] at hz
    exact congrArg (·.2.1.2)
      (kemFailSimImpl_inl_state_eq P K ℓ Dh encPt encT decT idOf lam qep n sC (g, false) tr z hz)
  · rw [kemFailSimImplHalted_transmit] at hz
    rcases kemFailSendStepHalted_mem_support_cases P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
        sC (g, false) tr hz with ⟨_, rfl⟩ | hz'
    · rfl
    · exact kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
        (.inl (Q, m₀, r)) sC g tr z hz'
  · rw [kemFailSimImplHalted_chall] at hz
    rcases kemFailSendStepHalted_mem_support_cases P K ℓ Dh encPt encT decT idOf lam qep Q m₀
        (some m₁) r sC (g, false) tr hz with ⟨_, rfl⟩ | hz'
    · rfl
    · exact kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (Q, m₀, m₁, r)) sC g tr z hz'
  · exact False.elim (hnd Q w rfl)
  · rw [kemFailSimImplHalted_inject] at hz
    exact kemFailSimImpl_inject_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q w sC g tr z hz
  · rw [kemFailSimImplHalted_corr] at hz
    exact kemFailSimImpl_corr_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q sC g tr z hz

private theorem kemFailSimImplHalted_flag_true_of_true
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
      (sC, (g, true), tr))) :
    z.2.2.1.2 = true := by
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rw [kemFailSimImplHalted_inl] at hz
    exact kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep (.inl n) sC g tr
      z hz
  · rw [kemFailSimImplHalted_transmit] at hz
    rcases kemFailSendStepHalted_mem_support_cases P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
        sC (g, true) tr hz with ⟨_, rfl⟩ | hz'
    · rfl
    · exact kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) sC g tr z hz'
  · rw [kemFailSimImplHalted_chall] at hz
    rcases kemFailSendStepHalted_mem_support_cases P K ℓ Dh encPt encT decT idOf lam qep Q m₀
        (some m₁) r sC (g, true) tr hz with ⟨_, rfl⟩ | hz'
    · rfl
    · exact kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) sC g tr z hz'
  · rw [kemFailSimImplHalted_deliver] at hz
    exact kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w))))) sC g tr z hz
  · rw [kemFailSimImplHalted_inject] at hz
    exact kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w)))) sC g tr z hz
  · rw [kemFailSimImplHalted_corr] at hz
    exact kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q)) sC g tr z hz

open Classical in
def splitSimImplHalted
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (updFl : Bool → Bool → Bool → Bool → Bool)
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :
    QueryImpl
      (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8)))
      (KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ)
  | .inr (.inl (.inl (.inr (Q, w)))) => do
    let ⟨sC, ⟨g, fl, dead⟩, tr⟩ ← get
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
    let j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let tr' := match r.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    let hlazy := decide (∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    let hprobe := r.2.2.2
    let fl' := updFl fl hlazy hprobe dead
    let dead' := dead || !hlazy
    set (r.2.1, (r.2.2.1, fl', dead'), tr')
    return r.1
  | q_sm => do
    let ⟨sC, ⟨g, fl, dead⟩, tr⟩ ← get
    let (ans, ⟨sC', ⟨g', fl'⟩, tr'⟩) ←
      StateT.lift ((kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
        (sC, (g, fl), tr))
    set (sC', (g', fl', dead), tr')
    return ans

abbrev firstNEHalted'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :=
  splitSimImplHalted (fun fl hlazy hprobe dead => fl || (hlazy && hprobe && !dead))
    P K InvPQ ℓ Dh encPt encT decT idOf lam qep q

abbrev evictOnlyHalted'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :=
  splitSimImplHalted (fun fl hlazy hprobe dead => fl || ((!hlazy || dead) && hprobe))
    P K InvPQ ℓ Dh encPt encT decT idOf lam qep q

theorem splitSimImplHalted_non_deliver_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (updFl : Bool → Bool → Bool → Bool → Bool)
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (splitSimImplHalted updFl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
      (sC, (g, fl, dead), tr) =
      ((kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, fl), tr) >>=
        fun x => pure (x.1, (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2))) := by
  have hlift : ∀ {α : Type} (m : ProbComp α),
      (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ α).run (sC, (g, fl, dead), tr) =
        (m >>= fun a => pure (a, (sC, (g, fl, dead), tr))) := fun _ => rfl
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp only [splitSimImplHalted, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · simp only [splitSimImplHalted, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · simp only [splitSimImplHalted, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · exact False.elim (hnd Q w rfl)
  · simp only [splitSimImplHalted, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
  · simp only [splitSimImplHalted, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]

private theorem firstNEHalted'_dead_step
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
      (sC, (g, false, true), tr))) :
    z.2.2.1.2.2 = true ∧ z.2.2.1.2.1 = false := by
  by_cases hdel : ∃ Q w, q_sm = .inr (.inl (.inl (.inr (Q, w))))
  · rcases hdel with ⟨Q, w, rfl⟩
    simp only [firstNEHalted', splitSimImplHalted, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  · have hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))) := fun Q w h => hdel ⟨Q, w, h⟩
    rw [firstNEHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf
      lam qep q q_sm hnd sC g false true tr, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨x, hx, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, kemFailSimImplHalted_non_deliver_flag_false P K ℓ Dh encPt encT decT idOf lam qep
      q_sm hnd sC g tr x hx⟩

theorem fl_false_of_dead_support_halted {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (tr : KemFailTrackState P.C.F)
      (z : α × (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
        KemFailTrackState P.C.F)),
      z ∈ support ((simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        oa).run (sC, (g, false, true), tr)) →
      z.2.2.1.2.2 = true ∧ z.2.2.1.2.1 = false := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC g tr z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl⟩
  | query_bind q_sm u ih =>
    intro sC g tr z hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u₁, sC₁, ⟨g₁, fl₁, dead₁⟩, tr₁⟩, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := firstNEHalted'_dead_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      q_sm sC g tr (u₁, sC₁, (g₁, fl₁, dead₁), tr₁) h₁
    exact ih u₁ sC₁ g₁ tr₁ z h₂

theorem evalDist_firstNEHalted'_dead_eq_zero {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, false, true), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} = 0 := by
  have hcongr :
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, false, true), tr) >>=
        fun z => pure z.2.2.1.2.1] =
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, false, true), tr) >>=
        fun _ => (pure false : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    rw [(fl_false_of_dead_support_halted P K InvPQ ℓ Dh encPt encT decT idOf lam qep q oa sC g tr
      z hz).2]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

open Classical in
private theorem evalDist_simulateQ_kemFailSimImplHalted_flag_true_eq_split {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (updFl : Bool → Bool → Bool → Bool → Bool)
    (hupd_true : ∀ hlazy hprobe dead, updFl true hlazy hprobe dead = true)
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (dead : Bool) (tr : KemFailTrackState P.C.F) :
    𝒟[(simulateQ (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep) oa).run
        (sC, (g, true), tr) >>=
      fun z => pure z.2.2.1.2] =
    𝒟[(simulateQ (splitSimImplHalted updFl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, true, dead), tr) >>=
      fun z => pure z.2.2.1.2.1] := by
  induction oa using OracleComp.inductionOn generalizing sC g dead tr with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    by_cases hdel : ∃ Q w, q_sm = .inr (.inl (.inl (.inr (Q, w))))
    · rcases hdel with ⟨Q, w, rfl⟩
      let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let tr' := match r₀.1, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      let hlazy := decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
      have hdel_kem :
          (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, true), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, true), tr')) := by
        have h := kemFailSimImpl_deliver_run P K ℓ Dh encPt encT decT idOf lam qep Q w
          sC (g, true) tr
        dsimp only at h
        rw [simRecvStepC_flag_or P ℓ Dh encPt encT decT idOf lam qep Q w true sC g true,
          Bool.true_or] at h
        exact h
      have hdel_sp :
          (splitSimImplHalted updFl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, true, dead), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, true, dead || !hlazy), tr')) := by
        simp [splitSimImplHalted, r₀, j?, tr', hlazy, hupd_true, StateT.run_bind, StateT.run_get,
          StateT.run_set]
        rfl
      rw [hdel_kem, hdel_sp, pure_bind, pure_bind]
      exact ih r₀.1 r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr'
    · have hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))) := fun Q w h => hdel ⟨Q, w, h⟩
      rw [splitSimImplHalted_non_deliver_run updFl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        q_sm hnd sC g true dead tr, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_congr_of_support _ _ _ fun z₁ hz₁ => ?_
      have hfl := kemFailSimImplHalted_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
        q_sm sC g tr z₁ hz₁
      rw [show z₁.2 = (z₁.2.1, (z₁.2.2.1.1, true), z₁.2.2.2) from
        Prod.ext rfl (Prod.ext (Prod.ext rfl hfl) rfl)]
      exact ih z₁.1 z₁.2.1 z₁.2.2.1.1 dead z₁.2.2.2

open Classical in
/-- Bounds the bad-event probability of `kemFailSimImplHalted` by the sum of `firstNEHalted'` and
`evictOnlyHalted'`. -/
theorem evalDist_simulateQ_kemFailSimImplHalted_le_firstNE'_add_evictOnly' {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (dead : Bool) (tr : KemFailTrackState P.C.F) :
    𝒟[(simulateQ (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep) oa).run
        (sC, (g, false), tr) >>=
      fun z => pure z.2.2.1.2] {true} ≤
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, false, dead), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} +
    𝒟[(simulateQ (evictOnlyHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, false, dead), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} := by
  induction oa using OracleComp.inductionOn generalizing sC g dead tr with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    by_cases hdel : ∃ Q w, q_sm = .inr (.inl (.inl (.inr (Q, w))))
    · rcases hdel with ⟨Q, w, rfl⟩
      let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let tr' := match r₀.1, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      let hlazy := decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
      have hdel_kem :
          (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, r₀.2.2.2), tr')) :=
        kemFailSimImpl_deliver_run P K ℓ Dh encPt encT decT idOf lam qep Q w sC (g, false) tr
      have hdel_ne :
          (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, dead), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, hlazy && r₀.2.2.2 && !dead, dead || !hlazy), tr')) := by
        simp [firstNEHalted', splitSimImplHalted, r₀, j?, tr', hlazy, StateT.run_bind,
          StateT.run_get, StateT.run_set]
        rfl
      have hdel_ev :
          (evictOnlyHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, dead), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, (!hlazy || dead) && r₀.2.2.2, dead || !hlazy), tr')) := by
        simp [evictOnlyHalted', splitSimImplHalted, r₀, j?, tr', hlazy, StateT.run_bind,
          StateT.run_get, StateT.run_set]
        rfl
      rw [hdel_kem, hdel_ne, hdel_ev, pure_bind, pure_bind, pure_bind]
      dsimp only
      cases hp : r₀.2.2.2
      · simp only [Bool.and_false]
        exact ih r₀.1 r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr'
      · cases hlazy <;> cases dead <;> simp only [Bool.not_true, Bool.not_false,
          Bool.and_true, Bool.and_false, Bool.true_or, Bool.false_or]
        · rw [evalDist_simulateQ_kemFailSimImplHalted_flag_true_eq_split
            (fun fl hlazy hprobe dead => fl || ((!hlazy || dead) && hprobe))
            (fun _ _ _ => Bool.true_or _) P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (u r₀.1)
            r₀.2.1 r₀.2.2.1 true tr']
          exact le_add_self
        · rw [evalDist_simulateQ_kemFailSimImplHalted_flag_true_eq_split
            (fun fl hlazy hprobe dead => fl || ((!hlazy || dead) && hprobe))
            (fun _ _ _ => Bool.true_or _) P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (u r₀.1)
            r₀.2.1 r₀.2.2.1 true tr']
          exact le_add_self
        · rw [evalDist_simulateQ_kemFailSimImplHalted_flag_true_eq_split
            (fun fl hlazy hprobe dead => fl || (hlazy && hprobe && !dead))
            (fun _ _ _ => Bool.true_or _) P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (u r₀.1)
            r₀.2.1 r₀.2.2.1 false tr']
          exact le_self_add
        · rw [evalDist_simulateQ_kemFailSimImplHalted_flag_true_eq_split
            (fun fl hlazy hprobe dead => fl || ((!hlazy || dead) && hprobe))
            (fun _ _ _ => Bool.true_or _) P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (u r₀.1)
            r₀.2.1 r₀.2.2.1 true tr']
          exact le_add_self
    · have hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))) := fun Q w h => hdel ⟨Q, w, h⟩
      rw [firstNEHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf
          lam qep q q_sm hnd sC g false dead tr,
        evictOnlyHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT idOf
          lam qep q q_sm hnd sC g false dead tr, bind_assoc, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun z₁ hz₁ => ?_
      have hfl₁ := kemFailSimImplHalted_non_deliver_flag_false P K ℓ Dh encPt encT decT idOf lam
        qep q_sm hnd sC g tr z₁ hz₁
      rw [show z₁.2 = (z₁.2.1, (z₁.2.2.1.1, false), z₁.2.2.2) from
        Prod.ext rfl (Prod.ext (Prod.ext rfl hfl₁) rfl)]
      exact ih z₁.1 z₁.2.1 z₁.2.2.1.1 dead z₁.2.2.2

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted
