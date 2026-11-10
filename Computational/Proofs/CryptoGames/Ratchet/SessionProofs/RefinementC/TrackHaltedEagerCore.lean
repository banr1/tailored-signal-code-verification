/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted non-eager runner and hook bridges

Defines `stepSimCTrackNone` and `runSimCTrackNone` together with per-step eager-coin equivalence
lemmas for `deliver`, `inject`, and `corrupt`.
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
open CryptoGames.CBC
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section EagerCore

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

def stepSimCTrackNone (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q ×
      (JointC PQ Pt ℓ × KemFailTrackState P.C.F)) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  (((simImplCTrackHalted P K encT decT qep fig fs (probeHook fig (qep + 1)) Dh (.inr q)).run
      (x.1, tr)).run x.2) >>=
    fun r => pure (r.1.1, ((r.1.2.1, r.2), r.1.2.2))

def simStepImplCTrackNone (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) :
    QueryImpl (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      (StateT (JointC PQ Pt ℓ × KemFailTrackState P.C.F) ProbComp) :=
  fun q => StateT.mk fun ⟨x, tr⟩ =>
    stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep q x tr

def runSimCTrackNone {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    ProbComp (α × (JointC PQ Pt ℓ × KemFailTrackState P.C.F)) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (JointC PQ Pt ℓ × KemFailTrackState P.C.F) ProbComp) +
    simStepImplCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
  (simulateQ impl oa).run (x, tr)

theorem runSimCTrackNone_pure {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (a : α) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (pure a) x tr = pure (a, (x, tr)) := by
  simp [runSimCTrackNone]

theorem runSimCTrackNone_inl_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inl u)) >>= cont) x tr =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (cont y) x tr := by
  simp only [runSimCTrackNone, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget (StateT (JointC PQ Pt ℓ × KemFailTrackState P.C.F) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        simStepImplCTrackNone P K ℓ Dh encPt encT decT idOf lam qep) (.inl u)) :
        StateT _ ProbComp (unifSpec.Range u)).run (x, tr) =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        pure (y, (x, tr))) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runSimCTrackNone_inr_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr q)) >>= cont) x tr =
      stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep q x tr >>= fun r =>
        runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (cont r.1) r.2.1 r.2.2 := by
  simp only [runSimCTrackNone, simStepImplCTrackNone, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

theorem tb_idHook_lift {α : Type} (x : Fig8Comp Pt ℓ α) :
    (idHook (ℓ := ℓ)).lift x = x := rfl

theorem tb_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift x).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

theorem tb_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem tb_run_h1_eq
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (b : Bool)
    (A : SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    SM.run fig 3 qepF SM.Config.h1 b A = (do
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      (simulateQ (fig8ImplH1 fig qepF) A).run (SM.initState fig k b)) := rfl

private theorem tb_simImplCTrackHalted_probeHook_inl_run
    (P : Params PQ (BitVec 512)) (K : MlKem) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (u : unifSpec.Domain) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    (((simImplCTrackHalted P K encT decT qep fig fs (probeHook fig qepF) Dh (.inl u)).run
        (x.1, tr)).run x.2) =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
        fun y => pure ((y, (x.1, tr)), x.2)) := by
  change (((StateT.lift ((probeHook fig qepF).lift
    (liftM (OracleSpec.query (spec := unifSpec) u : ProbComp _) : Fig8Comp Pt ℓ _)) :
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (ProbeM Pt ℓ) _).run (x.1, tr)).run x.2) = _
  simp only [StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply, StateT.run_bind,
    tb_probeHook_lift_run, bind_assoc, pure_bind, StateT.run_pure]
  have h1 : (simulateQ (fig8ImplH1 fig qepF)
      (liftM (OracleSpec.query (spec := unifSpec) u : ProbComp _) : Fig8Comp Pt ℓ _)).run x.2.1 =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
        fun y => pure (y, x.2.1)) := by
    unfold fig8ImplH1
    rw [Construction.AuthL11.simulateQ_liftM_run]
  rw [h1]
  simp only [bind_assoc, pure_bind]

private theorem tb_simulateQ_probeHook_eq_runSimCTrackNone {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (((simulateQ (simImplCTrackHalted P K encT decT qep fig fs (probeHook fig (qep + 1)) Dh)
        oa).run (x.1, tr)).run x.2 >>=
      fun r => pure (r.1.1, ((r.1.2.1, r.2), r.1.2.2))) =
      runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep oa x tr := by
  intro fig fs
  induction oa using OracleComp.inductionOn generalizing x tr with
  | pure a =>
    simp [runSimCTrackNone_pure]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        simulateQ_query_bind, StateT.run_bind, bind_assoc, runSimCTrackNone_inl_bind]
      have h1 := tb_simImplCTrackHalted_probeHook_inl_run P K encT decT qep fig fs (qep + 1) Dh u x tr
      change (((simImplCTrackHalted P K encT decT qep fig fs (probeHook fig (qep + 1)) Dh
        (.inl u)).run (x.1, tr)).run x.2 >>= _) = _
      rw [h1]
      simp only [bind_assoc, pure_bind]
      congr 1; funext y
      exact ih y x tr
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        simulateQ_query_bind, StateT.run_bind, bind_assoc, runSimCTrackNone_inr_bind]
      unfold stepSimCTrackNone
      simp only [bind_assoc, pure_bind]
      congr 1; funext r
      exact ih r.1.1 (r.1.2.1, r.2) r.1.2.2

theorem tb_hiddenSaltGameTrackHalted_eq_runSimCTrackNone
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    hiddenSaltGameTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
              (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k b, false)
              (initKemFailTrack P.C.F pqrKey) >>= fun z =>
              pure z.2.1.2.2) := by
  intro sm
  unfold hiddenSaltGameTrackHalted simRunCTrackHaltedWith
  congr 1; funext b
  congr 1; funext k
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply,
    StateT.run_bind, StateT.run_pure, tb_probeHook_lift_run, bind_assoc, pure_bind]
  have h1 : (simulateQ (fig8ImplH1 sm (qep + 1))
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))).run
      (SM.initState sm k b) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqrKey =>
        pure (pqrKey, SM.initState sm k b)) := by
    unfold fig8ImplH1
    rw [Construction.AuthL11.simulateQ_liftM_run]
  change (do
      let p ← (simulateQ (fig8ImplH1 sm (qep + 1)) (liftM ($ᵗ BitVec 256))).run (SM.initState sm k b)
      let x ← (((simulateQ (simImplCTrackHalted P K encT decT qep sm
        (lFS P.C P.codec ℓ encT idOf 25000) (probeHook sm (qep + 1)) Dh) A).run
        (initSimC (P.spqr.init .a2b p.1) (P.spqr.init .b2a p.1),
         initKemFailTrack P.C.F p.1)).run (p.2, false))
      pure x.2.2) = _
  rw [h1]
  simp only [bind_assoc, pure_bind]
  congr 1; funext pqrKey
  rw [← tb_simulateQ_probeHook_eq_runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm k b, false)
    (initKemFailTrack P.C.F pqrKey)]
  simp only [bind_assoc, pure_bind]
  rfl

private def tb_stRel {S α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    (mId : StateT S (Fig8Comp Pt ℓ) α)
    (mPr : StateT S (ProbeM Pt ℓ) α) : Prop :=
  ∀ (st : S)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (simulateQ (fig8ImplH1 fig qepF) (mId.run st)).run gh.1 =
      ((mPr.run st).run gh >>= fun r => pure (r.1, r.2.1))

private theorem tb_stRel_pure {S α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (a : α) :
    tb_stRel (S := S) fig qepF (pure a) (pure a) := by
  intro st gh; simp

private theorem tb_stRel_bind {S α β : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ}
    {mId : StateT S (Fig8Comp Pt ℓ) α} {mPr : StateT S (ProbeM Pt ℓ) α}
    {kId : α → StateT S (Fig8Comp Pt ℓ) β} {kPr : α → StateT S (ProbeM Pt ℓ) β}
    (hm : tb_stRel fig qepF mId mPr)
    (hk : ∀ a, tb_stRel fig qepF (kId a) (kPr a)) :
    tb_stRel fig qepF (mId >>= kId) (mPr >>= kPr) := by
  intro st gh
  simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
  rw [hm st gh]
  simp only [bind_assoc, pure_bind]
  congr 1; funext r
  exact hk r.1.1 r.1.2 r.2

private theorem tb_stRel_get {S : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) :
    tb_stRel (S := S) fig qepF get get := by
  intro st gh; simp

private theorem tb_stRel_set {S : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (st' : S) :
    tb_stRel (S := S) fig qepF (set st') (set st') := by
  intro st gh; simp

private theorem tb_stRel_modify {S : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (f : S → S) :
    tb_stRel (S := S) fig qepF (modify f) (modify f) := by
  intro st gh; simp

private theorem tb_stRel_ite {S α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {P_cond : Prop} [Decidable P_cond]
    {tId eId : StateT S (Fig8Comp Pt ℓ) α} {tPr ePr : StateT S (ProbeM Pt ℓ) α}
    (ht : tb_stRel fig qepF tId tPr) (he : tb_stRel fig qepF eId ePr) :
    tb_stRel fig qepF (if P_cond then tId else eId) (if P_cond then tPr else ePr) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem tb_stRel_lift_hook {S α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    tb_stRel (S := S) fig qepF
      (StateT.lift (idHook.lift x))
      (StateT.lift ((probeHook fig qepF).lift x)) := by
  intro st gh
  simp only [StateT.run_lift, tb_idHook_lift, map_eq_bind_pure_comp, Function.comp_apply,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, tb_probeHook_lift_run,
    bind_assoc, pure_bind]

private theorem tb_stRel_probe {S : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    tb_stRel (S := S) fig qepF
      (StateT.lift (idHook.probe Q c'))
      (StateT.lift ((probeHook fig qepF).probe Q c')) := by
  intro st gh
  have hid : (StateT.lift ((idHook (ℓ := ℓ)).probe Q c') : StateT S (Fig8Comp Pt ℓ) Unit).run st =
      pure ((), st) := rfl
  rw [hid]
  simp only [simulateQ_pure, StateT.run_pure, StateT.run_lift, map_eq_bind_pure_comp,
    Function.comp_apply, StateT.run_bind, tb_probeHook_probe_run, pure_bind]

private theorem tb_zoomB_probeHook_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((runOnBaseState (probeHook fig qepF) x).run sC).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1 >>= fun r =>
        pure ((r.1.1, { sC with base := r.1.2 }), (r.2, gh.2))) := by
  change (((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh = _
  rw [StateT.run_bind, tb_probeHook_lift_run]
  simp only [bind_assoc, pure_bind, StateT.run_pure]

private theorem tb_stRel_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    tb_stRel (S := LibsignalToModularSchemeSimState PQ Pt ℓ) fig qepF
      (runOnBaseState idHook x) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh
  change (simulateQ (fig8ImplH1 fig qepF)
      (idHook.lift (x.run sC.base) >>= fun p => pure (p.1, { sC with base := p.2 }))).run gh.1 =
    (((runOnBaseState (probeHook fig qepF) x).run sC).run gh >>= fun r => pure (r.1, r.2.1))
  rw [tb_zoomB_probeHook_run]
  simp only [tb_idHook_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind]

private theorem tb_stRel_guardC {α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ}
    {mId : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : tb_stRel fig qepF mId mPr) :
    tb_stRel fig qepF (guardC mId) (guardC mPr) := by
  unfold guardC
  refine tb_stRel_bind (tb_stRel_get fig qepF) fun sC => ?_
  exact tb_stRel_ite (tb_stRel_pure fig qepF none) hm

private theorem tb_stRel_liftS {F : ShaCompress} {α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ}
    {mId : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (hm : tb_stRel fig qepF mId mPr) :
    tb_stRel (S := LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState F) fig qepF
      (do let (sC, tr) ← get; let (a, sC') ← StateT.lift (mId.run sC); set (sC', tr); return a)
      (do let (sC, tr) ← get; let (a, sC') ← StateT.lift (mPr.run sC); set (sC', tr); return a) := by
  intro ⟨sC, tr⟩ gh
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
    map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind, simulateQ_pure, bind_assoc,
    pure_bind]
  rw [hm sC gh]
  simp only [bind_assoc, pure_bind]

private theorem tb_stRel_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    tb_stRel fig qepF
      (fwdAnswerC qep fig fs idHook Q w isDel ci? T pq' c')
      (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine tb_stRel_bind (tb_stRel_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact tb_stRel_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact tb_stRel_zoomB (PQ := PQ) fig qepF _
      | exact tb_stRel_bind (tb_stRel_modify fig qepF _) fun _ =>
          tb_stRel_zoomB (PQ := PQ) fig qepF _

private theorem tb_stRel_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    tb_stRel fig qepF
      (resyncC qep fig fs idHook Q w ci? T pq' c r)
      (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact tb_stRel_pure fig qepF _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine tb_stRel_bind (tb_stRel_lift_hook fig qepF _) fun res => ?_
    cases res with
    | none => exact tb_stRel_pure fig qepF _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact tb_stRel_bind (tb_stRel_modify fig qepF _) fun _ =>
          tb_stRel_zoomB (PQ := PQ) fig qepF _
      | _ => exact tb_stRel_pure fig qepF _

private theorem tb_stRel_fwdC (P : Params PQ (BitVec 512)) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    tb_stRel fig qepF
      (fwdC P qep fig fs idHook Q w isDel ci? T pq' honestC c')
      (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine tb_stRel_bind (tb_stRel_get fig qepF) fun sC => ?_
  cases honestC with
  | none => exact tb_stRel_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine tb_stRel_ite ?_ (tb_stRel_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact tb_stRel_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact tb_stRel_bind (tb_stRel_probe fig qepF Q c') fun _ =>
        tb_stRel_pure fig qepF _

private theorem tb_stRel_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    tb_stRel fig qepF
      (fwdEvictC qep fig fs idHook Q w isDel T pq' c')
      (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine tb_stRel_bind (tb_stRel_get fig qepF) fun sC => ?_
  refine tb_stRel_ite ?_ (tb_stRel_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact tb_stRel_bind (tb_stRel_probe fig qepF Q c') fun _ => tb_stRel_pure fig qepF _

private theorem tb_stRel_simRecvC (P : Params PQ (BitVec 512)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    tb_stRel fig qepF
      (simRecvC P encT decT qep fig fs idHook Q w isDel)
      (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine tb_stRel_bind (tb_stRel_get fig qepF) fun sC => ?_
  dsimp only
  refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
  refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
  refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
  refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact tb_stRel_pure fig qepF _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
    refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact tb_stRel_pure fig qepF _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
        exact tb_stRel_fwdC P qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
        refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
        refine tb_stRel_ite
          (tb_stRel_bind (tb_stRel_modify fig qepF _) fun _ => ?_) ?_ <;>
        · refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
          cases decT h.senderRatchetKey with
          | none => exact tb_stRel_pure fig qepF _
          | some T =>
            exact tb_stRel_ite
              (tb_stRel_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (tb_stRel_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

private theorem tb_stRel_simCorrC (P : Params PQ (BitVec 512)) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    tb_stRel fig qepF
      (simCorrC P encT idHook Dh Q)
      (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine tb_stRel_bind (tb_stRel_get fig qepF) fun sC => ?_
  dsimp only
  refine tb_stRel_ite (tb_stRel_pure fig qepF _) ?_
  refine tb_stRel_bind (tb_stRel_lift_hook fig qepF _) fun res => ?_
  cases res with
  | none => exact tb_stRel_pure fig qepF _
  | some st =>
    exact tb_stRel_bind (tb_stRel_set fig qepF _) fun _ => tb_stRel_pure fig qepF _

private theorem tb_stRel_simSendCTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    tb_stRel fig qepF
      (simSendCTrackHalted P K qep fig idHook Q m₀ chal r)
      (simSendCTrackHalted P K qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendCTrackHalted
  refine tb_stRel_bind (tb_stRel_get fig qepF) fun ⟨sC, tr⟩ => ?_
  dsimp only
  refine tb_stRel_ite (tb_stRel_pure fig qepF none) ?_
  cases sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => exact tb_stRel_pure fig qepF none
  | some s₁ =>
    dsimp only
    refine tb_stRel_ite (tb_stRel_pure fig qepF none) ?_
    refine tb_stRel_bind (tb_stRel_lift_hook fig qepF _) fun rq => ?_
    refine tb_stRel_ite
      (tb_stRel_bind (tb_stRel_set fig qepF _) fun _ => tb_stRel_pure fig qepF none) ?_
    refine tb_stRel_bind (tb_stRel_lift_hook fig qepF _) fun rc => ?_
    cases mkPub (P := P) sC.base Q rq
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
         else sC.base.pn Q) with
    | none =>
      exact tb_stRel_bind (tb_stRel_set fig qepF _) fun _ => tb_stRel_pure fig qepF none
    | some pp =>
      rcases pp with ⟨pq', pub⟩
      dsimp only
      refine tb_stRel_bind (tb_stRel_lift_hook fig qepF _) fun res => ?_
      cases res with
      | none =>
        exact tb_stRel_bind (tb_stRel_set fig qepF _) fun _ => tb_stRel_pure fig qepF none
      | some c =>
        exact tb_stRel_bind (tb_stRel_set fig qepF _) fun _ => tb_stRel_pure fig qepF _

private theorem tb_stRel_simImplCTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain) :
    tb_stRel fig qepF
      (simImplCTrackHalted P K encT decT qep fig fs idHook Dh t)
      (simImplCTrackHalted P K encT decT qep fig fs (probeHook fig qepF) Dh t) := by
  rcases t with u | ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact tb_stRel_lift_hook fig qepF _
  · exact tb_stRel_simSendCTrackHalted P K qep fig qepF Q m₀ none r'
  · exact tb_stRel_simSendCTrackHalted P K qep fig qepF Q m₀ (some m₁) r'
  · dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
    refine tb_stRel_bind (tb_stRel_get fig qepF) fun ⟨sC, _⟩ => ?_
    refine tb_stRel_bind
      (tb_stRel_liftS (tb_stRel_guardC (tb_stRel_simRecvC P encT decT qep fig fs qepF Q w true)))
      fun res => ?_
    dsimp only
    split
    · exact tb_stRel_bind (tb_stRel_modify fig qepF _) fun _ => tb_stRel_pure fig qepF _
    · exact tb_stRel_bind (tb_stRel_pure fig qepF ()) fun _ => tb_stRel_pure fig qepF _
  · exact tb_stRel_liftS (tb_stRel_guardC (tb_stRel_simRecvC P encT decT qep fig fs qepF Q w false))
  · exact tb_stRel_liftS (tb_stRel_guardC (tb_stRel_simCorrC P encT fig qepF Dh Q))

private theorem tb_stRel_simulateQ {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α) :
    tb_stRel fig qepF
      (simulateQ (simImplCTrackHalted P K encT decT qep fig fs idHook Dh) oa)
      (simulateQ (simImplCTrackHalted P K encT decT qep fig fs (probeHook fig qepF) Dh) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [simulateQ_pure]
    exact tb_stRel_pure fig qepF a
  | query_bind t cont ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    exact tb_stRel_bind (tb_stRel_simImplCTrackHalted P K encT decT qep fig fs qepF Dh t) ih

theorem tb_game_simRunCTrackHalted_eq_runSimCTrackNone
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    SM.game sm 3 (qep + 1) SM.Config.h1
        (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
              (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k b, false)
              (initKemFailTrack P.C.F pqrKey) >>= fun z =>
              pure (b == z.1 || z.2.1.2.1.win)) := by
  intro sm
  unfold SM.game runLibsignalToModularSchemeSimTrackHalted simRunCTrackHaltedWith
  congr 1; funext b
  rw [tb_run_h1_eq]
  simp only [bind_assoc]
  congr 1; funext k
  simp only [tb_idHook_lift, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  have h1 : (simulateQ (fig8ImplH1 sm (qep + 1))
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))).run
      (SM.initState sm k b) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqrKey =>
        pure (pqrKey, SM.initState sm k b)) := by
    unfold fig8ImplH1
    rw [Construction.AuthL11.simulateQ_liftM_run]
  change (do
      let x ← (simulateQ (fig8ImplH1 sm (qep + 1)) (liftM ($ᵗ BitVec 256))).run (SM.initState sm k b)
      let x ← (simulateQ (fig8ImplH1 sm (qep + 1))
        ((simulateQ (simImplCTrackHalted P K encT decT qep sm
          (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh) A).run
          (initSimC (P.spqr.init .a2b x.1) (P.spqr.init .b2a x.1),
           initKemFailTrack P.C.F x.1))).run x.2
      pure (b == x.1.1 || x.2.win)) = _
  rw [h1]
  simp only [bind_assoc, pure_bind]
  congr 1; funext pqrKey
  have hrel := tb_stRel_simulateQ P K encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000)
    (qep + 1) Dh A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
     initKemFailTrack P.C.F pqrKey)
    (SM.initState sm k b, false)
  rw [← tb_simulateQ_probeHook_eq_runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm k b, false)
    (initKemFailTrack P.C.F pqrKey)]
  change (simulateQ (fig8ImplH1 sm (qep + 1))
      ((simulateQ (simImplCTrackHalted P K encT decT qep sm
        (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
         initKemFailTrack P.C.F pqrKey))).run
      (SM.initState sm k b, false).1 >>= _ = _
  rw [hrel]
  simp only [bind_assoc, pure_bind]
  rfl

theorem tb_simCNoneWinEventTrackHalted_eq_runSimCTrackNone
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
              (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k b, false)
              (initKemFailTrack P.C.F pqrKey) >>= fun z =>
              pure z.2.1.2.1.win) := by
  intro sm
  unfold simCNoneWinEventTrackHalted runLibsignalToModularSchemeSimTrackHalted simRunCTrackHaltedWith
  congr 1; funext b
  dsimp only
  rw [tb_run_h1_eq]
  simp only [bind_assoc]
  congr 1; funext k
  simp only [tb_idHook_lift, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  have h1 : (simulateQ (fig8ImplH1 sm (qep + 1))
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))).run
      (SM.initState sm k b) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqrKey =>
        pure (pqrKey, SM.initState sm k b)) := by
    unfold fig8ImplH1
    rw [Construction.AuthL11.simulateQ_liftM_run]
  change (do
      let x ← (simulateQ (fig8ImplH1 sm (qep + 1)) (liftM ($ᵗ BitVec 256))).run (SM.initState sm k b)
      let x ← (simulateQ (fig8ImplH1 sm (qep + 1))
        ((simulateQ (simImplCTrackHalted P K encT decT qep sm
          (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh) A).run
          (initSimC (P.spqr.init .a2b x.1) (P.spqr.init .b2a x.1),
           initKemFailTrack P.C.F x.1))).run x.2
      pure x.2.win) = _
  rw [h1]
  simp only [bind_assoc, pure_bind]
  congr 1; funext pqrKey
  have hrel := tb_stRel_simulateQ P K encT decT qep sm (lFS P.C P.codec ℓ encT idOf 25000)
    (qep + 1) Dh A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
     initKemFailTrack P.C.F pqrKey)
    (SM.initState sm k b, false)
  rw [← tb_simulateQ_probeHook_eq_runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm k b, false)
    (initKemFailTrack P.C.F pqrKey)]
  change (simulateQ (fig8ImplH1 sm (qep + 1))
      ((simulateQ (simImplCTrackHalted P K encT decT qep sm
        (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
         initKemFailTrack P.C.F pqrKey))).run
      (SM.initState sm k b, false).1 >>= _ = _
  rw [hrel]
  simp only [bind_assoc, pure_bind]
  rfl

theorem tb_cxSend_base (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ)
    (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

def stepSimCTrackNoneSend (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    ProbComp (Option (List (BitVec 8)) × (JointC PQ Pt ℓ × KemFailTrackState P.C.F)) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  ((simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (x.1, tr))).run x.2.1) >>=
    fun z => pure (z.1.1, ((z.1.2.1, z.2, x.2.2), z.1.2.2))

abbrev Fig8Sch (Pt : Type) (ℓ : ℕ) :=
  SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
    (BitVec 256) (Fig8C Pt)

def tb_noProbe {S α : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ)
    (mId : StateT S (Fig8Comp Pt ℓ) α) (mPr : StateT S (ProbeM Pt ℓ) α) : Prop :=
  ∀ (st : S)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (mPr.run st).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) (mId.run st)).run gh.1 >>=
        fun r => pure (r.1, (r.2, gh.2)))

private theorem tb_noProbe_pure {S α : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ) (a : α) :
    tb_noProbe (S := S) fig qepF (pure a) (pure a) := fun _ _ => by simp

private theorem tb_noProbe_get {S : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ) :
    tb_noProbe (S := S) fig qepF get get := fun _ _ => by simp

private theorem tb_noProbe_set {S : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ) (st' : S) :
    tb_noProbe (S := S) fig qepF (set st') (set st') := fun _ _ => by simp

private theorem tb_noProbe_ite {S α : Type} {fig : Fig8Sch Pt ℓ} {qepF : ℕ}
    {P_cond : Prop} [Decidable P_cond]
    {tId eId : StateT S (Fig8Comp Pt ℓ) α} {tPr ePr : StateT S (ProbeM Pt ℓ) α}
    (ht : tb_noProbe fig qepF tId tPr) (he : tb_noProbe fig qepF eId ePr) :
    tb_noProbe fig qepF (if P_cond then tId else eId) (if P_cond then tPr else ePr) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem tb_noProbe_bind {S α β : Type} {fig : Fig8Sch Pt ℓ} {qepF : ℕ}
    {mId : StateT S (Fig8Comp Pt ℓ) α} {mPr : StateT S (ProbeM Pt ℓ) α}
    {kId : α → StateT S (Fig8Comp Pt ℓ) β} {kPr : α → StateT S (ProbeM Pt ℓ) β}
    (hm : tb_noProbe fig qepF mId mPr) (hk : ∀ a, tb_noProbe fig qepF (kId a) (kPr a)) :
    tb_noProbe fig qepF (mId >>= kId) (mPr >>= kPr) := by
  intro st gh
  simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
  rw [hm st gh]
  simp only [bind_assoc, pure_bind]
  congr 1; funext r
  exact hk r.1.1 r.1.2 (r.2, gh.2)

private theorem tb_noProbe_lift_hook {S α : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ)
    (x : Fig8Comp Pt ℓ α) :
    tb_noProbe (S := S) fig qepF
      (StateT.lift (idHook.lift x)) (StateT.lift ((probeHook fig qepF).lift x)) := by
  intro st gh
  simp only [StateT.run_lift, tb_idHook_lift, map_eq_bind_pure_comp, Function.comp_apply,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, tb_probeHook_lift_run,
    bind_assoc, pure_bind]

theorem tb_noProbe_simSendCTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ) (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    tb_noProbe fig qepF
      (simSendCTrackHalted P K qep fig idHook Q m₀ chal r)
      (simSendCTrackHalted P K qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendCTrackHalted
  refine tb_noProbe_bind (tb_noProbe_get fig qepF) fun ⟨sC, tr⟩ => ?_
  dsimp only
  refine tb_noProbe_ite (tb_noProbe_pure fig qepF none) ?_
  cases sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => exact tb_noProbe_pure fig qepF none
  | some s₁ =>
    dsimp only
    refine tb_noProbe_ite (tb_noProbe_pure fig qepF none) ?_
    refine tb_noProbe_bind (tb_noProbe_lift_hook fig qepF _) fun rq => ?_
    refine tb_noProbe_ite
      (tb_noProbe_bind (tb_noProbe_set fig qepF _) fun _ => tb_noProbe_pure fig qepF none) ?_
    refine tb_noProbe_bind (tb_noProbe_lift_hook fig qepF _) fun rc => ?_
    cases mkPub (P := P) sC.base Q rq
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
         else sC.base.pn Q) with
    | none =>
      exact tb_noProbe_bind (tb_noProbe_set fig qepF _) fun _ => tb_noProbe_pure fig qepF none
    | some pp =>
      rcases pp with ⟨pq', pub⟩
      dsimp only
      refine tb_noProbe_bind (tb_noProbe_lift_hook fig qepF _) fun res => ?_
      cases res with
      | none =>
        exact tb_noProbe_bind (tb_noProbe_set fig qepF _) fun _ => tb_noProbe_pure fig qepF none
      | some c =>
        exact tb_noProbe_bind (tb_noProbe_set fig qepF _) fun _ => tb_noProbe_pure fig qepF _

theorem tb_stepSimCTrackNone_transmit_eq (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
        (.inl (.inl (.inl (.inl (Q, m₀, r))))) x tr =
      stepSimCTrackNoneSend P K ℓ Dh encPt encT idOf lam qep Q m₀ none r x tr := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hrel := tb_noProbe_simSendCTrackHalted P K qep fig (qep + 1) Q m₀ none r (x.1, tr) x.2
  unfold stepSimCTrackNone stepSimCTrackNoneSend
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
  change (((simSendCTrackHalted P K qep fig (probeHook fig (qep + 1)) Q m₀ none r).run
      (x.1, tr)).run x.2 >>= _) =
    ((simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ none r).run (x.1, tr))).run x.2.1 >>= _)
  rw [hrel]
  simp only [bind_assoc, pure_bind]

theorem tb_stepSimCTrackNone_chall_eq (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
        (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) x tr =
      stepSimCTrackNoneSend P K ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r x tr := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hrel := tb_noProbe_simSendCTrackHalted P K qep fig (qep + 1) Q m₀ (some m₁) r (x.1, tr) x.2
  unfold stepSimCTrackNone stepSimCTrackNoneSend
  dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add]
  change (((simSendCTrackHalted P K qep fig (probeHook fig (qep + 1)) Q m₀ (some m₁) r).run
      (x.1, tr)).run x.2 >>= _) =
    ((simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ (some m₁) r).run (x.1, tr))).run x.2.1 >>= _)
  rw [hrel]
  simp only [bind_assoc, pure_bind]

theorem tb_stepSimCTrackNone_deliver_eq (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
        (.inl (.inl (.inr (Q, w)))) x tr =
      let j? := x.1.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x >>= fun res =>
        let tr' := match res.1, j? with
          | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
          | _, _ => tr
        pure (res.1, (res.2, tr')) := by
  unfold stepSimCTrackNone stepSimCNone
  dsimp only [simImplCTrackHalted, simImplC, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_modify,
    StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  congr 1; funext r
  rcases r with ⟨⟨res, sC'⟩, gh'⟩
  cases res with
  | none => simp
  | some rr =>
    cases rr <;> cases x.1.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> simp

theorem tb_stepSimCTrackNone_inject_eq (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep
        (.inl (.inr (Q, w))) x tr =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x >>= fun res =>
        pure (res.1, (res.2, tr)) := by
  unfold stepSimCTrackNone stepSimCNone
  dsimp only [simImplCTrackHalted, simImplC, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  rfl

theorem tb_stepSimCTrackNone_corr_eq (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) :
    stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (.inr Q) x tr =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x >>= fun res =>
        pure (res.1, (res.2, tr)) := by
  unfold stepSimCTrackNone stepSimCNone
  dsimp only [simImplCTrackHalted, simImplC, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  rfl

theorem tb_simRecvUsesCoin_none {PQC : Type} (P : Params PQ PQC)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvUsesCoin P encT decT none Q w isDel st = false := by
  unfold simRecvUsesCoin
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  simp only [hnone, Bool.and_false, Bool.false_eq_true, ite_false]
  repeat' (first | rfl | split)

theorem tb_onAcceptPure_stopped (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped := by
  unfold onAcceptPure
  dsimp only
  repeat' (first | rfl | split)

theorem tb_onAnswerPure_stopped (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped := by
  unfold onAnswerPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm => exact tb_onAcceptPure_stopped qep Q w isDel t i _ ci? T pq' s

private theorem tb_simRecvStep_none_stopped {PQC : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st).2.1.stopped =
      st.1.stopped := by
  unfold simRecvStep
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  by_cases h1 : st.1.stopped = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.1.mir.win = true
    · simp [h2, h1]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (isDel && (st.1.mir.inTransit Q.other w).isNone) = true
      · simp [h3, h1]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : (!isDel && ((st.1.mir.inTransit Q.other w).isSome || !st.1.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w)) = true
        · simp [h4, h1]
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]
          by_cases h5 : w.length < 9
          · simp [h5, h1]
          · simp only [h5, ↓reduceIte]
            cases (signalWireCodec P.codec).parse (List.take (w.length - 8) w) with
            | none => simp [h1]
            | some hb =>
              rcases hb with ⟨h, _⟩
              dsimp only
              by_cases h6 : (!LibsignalAead.addressCheckPasses h.addresses (P.expectedAddrs Q)) = true
              · simp [h6, h1]
              · simp only [h6, Bool.false_eq_true, ↓reduceIte]
                cases P.spqr.recv (st.1.pq Q) h.pqRatchet with
                | error _ => simp [h1]
                | ok ps =>
                  rcases ps with ⟨pq', salt⟩
                  dsimp only
                  cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (st.1.chains Q) with
                  | some ci =>
                    dsimp only
                    by_cases h7 : ((st.1.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects (h.counter.toNat + 1) = true
                    · simp only [h7, ↓reduceIte]; simp [h1]
                    · simp only [h7, Bool.false_eq_true, ↓reduceIte, tb_onAnswerPure_stopped]; simp [h1]
                  | none =>
                    dsimp only
                    by_cases h8 : (Option.map (fun c => decide (c.1.1 ≠ st.1.mir.epoch Q + 1)) (Option.map (fun x => x.2) (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) st.1.honest)) == some true) = true
                    · simp only [h8, ↓reduceIte]; simp [h1]
                    · simp only [h8, Bool.false_eq_true, ↓reduceIte]
                      by_cases h9 : (decT h.senderRatchetKey == some 0) = true
                      · simp [h9, h1]
                      · simp only [h9, hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                        by_cases h10 : (inReceiveOnlyEpoch st.1.mir Q || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                        · simp only [h10, ↓reduceIte]
                          by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]
                        · simp only [h10, Bool.false_eq_true, ↓reduceIte]
                          cases decT h.senderRatchetKey with
                          | none =>
                            dsimp only
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]
                          | some T =>
                            simp only [Bool.false_eq_true, ↓reduceIte, tb_onAnswerPure_stopped]
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]

theorem tb_simRecvStops_none {PQC : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st = false := by
  unfold simRecvStops
  rw [tb_simRecvStep_none_stopped]
  cases st.1.stopped <;> simp

theorem tb_stepSimC_none_eq {PQC : Type} [SampleableType PQC] (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep none q x =
      stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimC, tb_simRecvStops_none]

theorem tb_evalDist_stepSimCEagerDeliverTrack_none (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (G : Option (SM.RecvResult (Plain ℓ)) → JointC PQ Pt ℓ × KemFailTrackState P.C.F →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep none Q w x tr ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x tr >>= fun r =>
        withEagerCoins r.2.1.1.base.mir (G r.1 r.2)] := by
  rw [tb_stepSimCTrackNone_deliver_eq]
  simp only [stepSimCEagerDeliverTrack, stepSimCEagerDeliver, tb_simRecvUsesCoin_none,
    Bool.false_and, Bool.false_eq_true, ite_false, evictStopsC_none, tb_stepSimC_none_eq,
    bind_assoc, pure_bind]
  refine (evalDist_withEagerCoins_step_unused x.1.base.mir
    (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x)
    (fun res => res.2.1.base.mir) _).trans ?_
  congr 2; funext r
  cases r.1 with
  | none => rfl
  | some rr =>
    cases rr <;> cases x.1.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl

theorem tb_evalDist_stepSimCEagerInjectTrack_none (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (G : Option (SM.RecvResult (Plain ℓ)) → JointC PQ Pt ℓ × KemFailTrackState P.C.F →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w))) x tr ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x tr >>= fun r =>
        withEagerCoins r.2.1.1.base.mir (G r.1 r.2)] := by
  rw [tb_stepSimCTrackNone_inject_eq]
  simp only [stepSimCEagerTrack, stepSimCEagerInject, tb_simRecvUsesCoin_none,
    Bool.false_and, Bool.false_eq_true, ite_false, evictStopsC_none, tb_stepSimC_none_eq,
    bind_assoc, pure_bind]
  exact evalDist_withEagerCoins_step_unused x.1.base.mir
    (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x)
    (fun res => res.2.1.base.mir) (fun res => G res.1 (res.2, tr))

theorem tb_evalDist_stepSimCEagerCorrTrack_none (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (G : Option (GhostState PQ) → JointC PQ Pt ℓ × KemFailTrackState P.C.F →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none (.inr Q) x tr ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep (.inr Q) x tr >>= fun r =>
        withEagerCoins r.2.1.1.base.mir (G r.1 r.2)] := by
  rw [tb_stepSimCTrackNone_corr_eq]
  simp only [stepSimCEagerTrack, stepSimCEagerCorr, tb_stepSimC_none_eq, bind_assoc, pure_bind]
  exact evalDist_withEagerCoins_step_unused x.1.base.mir
    (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x)
    (fun res => res.2.1.base.mir) (fun res => G res.1 (res.2, tr))

end EagerCore

end CryptoGames.LibsignalSM.Proofs.Refinement
